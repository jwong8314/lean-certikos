import CertiKOS.MC2Queue

/-!
# mC2: two locked calls in sequence

mC2's scheduler chains locked calls on different locks: `wakeup` dequeues
from a sleeping queue under that queue's lock, then enqueues on a pending
queue under another. `atomic_call` gives one call: it starts with the lock
idle, the lock's fairness, and the invariant on its region, and it ends idle
on that lock. To start the second call, the second lock must still be idle
for this CPU, and its region must still satisfy its invariant, after the
first call. This file proves that, for bodies that touch only their own lock.

* `Own1 s`: every call in `s` names the lock in `lk` as its first argument,
  and `s` never assigns `lk`. So every event the body appends is on its own
  lock. `acquireA` and `relA` are `Own1` (`own1_acquire`, `own1_rel`).
* `Fr c j J l`: the log `l` is valid, CPU `c` is idle on lock `j`, and the
  region last released on `j` satisfies `J`.
* `fr_run`: **a run of `Own1` code on lock `i` keeps `Fr c j J` for every
  other lock `j`**, under the rely `RelyJ` for `j`. Our own events are on
  lock `i`, so they leave lock `j`'s state and last released region alone.
  The other CPUs' events leave our phase alone (`rothers`) and keep `J`
  (the rely).
* `atomic_call_frame`: `atomic_call`, plus: lock `j` is still idle and `J`
  still holds at the end.
* `atomic_seq`: **two atomic calls on different locks in sequence.** The
  code is `acquire; s1; release; lk := jv; acquire; s2; release`. The first
  call is one event `(c, o1)` of object `O1`, and the second one event
  `(c, o2)` of `O2`. The second call's precondition may use the first call's
  result (`hpre2`). At the end both locks are idle and both invariants hold.

The fairness of each lock is assumed at every ticket (`∀ tn, FairA …`), since
the ticket the second call draws depends on the first call's run. The fair
environment `LockArray.fairEnvA` gives it at every ticket (`fairA_fair`).
-/

set_option linter.unusedVariables false

namespace MC2

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_other)
open LockRegion (REvent RLog RState HLogR rreplay rstep REnv rpull Region hmemR consO)
open LockRegionCPU KernFrame Layer LogInv

/-! ## Code that touches only its own lock -/

/-- Every call names the lock in `lk` first, and nothing assigns `lk`. -/
def Own1 : Stmt APrim → Prop
  | .skip => True
  | .assign x _ => x ≠ "lk"
  | .seq a b => Own1 a ∧ Own1 b
  | .ite _ a b => Own1 a ∧ Own1 b
  | .while _ b => Own1 b
  | .call x _ args => x ≠ "lk" ∧ ∃ rest, args = lkE :: rest

def Own1K : Cont APrim → Prop
  | .stop => True
  | .seq s k => Own1 s ∧ Own1K k
  | .loop _ b k => Own1 b ∧ Own1K k

theorem own1_acquire : Own1 acquireA := by simp [Own1, acquireA, loopA]

theorem own1_rel : Own1 relA := by simp [Own1, relA]

/-- A step keeps `Own1` code `Own1`, and keeps `lk`. -/
theorem own1_step {P : Prims APrim RLog} {x x' : Config APrim RLog} (hS : Own1 x.stmt) (hK : Own1K x.cont)
    (hs : step P x = some x') : Own1 x'.stmt ∧ Own1K x'.cont ∧ x'.locals "lk" = x.locals "lk" := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  cases stmt with
  | skip =>
    cases cont with
    | stop => simp [step] at hs
    | seq s k => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hK.1, hK.2, rfl⟩
    | loop e b k => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hK.1, hK.2, rfl⟩
  | assign y e =>
    simp only [step, Option.some.injEq] at hs; subst hs
    exact ⟨trivial, hK, Locals.set_other _ _ (Ne.symm hS)⟩
  | seq a b => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hS.1, ⟨hS.2, hK⟩, rfl⟩
  | ite e a b =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨?_, hK, rfl⟩; simp only; split; exact hS.2; exact hS.1
  | «while» e b =>
    simp only [step] at hs
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst hs
    · exact ⟨trivial, hK, rfl⟩
    · exact ⟨hS, ⟨hS, hK⟩, rfl⟩
  | call y p args =>
    simp only [step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      exact ⟨trivial, hK, Locals.set_other _ _ (Ne.symm hS.1)⟩
    · simp at hs

/-- **A call on lock `v` appends only events of ours on lock `v`**, after the
environment's events. -/
theorem own_prim {εR : REnv} {c : CPU} {p : APrim} {v : Val} {vs : List Val} {l l' : RLog} {r : Val}
    (h : rprimsA εR c p (v :: vs) l = some (r, l')) :
    l' = l ∨ ∃ k, l' = ⟨c, v.toNat, k⟩ :: l ∨ l' = ⟨c, v.toNat, k⟩ :: rpull εR c l := by
  cases p <;> rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩ <;> simp [rprimsA] at h <;>
    (try obtain ⟨-, rfl⟩ := h) <;> simp [LockRegion.rev]

/-! ## The frame of another lock -/

/-- The log is valid, `c` is idle on lock `j`, and lock `j`'s last released
region satisfies `J`. -/
def Fr (c : CPU) (j : Nat) (J : Region → Prop) (l : RLog) : Prop :=
  ∃ S H, rreplay l = some (S, H) ∧ (S.lk j).phase c = .idle ∧ J (hmemR j H)

/-- An event on another lock leaves lock `j`'s state and last released region. -/
theorem rstep_frame {S S' : RState} {e : REvent} {o : Option LockRegion.HEventR} {H : HLogR} {j : Nat}
    (hj : e.lk ≠ j) (hs : rstep S e = some (S', o)) : S'.lk j = S.lk j ∧ hmemR j (consO o H) = hmemR j H := by
  obtain ⟨c, i, k⟩ := e
  simp only at hj
  cases k with
  | tk k =>
    simp only [rstep] at hs
    split at hs
    · simp at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      exact ⟨upd_other _ _ (Ne.symm hj), LockRegion.hmemR_lift_other hj _ _ _⟩
  | pull =>
    simp only [rstep] at hs
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs; exact ⟨rfl, rfl⟩
    · simp at hs
  | wr a v =>
    simp only [rstep] at hs
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs; exact ⟨rfl, rfl⟩
    · simp at hs

theorem fr_cons {c : CPU} {j : Nat} {J : Region → Prop} {l : RLog} (hF : Fr c j J l) {e : REvent}
    (he : e.lk ≠ j) (hv : ∃ S H, rreplay (e :: l) = some (S, H)) : Fr c j J (e :: l) := by
  obtain ⟨S, H, hl, hid, hJ⟩ := hF
  obtain ⟨S', H', hl'⟩ := hv
  obtain ⟨S0, H0, o, hl0, hs, rfl⟩ := LockRegion.rreplay_cons hl'
  rw [hl] at hl0
  simp only [Option.some.injEq, Prod.mk.injEq] at hl0; obtain ⟨rfl, rfl⟩ := hl0
  obtain ⟨g1, g2⟩ := rstep_frame (H := H) he hs
  exact ⟨S', _, hl', by rw [g1]; exact hid, by rw [g2]; exact hJ⟩

theorem rreplay_suffix : ∀ (ys : RLog) {l : RLog} {S : RState} {H : HLogR},
    rreplay (ys ++ l) = some (S, H) → ∃ S H, rreplay l = some (S, H)
  | [], _, S, H, h => ⟨S, H, h⟩
  | _ :: ys, _, _, _, h => by
    obtain ⟨S2, H2, -, h2, -, -⟩ := LockRegion.rreplay_cons h
    exact rreplay_suffix ys h2

/-- The environment's events keep `Fr`, under the rely. -/
theorem fr_pull {εR : REnv} {c : CPU} {j : Nat} {J : Region → Prop} (hRJ : RelyJ εR c j J) {l : RLog}
    (hF : Fr c j J l) (hv : ∃ S H, rreplay (rpull εR c l) = some (S, H)) : Fr c j J (rpull εR c l) := by
  obtain ⟨S, H, hl, hid, hJ⟩ := hF
  obtain ⟨S1, H1, hl1⟩ := hv
  obtain ⟨g1, -⟩ := rothers (c := c) (i := j) hl (εR.query c l) (εR.noSelf c l) hl1
  exact ⟨S1, H1, hl1, by rw [g1 j]; exact hid, hRJ _ S H S1 H1 hl hl1 hJ⟩

/-- A call on lock `v ≠ j` keeps `Fr c j J`. -/
theorem fr_prim {εR : REnv} {c : CPU} {j : Nat} {J : Region → Prop} (hRJ : RelyJ εR c j J) {p : APrim}
    {v : Val} {vs : List Val} {l l' : RLog} {r : Val} (hvj : v.toNat ≠ j)
    (h : rprimsA εR c p (v :: vs) l = some (r, l')) (hF : Fr c j J l) (hv : ∃ S H, rreplay l' = some (S, H)) :
    Fr c j J l' := by
  rcases own_prim h with rfl | ⟨k, rfl | rfl⟩
  · exact hF
  · exact fr_cons hF hvj hv
  · obtain ⟨S, H, hl⟩ := hv
    exact fr_cons (fr_pull hRJ hF (rreplay_suffix [_] hl)) hvj ⟨S, H, hl⟩

/-- An `Own1` step extends the log. -/
theorem own1_ext {εR : REnv} {c : CPU} {x x' : Config APrim RLog} (hS : Own1 x.stmt)
    (hs : step (rprimsA εR c) x = some x') : ∃ ys, x'.abs = ys ++ x.abs := by
  rcases step_abs hs with h | ⟨t, p, args, v, hst, hp⟩
  · exact ⟨[], h⟩
  · rw [hst] at hS
    obtain ⟨-, rest, rfl⟩ := hS
    simp only [List.map] at hp
    rcases own_prim hp with h | ⟨k, h | h⟩
    · exact ⟨[], h⟩
    · exact ⟨[_], h⟩
    · exact ⟨_ :: εR.query c x.abs, by rw [h]; rfl⟩

theorem own1_star_ext {εR : REnv} {c : CPU} {x z : Config APrim RLog} (h : Star (rprimsA εR c) x z) :
    Own1 x.stmt → Own1K x.cont → ∃ ys, z.abs = ys ++ x.abs := by
  induction h with
  | refl => intro _ _; exact ⟨[], rfl⟩
  | @step a b d hs _ ih =>
    intro hS hK
    obtain ⟨hS', hK', -⟩ := own1_step hS hK hs
    obtain ⟨ys, hys⟩ := ih hS' hK'
    obtain ⟨zs, hzs⟩ := own1_ext hS hs
    exact ⟨ys ++ zs, by rw [hys, hzs, List.append_assoc]⟩

/-- **A run of `Own1` code on lock `i` keeps `Fr c j J` for a lock `j ≠ i`**,
if the log it ends on is valid. -/
theorem fr_run {εR : REnv} {c : CPU} {j : Nat} {J : Region → Prop} (hRJ : RelyJ εR c j J)
    {x z : Config APrim RLog} (h : Star (rprimsA εR c) x z) :
    Own1 x.stmt → Own1K x.cont → (x.locals "lk").toNat ≠ j → Fr c j J x.abs →
    (∃ S H, rreplay z.abs = some (S, H)) → Fr c j J z.abs := by
  induction h with
  | refl => intro _ _ _ hF _; exact hF
  | @step a b d hs hrest ih =>
    intro hS hK hlk hF hz
    obtain ⟨hS', hK', hlk'⟩ := own1_step hS hK hs
    obtain ⟨ys, hys⟩ := own1_star_ext hrest hS' hK'
    have hb : ∃ S H, rreplay b.abs = some (S, H) := by
      obtain ⟨S, H, hz⟩ := hz; rw [hys] at hz; exact rreplay_suffix ys hz
    refine ih hS' hK' (by rw [hlk']; exact hlk) ?_ hz
    rcases step_abs hs with heq | ⟨t, p, args, v, hst, hp⟩
    · rw [heq]; exact hF
    · rw [hst] at hS
      obtain ⟨-, rest, rfl⟩ := hS
      simp only [List.map] at hp
      exact fr_prim hRJ hlk hp hF hb

/-! ## One call, with the frame of another lock -/

/-- **`atomic_call`, keeping another lock `j`**: if `c` is idle on `j` and
`j`'s region satisfies `J'` before the call, both still hold after it. -/
theorem atomic_call_frame {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) {O : AObj} {F : Nat → Prop} {pre : Locals → Prop} {o : O.Op}
    {x : Ident} {s : Stmt APrim} (hT : Impl εR c iv.toNat O F pre o x s) (hx : x ≠ "_")
    (hpre : ∀ σ1 : Locals, (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) → pre σ1)
    (hRJ : RelyJ εR c iv.toNat O.J) (hJ : O.J (hmemR iv.toNat H))
    {j : Nat} (hij : iv.toNat ≠ j) {J' : Region → Prop} (hRJ' : RelyJ εR c j J')
    (hid' : (S.lk j).phase c = .idle) (hJ' : J' (hmemR j H)) (hown : Own1 s) :
    ∃ H1 : HLogR, O.J (hmemR iv.toNat H1) ∧
      ∀ h, O.rep (O.replay h) (hmemR iv.toNat H1) →
        ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR),
          Star (rprimsA εR c) ⟨.seq acquireA (.seq s relA), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          O.rep (O.replay ((c, o) :: h)) (hmemR iv.toNat H3) ∧ O.J (hmemR iv.toNat H3) ∧
          (∀ r, O.result h c o = some r → σ' x = BitVec.ofNat 32 r) ∧
          (S3.lk j).phase c = .idle ∧ J' (hmemR j H3) := by
  obtain ⟨H1, hJ1, k⟩ := atomic_call hE hRR hc hRA hl hidle bound K hK hF σ hσ hT hx hpre hRJ hJ
  refine ⟨H1, hJ1, fun h hM => ?_⟩
  obtain ⟨σ', rb, S3, H3, hrun, hl3, hid, hM3, hJ3, hres⟩ := k h hM
  obtain ⟨S4, H4, hl4, hid4, hJ4⟩ := fr_run hRJ' hrun ⟨own1_acquire, hown, own1_rel⟩ trivial
    (by show (σ "lk").toNat ≠ j; rw [hσ]; exact hij) ⟨S, H, hl, hid', hJ'⟩ ⟨S3, H3, hl3⟩
  rw [hl3] at hl4
  simp only [Option.some.injEq, Prod.mk.injEq] at hl4; obtain ⟨rfl, rfl⟩ := hl4
  exact ⟨σ', rb, S3, H3, hrun, hl3, hid, hM3, hJ3, hres, hid4, hJ4⟩

/-! ## Two calls in sequence -/

/-- The code of two locked calls with `mid` between them:
`acquire; s1; release; mid; acquire; s2; release`. -/
def seq2 (s1 mid s2 : Stmt APrim) : Stmt APrim :=
  .seq (.seq acquireA (.seq s1 relA)) (.seq mid (.seq acquireA (.seq s2 relA)))

/-- **Two atomic calls on different locks in sequence.**

The first call finds the replay of some history `h1` of `O1` and is the
event `(c, o1)`. Between the calls, `mid` runs without touching the log, and
sets `lk` to the second lock (`hmid`, `hm`). The second call finds the replay
of some history `h2` of `O2` and is the event `(c, o2 h1)`: the operation may
depend on what the first call found, e.g. the thread it dequeued. Its
precondition may use the first call's result in `x1` (`hpre2`), for the
histories `h1` allowed by `G`.

At the end both locks are idle for `c` and both regions satisfy their
invariants. The first event is in the log `rm` at the first release, and the
final log extends `rm` (`rb = ys ++ rm`): the first call linearizes before
the second. -/
theorem atomic_seq {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv jv : Val} (hij : iv.toNat ≠ jv.toNat)
    (hid1 : (S.lk iv.toNat).phase c = .idle) (hid2 : (S.lk jv.toNat).phase c = .idle)
    (bound1 bound2 : ALog → Nat) (K1 K2 : Nat) (hK1 : ∀ l, bound1 l ≤ K1) (hK2 : ∀ l, bound2 l ≤ K2)
    (hF1 : ∀ tn, LockArray.FairA ε c iv.toNat tn bound1) (hF2 : ∀ tn, LockArray.FairA ε c jv.toNat tn bound2)
    (σ : Locals) (hσ : σ "lk" = iv)
    {O1 : AObj} {F1 : Nat → Prop} {pre1 : Locals → Prop} {o1 : O1.Op} {x1 : Ident} {s1 : Stmt APrim}
    (hT1 : Impl εR c iv.toNat O1 F1 pre1 o1 x1 s1) (hx1 : x1 ≠ "_") (hown1 : Own1 s1)
    (hpre1 : ∀ σ1 : Locals, (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) → pre1 σ1)
    (hRJ1 : RelyJ εR c iv.toNat O1.J) (hJ1 : O1.J (hmemR iv.toNat H))
    {mid : Stmt APrim} {m : Locals → Locals} (hmid : ∀ σ l, Runs (rprimsA εR c) mid σ l (m σ) l)
    (hm : ∀ σ, m σ "lk" = jv)
    {O2 : AObj} {F2 : Nat → Prop} {pre2 : List (CPU × O1.Op) → Locals → Prop} {o2 : List (CPU × O1.Op) → O2.Op}
    {x2 : Ident} {s2 : Stmt APrim}
    (hT2 : ∀ h1, Impl εR c jv.toNat O2 F2 (pre2 h1) (o2 h1) x2 s2) (hx2 : x2 ≠ "_") (hown2 : Own1 s2)
    (G : List (CPU × O1.Op) → Prop)
    (hpre2 : ∀ h1, G h1 → ∀ σ' : Locals, (∀ r, O1.result h1 c o1 = some r → σ' x1 = BitVec.ofNat 32 r) →
      ∀ σ1 : Locals, (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = m σ' z) → pre2 h1 σ1)
    (hRJ2 : RelyJ εR c jv.toNat O2.J) (hJ2 : O2.J (hmemR jv.toNat H)) :
    ∃ Ha : HLogR, O1.J (hmemR iv.toNat Ha) ∧
      ∀ h1, O1.rep (O1.replay h1) (hmemR iv.toNat Ha) → G h1 →
        ∃ Hb : HLogR, O2.J (hmemR jv.toNat Hb) ∧
          ∀ h2, O2.rep (O2.replay h2) (hmemR jv.toNat Hb) →
            ∃ (σ' : Locals) (rb : RLog) (S' : RState) (H' : HLogR) (rm : RLog) (Sm : RState) (Hm : HLogR)
              (ys : RLog),
              Star (rprimsA εR c) ⟨seq2 s1 mid s2, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
              rreplay rb = some (S', H') ∧
              (S'.lk iv.toNat).phase c = .idle ∧ (S'.lk jv.toNat).phase c = .idle ∧
              O1.J (hmemR iv.toNat H') ∧
              O2.rep (O2.replay ((c, o2 h1) :: h2)) (hmemR jv.toNat H') ∧ O2.J (hmemR jv.toNat H') ∧
              (∀ r, O2.result h2 c (o2 h1) = some r → σ' x2 = BitVec.ofNat 32 r) ∧
              rreplay rm = some (Sm, Hm) ∧ O1.rep (O1.replay ((c, o1) :: h1)) (hmemR iv.toNat Hm) ∧
              rb = ys ++ rm := by
  obtain ⟨Ha, hJa, k1⟩ := atomic_call_frame hE hRR hc hRA hl hid1 bound1 K1 hK1 (hF1 _) σ hσ hT1 hx1 hpre1
    hRJ1 hJ1 hij hRJ2 hid2 hJ2 hown1
  refine ⟨Ha, hJa, fun h1 hM1 hG => ?_⟩
  obtain ⟨σ1, rm, Sm, Hm, hrun1, hlm, hidm, hMm, hJm, hres1, hidm', hJm'⟩ := k1 h1 hM1
  obtain ⟨Hb, hJb, k2⟩ := atomic_call_frame hE hRR hc hRA hlm hidm' bound2 K2 hK2 (hF2 _) (m σ1)
    (hm σ1) (hT2 h1) hx2 (hpre2 h1 hG σ1 hres1) hRJ2 hJm' (Ne.symm hij) hRJ1 hidm hJm hown2
  refine ⟨Hb, hJb, fun h2 hM2 => ?_⟩
  obtain ⟨σf, rf, S5, H5, hrun2, hl5, hid5, hM5, hJ5, hres2, hid5', hJ5'⟩ := k2 h2 hM2
  obtain ⟨ys, hys⟩ := own1_star_ext hrun2 ⟨own1_acquire, hown2, own1_rel⟩ trivial
  exact ⟨σf, rf, S5, H5, rm, Sm, Hm, ys,
    (Runs.seq (Runs.of_stop hrun1) (Runs.seq (hmid σ1 rm) (Runs.of_stop hrun2))) .stop,
    hl5, hid5', hid5, hJ5', hM5, hJ5, hres2, hlm, hMm, hys⟩

/-! ## Moving a thread between two shared queues -/

section Move
open MC2Queue

theorem own1_enQS (np : Nat) : Own1 (enQS np) := by simp [Own1, enQS, MC2Queue.wr]

theorem own1_deQS (np : Nat) : Own1 (deQS np) := by simp [Own1, deQS, MC2Queue.wr]

/-- Between the calls: the dequeued thread `r` becomes the argument `pi`, and
`lk` becomes the second queue's lock. -/
def moveMid (jv : Val) : Stmt APrim := .seq (.assign "pi" (.var "r")) (.assign "lk" (.const jv))

/-- The thread a `deQ` after `h` returns (`np` for an empty queue). -/
def taken (np : Nat) (c : CPU) (h : List (CPU × (Q np).Op)) : Nat := ((Q np).result h c .deQ).getD np

/-- **`acquire(q1); t = dequeue(); release(q1); acquire(q2); enqueue(t);
release(q2)` is two events**: `(c, deQ)` on the first queue, then
`(c, enQ t)` on the second, where `t` is the head of the first queue after
the history the first call found. This is the shape of `wakeup`, which moves
a thread from a sleeping queue to a pending queue. -/
theorem move_atomic {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv jv : Val} (hij : iv.toNat ≠ jv.toNat)
    (hid1 : (S.lk iv.toNat).phase c = .idle) (hid2 : (S.lk jv.toNat).phase c = .idle)
    (bound1 bound2 : ALog → Nat) (K1 K2 : Nat) (hK1 : ∀ l, bound1 l ≤ K1) (hK2 : ∀ l, bound2 l ≤ K2)
    (hF1 : ∀ tn, LockArray.FairA ε c iv.toNat tn bound1) (hF2 : ∀ tn, LockArray.FairA ε c jv.toNat tn bound2)
    {np : Nat} (hnp : 2 * np + 4 < 2 ^ 32) (σ : Locals) (hσ : σ "lk" = iv)
    (hRJ1 : RelyJ εR c iv.toNat (Q np).J) (hJ1 : (Q np).J (hmemR iv.toNat H))
    (hRJ2 : RelyJ εR c jv.toNat (Q np).J) (hJ2 : (Q np).J (hmemR jv.toNat H)) :
    ∃ Ha : HLogR, (Q np).J (hmemR iv.toNat Ha) ∧
      ∀ h1, (Q np).rep ((Q np).replay h1) (hmemR iv.toNat Ha) → (Q np).replay h1 ≠ none →
        ∃ Hb : HLogR, (Q np).J (hmemR jv.toNat Hb) ∧
          ∀ h2, (Q np).rep ((Q np).replay h2) (hmemR jv.toNat Hb) →
            ∃ (σ' : Locals) (rb : RLog) (S' : RState) (H' : HLogR) (rm : RLog) (Sm : RState) (Hm : HLogR)
              (ys : RLog),
              Star (rprimsA εR c) ⟨seq2 (deQS np) (moveMid jv) (enQS np), .stop, σ, l⟩
                ⟨.skip, .stop, σ', rb⟩ ∧
              rreplay rb = some (S', H') ∧
              (S'.lk iv.toNat).phase c = .idle ∧ (S'.lk jv.toNat).phase c = .idle ∧
              (Q np).J (hmemR iv.toNat H') ∧
              (Q np).rep ((Q np).replay ((c, .enQ (taken np c h1)) :: h2)) (hmemR jv.toNat H') ∧
              (Q np).J (hmemR jv.toNat H') ∧
              rreplay rm = some (Sm, Hm) ∧ (Q np).rep ((Q np).replay ((c, .deQ) :: h1)) (hmemR iv.toNat Hm) ∧
              rb = ys ++ rm := by
  obtain ⟨Ha, hJa, k⟩ := atomic_seq (O1 := Q np) (O2 := Q np) (o1 := .deQ) (x1 := "r") (s1 := deQS np)
    (mid := moveMid jv) (m := fun σ => (σ.set "pi" (σ "r")).set "lk" jv)
    (pre2 := fun h1 σ => σ "pi" = BitVec.ofNat 32 (taken np c h1)) (o2 := fun h1 => .enQ (taken np c h1))
    (x2 := "r") (s2 := enQS np)
    hE hRR hc hRA hl hij hid1 hid2 bound1 bound2 K1 K2 hK1 hK2 hF1 hF2 σ hσ
    (deQ_impl εR c iv.toNat hnp) (by decide) (own1_deQS np) (fun _ _ => trivial) hRJ1 hJ1
    (fun σ l => Runs.seq (Runs.assign _ _) (Runs.assign _ _)) (fun σ => Locals.set_same _ _ _)
    (fun h1 => enQ_impl εR c jv.toNat hnp _) (by decide) (own1_enQS np)
    (fun h1 => (Q np).replay h1 ≠ none)
    (fun h1 hG σ' hres σ1 hfr => by
      rw [hfr "pi" (by decide) (by decide) (by decide) (by decide)]
      show ((σ'.set "pi" (σ' "r")).set "lk" jv) "pi" = _
      rw [Locals.set_other _ _ (by decide), Locals.set_same]
      cases hq : (Q np).replay h1 with
      | none => exact absurd hq hG
      | some q =>
        have hr : (Q np).result h1 c .deQ = some (q.getLastD np) := by
          show (qstep np .deQ ((Q np).replay h1)).2 = _; rw [hq]; rfl
        rw [hres _ hr]; simp [taken, hr])
    hRJ2 hJ2
  refine ⟨Ha, hJa, fun h1 hM1 hG => ?_⟩
  obtain ⟨Hb, hJb, k2⟩ := k h1 hM1 hG
  refine ⟨Hb, hJb, fun h2 hM2 => ?_⟩
  obtain ⟨σ', rb, S', H', rm, Sm, Hm, ys, hrun, hl', hi1, hi2, hJ1', hM', hJ2', -, hlm, hMm, hys⟩ := k2 h2 hM2
  exact ⟨σ', rb, S', H', rm, Sm, Hm, ys, hrun, hl', hi1, hi2, hJ1', hM', hJ2', hlm, hMm, hys⟩

end Move

end MC2
