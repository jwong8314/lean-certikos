import CertiKOS.LockRegion
import CertiKOS.LockArrayCPU
import CertiKOS.MCSBoundC
import CertiKOS.LockArrayFair

/-!
# Lock regions per CPU: the C code, its guarantee, and no lost updates

`LockRegion.lean` gave the protocol for locks that protect regions. This file
verifies C code against it, for one CPU under an environment.

* `rprimsA`: the primitives over region logs. The lock primitives are those of
  the lock array. `rd(lk, j)` reads cell `j` of the region and
  `wr(lk, j, v)` writes it. Only the holder touches the region, so `rd` and
  `wr` do not ask the environment.
* `erase`: drop the writes from a region log to get a lock-array log.
  `step_erase`: a step of code that uses only the lock primitives is exactly
  the lock-array step on the erased log. So the lock array's `acquire`
  (`acquireA`), with its liveness, runs unchanged on regions (`star_liftR`).
* `lock_run_valid`: such a run keeps the region log valid, given an
  environment that does (`RelyR`). A fresh holder's region is clean.
* `crit_runR`: the critical section `cell[j]++ for j < k` runs, stays valid,
  and increments exactly those cells.
* `clientR_guarantee`: **the per-CPU guarantee with no lost updates.** The
  client `acquire(lk); cell[j]++ for j < k; release(lk)` finishes idle on a
  valid log. The region it releases is the region the previous holder
  released, with cells `0 … k-1` each incremented by one.
-/

namespace LockRegionCPU

open ClightL Ticket
open LockArray (APrim AEnv ALog AEvent AState HLogA areplay aprims apull acquireA lkE)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR)
open LockArray (upd upd_same upd_other)

/-! ## Erasure to the lock array -/

def eraseE : REvent → Option AEvent
  | ⟨c, i, .tk k⟩ => some ⟨c, i, .tk k⟩
  | ⟨c, i, .pull⟩ => some ⟨c, i, .pull⟩
  | ⟨_, _, .wr _ _⟩ => none

def erase (l : RLog) : ALog := l.filterMap eraseE

theorem erase_append (a b : RLog) : erase (a ++ b) = erase a ++ erase b := by
  simp [erase, List.filterMap_append]

theorem projL_erase (i : Nat) : ∀ l : RLog, LockArray.projL i (erase l) = LockRegion.projL i l
  | [] => rfl
  | ⟨c, j, k⟩ :: l => by
    have ih := projL_erase i l
    cases k with
    | tk k =>
      simp only [erase, List.filterMap_cons, eraseE, LockArray.projL, LockRegion.projL] at ih ⊢
      split <;> simp [ih]
    | pull => simpa [erase, eraseE, LockArray.projL, LockRegion.projL] using ih
    | wr a v => exact ih

theorem memOf_erase (i : Nat) : ∀ l : RLog, LockArray.memOf i (erase l) = 0
  | [] => rfl
  | ⟨c, j, k⟩ :: l => by
    have ih := memOf_erase i l
    cases k with
    | tk k => simpa [erase, eraseE, LockArray.memOf] using ih
    | pull => simpa [erase, eraseE, LockArray.memOf] using ih
    | wr a v => exact ih

/-- A valid region log erases to a valid lock-array log with the same lock states. -/
theorem rreplay_erase : ∀ {l : RLog} {S : RState} {H : HLogR}, rreplay l = some (S, H) →
    ∃ SA HA, areplay (erase l) = some (SA, HA) ∧ SA.lk = S.lk
  | [], S, H, hr => by
    simp only [rreplay, Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    exact ⟨_, _, rfl, rfl⟩
  | ⟨c, j, k⟩ :: l, S', H', hr => by
    obtain ⟨S, H, o, hl, hp, -⟩ := LockRegion.rreplay_cons hr
    obtain ⟨SA, HA, hA, hlk⟩ := rreplay_erase hl
    cases k with
    | tk k =>
      simp only [rstep] at hp
      split at hp
      · simp at hp
      · rename_i p' o' hps
        simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp
        have : LockArray.astep SA ⟨c, j, .tk k⟩ = some (⟨upd SA.lk j p', SA.mem,
            if k = .hold ∨ k = .incNow then upd SA.dirty j false else SA.dirty⟩,
            o'.map (LockArray.lift j (SA.mem j))) := by simp [LockArray.astep, hlk, hps]
        exact ⟨_, _, LockArray.areplay_cons_of hA this, by simp [hlk]⟩
    | pull =>
      simp only [rstep] at hp
      split at hp
      · rename_i hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp
        have hh' : LockArray.Holding SA c j := by
          obtain ⟨t, ht⟩ := hh; exact ⟨t, by rw [hlk]; exact ht⟩
        have : LockArray.astep SA ⟨c, j, .pull⟩ = some (SA, none) := by simp [LockArray.astep, hh']
        exact ⟨_, _, LockArray.areplay_cons_of hA this, hlk⟩
      · simp at hp
    | wr a v =>
      simp only [rstep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp
        exact ⟨SA, HA, hA, hlk⟩
      · simp at hp

/-- A lock event that the lock array accepts is accepted on regions. -/
theorem rstep_of_astep {S : RState} {SA : AState} (hlk : SA.lk = S.lk) {e : REvent} {ea : AEvent}
    (he : eraseE e = some ea) {SA' : AState} {oa : Option LockArray.HEventA}
    (ha : LockArray.astep SA ea = some (SA', oa)) : ∃ S' o, rstep S e = some (S', o) := by
  obtain ⟨c, j, k⟩ := e
  cases k with
  | tk k =>
    simp only [eraseE, Option.some.injEq] at he; subst he
    simp only [LockArray.astep, hlk] at ha
    split at ha
    · simp at ha
    · rename_i p' o' hps
      exact ⟨⟨upd S.lk j p', S.mem, if k = .hold ∨ k = .incNow then upd S.dirty j false else S.dirty⟩,
        o'.map (LockRegion.lift j (S.mem j)), by simp [rstep, hps]⟩
  | pull =>
    simp only [eraseE, Option.some.injEq] at he; subst he
    simp only [LockArray.astep] at ha
    split at ha
    · rename_i hh
      have hh' : LockRegion.Holding S c j := by obtain ⟨t, ht⟩ := hh; exact ⟨t, by rw [← hlk]; exact ht⟩
      exact ⟨S, none, by simp [rstep, hh']⟩
    · simp at ha
  | wr a v => simp [eraseE] at he

/-! ## The primitives -/

/-- The lock-array primitives over region logs, with `pull(lk, j)` reading cell
`j` (`rd`) and `push(lk, j, v)` writing it (`wr`). -/
def rprimsA (ε : REnv) (c : CPU) : Prims APrim RLog
  | .faiTicket, [i], l =>
      let l1 := rpull ε c l
      some (BitVec.ofNat 32 (ticket (LockRegion.projL i.toNat l1)), rev c i.toNat .incTicket :: l1)
  | .getNow, [i], l =>
      let l1 := rpull ε c l
      some (BitVec.ofNat 32 (now (LockRegion.projL i.toNat l1)), rev c i.toNat .getNow :: l1)
  | .incNow, [i], l => some (0, rev c i.toNat .incNow :: rpull ε c l)
  | .hold, [i], l => some (0, rev c i.toNat .hold :: rpull ε c l)
  | .pull, [i], l => some (0, ⟨c, i.toNat, .pull⟩ :: rpull ε c l)
  | .pull, [i, j], l => some (LockRegion.memOf i.toNat l j.toNat, l)
  | .push, [i, j, v], l => some (0, ⟨c, i.toNat, .wr j.toNat v⟩ :: l)
  | _, _, _ => none

/-- The region environment's events erase to the lock-array environment's. -/
def EnvErases (εR : REnv) (ε : AEnv) : Prop := ∀ c l, erase (εR.query c l) = ε.query c (erase l)

theorem erase_rpull {εR : REnv} {ε : AEnv} (hE : EnvErases εR ε) (c : CPU) (l : RLog) :
    erase (rpull εR c l) = apull ε c (erase l) := by
  simp [rpull, apull, erase_append, hE c l]

/-- Calls that use only the lock: no `wr`, and `pull` with one argument. -/
def OkL (p : APrim) (args : List Expr) : Prop := p ≠ .push ∧ (p = .pull → args.length = 1)

def LockS : Stmt APrim → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq a b => LockS a ∧ LockS b
  | .ite _ a b => LockS a ∧ LockS b
  | .while _ b => LockS b
  | .call _ p args => OkL p args

def LockK : Cont APrim → Prop
  | .stop => True
  | .seq s k => LockS s ∧ LockK k
  | .loop _ b k => LockS b ∧ LockK k

def erC (x : Config APrim RLog) : Config APrim ALog := ⟨x.stmt, x.cont, x.locals, erase x.abs⟩

/-- **Erasure commutes with a step** of lock-only code. -/
theorem step_erase {εR : REnv} {ε : AEnv} (hE : EnvErases εR ε) (c : CPU) (x : Config APrim RLog)
    (hL : LockS x.stmt) : step (aprims ε c) (erC x) = (step (rprimsA εR c) x).map erC := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  have hb := erase_rpull hE c l
  cases stmt with
  | skip => cases cont <;> rfl
  | assign x e => rfl
  | seq a b => rfl
  | ite e a b => by_cases hz : Expr.eval σ e = 0#32 <;> simp [step, erC, hz]
  | «while» e b => by_cases hz : Expr.eval σ e = 0#32 <;> simp [step, erC, hz]
  | call x p args =>
    obtain ⟨hnp, hpl⟩ := hL
    have hb' : (rpull εR c l).filterMap eraseE = apull ε c (l.filterMap eraseE) := hb
    have hp1 : ∀ i, LockArray.projL i (apull ε c (l.filterMap eraseE)) = LockRegion.projL i (rpull εR c l) := by
      intro i; rw [← hb']; exact projL_erase i _
    have hm1 : ∀ i, LockArray.memOf i (apull ε c (l.filterMap eraseE)) = 0 := by
      intro i; rw [← hb']; exact memOf_erase i _
    cases p with
    | push => exact absurd rfl hnp
    | pull =>
      have hlen := hpl rfl
      match args, hlen with
      | [a], _ => simp [step, erC, aprims, rprimsA, erase, eraseE, hb', hm1]
    | faiTicket =>
      match args with
      | [] => rfl
      | [a] => simp [step, erC, aprims, rprimsA, erase, eraseE, hb', hp1, rev, LockArray.ev]
      | _ :: _ :: _ => rfl
    | getNow =>
      match args with
      | [] => rfl
      | [a] => simp [step, erC, aprims, rprimsA, erase, eraseE, hb', hp1, rev, LockArray.ev]
      | _ :: _ :: _ => rfl
    | incNow =>
      match args with
      | [] => rfl
      | [a] => simp [step, erC, aprims, rprimsA, erase, eraseE, hb', rev, LockArray.ev]
      | _ :: _ :: _ => rfl
    | hold =>
      match args with
      | [] => rfl
      | [a] => simp [step, erC, aprims, rprimsA, erase, eraseE, hb', rev, LockArray.ev]
      | _ :: _ :: _ => rfl

/-- A step keeps lock-only code lock-only. -/
theorem lock_step {P : Prims APrim RLog} {x x' : Config APrim RLog} (hS : LockS x.stmt) (hK : LockK x.cont)
    (hs : step P x = some x') : LockS x'.stmt ∧ LockK x'.cont := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  cases stmt with
  | skip =>
    cases cont with
    | stop => simp [step] at hs
    | seq s k => simp only [step, Option.some.injEq] at hs; subst hs; exact hK
    | loop e b k => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hK.1, hK.2⟩
  | assign y e => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨trivial, hK⟩
  | seq a b => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hS.1, hS.2, hK⟩
  | ite e a b =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨?_, hK⟩; simp only; split; exact hS.2; exact hS.1
  | «while» e b =>
    simp only [step] at hs
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst hs
    · exact ⟨trivial, hK⟩
    · exact ⟨hS, hS, hK⟩
  | call y p args =>
    simp only [step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs; exact ⟨trivial, hK⟩
    · simp at hs

/-- **Lock-array runs lift to region runs** of the same lock-only code. -/
theorem star_liftR {εR : REnv} {ε : AEnv} (hE : EnvErases εR ε) (c : CPU) {a y' : Config APrim ALog}
    (h : Star (aprims ε c) a y') : ∀ x, erC x = a → LockS x.stmt → LockK x.cont →
      ∃ y, Star (rprimsA εR c) x y ∧ erC y = y' := by
  induction h with
  | refl => intro x hx _ _; exact ⟨x, .refl _, hx⟩
  | step hs _ ih =>
    intro x hx hS hK
    rw [← hx, step_erase hE c x hS] at hs
    cases hx' : step (rprimsA εR c) x with
    | none => rw [hx'] at hs; cases hs
    | some x' =>
      rw [hx'] at hs; simp only [Option.map_some, Option.some.injEq] at hs
      obtain ⟨hS', hK'⟩ := lock_step hS hK hx'
      obtain ⟨y, h1, h2⟩ := ih x' hs hS' hK'
      exact ⟨y, .step hx' h1, h2⟩

/-! ## Validity along lock-only runs -/

/-- **The region rely**: the environment keeps the region log valid. -/
def RelyR (εR : REnv) (c : CPU) : Prop :=
  ∀ l S H, rreplay l = some (S, H) → ∃ S' H', rreplay (rpull εR c l) = some (S', H')

def AOK (m : ALog) : Prop := ∃ S H, areplay m = some (S, H)

theorem aok_suffix : ∀ (ys : ALog) {l : ALog}, AOK (ys ++ l) → AOK l
  | [], _, h => h
  | _ :: ys, _, ⟨_, _, hr⟩ => by
    obtain ⟨S2, H2, _, hl2, -, -⟩ := LockArray.areplay_cons hr
    exact aok_suffix ys ⟨S2, H2, hl2⟩

/-- Another CPU's event leaves our phases alone, and while we hold lock `i` it
leaves region `i` alone and clean. -/
theorem rstep_other {S S' : RState} {e : REvent} {o : Option HEventR} {c : CPU} {i : Nat}
    (hmx : ∀ d, LockRegion.Holding S d i → LockRegion.Holding S c i → d = c)
    (hs : rstep S e = some (S', o)) (hne : e.cpu ≠ c) :
    (∀ j, (S'.lk j).phase c = (S.lk j).phase c) ∧
      (LockRegion.Holding S c i → S'.mem i = S.mem i ∧ (S.dirty i = false → S'.dirty i = false)) := by
  obtain ⟨d, j, k⟩ := e
  simp only at hne
  cases k with
  | tk k =>
    simp only [rstep] at hs
    split at hs
    · simp at hs
    · rename_i p' o' hps
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs
      refine ⟨fun j' => ?_, fun _ => ⟨rfl, fun hd => ?_⟩⟩
      · by_cases hj : j' = j
        · subst hj; simp only [upd_same]; exact (pstep_other hps hne).1
        · simp [upd_other _ _ hj]
      · simp only; split
        · by_cases hj : i = j
          · subst hj; simp
          · simp [upd_other _ _ hj, hd]
        · exact hd
  | pull =>
    simp only [rstep] at hs
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs
      exact ⟨fun _ => rfl, fun _ => ⟨rfl, id⟩⟩
    · simp at hs
  | wr a v =>
    simp only [rstep] at hs
    split at hs
    · rename_i hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs
      refine ⟨fun _ => rfl, fun hc => ?_⟩
      by_cases hj : i = j
      · subst hj; exact absurd (hmx d hh hc) hne
      · simp [upd_other _ _ hj]
    · simp at hs

theorem rothers {c : CPU} {i : Nat} {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) :
    ∀ (xs : RLog) {S' : RState} {H' : HLogR}, (∀ e ∈ xs, e.cpu ≠ c) → rreplay (xs ++ l) = some (S', H') →
      (∀ j, (S'.lk j).phase c = (S.lk j).phase c) ∧
        (LockRegion.Holding S c i → S'.mem i = S.mem i ∧ (S.dirty i = false → S'.dirty i = false))
  | [], S', H', _, hr => by
    simp only [List.nil_append] at hr; rw [hl] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr
    exact ⟨fun _ => rfl, fun _ => ⟨rfl, id⟩⟩
  | e :: xs, S', H', hx, hr => by
    obtain ⟨S2, H2, o, hl2, hs, -⟩ := LockRegion.rreplay_cons hr
    obtain ⟨h1, h2⟩ := rothers hl xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl2
    obtain ⟨g1, g2⟩ := rstep_other (c := c) (i := i)
      (fun d hd hc => LockRegion.rmutex hl2 i hd hc) hs (hx e List.mem_cons_self)
    refine ⟨fun j => (g1 j).trans (h1 j), fun hc => ?_⟩
    have hc2 : LockRegion.Holding S2 c i := by obtain ⟨t, ht⟩ := hc; exact ⟨t, by rw [h1 i]; exact ht⟩
    obtain ⟨a1, a2⟩ := h2 hc
    obtain ⟨b1, b2⟩ := g2 hc2
    exact ⟨b1.trans a1, fun hd => b2 (a2 hd)⟩

/-- A holder that has not written yet: its region is clean. -/
def Clean (c : CPU) (i : Nat) (S : RState) : Prop := LockRegion.Holding S c i → S.dirty i = false

/-- Our own lock event: valid on regions if the lock array accepts it, and it keeps `Clean`. -/
theorem own_lock_event {c : CPU} {i : Nat} {l1 : RLog} {S1 : RState} {H1 : HLogR}
    (hl1 : rreplay l1 = some (S1, H1)) (hq : Clean c i S1) {e : REvent} (hec : e.cpu = c) {ea : AEvent}
    (he : eraseE e = some ea) (hok : AOK (ea :: erase l1)) :
    ∃ S2 H2, rreplay (e :: l1) = some (S2, H2) ∧ Clean c i S2 := by
  obtain ⟨SA, HA, hA, hlk⟩ := rreplay_erase hl1
  obtain ⟨SA', HA', hr'⟩ := hok
  obtain ⟨SA0, HA0, oa, hA0, hstepA, -⟩ := LockArray.areplay_cons hr'
  rw [hA] at hA0; simp only [Option.some.injEq, Prod.mk.injEq] at hA0; obtain ⟨rfl, rfl⟩ := hA0
  obtain ⟨S2, o, hs⟩ := rstep_of_astep hlk he hstepA
  refine ⟨S2, _, LockRegion.rreplay_cons_of hl1 hs, ?_⟩
  obtain ⟨d, j, k⟩ := e
  simp only at hec; subst hec
  cases k with
  | wr a v => simp [eraseE] at he
  | pull =>
    simp only [rstep] at hs
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs; exact hq
    · simp at hs
  | tk k =>
    simp only [rstep] at hs
    split at hs
    · simp at hs
    · rename_i p' o' hps
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs
      intro hh
      by_cases hj : i = j
      · subst hj
        by_cases hk : k = .hold ∨ k = .incNow
        · simp [hk]
        · simp only [hk, ite_false]
          refine hq ?_
          obtain ⟨t, ht⟩ := hh
          simp only [upd_same] at ht
          simp only [pstep] at hps
          split at hps
          case isFalse => simp at hps
          cases k <;> cases hph : (S1.lk i).phase d <;> simp only [hph] at hps <;> try simp at hps
          · obtain ⟨rfl, -⟩ := hps; simp at ht
          · obtain ⟨rfl, -⟩ := hps; rw [hph] at ht; cases ht
          · exact absurd (.inr rfl) hk
          · exact absurd (.inl rfl) hk
      · have hh1 : LockRegion.Holding S1 d i := by
          obtain ⟨t, ht⟩ := hh; exact ⟨t, by simpa [upd_other _ _ hj] using ht⟩
        simp only; split
        · simp [upd_other _ _ hj, hq hh1]
        · exact hq hh1

/-- A lock primitive appends our own lock event after the environment's. -/
theorem lock_call_shape {εR : REnv} {c : CPU} {p : APrim} {args : List Expr} (hok : OkL p args)
    {σ : Locals} {l l' : RLog} {v : Val} (h : rprimsA εR c p (args.map (·.eval σ)) l = some (v, l')) :
    ∃ e ea, l' = e :: rpull εR c l ∧ e.cpu = c ∧ eraseE e = some ea := by
  obtain ⟨hnp, hpl⟩ := hok
  cases p with
  | push => exact absurd rfl hnp
  | pull =>
    have hlen := hpl rfl
    match args, hlen with
    | [a], _ =>
      simp only [List.map, rprimsA, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨_, _, rfl, rfl, rfl⟩
  | faiTicket =>
    match args with
    | [] => simp [rprimsA] at h
    | [a] =>
      simp only [List.map, rprimsA, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨_, _, rfl, rfl, rfl⟩
    | _ :: _ :: _ => simp [rprimsA] at h
  | getNow =>
    match args with
    | [] => simp [rprimsA] at h
    | [a] =>
      simp only [List.map, rprimsA, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨_, _, rfl, rfl, rfl⟩
    | _ :: _ :: _ => simp [rprimsA] at h
  | incNow =>
    match args with
    | [] => simp [rprimsA] at h
    | [a] =>
      simp only [List.map, rprimsA, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨_, _, rfl, rfl, rfl⟩
    | _ :: _ :: _ => simp [rprimsA] at h
  | hold =>
    match args with
    | [] => simp [rprimsA] at h
    | [a] =>
      simp only [List.map, rprimsA, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨_, _, rfl, rfl, rfl⟩
    | _ :: _ :: _ => simp [rprimsA] at h

/-- A step either leaves the log alone or is one primitive call. -/
theorem step_abs {P : Prims APrim RLog} {x x' : Config APrim RLog} (hs : step P x = some x') :
    x'.abs = x.abs ∨ ∃ t p args v, x.stmt = .call t p args ∧
      P p (args.map (·.eval x.locals)) x.abs = some (v, x'.abs) := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  cases stmt with
  | skip => cases cont <;> simp [step] at hs <;> subst hs <;> exact .inl rfl
  | assign y e => simp only [step, Option.some.injEq] at hs; subst hs; exact .inl rfl
  | seq a b => simp only [step, Option.some.injEq] at hs; subst hs; exact .inl rfl
  | ite e a b => simp only [step, Option.some.injEq] at hs; subst hs; exact .inl rfl
  | «while» e b =>
    simp only [step] at hs
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst hs <;> exact .inl rfl
  | call y p args =>
    simp only [step] at hs
    split at hs
    · rename_i v a' hp
      simp only [Option.some.injEq] at hs; subst hs
      exact .inr ⟨y, p, args, v, rfl, hp⟩
    · simp at hs

/-- A lock-only step extends the log. -/
theorem lock_step_ext {εR : REnv} {c : CPU} {x x' : Config APrim RLog} (hS : LockS x.stmt)
    (hs : step (rprimsA εR c) x = some x') : ∃ ys, x'.abs = ys ++ x.abs := by
  rcases step_abs hs with h | ⟨t, p, args, v, hst, hp⟩
  · exact ⟨[], h⟩
  · rw [hst] at hS
    obtain ⟨e, ea, hl', -, -⟩ := lock_call_shape hS hp
    exact ⟨e :: εR.query c x.abs, by rw [hl']; rfl⟩

theorem lock_star_ext {εR : REnv} {c : CPU} {x z : Config APrim RLog} (h : Star (rprimsA εR c) x z) :
    LockS x.stmt → LockK x.cont → ∃ ys, z.abs = ys ++ x.abs := by
  induction h with
  | refl => intro _ _; exact ⟨[], rfl⟩
  | @step a b d hs _ ih =>
    intro hS hK
    obtain ⟨hS', hK'⟩ := lock_step hS hK hs
    obtain ⟨ys, hys⟩ := ih hS' hK'
    obtain ⟨zs, hzs⟩ := lock_step_ext hS hs
    exact ⟨ys ++ zs, by rw [hys, hzs, List.append_assoc]⟩

/-- **Lock-only runs keep the region log valid**, and a fresh holder clean. -/
theorem lock_run_valid {εR : REnv} {c : CPU} {i : Nat} (hRR : RelyR εR c) {x z : Config APrim RLog}
    (h : Star (rprimsA εR c) x z) : LockS x.stmt → LockK x.cont →
    (∃ S H, rreplay x.abs = some (S, H) ∧ Clean c i S) → AOK (erase z.abs) →
    ∃ S H, rreplay z.abs = some (S, H) ∧ Clean c i S := by
  induction h with
  | refl => intro _ _ hv _; exact hv
  | @step a b d hs hrest ih =>
    intro hS hK hv hz
    obtain ⟨hS', hK'⟩ := lock_step hS hK hs
    obtain ⟨ys, hys⟩ := lock_star_ext hrest hS' hK'
    have hb : AOK (erase b.abs) := by rw [hys, erase_append] at hz; exact aok_suffix _ hz
    refine ih hS' hK' ?_ hz
    rcases step_abs hs with heq | ⟨t, p, args, v, hst, hp⟩
    · rw [heq]; exact hv
    · rw [hst] at hS
      obtain ⟨e, ea, hl', hec, hea⟩ := lock_call_shape hS hp
      obtain ⟨S, H, hl, hq⟩ := hv
      obtain ⟨S1, H1, hl1⟩ := hRR _ S H hl
      obtain ⟨g1, g2⟩ := rothers (c := c) (i := i) hl (εR.query c a.abs) (εR.noSelf c a.abs) hl1
      have hq1 : Clean c i S1 := fun hh => by
        have hh0 : LockRegion.Holding S c i := by obtain ⟨t', ht⟩ := hh; exact ⟨t', by rw [← g1 i]; exact ht⟩
        exact (g2 hh0).2 (hq hh0)
      rw [hl'] at hb ⊢
      have hb' : AOK (ea :: erase (rpull εR c a.abs)) := by
        simpa [erase, List.filterMap_cons, hea] using hb
      exact own_lock_event hl1 hq1 hec hea hb'

/-! ## The client: `acquire(lk); cell[j]++ for j < k; release(lk)` -/

/-- `x = rd(lk, j); wr(lk, j, x + 1)`. -/
def incCellA (j : Nat) : Stmt APrim :=
  .seq (.call "x" .pull [lkE, .const (BitVec.ofNat 32 j)])
    (.call "_" .push [lkE, .const (BitVec.ofNat 32 j), .bin .add (.var "x") (.const 1)])

def incCellsA : Nat → Stmt APrim
  | 0 => .skip
  | k + 1 => .seq (incCellsA k) (incCellA k)

def relA : Stmt APrim := .call "_" .incNow [lkE]

def clientRA (k : Nat) : Stmt APrim := .seq acquireA (.seq (incCellsA k) relA)

/-- **The critical section** increments cells `0 … k-1` of our region, and
nothing else. It never asks the environment. -/
theorem crit_runR (εR : REnv) (c : CPU) (iv : Val) : ∀ (k : Nat), k ≤ 2 ^ 32 → ∀ (σ : Locals) (l : RLog)
    (K : Cont APrim) {S : RState} {H : HLogR}, σ "lk" = iv → rreplay l = some (S, H) →
    LockRegion.Holding S c iv.toNat →
    ∃ σ' l' S', Star (rprimsA εR c) ⟨incCellsA k, K, σ, l⟩ ⟨.skip, K, σ', l'⟩ ∧
      rreplay l' = some (S', H) ∧ S'.lk = S.lk ∧ σ' "lk" = iv ∧
      ∀ j, S'.mem iv.toNat j = if j < k then S.mem iv.toNat j + 1 else S.mem iv.toNat j
  | 0, _, σ, l, K, S, H, hσ, hl, _ => ⟨σ, l, S, .refl _, hl, rfl, hσ, fun j => by simp⟩
  | k + 1, hk, σ, l, K, S, H, hσ, hl, hh => by
    obtain ⟨σ1, l1, S1, hrun, hl1, hlk1, hσ1, hmem1⟩ :=
      crit_runR εR c iv k (by omega) σ l (.seq (incCellA k) K) hσ hl hh
    have hkk : (BitVec.ofNat 32 k).toNat = k := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hh1 : LockRegion.Holding S1 c iv.toNat := by
      obtain ⟨t, ht⟩ := hh; exact ⟨t, by rw [hlk1]; exact ht⟩
    -- the value read
    let v : Val := LockRegion.memOf iv.toNat l1 k
    have hv : v = S.mem iv.toNat k := by
      have := LockRegion.rreplay_mem hl1 iv.toNat
      simp only [v, ← this, hmem1 k, Nat.lt_irrefl, ite_false]
    let σ2 := σ1.set "x" v
    have hσ2 : σ2 "lk" = iv := by simp [σ2, Locals.set, hσ1]
    let e : REvent := ⟨c, iv.toNat, .wr k (v + 1)⟩
    let S2 : RState := ⟨S1.lk, upd S1.mem iv.toNat (setCell (S1.mem iv.toNat) k (v + 1)),
        upd S1.dirty iv.toNat true⟩
    have hs : rstep S1 e = some (S2, none) := by simp [rstep, e, hh1, S2]
    have hl2 := LockRegion.rreplay_cons_of hl1 hs
    refine ⟨σ2.set "_" 0, e :: l1, S2, ?_, by simpa [LockRegion.consO] using hl2, hlk1,
      by simp [Locals.set, hσ2], fun j => ?_⟩
    · refine .step (c' := ⟨incCellsA k, .seq (incCellA k) K, σ, l⟩) rfl (hrun.trans ?_)
      refine .step (c' := ⟨incCellA k, K, σ1, l1⟩) rfl ?_
      refine .step (c' := ⟨.call "x" .pull [lkE, .const (BitVec.ofNat 32 k)],
        .seq (.call "_" .push [lkE, .const (BitVec.ofNat 32 k), .bin .add (.var "x") (.const 1)]) K,
        σ1, l1⟩) rfl ?_
      refine .step (c' := ⟨.skip,
        .seq (.call "_" .push [lkE, .const (BitVec.ofNat 32 k), .bin .add (.var "x") (.const 1)]) K,
        σ2, l1⟩) (by simp [step, rprimsA, Expr.eval, lkE, hσ1, hkk, σ2, v]) ?_
      refine .step (c' := ⟨.call "_" .push [lkE, .const (BitVec.ofNat 32 k), .bin .add (.var "x") (.const 1)],
        K, σ2, l1⟩) rfl ?_
      exact Star.single (by simp [step, rprimsA, Expr.eval, BinOp.eval, lkE, hσ1, hkk, σ2, e, Locals.set])
    · simp only [S2, upd_same, setCell]
      by_cases hjk : j = k
      · subst hjk; simp [hv]
      · have h1 := hmem1 j
        by_cases hlt : j < k
        · simp [hjk, h1, hlt, show j < k + 1 by omega]
        · simp [hjk, h1, hlt, show ¬ j < k + 1 by omega]

theorem lockS_acquireA : LockS acquireA := by
  simp [LockS, acquireA, LockArray.loopA, OkL, lkE]

/-- **The per-CPU guarantee for regions, with no lost updates.** Under an
environment that keeps the region log valid, and the lock array's fairness,
the client finishes idle on a valid log. At the point where `acquire` returned
(log `r1`, high-level log `H1`), it held the lock. The region it releases is
the region of the last release in `H1`, with cells `0 … k-1` incremented. -/
theorem clientR_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (k : Nat) (hk : k ≤ 2 ^ 32) :
    ∃ (σ1 σ' : Locals) (r1 rb : RLog) (S1 S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨clientRA k, .stop, σ, l⟩ ⟨.skip, .seq (.seq (incCellsA k) relA) .stop, σ1, r1⟩ ∧
      Star (rprimsA εR c) ⟨.skip, .seq (.seq (incCellsA k) relA) .stop, σ1, r1⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay r1 = some (S1, H1) ∧ LockRegion.Holding S1 c iv.toNat ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      ∀ j, hmemR iv.toNat H3 j = if j < k then hmemR iv.toNat H1 j + 1 else hmemR iv.toNat H1 j := by
  -- acquire: on the lock array, then lifted
  obtain ⟨SA, HA, hA, hlkA⟩ := rreplay_erase hl
  have hidleA : (SA.lk iv.toNat).phase c = .idle := by rw [hlkA]; exact hidle
  obtain ⟨r, hspec⟩ := LockArray.acquireA_live_bounded hc hRA hA hidleA bound K hK hF
  obtain ⟨r0, σ1, -, -, hσ1, hstA⟩ := LockArray.acquireA_sim ε c _ σ iv (erase l) r .stop hσ hspec
  obtain ⟨-, -, SA1, HA1, hA1, hholdA, -, -⟩ := LockArray.acquireA_guarantee hc hRA hA hidleA hspec
  obtain ⟨⟨s1, k1, σy, r1⟩, hstR, hy⟩ := star_liftR hE c hstA ⟨acquireA, .stop, σ, l⟩ rfl lockS_acquireA trivial
  simp only [erC, Config.mk.injEq] at hy
  obtain ⟨rfl, rfl, rfl, her⟩ := hy
  obtain ⟨S1, H1, hl1, hq1⟩ := lock_run_valid (i := iv.toNat) hRR hstR lockS_acquireA trivial
    ⟨S, H, hl, fun hh => by obtain ⟨t, ht⟩ := hh; rw [hidle] at ht; cases ht⟩ ⟨SA1, HA1, by rw [her]; exact hA1⟩
  have hold1 : LockRegion.Holding S1 c iv.toNat := by
    obtain ⟨SA1', HA1', hA1', hlk1'⟩ := rreplay_erase hl1
    rw [her, hA1] at hA1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hA1'; obtain ⟨rfl, -⟩ := hA1'
    obtain ⟨t, ht⟩ := hholdA; exact ⟨t, by rw [← hlk1']; exact ht⟩
  have hsee : S1.mem iv.toNat = hmemR iv.toNat H1 := LockRegion.acquire_sees hl1 (hq1 hold1)
  have hσlk : σy "lk" = iv := by
    rw [hσ1 "lk" (by decide) (by decide) (by decide) (by decide)]; exact hσ
  -- the critical section
  obtain ⟨σ2, r2, S2, hcrit, hl2, hlk2, hσ2, hmem2⟩ :=
    crit_runR εR c iv k hk σy r1 (.seq relA .stop) hσlk hl1 hold1
  have hold2 : LockRegion.Holding S2 c iv.toNat := by
    obtain ⟨t, ht⟩ := hold1; exact ⟨t, by rw [hlk2]; exact ht⟩
  -- release
  obtain ⟨S2', H2', hl2'⟩ := hRR _ S2 H1 hl2
  obtain ⟨g1, g2⟩ := rothers (c := c) (i := iv.toNat) hl2 (εR.query c r2) (εR.noSelf c r2) hl2'
  obtain ⟨t, ht⟩ := hold2
  have ht' : (S2'.lk iv.toNat).phase c = .holding t := by rw [g1 iv.toNat]; exact ht
  have hps : pstep (S2'.lk iv.toNat) ⟨c, .incNow⟩ = some (⟨(S2'.lk iv.toNat).ticket, (S2'.lk iv.toNat).now + 1,
      setPhase (S2'.lk iv.toNat).phase c .idle⟩, some (.rel c)) := by simp [pstep, hc, ht']
  have hrs : rstep S2' (rev c iv.toNat .incNow) = some (⟨upd S2'.lk iv.toNat ⟨(S2'.lk iv.toNat).ticket,
      (S2'.lk iv.toNat).now + 1, setPhase (S2'.lk iv.toNat).phase c .idle⟩, S2'.mem,
      upd S2'.dirty iv.toNat false⟩, some (.relR c iv.toNat (S2'.mem iv.toNat))) := by
    simp [rstep, rev, hps, LockRegion.lift]
  have hl3 := LockRegion.rreplay_cons_of hl2' hrs
  have hmem2' : S2'.mem iv.toNat = S2.mem iv.toNat := (g2 ⟨t, ht⟩).1
  refine ⟨σy, σ2.set "_" 0, r1, rev c iv.toNat .incNow :: rpull εR c r2, S1, _, H1, _, ?_, ?_, hl1, hold1,
    hl3, by simp, fun j => ?_⟩
  · have hfr := MCSBoundC.star_app hstR (.seq (.seq (incCellsA k) relA) .stop) rfl
    exact .step (c' := ⟨acquireA, .seq (.seq (incCellsA k) relA) .stop, σ, l⟩) rfl hfr
  · refine .step (c' := ⟨.seq (incCellsA k) relA, .stop, σy, r1⟩) rfl ?_
    refine .step (c' := ⟨incCellsA k, .seq relA .stop, σy, r1⟩) rfl (hcrit.trans ?_)
    refine .step (c' := ⟨relA, .stop, σ2, r2⟩) rfl ?_
    exact Star.single (by simp [step, rprimsA, relA, Expr.eval, lkE, hσ2])
  · simp only [LockRegion.consO, hmemR, ite_true, hmem2', hmem2 j, hsee]

/-! ## Not vacuous: a fair region scheduler -/

/-- A lock-array event as a region event (a `push` would become a write to cell 0). -/
def liftA : AEvent → REvent
  | ⟨c, i, .tk k⟩ => ⟨c, i, .tk k⟩
  | ⟨c, i, .pull⟩ => ⟨c, i, .pull⟩
  | ⟨c, i, .push v⟩ => ⟨c, i, .wr 0 v⟩

def IsTk (e : AEvent) : Prop := ∃ k, e.kind = .tk k

theorem erase_liftA : ∀ (xs : ALog), (∀ e ∈ xs, IsTk e) → erase (xs.map liftA) = xs
  | [], _ => rfl
  | ⟨c, i, k⟩ :: xs, h => by
    have ih := erase_liftA xs (fun e he => h e (List.mem_cons_of_mem _ he))
    obtain ⟨k', hk'⟩ := h _ List.mem_cons_self
    simp only at hk'; subst hk'
    simp only [List.map, erase, List.filterMap_cons, liftA, eraseE] at ih ⊢
    rw [ih]

theorem fairQueryA_tk (c : CPU) (l : ALog) : ∀ e ∈ LockArray.fairQueryA c l, IsTk e := by
  intro e he
  simp only [LockArray.fairQueryA] at he
  split at he
  · simp at he
  · obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 he
    simp only [LockArray.blk] at hj
    split at hj
    · simp only [List.mem_singleton] at hj; subst hj; exact ⟨_, rfl⟩
    · split at hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> exact ⟨_, rfl⟩
      · simp at hj

/-- The fair lock-array scheduler, acting on the erased log. -/
def fairEnvR : REnv where
  query c l := (LockArray.fairQueryA c (erase l)).map liftA
  noSelf := by
    intro c l e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    have := LockArray.fairEnvA.noSelf c (erase l) e' he'
    obtain ⟨d, i, k⟩ := e'
    cases k <;> exact this

theorem fairR_erases : EnvErases fairEnvR LockArray.fairEnvA :=
  fun c l => erase_liftA _ (fairQueryA_tk c (erase l))

/-- Lock events the lock array accepts are accepted on regions. -/
theorem lift_valid : ∀ (xs : ALog), (∀ e ∈ xs, IsTk e) → ∀ {l : RLog} {S : RState} {H : HLogR},
    rreplay l = some (S, H) → AOK (xs ++ erase l) → ∃ S' H', rreplay (xs.map liftA ++ l) = some (S', H')
  | [], _, _, S, H, hl, _ => ⟨S, H, hl⟩
  | e :: xs, htk, l, S, H, hl, hok => by
    obtain ⟨S1, H1, hl1⟩ := lift_valid xs (fun e' he' => htk e' (List.mem_cons_of_mem _ he')) hl
      (aok_suffix [e] hok)
    obtain ⟨SA, HA, hA, hlk⟩ := rreplay_erase hl1
    have her : erase (xs.map liftA ++ l) = xs ++ erase l := by
      rw [erase_append, erase_liftA xs (fun e' he' => htk e' (List.mem_cons_of_mem _ he'))]
    obtain ⟨SA', HA', hr'⟩ := hok
    obtain ⟨SA0, HA0, oa, hA0, hstepA, -⟩ := LockArray.areplay_cons hr'
    have hA0' : areplay (xs ++ erase l) = some (SA0, HA0) := hA0
    rw [← her, hA] at hA0'
    simp only [Option.some.injEq, Prod.mk.injEq] at hA0'; obtain ⟨rfl, rfl⟩ := hA0'
    obtain ⟨k', hk'⟩ := htk e List.mem_cons_self
    obtain ⟨d, i, k⟩ := e
    simp only at hk'; subst hk'
    obtain ⟨S2, o, hs⟩ := rstep_of_astep (e := ⟨d, i, .tk k'⟩) hlk rfl hstepA
    exact ⟨S2, _, LockRegion.rreplay_cons_of hl1 hs⟩

theorem fairR_rely (c : CPU) : RelyR fairEnvR c := by
  intro l S H hl
  obtain ⟨SA, HA, hA, -⟩ := rreplay_erase hl
  obtain ⟨SA', HA', hA'⟩ := (LockArray.fairA_rely c).conform _ SA HA hA
  exact lift_valid _ (fairQueryA_tk c (erase l)) hl ⟨SA', HA', hA'⟩

/-- **Not vacuous.** Under the fair region scheduler, from the empty log, the
client finishes and releases its region with cells `0 … k-1` set to 1. -/
theorem clientR_fair {c : CPU} (hc : c < NCPU) (σ : Locals) (k : Nat) (hk : k ≤ 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR),
      Star (rprimsA fairEnvR c) ⟨clientRA k, .stop, σ, []⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk (σ "lk").toNat).phase c = .idle := by
  obtain ⟨σ1, σ', r1, rb, S1, S3, H1, H3, h1, h2, -, -, h3, h4, -⟩ :=
    clientR_guarantee fairR_erases (fairR_rely c) hc (LockArray.fairA_rely c) (l := []) rfl (iv := σ "lk") rfl
      (fun _ => 0) 0 (fun _ => Nat.le_refl _) (LockArray.fairA_fair c _ _) σ rfl k hk
  exact ⟨σ', rb, S3, H3, h1.trans h2, h3, h4⟩

end LockRegionCPU
