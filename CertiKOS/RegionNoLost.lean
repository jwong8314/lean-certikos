import CertiKOS.RegionLive

/-!
# No lost updates for lock regions on the multicore machine

Each CPU `c` runs `acquire(L c); cell[j]++ for j < nc; release(L c)` on the
global region log. CPUs that share a lock update the same cells.

* `wrT t`: the writes still to come in a thread's code. A step keeps it,
  except a write, which lowers it by one (`step_wr`).
* `GD`: the data invariant. Cell `j` of region `i` holds the number of CPUs on
  lock `i` that have already written it (those with `j + wrT < nc`).
* `gd_step`: every multicore step keeps it. A write is by the holder at its
  current cell, and the value it read is still the cell's contents, because
  nobody else can write while it holds the lock.
* `no_lost_updates_R`: **when every CPU has finished, each of the first `nc`
  cells of region `i` holds exactly the number of CPUs that used lock `i`.**
-/

namespace RegionNoLost

open ClightL Ticket ClightToPy TicketLive
open LockArray (APrim acquireA loopA lkE upd upd_same upd_other)
open ArrayLinkClient (holdPullS lgEA gnA restS)
open LockRegion (REvent RLog RState HLogR HEventR RKind Region rreplay rstep rev noEnvR rpull setCell)
open LockRegionCPU (rprimsA incCellA relA)
open RegionLive

/-! ## Counting the writes still to come -/

def wrS : Stmt APrim → Nat
  | .seq a b => wrS a + wrS b
  | .ite _ a b => wrS a + wrS b
  | .while _ b => wrS b
  | .call _ .push _ => 1
  | _ => 0

def wrK : Cont APrim → Nat
  | .stop => 0
  | .seq s k => wrS s + wrK k
  | .loop _ b k => wrS b + wrK k

def wrT (t : CThread APrim) : Nat := wrS t.stmt + wrK t.cont

def isPush : Stmt APrim → Bool
  | .call _ .push _ => true
  | _ => false

/-- Branches and loop bodies contain no writes. -/
def NoBrS : Stmt APrim → Prop
  | .seq a b => NoBrS a ∧ NoBrS b
  | .ite _ a b => wrS a = 0 ∧ wrS b = 0
  | .while _ b => wrS b = 0
  | _ => True

def NoBrK : Cont APrim → Prop
  | .stop => True
  | .seq s k => NoBrS s ∧ NoBrK k
  | .loop _ b k => wrS b = 0 ∧ NoBrK k

theorem noBr_of_zero : ∀ {s : Stmt APrim}, wrS s = 0 → NoBrS s
  | .skip, _ => trivial
  | .assign _ _, _ => trivial
  | .seq a b, h => by
    simp only [wrS] at h
    exact ⟨noBr_of_zero (by omega), noBr_of_zero (by omega)⟩
  | .ite _ a b, h => by simp only [wrS] at h; exact ⟨by omega, by omega⟩
  | .while _ b, h => by simp only [wrS] at h; exact h
  | .call _ _ _, _ => trivial

/-- **A step keeps the writes to come, except a write, which uses one.** -/
theorem step_wr {P : Prims APrim RLog} {x x' : Config APrim RLog} (hS : NoBrS x.stmt) (hK : NoBrK x.cont)
    (hs : step P x = some x') :
    NoBrS x'.stmt ∧ NoBrK x'.cont ∧
      wrS x'.stmt + wrK x'.cont + (if isPush x.stmt then 1 else 0) = wrS x.stmt + wrK x.cont := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  cases stmt with
  | skip =>
    cases cont with
    | stop => simp [step] at hs
    | seq s k => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hK.1, hK.2, by simp [wrS, wrK, isPush]⟩
    | loop e b k =>
      simp only [step, Option.some.injEq] at hs; subst hs
      exact ⟨hK.1, hK.2, by simp [wrS, wrK, isPush]⟩
  | assign y e =>
    simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨trivial, hK, by simp [wrS, isPush]⟩
  | seq a b =>
    simp only [step, Option.some.injEq] at hs; subst hs
    exact ⟨hS.1, ⟨hS.2, hK⟩, by simp [wrS, wrK, isPush]; omega⟩
  | ite e a b =>
    simp only [step, Option.some.injEq] at hs; subst hs
    obtain ⟨ha, hb⟩ := hS
    refine ⟨?_, hK, ?_⟩
    · simp only; split
      · exact noBr_of_zero hb
      · exact noBr_of_zero ha
    · simp only [wrS, isPush]; split <;> simp [ha, hb]
  | «while» e b =>
    simp only [step] at hs
    have hb : wrS b = 0 := hS
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst hs
    · exact ⟨trivial, hK, by simp [wrS, isPush, hb]⟩
    · exact ⟨noBr_of_zero hb, ⟨hb, hK⟩, by simp [wrS, wrK, isPush, hb]⟩
  | call y p args =>
    simp only [step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      refine ⟨trivial, hK, ?_⟩
      cases p <;> simp [wrS, isPush] <;> omega
    · simp at hs

theorem wrS_incFrom : ∀ (r m : Nat), wrS (incFrom m r) = r
  | 0, _ => rfl
  | r + 1, m => by simp [incFrom, wrS, incCellA_eq, rdC, wrC, wrS_incFrom r]; omega

theorem noBr_incFrom : ∀ (r m : Nat), NoBrS (incFrom m r)
  | 0, _ => trivial
  | r + 1, m => ⟨⟨trivial, trivial⟩, noBr_incFrom r (m + 1)⟩

theorem wrS_client (nc : Nat) : wrS (clientM nc) = nc := by
  simp [clientM, wrS, wrS_incFrom, acquireA, loopA, relA]

theorem noBr_client (nc : Nat) : NoBrS (clientM nc) := by
  refine ⟨?_, noBr_incFrom nc 0, trivial⟩
  simp [acquireA, loopA, NoBrS, wrS]

/-! ## Steps that are not writes leave the regions alone -/

theorem step_mem {c : CPU} {x x' : Config APrim RLog} (hs : step (rprimsA noEnvR c) x = some x')
    (hnp : isPush x.stmt = false) {S S' : RState} {H H' : HLogR} (hl : rreplay x.abs = some (S, H))
    (hl' : rreplay x'.abs = some (S', H')) : S'.mem = S.mem := by
  rcases LockRegionCPU.step_abs hs with heq | ⟨t, p, args, v, hst, hp⟩
  · rw [heq, hl] at hl'; simp only [Option.some.injEq, Prod.mk.injEq] at hl'; rw [hl'.1]
  · have key : x'.abs = x.abs ∨ ∃ e, x'.abs = e :: x.abs ∧ ∀ a v, e.kind ≠ .wr a v := by
      cases p with
      | push => rw [hst] at hnp; simp [isPush] at hnp
      | pull =>
        rcases hargs : args.map (·.eval x.locals) with _ | ⟨a, _ | ⟨b, _ | ⟨d, tl⟩⟩⟩ <;>
          rw [hargs] at hp <;> simp only [rprimsA, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hp
        · obtain ⟨-, h⟩ := hp; exact .inr ⟨_, h.symm, by simp⟩
        · obtain ⟨-, h⟩ := hp; exact .inl h.symm
      | faiTicket =>
        rcases hargs : args.map (·.eval x.locals) with _ | ⟨a, _ | ⟨b, tl⟩⟩ <;>
          rw [hargs] at hp <;> simp only [rprimsA, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hp
        obtain ⟨-, h⟩ := hp; exact .inr ⟨_, h.symm, by simp [rev]⟩
      | getNow =>
        rcases hargs : args.map (·.eval x.locals) with _ | ⟨a, _ | ⟨b, tl⟩⟩ <;>
          rw [hargs] at hp <;> simp only [rprimsA, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hp
        obtain ⟨-, h⟩ := hp; exact .inr ⟨_, h.symm, by simp [rev]⟩
      | incNow =>
        rcases hargs : args.map (·.eval x.locals) with _ | ⟨a, _ | ⟨b, tl⟩⟩ <;>
          rw [hargs] at hp <;> simp only [rprimsA, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hp
        obtain ⟨-, h⟩ := hp; exact .inr ⟨_, h.symm, by simp [rev]⟩
      | hold =>
        rcases hargs : args.map (·.eval x.locals) with _ | ⟨a, _ | ⟨b, tl⟩⟩ <;>
          rw [hargs] at hp <;> simp only [rprimsA, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hp
        obtain ⟨-, h⟩ := hp; exact .inr ⟨_, h.symm, by simp [rev]⟩
    rcases key with heq | ⟨e, heq, hne⟩
    · rw [heq, hl] at hl'; simp only [Option.some.injEq, Prod.mk.injEq] at hl'; rw [hl'.1]
    · rw [heq] at hl'
      obtain ⟨S0, H0, o, hl0, hp0, -⟩ := LockRegion.rreplay_cons hl'
      rw [hl] at hl0; simp only [Option.some.injEq, Prod.mk.injEq] at hl0; obtain ⟨rfl, rfl⟩ := hl0
      obtain ⟨d, j, k⟩ := e
      cases k with
      | wr a v => exact absurd rfl (hne a v)
      | pull =>
        simp only [rstep] at hp0; split at hp0
        · simp only [Option.some.injEq, Prod.mk.injEq] at hp0; rw [← hp0.1]
        · simp at hp0
      | tk k =>
        simp only [rstep] at hp0; split at hp0
        · simp at hp0
        · simp only [Option.some.injEq, Prod.mk.injEq] at hp0; rw [← hp0.1]

/-- A thread about to write is at its current cell, holding, with the cell's contents in `x`. -/
theorem at_wr {nc : Nat} {iv : Val} {c : CPU} {p : PState} {b : Region} {t : CThread APrim} {w : Nat}
    (hA : AtW nc iv c p b t w) (hp : isPush t.stmt = true) :
    ∃ σ tn m r, t = ⟨wrC m, .seq (incFrom (m + 1) r) KC, σ⟩ ∧ σ "lk" = iv ∧ p.phase c = .holding tn ∧
      m + r + 1 = nc ∧ σ "x" = b (BitVec.ofNat 32 m).toNat := by
  cases hA with
  | c5 hk h hm hx => exact ⟨_, _, _, _, rfl, hk, h, hm, hx⟩
  | @c1 σ tn m r hk h hm => cases r <;> simp [incFrom, isPush] at hp
  | _ => simp [isPush, clientM, incCellA_eq, rdC, relA, acquireA, restS, gnA, holdPullS, loopA] at hp

/-! ## The data invariant -/

def wrAt (cs : List (CThread APrim)) (c : Nat) : Nat :=
  match cs[c]? with
  | some t => wrT t
  | none => 0

/-- CPUs on lock `i` that have already written cell `j`. -/
def wrote (nc T : Nat) (L : Nat → Val) (cs : List (CThread APrim)) (i j : Nat) : Nat :=
  Ticket.cnt (fun c => decide ((L c).toNat = i ∧ j + wrAt cs c < nc)) T

def GD (nc T : Nat) (L : Nat → Val) (cs : List (CThread APrim)) (l : RLog) : Prop :=
  (∃ Φ, GL nc T L cs l Φ) ∧ (∀ c (hc : c < cs.length), NoBrS cs[c].stmt ∧ NoBrK cs[c].cont) ∧
    ∀ S H, rreplay l = some (S, H) → ∀ i j, S.mem i j = BitVec.ofNat 32 (wrote nc T L cs i j)

theorem gd_init (nc T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) : GD nc T L (poolR nc T L) [] := by
  refine ⟨⟨_, gl_init nc T L hT⟩, fun c hc => ?_, fun S H hr i j => ?_⟩
  · simp only [poolR, List.getElem_map, List.getElem_range]
    exact ⟨noBr_client nc, trivial⟩
  · simp only [rreplay, Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr
    have : wrote nc T L (poolR nc T L) i j = 0 := by
      unfold wrote
      rw [Ticket.cnt_congr (g' := fun _ => false) T (fun c hc => ?_)]
      · exact Ticket.cnt_zero (fun _ => rfl) T
      · have : wrAt (poolR nc T L) c = nc := by
          simp [wrAt, poolR, hc, wrT, wrS_client, wrK]
        simp [this]
    rw [this]; rfl

theorem wrAt_set_self {cs : List (CThread APrim)} {a : Nat} (ha : a < cs.length) (t : CThread APrim) :
    wrAt (cs.set a t) a = wrT t := by simp [wrAt, ha]

theorem wrAt_set_ne {cs : List (CThread APrim)} {a c : Nat} (h : c ≠ a) (t : CThread APrim) :
    wrAt (cs.set a t) c = wrAt cs c := by simp [wrAt, List.getElem?_set_ne (Ne.symm h)]

theorem wrAt_self {cs : List (CThread APrim)} {a : Nat} (ha : a < cs.length) : wrAt cs a = wrT cs[a] := by
  simp [wrAt, ha]

/-- **Every multicore step keeps the data invariant.** -/
theorem gd_step {nc T : Nat} {L : Nat → Val} (hnc : nc ≤ 2 ^ 32) {a : Nat} {cs cs' : List (CThread APrim)}
    {l l' : RLog} (hG : GD nc T L cs l) (hS : CStepI PGR a cs l cs' l') : GD nc T L cs' l' := by
  obtain ⟨⟨Φ, hGL⟩, hnb, hdata⟩ := hG
  obtain ⟨Φ', hGL', -⟩ := gstepW hGL hS
  obtain ⟨S, H, ws, hl, hlen, hT, hev, hAt, -, -⟩ := id hGL
  obtain ⟨S', H', -, hl', -⟩ := id hGL'
  obtain ⟨ha, c', hst, rfl, rfl⟩ := hS
  have haT : a < T := hlen ▸ ha
  obtain ⟨hnS, hnK⟩ := hnb a ha
  obtain ⟨hnS', hnK', hcount⟩ := step_wr (x := cs[a].cfg l) hnS hnK hst
  simp only [CThread.cfg] at hcount
  have hwa : wrAt (cs.set a (thr c')) a = wrS c'.stmt + wrK c'.cont := by
    rw [wrAt_set_self ha]; rfl
  have hwa0 : wrAt cs a = wrS cs[a].stmt + wrK cs[a].cont := wrAt_self ha
  refine ⟨⟨Φ', hGL'⟩, fun c hc => ?_, fun S2 H2 hr2 i j => ?_⟩
  · by_cases hca : c = a
    · subst hca; simp only [List.getElem_set_self]; exact ⟨hnS', hnK'⟩
    · simp only [List.getElem_set_ne (Ne.symm hca)]; exact hnb c (by simpa using hc)
  · rw [hl'] at hr2; simp only [Option.some.injEq, Prod.mk.injEq] at hr2; obtain ⟨rfl, -⟩ := hr2
    have hold := hdata S H hl i j
    by_cases hpush : isPush cs[a].stmt = true
    · -- a write: by the holder, at its current cell
      obtain ⟨σ, tn, m, r, hthr, hlk, hph, hm, hx⟩ := at_wr (hAt a ha) hpush
      have hmlt : m < 2 ^ 32 := by omega
      have hkk : (BitVec.ofNat 32 m).toNat = m := by
        simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hmlt
      rw [hkk] at hx
      have hst' : step (rprimsA noEnvR a) ⟨wrC m, .seq (incFrom (m + 1) r) KC, σ, l⟩ = some c' := by
        have := hst; rw [hthr] at this; exact this
      simp only [step, wrC, rprimsA, lkE, List.map, Expr.eval, BinOp.eval, hlk, hkk,
        Option.some.injEq] at hst'
      subst hst'
      have hrs : rstep S ⟨a, (L a).toNat, .wr m (σ "x" + 1)⟩ = some (⟨S.lk, upd S.mem (L a).toNat
          (setCell (S.mem (L a).toNat) m (σ "x" + 1)), upd S.dirty (L a).toNat true⟩, none) := by
        simp [rstep, LockRegion.Holding, hph]
      have hl2 := LockRegion.rreplay_cons_of hl hrs
      have hl'' : rreplay (⟨a, (L a).toNat, .wr m (σ "x" + 1)⟩ :: l) = some (S', H') := hl'
      rw [hl2] at hl''
      simp only [Option.some.injEq, Prod.mk.injEq] at hl''
      obtain ⟨rfl, -⟩ := hl''
      -- the counts
      have hw0 : wrAt cs a = r + 1 := by
        rw [hwa0, hthr]; simp [wrS, wrK, wrC, wrS_incFrom, KC, relA]; omega
      have hw1 : wrAt (cs.set a (thr ⟨.skip, .seq (incFrom (m + 1) r) KC, σ.set "_" 0,
          ⟨a, (L a).toNat, .wr m (σ "x" + 1)⟩ :: l⟩)) a = r := by
        rw [wrAt_set_self ha]; simp [wrT, thr, wrS, wrK, wrS_incFrom, KC, relA]
      by_cases hij : i = (L a).toNat ∧ j = m
      · obtain ⟨rfl, rfl⟩ := hij
        have hcnt : wrote nc T L (cs.set a (thr ⟨.skip, .seq (incFrom (j + 1) r) KC, σ.set "_" 0,
            ⟨a, (L a).toNat, .wr j (σ "x" + 1)⟩ :: l⟩)) (L a).toNat j = wrote nc T L cs (L a).toNat j + 1 := by
          unfold wrote
          refine Ticket.cnt_flip a (fun d hd => ?_) ?_ ?_ T haT
          · simp only [wrAt_set_ne hd]
          · simp only [hw0, decide_eq_false_iff_not]; omega
          · simp only [hw1, decide_eq_true_eq]; exact ⟨trivial, by omega⟩
        rw [hcnt]
        simp only [upd_same, setCell, ite_true]
        rw [hx, hold, BitVec.ofNat_add]; rfl
      · have hmem : (upd S.mem (L a).toNat (setCell (S.mem (L a).toNat) m (σ "x" + 1))) i j = S.mem i j := by
          by_cases hi : i = (L a).toNat
          · subst hi
            have hj : j ≠ m := fun e => hij ⟨rfl, e⟩
            simp [setCell, hj]
          · simp [upd_other _ _ hi]
        have hcnt : wrote nc T L (cs.set a (thr ⟨.skip, .seq (incFrom (m + 1) r) KC, σ.set "_" 0,
            ⟨a, (L a).toNat, .wr m (σ "x" + 1)⟩ :: l⟩)) i j = wrote nc T L cs i j := by
          unfold wrote
          refine Ticket.cnt_congr T fun d _ => ?_
          by_cases hd : d = a
          · subst hd
            simp only [hw0, hw1]
            by_cases hi : (L d).toNat = i
            · have hj : j ≠ m := fun e => hij ⟨hi.symm, e⟩
              simp only [hi, true_and, decide_eq_decide]; omega
            · simp [hi]
          · simp only [wrAt_set_ne hd]
        simp only [hmem, hcnt]; exact hold
    · -- not a write: the regions and the counts are unchanged
      have hnp : isPush cs[a].stmt = false := by simpa using hpush
      have hmem := step_mem (x := cs[a].cfg l) hst hnp hl hl'
      have hw : wrAt (cs.set a (thr c')) a = wrAt cs a := by
        rw [hwa, hwa0]; simp only [hnp] at hcount; simpa using hcount
      have hcnt : wrote nc T L (cs.set a (thr c')) i j = wrote nc T L cs i j := by
        unfold wrote
        refine Ticket.cnt_congr T fun d _ => ?_
        by_cases hd : d = a
        · subst hd; simp only [hw]
        · simp only [wrAt_set_ne hd]
      rw [hmem, hcnt]; exact hold

theorem gd_steps {nc T : Nat} {L : Nat → Val} (hnc : nc ≤ 2 ^ 32) {cs cs' : List (CThread APrim)}
    {l l' : RLog} (h : CSteps PGR cs l cs' l') : GD nc T L cs l → GD nc T L cs' l' := by
  induction h with
  | refl => exact id
  | step hs _ ih =>
    obtain ⟨i, hi, hst⟩ := hs
    exact fun hG => ih (gd_step hnc hG ⟨hi, _, hst, rfl, rfl⟩)

/-- **No lost updates on the multicore machine.** When every CPU has finished,
each of the first `nc` cells of region `i` holds the number of CPUs that used
lock `i`, and the other cells are untouched. -/
theorem no_lost_updates_R (nc T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) (hnc : nc ≤ 2 ^ 32)
    {cs : List (CThread APrim)} {l : RLog} (h : CSteps PGR (poolR nc T L) [] cs l)
    (hdone : ∀ c (hc : c < cs.length), Done cs[c]) {S : RState} {H : HLogR} (hr : rreplay l = some (S, H))
    (i j : Nat) :
    S.mem i j = if j < nc then BitVec.ofNat 32 (Ticket.cnt (fun c => decide ((L c).toNat = i)) T) else 0 := by
  obtain ⟨⟨Φ, hGL⟩, -, hdata⟩ := gd_steps hnc h (gd_init nc T L hT)
  obtain ⟨-, -, -, -, hlen, -⟩ := hGL
  rw [hdata S H hr i j]
  have hw : ∀ c, c < T → wrAt cs c = 0 := fun c hc => by
    have hc' : c < cs.length := by rw [hlen]; exact hc
    obtain ⟨h1, h2⟩ := hdone c hc'
    rw [wrAt_self hc']; simp [wrT, h1, h2, wrS, wrK]
  by_cases hj : j < nc
  · rw [if_pos hj]
    unfold wrote
    exact congrArg _ (Ticket.cnt_congr T fun c hc => by simp [hw c hc, hj])
  · rw [if_neg hj]
    unfold wrote
    rw [Ticket.cnt_congr (g' := fun _ => false) T fun c hc => by simp [hw c hc, hj],
      Ticket.cnt_zero (fun _ => rfl) T]
    rfl

end RegionNoLost
