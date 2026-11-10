import CertiKOS.LockArrayAtomic
import CertiKOS.FairEnv

/-!
# A concrete fair scheduler for the lock array: `RelyA` and `FairA` are satisfiable

The array analogue of `FairEnv.lean`. Whenever CPU `c` looks at the shared
log, `fairEnvA` moves *every lock that occurs in the log*, independently:

* if another CPU holds the lock, it releases (`inc_n`);
* otherwise, if another CPU waits for the ticket being served, it takes the
  lock and releases it (`hold`, `inc_n`).

Different locks' events touch different lock states, so the moves compose.
Then:

* `fairA_rely`: the scheduler keeps the array log valid (`RelyA`), for every CPU.
* `fairA_fair`: whenever `c` waits for a ticket that is not yet served on
  lock `i`, `now` on lock `i` advances at once. `FairA` holds with the
  constant-zero counter.
* `acquireA_refines_fair`, `acquireA_bounded_fair`: the lock-array refinement
  and liveness theorems are not vacuous. Under this scheduler, `acquire(i)`
  returns within `NCPU + 1` iterations.
-/

namespace LockArray

open ClightL Ticket

/-! ## The scheduler -/

/-- The other CPUs' moves on lock `j`, given its protocol state `p`. -/
def blk (p : PState) (c : CPU) (j : Nat) : List AEvent :=
  match findCPU (isHolding p c) NCPU with
  | some d => [ev d j .incNow]
  | none =>
    match findCPU (isNext p c) NCPU with
    | some d => [ev d j .incNow, ev d j .hold]
    | none => []

def dedup : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup {a : Nat} : ∀ {l : List Nat}, a ∈ dedup l ↔ a ∈ l
  | [] => by simp [dedup]
  | x :: xs => by
    have ih := mem_dedup (a := a) (l := xs)
    simp only [dedup]
    split
    · rename_i hx
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact ih.1 hx
        · exact h
    · rw [List.mem_cons, ih, List.mem_cons]

theorem nodup_dedup : ∀ l : List Nat, (dedup l).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    simp only [dedup]
    split
    · exact nodup_dedup xs
    · rename_i hx; exact List.nodup_cons.2 ⟨hx, nodup_dedup xs⟩

/-- The locks occurring in a log, without repetition. -/
def locks (l : ALog) : List Nat := dedup (l.map AEvent.lk)

def fairQueryA (c : CPU) (l : ALog) : List AEvent :=
  match areplay l with
  | none => []
  | some (S, _) => (locks l).flatMap fun j => blk (S.lk j) c j

theorem blk_cpu {p : PState} {c : CPU} {j : Nat} : ∀ e ∈ blk p c j, e.cpu ≠ c := by
  intro e he
  unfold blk at he
  split at he
  · rename_i d hd
    simp only [List.mem_singleton] at he; subst he
    exact (isHolding_true (findCPU_some hd).1).1
  · split at he
    · rename_i d hd
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact (isNext_true (findCPU_some hd).1).1
    · simp at he

def fairEnvA : AEnv where
  query := fairQueryA
  noSelf := by
    intro c l e he
    simp only [fairQueryA] at he
    split at he
    · simp at he
    · obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 he
      exact blk_cpu e hj

/-! ## One lock's moves -/

/-- The moves on lock `j` keep the log valid, touch only lock `j`, never lower
its `now`, and raise it when `c` waits for a ticket not yet served. -/
theorem blk_ok {c : CPU} {j : Nat} {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) :
    ∃ S' H', areplay (blk (S.lk j) c j ++ l) = some (S', H') ∧
      (∀ j', j' ≠ j → S'.lk j' = S.lk j') ∧ (S.lk j).now ≤ (S'.lk j).now ∧
      (∀ tn, (S.lk j).phase c = .waiting tn → (S.lk j).now < tn → (S'.lk j).now = (S.lk j).now + 1) := by
  have hp := areplay_proj hl j
  have hi := replay_inv hp
  generalize hpdef : S.lk j = p at hp hi ⊢
  unfold blk
  cases hfh : findCPU (isHolding p c) NCPU with
  | some d =>
    obtain ⟨hh, hd⟩ := findCPU_some hfh
    obtain ⟨_, t, ht⟩ := isHolding_true hh
    have hps : pstep p ⟨d, .incNow⟩ = some (⟨p.ticket, p.now + 1, setPhase p.phase d .idle⟩, some (.rel d)) := by
      simp [pstep, hd, ht]
    refine ⟨_, _, areplay_cons_of hl (astep_tk (i := j) (by rw [hpdef]; exact hps)), ?_, ?_, ?_⟩
    · intro j' hj'; simp [upd, hj']
    · simp [hpdef]
    · intro _ _ _; simp [hpdef]
  | none =>
    cases hfn : findCPU (isNext p c) NCPU with
    | some d =>
      obtain ⟨hn, hd⟩ := findCPU_some hfn
      obtain ⟨_, hw⟩ := isNext_true hn
      have hps1 : pstep p ⟨d, .hold⟩ =
          some (⟨p.ticket, p.now, setPhase p.phase d (.holding p.now)⟩, some (.acq d)) := by
        simp [pstep, hd, hw]
      have hr1 := areplay_cons_of hl (astep_tk (i := j) (by rw [hpdef]; exact hps1))
      have hps2 : pstep (upd S.lk j ⟨p.ticket, p.now, setPhase p.phase d (.holding p.now)⟩ j) ⟨d, .incNow⟩ =
          some (⟨p.ticket, p.now + 1, setPhase (setPhase p.phase d (.holding p.now)) d .idle⟩,
            some (.rel d)) := by
        simp [pstep, hd]
      have hr2 := areplay_cons_of hr1 (astep_tk hps2)
      refine ⟨_, _, by simpa using hr2, ?_, ?_, ?_⟩
      · intro j' hj'; simp [upd, hj']
      · simp
      · intro _ _ _; simp
    | none =>
      refine ⟨S, H, by simpa using hl, fun _ _ => rfl, by rw [hpdef]; exact Nat.le_refl _, ?_⟩
      intro tn hw hlt
      exfalso
      -- nobody holds lock `j`, so the owner of ticket `now` waits for it
      have htk : tn < p.ticket := hi.tkLt c tn (by simp [hw, Phase.tk])
      have hnohold : ∀ e t, p.phase e = .holding t → False := by
        intro e t he
        by_cases hen : e < NCPU
        · have hec := isHolding_false (findCPU_none hfh e hen) he
          subst hec; rw [hw] at he; cases he
        · rw [hi.idleOut e (Nat.le_of_not_lt hen)] at he; cases he
      obtain ⟨d, hd⟩ := replay_fill hp p.now (Nat.le_refl _) (by omega)
      have hdc : d ≠ c := by rintro rfl; rw [hw] at hd; simp [Phase.tk] at hd; omega
      have hdlt : d < NCPU := by
        apply Nat.lt_of_not_le; intro hge
        rw [hi.idleOut d hge] at hd; simp [Phase.tk] at hd
      have hdw : p.phase d = .waiting p.now := by
        cases hph : p.phase d with
        | idle => rw [hph] at hd; simp [Phase.tk] at hd
        | waiting t => rw [hph] at hd; simp [Phase.tk] at hd; rw [hd]
        | holding t => exact (hnohold d t hph).elim
      have h1 := findCPU_none hfn d hdlt
      simp [isNext, hdw, hdc] at h1

/-! ## All locks at once -/

/-- Moving the distinct locks `js` one block at a time. -/
theorem blks_ok {c : CPU} {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) :
    ∀ js : List Nat, js.Nodup →
      ∃ S' H', areplay (js.flatMap (fun j => blk (S.lk j) c j) ++ l) = some (S', H') ∧
        (∀ j, j ∉ js → S'.lk j = S.lk j) ∧ (∀ j, (S.lk j).now ≤ (S'.lk j).now) ∧
        (∀ j, j ∈ js → ∀ tn, (S.lk j).phase c = .waiting tn → (S.lk j).now < tn →
          (S'.lk j).now = (S.lk j).now + 1)
  | [], _ => ⟨S, H, by simpa using hl, fun _ _ => rfl, fun _ => Nat.le_refl _, by simp⟩
  | j :: js, hnd => by
    have hj : j ∉ js := (List.nodup_cons.1 hnd).1
    obtain ⟨S1, H1, hr1, hu1, hm1, hf1⟩ := blks_ok hl js (List.nodup_cons.1 hnd).2
    have hsame : S1.lk j = S.lk j := hu1 j hj
    obtain ⟨S2, H2, hr2, hu2, hm2, hf2⟩ := blk_ok (c := c) (j := j) hr1
    rw [hsame] at hr2 hm2 hf2
    refine ⟨S2, H2, by simpa [List.flatMap_cons, List.append_assoc] using hr2, ?_, ?_, ?_⟩
    · intro j' hj'
      have hne : j' ≠ j := fun e => hj' (e ▸ List.mem_cons_self)
      rw [hu2 j' hne]; exact hu1 j' (fun h => hj' (List.mem_cons_of_mem _ h))
    · intro j'
      by_cases hne : j' = j
      · subst hne; exact hm2
      · rw [hu2 j' hne]; exact hm1 j'
    · intro j' hj' tn hw hlt
      by_cases hne : j' = j
      · subst hne; exact hf2 tn hw hlt
      · rw [hu2 j' hne]
        exact hf1 j' ((List.mem_cons.1 hj').resolve_left hne) tn hw hlt

theorem locks_nodup (l : ALog) : (locks l).Nodup := nodup_dedup _

theorem mem_locks {l : ALog} {i : Nat} : i ∈ locks l ↔ i ∈ l.map AEvent.lk := mem_dedup

theorem projL_nil_of {i : Nat} : ∀ {l : ALog}, i ∉ l.map AEvent.lk → projL i l = []
  | [], _ => rfl
  | ⟨c, j, k⟩ :: l, h => by
    have hj : j ≠ i := fun e => h (by simp [e])
    have ih := projL_nil_of (l := l) (fun h' => h (List.mem_cons_of_mem _ h'))
    cases k <;> simp [projL, hj, ih]

theorem fairA_rely (c : CPU) : RelyA fairEnvA c where
  conform := by
    intro l S H hl
    obtain ⟨S', H', hr, -⟩ := blks_ok (c := c) hl (locks l) (locks_nodup l)
    refine ⟨S', H', ?_⟩
    simpa [apull, fairEnvA, fairQueryA, hl] using hr

/-- **The array scheduler is fair**: on the lock `c` waits for, `now` moves at once. -/
theorem fairA_fair (c : CPU) (i tn : Nat) : FairA fairEnvA c i tn (fun _ => 0) := by
  intro l S H hl hw hlt
  left
  obtain ⟨S', H', hr, -, -, hf⟩ := blks_ok (c := c) hl (locks l) (locks_nodup l)
  have hin : i ∈ locks l := by
    rw [mem_locks]
    refine Classical.byContradiction fun hn => ?_
    have := areplay_proj hl i
    rw [projL_nil_of hn] at this
    simp [replay] at this
    rw [← this.1] at hw; simp [PState.init] at hw
  have hpull : apull fairEnvA c l = (locks l).flatMap (fun j => blk (S.lk j) c j) ++ l := by
    simp [apull, fairEnvA, fairQueryA, hl]
  rw [hpull]
  rw [← (replay_counts (areplay_proj hl i)).1, ← (replay_counts (areplay_proj hr i)).1,
    hf i hin tn hw hlt]
  omega

/-! ## The lock-array theorems are not vacuous -/

/-- Under `fairEnvA`, `acquire(i)` returns within `NCPU + 1` iterations from any
valid log where `c` is idle on lock `i`. -/
theorem acquireA_bounded_fair {c : CPU} {i : Nat} (hc : c < NCPU) {l : ALog} {S : AState} {H : HLogA}
    (hl : areplay l = some (S, H)) (hidle : (S.lk i).phase c = .idle) :
    ∃ r, acquireSpecA fairEnvA c i ((NCPU + 1) * (0 + 1)) l = some r :=
  acquireA_live_bounded hc (fairA_rely c) hl hidle (fun _ => 0) 0 (fun _ => Nat.le_refl _)
    (fairA_fair c i _)

/-- Under `fairEnvA`, the C `acquire(i)` refines the atomic `acq(i)` with data. -/
theorem acquireA_refines_fair {c : CPU} (hc : c < NCPU) {l : ALog} {S : AState} {H : HLogA}
    (hl : areplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (σ : Locals) (hlk : σ "lk" = iv) (k : Cont APrim) :
    ∃ (εH : HEnvA) (r : ALog) (σ' : Locals) (E2 : HLogA) (S' : AState),
      HRelyA εH c ∧
      Star (aprims fairEnvA c) ⟨acquireA, k, σ, l⟩ ⟨.skip, k, σ', r⟩ ∧
      hprimsA εH c .acq [iv] H = some (σ' "v", .acqA c iv.toNat :: hpullA εH c H) ∧
      areplay r = some (S', E2 ++ .acqA c iv.toNat :: hpullA εH c H) ∧
      (∀ e ∈ E2, e.cpu ≠ c) ∧ Holding S' c iv.toNat :=
  acquireA_refines hc (fairA_rely c) hl hidle (fun _ => 0) 0 (fun _ => Nat.le_refl _)
    (fairA_fair c _ _) σ hlk k

/-! ## A concrete contended run -/

/-- CPU 1 holds lock 3 and CPU 2 is queued on it; CPU 4 holds lock 5. -/
def contendedA : ALog :=
  [ev 4 5 .hold, ev 4 5 .getNow, ev 4 5 .incTicket,
   ev 2 3 .incTicket, ev 1 3 .hold, ev 1 3 .getNow, ev 1 3 .incTicket]

/-- CPU 0 joins lock 3's queue as third and gets the lock (checked by evaluation). -/
theorem demo_contendedA : (acquireSpecA fairEnvA 0 3 8 contendedA).isSome = true := by decide

end LockArray
