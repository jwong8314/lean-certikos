import CertiKOS.Link
import CertiKOS.FairEnv

/-!
# Multicore linking, liveness half: the per-CPU `FairP` proof runs on the multicore machine

`TicketProtocol.lean` proves CPU `c`'s acquire live *per CPU*:
`acquire_live_bounded` says that under any environment `ε` satisfying `RelyP`
and `FairP` with a fairness counter bounded by `K`, the spec returns within
`(NCPU + 1) * (K + 1)` loop iterations (CertiKOS's `n × m × k`, OSDI'16
Lemma 6). Here that theorem is applied, unchanged, to runs of the shared-log
multicore machine.

* `CRun`: a finite run of the multicore machine, step by step.
* `runEnv r c`: the environment CPU `c` sees in run `r`. At each of `c`'s
  primitive calls it answers with the events the other CPUs appended since
  `c` last called. At every other log it answers like the eager fair
  scheduler `eagerEnv` (the holder releases; if no one holds, the next owner
  takes the lock and releases). `FairP` quantifies over *all* logs, and on
  those logs `now` then always advances.
* `proj`: CPU `c`'s steps in `r` are a run of its per-CPU layer
  `Star (prims (runEnv r c) c)`.
* `runEnv_rely`, `runEnv_fair`: `runEnv` satisfies `RelyP` (from the
  composition theorem of `Link.lean`) and `FairP`. The fairness counter is
  taken from the run: `1 +` the number of steps left before `now` passes the
  value `c` last saw. It is bounded under the environment-fairness
  hypothesis `EnvFair D`: whenever `c` polls while it is not its turn, `now`
  advances within `D` steps of the multicore machine. This is CCAL's
  assumption on the environment, which the per-CPU proof takes as given.
* `multicore_acquire_bounded`: in any run, once CPU `c` starts `acquire`, it
  issues at most `(NCPU + 1) * (D + 2) + 1` `get_n` events before its `hold`.
  The per-CPU bound is reused through determinism: `c`'s multicore steps are
  a prefix of its unique per-CPU execution under `runEnv`.
-/

namespace LiveLink

open ClightL Ticket ClightToPy TicketPy TicketLive Link

/-! ## Counting one CPU's own events -/

def cntC (c : CPU) (k : EvKind) (l : Log) : Nat := l.countP (fun e => e.cpu == c && e.kind == k)

theorem cntC_append (c : CPU) (k : EvKind) (xs l : Log) :
    cntC c k (xs ++ l) = cntC c k xs + cntC c k l := List.countP_append ..

theorem cntC_others {c : CPU} {k : EvKind} {xs : Log} (h : ∀ e ∈ xs, e.cpu ≠ c) : cntC c k xs = 0 := by
  unfold cntC
  rw [List.countP_eq_zero]
  intro e he
  simp [h e he]

theorem cntC_cons_self (c : CPU) (k : EvKind) (l : Log) : cntC c k (⟨c, k⟩ :: l) = cntC c k l + 1 := by
  simp [cntC, List.countP_cons]

theorem cntC_cons_other {c : CPU} {k k' : EvKind} (l : Log) (h : k' ≠ k) :
    cntC c k (⟨c, k'⟩ :: l) = cntC c k l := by
  simp [cntC, List.countP_cons, h]

theorem cntC_pull (ε : EnvCtx) (c : CPU) (k : EvKind) (l : Log) : cntC c k (pull ε c l) = cntC c k l := by
  simp [pull, cntC_append, cntC_others (ε.noSelf c l)]

/-! ## Per-CPU runs: logs only grow, and runs are deterministic -/

theorem step_ext {ε : EnvCtx} {c : CPU} {x y : Config Prim Log}
    (hs : ClightL.step (prims ε c) x = some y) : ∃ zs, y.abs = zs ++ x.abs := by
  rcases step_cases (t := thr x) (a := x.abs) hs with ⟨h, -⟩ | ⟨⟨p, args, v, hv⟩, -⟩
  · exact ⟨[], by simp [h]⟩
  · cases p <;> cases args <;> simp [prims] at hv <;> obtain ⟨-, h⟩ := hv <;>
      (rw [← h]; exact ⟨_ :: ε.query c x.abs, rfl⟩)

theorem star_ext {ε : EnvCtx} {c : CPU} {x y : Config Prim Log} (h : Star (prims ε c) x y) :
    ∃ zs, y.abs = zs ++ x.abs := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | step hs _ ih =>
    obtain ⟨z1, h1⟩ := step_ext hs
    obtain ⟨z2, h2⟩ := ih
    exact ⟨z2 ++ z1, by rw [h2, h1, List.append_assoc]⟩

theorem star_cnt {ε : EnvCtx} {c : CPU} (k : EvKind) {x y : Config Prim Log}
    (h : Star (prims ε c) x y) : cntC c k x.abs ≤ cntC c k y.abs := by
  obtain ⟨zs, hz⟩ := star_ext h
  rw [hz, cntC_append]; omega

theorem star_det {Pn Abs : Type} {P : Prims Pn Abs} {x y z : Config Pn Abs}
    (h1 : Star P x y) (h2 : Star P x z) : Star P y z ∨ Star P z y := by
  induction h1 generalizing z with
  | refl => exact .inl h2
  | @step a b y hs _ ih =>
    cases h2 with
    | refl => exact .inr (.step hs (by assumption))
    | step hs' h2' =>
      rw [hs] at hs'; cases hs'
      exact ih h2'

/-! ## `acquire` under any continuation, and what its spec does to our counts -/

theorem acquire_sim_k (ε : EnvCtx) (c : CPU) (fuel : Nat) (loc : Locals) (l r : Log) (k : Cont Prim)
    (h : acquireSpec ε c fuel l = some r) :
    ∃ loc' : Locals, Star (prims ε c) ⟨acquireCode, k, loc, l⟩ ⟨.skip, k, loc', r⟩ := by
  obtain ⟨r0, hw, rfl⟩ := acquireSpec_some h
  let l1 := pull ε c l
  let t := BitVec.ofNat 32 (ticket l1)
  let l2 : Log := ⟨c, .incTicket⟩ :: l1
  let l3 := pull ε c l2
  let n := BitVec.ofNat 32 (now l3)
  let loc1 := loc.set "t" t
  let loc2 := loc1.set "n" n
  have ht2 : loc2 "t" = t := by simp [loc2, loc1]
  have hn2 : loc2 "n" = n := by simp [loc2]
  obtain ⟨loc', _, hstar⟩ :=
    loop_sim ε c t fuel n loc2 (⟨c, .getNow⟩ :: l3) r0 (.seq holdCall k) ht2 hn2 hw
  refine ⟨loc'.set "_" 0, ?_⟩
  let rest : Stmt Prim := .seq (.call "n" .getNow []) (.seq acquireLoop holdCall)
  refine .step (c' := ⟨.call "t" .faiTicket [], .seq rest k, loc, l⟩)
      (by simp [step, acquireCode, rest]) ?_
  refine .step (c' := ⟨.skip, .seq rest k, loc1, l2⟩)
      (by simp [step, prims, loc1, t, l2, l1]) ?_
  refine .step (c' := ⟨rest, k, loc1, l2⟩) (by simp [step]) ?_
  refine .step (c' := ⟨.call "n" .getNow [], .seq (.seq acquireLoop holdCall) k, loc1, l2⟩)
      (by simp [step, rest]) ?_
  refine .step (c' := ⟨.skip, .seq (.seq acquireLoop holdCall) k, loc2, ⟨c, .getNow⟩ :: l3⟩)
      (by simp [step, prims, loc2, n, l3]) ?_
  refine .step (c' := ⟨.seq acquireLoop holdCall, k, loc2, ⟨c, .getNow⟩ :: l3⟩)
      (by simp [step]) ?_
  refine .step (c' := ⟨acquireLoop, .seq holdCall k, loc2, ⟨c, .getNow⟩ :: l3⟩)
      (by simp [step]) ?_
  refine Star.trans hstar ?_
  refine .step (c' := ⟨holdCall, k, loc', r0⟩) (by simp [step]) ?_
  exact Star.single (by simp [step, holdCall, prims, holdSpec])

theorem waitLoop_cnt (ε : EnvCtx) (c : CPU) (t : Val) :
    ∀ f n l r, waitLoop ε c t f n l = some r →
      cntC c .getNow r ≤ cntC c .getNow l + f ∧ cntC c .hold r = cntC c .hold l := by
  intro f
  induction f with
  | zero =>
    intro n l r h
    by_cases hnt : n = t <;> simp [waitLoop, hnt] at h
    subst h; exact ⟨by omega, rfl⟩
  | succ f ih =>
    intro n l r h
    by_cases hnt : n = t
    · simp [waitLoop, hnt] at h; subst h; exact ⟨by omega, rfl⟩
    · simp only [waitLoop, hnt, ite_false] at h
      obtain ⟨h1, h2⟩ := ih _ _ _ h
      rw [cntC_cons_self, cntC_pull] at h1
      rw [cntC_cons_other _ (by decide), cntC_pull] at h2
      exact ⟨by omega, h2⟩

theorem acquireSpec_cnt {ε : EnvCtx} {c : CPU} {fuel : Nat} {l r : Log}
    (h : acquireSpec ε c fuel l = some r) :
    cntC c .getNow r ≤ cntC c .getNow l + fuel + 1 ∧ cntC c .hold l + 1 ≤ cntC c .hold r := by
  obtain ⟨r0, hw, rfl⟩ := acquireSpec_some h
  obtain ⟨h1, h2⟩ := waitLoop_cnt ε c _ fuel _ _ _ hw
  have e1 : cntC c .getNow (⟨c, .getNow⟩ :: pull ε c (⟨c, .incTicket⟩ :: pull ε c l)) =
      cntC c .getNow l + 1 := by
    rw [cntC_cons_self, cntC_pull, cntC_cons_other _ (by decide), cntC_pull]
  have e2 : cntC c .hold (⟨c, .getNow⟩ :: pull ε c (⟨c, .incTicket⟩ :: pull ε c l)) =
      cntC c .hold l := by
    rw [cntC_cons_other _ (by decide), cntC_pull, cntC_cons_other _ (by decide), cntC_pull]
  have e3 : cntC c .getNow (holdSpec ε c r0) = cntC c .getNow r0 := by
    rw [holdSpec, cntC_cons_other _ (by decide), cntC_pull]
  have e4 : cntC c .hold (holdSpec ε c r0) = cntC c .hold r0 + 1 := by
    rw [holdSpec, cntC_cons_self, cntC_pull]
  omega

/-! ## The eager fair environment (used off the run) -/

def eagerQuery (c : CPU) (l : Log) : List Event :=
  match replay l with
  | none => []
  | some (s, _) =>
    match findCPU (isHolding s c) NCPU with
    | some d => [⟨d, .incNow⟩]
    | none =>
      match findCPU (isNext s c) NCPU with
      | some d => [⟨d, .incNow⟩, ⟨d, .hold⟩]
      | none => []

def eagerEnv : EnvCtx where
  query := eagerQuery
  noSelf := by
    intro c l e he
    simp only [eagerQuery] at he
    split at he
    · simp at he
    · rename_i s h _
      split at he
      · rename_i d hd
        simp at he; subst he
        exact (isHolding_true (findCPU_some hd).1).1
      · split at he
        · rename_i d hd
          simp at he
          rcases he with rfl | rfl <;> exact (isNext_true (findCPU_some hd).1).1
        · simp at he

theorem eager_rely (c : CPU) : RelyP eagerEnv c where
  conform := by
    intro l s h hl
    simp only [pull, eagerEnv, eagerQuery, hl]
    cases hfh : findCPU (isHolding s c) NCPU with
    | some d =>
      obtain ⟨hp, hd⟩ := findCPU_some hfh
      obtain ⟨_, t, ht⟩ := isHolding_true hp
      exact replay_cons_some hl (by simp [pstep, hd, ht])
    | none =>
      cases hfn : findCPU (isNext s c) NCPU with
      | some d =>
        obtain ⟨hp, hd⟩ := findCPU_some hfn
        obtain ⟨_, hw⟩ := isNext_true hp
        have hp1 : pstep s ⟨d, .hold⟩ =
            some (⟨s.ticket, s.now, setPhase s.phase d (.holding s.now)⟩, some (.acq d)) := by
          simp [pstep, hd, hw]
        obtain ⟨s2, h2, hr2⟩ := replay_cons_some (e := ⟨d, .incNow⟩) (replay_cons_of hl hp1)
          (by simp [pstep, hd])
        exact ⟨s2, h2, by simpa using hr2⟩
      | none => exact ⟨s, h, by simpa using hl⟩

/-- Off the run, whenever `c` waits for its turn, `now` advances. -/
theorem eager_fair {c : CPU} {l : Log} {s : PState} {h : List HEvent} {tn : Nat}
    (hl : replay l = some (s, h)) (hw : s.phase c = .waiting tn) (hlt : s.now < tn) :
    now l < now (pull eagerEnv c l) := by
  cases hfh : findCPU (isHolding s c) NCPU with
  | some d =>
    have hpull : pull eagerEnv c l = ⟨d, .incNow⟩ :: l := by
      simp [pull, eagerEnv, eagerQuery, hl, hfh]
    rw [hpull]; simp [now, countK]
  | none =>
    have hi := replay_inv hl
    have htk : tn < s.ticket := hi.tkLt c tn (by simp [hw, Phase.tk])
    have hnohold : ∀ e t, s.phase e = .holding t → False := by
      intro e t he
      by_cases hen : e < NCPU
      · have hec := isHolding_false (findCPU_none hfh e hen) he
        subst hec; rw [hw] at he; cases he
      · rw [hi.idleOut e (Nat.le_of_not_lt hen)] at he; cases he
    obtain ⟨d, hd⟩ := replay_fill hl s.now (Nat.le_refl _) (by omega)
    have hdc : d ≠ c := by rintro rfl; rw [hw] at hd; simp [Phase.tk] at hd; omega
    have hdlt : d < NCPU := by
      apply Nat.lt_of_not_le; intro hge
      rw [hi.idleOut d hge] at hd; simp [Phase.tk] at hd
    have hdw : s.phase d = .waiting s.now := by
      cases hph : s.phase d with
      | idle => rw [hph] at hd; simp [Phase.tk] at hd
      | waiting t => rw [hph] at hd; simp [Phase.tk] at hd; rw [hd]
      | holding t => exact (hnohold d t hph).elim
    cases hfn : findCPU (isNext s c) NCPU with
    | none =>
      exfalso
      have h1 := findCPU_none hfn d hdlt
      simp [isNext, hdw, hdc] at h1
    | some d' =>
      have hpull : pull eagerEnv c l = ⟨d', .incNow⟩ :: ⟨d', .hold⟩ :: l := by
        simp [pull, eagerEnv, eagerQuery, hl, hfh, hfn]
      rw [hpull]; simp [now, countK]

/-! ## Runs of the multicore machine -/

/-- A finite run of the multicore machine: at step `n`, CPU `lab n` moves. -/
structure CRun where
  len : Nat
  cs : Nat → List (CThread Prim)
  lg : Nat → Log
  lab : Nat → CPU
  step : ∀ n, n < len → CStepI PG (lab n) (cs n) (lg n) (cs (n + 1)) (lg (n + 1))

namespace CRun

variable (r : CRun) (c : CPU)

/-- CPU `c` makes a primitive call at step `n`. -/
def CallAt (n : Nat) : Prop := n < r.len ∧ r.lab n = c ∧ r.lg (n + 1) ≠ r.lg n

open Classical in
/-- CPU `c`'s view at time `n`: the log right after its last primitive call. -/
noncomputable def vw : Nat → Log
  | 0 => r.lg 0
  | n + 1 => if r.CallAt c n then r.lg (n + 1) else vw n

variable {r c}

theorem vw_succ_call {n : Nat} (h : r.CallAt c n) : r.vw c (n + 1) = r.lg (n + 1) := by
  simp [vw, h]

theorem vw_succ_nocall {n : Nat} (h : ¬ r.CallAt c n) : r.vw c (n + 1) = r.vw c n := by
  simp [vw, h]

theorem lg_ext {n : Nat} (hn : n < r.len) :
    ∃ ys, r.lg (n + 1) = ys ++ r.lg n ∧ ∀ e ∈ ys, e.cpu = r.lab n := by
  obtain ⟨hi, c', hst, -, hlg⟩ := r.step n hn
  obtain ⟨ys, hys, hy⟩ := gstep_log hst
  exact ⟨ys, hlg ▸ hys, hy⟩

/-- The global log is `c`'s view plus other CPUs' events. -/
theorem vw_split : ∀ n, n ≤ r.len → ∃ xs, r.lg n = xs ++ r.vw c n ∧ ∀ e ∈ xs, e.cpu ≠ c
  | 0, _ => ⟨[], by simp [vw], by simp⟩
  | n + 1, hn => by
    by_cases hc : r.CallAt c n
    · exact ⟨[], by simp [vw_succ_call hc], by simp⟩
    · rw [vw_succ_nocall hc]
      obtain ⟨xs, hxs, hx⟩ := vw_split n (by omega)
      obtain ⟨ys, hys, hy⟩ := lg_ext (r := r) (n := n) (by omega)
      by_cases hl : r.lab n = c
      · have heq : r.lg (n + 1) = r.lg n := Classical.byContradiction fun hne => hc ⟨by omega, hl, hne⟩
        exact ⟨xs, by rw [heq, hxs], hx⟩
      · refine ⟨ys ++ xs, by rw [hys, hxs, List.append_assoc], fun e he => ?_⟩
        rcases List.mem_append.1 he with he | he
        · rw [hy e he]; exact hl
        · exact hx e he

theorem lg_len_mono : ∀ {n m : Nat}, n ≤ m → m ≤ r.len → (r.lg n).length ≤ (r.lg m).length := by
  intro n m hnm hm
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with h | h
    · obtain ⟨ys, hys, -⟩ := lg_ext (r := r) (n := m) (by omega)
      have := ih (by omega) (by omega)
      rw [hys, List.length_append]; omega
    · subst h; exact Nat.le_refl _

theorem vw_len_le_lg {n : Nat} (hn : n ≤ r.len) : (r.vw c n).length ≤ (r.lg n).length := by
  obtain ⟨xs, hxs, -⟩ := vw_split (r := r) (c := c) n hn
  rw [hxs, List.length_append]; omega

theorem vw_len_mono : ∀ {n m : Nat}, n ≤ m → m ≤ r.len → (r.vw c n).length ≤ (r.vw c m).length := by
  intro n m hnm hm
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le hnm with h | h
    · have := ih (by omega) (by omega)
      by_cases hc : r.CallAt c m
      · rw [vw_succ_call hc]
        have h1 := vw_len_le_lg (r := r) (c := c) (n := m) (by omega)
        have h2 : (r.lg m).length ≤ (r.lg (m + 1)).length := lg_len_mono (by omega) hm
        omega
      · rw [vw_succ_nocall hc]; exact this
    · subst h; exact Nat.le_refl _

theorem call_len {n : Nat} (h : r.CallAt c n) : (r.lg n).length < (r.lg (n + 1)).length := by
  obtain ⟨ys, hys, -⟩ := lg_ext (r := r) (n := n) h.1
  have hne : ys ≠ [] := fun e => h.2.2 (by rw [hys, e]; rfl)
  rw [hys, List.length_append]
  cases ys with
  | nil => exact absurd rfl hne
  | cons y ys => simp only [List.length_cons]; omega

theorem call_vw_lt {n m : Nat} (hn : r.CallAt c n) (hnm : n < m) (hm : m ≤ r.len) :
    (r.vw c n).length < (r.vw c m).length := by
  have h1 := vw_len_le_lg (r := r) (c := c) (n := n) (by have := hn.1; omega)
  have h2 := call_len hn
  have h3 := vw_len_mono (r := r) (c := c) (Nat.succ_le_of_lt hnm) hm
  rw [vw_succ_call hn] at h3
  omega

theorem call_inj {n m : Nat} (hn : r.CallAt c n) (hm : r.CallAt c m) (he : r.vw c n = r.vw c m) :
    n = m := by
  rcases Nat.lt_trichotomy n m with h | h | h
  · have := call_vw_lt hn h (by have := hm.1; omega); rw [he] at this; omega
  · exact h
  · have := call_vw_lt hm h (by have := hn.1; omega); rw [he] at this; omega

/-! ## The environment CPU `c` sees -/

variable (r c)

/-- The events other CPUs appended above `c`'s view at time `n`. -/
noncomputable def delta (n : Nat) : List Event := (r.lg n).take ((r.lg n).length - (r.vw c n).length)

variable {r c}

theorem delta_eq {n : Nat} (hn : n ≤ r.len) {xs : Log} (hxs : r.lg n = xs ++ r.vw c n) :
    r.delta c n = xs := by
  simp only [delta, hxs, List.length_append, Nat.add_sub_cancel]
  exact List.take_left' rfl

variable (r c)

open Classical in
noncomputable def runEnv : EnvCtx where
  query d k := if h : d = c ∧ ∃ n, r.CallAt c n ∧ r.vw c n = k
    then r.delta c (Classical.choose h.2) else eagerEnv.query d k
  noSelf := by
    intro d l e he
    by_cases h : d = c ∧ ∃ n, r.CallAt c n ∧ r.vw c n = l
    · rw [dif_pos h] at he
      have hm := (Classical.choose_spec h.2).1
      obtain ⟨xs, hxs, hx⟩ := vw_split (r := r) (c := c) _ (Nat.le_of_lt hm.1)
      rw [delta_eq (Nat.le_of_lt hm.1) hxs] at he
      rw [h.1]; exact hx e he
    · rw [dif_neg h] at he; exact eagerEnv.noSelf d l e he

variable {r c}

theorem pull_used {n : Nat} (hn : r.CallAt c n) : pull (r.runEnv c) c (r.vw c n) = r.lg n := by
  have h : c = c ∧ ∃ n', r.CallAt c n' ∧ r.vw c n' = r.vw c n := ⟨rfl, n, hn, rfl⟩
  have hm := Classical.choose_spec h.2
  have e := call_inj hm.1 hn hm.2
  obtain ⟨xs, hxs, -⟩ := vw_split (r := r) (c := c) n (Nat.le_of_lt hn.1)
  simp only [pull, runEnv]
  rw [dif_pos h, e, delta_eq (Nat.le_of_lt hn.1) hxs, ← hxs]

theorem pull_unused {k : Log} (hk : ¬ ∃ n, r.CallAt c n ∧ r.vw c n = k) :
    pull (r.runEnv c) c k = pull eagerEnv c k := by
  simp only [pull, runEnv]
  rw [dif_neg (fun h => hk h.2)]

/-- **Projection.** CPU `c`'s steps in the run are a run of its per-CPU layer
under `runEnv`. -/
theorem proj {a : Nat} : ∀ k, a + k ≤ r.len → ∀ ta tb, (r.cs a)[c]? = some ta →
    (r.cs (a + k))[c]? = some tb → Star (prims (r.runEnv c) c) (ta.cfg (r.vw c a)) (tb.cfg (r.vw c (a + k)))
  | 0, _, ta, tb, ha, hb => by rw [Nat.add_zero, ha] at hb; cases hb; exact .refl _
  | k + 1, hk, ta, tb, ha, hb => by
    have hn : a + k < r.len := by omega
    obtain ⟨hi, c', hst, hcs, hlg⟩ := r.step (a + k) hn
    rw [← Nat.add_assoc, hcs] at hb
    have hclen : c < (r.cs (a + k)).length := by
      have := (List.getElem?_eq_some_iff.1 hb).1; simpa using this
    have ih := proj k (by omega) ta (r.cs (a + k))[c] ha (List.getElem?_eq_getElem hclen)
    rw [← Nat.add_assoc]
    by_cases hl : r.lab (a + k) = c
    · subst hl
      rw [List.getElem?_set_self hi] at hb; cases hb
      rcases step_cases hst with ⟨habs, hall⟩ | ⟨⟨p, args, v, hv⟩, hQ⟩
      · have hnc : ¬ r.CallAt (r.lab (a + k)) (a + k) := fun h => h.2.2 (by rw [hlg, habs])
        rw [vw_succ_nocall hnc]
        exact ih.trans (.single (hall _ _))
      · have hcall : r.CallAt (r.lab (a + k)) (a + k) := ⟨hn, rfl, fun h => by
          have := prims_len hv; rw [← hlg, h] at this; omega⟩
        rw [vw_succ_call hcall, hlg]
        exact ih.trans (.single (hQ _ _ fun p args =>
          prims_pull (by rw [pull_used hcall, pull_noEnv]) p args))
    · rw [List.getElem?_set_ne hl, List.getElem?_eq_getElem hclen] at hb
      cases hb
      have hnc : ¬ r.CallAt c (a + k) := fun h => hl h.2.1
      rw [vw_succ_nocall hnc]; exact ih

/-! ## `runEnv` satisfies the rely and the fairness hypothesis of the per-CPU proof -/

theorem run_csteps : ∀ n, n ≤ r.len → CSteps PG (r.cs 0) (r.lg 0) (r.cs n) (r.lg n)
  | 0, _ => .refl
  | n + 1, hn => by
    obtain ⟨hi, c', hst, hcs, hlg⟩ := r.step n (by omega)
    refine (run_csteps n (by omega)).trans (.step ?_ .refl)
    rw [hcs, hlg]; exact .step _ hi hst

theorem runEnv_rely {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (h0 : r.cs 0 = cPool T N)
    (hl0 : r.lg 0 = []) : RelyP (r.runEnv c) c where
  conform := by
    intro k s h hk
    by_cases hu : ∃ n, r.CallAt c n ∧ r.vw c n = k
    · obtain ⟨n, hn, rfl⟩ := hu
      rw [pull_used hn]
      have := run_csteps (r := r) n (Nat.le_of_lt hn.1)
      rw [h0, hl0] at this
      exact (ticket_linked T N hT hN this).1
    · rw [pull_unused hu]; exact (eager_rely c).conform k s h hk

variable (r c)

/-- **Environment fairness (CCAL's assumption).** Whenever CPU `c` polls while
it is not its turn, `now` advances within `D` steps of the multicore machine. -/
def EnvFair (D : Nat) : Prop :=
  ∀ n, r.CallAt c n → ∀ s h tn, replay (r.vw c n) = some (s, h) → s.phase c = .waiting tn →
    s.now < tn → ∀ t, n + D ≤ t → t ≤ r.len → now (r.vw c n) < now (r.lg t)

/-- Steps from `n` on at which `now` has not passed what `c` saw at `n`. -/
noncomputable def cntNow (n : Nat) : Nat :=
  Ticket.cnt (fun t => decide (n ≤ t ∧ now (r.lg t) ≤ now (r.vw c n))) (r.len + 1)

open Classical in
/-- The fairness counter, read off the run. -/
noncomputable def bnd (D : Nat) (k : Log) : Nat :=
  if h : ∃ n, r.CallAt c n ∧ r.vw c n = k then min (D + 1) (1 + r.cntNow c (Classical.choose h)) else 0

variable {r c}

theorem bnd_used {D n : Nat} (hn : r.CallAt c n) : r.bnd c D (r.vw c n) = min (D + 1) (1 + r.cntNow c n) := by
  have h : ∃ n', r.CallAt c n' ∧ r.vw c n' = r.vw c n := ⟨n, hn, rfl⟩
  have hm := Classical.choose_spec h
  simp only [bnd]
  rw [dif_pos h, call_inj hm.1 hn hm.2]

theorem bnd_unused {D : Nat} {k : Log} (hk : ¬ ∃ n, r.CallAt c n ∧ r.vw c n = k) : r.bnd c D k = 0 := by
  simp only [bnd]; rw [dif_neg hk]

theorem cnt_mono_lt {g g' : Nat → Bool} {i : Nat} (hsub : ∀ d, g' d = true → g d = true)
    (hi : g i = true) (hi' : g' i = false) : ∀ N, i < N → Ticket.cnt g' N < Ticket.cnt g N := by
  have hle : ∀ N, Ticket.cnt g' N ≤ Ticket.cnt g N := by
    intro N; induction N with
    | zero => simp [Ticket.cnt]
    | succ N ih =>
      simp only [Ticket.cnt]
      cases h1 : g' N
      · simp; split <;> omega
      · simp [hsub N h1]; omega
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [Ticket.cnt]
    by_cases hiN : i = N
    · subst hiN; simp [hi, hi']; have := hle i; omega
    · have := ih (by omega)
      cases h1 : g' N
      · simp; split <;> omega
      · simp [hsub N h1]; omega

theorem cnt_window {g : Nat → Bool} {n D : Nat} :
    ∀ N, (∀ d, d < N → g d = true → n ≤ d ∧ d < n + D) → Ticket.cnt g N ≤ D := by
  suffices ∀ N, (∀ d, d < N → g d = true → n ≤ d ∧ d < n + D) → Ticket.cnt g N ≤ min N (n + D) - n from
    fun N hw => by have := this N hw; omega
  intro N; induction N with
  | zero => intro _; simp [Ticket.cnt]
  | succ N ih =>
    intro hw
    have ih' := ih (fun d hd => hw d (by omega))
    simp only [Ticket.cnt]
    cases h : g N
    · simp; omega
    · have := hw N (by omega) h; simp; omega

theorem cs_len : ∀ n, n ≤ r.len → (r.cs n).length = (r.cs 0).length
  | 0, _ => rfl
  | n + 1, hn => by
    obtain ⟨hi, c', hst, hcs, hlg⟩ := r.step n (by omega)
    rw [hcs, List.length_set]; exact cs_len n (by omega)

theorem runEnv_fair {D : Nat} (hD : r.EnvFair c D) (tn : Nat) : FairP (r.runEnv c) c tn (r.bnd c D) := by
  intro k s h hk hw hlt
  by_cases hu : ∃ n, r.CallAt c n ∧ r.vw c n = k
  · obtain ⟨n, hn, rfl⟩ := hu
    rw [pull_used hn]
    by_cases hnow : now (r.vw c n) < now (r.lg n)
    · exact .inl hnow
    · right
      have hsnow : s.now = now (r.vw c n) := (replay_counts hk).1
      -- the counter at our poll is exact: `now` moves within `D` steps
      have hwin : r.cntNow c n ≤ D := cnt_window _ (fun d hdN hd => by
        simp only [decide_eq_true_eq] at hd
        refine ⟨hd.1, Nat.lt_of_not_le fun hge => ?_⟩
        have := hD n hn s h tn hk hw hlt d hge (by omega)
        omega)
      rw [bnd_used hn]
      by_cases hu' : ∃ m, r.CallAt c m ∧ r.vw c m = ⟨c, .getNow⟩ :: r.lg n
      · obtain ⟨m, hm, hme⟩ := hu'
        rw [← hme, bnd_used hm]
        have hnm : n < m := Nat.lt_of_not_le fun hle => by
          have h1 := vw_len_mono (r := r) (c := c) hle (Nat.le_of_lt hn.1)
          have h2 := vw_len_le_lg (r := r) (c := c) (n := n) (Nat.le_of_lt hn.1)
          rw [hme] at h1; simp at h1; omega
        have hthr : now (r.vw c m) = now (r.vw c n) := by
          rw [hme, now_getNow]
          obtain ⟨xs, hxs, -⟩ := vw_split (r := r) (c := c) n (Nat.le_of_lt hn.1)
          have : now (r.lg n) = now xs + now (r.vw c n) := by rw [hxs]; exact countK_append _ _ _
          omega
        have hlt' : r.cntNow c m < r.cntNow c n := by
          unfold cntNow
          refine cnt_mono_lt (i := n) (fun d hd => ?_) (by simp; omega) (by simp; omega) _ (by
            have := hn.1; omega)
          simp only [decide_eq_true_eq] at hd ⊢
          exact ⟨by omega, by omega⟩
        omega
      · rw [bnd_unused hu']; omega
  · exact .inl (by rw [pull_unused hu]; exact eager_fair hk hw hlt)

theorem bnd_le {D : Nat} (k : Log) : r.bnd c D k ≤ D + 1 := by
  unfold bnd; split <;> omega

end CRun

/-! ## The multicore theorem -/

theorem at_acq {N : Nat} {c : CPU} {s : PState} {t : CThread Prim} {w : Nat}
    (hA : At N c s t w) (ht : t.stmt = acquireCode ∧ t.cont = KA N) : s.phase c = .idle := by
  cases hA <;> simp_all [KA, KO, KR, KT, KW, KH, KL, loopS, bodyS, clientCode, acquireCode,
    releaseCode, incI, gnC, acquireLoop, holdCall]

open CRun in
/-- **Bounded acquire on the multicore machine, by the per-CPU proof.** In any
run of T ≤ NCPU CPUs running the client, suppose CPU `c` is at the start of
`acquire` at time `a`, and the environment is `D`-fair for `c`. Then, up to its
`hold`, `c` issues at most `(NCPU + 1) * (D + 2) + 1` `get_n` events. The
bound is `acquire_live_bounded`, applied to the environment `c` sees in the
run. -/
theorem multicore_acquire_bounded {T N : Nat} (hT : T ≤ NCPU) (hN : N < 2 ^ 32) (r : CRun)
    (h0 : r.cs 0 = cPool T N) (hl0 : r.lg 0 = []) {c : CPU} (hc : c < T) {D : Nat}
    (hD : r.EnvFair c D) {a t : Nat} {σ : Locals} (hat : a ≤ t) (ht : t ≤ r.len)
    (ha : (r.cs a)[c]? = some ⟨acquireCode, KA N, σ⟩)
    (hhold : cntC c .hold (r.lg t) = cntC c .hold (r.lg a)) :
    cntC c .getNow (r.lg t) ≤ cntC c .getNow (r.lg a) + (NCPU + 1) * (D + 2) + 1 := by
  have hcN : c < NCPU := Nat.lt_of_lt_of_le hc hT
  have hR := runEnv_rely (r := r) (c := c) hT hN h0 hl0
  -- c's view at `a` is reached by its per-CPU run from the initial thread
  have h0c : (r.cs 0)[c]? = some (cThread N) := by
    rw [h0]; simp [cPool, hc]
  have hstar0 := proj (r := r) (c := c) (a := 0) a (by omega) _ _ h0c (by simpa using ha)
  rw [show r.vw c 0 = [] from by simp [vw, hl0], Nat.zero_add] at hstar0
  obtain ⟨⟨s, h, hs⟩, s', h', w, hs', hA⟩ := client_pinv hcN hN hR hstar0
  have hidle : s.phase c = .idle := by
    have := (replay_others _ ((r.runEnv c).noSelf c _) hs hs').1
    rw [← this]; exact at_acq hA ⟨rfl, rfl⟩
  -- the per-CPU liveness theorem, under the run's environment
  obtain ⟨rr, hspec⟩ := acquire_live_bounded hcN hR hs hidle (r.bnd c D) (D + 1) bnd_le
    (runEnv_fair hD _)
  obtain ⟨σ', hend⟩ := acquire_sim_k _ c _ σ _ rr (KA N) hspec
  obtain ⟨hg, hh⟩ := acquireSpec_cnt hspec
  -- c's position at `t`, by determinism
  have hlen : c < (r.cs t).length := by
    rw [cs_len t ht, h0]; simpa [cPool] using hc
  have hstar := proj (r := r) (c := c) (a := a) (t - a) (by omega) _ (r.cs t)[c] ha
    (by rw [Nat.add_sub_cancel' hat]; exact List.getElem?_eq_getElem hlen)
  rw [Nat.add_sub_cancel' hat] at hstar
  obtain ⟨xa, hxa, hxa'⟩ := vw_split (r := r) (c := c) a (by omega)
  obtain ⟨xt, hxt, hxt'⟩ := vw_split (r := r) (c := c) t ht
  rw [hxa, hxt, cntC_append, cntC_append, cntC_others hxa', cntC_others hxt'] at hhold ⊢
  simp only [Nat.zero_add] at hhold ⊢
  rcases star_det hstar hend with h1 | h1
  · have := star_cnt .getNow h1
    simp only [CThread.cfg] at this hg
    have e : (NCPU + 1) * (D + 1 + 1) = (NCPU + 1) * (D + 2) := rfl
    omega
  · have := star_cnt .hold h1
    simp only [CThread.cfg] at this hh
    omega

end LiveLink
