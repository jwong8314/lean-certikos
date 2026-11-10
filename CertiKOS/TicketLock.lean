import CertiKOS.ClightL
import CertiKOS.Determinism

/-!
# Ticket-lock `acquire`: the CertiKOS liveness method, end to end, in miniature

What this file demonstrates (cf. `SCOPING.md` §2 and §4.4):

1. **Logs + environment context.** Shared state is a log of events. Every
   primitive first *pulls* the events other CPUs produced (by querying ε), then
   appends its own event. ε may not return events of the querying CPU.
2. **Deterministic primitives.** The primitive table is a function of
   (CPU, ε, log); all nondeterminism lives in the choice of ε.
3. **Fuel-based spec.** `acquireSpec` is a total Lean function that runs the
   wait loop for at most `fuel` iterations and returns `none` if fuel runs out.
4. **Forward simulation, termination-sensitive.** Whenever the spec returns
   `some r`, the C code reaches a final state whose log is `r`
   (`acquire_sim`). By determinism, the C code therefore cannot diverge
   (`acquire_terminates`).
5. **Liveness under a bounded-fairness rely.** If other CPUs never overtake our
   ticket and the scheduler is fair (a `CalBound`-style counter that must
   decrease whenever no release happens), the spec returns `some` for some
   fuel (`acquire_live`), so `acquire` terminates (`acquire_live_terminates`).
6. **Non-vacuity and vacuity checks.** A concrete ε satisfies the rely
   (`demoEnv_rely`). A forever-spinning `acquire` satisfies a
   partial-correctness refinement (`spin_partial`) but *fails* the
   termination-sensitive one (`spin_not_total`).

The code is CertiKOS's `acq`/`rel` (PLDI'18 Fig. 3), including the `hold()`
call that marks the linearization point. Mutual exclusion, the atomic layer and
the fairness witness are in `TicketProtocol.lean`, `AtomicLayer.lean` and
`FairEnv.lean`. `COMPARISON.md` lists what differs from CertiKOS.
-/

namespace Ticket

open ClightL

abbrev CPU := Nat

/-- Lock events. CertiKOS (PLDI'18 Fig. 3) names them `FAI_t`, `get_n`,
`inc_n` and `hold`; OSDI'16 Fig. 7 calls the last one `pull`. -/
inductive EvKind
  | incTicket | getNow | incNow | hold
  deriving DecidableEq

structure Event where
  cpu : CPU
  kind : EvKind
  deriving DecidableEq

/-- Shared log, newest event first (as in CertiKOS: `e :: l`). -/
abbrev Log := List Event

def countK (k : EvKind) : Log → Nat
  | [] => 0
  | e :: l => (if e.kind = k then 1 else 0) + countK k l

/-- Replay functions: shared state is reconstructed from the log. -/
def ticket (l : Log) : Nat := countK .incTicket l
def now (l : Log) : Nat := countK .incNow l

theorem countK_append (k : EvKind) (xs l : Log) :
    countK k (xs ++ l) = countK k xs + countK k l := by
  induction xs with
  | nil => simp [countK]
  | cons e xs ih => simp [countK, ih, Nat.add_assoc]

@[simp] theorem now_getNow (c : CPU) (l : Log) : now (⟨c, .getNow⟩ :: l) = now l := by
  simp [now, countK]

@[simp] theorem now_incTicket (c : CPU) (l : Log) : now (⟨c, .incTicket⟩ :: l) = now l := by
  simp [now, countK]

@[simp] theorem now_hold (c : CPU) (l : Log) : now (⟨c, .hold⟩ :: l) = now l := by
  simp [now, countK]

/-- Environment context: given the querying CPU and the current log, the
events that other CPUs produced since then. -/
structure EnvCtx where
  query : CPU → Log → List Event
  noSelf : ∀ c l e, e ∈ query c l → e.cpu ≠ c

/-- Query ε and append the returned events to the log. -/
def pull (ε : EnvCtx) (c : CPU) (l : Log) : Log := ε.query c l ++ l

theorem now_pull_ge (ε : EnvCtx) (c : CPU) (l : Log) : now l ≤ now (pull ε c l) := by
  simp [pull, now, countK_append]

/-! ## The underlay layer L0: atomic ticket-lock hardware operations -/

inductive Prim
  | faiTicket | getNow | incNow | hold

/-- Primitive table for CPU `c` under environment `ε`. Each primitive is one
atomic hardware action, hence one event: this is what keeps the model
fine-grained. -/
def prims (ε : EnvCtx) (c : CPU) : Prims Prim Log
  | .faiTicket, [], l =>
      let l1 := pull ε c l
      some (BitVec.ofNat 32 (ticket l1), ⟨c, .incTicket⟩ :: l1)
  | .getNow, [], l =>
      let l1 := pull ε c l
      some (BitVec.ofNat 32 (now l1), ⟨c, .getNow⟩ :: l1)
  | .incNow, [], l =>
      let l1 := pull ε c l
      some (0, ⟨c, .incNow⟩ :: l1)
  | .hold, [], l =>
      let l1 := pull ε c l
      some (0, ⟨c, .hold⟩ :: l1)
  | _, _, _ => none

/-! ## `release` -/

/-- `inc_now();` (the return value is ignored and stored in a dummy local). -/
def releaseCode : Stmt Prim := .call "_" .incNow []

def releaseSpec (ε : EnvCtx) (c : CPU) (l : Log) : Log := ⟨c, .incNow⟩ :: pull ε c l

theorem release_sim (ε : EnvCtx) (c : CPU) (loc : Locals) (l : Log) :
    ∃ loc' : Locals,
      Star (prims ε c) ⟨releaseCode, .stop, loc, l⟩ ⟨.skip, .stop, loc', releaseSpec ε c l⟩ :=
  ⟨loc.set "_" 0, Star.single (by simp [step, prims, releaseCode, releaseSpec])⟩

/-! ## The C code (ClightL) -/

/-- `while (n != t) { n = get_now(); }` -/
def acquireLoop : Stmt Prim :=
  .while (.bin .ne (.var "n") (.var "t")) (.call "n" .getNow [])

/-- `hold();` announces that the lock has been taken (CertiKOS's no-op `hold`
primitive; `pull(i)` in mC2). It is the linearization point of `acquire`. -/
def holdCall : Stmt Prim := .call "_" .hold []

/-- `t = FAI_t(); n = get_n(); while (n != t) { n = get_n(); } hold();`

This is CertiKOS's `acq` (PLDI'18 Fig. 3, lines 12-16):
`uint my_t = FAI_t(); while (get_n() != my_t) {}; hold();`
in Clight form. Clight has no calls inside expressions, so the call in the loop
condition is hoisted into a temporary, as CompCert's `SimplExpr` pass does. -/
def acquireCode : Stmt Prim :=
  .seq (.call "t" .faiTicket []) (.seq (.call "n" .getNow []) (.seq acquireLoop holdCall))

/-! ## The fuel-based spec -/

/-- The wait loop for at most `fuel` iterations (`CalMCS_AcqWait` style). -/
def waitLoop (ε : EnvCtx) (c : CPU) (t : Val) : Nat → Val → Log → Option Log
  | 0, n, l => if n = t then some l else none
  | f + 1, n, l =>
      if n = t then some l
      else waitLoop ε c t f (BitVec.ofNat 32 (now (pull ε c l))) (⟨c, .getNow⟩ :: pull ε c l)

def holdSpec (ε : EnvCtx) (c : CPU) (l : Log) : Log := ⟨c, .hold⟩ :: pull ε c l

def acquireSpec (ε : EnvCtx) (c : CPU) (fuel : Nat) (l : Log) : Option Log :=
  let l1 := pull ε c l
  let t := BitVec.ofNat 32 (ticket l1)
  let l2 := ⟨c, .incTicket⟩ :: l1
  let l3 := pull ε c l2
  (waitLoop ε c t fuel (BitVec.ofNat 32 (now l3)) (⟨c, .getNow⟩ :: l3)).map (holdSpec ε c)

/-- The wait loop that `acquireSpec ε c fuel l` runs. -/
abbrev acqWait (ε : EnvCtx) (c : CPU) (fuel : Nat) (l : Log) : Option Log :=
  waitLoop ε c (BitVec.ofNat 32 (ticket (pull ε c l))) fuel
    (BitVec.ofNat 32 (now (pull ε c (⟨c, .incTicket⟩ :: pull ε c l))))
    (⟨c, .getNow⟩ :: pull ε c (⟨c, .incTicket⟩ :: pull ε c l))

theorem acquireSpec_some {ε : EnvCtx} {c : CPU} {fuel : Nat} {l r : Log}
    (h : acquireSpec ε c fuel l = some r) : ∃ r0, acqWait ε c fuel l = some r0 ∧ r = holdSpec ε c r0 := by
  cases hw : acqWait ε c fuel l with
  | none => simp [acquireSpec, acqWait] at h hw; rw [hw] at h; simp at h
  | some r0 =>
    simp [acquireSpec, acqWait] at h hw; rw [hw] at h; simp at h
    exact ⟨r0, rfl, h.symm⟩

theorem acquireSpec_of_wait {ε : EnvCtx} {c : CPU} {fuel : Nat} {l r0 : Log}
    (h : acqWait ε c fuel l = some r0) : acquireSpec ε c fuel l = some (holdSpec ε c r0) := by
  simp [acquireSpec, acqWait] at h ⊢; exact ⟨r0, h, rfl⟩

/-! ## Forward simulation: spec returns ⇒ C reaches a matching final state -/

theorem loop_sim (ε : EnvCtx) (c : CPU) (t : Val) :
    ∀ (fuel : Nat) (n : Val) (loc : Locals) (l r : Log) (k : Cont Prim),
      loc "t" = t → loc "n" = n → waitLoop ε c t fuel n l = some r →
      ∃ loc' : Locals, loc' "t" = t ∧
        Star (prims ε c) ⟨acquireLoop, k, loc, l⟩ ⟨.skip, k, loc', r⟩ := by
  intro fuel
  induction fuel with
  | zero =>
    intro n loc l r k ht hn hw
    by_cases hnt : n = t
    · simp [waitLoop, hnt] at hw
      subst hw
      refine ⟨loc, ht, Star.single ?_⟩
      simp [step, acquireLoop, Expr.eval, BinOp.eval, ht, hn, hnt]
    · simp [waitLoop, hnt] at hw
  | succ f ih =>
    intro n loc l r k ht hn hw
    by_cases hnt : n = t
    · simp [waitLoop, hnt] at hw
      subst hw
      refine ⟨loc, ht, Star.single ?_⟩
      simp [step, acquireLoop, Expr.eval, BinOp.eval, ht, hn, hnt]
    · simp only [waitLoop, hnt, ite_false] at hw
      let l1 := pull ε c l
      let v := BitVec.ofNat 32 (now l1)
      let loc1 := loc.set "n" v
      have ht1 : loc1 "t" = t := by simp [loc1, ht]
      have hn1 : loc1 "n" = v := by simp [loc1]
      obtain ⟨loc', ht', hstar⟩ := ih v loc1 (⟨c, .getNow⟩ :: l1) r k ht1 hn1 hw
      refine ⟨loc', ht', ?_⟩
      -- while (cond true) → body; body = call get_now → skip; skip/loop → while
      refine .step (c' := ⟨.call "n" .getNow [], .loop (.bin .ne (.var "n") (.var "t"))
          (.call "n" .getNow []) k, loc, l⟩) ?_ ?_
      · simp [step, acquireLoop, Expr.eval, BinOp.eval, ht, hn, hnt]
      refine .step (c' := ⟨.skip, .loop (.bin .ne (.var "n") (.var "t"))
          (.call "n" .getNow []) k, loc1, ⟨c, .getNow⟩ :: l1⟩) ?_ ?_
      · simp [step, prims, loc1, v, l1]
      refine .step (c' := ⟨acquireLoop, k, loc1, ⟨c, .getNow⟩ :: l1⟩) ?_ hstar
      simp [step, acquireLoop]

theorem acquire_sim (ε : EnvCtx) (c : CPU) (fuel : Nat) (loc : Locals) (l r : Log)
    (h : acquireSpec ε c fuel l = some r) :
    ∃ loc' : Locals, Star (prims ε c) ⟨acquireCode, .stop, loc, l⟩ ⟨.skip, .stop, loc', r⟩ := by
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
    loop_sim ε c t fuel n loc2 (⟨c, .getNow⟩ :: l3) r0 (.seq holdCall .stop) ht2 hn2 hw
  refine ⟨loc'.set "_" 0, ?_⟩
  let rest : Stmt Prim := .seq (.call "n" .getNow []) (.seq acquireLoop holdCall)
  refine .step (c' := ⟨.call "t" .faiTicket [], .seq rest .stop, loc, l⟩)
      (by simp [step, acquireCode, rest]) ?_
  refine .step (c' := ⟨.skip, .seq rest .stop, loc1, l2⟩)
      (by simp [step, prims, loc1, t, l2, l1]) ?_
  refine .step (c' := ⟨rest, .stop, loc1, l2⟩) (by simp [step]) ?_
  refine .step (c' := ⟨.call "n" .getNow [], .seq (.seq acquireLoop holdCall) .stop, loc1, l2⟩)
      (by simp [step, rest]) ?_
  refine .step (c' := ⟨.skip, .seq (.seq acquireLoop holdCall) .stop, loc2, ⟨c, .getNow⟩ :: l3⟩)
      (by simp [step, prims, loc2, n, l3]) ?_
  refine .step (c' := ⟨.seq acquireLoop holdCall, .stop, loc2, ⟨c, .getNow⟩ :: l3⟩)
      (by simp [step]) ?_
  refine .step (c' := ⟨acquireLoop, .seq holdCall .stop, loc2, ⟨c, .getNow⟩ :: l3⟩)
      (by simp [step]) ?_
  refine Star.trans hstar ?_
  refine .step (c' := ⟨holdCall, .stop, loc', r0⟩) (by simp [step]) ?_
  exact Star.single (by simp [step, holdCall, prims, holdSpec])

/-- Determinism turns the forward simulation into termination of the C code. -/
theorem acquire_terminates (ε : EnvCtx) (c : CPU) (fuel : Nat) (loc : Locals) (l r : Log)
    (h : acquireSpec ε c fuel l = some r) :
    ¬ Diverges (prims ε c) ⟨acquireCode, .stop, loc, l⟩ := by
  obtain ⟨loc', hstar⟩ := acquire_sim ε c fuel loc l r h
  exact not_diverges_of_star_final hstar ⟨rfl, rfl⟩

/-! ## Liveness: the spec is defined under a bounded-fairness rely -/

/-- Rely condition on ε while CPU `c` waits for ticket `tn`.
* `noOvertake`: other CPUs never push `now` past our ticket (they only
  release a lock they hold, and tickets are served in order).
* `progress`: fairness + bounded critical sections, in `CalBound` style:
  every time we look, either some holder has released (`now` grew) or the
  fairness counter `bound` strictly decreased. -/
structure Rely (ε : EnvCtx) (c : CPU) (tn : Nat) (bound : Log → Nat) : Prop where
  noOvertake : ∀ l, now l ≤ tn → now (pull ε c l) ≤ tn
  progress : ∀ l, now l < tn →
    now l < now (pull ε c l) ∨ bound (⟨c, .getNow⟩ :: pull ε c l) < bound l

theorem waitLoop_mono (ε : EnvCtx) (c : CPU) (t : Val) :
    ∀ f n l r, waitLoop ε c t f n l = some r → waitLoop ε c t (f + 1) n l = some r := by
  intro f
  induction f with
  | zero =>
    intro n l r h
    by_cases hnt : n = t <;> simp_all [waitLoop]
  | succ f ih =>
    intro n l r h
    by_cases hnt : n = t
    · simp_all [waitLoop]
    · simp only [waitLoop, hnt, ite_false] at h ⊢
      exact ih _ _ _ h

theorem waitLoop_live (ε : EnvCtx) (c : CPU) (tn : Nat) (bound : Log → Nat)
    (hr : Rely ε c tn bound) :
    ∀ m b (l : Log), tn - now l = m → bound l = b → now l ≤ tn →
      ∃ f r, waitLoop ε c (BitVec.ofNat 32 tn) f (BitVec.ofNat 32 (now l)) l = some r := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro b
  induction b using Nat.strongRecOn with
  | _ b ihb =>
  intro l hm hb hle
  by_cases hnt : BitVec.ofNat 32 (now l) = BitVec.ofNat 32 tn
  · exact ⟨0, l, by simp [waitLoop, hnt]⟩
  · have hlt : now l < tn := by
      rcases Nat.lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (by rw [h]) hnt
    let l' : Log := ⟨c, .getNow⟩ :: pull ε c l
    have hle' : now l' ≤ tn := by simp [l']; exact hr.noOvertake l hle
    have hge : now l ≤ now l' := by simp [l']; exact now_pull_ge ε c l
    have step_eq : ∀ f, waitLoop ε c (BitVec.ofNat 32 tn) (f + 1) (BitVec.ofNat 32 (now l)) l
        = waitLoop ε c (BitVec.ofNat 32 tn) f (BitVec.ofNat 32 (now l')) l' := by
      intro f; simp [waitLoop, hnt, l']
    rcases hr.progress l hlt with hprog | hbound
    · have hlt' : tn - now l' < m := by simp [l'] at hle' ⊢; omega
      obtain ⟨f, r, hf⟩ := ihm _ hlt' (bound l') l' rfl rfl hle'
      exact ⟨f + 1, r, by rw [step_eq]; exact hf⟩
    · rcases Nat.lt_or_eq_of_le hge with hgt | heq
      · have hlt' : tn - now l' < m := by omega
        obtain ⟨f, r, hf⟩ := ihm _ hlt' (bound l') l' rfl rfl hle'
        exact ⟨f + 1, r, by rw [step_eq]; exact hf⟩
      · have hm' : tn - now l' = m := by omega
        obtain ⟨f, r, hf⟩ := ihb _ (by rw [← hb]; exact hbound) l' hm' rfl hle'
        exact ⟨f + 1, r, by rw [step_eq]; exact hf⟩

/-- Liveness of the spec. `hwf` is the log well-formedness fact `now ≤ ticket`,
which CertiKOS gets from the guarantees on ε. -/
theorem acquire_live (ε : EnvCtx) (c : CPU) (l : Log) (bound : Log → Nat)
    (hr : Rely ε c (ticket (pull ε c l)) bound)
    (hwf : now (pull ε c l) ≤ ticket (pull ε c l)) :
    ∃ fuel r, acquireSpec ε c fuel l = some r := by
  let l1 := pull ε c l
  let tn := ticket l1
  let l2 : Log := ⟨c, .incTicket⟩ :: l1
  let l3 := pull ε c l2
  have h3 : now l3 ≤ tn := hr.noOvertake l2 (by simp [l2]; exact hwf)
  obtain ⟨f, r, hf⟩ := waitLoop_live ε c tn bound hr _ _ (⟨c, .getNow⟩ :: l3) rfl rfl
    (by simp; exact h3)
  refine ⟨f, holdSpec ε c r, acquireSpec_of_wait ?_⟩
  simp only [now_getNow] at hf
  exact hf

/-- End-to-end liveness of the C code: under the rely, `acquire` terminates. -/
theorem acquire_live_terminates (ε : EnvCtx) (c : CPU) (l : Log) (loc : Locals)
    (bound : Log → Nat)
    (hr : Rely ε c (ticket (pull ε c l)) bound)
    (hwf : now (pull ε c l) ≤ ticket (pull ε c l)) :
    ¬ Diverges (prims ε c) ⟨acquireCode, .stop, loc, l⟩ := by
  obtain ⟨fuel, r, h⟩ := acquire_live ε c l bound hr hwf
  exact acquire_terminates ε c fuel loc l r h

/-! ## Non-vacuity: a concrete environment satisfying the rely -/

/-- Another CPU (`c + 1`) releases once per query until `now` reaches `T`. -/
def demoEnv (T : Nat) : EnvCtx where
  query c l := if now l < T then [⟨c + 1, .incNow⟩] else []
  noSelf := by
    intro c l e he
    by_cases h : now l < T
    · simp [h] at he; subst he; simp
    · simp [h] at he

theorem demoEnv_rely (T : Nat) (c : CPU) : Rely (demoEnv T) c T (fun _ => 0) where
  noOvertake := by
    intro l hl
    simp only [pull, demoEnv, now, countK_append] at hl ⊢
    by_cases h : countK .incNow l < T <;> simp [h, countK] <;> omega
  progress := by
    intro l hl
    left
    simp only [pull, demoEnv, now, countK_append] at hl ⊢
    simp [hl, countK]

/-- Two other CPUs already hold tickets 0 and 1. -/
def demoLog : Log := [⟨1, .incTicket⟩, ⟨2, .incTicket⟩]

theorem demo_acquire_terminates (loc : Locals) :
    ¬ Diverges (prims (demoEnv 2) 0) ⟨acquireCode, .stop, loc, demoLog⟩ := by
  have hT : ticket (pull (demoEnv 2) 0 demoLog) = 2 := by decide
  have hr := demoEnv_rely 2 0
  rw [← hT] at hr
  exact acquire_live_terminates (demoEnv 2) 0 demoLog loc (fun _ => 0) hr (by decide)

/-! ## Vacuity check: why the refinement must be termination-sensitive -/

/-- A broken `acquire` that takes a ticket and then spins forever. -/
def spinCode : Stmt Prim :=
  .seq (.call "t" .faiTicket []) (.while (.const 1) .skip)

/-- Partial-correctness refinement (the shape of Clift's `corres`): every run
that *terminates* matches the spec. -/
def PartialRefines (ε : EnvCtx) (c : CPU) (code : Stmt Prim)
    (spec : Nat → Log → Option Log) : Prop :=
  ∀ l loc (cfg : Config Prim Log), Star (prims ε c) ⟨code, .stop, loc, l⟩ cfg → Final cfg →
    ∃ fuel, spec fuel l = some cfg.abs

/-- Termination-sensitive refinement (CertiKOS style): whenever the spec
returns, the code reaches a matching final state. -/
def TotalRefines (ε : EnvCtx) (c : CPU) (code : Stmt Prim)
    (spec : Nat → Log → Option Log) : Prop :=
  ∀ fuel l r loc, spec fuel l = some r →
    ∃ cfg : Config Prim Log, Star (prims ε c) ⟨code, .stop, loc, l⟩ cfg ∧ Final cfg ∧ cfg.abs = r

theorem acquire_total (ε : EnvCtx) (c : CPU) :
    TotalRefines ε c acquireCode (acquireSpec ε c) := by
  intro fuel l r loc h
  obtain ⟨loc', hstar⟩ := acquire_sim ε c fuel loc l r h
  exact ⟨_, hstar, ⟨rfl, rfl⟩, rfl⟩

private def spinW : Stmt Prim := .while (.const 1) .skip

/-- Invariant: the reachable shapes of the spinner. None of them is final. -/
private def SpinInv (cfg : Config Prim Log) : Prop :=
  (cfg.stmt = spinCode ∧ cfg.cont = .stop) ∨
  (cfg.stmt = .call "t" .faiTicket [] ∧ cfg.cont = .seq spinW .stop) ∨
  (cfg.stmt = .skip ∧ cfg.cont = .seq spinW .stop) ∨
  (cfg.stmt = spinW ∧ cfg.cont = .stop) ∨
  (cfg.stmt = .skip ∧ cfg.cont = .loop (.const 1) .skip .stop)

private theorem spinInv_step (ε : EnvCtx) (c : CPU) {cfg cfg' : Config Prim Log}
    (hs : step (prims ε c) cfg = some cfg') (hi : SpinInv cfg) : SpinInv cfg' := by
  obtain ⟨stmt, cont, loc, l⟩ := cfg
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    simp only at h1 h2 <;> subst h1 <;> subst h2
  · simp [step, spinCode] at hs; subst hs; simp [SpinInv, spinW]
  · simp [step, prims] at hs; subst hs; simp [SpinInv, spinW]
  · simp [step] at hs; subst hs; simp [SpinInv, spinW]
  · simp [step, spinW, Expr.eval] at hs; subst hs; simp [SpinInv, spinW]
  · simp [step] at hs; subst hs; simp [SpinInv, spinW]

private theorem spinInv_not_final {cfg : Config Prim Log} (hi : SpinInv cfg) : ¬ Final cfg := by
  rintro ⟨h1, h2⟩
  rcases hi with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;>
    simp_all [spinCode, spinW]

theorem spin_never_final (ε : EnvCtx) (c : CPU) (loc : Locals) (l : Log)
    {cfg : Config Prim Log} (h : Star (prims ε c) ⟨spinCode, .stop, loc, l⟩ cfg) : ¬ Final cfg := by
  have : ∀ a b, Star (prims ε c) a b → SpinInv a → SpinInv b := by
    intro a b hab
    induction hab with
    | refl => exact id
    | step hs _ ih => exact fun hi => ih (spinInv_step ε c hs hi)
  exact spinInv_not_final (this _ _ h (Or.inl ⟨rfl, rfl⟩))

/-- The spinner *passes* the partial-correctness check, vacuously. -/
theorem spin_partial (ε : EnvCtx) (c : CPU) :
    PartialRefines ε c spinCode (acquireSpec ε c) := by
  intro l loc cfg hstar hfinal
  exact absurd hfinal (spin_never_final ε c loc l hstar)

/-- …and *fails* the termination-sensitive check. -/
theorem spin_not_total : ¬ TotalRefines (demoEnv 2) 0 spinCode (acquireSpec (demoEnv 2) 0) := by
  intro htot
  have hT : ticket (pull (demoEnv 2) 0 demoLog) = 2 := by decide
  have hr := demoEnv_rely 2 0
  rw [← hT] at hr
  obtain ⟨fuel, r, hspec⟩ := acquire_live (demoEnv 2) 0 demoLog (fun _ => 0) hr (by decide)
  obtain ⟨cfg, hstar, hfinal, _⟩ := htot fuel demoLog r (fun _ => 0) hspec
  exact spin_never_final (demoEnv 2) 0 _ _ hstar hfinal

end Ticket
