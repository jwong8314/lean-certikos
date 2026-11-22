import CertiKOS.MC2Sched

/-!
# mC2: the thread layers

Above the scheduling layer `L_btd[c]` (`MC2Sched`), mC2 reasons about one
thread at a time ([PLDI18] §5.2–5.3). In the thread-local layer `L[c][t]`,
`yield` and `sleep` always come back to `t`, so they act as no-ops on `t`'s
kernel context and update only the log. This needs the software scheduler to
be fair.

* `TSt`: the scheduling state with each CPU's registers `regs c` and each
  thread's saved kernel context `kctx t` (what `cswitch` saves: `ra, ebp,
  ebx, esi, edi, esp`; here any type `Ctx`).
* `tstep`: a scheduler step (`MC2Sched.stepE`) with `cswitch`: a thread that
  stops running (`yield2`, `sleep1`) has its registers saved, and the thread
  `pick` chooses has its context loaded. Or a step of the running thread
  itself, `run t f`, which changes the registers by `f`.
* `ctxOf ts t`: thread `t`'s context, in the registers of its CPU while it
  runs, saved otherwise.
* `sched_noop`: **every scheduler step, on any CPU, leaves every thread's
  context unchanged.** `run_local`: a thread's own step changes only its own
  context.
* `ctx_local`: **the thread-local layer.** After any interleaving of all
  CPUs and threads, thread `t`'s context is its initial context with `t`'s own
  steps applied, in order: other threads, other CPUs, and the scheduler are
  invisible to it.
* `ahead_step`, `ready_runs`: **the software scheduler is fair.** A ready
  thread with `k` threads ahead of it on its CPU's ready queue keeps its
  place (new threads join behind it, other CPUs never touch the queue), moves
  up at every `pick` of its CPU, and has run by its CPU's `(k+1)`-th `pick`.

Together these are what `L[c][t]` needs: from `t`'s point of view a
`yield` returns, with its context as it left it, after its CPU has run each
thread ahead of it once.
-/

set_option linter.unusedVariables false

namespace MC2Thread

open MC2 MC2Queue MC2Sched

variable (np : Nat) (own : Nat → Nat) {Ctx : Type}

/-! ## The state with contexts -/

structure TSt (Ctx : Type) where
  s : St
  regs : Nat → Ctx
  kctx : Nat → Ctx

inductive TEv (Ctx : Type)
  | sched (e : SOp)
  | run (t : Nat) (f : Ctx → Ctx)

/-- The steps after which the running thread has stopped. -/
def saves : SOp → Bool
  | .yield2 => true
  | .sleep1 _ => true
  | _ => false

/-- The saved contexts after a step of CPU `c` that may save its running
thread. -/
def saveK (ts : TSt Ctx) (c : Nat) (e : SOp) : Nat → Ctx :=
  match saves e, (ts.s.pv c).cur with
  | true, some t => upd ts.kctx t (ts.regs c)
  | _, _ => ts.kctx

/-- The registers after a step: `pick` loads the chosen thread's context. -/
def loadR (ts : TSt Ctx) (c : Nat) (e : SOp) (s' : St) (k : Nat → Ctx) : Nat → Ctx :=
  match e, (s'.pv c).cur with
  | .pick, some n => upd ts.regs c (k n)
  | _, _ => ts.regs

/-- **One step of CPU `c`.** -/
def tstep (ts : TSt Ctx) (c : Nat) : TEv Ctx → Option (TSt Ctx)
  | .sched e => (stepE np own ts.s c e).map fun s' => ⟨s', loadR ts c e s' (saveK ts c e), saveK ts c e⟩
  | .run t f =>
    if (ts.s.pv c).cur = some t ∧ (ts.s.pv c).pc = .idle then
      some ⟨ts.s, upd ts.regs c (f (ts.regs c)), ts.kctx⟩
    else none

/-- At the start every thread has its initial context `ctx0 t`. -/
def tinit (ctx0 : Nat → Ctx) : TSt Ctx := ⟨init np own, ctx0, ctx0⟩

def treplay (ctx0 : Nat → Ctx) : List (Nat × TEv Ctx) → Option (TSt Ctx)
  | [] => some (tinit np own ctx0)
  | (c, e) :: L => (treplay ctx0 L).bind (fun ts => tstep np own ts c e)

/-- Thread `t`'s context. -/
def ctxOf (ts : TSt Ctx) (t : Nat) : Ctx :=
  if (ts.s.pv (own t)).cur = some t then ts.regs (own t) else ts.kctx t

/-- `t`'s own steps in a log, applied in order. -/
def tfold (ctx0 : Nat → Ctx) (t : Nat) : List (Nat × TEv Ctx) → Ctx
  | [] => ctx0 t
  | (_, .run u f) :: L => if u = t then f (tfold ctx0 t L) else tfold ctx0 t L
  | (_, .sched _) :: L => tfold ctx0 t L

/-! ## What a scheduler step changes -/

variable {np own}

theorem stepE_other {s s' : St} {c : Nat} {e : SOp} (h : stepE np own s c e = some s') {c' : Nat} (hc : c' ≠ c) :
    s'.pv c' = s.pv c' := by
  cases e <;> simp only [stepE] at h <;> split at h <;> (try cases h) <;> (try split) <;> (try split) <;>
    simp [upd, hc]

/-- How a step of CPU `c` changes its running thread. -/
theorem stepE_cur {s s' : St} {c : Nat} {e : SOp} (h : stepE np own s c e = some s') :
    (saves e = true → (s'.pv c).cur = none) ∧
    (e = .pick → (s.pv c).cur = none) ∧
    (saves e = false → e ≠ .pick → (s'.pv c).cur = (s.pv c).cur) ∧
    ((s.pv c).cur = none → e ≠ .yield2 → saves e = true → False) := by
  cases e <;> simp only [stepE] at h <;> split at h <;> (try cases h) <;> (try split) <;> (try split) <;>
    simp_all [saves]

/-- **A scheduler step leaves every thread's context unchanged.** -/
theorem sched_noop {ts ts' : TSt Ctx} {c : Nat} {e : SOp} (hW : Wf np own ts.s)
    (h : tstep np own ts c (.sched e) = some ts') (u : Nat) : ctxOf own ts' u = ctxOf own ts u := by
  simp only [tstep, Option.map_eq_some_iff] at h
  obtain ⟨s', hs, rfl⟩ := h
  obtain ⟨hsv, hpk, hsame, -⟩ := stepE_cur hs
  unfold ctxOf
  by_cases hu : own u = c
  · subst hu
    cases hsv' : saves e
    · -- no save: the saved contexts are unchanged
      have hk : saveK ts (own u) e = ts.kctx := by simp [saveK, hsv']
      simp only [hk]
      by_cases hp : e = .pick
      · subst hp
        rw [hpk rfl]
        cases hn : (s'.pv (own u)).cur with
        | none => simp [loadR, hn]
        | some n =>
          simp only [loadR, hn, upd_self]
          by_cases e : n = u
          · subst e; simp
          · simp [e]
      · have hc := hsame hsv' hp
        have hr : loadR ts (own u) e s' ts.kctx = ts.regs := by
          unfold loadR; split
          · next h1 => exact absurd rfl hp
          · rfl
        rw [hr, hc]
    · rw [hsv hsv']
      have hr : loadR ts (own u) e s' (saveK ts (own u) e) = ts.regs := by
        unfold loadR; split
        · next => simp [saves] at hsv'
        · rfl
      rw [hr]
      simp only [reduceCtorEq, ite_false]
      unfold saveK; rw [hsv']
      cases hc : (ts.s.pv (own u)).cur with
      | none => simp
      | some t =>
        simp only
        by_cases e : u = t
        · subst e; simp
        · simp [upd, e, Ne.symm e]
  · rw [stepE_other hs hu]
    have hr : loadR ts c e s' (saveK ts c e) (own u) = ts.regs (own u) := by
      unfold loadR; cases e <;> (cases (s'.pv c).cur) <;> simp [upd, hu]
    dsimp only
    rw [hr]
    have hk : saveK ts c e u = ts.kctx u := by
      unfold saveK
      cases hct : (ts.s.pv c).cur with
      | none => cases saves e <;> rfl
      | some t =>
        have ht : t ∈ view np ts.s (.run c) := by simp [view, hct]
        have : own t = c := ok_of_mem hW ht
        have hne : u ≠ t := fun e => hu (e ▸ this)
        cases saves e <;> simp [upd, hne]
    rw [hk]

/-- **A thread's own step changes only its own context.** -/
theorem run_local {ts ts' : TSt Ctx} {c t : Nat} {f : Ctx → Ctx} (hW : Wf np own ts.s)
    (h : tstep np own ts c (.run t f) = some ts') (u : Nat) :
    ctxOf own ts' u = if u = t then f (ctxOf own ts u) else ctxOf own ts u := by
  simp only [tstep] at h
  split at h
  · next hc =>
    cases h
    obtain ⟨hcur, -⟩ := hc
    have ht : t ∈ view np ts.s (.run c) := by simp [view, hcur]
    have ho : own t = c := ok_of_mem hW ht
    unfold ctxOf
    by_cases e : u = t
    · subst e; subst ho; simp [hcur]
    · simp only [e, ite_false]
      by_cases hu : own u = c
      · subst hu; rw [hcur]; simp [Ne.symm e]
      · simp [upd, hu]
  · cases h

/-- **The thread-local layer `L[c][t]`.** After any interleaving of the CPUs'
scheduler steps and the threads' own steps, each thread's context is its
initial context with its own steps applied: nothing else is visible to it. -/
theorem ctx_local (ctx0 : Nat → Ctx) {L : List (Nat × TEv Ctx)} {ts : TSt Ctx}
    (h : treplay np own ctx0 L = some ts) : Wf np own ts.s ∧ ∀ t, ctxOf own ts t = tfold ctx0 t L := by
  induction L generalizing ts with
  | nil =>
    simp only [treplay, Option.some.injEq] at h; subst h
    refine ⟨wf_init, fun t => ?_⟩
    simp [ctxOf, tinit, init, tfold]
  | cons ce L ih =>
    obtain ⟨c, e⟩ := ce
    simp only [treplay] at h
    cases hL : treplay np own ctx0 L with
    | none => rw [hL] at h; cases h
    | some ts0 =>
      rw [hL] at h
      simp only [Option.bind] at h
      obtain ⟨hW, hc⟩ := ih hL
      cases e with
      | sched e =>
        have hs := h
        simp only [tstep, Option.map_eq_some_iff] at hs
        obtain ⟨s', hs', rfl⟩ := hs
        refine ⟨wf_step hW hs', fun t => ?_⟩
        rw [sched_noop hW h, hc]; rfl
      | run u f =>
        have hs := h
        simp only [tstep] at hs
        split at hs
        · cases hs
          refine ⟨hW, fun t => ?_⟩
          rw [run_local hW h, hc]; simp only [tfold]
          by_cases e : t = u
          · subst e; simp
          · simp [e, Ne.symm e]
        · cases hs

/-! ## The software scheduler is fair -/

/-- The threads ahead of `t` on a queue (tail first: those after it). -/
def ahead : List Nat → Nat → Nat
  | [], _ => 0
  | x :: l, t => if x = t then l.length else ahead l t

theorem ahead_cons_ne {x t : Nat} (l : List Nat) (h : x ≠ t) : ahead (x :: l) t = ahead l t := by
  simp [ahead, h]

theorem ahead_snoc {t a : Nat} : ∀ {l : List Nat}, t ∈ l → ahead (l ++ [a]) t = ahead l t + 1
  | [], ht => by simp at ht
  | x :: l, ht => by
    by_cases e : x = t
    · simp [ahead, e]
    · have ht' : t ∈ l := by
        rcases List.mem_cons.1 ht with h | h
        · exact absurd h.symm e
        · exact h
      simp only [List.cons_append, ahead, e, ite_false]; exact ahead_snoc ht'

/-- A step that puts `x`, found elsewhere, at the tail of the ready queue. -/
theorem left_cons {s : St} (hW : Wf np own s) {c t x : Nat} {p : Place} (ht : t ∈ (s.pv c).rdq)
    (hx : x ∈ view np s p) (hp : p ≠ .ready c) :
    t ∈ x :: (s.pv c).rdq ∧ ahead (x :: (s.pv c).rdq) t ≤ ahead (s.pv c).rdq t := by
  have hne : x ≠ t := fun e => hp (uniq hW hx (e ▸ ht : x ∈ view np s (.ready c)))
  exact ⟨List.mem_cons_of_mem _ ht, by rw [ahead_cons_ne _ hne]; exact Nat.le_refl _⟩

/-- **A ready thread keeps its place and moves up at each `pick`.** Steps of
other CPUs do not touch its queue; new threads join behind it; at a `pick` of
its CPU it either runs or has one thread fewer ahead of it. -/
theorem ahead_step {s s' : St} (hW : Wf np own s) {c t c' : Nat} {e : SOp} (ht : t ∈ (s.pv c).rdq)
    (h : stepE np own s c' e = some s') :
    (t ∈ (s'.pv c).rdq ∧ ahead (s'.pv c).rdq t ≤ ahead (s.pv c).rdq t ∧
      (c' = c → e = .pick → ahead (s'.pv c).rdq t < ahead (s.pv c).rdq t)) ∨
    (c' = c ∧ e = .pick ∧ (s'.pv c).cur = some t) := by
  by_cases hc : c' = c
  · subst hc
    have hr : t ∈ view np s (.ready c') := ht
    cases e with
    | yield1 =>
      simp only [stepE] at h; split at h
      · cases h
        obtain ⟨l, hl⟩ := qs_some hW (.pend c')
        rw [qres_eq np hl]
        refine .inl ?_
        simp only [upd_self]
        split
        · exact ⟨ht, Nat.le_refl _, fun _ e => by cases e⟩
        · next hn =>
          have hne : l ≠ [] := fun e => hn (by subst e; rfl)
          have hx : l.getLastD np ∈ view np s (.pend c') := by simp only [view, hl, Option.getD]; exact getLastD_mem hne
          obtain ⟨a, b⟩ := left_cons hW ht hx (by simp)
          exact ⟨a, b, fun _ e => by cases e⟩
      · cases h
    | yield2 =>
      simp only [stepE] at h; split at h
      · cases h
        refine .inl ?_
        simp only [upd_self]
        cases hcur : (s.pv c').cur with
        | none => exact ⟨ht, Nat.le_refl _, fun _ e => by cases e⟩
        | some x =>
          have hx : x ∈ view np s (.run c') := by simp [view, hcur]
          obtain ⟨a, b⟩ := left_cons hW ht hx (by simp)
          exact ⟨a, b, fun _ e => by cases e⟩
      · cases h
    | sleep1 i =>
      simp only [stepE] at h; split at h
      · cases h; exact .inl ⟨by simpa using ht, by simp, fun _ e => by cases e⟩
      · cases h
    | pick =>
      simp only [stepE] at h; split at h
      · cases h
        have hne : (s.pv c').rdq ≠ [] := fun e => by rw [e] at ht; simp at ht
        simp only [upd_self, pickP, if_neg hne]
        by_cases hh : (s.pv c').rdq.getLastD np = t
        · exact .inr ⟨by simp, by simp, by rw [hh]⟩
        · refine .inl ?_
          have hnod : (s.pv c').rdq.Nodup := hW.2.1 (.ready c')
          have hm : t ∈ (s.pv c').rdq.dropLast := (mem_dropLast hnod hne).2 ⟨ht, Ne.symm hh⟩
          rcases List.eq_nil_or_concat (s.pv c').rdq with e | ⟨l', a, e⟩
          · exact absurd e hne
          · rw [List.concat_eq_append] at e
            rw [e, List.dropLast_concat] at hm ⊢
            rw [ahead_snoc hm]
            exact ⟨hm, Nat.le_succ _, fun _ _ => Nat.lt_succ_self _⟩
      · cases h
    | wake1 i =>
      simp only [stepE] at h; split at h
      · cases h
        obtain ⟨l, hl⟩ := qs_some hW (.sleep i)
        rw [qres_eq np hl]
        refine .inl ?_
        split
        · exact ⟨ht, Nat.le_refl _, fun _ e => by cases e⟩
        · next hn =>
          split
          · simp only [upd_self]
            have hne : l ≠ [] := fun e => hn (by subst e; rfl)
            have hx : l.getLastD np ∈ view np s (.sleep i) := by simp only [view, hl, Option.getD]; exact getLastD_mem hne
            obtain ⟨a, b⟩ := left_cons hW ht hx (by simp)
            exact ⟨a, b, fun _ e => by cases e⟩
          · simp only [upd_self]; exact ⟨ht, Nat.le_refl _, fun _ e => by cases e⟩
      · cases h
    | wake2 =>
      simp only [stepE] at h; split at h
      · cases h; exact .inl ⟨by simpa using ht, by simp, fun _ e => by cases e⟩
      · cases h
  · rw [stepE_other h (Ne.symm hc)]
    exact .inl ⟨ht, Nat.le_refl _, fun e => absurd e hc⟩

def isPick : SOp → Bool
  | .pick => true
  | _ => false

/-- The `pick`s of CPU `c` in a log. -/
def npick (c : Nat) : List (Nat × SOp) → Nat
  | [] => 0
  | (c', e) :: L => (if c' = c ∧ isPick e = true then 1 else 0) + npick c L

/-- **Fairness of the software scheduler.** If thread `t` is ready on CPU `c`
after the log `L1`, then after any further steps `L2` of all CPUs, either `t`
is still ready with fewer threads ahead of it by the number of `c`'s `pick`s in
`L2`, or `t` has run on `c` at some point of `L2`. -/
theorem ready_runs {L1 : List (Nat × SOp)} {s1 : St} (h1 : replayS np own L1 = some s1) {c t : Nat}
    (ht : t ∈ (s1.pv c).rdq) : ∀ (L2 : List (Nat × SOp)) {s2 : St}, replayS np own (L2 ++ L1) = some s2 →
    (t ∈ (s2.pv c).rdq ∧ ahead (s2.pv c).rdq t + npick c L2 ≤ ahead (s1.pv c).rdq t) ∨
    ∃ L' L'', L2 = L'' ++ L' ∧ Rsched np own (L' ++ L1) c = some t
  | [], s2, h2 => by
    simp only [List.nil_append] at h2
    rw [h1] at h2; cases h2
    exact .inl ⟨ht, by simp [npick]⟩
  | (c', e) :: L2, s2, h2 => by
    simp only [List.cons_append, replayS] at h2
    cases hm : replayS np own (L2 ++ L1) with
    | none => rw [hm] at h2; cases h2
    | some sm =>
      rw [hm] at h2; simp only [Option.bind] at h2
      rcases ready_runs h1 ht L2 hm with ⟨htm, hle⟩ | ⟨L', L'', e2, hR⟩
      · rcases ahead_step (wf_replay hm) htm h2 with ⟨ht2, hle2, hlt⟩ | ⟨rfl, rfl, hcur⟩
        · refine .inl ⟨ht2, ?_⟩
          simp only [npick]
          by_cases hp : c' = c ∧ isPick e = true
          · obtain ⟨rfl, hpk⟩ := hp
            have : e = .pick := by cases e <;> simp_all [isPick]
            have := hlt rfl this
            simp only [isPick, true_and]; rw [if_pos (by simp_all)]; omega
          · rw [if_neg hp]; omega
        · refine .inr ⟨(c', .pick) :: L2, [], rfl, ?_⟩
          simp only [Rsched, List.cons_append, replayS, hm, Option.bind, h2, hcur]
      · exact .inr ⟨L', (c', e) :: L'', by rw [e2]; rfl, hR⟩

/-- **A ready thread runs by its CPU's `(k+1)`-th `pick`**, `k` the threads
ahead of it. -/
theorem ready_runs' {L1 L2 : List (Nat × SOp)} {s1 s2 : St} (h1 : replayS np own L1 = some s1)
    (h2 : replayS np own (L2 ++ L1) = some s2) {c t : Nat} (ht : t ∈ (s1.pv c).rdq)
    (hk : ahead (s1.pv c).rdq t < npick c L2) :
    ∃ L' L'', L2 = L'' ++ L' ∧ Rsched np own (L' ++ L1) c = some t := by
  rcases ready_runs h1 ht L2 h2 with ⟨-, hle⟩ | h
  · omega
  · exact h

end MC2Thread
