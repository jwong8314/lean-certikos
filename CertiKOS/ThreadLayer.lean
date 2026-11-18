import CertiKOS.Link

/-!
# A thread layer: threads on one CPU as virtual CPUs

CertiKOS builds a thread-local layer above the CPU-local one: threads that
share a CPU are scheduled cooperatively, and each thread is reasoned about
alone, with the other threads in its environment ([PLDI18] §5). This file is a
minimal version of that step.

* `TStep`: one CPU multiplexing a pool of threads. Only the current thread
  runs. Control moves to another thread only at a yield point of the current
  thread (`Yield`, any predicate on threads: explicit `yield()` calls,
  blocking points, or `fun _ => True` for a preemptive scheduler), or when the
  current thread has finished.
* `tsteps_csteps`: every run of the thread machine is a run of the multicore
  machine in which each thread is a CPU, with fewer interleavings. So every
  safety theorem proved for all multicore runs holds for threads on one CPU.
* `thread_cs_exclusive`: the instance for the ticket lock. Threads of one CPU
  running the lock client exclude each other in their critical sections, with
  thread ids as lock ids.

Not here: the scheduler's own data structures (ready and sleep queues, context
switch), and liveness, which needs the thread scheduler to be fair.
-/

namespace ThreadLayer

open ClightL Ticket ClightToPy TicketPy TicketLive Link

variable {Pn Abs : Type}

structure TState (Pn Abs : Type) where
  cs : List (CThread Pn)
  cur : Nat
  abs : Abs

/-- One CPU running a pool of threads, switching only at yield points. -/
inductive TStep (P : Nat → Prims Pn Abs) (Yield : CThread Pn → Prop) : TState Pn Abs → TState Pn Abs → Prop
  | run {cs : List (CThread Pn)} {cur : Nat} {a : Abs} {c' : Config Pn Abs} (hi : cur < cs.length) :
      ClightL.step (P cur) (cs[cur].cfg a) = some c' →
      TStep P Yield ⟨cs, cur, a⟩ ⟨cs.set cur (thr c'), cur, c'.abs⟩
  | switch {cs : List (CThread Pn)} {cur : Nat} {a : Abs} (j : Nat) :
      (∀ hi : cur < cs.length, Yield cs[cur] ∨ (cs[cur].stmt = .skip ∧ cs[cur].cont = .stop)) →
      TStep P Yield ⟨cs, cur, a⟩ ⟨cs, j, a⟩

inductive TSteps (P : Nat → Prims Pn Abs) (Yield : CThread Pn → Prop) : TState Pn Abs → TState Pn Abs → Prop
  | refl (s) : TSteps P Yield s s
  | step {s s' s''} : TStep P Yield s s' → TSteps P Yield s' s'' → TSteps P Yield s s''

/-- **Threads are virtual CPUs.** A run of the thread machine is a run of the
multicore machine over the same threads. -/
theorem tsteps_csteps {P : Nat → Prims Pn Abs} {Yield : CThread Pn → Prop} {s s' : TState Pn Abs}
    (h : TSteps P Yield s s') : CSteps P s.cs s.abs s'.cs s'.abs := by
  induction h with
  | refl => exact .refl
  | step hs _ ih =>
    cases hs with
    | run hi hst => exact .step (.step _ hi hst) ih
    | switch j _ => exact ih

/-- **Mutual exclusion for threads on one CPU**, for the ticket-lock client:
two threads in their critical sections are the same thread. -/
theorem thread_cs_exclusive (Yield : CThread Prim → Prop) (T N : Nat) (hT : T ≤ NCPU) (hN : N < 2 ^ 32)
    {s : TState Prim Log} (h : TSteps PG Yield ⟨cPool T N, 0, []⟩ s)
    (c d : Nat) (hc : c < s.cs.length) (hd : d < s.cs.length)
    (hcc : InCS N s.cs[c]) (hdc : InCS N s.cs[d]) : c = d :=
  multicore_cs_exclusive T N hT hN (tsteps_csteps h) c d hc hd hcc hdc

end ThreadLayer
