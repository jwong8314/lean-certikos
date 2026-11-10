import CertiKOS.ClightToPy
import CertiKOS.TicketLock

/-!
# The ticket lock, both targets: the C machine and the Python pool are equivalent

The C side is the verified ClightL `acquireCode`/`releaseCode` from
`TicketLock.lean`, run by the multicore machine of `ClightToPy.lean`. Every
CPU appends to the one global log, so the environment context is empty
(`noEnv`), exactly as in `Bench/Sim.lean`.

The Python side is `tr` of the same AST. Each L0 primitive becomes a
`with L:` block over the attributes `lk.ticket` and `lk.now` of object `0`:

```python
with L: _r = lk.ticket; lk.ticket = (_r + 1) % 2**32; x = _r     # FAI_t
with L: x = lk.now                                               # get_n
with L: _r = lk.now; lk.now = (_r + 1) % 2**32; x = 0            # inc_n
with L: x = 0                                                    # hold
```

The heap holds `ticket(log) mod 2³²` and `now(log) mod 2³²` (`R`). The only
reserved Python variable is `$r` (rendered `_r`).

* `primOK`: the four blocks implement the four primitives.
* `python_refines_c`: every run of T Python threads, under any interleaving,
  is matched by a run of the C machine on T CPUs.
* `c_refines_python`: and conversely.
* `python_done`: when all Python threads have finished, all C CPUs have
  finished, and the Python heap is `ticket`/`now` of the C log, mod 2³².
-/

namespace TicketPy

open ClightL Ticket ClightToPy
open PyL (Var Store Heap Cmd Thread Pool MStep MSteps Step)

/-- All CPUs share one global log, so nothing comes from an environment. -/
def noEnv : EnvCtx := ⟨fun _ _ => [], by intro c l e he; simp at he⟩

@[simp] theorem pull_noEnv (c : CPU) (l : Log) : pull noEnv c l = l := rfl

def lk : PyL.Expr := .const 0
def tkLoc : PyL.Loc := ⟨0, "ticket"⟩
def nwLoc : PyL.Loc := ⟨0, "now"⟩

theorem nw_ne_tk : nwLoc ≠ tkLoc := by simp [nwLoc, tkLoc]
theorem tk_ne_nw : tkLoc ≠ nwLoc := by simp [nwLoc, tkLoc]

def Rsv (x : Var) : Prop := x = "$r"

def wrapInc (x : Var) : PyL.Expr := .bin .fmod (.bin .add (.var x) (.const 1)) (.const M)

/-- Python implementations of the L0 primitives (bodies of the `with L:`). -/
def impl : Prim → List PyL.Expr → Var → Cmd
  | .faiTicket, _, x =>
      .seq (.load "$r" lk "ticket") (.seq (.store lk "ticket" (wrapInc "$r")) (.assign x (.var "$r")))
  | .getNow, _, x => .load x lk "now"
  | .incNow, _, x =>
      .seq (.load "$r" lk "now") (.seq (.store lk "now" (wrapInc "$r")) (.assign x (.const 0)))
  | .hold, _, x => .assign x (.const 0)

def arity : Prim → Nat := fun _ => 0

/-- The Python heap holds the replayed counters, mod 2³². -/
def R (l : Log) (H : Heap) : Prop :=
  H tkLoc = some ((ticket l : Int) % M) ∧ H nwLoc = some ((now l : Int) % M)

@[simp] theorem ticket_cons (e : Event) (l : Log) :
    ticket (e :: l) = (if e.kind = .incTicket then 1 else 0) + ticket l := rfl
@[simp] theorem now_cons (e : Event) (l : Log) :
    now (e :: l) = (if e.kind = .incNow then 1 else 0) + now l := rfl

theorem wrap_eq (n : Nat) (r : Int) (hr : r = (n : Int) % M) :
    Int.fmod (r + 1) M = ((1 + n : Nat) : Int) % M := by
  rw [Int.fmod_eq_emod_of_nonneg _ (by decide), hr]; simp only [M]; omega

theorem agree_res {σ : Locals} {s : Store} (hA : Agree Rsv σ s) {x : Var} (hx : ¬ Rsv x)
    (v : Val) (r : Int) (hr : r = enc v) (s' : Store)
    (hs' : ∀ y, y ≠ "$r" → s' y = if y = x then r else s y) : Agree Rsv (σ.set x v) s' := by
  intro y hy
  rw [hs' y hy]
  by_cases e : y = x
  · subst e; simp [hr]
  · simp [e, hA y hy]

theorem primOK : PrimOK impl Rsv arity (fun i => prims noEnv i) R where
  ok := by
    intro i p args x σ s a H v a' hA hx _ hR h
    obtain ⟨hT, hN⟩ := hR
    cases args with
    | cons _ _ => cases p <;> simp [prims] at h
    | nil =>
    cases p with
    | faiTicket =>
      simp only [prims, List.map_nil, pull_noEnv, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨_, _, .step (.seq (.load (v := (ticket a : Int) % M) hT)) (.step .seqSkip
        (.step (.seq (.store (by simp [lk, PyL.Expr.eval, tkLoc] at hT ⊢; simp [hT])))
        (.step .seqSkip (.single .assign)))), ?_, ?_, ?_⟩
      · refine agree_res hA hx _ _ (enc_ofNat _).symm _ fun y hy => ?_
        by_cases e : y = x <;> simp [PyL.Store.set, PyL.Expr.eval, e, hy]
      · simp only [lk, PyL.Expr.eval, PyL.Heap.upd, wrapInc, PyL.BinOp.eval, PyL.Store.set_same]
        simp only [tkLoc, eq_self, ite_true, Option.some.injEq, ticket_cons]
        exact wrap_eq _ _ rfl
      · simp only [lk, PyL.Expr.eval, PyL.Heap.upd]
        rw [ite_eq_right (by simp [nwLoc] : nwLoc ≠ ⟨0, "ticket"⟩)]
        simpa using hN
    | getNow =>
      simp only [prims, List.map_nil, pull_noEnv, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨_, _, .single (.load (v := (now a : Int) % M) hN), ?_, ?_, ?_⟩
      · refine agree_res hA hx _ _ (enc_ofNat _).symm _ fun y hy => ?_
        by_cases e : y = x <;> simp [PyL.Store.set, e]
      · simpa using hT
      · simpa using hN
    | incNow =>
      simp only [prims, List.map_nil, pull_noEnv, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨_, _, .step (.seq (.load (v := (now a : Int) % M) hN)) (.step .seqSkip
        (.step (.seq (.store (by simp [lk, PyL.Expr.eval, nwLoc] at hN ⊢; simp [hN])))
        (.step .seqSkip (.single .assign)))), ?_, ?_, ?_⟩
      · refine agree_res hA hx _ _ rfl _ fun y hy => ?_
        by_cases e : y = x <;> simp [PyL.Store.set, PyL.Expr.eval, e, hy, enc]
      · simp only [lk, PyL.Expr.eval, PyL.Heap.upd]
        rw [ite_eq_right (by simp [tkLoc] : tkLoc ≠ ⟨0, "now"⟩)]
        simpa using hT
      · simp only [lk, PyL.Expr.eval, PyL.Heap.upd, wrapInc, PyL.BinOp.eval, PyL.Store.set_same]
        simp only [nwLoc, eq_self, ite_true, Option.some.injEq, now_cons]
        exact wrap_eq _ _ rfl
    | hold =>
      simp only [prims, List.map_nil, pull_noEnv, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨_, _, .single .assign, ?_, ?_, ?_⟩
      · refine agree_res hA hx _ _ rfl _ fun y hy => ?_
        by_cases e : y = x <;> simp [PyL.Store.set, PyL.Expr.eval, e, enc]
      · simpa using hT
      · simpa using hN
  stuck := by
    intro i p args x σ s a H _ _ _ hlen _ h
    cases args with
    | cons _ _ => simp [arity] at hlen
    | nil => cases p <;> simp [prims] at h

/-! ## The programs -/

/-- `i = 0; while (i != N) { acquire(); release(); i = i + 1; }` (as in
`Bench/Sim.lean`). -/
def clientCode (N : Nat) : Stmt Prim :=
  .seq (.assign "i" (.const 0))
    (.while (.bin .ne (.var "i") (.const (BitVec.ofNat 32 N)))
      (.seq acquireCode (.seq releaseCode (.assign "i" (.bin .add (.var "i") (.const 1))))))

def cThread (N : Nat) : CThread Prim := ⟨clientCode N, .stop, fun _ => 0⟩

/-- T CPUs running the C client. -/
def cPool (T N : Nat) : List (CThread Prim) := List.replicate T (cThread N)

/-- T Python threads running the translated client. -/
def pyPool (T N : Nat) : Pool := List.replicate T ⟨embed impl (cThread N), fun _ => 0⟩

/-- Initial heap: `lk.ticket = lk.now = 0`. -/
def H0 : Heap := fun l => if l = tkLoc ∨ l = nwLoc then some 0 else none

/-- The C machine with the global log. -/
abbrev P : Nat → Prims Prim Log := fun i => prims noEnv i

theorem cThread_wf (N : Nat) : CWF Rsv arity (cThread N) := by
  simp [cThread, CWF, SWF, KWF, EWF, clientCode, acquireCode, acquireLoop, holdCall, releaseCode,
    Rsv, arity]

theorem sync0 (T N : Nat) : Sync impl Rsv arity R (cPool T N) [] (pyPool T N) H0 where
  len := by simp [cPool, pyPool]
  wf i hi := by simp only [cPool, List.getElem_replicate]; exact cThread_wf N
  thr i hi ht := by
    simp only [cPool, pyPool, List.getElem_replicate]
    exact ⟨by trivial, fun _ _ => by simp [cThread, enc]⟩
  heap := by simp [R, H0, tkLoc, nwLoc, ticket, now, countK]

/-- **Python ⇒ C.** Any interleaving of T Python threads running the
translated ticket-lock client is matched by a run of the C machine. -/
theorem python_refines_c (T N : Nat) {k : Nat} {ts : Pool} {H : Heap}
    (h : MSteps k (pyPool T N) H0 ts H) :
    ∃ cs l, CSteps P (cPool T N) [] cs l ∧ Rel impl Rsv arity R cs l ts H :=
  py_to_c primOK (sync_rel (sync0 T N)) h

/-- **C ⇒ Python.** Any run of the C machine is matched by a run of the
Python pool. -/
theorem c_refines_python (T N : Nat) {cs : List (CThread Prim)} {l : Log}
    (h : CSteps P (cPool T N) [] cs l) :
    ∃ k ts H, MSteps k (pyPool T N) H0 ts H ∧ Sync impl Rsv arity R cs l ts H :=
  c_to_py primOK (sync0 T N) h

/-- When all Python threads are done, the C machine has a matching finished
run, and the Python heap is the C log's `ticket`/`now`, mod 2³². -/
theorem python_done (T N : Nat) {k : Nat} {ts : Pool} {H : Heap}
    (h : MSteps k (pyPool T N) H0 ts H) (hdone : ∀ i (hi : i < ts.length), ts[i].cmd = .skip) :
    ∃ cs l, CSteps P (cPool T N) [] cs l ∧
      (∀ i (hi : i < cs.length), cs[i].stmt = .skip ∧ cs[i].cont = .stop) ∧
      H tkLoc = some ((ticket l : Int) % M) ∧ H nwLoc = some ((now l : Int) % M) := by
  obtain ⟨cs, l, hc, hR⟩ := python_refines_c T N h
  obtain ⟨hRH, hfin⟩ := py_done hR hdone
  exact ⟨cs, l, hc, fun i hi => ⟨(hfin i hi (hR.len ▸ hi)).1, (hfin i hi (hR.len ▸ hi)).2.1⟩,
    hRH.1, hRH.2⟩

end TicketPy
