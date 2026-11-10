/-!
# PyL: a small concurrent Python subset with a small-step semantics

PyL is the Python-side counterpart of `ClightL`. It models the part of Python
that systems code written in the style of `bench/py_threads.py` uses:

* **Values are Python `int`s** (unbounded `Int`). Booleans are `1`/`0`, as in
  Python where `True == 1`. Truthiness is "non-zero". `//` and `%` are floor
  division and floor modulo (`Int.fdiv`, `Int.fmod`), which is what Python
  computes. 32-bit wraparound is written explicitly, e.g. `(x + 1) % 2**32`.
* **Each thread has its own local variables** (a Python frame). Locals are
  never shared. All shared state lives in the **heap of object attributes**:
  a location is `(object id, attribute name)`, i.e. `o.f`.
* Statements: `pass`, `x = e`, `x = o.f`, `o.f = e`, `;`, `if`, `while`, and
  `with L: c` for one global `threading.Lock` `L`, written `atomic c`.
  Expressions only read locals; attribute reads are separate statements. This
  is the same A-normal form as `ClightL`, where calls are hoisted out of
  expressions.
* **Granularity.** One step performs at most one heap access. `x = o.f` and
  `o.f = e` are single bytecodes (`LOAD_ATTR`, `STORE_ATTR`) once the
  operands are locals. CPython executes each atomically under the GIL, and
  free-threaded CPython does too via per-object locking. All other steps touch
  only the thread's own frame, so their interleaving cannot be observed.
* `atomic c` takes the global lock: it may start only when no other thread is
  inside an `atomic`. Other threads keep running their non-atomic code
  meanwhile, exactly as with `with L:` in Python. `inAtomic c` is the
  run-time form "inside the block, `c` left to run".

Not modelled: allocation of new objects, creating attributes (stores need an
existing attribute), exceptions (division by zero yields `0` rather than
raising), function calls, and more than one lock.

Faults. Reading or writing an attribute that is not in the heap is a fault.
The separation logic in `PyCSL.lean` proves that verified programs never
fault and never race.
-/

namespace PyL

abbrev Var := String
abbrev Store := Var → Int

def Store.set (s : Store) (x : Var) (v : Int) : Store :=
  fun y => if y = x then v else s y

@[simp] theorem Store.set_same (s : Store) (x : Var) (v : Int) : s.set x v x = v := by
  simp [Store.set]

@[simp] theorem Store.set_other (s : Store) {x y : Var} (v : Int) (h : y ≠ x) :
    s.set x v y = s y := by simp [Store.set, h]

/-- A heap location: attribute `attr` of the object with id `obj`. -/
structure Loc where
  obj : Int
  attr : String
deriving DecidableEq, Repr

/-- The attribute heap (partial). -/
abbrev Heap := Loc → Option Int

/-! ## Heap algebra -/

namespace Heap

def emp : Heap := fun _ => none
def single (l : Loc) (v : Int) : Heap := fun l' => if l' = l then some v else none
def upd (h : Heap) (l : Loc) (v : Int) : Heap := fun l' => if l' = l then some v else h l'
/-- Union, left-biased (only used on disjoint heaps). -/
def union (h₁ h₂ : Heap) : Heap := fun l => (h₁ l).or (h₂ l)
def Disj (h₁ h₂ : Heap) : Prop := ∀ l, h₁ l = none ∨ h₂ l = none

scoped infixl:65 " ⊎ " => Heap.union

@[simp] theorem emp_apply (l : Loc) : emp l = none := rfl
theorem union_apply (h₁ h₂ : Heap) (l : Loc) : (h₁ ⊎ h₂) l = (h₁ l).or (h₂ l) := rfl
@[simp] theorem single_same (l : Loc) (v : Int) : single l v l = some v := by simp [single]
theorem single_other {l l' : Loc} (v : Int) (h : l' ≠ l) : single l v l' = none := by
  simp [single, h]
@[simp] theorem upd_same (h : Heap) (l : Loc) (v : Int) : h.upd l v l = some v := by simp [upd]
theorem upd_other (h : Heap) {l l' : Loc} (v : Int) (hne : l' ≠ l) : h.upd l v l' = h l' := by
  simp [upd, hne]

@[simp] theorem emp_union (h : Heap) : emp ⊎ h = h := by
  funext l; simp [union_apply]
@[simp] theorem union_emp (h : Heap) : h ⊎ emp = h := by
  funext l; simp only [union_apply, emp_apply]; cases h l <;> rfl

theorem union_assoc (a b c : Heap) : a ⊎ b ⊎ c = a ⊎ (b ⊎ c) := by
  funext l; simp only [union_apply]; cases a l <;> rfl

theorem Disj.symm {a b : Heap} (h : Disj a b) : Disj b a := fun l => (h l).symm

theorem union_comm {a b : Heap} (h : Disj a b) : a ⊎ b = b ⊎ a := by
  funext l; simp only [union_apply]
  rcases h l with e | e <;> simp [e]

theorem union_left_comm {a b : Heap} (c : Heap) (h : Disj a b) : a ⊎ (b ⊎ c) = b ⊎ (a ⊎ c) := by
  rw [← union_assoc, union_comm h, union_assoc]

@[simp] theorem disj_emp_left (h : Heap) : Disj emp h := fun _ => .inl rfl
@[simp] theorem disj_emp_right (h : Heap) : Disj h emp := fun _ => .inr rfl

theorem or_eq_none {a b : Option Int} : a.or b = none ↔ a = none ∧ b = none := by
  cases a <;> simp

theorem disj_union_left {a b c : Heap} : Disj (a ⊎ b) c ↔ Disj a c ∧ Disj b c := by
  constructor
  · intro h
    refine ⟨fun l => ?_, fun l => ?_⟩ <;> rcases h l with e | e <;>
      simp_all [union_apply]
  · rintro ⟨h₁, h₂⟩ l
    rcases h₁ l with e | e <;> rcases h₂ l with f | f <;> simp_all [union_apply]

theorem disj_union_right {a b c : Heap} : Disj a (b ⊎ c) ↔ Disj a b ∧ Disj a c := by
  constructor
  · intro h; have := disj_union_left.1 h.symm; exact ⟨this.1.symm, this.2.symm⟩
  · rintro ⟨h₁, h₂⟩; exact (disj_union_left.2 ⟨h₁.symm, h₂.symm⟩).symm

theorem union_some_left {a b : Heap} {l : Loc} {v : Int} (h : a l = some v) :
    (a ⊎ b) l = some v := by simp [union_apply, h]

theorem union_none_left {a b : Heap} {l : Loc} (h : a l = none) : (a ⊎ b) l = b l := by
  simp [union_apply, h]

theorem union_ne_none_left {a b : Heap} {l : Loc} (h : a l ≠ none) : (a ⊎ b) l ≠ none := by
  cases e : a l with
  | none => exact absurd e h
  | some v => simp [union_apply, e]

/-- Writing to a location owned by the left part. -/
theorem upd_union_left {a b : Heap} {l : Loc} (v : Int) (h : a l ≠ none) :
    (a ⊎ b).upd l v = a.upd l v ⊎ b := by
  funext l'
  by_cases e : l' = l
  · subst e; simp [union_apply, upd]
  · simp [union_apply, upd, e]

theorem disj_upd_left {a b : Heap} {l : Loc} (v : Int) (hd : Disj a b) (h : a l ≠ none) :
    Disj (a.upd l v) b := by
  intro l'
  by_cases e : l' = l
  · subst e; rcases hd l' with f | f
    · exact absurd f h
    · exact .inr f
  · rw [upd_other _ _ e]; exact hd l'

end Heap

open Heap

/-! ## Syntax -/

inductive BinOp
  | add | sub | mul | fdiv | fmod | eq | ne | lt | le
deriving DecidableEq, Repr

/-- Python's semantics of the operators on `int`. Comparisons return
`True`/`False`, i.e. `1`/`0`. -/
def BinOp.eval : BinOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .fdiv, a, b => Int.fdiv a b
  | .fmod, a, b => Int.fmod a b
  | .eq, a, b => if a = b then 1 else 0
  | .ne, a, b => if a = b then 0 else 1
  | .lt, a, b => if a < b then 1 else 0
  | .le, a, b => if a ≤ b then 1 else 0

inductive Expr
  | const (v : Int)
  | var (x : Var)
  | bin (op : BinOp) (a b : Expr)
  | not (a : Expr)
deriving DecidableEq, Repr

def Expr.eval (s : Store) : Expr → Int
  | .const v => v
  | .var x => s x
  | .bin op a b => op.eval (a.eval s) (b.eval s)
  | .not a => if a.eval s = 0 then 1 else 0

inductive Cmd
  /-- `pass` -/
  | skip
  /-- `x = e` -/
  | assign (x : Var) (e : Expr)
  /-- `x = o.f` -/
  | load (x : Var) (o : Expr) (f : String)
  /-- `o.f = e` -/
  | store (o : Expr) (f : String) (e : Expr)
  | seq (c₁ c₂ : Cmd)
  | ite (e : Expr) (c₁ c₂ : Cmd)
  | while (e : Expr) (c : Cmd)
  /-- `with L: c` -/
  | atomic (c : Cmd)
  /-- Run-time only: inside `with L:`, `c` remains. -/
  | inAtomic (c : Cmd)
deriving DecidableEq, Repr

/-- Does the thread currently hold the global lock? -/
def Cmd.locked : Cmd → Bool
  | .inAtomic _ => true
  | .seq c _ => c.locked
  | _ => false

/-- The heap location the next step accesses, if any. -/
def Cmd.acc (s : Store) : Cmd → Option Loc
  | .load _ o f => some ⟨o.eval s, f⟩
  | .store o f _ => some ⟨o.eval s, f⟩
  | .seq c _ => c.acc s
  | .inAtomic c => c.acc s
  | _ => none

/-- Local variables the command may assign. -/
def Cmd.mods : Cmd → List Var
  | .assign x _ => [x]
  | .load x _ _ => [x]
  | .seq c₁ c₂ => c₁.mods ++ c₂.mods
  | .ite _ c₁ c₂ => c₁.mods ++ c₂.mods
  | .while _ c => c.mods
  | .atomic c => c.mods
  | .inAtomic c => c.mods
  | _ => []

/-! ## Thread-local small-step semantics -/

/-- One step of one thread: `Step c s H c' s' H'`. -/
inductive Step : Cmd → Store → Heap → Cmd → Store → Heap → Prop
  | assign {x e s H} : Step (.assign x e) s H .skip (s.set x (e.eval s)) H
  | load {x o f s H v} : H ⟨o.eval s, f⟩ = some v →
      Step (.load x o f) s H .skip (s.set x v) H
  | store {o f e s H} : H ⟨o.eval s, f⟩ ≠ none →
      Step (.store o f e) s H .skip s (H.upd ⟨o.eval s, f⟩ (e.eval s))
  | seqSkip {c s H} : Step (.seq .skip c) s H c s H
  | seq {c₁ c₁' c₂ s s' H H'} : Step c₁ s H c₁' s' H' → Step (.seq c₁ c₂) s H (.seq c₁' c₂) s' H'
  | iteT {e c₁ c₂ s H} : e.eval s ≠ 0 → Step (.ite e c₁ c₂) s H c₁ s H
  | iteF {e c₁ c₂ s H} : e.eval s = 0 → Step (.ite e c₁ c₂) s H c₂ s H
  | while {e c s H} : Step (.while e c) s H (.ite e (.seq c (.while e c)) .skip) s H
  | atomic {c s H} : Step (.atomic c) s H (.inAtomic c) s H
  | inAtomic {c c' s s' H H'} : Step c s H c' s' H' → Step (.inAtomic c) s H (.inAtomic c') s' H'
  | inAtomicSkip {s H} : Step (.inAtomic .skip) s H .skip s H

theorem Step.no_skip {s H c' s' H'} : ¬ Step .skip s H c' s' H' := by
  intro h; cases h

/-- No allocation or deallocation: a step keeps the heap's domain. -/
theorem Step.dom {c s H c' s' H'} (h : Step c s H c' s' H') (l : Loc) :
    (H' l = none ↔ H l = none) := by
  induction h with
  | store hne =>
    rename_i o f e s H
    by_cases e' : l = ⟨o.eval s, f⟩
    · subst e'; simp [hne]
    · simp [upd_other _ _ e']
  | seq _ ih => exact ih
  | inAtomic _ ih => exact ih
  | _ => exact Iff.rfl

/-- A step changes only variables in `mods`, and `mods` only shrinks. -/
theorem Step.mods {c s H c' s' H'} (h : Step c s H c' s' H') :
    (∀ x, x ∉ c.mods → s' x = s x) ∧ (∀ x, x ∈ c'.mods → x ∈ c.mods) := by
  induction h with
  | @assign x _ _ _ =>
    refine ⟨fun y hy => ?_, fun _ h => by simp [Cmd.mods] at h⟩
    have : y ≠ x := by simpa [Cmd.mods] using hy
    simp [this]
  | @load x _ _ _ _ _ _ =>
    refine ⟨fun y hy => ?_, fun _ h => by simp [Cmd.mods] at h⟩
    have : y ≠ x := by simpa [Cmd.mods] using hy
    simp [this]
  | seq _ ih =>
    refine ⟨fun y hy => ih.1 y (by simp_all [Cmd.mods]), fun y hy => ?_⟩
    simp only [Cmd.mods, List.mem_append] at hy ⊢
    exact hy.imp_left (ih.2 y)
  | inAtomic _ ih => exact ⟨fun y hy => ih.1 y hy, fun y hy => ih.2 y hy⟩
  | seqSkip => exact ⟨fun _ _ => rfl, fun y hy => by simp [Cmd.mods, hy]⟩
  | iteT => exact ⟨fun _ _ => rfl, fun y hy => by simp [Cmd.mods, hy]⟩
  | iteF => exact ⟨fun _ _ => rfl, fun y hy => by simp [Cmd.mods, hy]⟩
  | «while» => exact ⟨fun _ _ => rfl, fun y hy => by simp_all [Cmd.mods]⟩
  | atomic => exact ⟨fun _ _ => rfl, fun y hy => by simpa [Cmd.mods] using hy⟩
  | inAtomicSkip => exact ⟨fun _ _ => rfl, fun y hy => by simp [Cmd.mods] at hy⟩
  | store => exact ⟨fun _ _ => rfl, fun y hy => by simp [Cmd.mods] at hy⟩

/-! ## Thread pool -/

structure Thread where
  cmd : Cmd
  store : Store

abbrev Pool := List Thread

/-- One step of the pool: some thread `i` steps. It may enter `with L:` only
if no other thread is inside one. -/
inductive MStep : Pool → Heap → Pool → Heap → Prop
  | step {ts : Pool} {H : Heap} (i : Nat) (hi : i < ts.length) {c' : Cmd} {s' : Store} {H' : Heap} :
      Step ts[i].cmd ts[i].store H c' s' H' →
      (ts[i].cmd.locked = false → c'.locked = true →
        ∀ j (hj : j < ts.length), j ≠ i → ts[j].cmd.locked = false) →
      MStep ts H (ts.set i ⟨c', s'⟩) H'

/-- `k` pool steps. -/
inductive MSteps : Nat → Pool → Heap → Pool → Heap → Prop
  | refl {ts H} : MSteps 0 ts H ts H
  | step {k ts H ts' H' ts'' H''} :
      MStep ts H ts' H' → MSteps k ts' H' ts'' H'' → MSteps (k + 1) ts H ts'' H''

/-- Some thread's next step accesses an attribute that does not exist. -/
def Faults (ts : Pool) (H : Heap) : Prop :=
  ∃ i, ∃ (hi : i < ts.length), ∃ l, ts[i].cmd.acc ts[i].store = some l ∧ H l = none

/-- Two different threads are about to access the same attribute. (Stronger
than a data race: even two reads count.) -/
def Race (ts : Pool) : Prop :=
  ∃ i j, ∃ (hi : i < ts.length) (hj : j < ts.length), i ≠ j ∧
    ∃ l, ts[i].cmd.acc ts[i].store = some l ∧ ts[j].cmd.acc ts[j].store = some l

end PyL
