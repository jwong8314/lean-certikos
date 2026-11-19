import CertiKOS.PyL
import CertiKOS.ClightL

/-!
# One AST, two targets: ClightL → PyL, proved equivalent on the concurrent machine

`tr` translates a ClightL statement into PyL. The C side is the multicore
machine that `Bench/Sim.lean` runs: N CPUs, each executing a ClightL
configuration, sharing the abstract state (the log) of the layer underneath;
any CPU may take the next step. The Python side is a PyL thread pool. A
primitive call `x = p(args)` becomes a `with L:` block containing a Python
implementation `impl p` of the primitive.

* **Values.** A C value `v : BitVec 32` is the Python int `v.toNat`
  (`enc`). `+`/`-` become `(a + b) % 2**32` / `(a - b) % 2**32`; this relies
  on Python's `%` being floor modulo, so a negative difference wraps exactly
  like unsigned C subtraction. `==`, `!=`, unsigned `<` map to themselves.
* **Control.** ClightL runs with CompCert-style continuations; PyL with
  nested `;`. `embed` plugs the translated statement into the translated
  continuation. The C step `s₁;s₂ ↦ s₁ · [s₂]` has no Python counterpart (the
  term is literally the same); a C `while` step takes two Python steps.
* **Primitives.** The user supplies `impl` and a relation `R : Abs → Heap`
  between the C layer's abstract state and the Python heap, and proves
  `PrimOK`: run alone, the block does what the primitive does, on related
  states. Nothing else about the primitive is assumed.

**Theorems.**

* `py_to_c`: every execution of the Python pool, under any interleaving,
  including executions where other threads run while one thread is in the
  middle of a `with L:` block, is matched by an execution of the C machine,
  related by `Rel`.
* `c_to_py`: every execution of the C machine is matched by an execution of
  the Python pool.
* `py_done`: when every Python thread has finished, every C CPU has finished,
  with agreeing locals and related shared state.

The concrete instance for the ticket lock is in `TicketPy.lean`.
-/

namespace ClightToPy

open ClightL (Val Ident Locals Stmt Cont Config Prims)
open PyL (Var Store Heap Cmd Thread Pool MStep MSteps)

/-! ## Values and expressions -/

def M : Int := 4294967296

theorem M_eq : M = 2 ^ 32 := rfl

/-- The Python int representing a 32-bit C value. -/
def enc (v : Val) : Int := v.toNat

@[simp] theorem enc_zero : enc 0 = 0 := rfl
@[simp] theorem enc_one : enc 1 = 1 := rfl

theorem enc_inj {a b : Val} : enc a = enc b ↔ a = b := by
  simp only [enc, Int.ofNat_inj, BitVec.toNat_inj]

theorem enc_eq_zero {a : Val} : enc a = 0 ↔ a = 0 := enc_inj (b := 0)

theorem enc_ofNat (n : Nat) : enc (BitVec.ofNat 32 n) = (n : Int) % M := by
  simp only [enc, BitVec.toNat_ofNat, M]; omega

def trOp : ClightL.BinOp → PyL.Expr → PyL.Expr → PyL.Expr
  | .add, a, b => .bin .fmod (.bin .add a b) (.const M)
  | .sub, a, b => .bin .fmod (.bin .sub a b) (.const M)
  | .mul, a, b => .bin .fmod (.bin .mul a b) (.const M)
  | .div, a, b => .bin .fdiv a b
  | .mod, a, b => .bin .fmod a b
  | .eq, a, b => .bin .eq a b
  | .ne, a, b => .bin .ne a b
  | .ltu, a, b => .bin .lt a b

def trE : ClightL.Expr → PyL.Expr
  | .const v => .const (enc v)
  | .var x => .var x
  | .bin op a b => trOp op (trE a) (trE b)

/-- `Rsv` names the Python variables reserved for primitive implementations;
C programs may not use them. Outside `Rsv`, the Python frame equals the C
locals. -/
def Agree (Rsv : Var → Prop) (σ : Locals) (s : Store) : Prop :=
  ∀ x, ¬ Rsv x → s x = enc (σ x)

def EWF (Rsv : Var → Prop) : ClightL.Expr → Prop
  | .const _ => True
  | .var x => ¬ Rsv x
  | .bin _ a b => EWF Rsv a ∧ EWF Rsv b

theorem trOp_eval (op : ClightL.BinOp) (a b : Val) (ea eb : PyL.Expr) (s : Store)
    (ha : ea.eval s = enc a) (hb : eb.eval s = enc b) :
    (trOp op ea eb).eval s = enc (op.eval a b) := by
  have la := a.isLt; have lb := b.isLt
  cases op with
  | add =>
    simp only [trOp, PyL.Expr.eval, PyL.BinOp.eval, ha, hb, ClightL.BinOp.eval]
    rw [Int.fmod_eq_emod_of_nonneg _ (by decide)]
    simp only [enc, BitVec.toNat_add, M]; omega
  | sub =>
    simp only [trOp, PyL.Expr.eval, PyL.BinOp.eval, ha, hb, ClightL.BinOp.eval]
    rw [Int.fmod_eq_emod_of_nonneg _ (by decide)]
    simp only [enc, BitVec.toNat_sub, M]; omega
  | mul =>
    simp only [trOp, PyL.Expr.eval, PyL.BinOp.eval, ha, hb, ClightL.BinOp.eval]
    rw [Int.fmod_eq_emod_of_nonneg _ (by decide)]
    have h : (a * b).toNat = a.toNat * b.toNat % 2 ^ 32 := BitVec.toNat_mul a b
    unfold enc; rw [h, Int.natCast_emod, Int.natCast_mul]; rfl
  | div =>
    simp only [trOp, PyL.Expr.eval, PyL.BinOp.eval, ha, hb, ClightL.BinOp.eval]
    have h : (a / b).toNat = a.toNat / b.toNat := BitVec.toNat_udiv
    unfold enc; rw [h]
    generalize a.toNat = m
    generalize b.toNat = n
    cases m with
    | zero => simp [Int.fdiv]
    | succ m => rfl
  | mod =>
    simp only [trOp, PyL.Expr.eval, PyL.BinOp.eval, ha, hb, ClightL.BinOp.eval]
    have h : (a % b).toNat = a.toNat % b.toNat := BitVec.toNat_umod
    unfold enc; rw [h]
    generalize a.toNat = m
    generalize b.toNat = n
    cases m with
    | zero => simp [Int.fmod]
    | succ m => rfl
  | eq =>
    simp only [trOp, PyL.Expr.eval, PyL.BinOp.eval, ha, hb, ClightL.BinOp.eval, enc_inj]
    split <;> rfl
  | ne =>
    simp only [trOp, PyL.Expr.eval, PyL.BinOp.eval, ha, hb, ClightL.BinOp.eval, enc_inj]
    split <;> rfl
  | ltu =>
    simp only [trOp, PyL.Expr.eval, PyL.BinOp.eval, ha, hb, ClightL.BinOp.eval]
    by_cases h : a.ult b = true
    · have : a.toNat < b.toNat := BitVec.lt_def.1 (BitVec.ult_iff_lt.1 h)
      simp [h, enc, this]
    · have : ¬ a.toNat < b.toNat := fun h' => h (BitVec.ult_iff_lt.2 (BitVec.lt_def.2 h'))
      simp [h, enc, this]

theorem trE_eval {Rsv : Var → Prop} {σ : Locals} {s : Store} (hA : Agree Rsv σ s) :
    ∀ e, EWF Rsv e → (trE e).eval s = enc (e.eval σ)
  | .const _, _ => rfl
  | .var x, h => hA x h
  | .bin op a b, ⟨ha, hb⟩ =>
    trOp_eval op _ _ _ _ s (trE_eval hA a ha) (trE_eval hA b hb)

theorem trE_eval_zero {Rsv : Var → Prop} {σ : Locals} {s : Store} (hA : Agree Rsv σ s)
    {e : ClightL.Expr} (he : EWF Rsv e) : (trE e).eval s = 0 ↔ e.eval σ = 0 := by
  rw [trE_eval hA e he]; exact enc_eq_zero

theorem agree_set {Rsv : Var → Prop} {σ : Locals} {s : Store} (hA : Agree Rsv σ s)
    (x : Ident) (v : Val) : Agree Rsv (σ.set x v) (s.set x (enc v)) := by
  intro y hy
  by_cases e : y = x
  · subst e; simp
  · simp [e, hA y hy]

/-! ## Statements -/

section Translate
variable {Pn : Type} (impl : Pn → List PyL.Expr → Var → Cmd)

/-- The translation. A primitive call becomes `with L: impl p args x`. -/
def tr : Stmt Pn → Cmd
  | .skip => .skip
  | .assign x e => .assign x (trE e)
  | .seq a b => .seq (tr a) (tr b)
  | .ite e a b => .ite (trE e) (tr a) (tr b)
  | .while e b => .while (trE e) (tr b)
  | .call x p args => .atomic (impl p (args.map trE) x)

/-- Translate a continuation as an evaluation context (nested `;`). -/
def plug : Cont Pn → Cmd → Cmd
  | .stop, c => c
  | .seq s k, c => plug k (.seq c (tr impl s))
  | .loop e b k, c => plug k (.seq c (tr impl (.while e b)))

end Translate

/-- One CPU of the C machine: a configuration without the shared state. -/
structure CThread (Pn : Type) where
  stmt : Stmt Pn
  cont : Cont Pn
  locals : Locals

def CThread.cfg {Pn Abs : Type} (t : CThread Pn) (a : Abs) : Config Pn Abs :=
  ⟨t.stmt, t.cont, t.locals, a⟩

def thr {Pn Abs : Type} (c : Config Pn Abs) : CThread Pn := ⟨c.stmt, c.cont, c.locals⟩

@[simp] theorem thr_cfg {Pn Abs : Type} (t : CThread Pn) (a : Abs) : thr (t.cfg a) = t := rfl

/-- The Python command a C thread corresponds to. -/
def embed {Pn : Type} (impl : Pn → List PyL.Expr → Var → Cmd) (t : CThread Pn) : Cmd :=
  plug impl t.cont (tr impl t.stmt)

section WF
variable {Pn : Type} (Rsv : Var → Prop) (arity : Pn → Nat)

def SWF : Stmt Pn → Prop
  | .skip => True
  | .assign x e => ¬ Rsv x ∧ EWF Rsv e
  | .seq a b => SWF a ∧ SWF b
  | .ite e a b => EWF Rsv e ∧ SWF a ∧ SWF b
  | .while e b => EWF Rsv e ∧ SWF b
  | .call x p args => ¬ Rsv x ∧ args.length = arity p ∧ ∀ a ∈ args, EWF Rsv a

def KWF : Cont Pn → Prop
  | .stop => True
  | .seq s k => SWF Rsv arity s ∧ KWF k
  | .loop e b k => EWF Rsv e ∧ SWF Rsv arity b ∧ KWF k

/-- Well-formed configuration: uses no reserved variable, calls have the
right arity. -/
def CWF (t : CThread Pn) : Prop := SWF Rsv arity t.stmt ∧ KWF Rsv arity t.cont

end WF

/-! ## Sequential PyL runs -/

open PyL (Step)

inductive PSteps : Cmd → Store → Heap → Cmd → Store → Heap → Prop
  | refl {c s H} : PSteps c s H c s H
  | step {c s H c₁ s₁ H₁ c₂ s₂ H₂} :
      Step c s H c₁ s₁ H₁ → PSteps c₁ s₁ H₁ c₂ s₂ H₂ → PSteps c s H c₂ s₂ H₂

theorem PSteps.single {c s H c' s' H'} (h : Step c s H c' s' H') : PSteps c s H c' s' H' :=
  .step h .refl

theorem PSteps.trans {c s H c₁ s₁ H₁ c₂ s₂ H₂} (h₁ : PSteps c s H c₁ s₁ H₁)
    (h₂ : PSteps c₁ s₁ H₁ c₂ s₂ H₂) : PSteps c s H c₂ s₂ H₂ := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem PSteps.snoc {c s H c₁ s₁ H₁ c₂ s₂ H₂} (h₁ : PSteps c s H c₁ s₁ H₁)
    (h₂ : Step c₁ s₁ H₁ c₂ s₂ H₂) : PSteps c s H c₂ s₂ H₂ := h₁.trans (.single h₂)

/-- Sequential PyL is deterministic. -/
theorem Step.det {c s H c₁ s₁ H₁ c₂ s₂ H₂} (h₁ : Step c s H c₁ s₁ H₁)
    (h₂ : Step c s H c₂ s₂ H₂) : c₁ = c₂ ∧ s₁ = s₂ ∧ H₁ = H₂ := by
  induction h₁ generalizing c₂ s₂ H₂ with
  | load hv => cases h₂ with | load hv' => rw [hv] at hv'; cases hv'; exact ⟨rfl, rfl, rfl⟩
  | seqSkip =>
    cases h₂ with
    | seqSkip => exact ⟨rfl, rfl, rfl⟩
    | seq h => exact absurd h Step.no_skip
  | seq h ih =>
    cases h₂ with
    | seqSkip => exact absurd h Step.no_skip
    | seq h' => obtain ⟨rfl, rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl, rfl⟩
  | iteT he => cases h₂ with
    | iteT => exact ⟨rfl, rfl, rfl⟩
    | iteF he' => exact absurd he' he
  | iteF he => cases h₂ with
    | iteT he' => exact absurd he he'
    | iteF => exact ⟨rfl, rfl, rfl⟩
  | inAtomic h ih =>
    cases h₂ with
    | inAtomic h' => obtain ⟨rfl, rfl, rfl⟩ := ih h'; exact ⟨rfl, rfl, rfl⟩
    | inAtomicSkip => exact absurd h Step.no_skip
  | inAtomicSkip =>
    cases h₂ with
    | inAtomic h => exact absurd h Step.no_skip
    | inAtomicSkip => exact ⟨rfl, rfl, rfl⟩
  | assign => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | store => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | «while» => cases h₂; exact ⟨rfl, rfl, rfl⟩
  | atomic => cases h₂; exact ⟨rfl, rfl, rfl⟩

/-- A sequential run that reaches `skip` has a unique final state. -/
theorem PSteps.skip_unique' {c s H c' s₁ H₁} (h₁ : PSteps c s H c' s₁ H₁) :
    c' = .skip → ∀ {s₂ H₂}, PSteps c s H .skip s₂ H₂ → s₁ = s₂ ∧ H₁ = H₂ := by
  induction h₁ with
  | refl =>
    intro he _ _ h₂; subst he
    cases h₂ with
    | refl => exact ⟨rfl, rfl⟩
    | step h _ => exact absurd h Step.no_skip
  | step h _ ih =>
    intro he _ _ h₂; subst he
    cases h₂ with
    | refl => exact absurd h Step.no_skip
    | step h' r =>
      obtain ⟨rfl, rfl, rfl⟩ := Step.det h h'
      exact ih rfl r

/-- A sequential run that reaches `skip` has a unique final state. -/
theorem PSteps.skip_unique {c s H s₁ H₁ s₂ H₂} (h₁ : PSteps c s H .skip s₁ H₁)
    (h₂ : PSteps c s H .skip s₂ H₂) : s₁ = s₂ ∧ H₁ = H₂ := h₁.skip_unique' rfl h₂

theorem PSteps.inAtomic {c s H c' s' H'} (h : PSteps c s H c' s' H') :
    PSteps (.inAtomic c) s H (.inAtomic c') s' H' := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (.inAtomic h) ih

/-! ## Evaluation contexts -/

section Plug
variable {Pn : Type} {impl : Pn → List PyL.Expr → Var → Cmd}

theorem plug_step (k : Cont Pn) {c s H c' s' H'} (h : Step c s H c' s' H') :
    Step (plug impl k c) s H (plug impl k c') s' H' := by
  induction k generalizing c c' with
  | stop => exact h
  | seq _ _ ih => exact ih (.seq h)
  | loop _ _ _ ih => exact ih (.seq h)

theorem plug_locked (k : Cont Pn) (c : Cmd) : (plug impl k c).locked = c.locked := by
  induction k generalizing c with
  | stop => rfl
  | seq _ _ ih => rw [plug, ih]; rfl
  | loop _ _ _ ih => rw [plug, ih]; rfl

/-- Inversion: a non-`skip` command in context steps only by itself. -/
theorem plug_inv (k : Cont Pn) {c s H X s' H'} (hc : c ≠ .skip)
    (h : Step (plug impl k c) s H X s' H') : ∃ c', Step c s H c' s' H' ∧ X = plug impl k c' := by
  induction k generalizing c X with
  | stop => exact ⟨X, h, rfl⟩
  | seq t k ih =>
    obtain ⟨c'', hs, rfl⟩ := ih (by simp) h
    cases hs with
    | seqSkip => exact absurd rfl hc
    | seq h' => exact ⟨_, h', rfl⟩
  | loop e b k ih =>
    obtain ⟨c'', hs, rfl⟩ := ih (by simp) h
    cases hs with
    | seqSkip => exact absurd rfl hc
    | seq h' => exact ⟨_, h', rfl⟩

theorem tr_locked (s : Stmt Pn) : (tr impl s).locked = false := by
  induction s with
  | seq a b iha _ => simpa [tr, Cmd.locked] using iha
  | _ => rfl

theorem embed_locked (c : CThread Pn) : (embed impl c).locked = false := by
  rw [embed, plug_locked, tr_locked]

theorem plug_eq_skip {k : Cont Pn} {c : Cmd} (h : plug impl k c = .skip) : k = .stop ∧ c = .skip := by
  induction k generalizing c with
  | stop => exact ⟨rfl, h⟩
  | seq _ _ ih => exact absurd (ih h).2 (by simp)
  | loop _ _ _ ih => exact absurd (ih h).2 (by simp)

theorem tr_eq_skip {s : Stmt Pn} (h : tr impl s = .skip) : s = .skip := by
  cases s <;> simp_all [tr]

end Plug

theorem PSteps.plug {Pn : Type} {impl : Pn → List PyL.Expr → Var → Cmd} (k : Cont Pn)
    {c s H c' s' H'} (h : PSteps c s H c' s' H') :
    PSteps (plug impl k c) s H (plug impl k c') s' H' := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (plug_step k h) ih

theorem MSteps_trans {k₁ k₂ : Nat} {ts H ts₁ H₁ ts₂ H₂} (h₁ : MSteps k₁ ts H ts₁ H₁)
    (h₂ : MSteps k₂ ts₁ H₁ ts₂ H₂) : MSteps (k₁ + k₂) ts H ts₂ H₂ := by
  induction h₁ with
  | refl => simpa using h₂
  | step h _ ih => rw [Nat.add_right_comm]; exact .step h (ih h₂)

/-! ## The two machines -/

section Machine
variable {Pn Abs : Type} (impl : Pn → List PyL.Expr → Var → Cmd)
  (Rsv : Var → Prop) (arity : Pn → Nat) (P : Nat → Prims Pn Abs) (R : Abs → Heap → Prop)

/-- The C multicore machine: CPU `i` runs its ClightL configuration against the
shared abstract state `a`, using its primitive table `P i`. Any CPU may move.
This is the machine `Bench/Sim.lean` executes. -/
inductive CStep : List (CThread Pn) → Abs → List (CThread Pn) → Abs → Prop
  | step {cs : List (CThread Pn)} {a : Abs} {c' : Config Pn Abs} (i : Nat) (hi : i < cs.length) :
      ClightL.step (P i) (cs[i].cfg a) = some c' → CStep cs a (cs.set i (thr c')) c'.abs

inductive CSteps : List (CThread Pn) → Abs → List (CThread Pn) → Abs → Prop
  | refl {cs a} : CSteps cs a cs a
  | step {cs a cs' a' cs'' a''} : CStep P cs a cs' a' → CSteps cs' a' cs'' a'' → CSteps cs a cs'' a''

/-- What the primitive implementations must satisfy. `ok`: run alone on a
related heap, `impl p` reaches the end of the block with the result in `x`, the
rest of the frame unchanged (outside reserved variables), and a heap related to
the new abstract state. `stuck`: if the C primitive is stuck, the block does not
complete. -/
structure PrimOK : Prop where
  ok : ∀ (i : Nat) (p : Pn) (args : List ClightL.Expr) (x : Var) (σ : Locals) (s : Store)
    (a : Abs) (H : Heap) (v : Val) (a' : Abs), Agree Rsv σ s → ¬ Rsv x → (∀ e ∈ args, EWF Rsv e) → R a H →
    P i p (args.map (·.eval σ)) a = some (v, a') →
    ∃ s' H', PSteps (impl p (args.map trE) x) s H .skip s' H' ∧ Agree Rsv (σ.set x v) s' ∧ R a' H'
  stuck : ∀ (i : Nat) (p : Pn) (args : List ClightL.Expr) (x : Var) (σ : Locals) (s : Store)
    (a : Abs) (H : Heap), Agree Rsv σ s → ¬ Rsv x → (∀ e ∈ args, EWF Rsv e) →
    args.length = arity p → R a H → P i p (args.map (·.eval σ)) a = none →
    ∀ s' H', ¬ PSteps (impl p (args.map trE) x) s H .skip s' H'

/-- Thread `i` of the Python pool sits at, or one Python step into, the C
statement of CPU `i`, outside any `with L:` block. -/
inductive Out : CThread Pn → Thread → Prop
  | here {t : CThread Pn} {s : Store} : Agree Rsv t.locals s → Out t ⟨embed impl t, s⟩
  | wmid {t : CThread Pn} {e b s} : t.stmt = .while e b → Agree Rsv t.locals s →
      Out t ⟨plug impl t.cont (.ite (trE e) (.seq (tr impl b) (tr impl (.while e b))) .skip), s⟩

/-- Thread `i` is inside the `with L:` block of the call CPU `i` is about to
make. It started from a frame agreeing with the C locals and a heap related to
the current abstract state, and has run part of the block since. -/
def InBlk (t : CThread Pn) (a : Abs) (th : Thread) (H : Heap) : Prop :=
  ∃ x p args B s₀ H₀, t.stmt = .call x p args ∧ th.cmd = plug impl t.cont (.inAtomic B) ∧
    Agree Rsv t.locals s₀ ∧ R a H₀ ∧ PSteps (impl p (args.map trE) x) s₀ H₀ B th.store H

/-- The simulation relation between the C machine and the Python pool. -/
structure Rel (cs : List (CThread Pn)) (a : Abs) (ts : Pool) (H : Heap) : Prop where
  len : cs.length = ts.length
  wf : ∀ i (hi : i < cs.length), CWF Rsv arity cs[i]
  thr : ∀ i (hi : i < cs.length) (ht : i < ts.length),
    Out impl Rsv cs[i] ts[i] ∨ InBlk impl Rsv R cs[i] a ts[i] H
  heap : (∀ i (ht : i < ts.length), ts[i].cmd.locked = false) → R a H
  one : ∀ i j (hi : i < ts.length) (hj : j < ts.length),
    ts[i].cmd.locked = true → ts[j].cmd.locked = true → i = j

/-- Lock-step relation: every Python thread is exactly at its C statement. -/
structure Sync (cs : List (CThread Pn)) (a : Abs) (ts : Pool) (H : Heap) : Prop where
  len : cs.length = ts.length
  wf : ∀ i (hi : i < cs.length), CWF Rsv arity cs[i]
  thr : ∀ i (hi : i < cs.length) (ht : i < ts.length),
    ts[i].cmd = embed impl cs[i] ∧ Agree Rsv cs[i].locals ts[i].store
  heap : R a H

variable {impl Rsv arity P R}

theorem CSteps.trans {cs a cs' a' cs'' a''} (h₁ : CSteps P cs a cs' a')
    (h₂ : CSteps P cs' a' cs'' a'') : CSteps P cs a cs'' a'' := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem star_csteps (i : Nat) {c c' : Config Pn Abs} (h : ClightL.Star (P i) c c') :
    ∀ (cs : List (CThread Pn)) (hi : i < cs.length), c = cs[i].cfg c.abs →
      CSteps P cs c.abs (cs.set i (thr c')) c'.abs := by
  induction h with
  | refl c =>
    intro cs hi he
    have : thr c = cs[i] := by rw [he]; rfl
    rw [this, List.set_getElem_self]; exact .refl
  | @step c₁ c₂ c₃ hs _ ih =>
    intro cs hi he
    have h1 : CStep P cs c₁.abs (cs.set i (thr c₂)) c₂.abs := .step i hi (by rw [← he]; exact hs)
    have h2 := ih (cs.set i (thr c₂)) (by simpa using hi)
      (by simp only [List.getElem_set_self]; rfl)
    rw [List.set_set] at h2
    exact .step h1 h2

theorem out_locked {t : CThread Pn} {th : Thread} (h : Out impl Rsv t th) : th.cmd.locked = false := by
  cases h with
  | here => exact embed_locked _
  | wmid => simp only [plug_locked]; rfl

theorem inBlk_locked {t : CThread Pn} {a : Abs} {th : Thread} {H : Heap}
    (h : InBlk impl Rsv R t a th H) : th.cmd.locked = true := by
  obtain ⟨_, _, _, _, _, _, _, hc, _⟩ := h
  rw [hc, plug_locked]; rfl

/-! ### C steps, unfolded -/

theorem cstep_ite (Q : Prims Pn Abs) (e : ClightL.Expr) (b₁ b₂ : Stmt Pn) (k : Cont Pn) (σ : Locals)
    (a : Abs) : ClightL.step Q (CThread.cfg ⟨.ite e b₁ b₂, k, σ⟩ a) =
      some (CThread.cfg ⟨if e.eval σ = 0 then b₂ else b₁, k, σ⟩ a) := rfl

theorem cstep_while (Q : Prims Pn Abs) (e : ClightL.Expr) (b : Stmt Pn) (k : Cont Pn) (σ : Locals)
    (a : Abs) : ClightL.step Q (CThread.cfg ⟨.while e b, k, σ⟩ a) =
      if e.eval σ = 0 then some (CThread.cfg ⟨.skip, k, σ⟩ a)
      else some (CThread.cfg ⟨b, .loop e b k, σ⟩ a) := rfl

/-! ### Well-formedness is preserved by C steps -/

theorem step_wf {i : Nat} {c c' : Config Pn Abs} (hw : CWF Rsv arity (thr c))
    (h : ClightL.step (P i) c = some c') : CWF Rsv arity (thr c') := by
  obtain ⟨stmt, k, σ, a⟩ := c
  obtain ⟨hs, hk⟩ := hw
  cases stmt with
  | skip =>
    cases k with
    | stop => simp [ClightL.step] at h
    | seq s k => simp [ClightL.step] at h; subst h; exact hk
    | loop e b k => simp [ClightL.step] at h; subst h; exact ⟨⟨hk.1, hk.2.1⟩, hk.2.2⟩
  | assign x e => simp [ClightL.step] at h; subst h; exact ⟨trivial, hk⟩
  | seq a b => simp [ClightL.step] at h; subst h; exact ⟨hs.1, hs.2, hk⟩
  | ite e a b =>
    simp [ClightL.step] at h; subst h
    refine ⟨?_, hk⟩; dsimp only [thr]; split
    · exact hs.2.2
    · exact hs.2.1
  | «while» e b =>
    simp only [ClightL.step] at h
    split at h <;> (simp at h; subst h)
    · exact ⟨trivial, hk⟩
    · exact ⟨hs.2, hs.1, hs.2, hk⟩
  | call x p args =>
    simp only [ClightL.step] at h
    split at h
    · simp at h; subst h; exact ⟨trivial, hk⟩
    · simp at h

theorem star_wf {i : Nat} {c c' : Config Pn Abs} (h : ClightL.Star (P i) c c') :
    CWF Rsv arity (thr c) → CWF Rsv arity (thr c') := by
  induction h with
  | refl => exact id
  | step hs _ ih => exact fun hw => ih (step_wf hw hs)

/-! ### Normalisation: C `;`-steps have no Python counterpart -/

theorem normalize (i : Nat) (a : Abs) :
    ∀ (s : Stmt Pn) (k : Cont Pn) (σ : Locals), ∃ t' : CThread Pn,
      ClightL.Star (P i) (CThread.cfg ⟨s, k, σ⟩ a) (t'.cfg a) ∧
      embed impl t' = embed impl ⟨s, k, σ⟩ ∧ t'.locals = σ ∧ (∀ s₁ s₂, t'.stmt ≠ .seq s₁ s₂)
  | .seq s₁ s₂, k, σ => by
    obtain ⟨t', hs, he, hl, hn⟩ := normalize i a s₁ (.seq s₂ k) σ
    exact ⟨t', .step rfl hs, he, hl, hn⟩
  | .skip, k, σ => ⟨_, .refl _, rfl, rfl, by intro _ _ h; cases h⟩
  | .assign x e, k, σ => ⟨_, .refl _, rfl, rfl, by intro _ _ h; cases h⟩
  | .ite e a b, k, σ => ⟨_, .refl _, rfl, rfl, by intro _ _ h; cases h⟩
  | .while e b, k, σ => ⟨_, .refl _, rfl, rfl, by intro _ _ h; cases h⟩
  | .call x p args, k, σ => ⟨_, .refl _, rfl, rfl, by intro _ _ h; cases h⟩


/-! ### One Python step of one thread -/

/-- A Python step of a thread outside any block leaves the heap alone, and
corresponds to zero or more C steps (zero: `;`-steps and the first half of a
`while`). Entering `with L:` starts a block. -/
theorem thread_step_out (i : Nat) {t : CThread Pn} {th : Thread} {a : Abs} {H : Heap}
    {c' : Cmd} {s' : Store} {H' : Heap}
    (hwf : CWF Rsv arity t) (hO : Out impl Rsv t th) (hs : Step th.cmd th.store H c' s' H') :
    H' = H ∧ ∃ t' : CThread Pn, ClightL.Star (P i) (t.cfg a) (t'.cfg a) ∧
      (Out impl Rsv t' ⟨c', s'⟩ ∨
        (c'.locked = true ∧ (R a H → InBlk impl Rsv R t' a ⟨c', s'⟩ H'))) := by
  cases hO with
  | @here s hA =>
    obtain ⟨⟨stmt, k, σ⟩, hst, he, hl, hn⟩ :=
      normalize (P := P) (impl := impl) i a t.stmt t.cont t.locals
    have hst : ClightL.Star (P i) (t.cfg a) (CThread.cfg ⟨stmt, k, σ⟩ a) := hst
    have hw : CWF Rsv arity ⟨stmt, k, σ⟩ := by simpa using star_wf hst (by simpa using hwf)
    simp only at hl; subst hl
    have hs : Step (embed impl ⟨stmt, k, t.locals⟩) s H c' s' H' := by rw [he]; exact hs
    cases stmt with
    | skip =>
      cases k with
      | stop => exact absurd hs Step.no_skip
      | seq s₂ k =>
        obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .seqSkip)
        exact ⟨rfl, ⟨s₂, k, t.locals⟩, hst.trans (.single rfl), .inl (.here hA)⟩
      | loop e b k =>
        obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .seqSkip)
        exact ⟨rfl, ⟨.while e b, k, t.locals⟩, hst.trans (.single rfl), .inl (.here hA)⟩
    | assign x e =>
      obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .assign)
      refine ⟨rfl, ⟨.skip, k, t.locals.set x (e.eval t.locals)⟩, hst.trans (.single rfl), .inl ?_⟩
      have := Out.here (impl := impl) (t := ⟨.skip, k, t.locals.set x (e.eval t.locals)⟩)
        (agree_set hA x (e.eval t.locals))
      rwa [← trE_eval hA e hw.1.2] at this
    | seq _ _ => exact absurd rfl (hn _ _)
    | ite e b₁ b₂ =>
      by_cases hz : e.eval t.locals = 0
      · obtain ⟨rfl, rfl, rfl⟩ :=
          Step.det hs (plug_step (impl := impl) k (.iteF ((trE_eval_zero hA hw.1.1).2 hz)))
        exact ⟨rfl, ⟨b₂, k, t.locals⟩,
          hst.trans (.single (by rw [cstep_ite, ite_eq_left hz])), .inl (.here hA)⟩
      · obtain ⟨rfl, rfl, rfl⟩ :=
          Step.det hs (plug_step (impl := impl) k (.iteT (mt (trE_eval_zero hA hw.1.1).1 hz)))
        exact ⟨rfl, ⟨b₁, k, t.locals⟩,
          hst.trans (.single (by rw [cstep_ite, ite_eq_right hz])), .inl (.here hA)⟩
    | «while» e b =>
      obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .while)
      exact ⟨rfl, ⟨.while e b, k, t.locals⟩, hst, .inl (.wmid rfl hA)⟩
    | call x p args =>
      obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .atomic)
      refine ⟨rfl, ⟨.call x p args, k, t.locals⟩, hst, .inr ⟨by simp [plug_locked, Cmd.locked], ?_⟩⟩
      intro hR
      exact ⟨x, p, args, _, _, _, rfl, rfl, hA, hR, .refl⟩
  | @wmid e b s hwh hA =>
    obtain ⟨stmt, k, σ⟩ := t
    simp only at hwh hA; subst hwh
    have he : EWF Rsv e := hwf.1.1
    by_cases hz : e.eval σ = 0
    · obtain ⟨rfl, rfl, rfl⟩ :=
        Step.det hs (plug_step (impl := impl) k (.iteF ((trE_eval_zero hA he).2 hz)))
      exact ⟨rfl, ⟨.skip, k, σ⟩, .single (by rw [cstep_while, ite_eq_left hz]), .inl (.here hA)⟩
    · obtain ⟨rfl, rfl, rfl⟩ :=
        Step.det hs (plug_step (impl := impl) k (.iteT (mt (trE_eval_zero hA he).1 hz)))
      exact ⟨rfl, ⟨b, .loop e b k, σ⟩, .single (by rw [cstep_while, ite_eq_right hz]),
        .inl (.here hA)⟩

/-- A Python step of the thread inside the block either continues the block,
or leaves it. Leaving it is where the C call happens: by `PrimOK` and
determinism the block computed exactly the primitive's result. -/
theorem thread_step_blk (hP : PrimOK impl Rsv arity P R) (i : Nat) {t : CThread Pn} {a : Abs}
    {th : Thread} {H : Heap} {c' : Cmd} {s' : Store} {H' : Heap}
    (hwf : CWF Rsv arity t) (hB : InBlk impl Rsv R t a th H) (hs : Step th.cmd th.store H c' s' H') :
    InBlk impl Rsv R t a ⟨c', s'⟩ H' ∨
      ∃ c₁ : Config Pn Abs, ClightL.step (P i) (t.cfg a) = some c₁ ∧
        Out impl Rsv (thr c₁) ⟨c', s'⟩ ∧ R c₁.abs H' := by
  obtain ⟨x, p, args, B, s₀, H₀, hst, hc, hA, hR, hps⟩ := hB
  obtain ⟨stmt, k, σ⟩ := t
  simp only at hst hc hA hwf; subst hst
  rw [hc] at hs
  by_cases hBs : B = .skip
  · subst hBs
    obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .inAtomicSkip)
    right
    have hw : ¬ Rsv x ∧ args.length = arity p ∧ ∀ e ∈ args, EWF Rsv e := hwf.1
    cases hv : P i p (args.map (·.eval σ)) a with
    | none => exact absurd hps (hP.stuck i p args x σ s₀ a H₀ hA hw.1 hw.2.2 hw.2.1 hR hv _ _)
    | some r =>
      obtain ⟨v, a'⟩ := r
      obtain ⟨s'', H'', hps', hA', hR'⟩ := hP.ok i p args x σ s₀ a H₀ v a' hA hw.1 hw.2.2 hR hv
      obtain ⟨rfl, rfl⟩ := PSteps.skip_unique hps hps'
      exact ⟨⟨.skip, k, σ.set x v, a'⟩, by simp [ClightL.step, CThread.cfg, hv], .here hA', hR'⟩
  · obtain ⟨c'', hstep, rfl⟩ := plug_inv k (by simp) hs
    cases hstep with
    | inAtomic h => exact .inl ⟨x, p, args, _, s₀, H₀, rfl, rfl, hA, hR, hps.snoc h⟩
    | inAtomicSkip => exact absurd rfl hBs

/-! ### Python ⇒ C -/

theorem rel_step (hP : PrimOK impl Rsv arity P R) {cs : List (CThread Pn)} {a : Abs}
    {ts ts' : Pool} {H H' : Heap}
    (hR : Rel impl Rsv arity R cs a ts H) (hm : MStep ts H ts' H') :
    ∃ cs' a', CSteps P cs a cs' a' ∧ Rel impl Rsv arity R cs' a' ts' H' := by
  cases hm with
  | @step i hi c' s' H' hs hlk =>
  have hci : i < cs.length := hR.len ▸ hi
  rcases hR.thr i hci hi with hO | hB
  · -- outside any block
    obtain ⟨rfl, t', hst, hres⟩ := thread_step_out (P := P) (a := a) i (hR.wf i hci) hO hs
    have hC : CSteps P cs a (cs.set i t') a := star_csteps i hst cs hci rfl
    have hw' : CWF Rsv arity t' := by simpa using star_wf hst (by simpa using hR.wf i hci)
    have hil : ts[i].cmd.locked = false := out_locked hO
    refine ⟨_, _, hC, ⟨by simp [hR.len], ?_, ?_, ?_, ?_⟩⟩
    · intro j hj
      rw [List.getElem_set]; split
      · rename_i hij; subst hij; exact hw'
      · exact hR.wf j (by simpa using hj)
    · intro j hj hj'
      simp only [List.getElem_set]; split
      · rename_i hij; subst hij
        rcases hres with h | ⟨hl, hb⟩
        · exact .inl h
        · refine .inr (hb (hR.heap fun j hj => ?_))
          by_cases hji : j = i
          · subst hji; exact hil
          · exact hlk hil hl j hj hji
      · exact hR.thr j (by simpa using hj) (by simpa using hj')
    · intro hall; apply hR.heap; intro j hj
      by_cases hji : j = i
      · subst hji; exact hil
      · have := hall j (by simpa using hj)
        simpa [List.getElem_set, Ne.symm hji] using this
    · intro j l hj hl hjl hll
      rw [List.getElem_set] at hjl hll
      by_cases hij : i = j <;> by_cases hil' : i = l
      · exact hij.symm.trans hil'
      · rw [ite_eq_left hij] at hjl; rw [ite_eq_right hil'] at hll
        rw [hlk hil hjl l (by simpa using hl) (Ne.symm hil')] at hll; cases hll
      · rw [ite_eq_right hij] at hjl; rw [ite_eq_left hil'] at hll
        rw [hlk hil hll j (by simpa using hj) (Ne.symm hij)] at hjl; cases hjl
      · rw [ite_eq_right hij] at hjl; rw [ite_eq_right hil'] at hll
        exact hR.one j l (by simpa using hj) (by simpa using hl) hjl hll
  · -- inside the block
    have hil : ts[i].cmd.locked = true := inBlk_locked hB
    have hO' : ∀ j (hj : j < cs.length) (hj' : j < ts.length), j ≠ i →
        Out impl Rsv cs[j] ts[j] := by
      intro j hj hj' hne
      rcases hR.thr j hj hj' with h | h
      · exact h
      · exact absurd (hR.one j i hj' hi (inBlk_locked h) hil) hne
    rcases thread_step_blk hP i (hR.wf i hci) hB hs with hB' | ⟨c₁, hc₁, hO₁, hR₁⟩
    · refine ⟨cs, a, .refl, ⟨by simp [hR.len], hR.wf, ?_, ?_, ?_⟩⟩
      · intro j hj hj'
        simp only [List.getElem_set]; split
        · rename_i hij; subst hij; exact .inr hB'
        · exact .inl (hO' j hj (by simpa using hj') (Ne.symm ‹_›))
      · intro hall
        have := hall i (by simpa using hi)
        simp only [List.getElem_set_self] at this
        rw [inBlk_locked hB'] at this; cases this
      · intro j l hj hl hjl hll
        rw [List.getElem_set] at hjl hll
        by_cases hij : i = j <;> by_cases hil' : i = l
        · exact hij.symm.trans hil'
        · rw [ite_eq_right hil'] at hll
          exact absurd (hR.one l i (by simpa using hl) hi hll hil) (Ne.symm hil')
        · rw [ite_eq_right hij] at hjl
          exact absurd (hR.one j i (by simpa using hj) hi hjl hil) (Ne.symm hij)
        · rw [ite_eq_right hij] at hjl; rw [ite_eq_right hil'] at hll
          exact hR.one j l (by simpa using hj) (by simpa using hl) hjl hll
    · refine ⟨cs.set i (thr c₁), c₁.abs, .step (.step i hci hc₁) .refl,
        ⟨by simp [hR.len], ?_, ?_, fun _ => hR₁, ?_⟩⟩
      · intro j hj
        rw [List.getElem_set]; split
        · rename_i hij; subst hij; exact step_wf (by simpa using hR.wf i hci) hc₁
        · exact hR.wf j (by simpa using hj)
      · intro j hj hj'
        simp only [List.getElem_set]; split
        · rename_i hij; subst hij; exact .inl hO₁
        · exact .inl (hO' j (by simpa using hj) (by simpa using hj') (Ne.symm ‹_›))
      · intro j l hj hl hjl hll
        rw [List.getElem_set] at hjl hll
        by_cases hij : i = j <;> by_cases hil' : i = l
        · exact hij.symm.trans hil'
        · rw [ite_eq_left hij, out_locked hO₁] at hjl; cases hjl
        · rw [ite_eq_left hil', out_locked hO₁] at hll; cases hll
        · rw [ite_eq_right hij] at hjl; rw [ite_eq_right hil'] at hll
          exact hR.one j l (by simpa using hj) (by simpa using hl) hjl hll

/-- **Python ⇒ C.** Every execution of the Python pool, under any
interleaving, is matched by an execution of the C machine. -/
theorem py_to_c (hP : PrimOK impl Rsv arity P R) {k : Nat} {cs : List (CThread Pn)} {a : Abs}
    {ts ts' : Pool} {H H' : Heap}
    (hR : Rel impl Rsv arity R cs a ts H) (hm : MSteps k ts H ts' H') :
    ∃ cs' a', CSteps P cs a cs' a' ∧ Rel impl Rsv arity R cs' a' ts' H' := by
  induction hm generalizing cs a with
  | refl => exact ⟨cs, a, .refl, hR⟩
  | step h _ ih =>
    obtain ⟨cs₁, a₁, hc₁, hR₁⟩ := rel_step hP hR h
    obtain ⟨cs₂, a₂, hc₂, hR₂⟩ := ih hR₁
    exact ⟨cs₂, a₂, hc₁.trans hc₂, hR₂⟩

/-- When every Python thread has finished, so has every C CPU: same locals,
related shared state. -/
theorem py_done {cs : List (CThread Pn)} {a : Abs} {ts : Pool} {H : Heap}
    (hR : Rel impl Rsv arity R cs a ts H) (hdone : ∀ i (hi : i < ts.length), ts[i].cmd = .skip) :
    R a H ∧ ∀ i (hi : i < cs.length) (ht : i < ts.length),
      cs[i].stmt = .skip ∧ cs[i].cont = .stop ∧ Agree Rsv cs[i].locals ts[i].store := by
  refine ⟨hR.heap fun i hi => by rw [hdone i hi]; rfl, fun i hi ht => ?_⟩
  have hd := hdone i ht
  rcases hR.thr i hi ht with hO | hB
  · generalize ts[i] = th at hO hd ⊢
    cases hO with
    | here hA =>
      obtain ⟨hk, hs⟩ := plug_eq_skip hd
      exact ⟨tr_eq_skip hs, hk, hA⟩
    | wmid => exact absurd (plug_eq_skip hd).2 (by simp)
  · obtain ⟨_, _, _, _, _, _, _, hc, _⟩ := hB
    rw [hd] at hc
    exact absurd (plug_eq_skip hc.symm).2 (by simp)

/-! ### C ⇒ Python -/

theorem out_of_eq {t : CThread Pn} {th : Thread} (h : th.cmd = embed impl t)
    (hA : Agree Rsv t.locals th.store) : Out impl Rsv t th := by
  obtain ⟨c, s⟩ := th
  simp only at h hA; subst h; exact .here hA

theorem sync_rel {cs : List (CThread Pn)} {a : Abs} {ts : Pool} {H : Heap}
    (hS : Sync impl Rsv arity R cs a ts H) : Rel impl Rsv arity R cs a ts H where
  len := hS.len
  wf := hS.wf
  thr i hi ht := .inl (out_of_eq (hS.thr i hi ht).1 (hS.thr i hi ht).2)
  heap _ := hS.heap
  one i _ hi _ h := by
    rw [(hS.thr i (hS.len ▸ hi) hi).1, embed_locked] at h; cases h

/-- One C step of one CPU is matched by a run of the corresponding Python
thread (a `with L:` block for a primitive call). -/
theorem thread_c_step (hP : PrimOK impl Rsv arity P R) (i : Nat) {t : CThread Pn} {a : Abs}
    {s : Store} {H : Heap} {c₁ : Config Pn Abs}
    (hwf : CWF Rsv arity t) (hA : Agree Rsv t.locals s) (hR : R a H)
    (h : ClightL.step (P i) (t.cfg a) = some c₁) :
    ∃ s' H', PSteps (embed impl t) s H (embed impl (thr c₁)) s' H' ∧
      Agree Rsv c₁.locals s' ∧ R c₁.abs H' := by
  obtain ⟨stmt, k, σ⟩ := t
  cases stmt with
  | skip =>
    cases k with
    | stop => simp [ClightL.step, CThread.cfg] at h
    | seq s₂ k =>
      simp [ClightL.step, CThread.cfg] at h; subst h
      exact ⟨s, H, .single (plug_step k .seqSkip), hA, hR⟩
    | loop e b k =>
      simp [ClightL.step, CThread.cfg] at h; subst h
      exact ⟨s, H, .single (plug_step k .seqSkip), hA, hR⟩
  | assign x e =>
    simp [ClightL.step, CThread.cfg] at h; subst h
    refine ⟨_, H, .single (plug_step k .assign), ?_, hR⟩
    rw [trE_eval hA e hwf.1.2]; exact agree_set hA x _
  | seq a b =>
    simp [ClightL.step, CThread.cfg] at h; subst h
    exact ⟨s, H, .refl, hA, hR⟩
  | ite e b₁ b₂ =>
    rw [cstep_ite] at h; cases h
    by_cases hz : e.eval σ = 0
    · rw [ite_eq_left hz]
      exact ⟨s, H, .single (plug_step k (.iteF ((trE_eval_zero hA hwf.1.1).2 hz))), hA, hR⟩
    · rw [ite_eq_right hz]
      exact ⟨s, H, .single (plug_step k (.iteT (mt (trE_eval_zero hA hwf.1.1).1 hz))), hA, hR⟩
  | «while» e b =>
    rw [cstep_while] at h
    by_cases hz : e.eval σ = 0
    · rw [ite_eq_left hz] at h; cases h
      exact ⟨s, H, .step (plug_step k .while)
        (.single (plug_step k (.iteF ((trE_eval_zero hA hwf.1.1).2 hz)))), hA, hR⟩
    · rw [ite_eq_right hz] at h; cases h
      exact ⟨s, H, .step (plug_step k .while)
        (.single (plug_step k (.iteT (mt (trE_eval_zero hA hwf.1.1).1 hz)))), hA, hR⟩
  | call x p args =>
    have hw : ¬ Rsv x ∧ args.length = arity p ∧ ∀ e ∈ args, EWF Rsv e := hwf.1
    cases hv : P i p (args.map (·.eval σ)) a with
    | none => simp [ClightL.step, CThread.cfg, hv] at h
    | some r =>
      obtain ⟨v, a'⟩ := r
      simp [ClightL.step, CThread.cfg, hv] at h; subst h
      obtain ⟨s', H', hps, hA', hR'⟩ := hP.ok i p args x σ s a H v a' hA hw.1 hw.2.2 hR hv
      exact ⟨s', H', .step (plug_step k .atomic)
        ((hps.inAtomic.plug k).trans (.single (plug_step k .inAtomicSkip))), hA', hR'⟩

/-- A thread can run a sequential stretch on its own in the pool, provided no
other thread holds the lock. -/
theorem lift_psteps (i : Nat) {c s H c' s' H'} (h : PSteps c s H c' s' H') :
    ∀ (ts : Pool) (hi : i < ts.length), ts[i] = ⟨c, s⟩ →
      (∀ j (hj : j < ts.length), j ≠ i → ts[j].cmd.locked = false) →
      ∃ k, MSteps k ts H (ts.set i ⟨c', s'⟩) H' := by
  induction h with
  | refl =>
    intro ts hi he _
    rw [← he, List.set_getElem_self]; exact ⟨0, .refl⟩
  | @step c s H c₁ s₁ H₁ c₂ s₂ H₂ h₁ _ ih =>
    intro ts hi he hoth
    have hm : MStep ts H (ts.set i ⟨c₁, s₁⟩) H₁ :=
      .step i hi (by rw [he]; exact h₁) (fun _ _ j hj hne => hoth j hj hne)
    obtain ⟨k, hk⟩ := ih (ts.set i ⟨c₁, s₁⟩) (by simpa using hi) (by simp) (by
      intro j hj hne
      simp only [List.getElem_set, Ne.symm hne, ite_false]
      exact hoth j (by simpa using hj) hne)
    rw [List.set_set] at hk
    exact ⟨k + 1, .step hm hk⟩

theorem sync_step (hP : PrimOK impl Rsv arity P R) {cs cs' : List (CThread Pn)} {a a' : Abs}
    {ts : Pool} {H : Heap}
    (hS : Sync impl Rsv arity R cs a ts H) (hc : CStep P cs a cs' a') :
    ∃ k ts' H', MSteps k ts H ts' H' ∧ Sync impl Rsv arity R cs' a' ts' H' := by
  cases hc with
  | @step c₁ i hi h =>
  have hti : i < ts.length := hS.len ▸ hi
  obtain ⟨hc, hA⟩ := hS.thr i hi hti
  obtain ⟨s', H', hps, hA', hR'⟩ := thread_c_step hP i (hS.wf i hi) hA hS.heap h
  rw [← hc] at hps
  obtain ⟨k, hk⟩ := lift_psteps i hps ts hti rfl (fun j hj _ => by
    rw [(hS.thr j (hS.len ▸ hj) hj).1, embed_locked])
  refine ⟨k, _, H', hk, ⟨by simp [hS.len], ?_, ?_, hR'⟩⟩
  · intro j hj
    rw [List.getElem_set]; split
    · rename_i hij; subst hij; exact step_wf (by simpa using hS.wf i hi) h
    · exact hS.wf j (by simpa using hj)
  · intro j hj hj'
    simp only [List.getElem_set]; split
    · rename_i hij; subst hij; exact ⟨rfl, hA'⟩
    · exact hS.thr j (by simpa using hj) (by simpa using hj')

/-- **C ⇒ Python.** Every execution of the C machine is matched by an
execution of the Python pool. -/
theorem c_to_py (hP : PrimOK impl Rsv arity P R) {cs cs' : List (CThread Pn)} {a a' : Abs}
    {ts : Pool} {H : Heap}
    (hS : Sync impl Rsv arity R cs a ts H) (hc : CSteps P cs a cs' a') :
    ∃ k ts' H', MSteps k ts H ts' H' ∧ Sync impl Rsv arity R cs' a' ts' H' := by
  induction hc generalizing ts H with
  | refl => exact ⟨0, ts, H, .refl, hS⟩
  | step h _ ih =>
    obtain ⟨k₁, ts₁, H₁, hm₁, hS₁⟩ := sync_step hP hS h
    obtain ⟨k₂, ts₂, H₂, hm₂, hS₂⟩ := ih hS₁
    exact ⟨_, ts₂, H₂, MSteps_trans hm₁ hm₂, hS₂⟩

end Machine

end ClightToPy
