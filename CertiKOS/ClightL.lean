/-!
# ClightL: a tiny Clight-style language with a deterministic small-step semantics

Prototype of the C semantics proposed in `SCOPING.md` §4.1.

Design points carried over from CertiKOS (CCAL):
* `step` is a *function* `Config → Option Config`, so the semantics is
  deterministic by construction.
* The language itself knows nothing about concurrency. The only way to touch
  shared state is an external `call` to a primitive of the layer underneath.
  A primitive table is a deterministic function; in the concurrent setting it
  closes over the CPU id and the environment context ε (see `TicketLock.lean`).
* Values are 32-bit, matching IA-32 mC2.

Not yet modelled (needed before real kernel code): block-based memory and
pointers, structs, function calls between C functions, `return`, and `break`.
-/

namespace ClightL

/-- 32-bit machine values (IA-32). -/
abbrev Val := BitVec 32
abbrev Ident := String
abbrev Locals := Ident → Val

def Locals.set (σ : Locals) (x : Ident) (v : Val) : Locals :=
  fun y => if y = x then v else σ y

@[simp] theorem Locals.set_same (σ : Locals) (x : Ident) (v : Val) :
    σ.set x v x = v := by simp [Locals.set]

@[simp] theorem Locals.set_other (σ : Locals) {x y : Ident} (v : Val) (h : y ≠ x) :
    σ.set x v y = σ y := by simp [Locals.set, h]

inductive BinOp
  | add | sub | eq | ne | ltu

inductive Expr
  | const (v : Val)
  | var (x : Ident)
  | bin (op : BinOp) (a b : Expr)

def BinOp.eval : BinOp → Val → Val → Val
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .eq,  a, b => if a = b then 1 else 0
  | .ne,  a, b => if a = b then 0 else 1
  | .ltu, a, b => if a.ult b then 1 else 0

def Expr.eval (σ : Locals) : Expr → Val
  | .const v => v
  | .var x => σ x
  | .bin op a b => op.eval (a.eval σ) (b.eval σ)

/-- Statements, parameterised by the type `Pn` of primitive names offered by
the layer underneath. -/
inductive Stmt (Pn : Type)
  | skip
  | assign (x : Ident) (e : Expr)
  | seq (s₁ s₂ : Stmt Pn)
  | ite (c : Expr) (s₁ s₂ : Stmt Pn)
  | while (c : Expr) (body : Stmt Pn)
  /-- `x := p(args)`: call primitive `p` of the underlying layer. -/
  | call (x : Ident) (p : Pn) (args : List Expr)

/-- CompCert-style continuations. -/
inductive Cont (Pn : Type)
  | stop
  | seq (s : Stmt Pn) (k : Cont Pn)
  | loop (c : Expr) (body : Stmt Pn) (k : Cont Pn)

structure Config (Pn Abs : Type) where
  stmt : Stmt Pn
  cont : Cont Pn
  locals : Locals
  /-- Abstract state of the layer underneath (e.g. the shared log). -/
  abs : Abs

/-- The primitive table of a layer. Deterministic by its type: given the
arguments and the abstract state it returns at most one result.
`none` means the primitive's precondition fails (stuck, as in CertiKOS). -/
abbrev Prims (Pn Abs : Type) := Pn → List Val → Abs → Option (Val × Abs)

variable {Pn Abs : Type}

/-- One small step. `none` means the configuration is final or stuck. -/
def step (P : Prims Pn Abs) (c : Config Pn Abs) : Option (Config Pn Abs) :=
  match c.stmt, c.cont with
  | .skip, .stop => none
  | .skip, .seq s k => some { c with stmt := s, cont := k }
  | .skip, .loop e b k => some { c with stmt := .while e b, cont := k }
  | .assign x e, _ =>
      some { c with stmt := .skip, locals := c.locals.set x (e.eval c.locals) }
  | .seq s₁ s₂, k => some { c with stmt := s₁, cont := .seq s₂ k }
  | .ite e s₁ s₂, _ =>
      some { c with stmt := if e.eval c.locals = 0 then s₂ else s₁ }
  | .while e b, k =>
      if e.eval c.locals = 0 then some { c with stmt := .skip }
      else some { c with stmt := b, cont := .loop e b k }
  | .call x p args, _ =>
      match P p (args.map (·.eval c.locals)) c.abs with
      | some (v, a') => some { c with stmt := .skip, locals := c.locals.set x v, abs := a' }
      | none => none

/-- Reflexive-transitive closure of `step`. -/
inductive Star (P : Prims Pn Abs) : Config Pn Abs → Config Pn Abs → Prop
  | refl (c) : Star P c c
  | step {c c' c''} : step P c = some c' → Star P c' c'' → Star P c c''

theorem Star.trans {P : Prims Pn Abs} {a b c : Config Pn Abs} :
    Star P a b → Star P b c → Star P a c := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem Star.single {P : Prims Pn Abs} {a b : Config Pn Abs} (h : ClightL.step P a = some b) :
    Star P a b := .step h (.refl _)

/-- A configuration has finished normally. -/
def Final (c : Config Pn Abs) : Prop := c.stmt = .skip ∧ c.cont = .stop

theorem step_final {P : Prims Pn Abs} {c : Config Pn Abs} (h : Final c) : step P c = none := by
  obtain ⟨stmt, cont, locals, abs⟩ := c
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  subst h1; subst h2
  rfl

end ClightL
