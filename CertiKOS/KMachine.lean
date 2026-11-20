import CertiKOS.MALOp

/-!
# The machine model, second part: kernel contexts

In mCertiKOS a kernel context is six saved registers (`ESP`, `EDI`, `ESI`,
`EBX`, `EBP` and the return address), and `cswitch` is twenty assembly
instructions that store them and load another six. What that means is control:
execution continues where the other context left off, on its stack.

ClightL has no registers, stack or code pointers. So here **a kernel context
is a suspended ClightL computation**: the statement to run, the continuation
(the stack and the return address), and the locals (the saved registers).

* `KCtx`: a suspended computation. `KState`: the running one, the pool of
  kernel contexts, and the shared log.
* `kstep`: one step of the kernel machine. Ordinary steps are ClightL's and
  leave the pool alone. Three calls are the machine's own:
  * `cswitch(n, n')` parks the running computation in slot `n`, as a
    computation about to return `0` from the call, and resumes slot `n'`.
    This is the whole of `cswitch`.
  * `set_SP(n)` gives context `n` an empty stack.
  * `set_RA(n, f)` makes context `n` start at function `f`. Function
    pointers are numbers, looked up in the table `code`.
* `runs_map`, `KStar.of_runs`: **code of the layers below runs on the kernel
  machine as it did**, and leaves the pool alone. Every triple proved so far
  is about such code.
* `kstar_seq`: a statement of the layers below followed by something else.
* `kstep_cswitch`, `kstep_setSP`, `kstep_setRA`: the three machine calls.

What this leaves out: the pool is the state of one CPU's machine, not a
table shared by CPUs, so a thread does not move between CPUs. Nothing here
says a parked thread is ever resumed; that is the scheduler's business.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace KMach

open ClightL Ticket
open LockArray (APrim)
open LockRegion (RLog REnv)
open LockRegionCPU KernFrame MALOp

/-! ## Renaming primitives -/

section Map
variable {Pn Qn Abs : Type}

def mapS (f : Pn → Qn) : Stmt Pn → Stmt Qn
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq a b => .seq (mapS f a) (mapS f b)
  | .ite c a b => .ite c (mapS f a) (mapS f b)
  | .while c b => .while c (mapS f b)
  | .call x p args => .call x (f p) args

def mapK (f : Pn → Qn) : Cont Pn → Cont Qn
  | .stop => .stop
  | .seq s k => .seq (mapS f s) (mapK f k)
  | .loop c b k => .loop c (mapS f b) (mapK f k)

def mapC (f : Pn → Qn) (c : Config Pn Abs) : Config Qn Abs :=
  ⟨mapS f c.stmt, mapK f c.cont, c.locals, c.abs⟩

/-- A step commutes with renaming, when the tables agree. -/
theorem step_map {P : Prims Pn Abs} {Q : Prims Qn Abs} {f : Pn → Qn} (hf : ∀ p, Q (f p) = P p)
    (c : Config Pn Abs) : step Q (mapC f c) = (step P c).map (mapC f) := by
  obtain ⟨s, k, σ, a⟩ := c
  cases s with
  | skip => cases k <;> rfl
  | assign x e => rfl
  | seq s1 s2 => rfl
  | ite e s1 s2 =>
    by_cases h : e.eval σ = 0#32 <;> simp [step, mapC, mapS, h]
  | «while» e b =>
    by_cases h : e.eval σ = 0#32 <;> simp [step, mapC, mapS, mapK, h]
  | call x p args =>
    show (match Q (f p) (args.map (Expr.eval σ)) a with
      | some (v, a') => some (⟨.skip, mapK f k, σ.set x v, a'⟩ : Config Qn Abs)
      | none => none) = _
    rw [hf]
    show _ = (match P p (args.map (Expr.eval σ)) a with
      | some (v, a') => some (⟨.skip, k, σ.set x v, a'⟩ : Config Pn Abs)
      | none => none).map (mapC f)
    cases P p (args.map (Expr.eval σ)) a with
    | none => rfl
    | some va => rfl

theorem star_map {P : Prims Pn Abs} {Q : Prims Qn Abs} {f : Pn → Qn} (hf : ∀ p, Q (f p) = P p)
    {c c' : Config Pn Abs} (h : Star P c c') : Star Q (mapC f c) (mapC f c') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (by rw [step_map hf, hs]; rfl) ih

/-- **Renamed code runs as the original.** -/
theorem runs_map {P : Prims Pn Abs} {Q : Prims Qn Abs} {f : Pn → Qn} (hf : ∀ p, Q (f p) = P p)
    {s : Stmt Pn} {σ σ' : Locals} {l l' : Abs} (h : Runs P s σ l σ' l') : Runs Q (mapS f s) σ l σ' l' :=
  Runs.of_stop (star_map hf (h .stop))

end Map

/-! ## The kernel machine -/

/-- The primitives of the kernel machine: those of the layers below, and the
three that act on kernel contexts. -/
inductive KPrim
  | base (p : APrim)
  | cswitch
  | setSP
  | setRA

/-- The table for ClightL: only the primitives of the layers below. The
other three are steps of the machine. -/
def kprims (εR : REnv) (c : CPU) : Prims KPrim RLog
  | .base p, args, l => rprimsA εR c p args l
  | _, _, _ => none

/-- **A kernel context**: a suspended computation. -/
structure KCtx where
  stmt : Stmt KPrim
  cont : Cont KPrim
  locals : Locals

structure KState where
  /-- the computation that is running -/
  run : KCtx
  /-- the kernel contexts -/
  pool : Nat → KCtx
  log : RLog

/-- One step of the kernel machine. `code` is the text: function `f` is
`code f`. -/
def kstep (εR : REnv) (c : CPU) (code : Nat → Stmt KPrim) (s : KState) : Option KState :=
  match ClightL.step (kprims εR c) ⟨s.run.stmt, s.run.cont, s.run.locals, s.log⟩ with
  | some c' => some ⟨⟨c'.stmt, c'.cont, c'.locals⟩, s.pool, c'.abs⟩
  | none =>
    match s.run.stmt with
    | .call x .cswitch [e1, e2] =>
      let pool' := setAt s.pool (e1.eval s.run.locals).toNat ⟨.skip, s.run.cont, s.run.locals.set x 0⟩
      some ⟨pool' (e2.eval s.run.locals).toNat, pool', s.log⟩
    | .call x .setSP [e1] =>
      let n := (e1.eval s.run.locals).toNat
      some ⟨⟨.skip, s.run.cont, s.run.locals.set x 0⟩, setAt s.pool n { s.pool n with cont := .stop }, s.log⟩
    | .call x .setRA [e1, e2] =>
      let n := (e1.eval s.run.locals).toNat
      some ⟨⟨.skip, s.run.cont, s.run.locals.set x 0⟩,
        setAt s.pool n { s.pool n with stmt := code (e2.eval s.run.locals).toNat }, s.log⟩
    | _ => none

inductive KStar (εR : REnv) (c : CPU) (code : Nat → Stmt KPrim) : KState → KState → Prop
  | refl (s) : KStar εR c code s s
  | step {s s' s''} : kstep εR c code s = some s' → KStar εR c code s' s'' → KStar εR c code s s''

section Machine
variable {εR : REnv} {c : CPU} {code : Nat → Stmt KPrim}

theorem KStar.trans {a b d : KState} (h1 : KStar εR c code a b) (h2 : KStar εR c code b d) :
    KStar εR c code a d := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

theorem KStar.single {a b : KState} (h : kstep εR c code a = some b) : KStar εR c code a b :=
  .step h (.refl _)

/-- A ClightL step is a step of the kernel machine that leaves the pool alone. -/
theorem kstep_of_step {cfg cfg' : Config KPrim RLog} (h : ClightL.step (kprims εR c) cfg = some cfg')
    (pool : Nat → KCtx) :
    kstep εR c code ⟨⟨cfg.stmt, cfg.cont, cfg.locals⟩, pool, cfg.abs⟩ =
      some ⟨⟨cfg'.stmt, cfg'.cont, cfg'.locals⟩, pool, cfg'.abs⟩ := by
  unfold kstep
  have e : (⟨cfg.stmt, cfg.cont, cfg.locals, cfg.abs⟩ : Config KPrim RLog) = cfg := rfl
  simp only [e, h]

theorem KStar.of_star {cfg cfg' : Config KPrim RLog} (h : Star (kprims εR c) cfg cfg') (pool : Nat → KCtx) :
    KStar εR c code ⟨⟨cfg.stmt, cfg.cont, cfg.locals⟩, pool, cfg.abs⟩
      ⟨⟨cfg'.stmt, cfg'.cont, cfg'.locals⟩, pool, cfg'.abs⟩ := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (kstep_of_step hs pool) ih

theorem kprims_base (p : APrim) : kprims εR c (.base p) = rprimsA εR c p := rfl

/-- **Code of the layers below runs on the kernel machine as it did**, under
any continuation, and leaves the kernel contexts alone. -/
theorem KStar.of_runs {s : Stmt APrim} {σ σ' : Locals} {l l' : RLog}
    (h : Runs (rprimsA εR c) s σ l σ' l') (K : Cont KPrim) (pool : Nat → KCtx) :
    KStar εR c code ⟨⟨mapS .base s, K, σ⟩, pool, l⟩ ⟨⟨.skip, K, σ'⟩, pool, l'⟩ :=
  KStar.of_star (cfg := ⟨mapS .base s, K, σ, l⟩) (cfg' := ⟨.skip, K, σ', l'⟩)
    (runs_map (Q := kprims εR c) (f := KPrim.base) kprims_base h K) pool

/-- A statement of the layers below, then the rest. -/
theorem kstar_seq {s : Stmt APrim} {σ σ' : Locals} {l l' : RLog} (h : Runs (rprimsA εR c) s σ l σ' l')
    (rest : Stmt KPrim) (K : Cont KPrim) (pool : Nat → KCtx) :
    KStar εR c code ⟨⟨.seq (mapS .base s) rest, K, σ⟩, pool, l⟩ ⟨⟨rest, K, σ'⟩, pool, l'⟩ := by
  have h1 : kstep εR c code ⟨⟨.seq (mapS .base s) rest, K, σ⟩, pool, l⟩ =
      some ⟨⟨mapS .base s, .seq rest K, σ⟩, pool, l⟩ :=
    kstep_of_step (cfg := ⟨.seq (mapS .base s) rest, K, σ, l⟩) (cfg' := ⟨mapS .base s, .seq rest K, σ, l⟩) rfl pool
  have h2 : kstep εR c code ⟨⟨.skip, .seq rest K, σ'⟩, pool, l'⟩ = some ⟨⟨rest, K, σ'⟩, pool, l'⟩ :=
    kstep_of_step (cfg := ⟨.skip, .seq rest K, σ', l'⟩) (cfg' := ⟨rest, K, σ', l'⟩) rfl pool
  exact .step h1 ((KStar.of_runs h (.seq rest K) pool).trans (.single h2))

/-- **`cswitch(n, n')`**: the running computation is parked in slot `n`, about
to return `0`, and slot `n'` runs. -/
theorem kstep_cswitch (x : Ident) (e1 e2 : Expr) (K : Cont KPrim) (σ : Locals) (pool : Nat → KCtx) (l : RLog) :
    kstep εR c code ⟨⟨.call x .cswitch [e1, e2], K, σ⟩, pool, l⟩ =
      some ⟨setAt pool (e1.eval σ).toNat ⟨.skip, K, σ.set x 0⟩ (e2.eval σ).toNat,
        setAt pool (e1.eval σ).toNat ⟨.skip, K, σ.set x 0⟩, l⟩ := rfl

/-- **`set_SP(n)`**: context `n` gets an empty stack. -/
theorem kstep_setSP (x : Ident) (e1 : Expr) (K : Cont KPrim) (σ : Locals) (pool : Nat → KCtx) (l : RLog) :
    kstep εR c code ⟨⟨.call x .setSP [e1], K, σ⟩, pool, l⟩ =
      some ⟨⟨.skip, K, σ.set x 0⟩,
        setAt pool (e1.eval σ).toNat { pool (e1.eval σ).toNat with cont := .stop }, l⟩ := rfl

/-- **`set_RA(n, f)`**: context `n` starts at function `f`. -/
theorem kstep_setRA (x : Ident) (e1 e2 : Expr) (K : Cont KPrim) (σ : Locals) (pool : Nat → KCtx) (l : RLog) :
    kstep εR c code ⟨⟨.call x .setRA [e1, e2], K, σ⟩, pool, l⟩ =
      some ⟨⟨.skip, K, σ.set x 0⟩,
        setAt pool (e1.eval σ).toNat { pool (e1.eval σ).toNat with stmt := code (e2.eval σ).toNat }, l⟩ := rfl

/-- `skip` under a sequence: on to the next statement. -/
theorem kstep_skip_seq (rest : Stmt KPrim) (K : Cont KPrim) (σ : Locals) (pool : Nat → KCtx) (l : RLog) :
    kstep εR c code ⟨⟨.skip, .seq rest K, σ⟩, pool, l⟩ = some ⟨⟨rest, K, σ⟩, pool, l⟩ := rfl

/-- A sequence: start on its first statement. -/
theorem kstep_seq (s1 s2 : Stmt KPrim) (K : Cont KPrim) (σ : Locals) (pool : Nat → KCtx) (l : RLog) :
    kstep εR c code ⟨⟨.seq s1 s2, K, σ⟩, pool, l⟩ = some ⟨⟨s1, .seq s2 K, σ⟩, pool, l⟩ := rfl

/-- A conditional. -/
theorem kstep_ite (e : Expr) (s1 s2 : Stmt KPrim) (K : Cont KPrim) (σ : Locals) (pool : Nat → KCtx) (l : RLog) :
    kstep εR c code ⟨⟨.ite e s1 s2, K, σ⟩, pool, l⟩ =
      some ⟨⟨if e.eval σ = 0 then s2 else s1, K, σ⟩, pool, l⟩ := rfl

/-- **A statement of the layers below, at the end.** -/
theorem kstar_base {s : Stmt APrim} {σ σ' : Locals} {l l' : RLog} (h : Runs (rprimsA εR c) s σ l σ' l')
    (K : Cont KPrim) (pool : Nat → KCtx) :
    KStar εR c code ⟨⟨mapS .base s, K, σ⟩, pool, l⟩ ⟨⟨.skip, K, σ'⟩, pool, l'⟩ := KStar.of_runs h K pool

end Machine

end KMach
