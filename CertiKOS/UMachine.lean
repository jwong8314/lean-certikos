import CertiKOS.PUCtxtIntro

/-!
# The machine model, third part: user mode

mCertiKOS's processor is either in kernel mode or in user mode (`ikern`). A
trap takes it from user mode into the kernel with the user's registers on the
kernel stack; `trap_out` (an `iret`) takes it back with the registers the
kernel loaded.

Here the kernel machine of `KMachine.lean` gets a second kind of state.

* `UState`: the machine is either running a kernel computation (`kern`), or
  in user mode with seventeen registers (`user`).
* `UStep`:
  * `kern`: a step of the kernel machine.
  * `iret`: **a kernel computation that has finished on an empty stack
    returns to user mode**, with the registers it left in the locals `u0` …
    `u16`. This is `trap_out`.
  * `trap`: from user mode the processor enters the kernel at the handler of
    the trap, on an empty kernel stack. The user's registers at that moment
    are in the locals `u0` … `u16`; the user program may have left anything
    in them, so they are arbitrary. This is the trap gate and `trap_in`.
* `UStar`, `UStar.of_kstar`.

So `ikern` is the kind of state the machine is in. What the user program does
between an `iret` and the next trap is not modelled, as in mCertiKOS, where
user code is the context the kernel is linked with.

What this leaves out: the lock. Every theorem about kernel code so far is
inside a critical section, and the kernel is entered and left with the lock
held by the CPU; acquiring it at the trap and releasing it at the `iret` is
not part of this machine yet. Interrupts are not modelled: a trap happens
only from user mode.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace UMach

open ClightL Ticket
open LockArray (APrim)
open LockRegion (RLog REnv)
open LockRegionCPU KernFrame MALOp KMach PUCtxt

/-- A state of the machine with user mode. -/
inductive UState
  /-- kernel mode: a kernel computation is running -/
  | kern (s : KState)
  /-- user mode, with the registers the kernel returned -/
  | user (rs : Nat → Val) (pool : Nat → KCtx) (log : RLog)

/-- The registers a kernel computation leaves for user mode. -/
def regsOf (σ : Locals) : Nat → Val := fun n => σ (ureg n)

/-- One step. `entry n` is the handler of trap `n`, as an index into `code`;
`lk` is the kernel lock, which every handler finds in the local `lk`. -/
inductive UStep (εR : REnv) (c : CPU) (code : Nat → Stmt KPrim) (entry : Nat → Nat) (lk : Val) :
    UState → UState → Prop
  | kern {s s' : KState} (h : kstep εR c code s = some s') : UStep εR c code entry lk (.kern s) (.kern s')
  | iret (σ : Locals) (pool : Nat → KCtx) (l : RLog) :
      UStep εR c code entry lk (.kern ⟨⟨.skip, .stop, σ⟩, pool, l⟩) (.user (regsOf σ) pool l)
  | trap (rs : Nat → Val) (pool : Nat → KCtx) (l : RLog) (n : Nat) (σ : Locals) (hlk : σ "lk" = lk) :
      UStep εR c code entry lk (.user rs pool l) (.kern ⟨⟨code (entry n), .stop, σ⟩, pool, l⟩)

inductive UStar (εR : REnv) (c : CPU) (code : Nat → Stmt KPrim) (entry : Nat → Nat) (lk : Val) :
    UState → UState → Prop
  | refl (s) : UStar εR c code entry lk s s
  | step {s s' s''} : UStep εR c code entry lk s s' → UStar εR c code entry lk s' s'' →
      UStar εR c code entry lk s s''

section Lemmas
variable {εR : REnv} {c : CPU} {code : Nat → Stmt KPrim} {entry : Nat → Nat} {lk : Val}

theorem UStar.trans {a b d : UState} (h1 : UStar εR c code entry lk a b) (h2 : UStar εR c code entry lk b d) :
    UStar εR c code entry lk a d := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem UStar.single {a b : UState} (h : UStep εR c code entry lk a b) : UStar εR c code entry lk a b :=
  .step h (.refl _)

/-- A run of the kernel machine is a run of the machine with user mode. -/
theorem UStar.of_kstar {s s' : KState} (h : KStar εR c code s s') :
    UStar εR c code entry lk (.kern s) (.kern s') := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.kern h) ih

/-- **A kernel run that ends on an empty stack ends in user mode.** -/
theorem UStar.iret {s : KState} {σ : Locals} {pool : Nat → KCtx} {l : RLog}
    (h : KStar εR c code s ⟨⟨.skip, .stop, σ⟩, pool, l⟩) :
    UStar εR c code entry lk (.kern s) (.user (regsOf σ) pool l) :=
  (UStar.of_kstar h).trans (.single (.iret σ pool l))

/-- **A trap, then a kernel run that ends on an empty stack**: from user mode
back to user mode. -/
theorem UStar.syscall {rs : Nat → Val} {pool pool' : Nat → KCtx} {l l' : RLog} (n : Nat) {σ σ' : Locals}
    (hlk : σ "lk" = lk)
    (h : KStar εR c code ⟨⟨code (entry n), .stop, σ⟩, pool, l⟩ ⟨⟨.skip, .stop, σ'⟩, pool', l'⟩) :
    UStar εR c code entry lk (.user rs pool l) (.user (regsOf σ') pool' l') :=
  .step (.trap rs pool l n σ hlk) (UStar.iret h)

end Lemmas

end UMach
