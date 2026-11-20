import CertiKOS.UMachine

/-!
# The machine model, fourth part: guest mode

With hardware virtualization the processor has a third mode: running a guest
(VMX non-root operation, `ihost = false` in mCertiKOS). The kernel enters it
with `vmlaunch`/`vmresume` at the end of `vm_run`; a VM exit takes the
processor back to the host, at the point `vmx_enter` saved, where
`vmx_return_from_guest` runs.

Here the machine of `UMachine.lean` gets a third kind of state.

* `GState`: kernel mode, user mode, or guest mode with the guest's seven
  registers (`EAX`, `EBX`, `EDX`, `ESI`, `EDI`, `EBP`, and `RA` for `eip`).
* `GStep`:
  * `kern`, `iret`, `trap`: as in `UMachine`. A kernel computation that ends
    on an empty stack with the local `GUEST` zero returns to user mode.
  * `vmentry`: **a kernel computation that ends on an empty stack with
    `GUEST` set enters the guest**, with the registers it left in `EAX` …
    `RA`. This is the `vmlaunch` at the end of `vm_run` (`VVMX.vmRun_step`
    leaves the guest's registers there).
  * `vmexit`: from guest mode the processor enters the kernel at the exit
    handler, on an empty kernel stack. The guest's registers at that moment
    are in `EAX` … `RA`; the guest may have left anything in them, so they
    are arbitrary. The handler begins with `vmx_return_from_guest`
    (`VVMX.return_step`), which saves them and restores the host's `ebp` and
    `edi` (`VVMX.vm_roundtrip`).
* `GStar`, `GStar.of_kstar`, `GStar.vmenter`, `GStar.reenter` (a VM exit,
  then a kernel run that enters the guest again), `GStar.exit_to_user`.

What the guest does between a VM entry and the next VM exit is not modelled,
as user code is not.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false

namespace GMach

open ClightL Ticket
open LockRegion (RLog REnv)
open LockRegionCPU KernFrame MALOp KMach PUCtxt UMach

/-- The guest registers, as locals of the kernel. -/
def gname : Nat → Ident
  | 0 => "EAX" | 1 => "EBX" | 2 => "EDX" | 3 => "ESI" | 4 => "EDI" | 5 => "EBP" | _ => "RA"

/-- The registers a kernel computation leaves for the guest. -/
def gregsOf (σ : Locals) : Nat → Val := fun n => σ (gname n)

/-- A state of the machine with guest mode. -/
inductive GState
  | kern (s : KState)
  | user (rs : Nat → Val) (pool : Nat → KCtx) (log : RLog)
  /-- guest mode, with the guest's registers -/
  | guest (gr : Nat → Val) (pool : Nat → KCtx) (log : RLog)

/-- One step. `entry n` is the handler of trap `n` and `exitEntry` the VM exit
handler, as indices into `code`; `lk` is the kernel lock. -/
inductive GStep (εR : REnv) (c : CPU) (code : Nat → Stmt KPrim) (entry : Nat → Nat) (exitEntry : Nat) (lk : Val) :
    GState → GState → Prop
  | kern {s s' : KState} (h : kstep εR c code s = some s') : GStep εR c code entry exitEntry lk (.kern s) (.kern s')
  | iret (σ : Locals) (pool : Nat → KCtx) (l : RLog) (hg : σ "GUEST" = 0) :
      GStep εR c code entry exitEntry lk (.kern ⟨⟨.skip, .stop, σ⟩, pool, l⟩) (.user (regsOf σ) pool l)
  | trap (rs : Nat → Val) (pool : Nat → KCtx) (l : RLog) (n : Nat) (σ : Locals) (hlk : σ "lk" = lk) :
      GStep εR c code entry exitEntry lk (.user rs pool l) (.kern ⟨⟨code (entry n), .stop, σ⟩, pool, l⟩)
  | vmentry (σ : Locals) (pool : Nat → KCtx) (l : RLog) (hg : σ "GUEST" ≠ 0) :
      GStep εR c code entry exitEntry lk (.kern ⟨⟨.skip, .stop, σ⟩, pool, l⟩) (.guest (gregsOf σ) pool l)
  | vmexit (gr : Nat → Val) (pool : Nat → KCtx) (l : RLog) (σ : Locals) (hlk : σ "lk" = lk) :
      GStep εR c code entry exitEntry lk (.guest gr pool l) (.kern ⟨⟨code exitEntry, .stop, σ⟩, pool, l⟩)

inductive GStar (εR : REnv) (c : CPU) (code : Nat → Stmt KPrim) (entry : Nat → Nat) (exitEntry : Nat) (lk : Val) :
    GState → GState → Prop
  | refl (s) : GStar εR c code entry exitEntry lk s s
  | step {s s' s''} : GStep εR c code entry exitEntry lk s s' → GStar εR c code entry exitEntry lk s' s'' →
      GStar εR c code entry exitEntry lk s s''

section Lemmas
variable {εR : REnv} {c : CPU} {code : Nat → Stmt KPrim} {entry : Nat → Nat} {exitEntry : Nat} {lk : Val}

theorem GStar.trans {a b d : GState} (h1 : GStar εR c code entry exitEntry lk a b)
    (h2 : GStar εR c code entry exitEntry lk b d) : GStar εR c code entry exitEntry lk a d := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem GStar.single {a b : GState} (h : GStep εR c code entry exitEntry lk a b) :
    GStar εR c code entry exitEntry lk a b :=
  .step h (.refl _)

/-- A run of the kernel machine is a run of the machine with guest mode. -/
theorem GStar.of_kstar {s s' : KState} (h : KStar εR c code s s') :
    GStar εR c code entry exitEntry lk (.kern s) (.kern s') := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.kern h) ih

/-- **A kernel run that ends on an empty stack with `GUEST` set enters the
guest**, with the registers it left. -/
theorem GStar.vmenter {s : KState} {σ : Locals} {pool : Nat → KCtx} {l : RLog}
    (h : KStar εR c code s ⟨⟨.skip, .stop, σ⟩, pool, l⟩) (hg : σ "GUEST" ≠ 0) :
    GStar εR c code entry exitEntry lk (.kern s) (.guest (gregsOf σ) pool l) :=
  (GStar.of_kstar h).trans (.single (.vmentry σ pool l hg))

/-- **A VM exit, then a kernel run that enters the guest again**: from guest
mode back to guest mode. -/
theorem GStar.reenter {gr : Nat → Val} {pool pool' : Nat → KCtx} {l l' : RLog} {σ σ' : Locals}
    (hlk : σ "lk" = lk)
    (h : KStar εR c code ⟨⟨code exitEntry, .stop, σ⟩, pool, l⟩ ⟨⟨.skip, .stop, σ'⟩, pool', l'⟩)
    (hg : σ' "GUEST" ≠ 0) :
    GStar εR c code entry exitEntry lk (.guest gr pool l) (.guest (gregsOf σ') pool' l') :=
  .step (.vmexit gr pool l σ hlk) (GStar.vmenter h hg)

/-- A VM exit, then a kernel run that returns to user mode. -/
theorem GStar.exit_to_user {gr : Nat → Val} {pool pool' : Nat → KCtx} {l l' : RLog} {σ σ' : Locals}
    (hlk : σ "lk" = lk)
    (h : KStar εR c code ⟨⟨code exitEntry, .stop, σ⟩, pool, l⟩ ⟨⟨.skip, .stop, σ'⟩, pool', l'⟩)
    (hg : σ' "GUEST" = 0) :
    GStar εR c code entry exitEntry lk (.guest gr pool l) (.user (regsOf σ') pool' l') :=
  .step (.vmexit gr pool l σ hlk) ((GStar.of_kstar h).trans (.single (.iret σ' pool' l' hg)))

/-- The registers a guest finds at a VM entry are those `vm_run` loaded. -/
theorem gregsOf_eq {σ : Locals} {a bx dx si di bp ip : Val} (h0 : σ "EAX" = a) (h1 : σ "EBX" = bx)
    (h2 : σ "EDX" = dx) (h3 : σ "ESI" = si) (h4 : σ "EDI" = di) (h5 : σ "EBP" = bp) (h6 : σ "RA" = ip) :
    gregsOf σ 0 = a ∧ gregsOf σ 1 = bx ∧ gregsOf σ 2 = dx ∧ gregsOf σ 3 = si ∧ gregsOf σ 4 = di ∧
      gregsOf σ 5 = bp ∧ gregsOf σ 6 = ip :=
  ⟨h0, h1, h2, h3, h4, h5, h6⟩

end Lemmas

end GMach
