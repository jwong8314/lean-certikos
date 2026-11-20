import CertiKOS.KMachine
import CertiKOS.PThreadSched

/-!
# mCertiKOS `PKContext`: kernel contexts, ported

Ported from `objects/ObjThread.v`: `kctxt_ra_spec`, `kctxt_sp_spec`,
`kctxt_switch_spec`. They keep their shape. What changes is the type of a
kernel context: mCertiKOS's is a set of saved registers, here it is a
suspended computation (`KMachine.lean`). The specifications never look
inside one, except that `kctxt_sp_spec` and `kctxt_ra_spec` set its stack and
its entry point.

* `KData`: `CData` with the pool of kernel contexts.
* `kctxt_switch_refines`, `kctxt_sp_refines`, `kctxt_ra_refines`: **the
  machine's three calls refine the three specifications.** For the switch
  the context handed to the specification is the running computation, about
  to return `0` from the call. mCertiKOS proves this of twenty assembly
  instructions; here the switch is one step of the machine, so the proof is
  short and the trust is in `kstep`.

What differs: the entry point given to `set_RA` is a number looked up in the
machine's text `code`, not a block and an offset.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PKCtx

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID KMach
open MALInit (tn)

/-- `CData` with the kernel contexts. -/
structure KData extends CData where
  kctxt : Nat → KCtx

section Specs
variable (num_proc : Nat)

/-- `kctxt_ra_spec`: context `n` starts at function `f`. -/
def kctxt_ra_spec (code : Nat → Stmt KPrim) (n f : Nat) (d : KData) : Option KData :=
  if d.pg = true ∧ d.ipt = true ∧ 0 < n ∧ n < num_proc then
    some { d with kctxt := setAt d.kctxt n { d.kctxt n with stmt := code f } }
  else none

/-- `kctxt_sp_spec`: context `n` gets an empty stack. -/
def kctxt_sp_spec (n : Nat) (d : KData) : Option KData :=
  if d.pg = true ∧ d.ipt = true ∧ 0 < n ∧ n < num_proc then
    some { d with kctxt := setAt d.kctxt n { d.kctxt n with cont := .stop } }
  else none

/-- **`kctxt_switch_spec`**: the context `rs` that was running is stored in
slot `n`, and the context of slot `n'` is returned to run. -/
def kctxt_switch_spec (n n' : Nat) (rs : KCtx) (d : KData) : Option (KData × KCtx) :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_proc ∧ n' < num_proc then
    if n = n' then none else some ({ d with kctxt := setAt d.kctxt n rs }, d.kctxt n')
  else none

end Specs

section Refines
variable {num_proc : Nat} {εR : REnv} {c : CPU} {code : Nat → Stmt KPrim}

/-- **`cswitch` refines `kctxt_switch_spec`.** -/
theorem kctxt_switch_refines {d d' : KData} {rs' : KCtx} {x : Ident} {e1 e2 : Expr} {K : Cont KPrim}
    {σ : Locals} {l : RLog} {n n' : Nat} (h1 : e1.eval σ = BitVec.ofNat 32 n)
    (h2 : e2.eval σ = BitVec.ofNat 32 n') (hn : n < 2 ^ 32) (hn' : n' < 2 ^ 32)
    (hs : kctxt_switch_spec num_proc n n' ⟨.skip, K, σ.set x 0⟩ d = some (d', rs')) :
    kstep εR c code ⟨⟨.call x .cswitch [e1, e2], K, σ⟩, d.kctxt, l⟩ = some ⟨rs', d'.kctxt, l⟩ := by
  unfold kctxt_switch_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_proc ∧ n' < num_proc
  · rw [if_pos hc] at hs
    by_cases e : n = n'
    · rw [if_pos e] at hs; cases hs
    · rw [if_neg e] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨hd, hr⟩ := hs
      subst hd; subst hr
      rw [kstep_cswitch, h1, h2, tn hn, tn hn', setAt_ne _ _ (fun e' => e e'.symm)]
  · rw [if_neg hc] at hs; cases hs

/-- **`set_SP` refines `kctxt_sp_spec`.** -/
theorem kctxt_sp_refines {d d' : KData} {x : Ident} {e1 : Expr} {K : Cont KPrim} {σ : Locals} {l : RLog}
    {n : Nat} (h1 : e1.eval σ = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (hs : kctxt_sp_spec num_proc n d = some d') :
    kstep εR c code ⟨⟨.call x .setSP [e1], K, σ⟩, d.kctxt, l⟩ = some ⟨⟨.skip, K, σ.set x 0⟩, d'.kctxt, l⟩ := by
  unfold kctxt_sp_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ 0 < n ∧ n < num_proc
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    rw [kstep_setSP, h1, tn hn]
  · rw [if_neg hc] at hs; cases hs

/-- **`set_RA` refines `kctxt_ra_spec`.** -/
theorem kctxt_ra_refines {d d' : KData} {x : Ident} {e1 e2 : Expr} {K : Cont KPrim} {σ : Locals} {l : RLog}
    {n f : Nat} (h1 : e1.eval σ = BitVec.ofNat 32 n) (h2 : e2.eval σ = BitVec.ofNat 32 f) (hn : n < 2 ^ 32)
    (hf : f < 2 ^ 32) (hs : kctxt_ra_spec num_proc code n f d = some d') :
    kstep εR c code ⟨⟨.call x .setRA [e1, e2], K, σ⟩, d.kctxt, l⟩ =
      some ⟨⟨.skip, K, σ.set x 0⟩, d'.kctxt, l⟩ := by
  unfold kctxt_ra_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ 0 < n ∧ n < num_proc
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    rw [kstep_setRA, h1, h2, tn hn, tn hf]
  · rw [if_neg hc] at hs; cases hs

end Refines

end PKCtx
