import CertiKOS.TSecH
import CertiKOS.TRunVM

/-!
# Isolation around the guest

* `integ_run_vm`: entering the guest (`SYS_hvm_run_vm`) keeps every other
  process's observation: it changes only the virtual machine and the mode
  flag, which another process does not see.
* `integ_vm_exit`: so does the VM exit handler, which also writes the
  caller's error code.
* `integ_visit`: **a whole visit to the guest, from `SYS_hvm_run_vm` to the
  return to the caller, keeps every other process's observation.**

What is not covered: what the guest does while it runs is not modelled (as
user code is not); the guest's memory is the caller's pages (`SYS_hvm_mmap`
maps only pages from the caller's page table), so a guest that writes it
changes what the caller, and a process it shares a page with, observe. There
is one virtual machine, and any process may make hypercalls, as in mCertiKOS.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false

namespace TTop

open ClightL Security TTrap PUCtxt

variable {i : Nat}

theorem integ_run_vm {r1 r2 : Val} {d d' : HData} (h : run_vm_spec r1 r2 d = some d') (hi : i ≠ d.cid) :
    ObsEq i d.toUData d'.toUData := by
  unfold run_vm_spec at h
  cases hx : VVMX.vm_run_spec r1 r2 (toX d) with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h; simp only [Option.some.injEq] at h; subst h
    exact ObsEq.inactive_same hi hi rfl rfl rfl rfl rfl rfl

theorem integ_vm_exit {a b c' dx si bp : Val} {d d' : HData} (h : exit_spec a b c' dx si bp d = some d')
    (hi : i ≠ d.cid) : ObsEq i d.toUData d'.toUData := by
  unfold exit_spec at h
  cases hx : VVMX.vmx_return_from_guest_spec a b c' dx si bp (toX d) with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h; simp only at h
    have h1 : ObsEq i d.toUData ({ d with ihost := true } : HData).toUData :=
      ObsEq.inactive_same hi hi rfl rfl rfl rfl rfl rfl
    exact h1.trans (integ_hcall (d := ({ d with ihost := true } : HData)) h hi)

/-- **A visit to the guest keeps every other process's observation.** -/
theorem integ_visit {r1 r2 a b c' dx si bp : Val} {d d1 d' : HData} (h1 : run_vm_spec r1 r2 d = some d1)
    (h2 : exit_spec a b c' dx si bp d1 = some d') (hi : i ≠ d.cid) : ObsEq i d.toUData d'.toUData := by
  have o1 := integ_run_vm h1 hi
  have hc : d1.cid = d.cid := by
    unfold run_vm_spec at h1
    cases hx : VVMX.vm_run_spec r1 r2 (toX d) with
    | none => rw [hx] at h1; cases h1
    | some x => rw [hx] at h1; simp only [Option.some.injEq] at h1; subst h1; rfl
  exact o1.trans (integ_vm_exit h2 (by rw [hc]; exact hi))

end TTop
