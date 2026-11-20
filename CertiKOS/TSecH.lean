import CertiKOS.TDispatchH
import CertiKOS.Integrity

/-!
# Integrity of the hypercalls and of `SYS_print`

The security proof (`Integrity`, `Confidentiality`, `Security`) observes a
process through `Security.observe` on the process layers' state (`UData`):
its address space, its container, its kernel and user contexts. The parts the
top state adds are not observed: the consoles (mCertiKOS observes `devout`;
here it is left out, see `ObsEq`) and the virtual machine.

* `integ_setRegs`, `integ_hcall`: a hypercall writes only the caller's
  registers in the process layers, so **every other process observes the
  same before and after** (mCertiKOS's integrity, for the hypercalls).
* `integ_print`: the same for `SYS_print`.
* `integ_mmap`: the same for `SYS_hvm_mmap`, whose fresh page for the caller
  is none of the observer's pages (as for the page-fault handler).
* `integ_dispatch_h`: **every system call the top state's dispatcher
  handles keeps the observation of every process other than the caller**,
  except `SYS_share`, whose purpose is to change process 2's address space,
  `SYS_recv`, which copies into the caller's buffer (a page the caller may
  share with the observer) and wakes the sender, and `SYS_spawn`, whose
  integrity is `integ_trap_proc_create`. mCertiKOS's security proof is about
  its verified dispatcher (`sys_dispatch_c_spec`), which has no `SYS_recv`.

What this does not say: there is one virtual machine, and, as in mCertiKOS,
any process may make hypercalls. Guests are not isolated from one another,
nor the virtual machine from the processes; only the processes are isolated
from the hypercalls of another.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false

namespace TTop

open Security TTrap PUCtxt MPTOp MPTNew

variable {i : Nat}

theorem integ_setRegs : ∀ (o : List (Nat × Nat)) (u u' : UData), setRegs o u = some u' → i ≠ u.cid →
    ObsEq i u u' ∧ u'.cid = u.cid
  | [], u, u', h, _ => by
    simp only [setRegs, Option.some.injEq] at h; subst h; exact ⟨ObsEq.refl i u, rfl⟩
  | (r, n) :: t, u, u', h, hi => by
    simp only [setRegs] at h
    cases h1 : uctx_set_reg_spec r n u with
    | none => rw [h1] at h; cases h
    | some u1 =>
      rw [h1] at h
      have c1 := Security.set_reg_cid h1
      obtain ⟨o2, c2⟩ := integ_setRegs t u1 u' h (by rw [c1]; exact hi)
      exact ⟨(integ_uctx_set_reg h1 hi).trans o2, c2.trans c1⟩

/-- **A hypercall keeps every other process's observation.** -/
theorem integ_hcall {r : Option (VVMX.XSt × List (Nat × Nat))} {d d' : HData} (h : hcall r d = some d')
    (hi : i ≠ d.cid) : ObsEq i d.toUData d'.toUData := by
  obtain ⟨x, o, u, -, hR, rfl⟩ := hcall_some h
  exact (integ_setRegs o _ u hR hi).1

theorem integ_print {d d' : HData} (h : print_spec d = some d') (hi : i ≠ d.cid) :
    ObsEq i d.toUData d'.toUData := by
  unfold print_spec at h
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at h; cases h
  | some x =>
    cases e0 : uctx_set_errno_spec E_SUCC d.toUData with
    | none => rw [e2, e0] at h; cases h
    | some u =>
      rw [e2, e0] at h; simp only [Option.some.injEq] at h; rw [← h]
      exact integ_uctx_set_reg e0 hi


/-- **`SYS_hvm_mmap` keeps every other process's observation**: the page it
may reserve for the caller is none of the pages the observer maps. -/
theorem integ_mmap {np mp : Nat} {d d' : HData} (hmu : MappedUsed i d.toPTData) (h : trap_mmap_spec np mp d = some d')
    (hi : i ≠ d.cid) : ObsEq i d.toUData d'.toUData := by
  unfold trap_mmap_spec at h
  cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;>
    cases e4 : uctx_arg4_spec d.toUData <;> simp only [e2, e3, e4] at h <;> try cases h
  split at h
  · cases hp : ptRead_spec np d.cid _ d.toPTData with
    | none => rw [hp] at h; cases h
    | some hpa =>
      rw [hp] at h; simp only at h
      split at h
      · cases hr : ptResv_spec mp np d.cid _ 7 d.toPTData with
        | none => rw [hr] at h; cases h
        | some pr =>
          obtain ⟨p0, r⟩ := pr
          rw [hr] at h; simp only at h
          cases hp' : ptRead_spec np d.cid _ p0 with
          | none => rw [hp'] at h; cases h
          | some hpa' =>
            rw [hp'] at h; simp only at h; unfold mmapTail at h
            have h1 : ObsEq i d.toUData ({ d with toPTData := p0 } : HData).toUData := by
              have hf := ptResv_frame hr
              refine ObsEq.inactive hi hi (hf.other i hi).1 (fun v pte pi pm h1 w h2 => ?_) (hf.other i hi).2 rfl rfl
              obtain ⟨a1, a2, -⟩ := hf.used w (hmu _ pi pte h1 _ w pm h2)
              exact ⟨a2 _ (by omega), a1⟩
            exact h1.trans (integ_hcall (d := ({ d with toPTData := p0 } : HData)) h hi)
      · unfold mmapTail at h; exact integ_hcall h hi
  · exact integ_hcall h hi

/-- **Every call of the dispatcher's table but `SYS_share` and `SYS_recv` keeps every other
process's observation.** -/
theorem integ_dispatch_h {np mp nc a : Nat} {d d' : HData} (ha : a ≠ 27) (hr : a ≠ 9)
    (hmu : MappedUsed i d.toPTData) (h : chainF (hspecs np mp nc) a d = some d') (hi : i ≠ d.cid) : ObsEq i d.toUData d'.toUData := by
  have H : ∀ (f : HData → Option HData), (∀ d d', f d = some d' → i ≠ d.cid → ObsEq i d.toUData d'.toUData) →
      ∀ d d', f d = some d' → i ≠ d.cid → ObsEq i d.toUData d'.toUData := fun f hf => hf
  simp only [hspecs, chainF] at h
  by_cases e22 : a = 22
  · rw [if_pos e22] at h; unfold trap_get_tsc_offset_spec at h; exact integ_hcall h hi
  rw [if_neg e22] at h
  by_cases e23 : a = 23
  · rw [if_pos e23] at h; unfold trap_set_tsc_offset_spec at h
    cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;> simp only [e2, e3] at h
    all_goals first | exact integ_hcall h hi | cases h
  rw [if_neg e23] at h
  by_cases e12 : a = 12
  · rw [if_pos e12] at h; unfold trap_get_exitinfo_spec at h; exact integ_hcall h hi
  rw [if_neg e12] at h
  by_cases e15 : a = 15
  · rw [if_pos e15] at h; unfold trap_set_reg_spec at h
    cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;> simp only [e2, e3] at h
    all_goals first | exact integ_hcall h hi | cases h
  rw [if_neg e15] at h
  by_cases e16 : a = 16
  · rw [if_pos e16] at h; unfold trap_get_reg_spec at h
    cases e2 : uctx_arg2_spec d.toUData <;> simp only [e2] at h
    all_goals first | exact integ_hcall h hi | cases h
  rw [if_neg e16] at h
  by_cases e14 : a = 14
  · rw [if_pos e14] at h; unfold trap_set_seg_spec at h
    cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;>
      cases e4 : uctx_arg4_spec d.toUData <;> cases e5 : uctx_arg5_spec d.toUData <;>
      cases e6 : uctx_arg6_spec d.toUData <;> simp only [e2, e3, e4, e5, e6] at h
    all_goals first | exact integ_hcall h hi | cases h
  rw [if_neg e14] at h
  by_cases e17 : a = 17
  · rw [if_pos e17] at h; unfold trap_get_next_eip_spec at h; exact integ_hcall h hi
  rw [if_neg e17] at h
  by_cases e18 : a = 18
  · rw [if_pos e18] at h; unfold trap_inject_event_spec at h
    cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;>
      cases e4 : uctx_arg4_spec d.toUData <;> cases e5 : uctx_arg5_spec d.toUData <;>
      simp only [e2, e3, e4, e5] at h
    all_goals first | exact integ_hcall h hi | cases h
  rw [if_neg e18] at h
  by_cases e20 : a = 20
  · rw [if_pos e20] at h; unfold trap_check_pending_event_spec at h; exact integ_hcall h hi
  rw [if_neg e20] at h
  by_cases e19 : a = 19
  · rw [if_pos e19] at h; unfold trap_check_int_shadow_spec at h; exact integ_hcall h hi
  rw [if_neg e19] at h
  by_cases e21 : a = 21
  · rw [if_pos e21] at h; unfold trap_intercept_int_window_spec at h
    cases e2 : uctx_arg2_spec d.toUData <;> simp only [e2] at h
    all_goals first | exact integ_hcall h hi | cases h
  rw [if_neg e21] at h
  by_cases e24 : a = 24
  · rw [if_pos e24] at h; unfold trap_handle_rdmsr_spec at h; exact integ_hcall h hi
  rw [if_neg e24] at h
  by_cases e13 : a = 13
  · rw [if_pos e13] at h; exact integ_mmap hmu h hi
  rw [if_neg e13] at h
  by_cases e25 : a = 25
  · rw [if_pos e25] at h; unfold trap_handle_wrmsr_spec at h; exact integ_hcall h hi
  rw [if_neg e25] at h
  by_cases e26 : a = 26
  · rw [if_pos e26] at h; unfold onU at h
    cases hq : trap_get_quota_spec d.toUData with
    | none => rw [hq] at h; cases h
    | some u => rw [hq] at h; simp only [Option.some.injEq] at h; rw [← h]; exact integ_trap_get_quota hq hi
  rw [if_neg e26] at h
  rw [if_neg hr] at h
  rw [if_neg ha] at h
  by_cases e28 : a = 28
  · rw [if_pos e28] at h; exact integ_print h hi
  rw [if_neg e28] at h
  exact integ_hcall h hi

end TTop
