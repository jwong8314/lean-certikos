import CertiKOS.THyp3

/-!
# The system-call dispatcher on the top state

mCertiKOS has two dispatchers that do not agree: the verified specification
`sys_dispatch_c_spec` (`objects/ObjTrap.v`) handles `SYS_spawn`,
`SYS_get_quota`, `SYS_share` and `SYS_print`; the C file
`trap/syscall_dispatch_c.c` handles `SYS_spawn`, `SYS_get_quota`,
`SYS_recv` and the hypercalls (`SYS_hvm_*`). This dispatcher handles the
union, in the C file's order, with `SYS_share` and `SYS_print` last:

| number | call | handler |
|---|---|---|
| 2 | `SYS_spawn` | `sys_proc_create` (`TDispatch`) |
| 22, 23 | `SYS_hvm_get_tsc_offset`, `SYS_hvm_set_tsc_offset` | `THyp` |
| 12 | `SYS_hvm_get_exitinfo` | `THyp2` |
| 15, 16, 14 | `SYS_hvm_set_reg`, `SYS_hvm_get_reg`, `SYS_hvm_set_seg` | `THyp` |
| 17, 18, 20, 19, 21 | next eip, inject event, pending event, interrupt shadow, interrupt window | `THyp` |
| 24, 25 | `SYS_hvm_handle_rdmsr`, `SYS_hvm_handle_wrmsr` | `THyp2` |
| 26 | `SYS_get_quota` | `TTrap` |
| 9 | `SYS_recv` | `sys_receive_chan` (`TTrap`) |
| 27 | `SYS_share` | `TShare` |
| 28 | `SYS_print` | `TTop` |
| other | | `E_INVAL_CALLNR` |

* `chainS`, `chainF`: a list of (number, handler), as code and as
  specification. `chain_triple`: **if each handler refines its
  specification, the chain does.**
* `liftUT`: a triple of the process layers holds in the top state.
* `sysDispatchH_run`: **`syscall_dispatch_c` on the kernel machine does what
  `sys_dispatch_h_spec` says**, for every number.

`SYS_hvm_mmap` (13) is dispatched after `SYS_hvm_handle_rdmsr`, as in the C
file. Not dispatched: `SYS_hvm_run_vm` (entering the guest is a transition of
the machine, `TRunVM`).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace TTop

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt UMach MCPU PProc FlatMem TTrap
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)
open VVMX (XSt MatchX XF)

/-! ## The chain of tests -/

def chainS (cidb ucb : Nat) : List (Nat × Stmt APrim) → Stmt APrim
  | [] => errS cidb ucb 3
  | (n, s) :: t => .ite (.bin .eq (.var "arg1") (.const (BitVec.ofNat 32 n))) s (chainS cidb ucb t)

def chainF : List (Nat × (HData → Option HData)) → Nat → HData → Option HData
  | [], _, d => hcall (some (toX d, [(U_EAX, E_INVAL_CALLNR)])) d
  | (n, f) :: t, a, d => if a = n then f d else chainF t a d

/-- A specification of the process layers, on the top state. -/
def onU (f : UData → Option UData) (d : HData) : Option HData :=
  match f d.toUData with
  | some u => some { d with toUData := u }
  | none => none

section Dispatch
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb
local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- Every cell a dispatched call may write. -/
def DF (cb num_id pb sb num_proc ucb ob xb vb eb tb qb num_chan ipb fb : Nat) (k : Nat) : Prop :=
  ShareF cb num_id pb sb num_proc k ∨ UCF ucb num_proc k ∨ OF ob num_proc k ∨ XF xb vb eb k ∨
    RecvF tb num_proc qb num_chan ipb fb k

/-- **The chain refines its specification.** -/
theorem chain_triple (hL : HL) {F : Nat → Prop} (hUF : ∀ k, HF ucb num_proc xb vb eb k → F k) (Pre : HData → Prop)
    (hPre : ∀ d, Pre d → d.cid < num_proc) :
    ∀ (l : List (Nat × Stmt APrim × (HData → Option HData))) (a : Nat),
    (∀ p ∈ l, p.1 < 2 ^ 32 ∧ Triple εR c i0 MH F (fun _ d => Pre d ∧ ∃ d1, p.2.2 d = some d1) p.2.1
      (fun _ d _ d' => p.2.2 d = some d')) →
    Triple εR c i0 MH F
      (fun σ d => σ "arg1" = BitVec.ofNat 32 a ∧ a < 2 ^ 32 ∧ Pre d ∧
        ∃ d1, chainF (l.map fun p => (p.1, p.2.2)) a d = some d1)
      (chainS cidb ucb (l.map fun p => (p.1, p.2.1)))
      (fun _ d _ d' => chainF (l.map fun p => (p.1, p.2.2)) a d = some d')
  | [], a, _ => by
    refine Step.triple (fun σ d ⟨_, _, hp, d1, hs⟩ => ?_)
    have hs0 := hs
    simp only [List.map, chainF] at hs
    obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨σ', S⟩ := errH (ida := ida) εR c i0 hL (σ := σ) (d := putX d (toX d)) (hPre d hp) hR
    exact ⟨σ', _, S.widen hUF, hs0⟩
  | (n, s, f) :: t, a, hl => by
    intro σ l b d hlk hcs hM ⟨ha, ha32, hp, d1, hs⟩
    obtain ⟨hn32, T⟩ := hl (n, s, f) (List.mem_cons_self ..)
    simp only [List.map, chainF] at hs
    by_cases e : a = n
    · rw [if_pos e] at hs
      obtain ⟨σ', l', b', d', r, c', m', k', fr, q⟩ := T σ l b d hlk hcs hM ⟨hp, d1, hs⟩
      refine ⟨σ', l', b', d', Runs.ite_true (eqc_true ha e) r, c', m', k', fr, ?_⟩
      simp only [List.map, chainF]; rw [if_pos e]; exact q
    · rw [if_neg e] at hs
      obtain ⟨σ', l', b', d', r, c', m', k', fr, q⟩ := chain_triple hL hUF Pre hPre t a
        (fun p hm => hl p (List.mem_cons_of_mem _ hm)) σ l b d hlk hcs hM ⟨ha, ha32, hp, d1, hs⟩
      refine ⟨σ', l', b', d', Runs.ite_false (eqc_false ha ha32 hn32 e) r, c', m', k', fr, ?_⟩
      simp only [List.map, chainF]; rw [if_neg e]; exact q

end Dispatch

/-! ## The dispatcher -/

/-- The handlers after `SYS_spawn`, with their specifications. -/
def hlist (cb maxpage pb fb sb num_proc cidb ucb ob xb vb eb tb qb ipb num_chan : Nat) :
    List (Nat × Stmt APrim × (HData → Option HData)) :=
  [(22, getTscH cidb ucb vb, trap_get_tsc_offset_spec),
   (23, setTscH cidb ucb vb, trap_set_tsc_offset_spec),
   (12, getExitinfoH cidb ucb xb vb, trap_get_exitinfo_spec),
   (15, setRegH cidb ucb xb vb, trap_set_reg_spec),
   (16, getRegH cidb ucb xb vb, trap_get_reg_spec),
   (14, setSegH cidb ucb vb, trap_set_seg_spec),
   (17, getNextEipH cidb ucb xb vb, trap_get_next_eip_spec),
   (18, injectH cidb ucb vb, trap_inject_event_spec),
   (20, checkPendingH cidb ucb vb, trap_check_pending_event_spec),
   (19, checkIntShadowH cidb ucb vb, trap_check_int_shadow_spec),
   (21, interceptH cidb ucb vb, trap_intercept_int_window_spec),
   (24, rdmsrH cidb ucb xb vb, trap_handle_rdmsr_spec),
   (13, mmapH cb maxpage pb fb cidb ucb eb, trap_mmap_spec num_proc maxpage),
   (25, wrmsrH cidb ucb xb vb, trap_handle_wrmsr_spec),
   (26, trapGetQuotaS cb cidb ucb, onU trap_get_quota_spec),
   (9, trapReceiveS tb qb cidb pb fb ipb ucb num_proc num_chan, onU (trap_receivechan_spec num_proc num_chan)),
   (27, trapShareS cb maxpage pb fb sb num_proc cidb ucb, onU (trap_offer_shared_mem_spec num_proc maxpage)),
   (28, printS cidb ucb ob, print_spec)]

/-- The specifications alone. -/
def hspecs (num_proc maxpage num_chan : Nat) : List (Nat × (HData → Option HData)) :=
  [(22, trap_get_tsc_offset_spec), (23, trap_set_tsc_offset_spec), (12, trap_get_exitinfo_spec),
   (15, trap_set_reg_spec), (16, trap_get_reg_spec), (14, trap_set_seg_spec), (17, trap_get_next_eip_spec),
   (18, trap_inject_event_spec), (20, trap_check_pending_event_spec), (19, trap_check_int_shadow_spec),
   (21, trap_intercept_int_window_spec), (24, trap_handle_rdmsr_spec), (13, trap_mmap_spec num_proc maxpage),
   (25, trap_handle_wrmsr_spec),
   (26, onU trap_get_quota_spec), (9, onU (trap_receivechan_spec num_proc num_chan)), (27, onU (trap_offer_shared_mem_spec num_proc maxpage)), (28, print_spec)]

theorem hlist_specs (cb maxpage pb fb sb num_proc cidb ucb ob xb vb eb tb qb ipb num_chan : Nat) :
    (hlist cb maxpage pb fb sb num_proc cidb ucb ob xb vb eb tb qb ipb num_chan).map (fun p => (p.1, p.2.2)) =
      hspecs num_proc maxpage num_chan :=
  rfl

/-- **`sys_dispatch_h_spec`**: argument 1 is the system-call number. -/
def sys_dispatch_h_spec (num_id mc num_chan num_proc maxpage : Nat) (code : Nat → Stmt KPrim) (pstart : Nat)
    (elf : Nat → Nat) (d : HData) : Option HData :=
  match uctx_arg1_spec d.toUData with
  | some a =>
    if a = 2 then onU (trap_proc_create_spec num_id mc num_chan code pstart elf) d
    else chainF (hspecs num_proc maxpage num_chan) a d
  | none => none

/-- `syscall_dispatch_c`:
```
arg1 = uctx_arg1();
if (arg1 == SYS_spawn) sys_proc_create();
else if (arg1 == SYS_hvm_get_tsc_offset) sys_get_tsc_offset();
… (the table above)
else uctx_set_errno(E_INVAL_CALLNR);
``` -/
def sysDispatchHK (cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart maxpage pb fb sb ob xb vb eb ipb : Nat) :
    Stmt KPrim :=
  .seq (mapS .base (uctxArgS cidb ucb "arg1" U_EAX))
    (.ite (.bin .eq (.var "arg1") (.const 2))
      (sysProcCreateK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart)
      (mapS .base (chainS cidb ucb ((hlist cb maxpage pb fb sb num_proc cidb ucb ob xb vb eb tb qb ipb num_chan).map
        fun p => (p.1, p.2.1)))))


/-! ## The handlers keep the kernel contexts -/

theorem setRegs_kctxt : ∀ (o : List (Nat × Nat)) (u u' : UData), setRegs o u = some u' → u'.kctxt = u.kctxt
  | [], u, u', h => by simp only [setRegs, Option.some.injEq] at h; rw [h]
  | (r, n) :: t, u, u', h => by
    simp only [setRegs] at h
    cases h1 : uctx_set_reg_spec r n u with
    | none => rw [h1] at h; cases h
    | some u1 =>
      rw [h1] at h
      obtain ⟨U, e⟩ := set_reg_shape h1
      rw [setRegs_kctxt t u1 u' h, e]

theorem hcall_kctxt {r : Option (XSt × List (Nat × Nat))} {d d' : HData} (h : hcall r d = some d') :
    d'.kctxt = d.kctxt := by
  obtain ⟨x, o, u, -, hR, rfl⟩ := hcall_some h
  exact setRegs_kctxt o _ u hR

theorem share_kctxt {np mp : Nat} {u u' : UData} (h : trap_offer_shared_mem_spec np mp u = some u') :
    u'.kctxt = u.kctxt := by
  unfold trap_offer_shared_mem_spec at h
  cases e2 : uctx_arg2_spec u with
  | none => rw [e2] at h; cases h
  | some va =>
    rw [e2] at h; simp only at h
    by_cases c1 : u.cid = 1
    · rw [if_pos c1] at h
      cases ho : offer_shared_mem_spec np mp 1 2 va u.toSData with
      | none => rw [ho] at h; cases h
      | some pr =>
        obtain ⟨s', r⟩ := pr
        rw [ho] at h; simp only at h
        cases h1 : uctx_set_retval1_spec r { u with toSData := s' } with
        | none => rw [h1] at h; cases h
        | some u1 =>
          rw [h1] at h; simp only at h
          obtain ⟨U, e⟩ := set_reg_shape h
          obtain ⟨U1, e1⟩ := set_reg_shape h1
          rw [e, e1]
    · rw [if_neg c1] at h
      obtain ⟨U, e⟩ := set_reg_shape h
      rw [e]

theorem recv_kctxt {np nc : Nat} {u u' : UData} (h : trap_receivechan_spec np nc u = some u') :
    u'.kctxt = u.kctxt := by
  unfold trap_receivechan_spec at h
  cases e2 : uctx_arg2_spec u <;> cases e3 : uctx_arg3_spec u <;> cases e4 : uctx_arg4_spec u <;>
    simp only [e2, e3, e4] at h <;> try cases h
  cases hr : syncreceive_chan_spec np nc _ _ _ u.toIData with
  | none => rw [hr] at h; cases h
  | some pr =>
    obtain ⟨i1, r⟩ := pr
    rw [hr] at h; simp only at h
    cases h1 : uctx_set_retval1_spec r { u with toIData := i1 } with
    | none => rw [h1] at h; cases h
    | some u1 =>
      rw [h1] at h; simp only at h
      obtain ⟨U, e⟩ := set_reg_shape h
      obtain ⟨U1, e1⟩ := set_reg_shape h1
      rw [e, e1]

theorem onU_kctxt {f : UData → Option UData} (hf : ∀ u u', f u = some u' → u'.kctxt = u.kctxt) {d d' : HData}
    (h : onU f d = some d') : d'.kctxt = d.kctxt := by
  unfold onU at h
  cases hu : f d.toUData with
  | none => rw [hu] at h; cases h
  | some u => rw [hu] at h; simp only [Option.some.injEq] at h; rw [← h]; exact hf _ _ hu

theorem print_kctxt {d d' : HData} (h : print_spec d = some d') : d'.kctxt = d.kctxt := by
  unfold print_spec at h
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at h; cases h
  | some x =>
    cases e0 : uctx_set_errno_spec E_SUCC d.toUData with
    | none => rw [e2, e0] at h; cases h
    | some u =>
      rw [e2, e0] at h; simp only [Option.some.injEq] at h; rw [← h]
      obtain ⟨U, e⟩ := set_reg_shape e0; rw [e]


theorem mmap_kctxt {np mp : Nat} {d d' : HData} (h : trap_mmap_spec np mp d = some d') : d'.kctxt = d.kctxt := by
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
          | some hpa' => rw [hp'] at h; simp only at h; unfold mmapTail at h; have := hcall_kctxt h; exact this
      · unfold mmapTail at h; exact hcall_kctxt h
  · exact hcall_kctxt h

theorem chainF_kctxt : ∀ (l : List (Nat × (HData → Option HData))) (a : Nat) (d d' : HData),
    (∀ p ∈ l, ∀ d d', p.2 d = some d' → d'.kctxt = d.kctxt) → chainF l a d = some d' → d'.kctxt = d.kctxt
  | [], a, d, d', _, h => hcall_kctxt h
  | (n, f) :: t, a, d, d', hl, h => by
    simp only [chainF] at h
    by_cases e : a = n
    · rw [if_pos e] at h; exact hl (n, f) (List.mem_cons_self ..) d d' h
    · rw [if_neg e] at h; exact chainF_kctxt t a d d' (fun p hm => hl p (List.mem_cons_of_mem _ hm)) h

theorem chain_kctxt {np mp nc a : Nat} {d d' : HData} (h : chainF (hspecs np mp nc) a d = some d') :
    d'.kctxt = d.kctxt := by
  refine chainF_kctxt _ a d d' (fun p hm => ?_) h
  simp only [hspecs, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro d d' h; unfold trap_get_tsc_offset_spec at h; (repeat' (split at h)) <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_set_tsc_offset_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> simp only [e0, e1] at h <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_get_exitinfo_spec at h; (repeat' (split at h)) <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_set_reg_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> simp only [e0, e1] at h <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_get_reg_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> simp only [e0] at h <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_set_seg_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> cases e2 : uctx_arg4_spec d.toUData <;> cases e3 : uctx_arg5_spec d.toUData <;> cases e4 : uctx_arg6_spec d.toUData <;> simp only [e0, e1, e2, e3, e4] at h <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_get_next_eip_spec at h; (repeat' (split at h)) <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_inject_event_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> cases e2 : uctx_arg4_spec d.toUData <;> cases e3 : uctx_arg5_spec d.toUData <;> simp only [e0, e1, e2, e3] at h <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_check_pending_event_spec at h; (repeat' (split at h)) <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_check_int_shadow_spec at h; (repeat' (split at h)) <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_intercept_int_window_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> simp only [e0] at h <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; unfold trap_handle_rdmsr_spec at h; (repeat' (split at h)) <;> first | exact hcall_kctxt h | cases h
  · intro d d' h; exact mmap_kctxt h
  · intro d d' h; unfold trap_handle_wrmsr_spec at h; (repeat' (split at h)) <;> first | exact hcall_kctxt h | cases h
  · exact fun d d' h => onU_kctxt (fun u u' hu => by obtain ⟨U, e⟩ := get_quota_shape hu; rw [e]) h
  · exact fun d d' h => onU_kctxt (fun u u' hu => recv_kctxt hu) h
  · exact fun d d' h => onU_kctxt (fun u u' hu => share_kctxt hu) h
  · exact fun d d' h => print_kctxt h

section Run
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb
local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- What every handler after `SYS_spawn` may assume. -/
def DPre (maxpage num_id num_proc num_chan kl kh : Nat) (d : HData) : Prop :=
  d.cid < num_proc ∧ d.cid < num_id ∧ (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota ∧
    ATInv maxpage kl kh d.toPData ∧ UQ d.AC ∧ AInv num_proc num_chan d.toAData

/-- **Each handler of the table refines its specification.** -/
theorem hlist_triples (hL : HL) (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32)
    (hmp : maxpage ≤ 2 ^ 20) (hnn : num_proc ≤ num_id) (hnpc : num_proc ≤ num_chan) {kl kh : Nat} :
    ∀ p ∈ hlist cb maxpage pb fb sb num_proc cidb ucb ob xb vb eb tb qb ipb num_chan, p.1 < 2 ^ 32 ∧
      Triple εR c i0 MH (DF cb num_id pb sb num_proc ucb ob xb vb eb tb qb num_chan ipb fb)
        (fun _ d => DPre maxpage num_id num_proc num_chan kl kh d ∧ ∃ d1, p.2.2 d = some d1) p.2.1
        (fun _ d _ d' => p.2.2 d = some d') := by
  have hU := hL.ulay
  have wH : ∀ k, HF ucb num_proc xb vb eb k → DF cb num_id pb sb num_proc ucb ob xb vb eb tb qb num_chan ipb fb k :=
    fun k hk => hk.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))
  have pre : ∀ (f : HData → Option HData) (σ : Locals) (d : HData),
      (DPre maxpage num_id num_proc num_chan kl kh d ∧ ∃ d1, f d = some d1) → d.cid < num_proc ∧ ∃ d1, f d = some d1 :=
    fun f σ d h => ⟨h.1.1, h.2⟩
  have H := fun {s : Stmt APrim} {f : HData → Option HData}
      (T : Triple εR c i0 MH (HF ucb num_proc xb vb eb) (fun _ d => d.cid < num_proc ∧ ∃ d1, f d = some d1) s
        (fun _ d _ d' => f d = some d')) =>
    (T.widen wH).conseq (pre f) (fun _ _ _ _ _ h => h)
  intro p hm
  simp only [hlist, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by dsimp only; decide, H (getTsc_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (setTsc_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (getExitinfo_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (setReg_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (getReg_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (setSeg_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (getNextEip_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (inject_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (checkPending_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (checkIntShadow_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (intercept_triple (ida := ida) εR c i0 hL)⟩
  · exact ⟨by dsimp only; decide, H (rdmsr_triple (ida := ida) εR c i0 hL)⟩
  · refine ⟨by dsimp only; decide, ((mmap_triple (ida := ida) εR c i0 hL hmax hnum hmp hnn (kl := kl) (kh := kh)).widen
      (fun k hk => hk.elim (fun h => Or.inl (Or.inl h)) (fun h => wH k h))).conseq
      (fun σ d ⟨hp, d1, hs⟩ => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, d1, hs⟩) (fun _ _ _ _ _ h => h)⟩
  · exact ⟨by dsimp only; decide, H (wrmsr_triple (ida := ida) εR c i0 hL)⟩
  · refine ⟨by dsimp only; decide, ?_⟩
    have := hL.hob
    have T := liftUT (ida := ida) (ob := ob) (xb := xb) (vb := vb) (eb := eb) εR c i0 hL
      (trapGetQuota_triple (ida := ida) εR c i0 hU hnum) (fun k hk => by unfold UCF at hk; omega)
    refine (T.widen (fun k hk => Or.inr (Or.inl hk))).conseq (fun σ d ⟨hp, d1, hs⟩ => ?_) (fun σ d σ' d' _ hq => ?_)
    · have hs' : onU trap_get_quota_spec d = some d1 := hs
      unfold onU at hs'
      cases hq : trap_get_quota_spec d.toUData with
      | none => rw [hq] at hs'; cases hs'
      | some u => exact ⟨hp.1, hp.2.1, hp.2.2.1, u, by first | exact hq | rfl⟩
    · obtain ⟨u, rfl, hu⟩ := hq
      show onU trap_get_quota_spec d = _
      unfold onU; rw [hu]
  · refine ⟨by dsimp only; decide, ?_⟩
    have := hL.hob; have := hU.hub0; have := hU.ilay.hib0; have := hU.ilay.clay.hcb
    have := hU.ilay.clay.qlay.hqb; have := hU.ilay.clay.qlay.tlay.slay.lay.hib
    have := hU.ilay.clay.qlay.tlay.slay.lay.hfb
    have T := liftUT (ida := ida) (ob := ob) (xb := xb) (vb := vb) (eb := eb) εR c i0 hL
      (trapReceive_triple (ida := ida) εR c i0 hU hnpc)
      (fun k hk => by
        rcases hk with ((⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) | h1) | ⟨h1, h2⟩ <;> omega)
    refine (T.widen (fun k hk => hk.elim (fun h => Or.inr (Or.inr (Or.inr (Or.inr h))))
      (fun h => Or.inr (Or.inl h)))).conseq (fun σ d ⟨hp, d1, hs⟩ => ?_) (fun σ d σ' d' _ hq => ?_)
    · have hs' : onU (trap_receivechan_spec num_proc num_chan) d = some d1 := hs
      unfold onU at hs'
      cases hq : trap_receivechan_spec num_proc num_chan d.toUData with
      | none => rw [hq] at hs'; cases hs'
      | some u => exact ⟨hp.1, hp.2.2.2.2.2, u, by first | exact hq | rfl⟩
    · obtain ⟨u, rfl, hu⟩ := hq
      show onU (trap_receivechan_spec num_proc num_chan) d = _
      unfold onU; rw [hu]
  · refine ⟨by dsimp only; decide, ?_⟩
    have := hL.hob; have := hU.ilay.clay.qlay.tlay.htb; have := hU.ilay.clay.qlay.tlay.hte
    have := hU.ilay.clay.qlay.hqb; have := hU.ilay.clay.hcb; have := hU.ilay.hib0; have := hU.ilay.hie
    have := hU.hub0; have := hU.ilay.clay.qlay.tlay.slay.hsb
    have T := liftUT (ida := ida) (ob := ob) (xb := xb) (vb := vb) (eb := eb) εR c i0 hL
      (trapShare_triple (ida := ida) εR c i0 hU hmax hnum hmp hnn (kl := kl) (kh := kh))
      (fun k hk => by unfold ShareF UCF at hk; omega)
    refine (T.widen (fun k hk => hk.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))).conseq
      (fun σ d ⟨hp, d1, hs⟩ => ?_) (fun σ d σ' d' _ hq => ?_)
    · have hs' : onU (trap_offer_shared_mem_spec num_proc maxpage) d = some d1 := hs
      unfold onU at hs'
      cases hq : trap_offer_shared_mem_spec num_proc maxpage d.toUData with
      | none => rw [hq] at hs'; cases hs'
      | some u => exact ⟨hp.1, hp.2.2.2.1, hp.2.2.2.2.1, u, by first | exact hq | rfl⟩
    · obtain ⟨u, rfl, hu⟩ := hq
      show onU (trap_offer_shared_mem_spec num_proc maxpage) d = _
      unfold onU; rw [hu]
  · exact ⟨by dsimp only; decide, ((print_triple (ida := ida) εR c i0 hL).widen
      (fun k hk => hk.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inl h))))).conseq
      (pre _) (fun _ _ _ _ _ h => h)⟩

/-- **`syscall_dispatch_c` on the kernel machine does what
`sys_dispatch_h_spec` says.** -/
theorem sysDispatchH_run (code : Nat → Stmt KPrim) (hL : HL) (hmax : 3 * maxpage < 2 ^ 32)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20) (hnn : num_id ≤ num_proc) (hnn' : num_proc ≤ num_id)
    (hnpc : num_proc ≤ num_chan) (hel0 : cb + 5 * num_id ≤ elb) (hel1 : elb + num_id ≤ sb) {mc pstart : Nat} {elf : Nat → Nat}
    (hov : num_id * mc + mc + 1 < 2 ^ 32) (hps : pstart < 2 ^ 32) {kl kh : Nat} {σ : Locals} {K : Cont KPrim}
    {l : RLog} {b : Region} {d d' : HData}
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MH d b) (hE : MatchELF num_id elb elf b)
    (hP : DPre maxpage num_id num_proc num_chan kl kh d)
    (hCV : Container_valid num_id mc d.AC) (hcu : (d.AC d.cid).cused = true)
    (hs : sys_dispatch_h_spec num_id mc num_chan num_proc maxpage code pstart elf d = some d') :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      KStar εR c code
        ⟨⟨sysDispatchHK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart maxpage pb fb sb ob xb vb eb ipb, K, σ⟩,
          d.kctxt, l⟩
        ⟨⟨.skip, K, σ'⟩, d'.kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MH d' b' ∧ σ' "lk" = σ "lk" := by
  have hU := hL.ulay
  have := hL.hob; have := hL.hxb; have := hL.hxv; have := hL.hve; have := hL.hep
  have hcp := hP.1
  have hI := hP.2.2.2.2.2
  unfold sys_dispatch_h_spec at hs
  cases e1 : uctx_arg1_spec d.toUData with
  | none => rw [e1] at hs; cases hs
  | some a =>
    rw [e1] at hs; simp only at hs
    obtain ⟨ha, ha32⟩ := arg_val e1
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (uctxArgU (ida := ida) (cidb := cidb) εR c i0 hU (F := fun _ => False)
      "arg1" (by decide) (reg := U_EAX) (by decide) (σ := σ) hcp ha).2 l b hlk hcs hM.1
    have hb1 : b = b1 := (funext (fun k => f1 k (fun h => h))).symm
    subst hb1
    let σ1 := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "arg1" (BitVec.ofNat 32 a)
    have harg : σ1 "arg1" = BitVec.ofNat 32 a := by simp [σ1]
    have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
    let rest : Stmt KPrim := .ite (.bin .eq (.var "arg1") (.const 2))
      (sysProcCreateK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart)
      (mapS .base (chainS cidb ucb ((hlist cb maxpage pb fb sb num_proc cidb ucb ob xb vb eb tb qb ipb num_chan).map fun p => (p.1, p.2.1))))
    have k1 := kstar_seq (εR := εR) (c := c) (code := code) r1 rest K d.kctxt
    have k2 := kstep_ite (εR := εR) (c := c) (code := code) (.bin .eq (.var "arg1") (.const 2))
      (sysProcCreateK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart)
      (mapS .base (chainS cidb ucb ((hlist cb maxpage pb fb sb num_proc cidb ucb ob xb vb eb tb qb ipb num_chan).map fun p => (p.1, p.2.1))))
      K σ1 d.kctxt l1
    by_cases h2 : a = 2
    · rw [if_pos h2] at hs
      unfold onU at hs
      cases hq : trap_proc_create_spec num_id mc num_chan code pstart elf d.toUData with
      | none => rw [hq] at hs; cases hs
      | some u =>
        rw [hq] at hs; simp only [Option.some.injEq] at hs; subst hs
        have hg : ¬ (Expr.bin .eq (.var "arg1") (.const 2)).eval σ1 = 0 := eqc_true (b := 2) harg h2
        rw [if_neg hg] at k2
        obtain ⟨σ', l', b', hks, hcs', hM', -, hlk', hf', -⟩ := sysProcCreate_run εR c i0 code hU hnum hnn hel0
          hel1 hov hps (K := K) (σ := σ1) hlk1 c1 hM.1 hE hcp hI hCV hcu hq
        have hCF : ∀ k, CreateF cb num_id tb num_proc qb num_chan ucb k → k < ucb + 17 * num_proc := by
          have := hU.hub0; have := hU.ilay.hib0; have := hU.ilay.clay.hcb; have := hU.ilay.clay.qlay.hqb
          have := hU.ilay.clay.qlay.tlay.htb; have := hU.ilay.clay.qlay.tlay.slay.hsb
          have := hU.ilay.clay.qlay.tlay.slay.hse; have := hU.ilay.clay.qlay.hqe
          intro k hk
          unfold CreateF SpawnF QTF TF QF UCF at hk
          omega
        refine ⟨σ', l', b', k1.trans (.step k2 hks), hcs', ⟨hM', matchOut_frame hM.2.1 (fun k hk => hf' k
          (fun h => by have := hCF k h; unfold OF at hk; omega)),
          matchX_of (matchX_frame hM.2.2 (fun k h1 h2' => hf' k (fun h => by have := hCF k h; omega))
            hL.hxv hL.hve) rfl rfl rfl⟩, by rw [hlk']; simp [σ1, Locals.set]⟩
    · rw [if_neg h2] at hs
      have hg : (Expr.bin .eq (.var "arg1") (.const 2)).eval σ1 = 0 := eqc_false (b := 2) harg ha32 (by decide) h2
      rw [if_pos hg] at k2
      have hs' := hs
      rw [← hlist_specs cb maxpage pb fb sb num_proc cidb ucb ob xb vb eb tb qb ipb num_chan] at hs'
      have wH : ∀ k, HF ucb num_proc xb vb eb k → DF cb num_id pb sb num_proc ucb ob xb vb eb tb qb num_chan ipb fb k :=
        fun k hk => hk.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr (Or.inr (Or.inl h))))
      obtain ⟨σ', l', b', d'', r, c', m', k', fr, q⟩ := chain_triple (ida := ida) (cidb := cidb) εR c i0 hL wH
        (DPre maxpage num_id num_proc num_chan kl kh) (fun d h => h.1) (hlist cb maxpage pb fb sb num_proc cidb ucb ob xb vb eb tb qb ipb num_chan) a
        (hlist_triples (ida := ida) εR c i0 hL hmax hnum hmp hnn' hnpc) σ1 l1 b d hlk1 c1 hM ⟨harg, ha32, hP, d', hs'⟩
      rw [hs'] at q; simp only [Option.some.injEq] at q; subst q
      rw [chain_kctxt hs]
      exact ⟨σ', l', b', k1.trans (.step k2 (kstar_base r K d.kctxt)), c', m', by rw [k']; simp [σ1, Locals.set]⟩

end Run

end TTop
