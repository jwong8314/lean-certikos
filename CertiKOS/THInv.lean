import CertiKOS.THEntry

/-!
# The kernel invariant through the full dispatcher

`TInv.dispatch_keeps` showed that mCertiKOS's verified dispatcher keeps
`KInv`. Here the same for the full dispatcher of `TDispatchH`, every row:

* `hcall_keeps`: a hypercall writes only the caller's registers (and the
  virtual machine, which `KInv` does not read).
* `print_keeps`, `quota` (by shape), `trap_create_keeps` (`SYS_spawn`).
* `KInv.ofMono`: a change of the memory model that keeps the threads, raises
  usages within quota and keeps the allocation table's invariant keeps
  `KInv`. `ptResv2_facts`, `offer_facts`, `share_keeps`: **`SYS_share`**;
  `mmap_keeps`: **`SYS_hvm_mmap`**.
* `wakeup_other`, `recv_keeps`: **`SYS_recv`**: the copy changes only memory
  contents, and waking the sender leaves the running thread alone.
* `dispatch_h_keeps`: **the full dispatcher keeps `KInv`**, for every number.
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


open TSysCall TInv MMInv

section
variable {num_id mc num_proc num_chan maxpage kl kh : Nat}

local notation "KI" => KInv num_id mc num_proc num_chan maxpage kl kh

theorem setRegs_keeps : ∀ (o : List (Nat × Nat)) (u u' : UData), setRegs o u = some u' → KI u → KI u'
  | [], u, u', h, hI => by simp only [setRegs, Option.some.injEq] at h; rw [← h]; exact hI
  | (r, n) :: t, u, u', h, hI => by
    simp only [setRegs] at h
    cases h1 : uctx_set_reg_spec r n u with
    | none => rw [h1] at h; cases h
    | some u1 =>
      rw [h1] at h
      exact setRegs_keeps t u1 u' h (setReg_keeps h1 hI)

theorem hcall_keeps {r : Option (XSt × List (Nat × Nat))} {d d' : HData} (h : hcall r d = some d')
    (hI : KI d.toUData) : KI d'.toUData := by
  obtain ⟨x, o, u, -, hR, rfl⟩ := hcall_some h
  exact setRegs_keeps o _ u hR hI

theorem print_keeps {d d' : HData} (h : print_spec d = some d') (hI : KI d.toUData) : KI d'.toUData := by
  unfold print_spec at h
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at h; cases h
  | some x =>
    cases e0 : uctx_set_errno_spec E_SUCC d.toUData with
    | none => rw [e2, e0] at h; cases h
    | some u =>
      rw [e2, e0] at h; simp only [Option.some.injEq] at h; rw [← h]
      exact setReg_keeps e0 hI

theorem trap_create_keeps (hnn : num_id ≤ num_proc) {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
    {u u' : UData} (h : trap_proc_create_spec num_id mc num_chan code pstart elf u = some u') (hI : KI u) : KI u' := by
  unfold trap_proc_create_spec at h
  cases e3 : uctx_arg3_spec u with
  | none => rw [e3] at h; cases h
  | some a3 =>
    rw [e3] at h; simp only at h
    by_cases c1 : a3 + (u.AC u.cid).cusage ≤ (u.AC u.cid).cquota
    · rw [if_pos c1] at h
      by_cases c2 : u.cid * mc + 1 + mc ≤ num_id
      · rw [if_pos c2] at h
        by_cases c3 : (u.AC u.cid).cchildren.length < mc
        · rw [if_pos c3] at h
          cases e2 : uctx_arg2_spec u with
          | none => rw [e2] at h; cases h
          | some a1 =>
            rw [e2] at h; simp only at h
            by_cases c4 : a1 < num_id
            · rw [if_pos c4] at h
              cases hp : proc_create_spec num_id mc num_chan code pstart (elf a1) a3 u with
              | none => rw [hp] at h; cases h
              | some pr =>
                obtain ⟨d1, n⟩ := pr
                rw [hp] at h; simp only at h
                cases hr : uctx_set_retval1_spec n d1 with
                | none => rw [hr] at h; cases h
                | some d2 =>
                  rw [hr] at h; simp only at h
                  exact setReg_keeps h (setReg_keeps hr (create_keeps hnn hp hI))
            · rw [if_neg c4] at h; cases h
        · rw [if_neg c3] at h; exact setReg_keeps h hI
      · rw [if_neg c2] at h; exact setReg_keeps h hI
    · rw [if_neg c1] at h; exact setReg_keeps h hI

/-! ## Changes of the memory model -/

/-- **A change that keeps the threads, raises usages within quota and keeps
the allocation table's invariant keeps `KInv`.** -/
theorem KInv.ofMono {d d' : UData} (hI : KI d) (e1 : d'.cid = d.cid) (e2 : d'.abtcb = d.abtcb)
    (e3 : d'.abq = d.abq) (e7 : d'.ihost = d.ihost) (hm : ACMono d.AC d'.AC) (hmmi : MMI maxpage kl kh d'.toPTData)
    (hinit : d'.init = d.init) (hpg : d'.pg = d.pg) : KI d' := by
  have hcu : ∀ j, (d'.AC j).cused = (d.AC j).cused := fun j => (hm j).2.2.2.1
  refine ⟨by rw [e1]; exact hI.cid, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hmmi.1, hmmi.2, by rw [hpg]; exact hI.pg,
    by rw [e7]; exact hI.ihost, by rw [hinit]; exact hI.init⟩
  · show (d'.AC d'.cid).cused = true
    rw [hcu, e1]; exact hI.cur.1
  · show d'.abtcb d'.cid = _
    rw [e2, e1]; exact hI.cur.2
  · show AbTCBCorrect_range _ _ d'.abtcb
    rw [e2]; exact hI.ainv.tc
  · show AbQCorrect_range _ _ d'.abq
    rw [e3]; exact hI.ainv.qc
  · intro j s b' hj hc hjt
    have hc' : (d'.AC j).cused = false := hc
    rw [hcu] at hc'
    have hjt' : d.abtcb j = .AbTCBValid s b' := by rw [← e2]; exact hjt
    exact hI.ainv.niq j s b' hj hc' hjt'
  · show QCount _ _ d'.abtcb d'.abq
    rw [e2, e3]; exact hI.ainv.cnt
  · show InQ _ _ d'.abtcb d'.abq
    rw [e2, e3]; exact hI.ainv.inq
  · exact Container_valid.of_same hI.cv (fun j => (hm j).1) (fun j => (hm j).2.1) (fun j => (hm j).2.2.1) hcu
      (fun j _ => ⟨(hm j).2.2.2.2, by rw [← (hm j).1]; exact hmmi.2 j⟩)

theorem ptResv2_facts {mp np n vadr perm n' vadr' perm' : Nat} {d d' : PTData} {r : Nat}
    (h : ptResv2_spec mp np n vadr perm n' vadr' perm' d = some (d', r)) :
    ACMono d.AC d'.AC ∧ d'.init = d.init ∧ d'.pg = d.pg := by
  unfold ptResv2_spec at h
  cases hA : container_alloc_spec n d.toRData with
  | none => rw [hA] at h; cases h
  | some pr =>
    obtain ⟨r1, b⟩ := pr
    rw [hA] at h; simp only at h
    obtain ⟨a1, b1⟩ := alloc_facts' hA
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact ⟨ACMono.refl _, rfl, rfl⟩
    · cases hi : ptInsert_spec mp np n vadr b perm { d with toRData := r1 } with
      | none => rw [hi] at h; cases h
      | some pr2 =>
        obtain ⟨d2, v⟩ := pr2
        rw [hi] at h; simp only at h
        obtain ⟨a2, b2, c2⟩ := ptInsert_facts hi
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          exact ⟨a1.trans a2, b2.trans b1, c2⟩
        · obtain ⟨a3, b3, c3⟩ := ptInsert_facts h
          exact ⟨a1.trans (a2.trans a3), b3.trans (b2.trans b1), c3.trans c2⟩

theorem offer_facts {np mp p1 p2 va : Nat} {s s' : SData} {r : Nat}
    (h : offer_shared_mem_spec np mp p1 p2 va s = some (s', r)) :
    ACMono s.AC s'.AC ∧ s'.init = s.init ∧ s'.pg = s.pg := by
  unfold offer_shared_mem_spec at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
       first
         | exact ⟨ACMono.refl _, rfl, rfl⟩
         | exact ptResv2_facts ‹ptResv2_spec _ _ _ _ _ _ _ _ _ = some _›; done)
    | cases h

/-- **`SYS_share` keeps the invariant.** -/
theorem share_keeps {u u' : UData} (h : trap_offer_shared_mem_spec num_proc maxpage u = some u') (hI : KI u) :
    KI u' := by
  unfold trap_offer_shared_mem_spec at h
  cases e2 : uctx_arg2_spec u with
  | none => rw [e2] at h; cases h
  | some va =>
    rw [e2] at h; simp only at h
    by_cases c1 : u.cid = 1
    · rw [if_pos c1] at h
      cases ho : offer_shared_mem_spec num_proc maxpage 1 2 va u.toSData with
      | none => rw [ho] at h; cases h
      | some pr =>
        obtain ⟨s', r⟩ := pr
        rw [ho] at h; simp only at h
        cases h1 : uctx_set_retval1_spec r { u with toSData := s' } with
        | none => rw [h1] at h; cases h
        | some u1 =>
          rw [h1] at h; simp only at h
          obtain ⟨hm, hinit, hpg⟩ := offer_facts ho
          have hK : KI ({ u with toSData := s' } : UData) :=
            KInv.ofMono hI rfl rfl rfl rfl hm (offer_keeps (maxpage := maxpage) (kl := kl) (kh := kh)
              ⟨hI.atinv, hI.uq⟩ ho) hinit hpg
          exact setReg_keeps h (setReg_keeps h1 hK)
    · rw [if_neg c1] at h; exact setReg_keeps h hI

/-- **`SYS_hvm_mmap` keeps the invariant.** -/
theorem mmap_keeps {d d' : HData} (h : trap_mmap_spec num_proc maxpage d = some d') (hI : KI d.toUData) :
    KI d'.toUData := by
  unfold trap_mmap_spec at h
  cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;>
    cases e4 : uctx_arg4_spec d.toUData <;> simp only [e2, e3, e4] at h <;> try cases h
  split at h
  · cases hp : ptRead_spec num_proc d.cid _ d.toPTData with
    | none => rw [hp] at h; cases h
    | some hpa =>
      rw [hp] at h; simp only at h
      split at h
      · cases hr : ptResv_spec maxpage num_proc d.cid _ 7 d.toPTData with
        | none => rw [hr] at h; cases h
        | some pr =>
          obtain ⟨p0, r⟩ := pr
          rw [hr] at h; simp only at h
          cases hp' : ptRead_spec num_proc d.cid _ p0 with
          | none => rw [hp'] at h; cases h
          | some hpa' =>
            rw [hp'] at h; simp only at h; unfold mmapTail at h
            obtain ⟨hm, hinit, hpg⟩ := ptResv_facts hr
            have hK : KI ({ d with toPTData := p0 } : HData).toUData :=
              KInv.ofMono hI rfl rfl rfl rfl hm (ptResv_keeps (maxpage := maxpage) (kl := kl) (kh := kh)
                ⟨hI.atinv, hI.uq⟩ hr) hinit hpg
            exact hcall_keeps h hK
      · unfold mmapTail at h; exact hcall_keeps h hI
  · exact hcall_keeps h hI

/-! ## `SYS_recv` -/

/-- Waking a thread leaves the running thread (on no queue) alone. -/
theorem wakeup_other {n : Nat} {a a' : AData} (hI : AInv num_proc num_chan a)
    (hs : thread_wakeup_spec num_proc num_chan n a = some a') {j : Nat} {s : ThreadState}
    (hj : a.abtcb j = .AbTCBValid s (-1)) : a'.abtcb j = a.abtcb j ∧ a'.toSData = a.toSData := by
  unfold thread_wakeup_spec at hs
  split at hs
  · rename_i hc
    cases hl : a.abq n with
    | AbQUndef => rw [hl] at hs; cases hs
    | AbQValid l =>
      rw [hl] at hs; simp only at hs
      split at hs
      · simp only [Option.some.injEq] at hs; subst hs; exact ⟨rfl, rfl⟩
      · rename_i hne
        split at hs
        · simp only [Option.some.injEq] at hs; subst hs
          refine ⟨?_, rfl⟩
          have hmem := PSched.last_mem (l := l) rfl hne
          have hlt := q_lt hI.qc (Nat.le_of_lt hc.2.2) hl hmem
          obtain ⟨s', hai⟩ := hI.inq _ n l hlt (Nat.le_of_lt hc.2.2) hl hmem
          have hjne : j ≠ l.getLastD num_proc := by
            intro e
            rw [e, hai] at hj
            injection hj with e1 e2
            omega
          show setAt a.abtcb _ _ j = _
          rw [setAt_ne _ _ hjne]
        · cases hs
  · cases hs

/-- The successful receive. -/
theorem recv_core {cnt src dst fromid k : Nat} {u : UData} {p : PTData} {a3 : AData}
    (hcp : flatmem_copy_spec cnt src dst u.toPTData = some p)
    (hw : thread_wakeup_spec num_proc num_chan fromid (PIPC.recvDone num_chan fromid k p u.toIData).toAData = some a3)
    (hI : KI u) : KI ({ u with toIData := { PIPC.recvDone num_chan fromid k p u.toIData with toAData := a3 } } : UData) := by
  have hp : p.toRData = u.toRData ∧ p.pg = u.pg := by
    unfold flatmem_copy_spec at hcp
    split at hcp
    · split at hcp
      · simp only [Option.some.injEq] at hcp; subst hcp; exact ⟨rfl, rfl⟩
      · cases hcp
    · cases hcp
  have eAC0 : p.AC = u.AC := congrArg (fun r => r.AC) hp.1
  have hA : AInv num_proc num_chan (PIPC.recvDone num_chan fromid k p u.toIData).toAData := by
    refine ⟨hI.ainv.tc, hI.ainv.qc, ?_, hI.ainv.cnt, hI.ainv.inq⟩
    intro j s b' hj hc hjt
    have hc' : (p.AC j).cused = false := hc
    rw [eAC0] at hc'
    exact hI.ainv.niq j s b' hj hc' hjt
  obtain ⟨ej, es⟩ := wakeup_other hA hw hI.cur.2
  have eAC : a3.AC = u.AC := (congrArg (fun s => s.AC) es).trans eAC0
  have eP : a3.toPData = u.toPData := (congrArg (fun s => s.toPData) es).trans (congrArg (fun r => r.toPData) hp.1)
  refine ⟨hI.cid, ⟨?_, ?_⟩, PSched.thread_wakeup_keeps hA hw, ?_, ?_, ?_, ?_, hI.ihost, ?_⟩
  · show (a3.AC u.cid).cused = true
    rw [eAC]; exact hI.cur.1
  · show a3.abtcb u.cid = _
    rw [ej]; exact hI.cur.2
  · show Container_valid num_id mc a3.AC
    rw [eAC]; exact hI.cv
  · show ATInv maxpage kl kh a3.toPData
    rw [eP]; exact hI.atinv
  · show UQ a3.AC
    rw [eAC]; exact hI.uq
  · show a3.pg = true
    rw [show a3.pg = u.pg from (congrArg (fun s => s.pg) es).trans hp.2]; exact hI.pg
  · show a3.init = true
    rw [show a3.init = u.init from congrArg (fun r => r.init) eP]; exact hI.init

/-- **`SYS_recv` keeps the invariant.** -/
theorem recv_keeps {u u' : UData} (h : trap_receivechan_spec num_proc num_chan u = some u') (hI : KI u) : KI u' := by
  unfold trap_receivechan_spec at h
  cases e2 : uctx_arg2_spec u <;> cases e3 : uctx_arg3_spec u <;> cases e4 : uctx_arg4_spec u <;>
    simp only [e2, e3, e4] at h <;> try cases h
  cases hr : syncreceive_chan_spec num_proc num_chan _ _ _ u.toIData with
  | none => rw [hr] at h; cases h
  | some pr =>
    obtain ⟨i1, r⟩ := pr
    rw [hr] at h; simp only at h
    cases h1 : uctx_set_retval1_spec r { u with toIData := i1 } with
    | none => rw [h1] at h; cases h
    | some u1 =>
      rw [h1] at h; simp only at h
      refine setReg_keeps h (setReg_keeps h1 ?_)
      unfold syncreceive_chan_spec at hr
      repeat' split at hr
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr; exact hI; done)
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr
           exact recv_core ‹flatmem_copy_spec _ _ _ _ = some _› ‹thread_wakeup_spec _ _ _ _ = some _› hI; done)
        | cases hr

/-! ## The full dispatcher -/

/-- **The full dispatcher keeps `KInv`**, for every number. -/
theorem dispatch_h_keeps (hnn : num_id ≤ num_proc) {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
    {d d' : HData} (hs : sys_dispatch_h_spec num_id mc num_chan num_proc maxpage code pstart elf d = some d')
    (hI : KI d.toUData) : KI d'.toUData := by
  unfold sys_dispatch_h_spec at hs
  cases e1 : uctx_arg1_spec d.toUData with
  | none => rw [e1] at hs; cases hs
  | some a =>
    rw [e1] at hs; simp only at hs
    split at hs
    · unfold onU at hs
      cases hq : trap_proc_create_spec num_id mc num_chan code pstart elf d.toUData with
      | none => rw [hq] at hs; cases hs
      | some u => rw [hq] at hs; simp only [Option.some.injEq] at hs; rw [← hs]; exact trap_create_keeps hnn hq hI
    · have h := hs
      simp only [hspecs, chainF] at h
      by_cases e22 : a = 22
      · rw [if_pos e22] at h; unfold trap_get_tsc_offset_spec at h; exact hcall_keeps h hI
      rw [if_neg e22] at h
      by_cases e23 : a = 23
      · rw [if_pos e23] at h; unfold trap_set_tsc_offset_spec at h
        cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;> simp only [e2, e3] at h
        all_goals first | exact hcall_keeps h hI | cases h
      rw [if_neg e23] at h
      by_cases e12 : a = 12
      · rw [if_pos e12] at h; unfold trap_get_exitinfo_spec at h; exact hcall_keeps h hI
      rw [if_neg e12] at h
      by_cases e15 : a = 15
      · rw [if_pos e15] at h; unfold trap_set_reg_spec at h
        cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;> simp only [e2, e3] at h
        all_goals first | exact hcall_keeps h hI | cases h
      rw [if_neg e15] at h
      by_cases e16 : a = 16
      · rw [if_pos e16] at h; unfold trap_get_reg_spec at h
        cases e2 : uctx_arg2_spec d.toUData <;> simp only [e2] at h
        all_goals first | exact hcall_keeps h hI | cases h
      rw [if_neg e16] at h
      by_cases e14 : a = 14
      · rw [if_pos e14] at h; unfold trap_set_seg_spec at h
        cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;>
          cases e4 : uctx_arg4_spec d.toUData <;> cases e5 : uctx_arg5_spec d.toUData <;>
          cases e6 : uctx_arg6_spec d.toUData <;> simp only [e2, e3, e4, e5, e6] at h
        all_goals first | exact hcall_keeps h hI | cases h
      rw [if_neg e14] at h
      by_cases e17 : a = 17
      · rw [if_pos e17] at h; unfold trap_get_next_eip_spec at h; exact hcall_keeps h hI
      rw [if_neg e17] at h
      by_cases e18 : a = 18
      · rw [if_pos e18] at h; unfold trap_inject_event_spec at h
        cases e2 : uctx_arg2_spec d.toUData <;> cases e3 : uctx_arg3_spec d.toUData <;>
          cases e4 : uctx_arg4_spec d.toUData <;> cases e5 : uctx_arg5_spec d.toUData <;>
          simp only [e2, e3, e4, e5] at h
        all_goals first | exact hcall_keeps h hI | cases h
      rw [if_neg e18] at h
      by_cases e20 : a = 20
      · rw [if_pos e20] at h; unfold trap_check_pending_event_spec at h; exact hcall_keeps h hI
      rw [if_neg e20] at h
      by_cases e19 : a = 19
      · rw [if_pos e19] at h; unfold trap_check_int_shadow_spec at h; exact hcall_keeps h hI
      rw [if_neg e19] at h
      by_cases e21 : a = 21
      · rw [if_pos e21] at h; unfold trap_intercept_int_window_spec at h
        cases e2 : uctx_arg2_spec d.toUData <;> simp only [e2] at h
        all_goals first | exact hcall_keeps h hI | cases h
      rw [if_neg e21] at h
      by_cases e24 : a = 24
      · rw [if_pos e24] at h; unfold trap_handle_rdmsr_spec at h; exact hcall_keeps h hI
      rw [if_neg e24] at h
      by_cases e13 : a = 13
      · rw [if_pos e13] at h; exact mmap_keeps h hI
      rw [if_neg e13] at h
      by_cases e25 : a = 25
      · rw [if_pos e25] at h; unfold trap_handle_wrmsr_spec at h; exact hcall_keeps h hI
      rw [if_neg e25] at h
      by_cases e26 : a = 26
      · rw [if_pos e26] at h; unfold onU at h
        cases hq : trap_get_quota_spec d.toUData with
        | none => rw [hq] at h; cases h
        | some u =>
          rw [hq] at h; simp only [Option.some.injEq] at h; rw [← h]
          obtain ⟨U, e⟩ := get_quota_shape hq; subst e
          exact hI.congr rfl rfl rfl rfl rfl rfl rfl
      rw [if_neg e26] at h
      by_cases e9 : a = 9
      · rw [if_pos e9] at h; unfold onU at h
        cases hq : trap_receivechan_spec num_proc num_chan d.toUData with
        | none => rw [hq] at h; cases h
        | some u => rw [hq] at h; simp only [Option.some.injEq] at h; rw [← h]; exact recv_keeps hq hI
      rw [if_neg e9] at h
      by_cases e27 : a = 27
      · rw [if_pos e27] at h; unfold onU at h
        cases hq : trap_offer_shared_mem_spec num_proc maxpage d.toUData with
        | none => rw [hq] at h; cases h
        | some u => rw [hq] at h; simp only [Option.some.injEq] at h; rw [← h]; exact share_keeps hq hI
      rw [if_neg e27] at h
      by_cases e28 : a = 28
      · rw [if_pos e28] at h; exact print_keeps h hI
      rw [if_neg e28] at h
      exact hcall_keeps h hI

end

end TTop
