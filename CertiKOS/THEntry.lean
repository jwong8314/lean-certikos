import CertiKOS.TDispatchH
import CertiKOS.TInv

/-!
# `syscall_dispatch` on the full state

The dispatcher of `TDispatchH` handles every system call of the full state
(the hypercalls, `SYS_share`, `SYS_print`, `SYS_recv`, `SYS_hvm_mmap`), but
it was not yet an entry point: here it gets mCertiKOS's
`proc_exit_user; syscall_dispatch_c; proc_start_user` around it.

* `MatchHP`: the full state with the two CPU words (`CR3`, the paging bit).
* `liftUPT`: a triple of the process layers with the CPU words holds on the
  full state, if it writes none of the consoles and VMX blocks.
* `chain_cidH`, `dispatch_h_cid`: the dispatcher keeps the running process.
* `sysEntryHK`, `syscall_h_run`: **a system call on the full state, on the
  kernel machine**, from the trap to the end of the kernel computation,
  assuming the kernel invariant `KInv` at the trap.
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


open TSysCall TInv

/-! ## The dispatcher keeps the running process -/

theorem setRegs_cidH : ∀ (o : List (Nat × Nat)) (u u' : UData), setRegs o u = some u' → u'.cid = u.cid
  | [], u, u', h => by simp only [setRegs, Option.some.injEq] at h; rw [h]
  | (r, n) :: t, u, u', h => by
    simp only [setRegs] at h
    cases h1 : uctx_set_reg_spec r n u with
    | none => rw [h1] at h; cases h
    | some u1 =>
      rw [h1] at h
      obtain ⟨U, e⟩ := set_reg_shape h1
      rw [setRegs_cidH t u1 u' h, e]

theorem hcall_cidH {r : Option (XSt × List (Nat × Nat))} {d d' : HData} (h : hcall r d = some d') :
    d'.cid = d.cid := by
  obtain ⟨x, o, u, -, hR, rfl⟩ := hcall_some h
  exact setRegs_cidH o _ u hR

theorem share_cidH {np mp : Nat} {u u' : UData} (h : trap_offer_shared_mem_spec np mp u = some u') :
    u'.cid = u.cid := by
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

theorem recv_cidH {np nc : Nat} {u u' : UData} (h : trap_receivechan_spec np nc u = some u') :
    u'.cid = u.cid := by
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
      rw [e, e1]; exact TTrap.recv_cid hr

theorem onU_cidH {f : UData → Option UData} (hf : ∀ u u', f u = some u' → u'.cid = u.cid) {d d' : HData}
    (h : onU f d = some d') : d'.cid = d.cid := by
  unfold onU at h
  cases hu : f d.toUData with
  | none => rw [hu] at h; cases h
  | some u => rw [hu] at h; simp only [Option.some.injEq] at h; rw [← h]; exact hf _ _ hu

theorem print_cidH {d d' : HData} (h : print_spec d = some d') : d'.cid = d.cid := by
  unfold print_spec at h
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at h; cases h
  | some x =>
    cases e0 : uctx_set_errno_spec E_SUCC d.toUData with
    | none => rw [e2, e0] at h; cases h
    | some u =>
      rw [e2, e0] at h; simp only [Option.some.injEq] at h; rw [← h]
      obtain ⟨U, e⟩ := set_reg_shape e0; rw [e]


theorem mmap_cidH {np mp : Nat} {d d' : HData} (h : trap_mmap_spec np mp d = some d') : d'.cid = d.cid := by
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
          | some hpa' => rw [hp'] at h; simp only at h; unfold mmapTail at h; have := hcall_cidH h; exact this
      · unfold mmapTail at h; exact hcall_cidH h
  · exact hcall_cidH h

theorem chainF_cidH : ∀ (l : List (Nat × (HData → Option HData))) (a : Nat) (d d' : HData),
    (∀ p ∈ l, ∀ d d', p.2 d = some d' → d'.cid = d.cid) → chainF l a d = some d' → d'.cid = d.cid
  | [], a, d, d', _, h => hcall_cidH h
  | (n, f) :: t, a, d, d', hl, h => by
    simp only [chainF] at h
    by_cases e : a = n
    · rw [if_pos e] at h; exact hl (n, f) (List.mem_cons_self ..) d d' h
    · rw [if_neg e] at h; exact chainF_cidH t a d d' (fun p hm => hl p (List.mem_cons_of_mem _ hm)) h

theorem chain_cidH {np mp nc a : Nat} {d d' : HData} (h : chainF (hspecs np mp nc) a d = some d') :
    d'.cid = d.cid := by
  refine chainF_cidH _ a d d' (fun p hm => ?_) h
  simp only [hspecs, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro d d' h; unfold trap_get_tsc_offset_spec at h; (repeat' (split at h)) <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_set_tsc_offset_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> simp only [e0, e1] at h <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_get_exitinfo_spec at h; (repeat' (split at h)) <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_set_reg_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> simp only [e0, e1] at h <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_get_reg_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> simp only [e0] at h <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_set_seg_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> cases e2 : uctx_arg4_spec d.toUData <;> cases e3 : uctx_arg5_spec d.toUData <;> cases e4 : uctx_arg6_spec d.toUData <;> simp only [e0, e1, e2, e3, e4] at h <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_get_next_eip_spec at h; (repeat' (split at h)) <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_inject_event_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> cases e2 : uctx_arg4_spec d.toUData <;> cases e3 : uctx_arg5_spec d.toUData <;> simp only [e0, e1, e2, e3] at h <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_check_pending_event_spec at h; (repeat' (split at h)) <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_check_int_shadow_spec at h; (repeat' (split at h)) <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_intercept_int_window_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> simp only [e0] at h <;> first | exact hcall_cidH h | cases h
  · intro d d' h; unfold trap_handle_rdmsr_spec at h; (repeat' (split at h)) <;> first | exact hcall_cidH h | cases h
  · intro d d' h; exact mmap_cidH h
  · intro d d' h; unfold trap_handle_wrmsr_spec at h; (repeat' (split at h)) <;> first | exact hcall_cidH h | cases h
  · exact fun d d' h => onU_cidH (fun u u' hu => by obtain ⟨U, e⟩ := get_quota_shape hu; rw [e]) h
  · exact fun d d' h => onU_cidH (fun u u' hu => recv_cidH hu) h
  · exact fun d d' h => onU_cidH (fun u u' hu => share_cidH hu) h
  · exact fun d d' h => print_cidH h


theorem trap_create_cid {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
    {u u' : UData} (h : trap_proc_create_spec num_id mc num_chan code pstart elf u = some u') : u'.cid = u.cid := by
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
                  obtain ⟨U, e⟩ := set_reg_shape h
                  obtain ⟨U1, e1⟩ := set_reg_shape hr
                  have hc := proc_create_cid hp; rw [e, e1]; exact hc
            · rw [if_neg c4] at h; cases h
        · rw [if_neg c3] at h; obtain ⟨U, e⟩ := set_reg_shape h; rw [e]
      · rw [if_neg c2] at h; obtain ⟨U, e⟩ := set_reg_shape h; rw [e]
    · rw [if_neg c1] at h; obtain ⟨U, e⟩ := set_reg_shape h; rw [e]

theorem dispatch_h_cid {num_id mc num_chan num_proc maxpage : Nat} {code : Nat → Stmt KPrim} {pstart : Nat}
    {elf : Nat → Nat} {d d' : HData} (h : sys_dispatch_h_spec num_id mc num_chan num_proc maxpage code pstart elf d = some d') :
    d'.cid = d.cid := by
  unfold sys_dispatch_h_spec at h
  cases e1 : uctx_arg1_spec d.toUData with
  | none => rw [e1] at h; cases h
  | some a =>
    rw [e1] at h; simp only at h
    split at h
    · exact onU_cidH (fun u u' hu => trap_create_cid hu) h
    · exact chain_cidH h

/-! ## The full state with the CPU words -/

def MatchHP (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub : Nat) (d : HData)
    (b : Region) : Prop :=
  MatchUP maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub d.toUData b ∧
    (MatchOut num_proc ob d.devout b ∧ (MatchX xb vb eb (toX d) b ∧ VEPT.MatchUp (upb vb) eb d.ept b))

/-- `syscall_dispatch` on the full state:
`proc_exit_user; syscall_dispatch_c; proc_start_user`. -/
def sysEntryHK (cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart maxpage pb fb sb ob xb vb eb ipb cpub : Nat) :
    Stmt KPrim :=
  .seq (mapS .base (procExitUserS cidb ucb pb cpub))
    (.seq (sysDispatchHK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart maxpage pb fb sb ob xb vb eb ipb)
      (mapS .base (procStartUserS cidb ucb pb cpub)))

section Entry
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub elb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MUP" => MatchUP maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub
local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb
local notation "MHP" => MatchHP maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

theorem matchHP_H {d : HData} {b : Region} (h : MHP d b) : MH d b := ⟨h.1.1, h.2⟩

/-- **A triple of the process layers with the CPU words holds on the full
state.** -/
theorem liftUPT (hL : HL) {F : Nat → Prop} {P : Locals → UData → Prop} {s : Stmt APrim}
    {Q : Locals → UData → Locals → UData → Prop} (h : Triple εR c i0 MUP F P s Q)
    (hF : ∀ k, F k → k < ucb + 17 * num_proc ∨ pb ≤ k) :
    Triple εR c i0 MHP F (fun σ d => P σ d.toUData) s
      (fun σ d σ' d' => ∃ u, d' = { d with toUData := u } ∧ Q σ d.toUData σ' u) := by
  have := hL.hob; have := hL.hxb; have := hL.hxv; have := hL.hve; have := hL.hep; have := hL.hup
  exact h.lift (π := HData.toUData) (put := fun (d' : HData) (u' : UData) => ({ d' with toUData := u' } : HData))
    (M2 := fun d' b => MatchOut num_proc ob d'.devout b ∧
      (MatchX xb vb eb (toX d') b ∧ VEPT.MatchUp (upb vb) eb d'.ept b)) (fun _ _ => rfl)
    (fun d' b σ σ' d1 b' h2 _ _ _ hf => ⟨matchOut_frame h2.1 (fun k hk => hf k (fun h' => by
        have := hF k h'; unfold OF at hk; omega)),
      matchX_of (matchX_frame h2.2.1 (fun k h1 h2' => hf k (fun h' => by
        have := hF k h'; unfold VEPT.NPG at h2'; omega)) hL.hxv hL.hve) rfl rfl rfl,
      VEPT.matchUp_frame h2.2.2 (fun a ha => hf a (fun h' => by
        have := hF a h'; unfold VEPT.InUp upb at ha; omega))⟩)

/-- **A system call on the full state, on the kernel machine.** -/
theorem syscall_h_run (code : Nat → Stmt KPrim) (hL : HL) (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_id ≤ num_proc) (hnn' : num_proc ≤ num_id) (hnpc : num_proc ≤ num_chan)
    (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub) {mc pstart : Nat} {elf : Nat → Nat}
    (hov : num_id * mc + mc + 1 < 2 ^ 32) (hps : pstart < 2 ^ 32) {kl kh : Nat} {σ : Locals} {K : Cont KPrim}
    {l : RLog} {b : Region} {d d2 : HData} {u1 u3 : UData} {rs rs' : UContext}
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MHP d b) (hE : MatchELF num_id elb elf b)
    (hI : KInv num_id mc num_proc num_chan maxpage kl kh d.toUData)
    (hrs : ∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) (h1 : proc_exit_user_spec rs d.toUData = some u1)
    (h2 : sys_dispatch_h_spec num_id mc num_chan num_proc maxpage code pstart elf { d with toUData := u1 } = some d2)
    (h3 : proc_start_user_spec d2.toUData = some (u3, rs')) :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      KStar εR c code
        ⟨⟨sysEntryHK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart maxpage pb fb sb ob xb vb eb ipb cpub, K, σ⟩,
          d.kctxt, l⟩ ⟨⟨.skip, K, σ'⟩, u3.kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MHP { d2 with toUData := u3 } b' ∧ MatchELF num_id elb elf b' ∧
      (∀ n, n < 17 → ∀ v, rs' n = some v → σ' (ureg n) = v) ∧ σ' "lk" = σ "lk" := by
  have hU := hL.ulay
  have hCL := hU.ilay.clay
  have := hU.hub0; have := hU.hue; have := hU.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb
  have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse
  have := hL.hob; have := hL.hxb
  obtain ⟨hd1, hpg⟩ := exit_shape h1
  -- `proc_exit_user`
  have T := liftUPT (ida := ida) εR c i0 hL (procExitUser_triple εR c i0 hU hcp0 hcp1 rs)
    (fun k hk => by rcases hk with ⟨h3', h4'⟩ | h3' <;> omega)
  obtain ⟨σ1, l1, b1, d1', r1, c1, m1, k1, f1, u, hd1', hq1, fr1⟩ := T σ l b d hlk hcs hM ⟨hI.cid, hrs, u1, h1⟩
  rw [h1] at hq1
  simp only [Option.some.injEq] at hq1
  subst hq1; subst hd1'
  have hlk1 : (σ1 "lk").toNat = i0 := by rw [k1]; exact hlk
  have hE1 : MatchELF num_id elb elf b1 := fun i hi => by
    rw [f1 _ (fun h => by rcases h with ⟨h3', h4'⟩ | h3' <;> omega)]
    exact hE i hi
  have hne1 : b1 (cpub + 1) ≠ 0 := m1.1.2.2.1 (by rw [hd1]; exact hpg)
  have hI1 := exit_keeps h1 hI
  -- `syscall_dispatch_c`
  obtain ⟨σ2, l2, b2, hks, c2, m2, k2, f2⟩ := sysDispatchH_run εR c i0 code hL hmax hnum hmp hnn hnn' hnpc hel0
    (by omega) hov hps (kl := kl) (kh := kh) (σ := σ1) (K := .seq (mapS .base (procStartUserS cidb ucb pb cpub)) K)
    hlk1 c1 (matchHP_H m1) hE1 ⟨hI1.cid, Nat.lt_of_lt_of_le hI1.cid hnn', hI1.uq _, hI1.atinv, hI1.uq, hI1.ainv⟩
    hI1.cv hI1.cur.1 h2
  have hne2 : b2 (cpub + 1) ≠ 0 := by rw [f2 _ (by omega) (by omega)]; exact hne1
  have hcid2 : d2.cid < num_proc := by rw [dispatch_h_cid h2]; exact hI1.cid
  -- `proc_start_user`
  obtain ⟨hd3, -, hpg2⟩ := start_shape h3
  obtain ⟨σ3, l3, b3, r3, c3, m3, hreg, f3⟩ := procStartUser_run εR c i0 hU hcp0 hcp1 (σ := σ2)
    (by rw [k2]; exact hlk1) c2 m2.1 ⟨fun _ => hne2, fun _ => hpg2⟩ hcid2 h3
  refine ⟨σ3, l3, b3, ?_, c3, ⟨m3, matchOut_frame m2.2.1 (fun k hk => f3 k (by unfold OF at hk; omega)),
    matchX_of (matchX_frame m2.2.2.1 (fun k h1' h2' => f3 k (by omega)) hL.hxv hL.hve) rfl rfl rfl,
    VEPT.matchUp_frame m2.2.2.2 (fun a ha => f3 a (by have := hL.hxv; unfold VEPT.InUp upb at ha; omega))⟩,
    fun i hi => ?_, hreg, ?_⟩
  · have hk3 : u3.kctxt = d2.kctxt := by rw [hd3]
    have hk1 : u1.kctxt = d.kctxt := by rw [hd1]
    rw [hk3]
    refine (kstar_seq r1 _ K d.kctxt).trans ((KStar.single (kstep_seq _ _ K σ1 d.kctxt l1)).trans ?_)
    rw [← hk1]
    exact hks.trans ((KStar.single (kstep_skip_seq _ K σ2 d2.kctxt l2)).trans (kstar_base r3 K d2.kctxt))
  · rw [f3 _ (by omega), f2 _ (by omega) (by omega)]
    exact hE1 i hi
  · rw [r3.frame rfl, k2, k1]

end Entry

end TTop
