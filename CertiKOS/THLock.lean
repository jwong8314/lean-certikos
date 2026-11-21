import CertiKOS.THInv
import CertiKOS.TLock

/-!
# The full-state system call, with the lock

`THEntry.syscall_h_run` runs a system call of the full state on the kernel
machine; `THInv.dispatch_h_keeps` shows the full dispatcher keeps `KInv`.
Here, as `TLock` does for mCertiKOS's verified dispatcher, the entry point
takes the lock at the boundary and the invariant lives on the log.

* `QMonoP`: every thread on a queue afterwards was on a queue before.
  `wakeup_qm`, `recv_qm`: `SYS_recv` wakes a thread that was waiting;
  `chain_qm`: every other row leaves the threads alone.
* `pool_dispatch_h`: **the full dispatcher keeps `PoolInv`**.
* `GoodH`: what holds of the full state each time the lock is released on the
  way back to user mode.
* `syscall_h_locked`: **a system call of the full state, with the lock at the
  boundary**, from a `GoodH` log to a `GoodH` log.
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


open LockArray (AEnv ALog acquireA apull)
open LockRegion (RState HLogR rreplay hmemR)
open LogInv TSysCall TInv TLock

/-! ## The handlers and the thread table -/

theorem setRegs_abH : ∀ (o : List (Nat × Nat)) (u u' : UData), setRegs o u = some u' → u'.abtcb = u.abtcb
  | [], u, u', h => by simp only [setRegs, Option.some.injEq] at h; rw [h]
  | (r, n) :: t, u, u', h => by
    simp only [setRegs] at h
    cases h1 : uctx_set_reg_spec r n u with
    | none => rw [h1] at h; cases h
    | some u1 =>
      rw [h1] at h
      obtain ⟨U, e⟩ := set_reg_shape h1
      rw [setRegs_abH t u1 u' h, e]

theorem hcall_abH {r : Option (XSt × List (Nat × Nat))} {d d' : HData} (h : hcall r d = some d') :
    d'.abtcb = d.abtcb := by
  obtain ⟨x, o, u, -, hR, rfl⟩ := hcall_some h
  exact setRegs_abH o _ u hR

theorem share_abH {np mp : Nat} {u u' : UData} (h : trap_offer_shared_mem_spec np mp u = some u') :
    u'.abtcb = u.abtcb := by
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

theorem onU_abH {f : UData → Option UData} (hf : ∀ u u', f u = some u' → u'.abtcb = u.abtcb) {d d' : HData}
    (h : onU f d = some d') : d'.abtcb = d.abtcb := by
  unfold onU at h
  cases hu : f d.toUData with
  | none => rw [hu] at h; cases h
  | some u => rw [hu] at h; simp only [Option.some.injEq] at h; rw [← h]; exact hf _ _ hu

theorem print_abH {d d' : HData} (h : print_spec d = some d') : d'.abtcb = d.abtcb := by
  unfold print_spec at h
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at h; cases h
  | some x =>
    cases e0 : uctx_set_errno_spec E_SUCC d.toUData with
    | none => rw [e2, e0] at h; cases h
    | some u =>
      rw [e2, e0] at h; simp only [Option.some.injEq] at h; rw [← h]
      obtain ⟨U, e⟩ := set_reg_shape e0; rw [e]


theorem mmap_abH {np mp : Nat} {d d' : HData} (h : trap_mmap_spec np mp d = some d') : d'.abtcb = d.abtcb := by
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
          | some hpa' => rw [hp'] at h; simp only at h; unfold mmapTail at h; have := hcall_abH h; exact this
      · unfold mmapTail at h; exact hcall_abH h
  · exact hcall_abH h


/-- Every thread on a queue in `A'` was on a queue in `A`. -/
def QMonoP (A A' : AbTCBPool) : Prop :=
  ∀ (t : Nat) (s : ThreadState) (q : Int), A' t = .AbTCBValid s q → q ≠ -1 →
    ∃ (s' : ThreadState) (q' : Int), A t = .AbTCBValid s' q' ∧ q' ≠ -1

theorem qm_of_eq {A A' : AbTCBPool} (h : A' = A) : QMonoP A A' := fun t s q hs hq => ⟨s, q, by rw [← h]; exact hs, hq⟩

theorem wakeup_qm {np nc n : Nat} {a a' : AData} (hqc : AbQCorrect_range np nc a.abq) (hinq : InQ np nc a.abtcb a.abq)
    (hs : PSched.thread_wakeup_spec np nc n a = some a') : QMonoP a.abtcb a'.abtcb := by
  unfold PSched.thread_wakeup_spec at hs
  split at hs
  · rename_i hc
    cases hl : a.abq n with
    | AbQUndef => rw [hl] at hs; cases hs
    | AbQValid l =>
      rw [hl] at hs; simp only at hs
      split at hs
      · simp only [Option.some.injEq] at hs; subst hs; exact qm_of_eq rfl
      · rename_i hne
        split at hs
        · simp only [Option.some.injEq] at hs; subst hs
          intro t s q ht hq
          have hmem := PSched.last_mem (l := l) rfl hne
          have hlt := q_lt hqc (Nat.le_of_lt hc.2.2) hl hmem
          obtain ⟨s', hai⟩ := hinq _ n l hlt (Nat.le_of_lt hc.2.2) hl hmem
          by_cases e : t = l.getLastD np
          · rw [e]; exact ⟨s', n, hai, by omega⟩
          · have ht' : setAt a.abtcb _ _ t = _ := ht
            rw [setAt_ne _ _ e] at ht'
            exact ⟨s, q, ht', hq⟩
        · cases hs
  · cases hs

theorem recv_qm_core {np nc n k : Nat} {u : UData} {p : PTData} {a3 : AData} (hI : AInv np nc u.toAData)
    (hw : PSched.thread_wakeup_spec np nc n (PIPC.recvDone nc n k p u.toIData).toAData = some a3) :
    QMonoP u.abtcb a3.abtcb :=
  wakeup_qm (a := (PIPC.recvDone nc n k p u.toIData).toAData) hI.qc hI.inq hw

/-- **`SYS_recv` wakes a thread that was waiting.** -/
theorem recv_qm {np nc : Nat} {u u' : UData} (hI : AInv np nc u.toAData) (h : trap_receivechan_spec np nc u = some u') :
    QMonoP u.abtcb u'.abtcb := by
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
      have hab : u'.abtcb = i1.abtcb := by rw [e, e1]
      rw [hab]
      unfold syncreceive_chan_spec at hr
      repeat' split at hr
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr; exact qm_of_eq rfl; done)
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr
           exact recv_qm_core hI ‹PSched.thread_wakeup_spec _ _ _ _ = some _›; done)
        | cases hr

theorem recv_qmH {np nc : Nat} {d d' : HData} (hA : AInv np nc d.toAData)
    (h : onU (trap_receivechan_spec np nc) d = some d') : QMonoP d.abtcb d'.abtcb := by
  unfold onU at h
  cases hq : trap_receivechan_spec np nc d.toUData with
  | none => rw [hq] at h; cases h
  | some u => rw [hq] at h; simp only [Option.some.injEq] at h; rw [← h]; exact recv_qm hA hq

theorem chainF_qm {np nc : Nat} : ∀ (l : List (Nat × (HData → Option HData))) (a : Nat) (d d' : HData),
    (∀ p ∈ l, ∀ d d', p.2 d = some d' → AInv np nc d.toAData → QMonoP d.abtcb d'.abtcb) →
    chainF l a d = some d' → AInv np nc d.toAData → QMonoP d.abtcb d'.abtcb
  | [], a, d, d', _, h, _ => qm_of_eq (hcall_abH h)
  | (n, f) :: t, a, d, d', hl, h, hA => by
    simp only [chainF] at h
    by_cases e : a = n
    · rw [if_pos e] at h; exact hl (n, f) (List.mem_cons_self ..) d d' h hA
    · rw [if_neg e] at h; exact chainF_qm t a d d' (fun p hm => hl p (List.mem_cons_of_mem _ hm)) h hA

/-- **Every row but `SYS_spawn` keeps the threads on queues** (`SYS_recv`
moves one that was waiting). -/
theorem chain_qm {np mp nc a : Nat} {d d' : HData} (hA : AInv np nc d.toAData)
    (h : chainF (hspecs np mp nc) a d = some d') : QMonoP d.abtcb d'.abtcb := by
  refine chainF_qm _ a d d' (fun p hm => ?_) h hA
  simp only [hspecs, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro d d' h hA; unfold trap_get_tsc_offset_spec at h; (repeat' (split at h)) <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_set_tsc_offset_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> simp only [e0, e1] at h <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_get_exitinfo_spec at h; (repeat' (split at h)) <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_set_reg_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> simp only [e0, e1] at h <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_get_reg_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> simp only [e0] at h <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_set_seg_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> cases e2 : uctx_arg4_spec d.toUData <;> cases e3 : uctx_arg5_spec d.toUData <;> cases e4 : uctx_arg6_spec d.toUData <;> simp only [e0, e1, e2, e3, e4] at h <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_get_next_eip_spec at h; (repeat' (split at h)) <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_inject_event_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> cases e1 : uctx_arg3_spec d.toUData <;> cases e2 : uctx_arg4_spec d.toUData <;> cases e3 : uctx_arg5_spec d.toUData <;> simp only [e0, e1, e2, e3] at h <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_check_pending_event_spec at h; (repeat' (split at h)) <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_check_int_shadow_spec at h; (repeat' (split at h)) <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_intercept_int_window_spec at h; cases e0 : uctx_arg2_spec d.toUData <;> simp only [e0] at h <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; unfold trap_handle_rdmsr_spec at h; (repeat' (split at h)) <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · intro d d' h hA; exact qm_of_eq (mmap_abH h)
  · intro d d' h hA; unfold trap_handle_wrmsr_spec at h; (repeat' (split at h)) <;> first | exact qm_of_eq (hcall_abH h) | cases h
  · exact fun d d' h _ => qm_of_eq (onU_abH (fun u u' hu => by obtain ⟨U, e⟩ := get_quota_shape hu; rw [e]) h)
  · exact fun d d' h hA => recv_qmH hA h
  · exact fun d d' h _ => qm_of_eq (onU_abH (fun u u' hu => share_abH hu) h)
  · exact fun d d' h _ => qm_of_eq (print_abH h)

/-! ## The pool invariant -/

section
variable {code : Nat → Stmt KPrim} {pstart cidb ucb pb cpub num_proc num_chan : Nat} {lk : Val}

local notation "PI" => PoolInv code pstart cidb ucb pb cpub num_proc num_chan lk

theorem pool_of_qm {d d' : UData} (hP : PI d) (hk : d'.kctxt = d.kctxt) (hc : d'.cid = d.cid)
    (hq : QMonoP d.abtcb d'.abtcb) : PI d' := by
  intro t ht
  rw [hk, hc]
  refine ⟨(hP t ht).1, fun hne s q hs hq' => ?_⟩
  obtain ⟨s', q', hs', hq''⟩ := hq t s q hs hq'
  exact (hP t ht).2 hne s' q' hs' hq''

theorem pool_trap_create {num_id mc : Nat} (hnn : num_id ≤ num_proc) {elf : Nat → Nat} {u u' : UData}
    (h : trap_proc_create_spec num_id mc num_chan code pstart elf u = some u') (hP : PI u) : PI u' := by
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
                  exact pool_setReg h (pool_setReg hr (pool_create hnn hp hP))
            · rw [if_neg c4] at h; cases h
        · rw [if_neg c3] at h; exact pool_setReg h hP
      · rw [if_neg c2] at h; exact pool_setReg h hP
    · rw [if_neg c1] at h; exact pool_setReg h hP

/-- **The full dispatcher keeps `PoolInv`.** -/
theorem pool_dispatch_h {num_id mc maxpage : Nat} (hnn : num_id ≤ num_proc) {elf : Nat → Nat} {d d' : HData}
    (hA : AInv num_proc num_chan d.toAData)
    (hs : sys_dispatch_h_spec num_id mc num_chan num_proc maxpage code pstart elf d = some d') (hP : PI d.toUData) :
    PI d'.toUData := by
  unfold sys_dispatch_h_spec at hs
  cases e1 : uctx_arg1_spec d.toUData with
  | none => rw [e1] at hs; cases hs
  | some a =>
    rw [e1] at hs; simp only at hs
    split at hs
    · unfold onU at hs
      cases hq : trap_proc_create_spec num_id mc num_chan code pstart elf d.toUData with
      | none => rw [hq] at hs; cases hs
      | some u => rw [hq] at hs; simp only [Option.some.injEq] at hs; rw [← hs]; exact pool_trap_create hnn hq hP
    · exact pool_of_qm hP (chain_kctxt hs) (chain_cidH hs) (chain_qm hA hs)

end

/-! ## The entry point with the lock -/

section Locked
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub elb mc kl kh
  pstart : Nat}
variable {elf : Nat → Nat} {code : Nat → Stmt KPrim} {lk : Val}

/-- **What holds of the full state each time the lock is released on the way
to user mode.** -/
def GoodH (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub elb mc kl kh
    pstart : Nat) (elf : Nat → Nat) (code : Nat → Stmt KPrim) (lk : Val) (d : HData) (b : Region) : Prop :=
  MatchHP maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub d b ∧
    MatchELF num_id elb elf b ∧ KInv num_id mc num_proc num_chan maxpage kl kh d.toUData ∧ d.ikern = false ∧
    PoolInv code pstart cidb ucb pb cpub num_proc num_chan lk d.toUData

local notation "GH" => GoodH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb cpub
  elb mc kl kh pstart elf code lk
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- **A system call of the full state, with the lock at the boundary.** -/
theorem syscall_h_locked {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c) (hc : c < NCPU)
    (hRA : LockArray.RelyA ε c) (entry : Nat → Nat) (tn : Nat) (hL : HL)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (hmax : 3 * maxpage < 2 ^ 32)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20) (hnn : num_id ≤ num_proc) (hnn' : num_proc ≤ num_id)
    (hnpc : num_proc ≤ num_chan) (hel0 : cb + 5 * num_id ≤ elb) (hec : elb + num_id ≤ cpub)
    (hov : num_id * mc + mc + 1 < 2 ^ 32) (hps : pstart < 2 ^ 32)
    (hentry : code (entry tn) =
      lockedK (sysEntryHK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart maxpage pb fb sb ob xb vb eb ipb cpub))
    {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) (hidle : (S.lk lk.toNat).phase c = .idle)
    (bound : ALog → Nat) (Kb : Nat) (hK : ∀ l, bound l ≤ Kb)
    (hF : LockArray.FairA ε c lk.toNat (ticket (LockArray.projL lk.toNat (apull ε c (erase l)))) bound)
    {pool : Nat → KCtx} (hRJ : RelyJ εR c lk.toNat (fun b => ∃ d, GH d b ∧ d.kctxt = pool))
    (hJ : ∃ d, GH d (hmemR lk.toNat H) ∧ d.kctxt = pool) (ur0 : Nat → Val) (σ : Locals) (hσ : σ "lk" = lk) :
    ∃ H1 : HLogR, (∃ d, GH d (hmemR lk.toNat H1) ∧ d.kctxt = pool) ∧
      ∀ (d d2 : HData) (u1 u3 : UData) (rs rs' : UContext), GH d (hmemR lk.toNat H1) → d.kctxt = pool →
        (∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) → proc_exit_user_spec rs d.toUData = some u1 →
        sys_dispatch_h_spec num_id mc num_chan num_proc maxpage code pstart elf { d with toUData := u1 } = some d2 →
        proc_start_user_spec d2.toUData = some (u3, rs') →
        ∃ (ur : Nat → Val) (l' : RLog) (S' : RState) (H' : HLogR),
          UStar εR c code entry lk (.user ur0 pool l) (.user ur u3.kctxt l') ∧
          rreplay l' = some (S', H') ∧ (S'.lk lk.toNat).phase c = .idle ∧
          GH { d2 with toUData := u3 } (hmemR lk.toNat H') ∧ ∀ n, n < 17 → ∀ v, rs' n = some v → ur n = v := by
  obtain ⟨σ1, r1, H1, hacq, hcs1, hJ1, hlk1, hfr⟩ :=
    acquire_runs_inv hE hRR hc hRA hl hRJ hJ hidle bound Kb hK hF σ hσ
  refine ⟨H1, hJ1, fun d d2 u1 u3 rs rs' hG hpool hrs h1 h2 h3 => ?_⟩
  obtain ⟨hM, hE1, hI, hik, hP⟩ := hG
  have hrs1 : ∀ n, n < 17 → ∀ v, rs n = some v → σ1 (ureg n) = v := fun n hn v hv => by
    obtain ⟨a, b', c', e⟩ := TLock.ureg_ne n hn
    rw [hfr _ a b' c' e]; exact hrs n hn v hv
  obtain ⟨σ', l', b', hks, hcs', hM', hE', hreg, hlk'⟩ := syscall_h_run εR c lk.toNat code hL hcp0 hcp1 hmax hnum
    hmp hnn hnn' hnpc hel0 hec hov hps (kl := kl) (kh := kh) (σ := σ1) (K := relK) (by rw [hlk1]) hcs1 hM hE1 hI
    hrs1 h1 h2 h3
  obtain ⟨rb, S3, H3, hrel, hl3, hid3, hmem⟩ := release_runs (εR := εR) hRR hc hcs' (hlk'.trans hlk1)
  have I1 := exit_keeps h1 hI
  obtain ⟨I3, hik3⟩ := start_keeps h3 (dispatch_h_keeps hnn h2 I1)
  have P3 := pool_start h3 (pool_dispatch_h hnn I1.ainv h2 (pool_exit h1 hP))
  refine ⟨regsOf (σ'.set "_" 0), rb, S3, H3, ?_, hl3, hid3,
    ⟨by rw [hmem]; exact hM', by rw [hmem]; exact hE', I3, hik3, P3⟩, fun n hn v hv => ?_⟩
  · refine .step (.trap ur0 pool l tn σ hσ) ?_
    rw [hentry, ← hpool]
    exact UStar.iret ((kstar_seq hacq _ .stop d.kctxt).trans ((KStar.single (kstep_seq _ _ .stop σ1 d.kctxt r1)).trans
      (hks.trans ((KStar.single (kstep_skip_seq _ .stop σ' u3.kctxt l')).trans (kstar_base hrel .stop u3.kctxt)))))
  · show (σ'.set "_" 0) (ureg n) = v
    rw [Locals.set_other _ _ (TLock.ureg_ne n hn).2.2.1]; exact hreg n hn v hv

end Locked

end TTop
