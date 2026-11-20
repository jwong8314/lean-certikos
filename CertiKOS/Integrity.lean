import CertiKOS.ObsEq

/-!
# mCertiKOS security: integrity, ported

Ported from `security/Integrity.v` (Costanzo, Shao, Gu, PLDI'16, section 5).

**Integrity**: while process `i` is not running, nothing the running process
does in the kernel changes what `i` observes. The proof goes specification by
specification, as mCertiKOS's does.

* `ObsEq.inactive`: for an observer that is not running before or after, the
  observation depends only on its page table, the memory it maps, its
  container, its kernel context and its user context.
* `integ_uctx_set_reg`, `integ_trap_get_quota`, `integ_proc_create`,
  `integ_trap_proc_create`, `integ_sys_dispatch_c`: the system calls.
* `PFrame`, `ptResv_frame`: what `pt_resv` for process `n` leaves alone: the
  other processes' page tables and containers, and the type and contents of
  every page that was not free. `integ_ptfault_resv`: the page-fault handler.
* `integ_proc_exit_user`, `integ_proc_start_user`, `integ_thread_yield`: the
  mode switches and the scheduler.
* `integrity_syscall`, `integrity_pgf`, `integrity_yield`: **integrity for
  the three entry points of the kernel.**

What is assumed, as in mCertiKOS (`high_level_invariant`, `secure_inv`): the
container pool is valid, the observer's container is in use, and the pages
the observer maps are not free (`MappedUsed`). The last one is what makes a
fresh page for another process invisible to the observer; here it is a
hypothesis, in mCertiKOS it follows from the owner lists.

What differs: integrity of user-mode instructions (`exec_loadex`,
`exec_storeex`) is not here, because user code is not modelled. Shared memory
and printing are not ported, so neither is their integrity.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Security

open ClightL
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt PProc TTrap TSysCall

variable {i : Nat}

/-! ## An observer that is not running -/

theorem vread_congr {v : Nat} {ptp ptp' : PMapPool} {hp hp' : Nat → Option Val} (h1 : ptp' i = ptp i)
    (h2 : ∀ pte pi p, ptp i (PDX v) = .PDEValid pi pte → ∀ w, pte (PTX v) = .PTEValid w p →
      hp' (w * 1024 + v % 4096 / 4) = hp (w * 1024 + v % 4096 / 4)) :
    vread i v ptp' hp' = vread i v ptp hp := by
  unfold vread
  rw [h1]
  split
  · cases hp1 : ptp i (PDX v) with
    | PDEValid pi pte =>
      simp only
      cases hp2 : pte (PTX v) with
      | PTEValid w p => simp only; rw [h2 pte pi p hp1 w hp2]
      | PTEUnPresent => rfl
      | PTEUndef => rfl
    | PDEID => rfl
    | PDEUnPresent => rfl
    | PDEUndef => rfl
  · rfl

theorem vread_perm_congr {v : Nat} {ptp ptp' : PMapPool} {pp pp' : Nat → PPgInfo} (h1 : ptp' i = ptp i)
    (h2 : ∀ pte pi p, ptp i (PDX v) = .PDEValid pi pte → ∀ w, pte (PTX v) = .PTEValid w p → pp' w = pp w) :
    vread_perm i v ptp' pp' = vread_perm i v ptp pp := by
  unfold vread_perm
  rw [h1]
  split
  · cases hp1 : ptp i (PDX v) with
    | PDEValid pi pte =>
      simp only
      cases hp2 : pte (PTX v) with
      | PTEValid w p => simp only; rw [h2 pte pi p hp1 w hp2]
      | PTEUnPresent => rfl
      | PTEUndef => rfl
    | PDEID => rfl
    | PDEUnPresent => rfl
    | PDEUndef => rfl
  · rfl

/-- **An observer that is not running** sees the same thing in two states that
agree on its page table, the pages it maps, its container, and its two
contexts. -/
theorem ObsEq.inactive {d d' : UData} (hi : i ≠ d.cid) (hi' : i ≠ d'.cid) (hpt : d'.ptpool i = d.ptpool i)
    (hmem : ∀ v pte pi p, d.ptpool i (PDX v) = .PDEValid pi pte → ∀ w, pte (PTX v) = .PTEValid w p →
      d'.HP (w * 1024 + v % 4096 / 4) = d.HP (w * 1024 + v % 4096 / 4) ∧ d'.pperm w = d.pperm w)
    (hAC : d'.AC i = d.AC i) (hk : d'.kctxt i = d.kctxt i) (hu : d'.uctxt i = d.uctxt i) : ObsEq i d d' :=
  ⟨fun v => (vread_congr hpt (fun pte pi p h1 w h2 => (hmem v pte pi p h1 w h2).1)).symm,
    fun v => (vread_perm_congr hpt (fun pte pi p h1 w h2 => (hmem v pte pi p h1 w h2).2)).symm,
    by rw [hAC], by rw [hAC], by rw [hAC], ⟨fun e => absurd e hi, fun e => absurd e hi'⟩, hk.symm, hu.symm,
    fun e => absurd e hi, fun e => absurd e hi, fun e => absurd e hi, fun e => absurd e hi,
    fun e => absurd e hi⟩

/-- The same, when memory and the page tables did not change at all. -/
theorem ObsEq.inactive_same {d d' : UData} (hi : i ≠ d.cid) (hi' : i ≠ d'.cid) (hpt : d'.ptpool = d.ptpool)
    (hHP : d'.HP = d.HP) (hpp : d'.pperm = d.pperm) (hAC : d'.AC i = d.AC i) (hk : d'.kctxt i = d.kctxt i)
    (hu : d'.uctxt i = d.uctxt i) : ObsEq i d d' :=
  ObsEq.inactive hi hi' (by rw [hpt]) (fun _ _ _ _ _ _ _ => ⟨by rw [hHP], by rw [hpp]⟩) hAC hk hu

/-! ## System-call arguments and results -/

theorem set_reg_cid {reg n : Nat} {d d' : UData} (h : uctx_set_reg_spec reg n d = some d') : d'.cid = d.cid := by
  obtain ⟨U, e⟩ := set_reg_shape h
  rw [e]

/-- Integrity for `uctx_set_errno` and `uctx_set_retvalN`. -/
theorem integ_uctx_set_reg {reg n : Nat} {d d' : UData} (h : uctx_set_reg_spec reg n d = some d')
    (hi : i ≠ d.cid) : ObsEq i d d' := by
  unfold uctx_set_reg_spec at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ObsEq.inactive_same hi hi rfl rfl rfl rfl rfl (setAt_ne _ _ hi)
  · cases h

/-- Integrity for `sys_get_quota`. -/
theorem integ_trap_get_quota {d d' : UData} (h : trap_get_quota_spec d = some d') (hi : i ≠ d.cid) :
    ObsEq i d d' := by
  unfold trap_get_quota_spec at h
  repeat' split at h
  all_goals first
    | cases h
    | (rename_i d1 h1
       exact (integ_uctx_set_reg h1 hi).trans (integ_uctx_set_reg h (by rw [set_reg_cid h1]; exact hi)))

/-! ## Spawning a process -/

/-- Integrity for `proc_create`. The observer's container is in use, so the
observer is not the child, whose slot was free. -/
theorem integ_proc_create {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart uentry q : Nat}
    {d d' : UData} {r : Nat} (hCV : Container_valid num_id mc d.AC) (hcu : (d.AC d.cid).cused = true)
    (hiu : (d.AC i).cused = true)
    (h : proc_create_spec num_id mc num_chan code pstart uentry q d = some (d', r)) (hi : i ≠ d.cid) :
    ObsEq i d d' := by
  unfold proc_create_spec at h
  simp only at h
  split at h
  · rename_i hc
    have hfree := split_child_free hCV hcu hc.2.2.2.2.2.1
    have hne : i ≠ d.cid * mc + 1 + (d.AC d.cid).cchildren.length := fun e => by
      rw [← e, hiu] at hfree; cases hfree
    cases habq : d.abq num_chan with
    | AbQUndef => rw [habq] at h; cases h
    | AbQValid l =>
      rw [habq] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hd, -⟩ := h
      subst hd
      exact ObsEq.inactive_same hi hi rfl rfl rfl ((setAt_ne _ _ hne).trans (setAt_ne _ _ hi))
        (setAt_ne _ _ hne) (setAt_ne _ _ hne)
  · cases h

/-- Integrity for `sys_proc_create`. -/
theorem integ_trap_proc_create {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat}
    {elf : Nat → Nat} {d d' : UData} (hCV : Container_valid num_id mc d.AC)
    (hcu : (d.AC d.cid).cused = true) (hiu : (d.AC i).cused = true)
    (h : trap_proc_create_spec num_id mc num_chan code pstart elf d = some d') (hi : i ≠ d.cid) :
    ObsEq i d d' := by
  unfold trap_proc_create_spec at h
  cases e3 : uctx_arg3_spec d with
  | none => rw [e3] at h; cases h
  | some q =>
    rw [e3] at h
    simp only at h
    by_cases h1 : q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota
    · rw [if_pos h1] at h
      by_cases h2 : d.cid * mc + 1 + mc ≤ num_id
      · rw [if_pos h2] at h
        by_cases h3 : (d.AC d.cid).cchildren.length < mc
        · rw [if_pos h3] at h
          cases e2 : uctx_arg2_spec d with
          | none => rw [e2] at h; cases h
          | some a1 =>
            rw [e2] at h
            simp only at h
            by_cases ha : a1 < num_id
            · rw [if_pos ha] at h
              cases hpc : proc_create_spec num_id mc num_chan code pstart (elf a1) q d with
              | none => rw [hpc] at h; cases h
              | some pr =>
                obtain ⟨d1, n⟩ := pr
                rw [hpc] at h
                simp only at h
                cases hr1 : uctx_set_retval1_spec n d1 with
                | none => rw [hr1] at h; cases h
                | some d2 =>
                  rw [hr1] at h
                  simp only at h
                  have c1 : d1.cid = d.cid := proc_create_cid hpc
                  have c2 : d2.cid = d1.cid := set_reg_cid hr1
                  exact ((integ_proc_create hCV hcu hiu hpc hi).trans
                    (integ_uctx_set_reg hr1 (by rw [c1]; exact hi))).trans
                    (integ_uctx_set_reg h (by rw [c2, c1]; exact hi))
            · rw [if_neg ha] at h; cases h
        · rw [if_neg h3] at h; exact integ_uctx_set_reg h hi
      · rw [if_neg h2] at h; exact integ_uctx_set_reg h hi
    · rw [if_neg h1] at h; exact integ_uctx_set_reg h hi

/-- Integrity for the system-call dispatcher. -/
theorem integ_sys_dispatch_c {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat}
    {elf : Nat → Nat} {d d' : UData} (hCV : Container_valid num_id mc d.AC)
    (hcu : (d.AC d.cid).cused = true) (hiu : (d.AC i).cused = true)
    (h : sys_dispatch_c_spec num_id mc num_chan code pstart elf d = some d') (hi : i ≠ d.cid) :
    ObsEq i d d' := by
  unfold sys_dispatch_c_spec at h
  cases e1 : uctx_arg1_spec d with
  | none => rw [e1] at h; cases h
  | some a =>
    rw [e1] at h
    simp only at h
    by_cases h2 : a = 2
    · rw [if_pos h2] at h; exact integ_trap_proc_create hCV hcu hiu h hi
    · rw [if_neg h2] at h
      by_cases h26 : a = 26
      · rw [if_pos h26] at h; exact integ_trap_get_quota h hi
      · rw [if_neg h26] at h; exact integ_uctx_set_reg h hi

/-! ## The page-fault handler -/

/-- Page `v` is not free. -/
def NotFree (AT : ATable) (v : Nat) : Prop := ∀ c, AT v ≠ .ATValid false .ATNorm c

theorem notFree_set {AT : ATable} {v padr c0 : Nat} (hv : NotFree AT v) :
    NotFree (setAt AT padr (.ATValid true .ATNorm c0)) v := by
  intro c
  by_cases e : v = padr
  · rw [e, setAt_eq]; intro h; cases h
  · rw [setAt_ne _ _ e]; exact hv c

/-- **What an operation on process `n`'s memory leaves alone**: the other
processes' page tables and containers, and the type and contents of every
page that was not free. -/
structure PFrame (n : Nat) (d d' : PTData) : Prop where
  other : ∀ j, j ≠ n → d'.ptpool j = d.ptpool j ∧ d'.AC j = d.AC j
  used : ∀ v, NotFree d.AT v →
    d'.pperm v = d.pperm v ∧ (∀ a, a / 1024 = v → d'.HP a = d.HP a) ∧ NotFree d'.AT v
  flags : d'.pg = d.pg ∧ d'.ipt = d.ipt ∧ d'.init = d.init

theorem PFrame.refl (n : Nat) (d : PTData) : PFrame n d d :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ hv => ⟨rfl, fun _ _ => rfl, hv⟩, rfl, rfl, rfl⟩

theorem PFrame.trans {n : Nat} {d1 d2 d3 : PTData} (h1 : PFrame n d1 d2) (h2 : PFrame n d2 d3) :
    PFrame n d1 d3 := by
  refine ⟨fun j hj => ⟨((h2.other j hj).1).trans (h1.other j hj).1, ((h2.other j hj).2).trans (h1.other j hj).2⟩,
    fun v hv => ?_, h2.flags.1.trans h1.flags.1, h2.flags.2.1.trans h1.flags.2.1,
    h2.flags.2.2.trans h1.flags.2.2⟩
  obtain ⟨a1, a2, a3⟩ := h1.used v hv
  obtain ⟨b1, b2, b3⟩ := h2.used v a3
  exact ⟨b1.trans a1, fun a ha => (b2 a ha).trans (a2 a ha), b3⟩

theorem alloc_frame {n : Nat} {d : PTData} {r1 : RData} {b : Nat}
    (h : container_alloc_spec n d.toRData = some (r1, b)) : PFrame n d { d with toRData := r1 } := by
  unfold container_alloc_spec at h
  simp only at h
  split at h
  · split at h
    · cases hff : first_free d.AT d.nps with
      | none => rw [hff] at h; cases h
      | some pi =>
        rw [hff] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨-, -, ⟨c0, hc0⟩, -⟩ := first_free_some hff
        refine ⟨fun j hj => ⟨rfl, setAt_ne _ _ hj⟩, fun v hv => ?_, rfl, rfl, rfl⟩
        have hne : v ≠ pi := fun e => hv c0 (e ▸ hc0)
        exact ⟨setAt_ne _ _ hne, fun _ _ => rfl, notFree_set hv⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact PFrame.refl _ _
  · cases h

theorem insertPTE_frame {n vadr padr : Nat} {p : PTPerm} {d d' : PTData}
    (h : ptInsertPTE_spec n vadr padr p d = some d') : PFrame n d d' := by
  unfold ptInsertPTE_spec at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq] at h
       subst h
       exact ⟨fun j hj => ⟨setAt_ne _ _ hj, rfl⟩, fun v hv => ⟨rfl, fun _ _ => rfl, notFree_set hv⟩,
         rfl, rfl, rfl⟩)
    | cases h

theorem allocPDE_frame {np n vadr : Nat} {d d' : PTData} {v : Nat}
    (h : ptAllocPDE_spec np n vadr d = some (d', v)) : PFrame n d d' := by
  unfold ptAllocPDE_spec at h
  simp only at h
  split at h
  · split at h
    · cases h
    · cases hp : d.ptpool n (PDX vadr) with
      | PDEUnPresent =>
        rw [hp] at h
        simp only at h
        split at h
        · cases hff : first_free d.AT d.nps with
          | none => rw [hff] at h; cases h
          | some pi =>
            rw [hff] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            obtain ⟨-, -, ⟨c0, hc0⟩, -⟩ := first_free_some hff
            refine ⟨fun j hj => ⟨setAt_ne _ _ hj, setAt_ne _ _ hj⟩, fun w hw => ?_, rfl, rfl, rfl⟩
            have hne : w ≠ pi := fun e => hw c0 (e ▸ hc0)
            refine ⟨setAt_ne _ _ hne, fun a ha => ?_, notFree_set hw⟩
            show free_page pi d.HP a = d.HP a
            unfold free_page
            rw [if_neg (by rw [ha]; exact hne)]
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact PFrame.refl _ _
      | PDEValid _ _ => rw [hp] at h; cases h
      | PDEID => rw [hp] at h; cases h
      | PDEUndef => rw [hp] at h; cases h
  · cases h

theorem insert_frame {mp np n vadr padr perm : Nat} {d d' : PTData} {r : Nat}
    (h : ptInsert_spec mp np n vadr padr perm d = some (d', r)) : PFrame n d d' := by
  unfold ptInsert_spec at h
  split at h
  · cases hz : ZtoPerm perm with
    | none => rw [hz] at h; cases h
    | some p =>
      rw [hz] at h
      simp only at h
      cases hp : d.ptpool n (PDX vadr) with
      | PDEValid pi pte =>
        rw [hp] at h
        simp only at h
        cases hi : ptInsertPTE_spec n vadr padr p d with
        | none => rw [hi] at h; cases h
        | some d1 =>
          rw [hi] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact insertPTE_frame hi
      | PDEUnPresent =>
        rw [hp] at h
        simp only at h
        cases ha : ptAllocPDE_spec np n vadr d with
        | none => rw [ha] at h; cases h
        | some pr =>
          obtain ⟨d1, v⟩ := pr
          rw [ha] at h
          simp only at h
          by_cases hv : v = 0
          · rw [if_pos hv] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact allocPDE_frame ha
          · rw [if_neg hv] at h
            cases hi : ptInsertPTE_spec n vadr padr p d1 with
            | none => rw [hi] at h; cases h
            | some d2 =>
              rw [hi] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              exact (allocPDE_frame ha).trans (insertPTE_frame hi)
      | PDEID => rw [hp] at h; cases h
      | PDEUndef => rw [hp] at h; cases h
  · cases h

/-- **What `pt_resv` leaves alone.** -/
theorem ptResv_frame {mp np n vadr perm : Nat} {d d' : PTData} {r : Nat}
    (h : ptResv_spec mp np n vadr perm d = some (d', r)) : PFrame n d d' := by
  unfold ptResv_spec at h
  cases hA : container_alloc_spec n d.toRData with
  | none => rw [hA] at h; cases h
  | some pr =>
    obtain ⟨r1, b⟩ := pr
    rw [hA] at h
    simp only at h
    by_cases hb : b = 0
    · rw [if_pos hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact PFrame.refl _ _
    · rw [if_neg hb] at h
      exact (alloc_frame hA).trans (insert_frame h)

/-- The pages process `i` maps are not free. -/
def MappedUsed (i : Nat) (d : PTData) : Prop :=
  ∀ j pi pte, d.ptpool i j = .PDEValid pi pte → ∀ k w p, pte k = .PTEValid w p → NotFree d.AT w

/-- Integrity for the page-fault handler: a fresh page for the faulting
process is none of the pages the observer maps. -/
theorem integ_ptfault_resv {mp np vadr : Nat} {d d' : UData} (hmu : MappedUsed i d.toPTData)
    (h : ptfault_resv_spec mp np vadr d = some d') (hi : i ≠ d.cid) : ObsEq i d d' := by
  unfold ptfault_resv_spec at h
  split at h
  · split at h
    · cases hp : ptResv_spec mp np d.cid vadr 7 d.toPTData with
      | none => rw [hp] at h; cases h
      | some pr =>
        obtain ⟨p, r⟩ := pr
        rw [hp] at h
        simp only [Option.some.injEq] at h
        subst h
        have hf := ptResv_frame hp
        refine ObsEq.inactive hi hi (hf.other i hi).1 (fun v pte pi pm h1 w h2 => ?_) (hf.other i hi).2 rfl rfl
        obtain ⟨a1, a2, -⟩ := hf.used w (hmu _ pi pte h1 _ w pm h2)
        exact ⟨a2 _ (by omega), a1⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ObsEq.refl _ _
  · cases h

/-! ## The mode switches and the scheduler -/

/-- Integrity for `proc_exit_user`. -/
theorem integ_proc_exit_user {rs : UContext} {d d' : UData} (h : proc_exit_user_spec rs d = some d')
    (hi : i ≠ d.cid) : ObsEq i d d' := by
  obtain ⟨hd, -⟩ := exit_shape h
  subst hd
  exact ObsEq.inactive_same hi hi rfl rfl rfl rfl rfl (setAt_ne _ _ hi)

/-- Integrity for `proc_start_user`. -/
theorem integ_proc_start_user {rs : UContext} {d d' : UData} (h : proc_start_user_spec d = some (d', rs))
    (hi : i ≠ d.cid) : ObsEq i d d' := by
  obtain ⟨hd, -, -⟩ := start_shape h
  subst hd
  exact ObsEq.inactive_same hi hi rfl rfl rfl rfl rfl rfl

/-- Integrity for `thread_yield`, when the observer is neither the process
that yields nor the one that is resumed. -/
theorem integ_thread_yield {nc la : Nat} {ql : List Nat} {rs : KCtx} {d : UData} (hi : i ≠ d.cid)
    (hla : i ≠ la) : ObsEq i d (putK d (yieldOut nc la ql rs (toK d))) :=
  ObsEq.inactive_same hi hla rfl rfl rfl rfl (setAt_ne _ _ hi) rfl

/-! ## The three entry points -/

/-- **Integrity of a system call.** -/
theorem integrity_syscall {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
    {d d1 d2 d3 : UData} {rs rs' : UContext} (hCV : Container_valid num_id mc d.AC)
    (hcu : (d.AC d.cid).cused = true) (hiu : (d.AC i).cused = true)
    (h1 : proc_exit_user_spec rs d = some d1)
    (h2 : sys_dispatch_c_spec num_id mc num_chan code pstart elf d1 = some d2)
    (h3 : proc_start_user_spec d2 = some (d3, rs')) (hi : i ≠ d.cid) : ObsEq i d d3 := by
  obtain ⟨hd1, -⟩ := exit_shape h1
  have hi1 : i ≠ d1.cid := by rw [hd1]; exact hi
  have e2 := integ_sys_dispatch_c (i := i) (by rw [hd1]; exact hCV) (by rw [hd1]; exact hcu)
    (by rw [hd1]; exact hiu) h2 hi1
  have hi2 : i ≠ d2.cid := fun e => hi1 (e2.hcid.2 e)
  exact ((integ_proc_exit_user h1 hi).trans e2).trans (integ_proc_start_user h3 hi2)

/-- **Integrity of a page fault.** -/
theorem integrity_pgf {mp np vadr : Nat} {d d1 d2 d3 : UData} {rs rs' : UContext}
    (hmu : MappedUsed i d.toPTData) (h1 : proc_exit_user_spec rs d = some d1)
    (h2 : ptfault_resv_spec mp np vadr d1 = some d2) (h3 : proc_start_user_spec d2 = some (d3, rs'))
    (hi : i ≠ d.cid) : ObsEq i d d3 := by
  obtain ⟨hd1, -⟩ := exit_shape h1
  have hi1 : i ≠ d1.cid := by rw [hd1]; exact hi
  have e2 := integ_ptfault_resv (i := i) (by rw [hd1]; exact hmu) h2 hi1
  have hi2 : i ≠ d2.cid := fun e => hi1 (e2.hcid.2 e)
  exact ((integ_proc_exit_user h1 hi).trans e2).trans (integ_proc_start_user h3 hi2)

/-- **Integrity of a yield**, for an observer that is neither process. -/
theorem integrity_yield {nc la : Nat} {ql : List Nat} {rsK : KCtx} {d d1 : UData} {rs : UContext}
    (h1 : proc_exit_user_spec rs d = some d1) (hi : i ≠ d.cid) (hla : i ≠ la) :
    ObsEq i d (putK d1 (yieldOut nc la ql rsK (toK d1))) := by
  obtain ⟨hd1, -⟩ := exit_shape h1
  exact (integ_proc_exit_user h1 hi).trans (integ_thread_yield (by rw [hd1]; exact hi) hla)

end Security
