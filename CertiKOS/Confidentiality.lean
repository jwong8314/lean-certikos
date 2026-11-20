import CertiKOS.Integrity

/-!
# mCertiKOS security: confidentiality, ported (system calls and the scheduler)

Ported from `security/Confidentiality.v` (Costanzo, Shao, Gu, PLDI'16,
section 5).

**Confidentiality**: what the running process `i` observes after a passage
through the kernel depends only on what it observed before. Two states that
`i` cannot tell apart stay that way, and the registers the kernel returns are
the same.

The proofs here go through a stronger statement than mCertiKOS's: for each
specification, the observation after is a *function* of the observation
before (`obs_set_reg`, `obs_get_quota`, `obs_proc_create`,
`obs_trap_proc_create`, `obs_dispatch`, `obs_exit_user`, `obs_start_user`,
`obs_yield`). The functions (`obsSetReg`, `obsCreate`, `obsDispatch`, …) are
the kernel as the process sees it. Confidentiality in mCertiKOS's form, with
two runs, follows by applying the function to equal observations.

* `conf_uctx_arg`, `conf_uctx_set_reg`, `conf_trap_get_quota`,
  `conf_proc_create`, `conf_trap_proc_create`, `conf_sys_dispatch_c`,
  `conf_proc_exit_user`, `conf_proc_start_user`, `conf_thread_yield`: the
  lemmas of `Confidentiality.v`.
* `obs_syscall`, `confidentiality_syscall`: **confidentiality of a system
  call**, from the trap to the return, with equal registers returned.
* `confidentiality_yield`: **of a yield**: afterwards the process is parked
  and observes the same in both states, whoever was resumed.

* `conf_thread_yield_restore`, `confidentiality_restore`: **when a parked
  process is resumed** (`ConfidentialityRestore.v`). Two states it could not
  tell apart while parked: once resumed it still cannot, and it resumes the
  same kernel computation.

The page-fault handler is in `ConfidentialityPF.lean`. Not ported: user-mode
instructions, which are not modelled.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Security

open ClightL
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt PProc TTrap TSysCall

variable {i : Nat}

theorem MyObs.ext13 {a b : MyObs} (h1 : a.observe_HP = b.observe_HP) (h2 : a.observe_perm = b.observe_perm)
    (h3 : a.observe_AC_quota = b.observe_AC_quota) (h4 : a.observe_AC_nchildren = b.observe_AC_nchildren)
    (h5 : a.observe_AC_used = b.observe_AC_used) (h6 : a.observe_cid = b.observe_cid)
    (h7 : a.observe_kctxt = b.observe_kctxt) (h8 : a.observe_uctxt = b.observe_uctxt)
    (h9 : a.observe_ikern = b.observe_ikern) (h10 : a.observe_ihost = b.observe_ihost)
    (h11 : a.observe_pg = b.observe_pg) (h12 : a.observe_ipt = b.observe_ipt)
    (h13 : a.observe_init = b.observe_init) : a = b := by
  cases a; cases b
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7; subst h8; subst h9; subst h10
  subst h11; subst h12; subst h13
  rfl

/-- The running process is the observer. -/
theorem obs_running {d : UData} (hi : i = d.cid) : (observe i d).observe_cid = true := by
  show decide (i = d.cid) = true
  exact decide_eq_true hi

theorem running_of_obs {d : UData} (h : (observe i d).observe_cid = true) : i = d.cid :=
  of_decide_eq_true h

/-! ## The kernel as the running process sees it -/

/-- Writing one of its registers. -/
def obsSetReg (reg n : Nat) (o : MyObs) : MyObs :=
  { o with observe_uctxt := setAt o.observe_uctxt reg (some (BitVec.ofNat 32 n)) }

/-- `sys_get_quota`. -/
def obsGetQuota (o : MyObs) : MyObs := obsSetReg U_EAX E_SUCC (obsSetReg U_EBX o.observe_AC_quota.toNat o)

/-- `proc_create` with quota `q`: less quota, one more child. -/
def obsCreate (q : Nat) (o : MyObs) : MyObs :=
  { o with observe_AC_quota := o.observe_AC_quota - q, observe_AC_nchildren := o.observe_AC_nchildren + 1 }

/-- `sys_proc_create`. -/
def obsTrapCreate (num_id mc i : Nat) (o : MyObs) : MyObs :=
  match o.observe_uctxt U_ECX with
  | some q =>
    if (q.toNat : Int) ≤ o.observe_AC_quota ∧ i * mc + 1 + mc ≤ num_id ∧ o.observe_AC_nchildren < mc then
      obsSetReg U_EAX E_SUCC (obsSetReg U_EBX (i * mc + 1 + o.observe_AC_nchildren) (obsCreate q.toNat o))
    else obsSetReg U_EAX E_MEM o
  | none => o

/-- `syscall_dispatch_c`. -/
def obsDispatch (num_id mc i : Nat) (o : MyObs) : MyObs :=
  match o.observe_uctxt U_EAX with
  | some a =>
    if a.toNat = 2 then obsTrapCreate num_id mc i o
    else if a.toNat = 26 then obsGetQuota o
    else obsSetReg U_EAX E_INVAL_CALLNR o
  | none => o

/-- `proc_exit_user`: the registers of the trap are saved; kernel mode. -/
def obsExit (rs : UContext) (o : MyObs) : MyObs :=
  { o with observe_uctxt := rs, observe_ikern := some true, observe_ipt := some true }

/-- `proc_start_user`: user mode. -/
def obsStart (o : MyObs) : MyObs := { o with observe_ikern := some false, observe_ipt := some false }

/-- `thread_yield`: no longer running; the kernel context is the one parked. -/
def obsYield (rsK : KCtx) (o : MyObs) : MyObs :=
  { o with observe_cid := false, observe_kctxt := rsK, observe_ikern := none, observe_ihost := none,
           observe_pg := none, observe_ipt := none, observe_init := none }

/-! ## Each specification, on the observation -/

theorem obs_set_reg {reg n : Nat} {d d' : UData} (h : uctx_set_reg_spec reg n d = some d') (hi : i = d.cid) :
    observe i d' = obsSetReg reg n (observe i d) := by
  unfold uctx_set_reg_spec at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h; subst hi
    unfold observe obsSetReg
    simp only [setAt_eq]
  · cases h

/-- An argument is a register the process observes. -/
theorem obs_arg {reg r : Nat} {d : UData} (h : uctx_arg_spec reg d = some r) (hi : i = d.cid) :
    (observe i d).observe_uctxt reg = some (BitVec.ofNat 32 r) ∧ r < 2 ^ 32 := by
  subst hi
  exact arg_val h

theorem obs_get_quota {d d' : UData} (h : trap_get_quota_spec d = some d') (hi : i = d.cid) :
    observe i d' = obsGetQuota (observe i d) := by
  unfold trap_get_quota_spec get_curid_spec container_get_quota_spec container_get_usage_spec at h
  by_cases hpg : d.pg = true
  · rw [if_pos hpg] at h
    simp only at h
    by_cases hu : (d.AC d.cid).cused = true
    · simp only [if_pos hu] at h
      cases h1 : uctx_set_retval1_spec ((d.AC d.cid).cquota - (d.AC d.cid).cusage) d with
      | none => rw [h1] at h; cases h
      | some d1 =>
        rw [h1] at h
        simp only at h
        rw [obs_set_reg h (hi.trans (set_reg_cid h1).symm), obs_set_reg h1 hi]
        unfold obsGetQuota
        have e : (observe i d).observe_AC_quota.toNat = (d.AC d.cid).cquota - (d.AC d.cid).cusage := by
          subst hi
          show (((d.AC d.cid).cquota : Int) - (d.AC d.cid).cusage).toNat = _
          omega
        rw [e]
    · simp only [if_neg hu] at h
      cases h
  · rw [if_neg hpg] at h; cases h

theorem obs_proc_create {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart uentry q : Nat}
    {d d' : UData} {r : Nat} (h : proc_create_spec num_id mc num_chan code pstart uentry q d = some (d', r))
    (hi : i = d.cid) :
    observe i d' = obsCreate q (observe i d) ∧ r = i * mc + 1 + (observe i d).observe_AC_nchildren := by
  unfold proc_create_spec at h
  simp only at h
  split at h
  · rename_i hc
    have hmul : d.cid ≤ d.cid * mc := Nat.le_mul_of_pos_right _ (by omega)
    have hne : d.cid ≠ d.cid * mc + 1 + (d.AC d.cid).cchildren.length := by omega
    cases habq : d.abq num_chan with
    | AbQUndef => rw [habq] at h; cases h
    | AbQValid l =>
      rw [habq] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hd, hr⟩ := h
      subst hd; subst hr; subst hi
      refine ⟨?_, rfl⟩
      apply MyObs.ext13
      · rfl
      · rfl
      · show ((setAt (setAt d.AC d.cid _) _ _ d.cid).cquota : Int) - (setAt (setAt d.AC d.cid _) _ _ d.cid).cusage =
          ((d.AC d.cid).cquota : Int) - (d.AC d.cid).cusage - q
        rw [setAt_ne _ _ hne, setAt_eq]
        show ((d.AC d.cid).cquota : Int) - ((d.AC d.cid).cusage + q : Nat) = _
        omega
      · show (setAt (setAt d.AC d.cid _) _ _ d.cid).cchildren.length = (d.AC d.cid).cchildren.length + 1
        rw [setAt_ne _ _ hne, setAt_eq]
        rfl
      · show (setAt (setAt d.AC d.cid _) _ _ d.cid).cused = (d.AC d.cid).cused
        rw [setAt_ne _ _ hne, setAt_eq]
      · rfl
      · show setAt d.kctxt _ _ d.cid = d.kctxt d.cid
        rw [setAt_ne _ _ hne]
      · show setAt d.uctxt _ _ d.cid = d.uctxt d.cid
        rw [setAt_ne _ _ hne]
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  · cases h

theorem obs_trap_proc_create {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat}
    {elf : Nat → Nat} {d d' : UData}
    (h : trap_proc_create_spec num_id mc num_chan code pstart elf d = some d') (hi : i = d.cid) :
    observe i d' = obsTrapCreate num_id mc i (observe i d) := by
  unfold trap_proc_create_spec at h
  cases e3 : uctx_arg3_spec d with
  | none => rw [e3] at h; cases h
  | some q =>
    rw [e3] at h
    simp only at h
    obtain ⟨ho3, hq32⟩ := obs_arg (i := i) e3 hi
    have hqn : (BitVec.ofNat 32 q : Val).toNat = q := MALInit.tn hq32
    have hquo : (observe i d).observe_AC_quota = ((d.AC d.cid).cquota : Int) - (d.AC d.cid).cusage := by
      subst hi; rfl
    have hnch : (observe i d).observe_AC_nchildren = (d.AC d.cid).cchildren.length := by subst hi; rfl
    unfold obsTrapCreate
    rw [show (observe i d).observe_uctxt U_ECX = some (BitVec.ofNat 32 q) from ho3]
    simp only
    rw [hqn]
    by_cases hall : q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota ∧ d.cid * mc + 1 + mc ≤ num_id ∧
        (d.AC d.cid).cchildren.length < mc
    · obtain ⟨h1, h2, h3⟩ := hall
      rw [if_pos h1, if_pos h2, if_pos h3] at h
      rw [if_pos ⟨by rw [hquo]; omega, by rw [hi]; exact h2, by rw [hnch]; exact h3⟩]
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
              obtain ⟨o1, hn⟩ := obs_proc_create (i := i) hpc hi
              rw [obs_set_reg h (by rw [c2, c1]; exact hi), obs_set_reg hr1 (by rw [c1]; exact hi), o1, hn]
        · rw [if_neg ha] at h; cases h
    · have hs' : uctx_set_errno_spec E_MEM d = some d' := by
        by_cases h1 : q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota
        · rw [if_pos h1] at h
          by_cases h2 : d.cid * mc + 1 + mc ≤ num_id
          · rw [if_pos h2] at h
            by_cases h3 : (d.AC d.cid).cchildren.length < mc
            · exact absurd ⟨h1, h2, h3⟩ hall
            · rw [if_neg h3] at h; exact h
          · rw [if_neg h2] at h; exact h
        · rw [if_neg h1] at h; exact h
      rw [if_neg (fun hc => hall ⟨by have := hc.1; rw [hquo] at this; omega, by have := hc.2.1; rw [hi] at this; exact this,
        by have := hc.2.2; rw [hnch] at this; exact this⟩)]
      exact obs_set_reg hs' hi

theorem obs_dispatch {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
    {d d' : UData} (h : sys_dispatch_c_spec num_id mc num_chan code pstart elf d = some d') (hi : i = d.cid) :
    observe i d' = obsDispatch num_id mc i (observe i d) := by
  unfold sys_dispatch_c_spec at h
  cases e1 : uctx_arg1_spec d with
  | none => rw [e1] at h; cases h
  | some a =>
    rw [e1] at h
    simp only at h
    obtain ⟨ho1, ha32⟩ := obs_arg (i := i) e1 hi
    unfold obsDispatch
    rw [show (observe i d).observe_uctxt U_EAX = some (BitVec.ofNat 32 a) from ho1]
    simp only
    rw [MALInit.tn ha32]
    by_cases h2 : a = 2
    · rw [if_pos h2] at h
      rw [if_pos h2]
      exact obs_trap_proc_create h hi
    · rw [if_neg h2] at h
      rw [if_neg h2]
      by_cases h26 : a = 26
      · rw [if_pos h26] at h
        rw [if_pos h26]
        exact obs_get_quota h hi
      · rw [if_neg h26] at h
        rw [if_neg h26]
        exact obs_set_reg h hi

theorem obs_exit_user {rs : UContext} {d d' : UData} (h : proc_exit_user_spec rs d = some d') (hi : i = d.cid) :
    observe i d' = obsExit rs (observe i d) := by
  obtain ⟨hd, -⟩ := exit_shape h
  subst hd; subst hi
  apply MyObs.ext13 <;> first
    | rfl
    | (show setAt d.uctxt d.cid rs d.cid = rs; exact setAt_eq _ _ _)
    | (show (if d.cid = d.cid then some true else none) = some true; exact if_pos rfl)

theorem obs_start_user {rs : UContext} {d d' : UData} (h : proc_start_user_spec d = some (d', rs))
    (hi : i = d.cid) : observe i d' = obsStart (observe i d) ∧ rs = (observe i d).observe_uctxt := by
  obtain ⟨hd, hr, -⟩ := start_shape h
  subst hd; subst hi
  refine ⟨?_, hr⟩
  apply MyObs.ext13 <;> first
    | rfl
    | (show (if d.cid = d.cid then some false else none) = some false; exact if_pos rfl)

theorem obs_yield {nc la : Nat} {ql : List Nat} {rsK : KCtx} {d : UData} (hi : i = d.cid) (hla : la ≠ d.cid) :
    observe i (putK d (yieldOut nc la ql rsK (toK d))) = obsYield rsK (observe i d) := by
  subst hi
  have hne : ¬ d.cid = la := fun e => hla e.symm
  apply MyObs.ext13 <;> first
    | rfl
    | (show decide (d.cid = la) = false; exact decide_eq_false hne)
    | (show setAt d.kctxt d.cid rsK d.cid = rsK; exact setAt_eq _ _ _)
    | (show (if d.cid = la then some _ else none) = none; exact if_neg hne)

/-! ## Confidentiality, lemma by lemma (`Confidentiality.v`) -/

theorem conf_uctx_arg {reg r1 r2 : Nat} {d1 d2 : UData} (h1 : uctx_arg_spec reg d1 = some r1)
    (h2 : uctx_arg_spec reg d2 = some r2) (hi : i = d1.cid) (h : ObsEq i d1 d2) : r1 = r2 := by
  obtain ⟨a1, b1⟩ := obs_arg (i := i) h1 hi
  obtain ⟨a2, b2⟩ := obs_arg (i := i) h2 (h.hcid.1 hi)
  rw [(obsEq_convert i d1 d2).1 h, a2] at a1
  exact (Layer.w32_inj b1 b2 (Option.some.inj a1).symm)

theorem conf_uctx_set_reg {reg n : Nat} {d1 d2 d1' d2' : UData} (h1 : uctx_set_reg_spec reg n d1 = some d1')
    (h2 : uctx_set_reg_spec reg n d2 = some d2') (hi : i = d1.cid) (h : ObsEq i d1 d2) : ObsEq i d1' d2' :=
  (obsEq_convert _ _ _).2 (by
    rw [obs_set_reg h1 hi, obs_set_reg h2 (h.hcid.1 hi), (obsEq_convert i d1 d2).1 h])

theorem conf_trap_get_quota {d1 d2 d1' d2' : UData} (h1 : trap_get_quota_spec d1 = some d1')
    (h2 : trap_get_quota_spec d2 = some d2') (hi : i = d1.cid) (h : ObsEq i d1 d2) : ObsEq i d1' d2' :=
  (obsEq_convert _ _ _).2 (by
    rw [obs_get_quota h1 hi, obs_get_quota h2 (h.hcid.1 hi), (obsEq_convert i d1 d2).1 h])

theorem conf_proc_create {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart u1 u2 q : Nat}
    {d1 d2 d1' d2' : UData} {r1 r2 : Nat}
    (h1 : proc_create_spec num_id mc num_chan code pstart u1 q d1 = some (d1', r1))
    (h2 : proc_create_spec num_id mc num_chan code pstart u2 q d2 = some (d2', r2)) (hi : i = d1.cid)
    (h : ObsEq i d1 d2) : ObsEq i d1' d2' ∧ r1 = r2 := by
  obtain ⟨a1, b1⟩ := obs_proc_create (i := i) h1 hi
  obtain ⟨a2, b2⟩ := obs_proc_create (i := i) h2 (h.hcid.1 hi)
  have e := (obsEq_convert i d1 d2).1 h
  exact ⟨(obsEq_convert _ _ _).2 (by rw [a1, a2, e]), by rw [b1, b2, e]⟩

theorem conf_trap_proc_create {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat}
    {elf : Nat → Nat} {d1 d2 d1' d2' : UData}
    (h1 : trap_proc_create_spec num_id mc num_chan code pstart elf d1 = some d1')
    (h2 : trap_proc_create_spec num_id mc num_chan code pstart elf d2 = some d2') (hi : i = d1.cid)
    (h : ObsEq i d1 d2) : ObsEq i d1' d2' :=
  (obsEq_convert _ _ _).2 (by
    rw [obs_trap_proc_create h1 hi, obs_trap_proc_create h2 (h.hcid.1 hi), (obsEq_convert i d1 d2).1 h])

theorem conf_sys_dispatch_c {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat}
    {elf : Nat → Nat} {d1 d2 d1' d2' : UData}
    (h1 : sys_dispatch_c_spec num_id mc num_chan code pstart elf d1 = some d1')
    (h2 : sys_dispatch_c_spec num_id mc num_chan code pstart elf d2 = some d2') (hi : i = d1.cid)
    (h : ObsEq i d1 d2) : ObsEq i d1' d2' :=
  (obsEq_convert _ _ _).2 (by
    rw [obs_dispatch h1 hi, obs_dispatch h2 (h.hcid.1 hi), (obsEq_convert i d1 d2).1 h])

theorem conf_proc_exit_user {rs : UContext} {d1 d2 d1' d2' : UData} (h1 : proc_exit_user_spec rs d1 = some d1')
    (h2 : proc_exit_user_spec rs d2 = some d2') (hi : i = d1.cid) (h : ObsEq i d1 d2) : ObsEq i d1' d2' :=
  (obsEq_convert _ _ _).2 (by
    rw [obs_exit_user h1 hi, obs_exit_user h2 (h.hcid.1 hi), (obsEq_convert i d1 d2).1 h])

theorem conf_proc_start_user {r1 r2 : UContext} {d1 d2 d1' d2' : UData}
    (h1 : proc_start_user_spec d1 = some (d1', r1)) (h2 : proc_start_user_spec d2 = some (d2', r2))
    (hi : i = d1.cid) (h : ObsEq i d1 d2) : ObsEq i d1' d2' ∧ r1 = r2 := by
  obtain ⟨a1, b1⟩ := obs_start_user (i := i) h1 hi
  obtain ⟨a2, b2⟩ := obs_start_user (i := i) h2 (h.hcid.1 hi)
  have e := (obsEq_convert i d1 d2).1 h
  exact ⟨(obsEq_convert _ _ _).2 (by rw [a1, a2, e]), by rw [b1, b2, e]⟩

/-- Confidentiality for `thread_yield`: whoever is resumed in each state, the
process that yielded observes the same. -/
theorem conf_thread_yield {nc la1 la2 : Nat} {ql1 ql2 : List Nat} {rsK : KCtx} {d1 d2 : UData}
    (hi : i = d1.cid) (hl1 : la1 ≠ d1.cid) (hl2 : la2 ≠ d2.cid) (h : ObsEq i d1 d2) :
    ObsEq i (putK d1 (yieldOut nc la1 ql1 rsK (toK d1))) (putK d2 (yieldOut nc la2 ql2 rsK (toK d2))) :=
  (obsEq_convert _ _ _).2 (by
    rw [obs_yield hi hl1, obs_yield (h.hcid.1 hi) hl2, (obsEq_convert i d1 d2).1 h])

/-! ## The entry points -/

/-- **A system call, on the observation of the caller.** -/
theorem obs_syscall {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat} {elf : Nat → Nat}
    {d d1 d2 d3 : UData} {rs rs' : UContext} (h1 : proc_exit_user_spec rs d = some d1)
    (h2 : sys_dispatch_c_spec num_id mc num_chan code pstart elf d1 = some d2)
    (h3 : proc_start_user_spec d2 = some (d3, rs')) (hi : i = d.cid) :
    observe i d3 = obsStart (obsDispatch num_id mc i (obsExit rs (observe i d))) ∧
      rs' = (obsDispatch num_id mc i (obsExit rs (observe i d))).observe_uctxt := by
  have hi1 : i = d1.cid := by rw [(exit_shape h1).1]; exact hi
  have o1 := obs_exit_user h1 hi
  have o2 := obs_dispatch h2 hi1
  have hi2 : i = d2.cid := by
    apply running_of_obs
    rw [o2]
    have hr := obs_running hi1
    revert hr
    generalize observe i d1 = o
    intro hr
    unfold obsDispatch obsTrapCreate obsGetQuota obsSetReg obsCreate
    repeat' split
    all_goals exact hr
  obtain ⟨o3, hr3⟩ := obs_start_user h3 hi2
  rw [o3, hr3, o2, o1]
  exact ⟨rfl, rfl⟩

/-- **Confidentiality of a system call.** Two states the caller cannot tell
apart, the same registers at the trap: afterwards it still cannot tell them
apart, and it gets the same registers back. -/
theorem confidentiality_syscall {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart : Nat}
    {elf : Nat → Nat} {d d1 d2 d3 e e1 e2 e3 : UData} {rs rsd rse : UContext}
    (h1 : proc_exit_user_spec rs d = some d1)
    (h2 : sys_dispatch_c_spec num_id mc num_chan code pstart elf d1 = some d2)
    (h3 : proc_start_user_spec d2 = some (d3, rsd)) (g1 : proc_exit_user_spec rs e = some e1)
    (g2 : sys_dispatch_c_spec num_id mc num_chan code pstart elf e1 = some e2)
    (g3 : proc_start_user_spec e2 = some (e3, rse)) (hi : i = d.cid) (h : ObsEq i d e) :
    ObsEq i d3 e3 ∧ rsd = rse := by
  obtain ⟨a1, b1⟩ := obs_syscall (i := i) h1 h2 h3 hi
  obtain ⟨a2, b2⟩ := obs_syscall (i := i) g1 g2 g3 (h.hcid.1 hi)
  have eo := (obsEq_convert i d e).1 h
  exact ⟨(obsEq_convert _ _ _).2 (by rw [a1, a2, eo]), by rw [b1, b2, eo]⟩

/-- **Confidentiality of a yield.** -/
theorem confidentiality_yield {nc la1 la2 : Nat} {ql1 ql2 : List Nat} {rsK : KCtx} {d d1 e e1 : UData}
    {rs : UContext} (h1 : proc_exit_user_spec rs d = some d1) (g1 : proc_exit_user_spec rs e = some e1)
    (hi : i = d.cid) (hl1 : la1 ≠ d.cid) (hl2 : la2 ≠ e.cid) (h : ObsEq i d e) :
    ObsEq i (putK d1 (yieldOut nc la1 ql1 rsK (toK d1))) (putK e1 (yieldOut nc la2 ql2 rsK (toK e1))) := by
  have c1 : d1.cid = d.cid := by rw [(exit_shape h1).1]
  have c2 : e1.cid = e.cid := by rw [(exit_shape g1).1]
  exact conf_thread_yield (by rw [c1]; exact hi) (by rw [c1]; exact hl1) (by rw [c2]; exact hl2)
    (conf_proc_exit_user h1 g1 hi h)

/-! ## A parked process is resumed (`ConfidentialityRestore.v`) -/

/-- `thread_yield` that resumes the observer: it runs again, and sees the
flags. -/
theorem obs_resume {nc : Nat} {ql : List Nat} {rsK : KCtx} {d : UData} (hi : i ≠ d.cid) :
    observe i (putK d (yieldOut nc i ql rsK (toK d))) =
      { observe i d with observe_cid := true, observe_ikern := some d.ikern, observe_ihost := some d.ihost,
                         observe_pg := some d.pg, observe_ipt := some d.ipt, observe_init := some d.init } := by
  apply MyObs.ext13 <;> first
    | rfl
    | (show decide (i = i) = true; exact decide_eq_true rfl)
    | (show setAt d.kctxt d.cid rsK i = d.kctxt i; exact setAt_ne _ _ hi)
    | (show (if i = i then some _ else none) = some _; exact if_pos rfl)

/-- Confidentiality when the observer is resumed (`conf_thread_yield_restore`):
two states it could not tell apart while parked, in both of which some other
process yields to it. It still cannot tell them apart, and it resumes the same
kernel computation. -/
theorem conf_thread_yield_restore {nc : Nat} {ql1 ql2 : List Nat} {rs1 rs2 : KCtx} {d1 d2 : UData}
    (hi : i ≠ d1.cid) (hk : d1.ikern = d2.ikern) (hh : d1.ihost = d2.ihost) (hp : d1.pg = d2.pg)
    (ht : d1.ipt = d2.ipt) (hn : d1.init = d2.init) (h : ObsEq i d1 d2) :
    ObsEq i (putK d1 (yieldOut nc i ql1 rs1 (toK d1))) (putK d2 (yieldOut nc i ql2 rs2 (toK d2))) ∧
      d1.kctxt i = d2.kctxt i := by
  have hi2 : i ≠ d2.cid := fun e => hi (h.hcid.2 e)
  refine ⟨(obsEq_convert _ _ _).2 ?_, h.hkctxt⟩
  rw [obs_resume hi, obs_resume hi2, (obsEq_convert i d1 d2).1 h, hk, hh, hp, ht, hn]

/-- **Confidentiality when a parked process is resumed by a yield.** The two
yielding processes may have trapped with different registers. -/
theorem confidentiality_restore {nc : Nat} {ql1 ql2 : List Nat} {rsK1 rsK2 : KCtx} {d d1 e e1 : UData}
    {rs1 rs2 : UContext} (h1 : proc_exit_user_spec rs1 d = some d1) (g1 : proc_exit_user_spec rs2 e = some e1)
    (hi : i ≠ d.cid) (hin1 : d.init = true) (hin2 : e.init = true) (hh1 : d.ihost = true)
    (hh2 : e.ihost = true) (h : ObsEq i d e) :
    ObsEq i (putK d1 (yieldOut nc i ql1 rsK1 (toK d1))) (putK e1 (yieldOut nc i ql2 rsK2 (toK e1))) ∧
      d.kctxt i = e.kctxt i := by
  have hi2 : i ≠ e.cid := fun e' => hi (h.hcid.2 e')
  obtain ⟨hd1, hpg1⟩ := exit_shape h1
  obtain ⟨he1, hpg2⟩ := exit_shape g1
  have h' : ObsEq i d1 e1 :=
    ((integ_proc_exit_user h1 hi).symm.trans h).trans (integ_proc_exit_user g1 hi2)
  obtain ⟨a, b⟩ := conf_thread_yield_restore (nc := nc) (ql1 := ql1) (ql2 := ql2) (rs1 := rsK1) (rs2 := rsK2)
    (d1 := d1) (d2 := e1) (by rw [hd1]; exact hi) (by rw [hd1, he1]) (by rw [hd1, he1]; exact hh1.trans hh2.symm)
    (by rw [hd1, he1]; exact hpg1.trans hpg2.symm) (by rw [hd1, he1])
    (by rw [hd1, he1]; exact hin1.trans hin2.symm) h'
  refine ⟨a, ?_⟩
  have e1' : d1.kctxt i = d.kctxt i := by rw [hd1]
  have e2' : e1.kctxt i = e.kctxt i := by rw [he1]
  rw [← e1', ← e2']
  exact b

end Security
