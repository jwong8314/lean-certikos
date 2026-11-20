import CertiKOS.TTrapArg

/-!
# mCertiKOS `TTrap`: system-call handlers, ported (first part)

A handler reads its arguments from the caller's user context, calls the
kernel function, and writes the result and the error code back.

Ported from `objects/ObjTrap.v`: `trap_sendtochan_pre_spec`,
`trap_sendtochan_post_spec`, `trap_receivechan_spec`, `trap_get_quota_spec`,
`ptfault_resv_spec`. Ported from `trap/TTrapArgCSource.v` and
`trap/TTrapCSource.v`: the C code of `trap_sendtochan_pre`,
`trap_sendtochan_post`, `sys_receive_chan`, `sys_get_quota`, `ptfault_resv`.

* `ctGetQuotaU`, `ctGetUsageU`, `ctGetNchildrenU`: the container getters as
  steps on the top state.
* `retDone_step`: `uctx_set_retval1(v); uctx_set_errno(0);`, how every
  successful handler ends.
* `trapSendPre_triple`, `trapSendPost_triple`, `trapReceive_triple`,
  `trapGetQuota_triple`: **each handler refines its specification.** The
  calls inside go through `syncSendPre_triple`, `syncSendPost_triple`,
  `syncReceive_triple` (carried up by `liftIU`) and the steps of the
  accessors.

* `ptfaultResv_triple`: **`ptfault_resv` refines `ptfault_resv_spec`**: a
  fault at a user address maps a fresh page there. `pt_resv` is called
  through its triple, carried up by `liftPC'`, `liftCI` and `liftIU`.

What differs: the handlers assume what mCertiKOS keeps as invariants: the
current thread is a valid process, the queue invariants hold (for the
receive), the container's usage is within its quota, and the allocation
table's invariant (for `pt_resv`). The C tests `addr_low <= vaddr &&
vaddr < addr_high`; ClightL has neither `&&` nor `<=`, so the code is two
nested tests with `<`. `sys_proc_create` and the dispatcher are in
`TDispatch.lean`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace TTrap

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt UMach MCPU PProc FlatMem
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## Specifications (`ObjTrap.v`) -/

/-- **`trap_sendtochan_pre_spec`**: the receiver, the buffer and the length
are arguments 2 to 4. -/
def trap_sendtochan_pre_spec (num_proc num_chan : Nat) (d : UData) : Option (UData × Nat) :=
  match uctx_arg2_spec d with
  | some chid =>
    match uctx_arg3_spec d with
    | some vaddr =>
      match uctx_arg4_spec d with
      | some scount =>
        match syncsendto_chan_pre_spec num_proc num_chan chid vaddr scount d.toIData with
        | some (i1, r) => some ({ d with toIData := i1 }, r)
        | none => none
      | none => none
    | none => none
  | none => none

/-- **`trap_sendtochan_post_spec`**: the count received is the return value. -/
def trap_sendtochan_post_spec (num_chan : Nat) (d : UData) : Option UData :=
  match syncsendto_chan_post_spec num_chan d.toIData with
  | some (i1, r) =>
    match uctx_set_retval1_spec r { d with toIData := i1 } with
    | some d1 => uctx_set_errno_spec E_SUCC d1
    | none => none
  | none => none

/-- **`trap_receivechan_spec`**: the sender, the buffer and its length are
arguments 2 to 4; the count received is the return value. -/
def trap_receivechan_spec (num_proc num_chan : Nat) (d : UData) : Option UData :=
  match uctx_arg2_spec d with
  | some fromid =>
    match uctx_arg3_spec d with
    | some vaddr =>
      match uctx_arg4_spec d with
      | some rcount =>
        match syncreceive_chan_spec num_proc num_chan fromid vaddr rcount d.toIData with
        | some (i1, r) =>
          match uctx_set_retval1_spec r { d with toIData := i1 } with
          | some d1 => uctx_set_errno_spec E_SUCC d1
          | none => none
        | none => none
      | none => none
    | none => none
  | none => none

/-- **`trap_get_quota_spec`**: what is left of the caller's quota. -/
def trap_get_quota_spec (d : UData) : Option UData :=
  match get_curid_spec d.toCData with
  | some curid =>
    match container_get_quota_spec curid d.toRData with
    | some quota =>
      match container_get_usage_spec curid d.toRData with
      | some usage =>
        match uctx_set_retval1_spec (quota - usage) d with
        | some d1 => uctx_set_errno_spec E_SUCC d1
        | none => none
      | none => none
    | none => none
  | none => none

/-- **`ptfault_resv_spec`**: a page fault at a user address gets a page. -/
def ptfault_resv_spec (maxpage num_proc vadr : Nat) (d : UData) : Option UData :=
  if d.ikern = true ∧ d.ihost = true ∧ d.pg = true then
    if 1073741824 ≤ vadr ∧ vadr < 4026531840 then
      match ptResv_spec maxpage num_proc d.cid vadr 7 d.toPTData with
      | some (p, _) => some { d with toPTData := p }
      | none => none
    else some d
  else none

/-! ## The code -/

/-- `x = container_get_quota(id)` (field 0), `container_get_usage` (1),
`container_get_nchildren` (3): `return CONTAINER_POOL[id].field;` -/
def ctGetS (cb : Nat) (x idv : Ident) (f : Val) : Stmt APrim := .call x .pull [lkE, ccellE cb idv f]

/-- `uctx_set_retval1(v); uctx_set_errno(0);` -/
def retDoneS (cidb ucb : Nat) (ve : Expr) : Stmt APrim :=
  .seq (uctxSetRegS cidb ucb U_EBX ve) (uctxSetRegS cidb ucb U_EAX (.const 0))

/-- `pid = uctx_arg2(); vaddr = uctx_arg3(); x4 = uctx_arg4();` -/
def args3S (cidb ucb : Nat) (x4 : Ident) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "pid" U_EBX) (.seq (uctxArgS cidb ucb "vaddr" U_ECX) (uctxArgS cidb ucb x4 U_EDX))

/-- `trap_sendtochan_pre`:
`chid = uctx_arg2(); vaddr = uctx_arg3(); scount = uctx_arg4(); r = syncsendto_chan_pre(chid, vaddr, scount);` -/
def trapSendPreS (tb cidb pb fb ipb ucb num_chan : Nat) : Stmt APrim :=
  .seq (args3S cidb ucb "scount") (syncSendPreS tb cidb pb fb ipb num_chan)

/-- `trap_sendtochan_post`:
`val = syncsendto_chan_post(); uctx_set_retval1(val); uctx_set_errno(0);` -/
def trapSendPostS (cidb ipb ucb num_chan : Nat) : Stmt APrim :=
  .seq (syncSendPostS cidb ipb num_chan) (retDoneS cidb ucb (.var "r"))

/-- `sys_receive_chan`:
```
fromid = uctx_arg2(); vaddr = uctx_arg3(); rcount = uctx_arg4();
val = syncreceive_chan(fromid, vaddr, rcount);
uctx_set_retval1(val); uctx_set_errno(0);
``` -/
def trapReceiveS (tb qb cidb pb fb ipb ucb num_proc num_chan : Nat) : Stmt APrim :=
  .seq (args3S cidb ucb "rcount")
    (.seq (syncReceiveS tb qb cidb pb fb ipb num_proc num_chan) (retDoneS cidb ucb (.var "r")))

/-- `sys_get_quota`:
```
curid = get_curid(); quota = container_get_quota(curid); usage = container_get_usage(curid);
uctx_set_retval1(quota - usage); uctx_set_errno(0);
``` -/
def trapGetQuotaS (cb cidb ucb : Nat) : Stmt APrim :=
  .seq (getCuridS cidb "curid")
    (.seq (ctGetS cb "quota" "curid" 0)
      (.seq (ctGetS cb "usage" "curid" 1) (retDoneS cidb ucb (.bin .sub (.var "quota") (.var "usage")))))

/-- `ptfault_resv(vaddr)`:
`curid = get_curid(); if (addr_low <= vaddr && vaddr < addr_high) pt_resv(curid, vaddr, PT_PERM_PTU);` -/
def ptfaultResvS (cb cidb maxpage pb fb : Nat) : Stmt APrim :=
  .seq (getCuridS cidb "curid")
    (.ite (.bin .ltu (.var "vaddr") (.const 1073741824)) .skip
      (.ite (.bin .ltu (.var "vaddr") (.const 4026531840))
        (.seq (.assign "n" (.var "curid")) (.seq (.assign "perm" (.const 7)) (ptResvS cb maxpage pb fb)))
        .skip))

/-! ## What the specifications below keep -/

/-- An argument that is defined is a known register, and the kernel is in
kernel mode. -/
theorem arg_val {reg : Nat} {d : UData} {a : Nat} (h : uctx_arg_spec reg d = some a) :
    d.uctxt d.cid reg = some (BitVec.ofNat 32 a) ∧ a < 2 ^ 32 := by
  unfold uctx_arg_spec at h
  split at h
  · cases hu : d.uctxt d.cid reg with
    | none => rw [hu] at h; cases h
    | some w =>
      rw [hu] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨by simp, w.isLt⟩
  · cases h

theorem sendPost_cid {nc : Nat} {d d' : IData} {r : Nat} (h : syncsendto_chan_post_spec nc d = some (d', r)) :
    d'.cid = d.cid := by
  unfold syncsendto_chan_post_spec at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

theorem recv_cid {np nc fromid vaddr rcount : Nat} {d d' : IData} {r : Nat}
    (h : syncreceive_chan_spec np nc fromid vaddr rcount d = some (d', r)) : d'.cid = d.cid := by
  unfold syncreceive_chan_spec at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb

/-! ### The container getters, as steps -/

/-- `container_get_quota`. -/
theorem ctGetQuotaU (hnum : cb + 5 * num_id < 2 ^ 32) (x idv : Ident) (hx : x ≠ "lk") {σ : Locals} {d : UData}
    {i : Nat} (hid : σ idv = BitVec.ofNat 32 i) (hi : i < num_id) (hu : (d.AC i).cused = true) :
    Step εR c i0 MU F (ctGetS cb x idv 0) σ d (σ.set x (BitVec.ofNat 32 (d.AC i).cquota)) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk x (ccellE cb idv 0) (n := ccell cb (σ idv) 0) rfl
  rw [hid, get_quota_ref hnum (d := d.toRData) (matchC_all hM.1.1).mm.mAC hi (v := (d.AC i).cquota)
    (by unfold container_get_quota_spec; rw [if_pos hu])] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

/-- `container_get_usage`. -/
theorem ctGetUsageU (hnum : cb + 5 * num_id < 2 ^ 32) (x idv : Ident) (hx : x ≠ "lk") {σ : Locals} {d : UData}
    {i : Nat} (hid : σ idv = BitVec.ofNat 32 i) (hi : i < num_id) (hu : (d.AC i).cused = true) :
    Step εR c i0 MU F (ctGetS cb x idv 1) σ d (σ.set x (BitVec.ofNat 32 (d.AC i).cusage)) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk x (ccellE cb idv 1) (n := ccell cb (σ idv) 1) rfl
  rw [hid, get_usage_ref hnum (d := d.toRData) (matchC_all hM.1.1).mm.mAC hi (v := (d.AC i).cusage)
    (by unfold container_get_usage_spec; rw [if_pos hu])] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

/-- `container_get_nchildren`. -/
theorem ctGetNchildrenU (hnum : cb + 5 * num_id < 2 ^ 32) (x idv : Ident) (hx : x ≠ "lk") {σ : Locals}
    {d : UData} {i : Nat} (hid : σ idv = BitVec.ofNat 32 i) (hi : i < num_id) (hu : (d.AC i).cused = true) :
    Step εR c i0 MU F (ctGetS cb x idv 3) σ d (σ.set x (BitVec.ofNat 32 (d.AC i).cchildren.length)) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk x (ccellE cb idv 3) (n := ccell cb (σ idv) 3) rfl
  rw [hid, get_nchildren_ref hnum (d := d.toRData) (matchC_all hM.1.1).mm.mAC hi
    (v := (d.AC i).cchildren.length) (by unfold container_get_nchildren_spec; rw [if_pos hu])] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

/-! ### The end of a handler -/

/-- **`uctx_set_retval1(v); uctx_set_errno(0);`** -/
theorem retDone_step (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hF : ∀ k, UCF ucb num_proc k → F k) {ve : Expr} {σ : Locals} {d d1 d2 : UData} {r : Nat}
    (hve : ve.eval (σ.set "curid" (BitVec.ofNat 32 d.cid)) = BitVec.ofNat 32 r) (hcid : d.cid < num_proc)
    (h1 : uctx_set_retval1_spec r d = some d1) (h2 : uctx_set_errno_spec E_SUCC d1 = some d2) :
    ∃ σ', Step εR c i0 MU F (retDoneS cidb ucb ve) σ d σ' d2 ∧ σ' "lk" = σ "lk" := by
  unfold uctx_set_retval1_spec uctx_set_reg_spec at h1
  by_cases hc : d.ikern = true ∧ d.pg = true ∧ d.ihost = true
  · rw [if_pos hc] at h1
    simp only [Option.some.injEq] at h1
    subst h1
    unfold uctx_set_errno_spec uctx_set_reg_spec at h2
    dsimp only at h2
    rw [if_pos hc] at h2
    simp only [Option.some.injEq] at h2
    subst h2
    have s1 := uctxSetRegU (ida := ida) (cidb := cidb) εR c i0 hL hF (reg := U_EBX) (by decide) hve hcid
    exact ⟨_, Step.seq s1 (uctxSetRegU εR c i0 hL hF (reg := U_EAX) (by decide) (ve := .const 0)
      (w := BitVec.ofNat 32 E_SUCC) rfl hcid), by simp [Locals.set]⟩
  · rw [if_neg hc] at h1; cases h1

/-! ### The handlers -/

/-- **`trap_sendtochan_post` refines `trap_sendtochan_post_spec`.** -/
theorem trapSendPost_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb) :
    Triple εR c i0 MU (fun k => IPF ipb num_chan k ∨ UCF ucb num_proc k)
      (fun _ d => d.cid < num_chan ∧ d.cid < num_proc ∧ ∃ d1, trap_sendtochan_post_spec num_chan d = some d1)
      (trapSendPostS cidb ipb ucb num_chan)
      (fun _ d _ d' => trap_sendtochan_post_spec num_chan d = some d') := by
  intro σ l b d hlk hcs hM ⟨hcc, hcp, d', hs⟩
  have := hL.hub0
  have hs0 := hs
  unfold trap_sendtochan_post_spec at hs
  cases hp : syncsendto_chan_post_spec num_chan d.toIData with
  | none => rw [hp] at hs; cases hs
  | some pr =>
    obtain ⟨i1, r⟩ := pr
    rw [hp] at hs
    simp only at hs
    cases h1 : uctx_set_retval1_spec r { d with toIData := i1 } with
    | none => rw [h1] at hs; cases hs
    | some d1 =>
      rw [h1] at hs
      simp only at hs
      obtain ⟨σ1, l1, b1, u1, r1, c1, m1, k1, f1, i1', hu1, r', hq, hr⟩ :=
        liftIU εR c i0 hL (syncSendPost_triple εR c i0 hL.ilay)
          (fun k hk => Or.inl (by unfold IPF at hk; omega)) σ l b d hlk hcs hM ⟨hcc, i1, r, hp⟩
      rw [hp] at hq
      simp only [Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨e1, e2⟩ := hq
      subst e1; subst e2; subst hu1
      have hcid1 : ({ d with toIData := i1 } : UData).cid < num_proc := by
        show i1.cid < num_proc
        rw [sendPost_cid hp]; exact hcp
      obtain ⟨σ2, hst, hlk2⟩ := retDone_step (ida := ida) (cidb := cidb) εR c i0 hL
        (F := fun k => IPF ipb num_chan k ∨ UCF ucb num_proc k) (fun _ h => Or.inr h) (ve := .var "r") (σ := σ1)
        (by simp [Expr.eval, Locals.set, hr]) hcid1 h1 hs
      obtain ⟨l2, b2, r2, c2, m2, f2⟩ := hst.2 l1 b1 (by rw [k1]; exact hlk) c1 m1
      exact ⟨σ2, l2, b2, d', Runs.seq r1 r2, c2, m2, hlk2.trans k1,
        fun k hk => (f2 k hk).trans (f1 k (fun h => hk (Or.inl h))), hs0⟩

/-- The three argument reads of the IPC handlers. -/
theorem args3_run (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (x4 : Ident) (h4a : x4 ≠ "lk") (h4b : x4 ≠ "pid") (h4c : x4 ≠ "vaddr") (h4d : x4 ≠ "curid") {σ : Locals}
    {d : UData} {a2 a3 a4 : Nat} (hcid : d.cid < num_proc) (e2 : uctx_arg2_spec d = some a2)
    (e3 : uctx_arg3_spec d = some a3) (e4 : uctx_arg4_spec d = some a4) :
    ∃ σ', Step εR c i0 MU F (args3S cidb ucb x4) σ d σ' d ∧
      σ' "pid" = BitVec.ofNat 32 a2 ∧ σ' "vaddr" = BitVec.ofNat 32 a3 ∧ σ' x4 = BitVec.ofNat 32 a4 := by
  have s1 := uctxArgU (ida := ida) (cidb := cidb) εR c i0 hL (F := F) "pid" (by decide) (reg := U_EBX)
    (by decide) (σ := σ) hcid (arg_val e2).1
  refine ⟨_, Step.seq s1 (Step.seq (uctxArgU εR c i0 hL "vaddr" (by decide) (reg := U_ECX) (by decide) hcid
    (arg_val e3).1) (uctxArgU εR c i0 hL x4 h4a (reg := U_EDX) (by decide) hcid (arg_val e4).1)), ?_, ?_, ?_⟩
  · simp [Locals.set, h4b.symm]
  · simp [Locals.set, h4c.symm]
  · simp [Locals.set]

/-- **`trap_sendtochan_pre` refines `trap_sendtochan_pre_spec`.** The result
is in `r`. -/
theorem trapSendPre_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hnpc : num_proc ≤ num_chan) :
    Triple εR c i0 MU (IPF ipb num_chan)
      (fun _ d => d.cid < num_proc ∧
        ∃ d1 r, trap_sendtochan_pre_spec num_proc num_chan d = some (d1, r))
      (trapSendPreS tb cidb pb fb ipb ucb num_chan)
      (fun _ d σ' d' => ∃ r, trap_sendtochan_pre_spec num_proc num_chan d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hcp, d', r, hs⟩
  have := hL.hub0
  have hs0 := hs
  unfold trap_sendtochan_pre_spec at hs
  cases e2 : uctx_arg2_spec d with
  | none => rw [e2] at hs; cases hs
  | some chid =>
    rw [e2] at hs; simp only at hs
    cases e3 : uctx_arg3_spec d with
    | none => rw [e3] at hs; cases hs
    | some vaddr =>
      rw [e3] at hs; simp only at hs
      cases e4 : uctx_arg4_spec d with
      | none => rw [e4] at hs; cases hs
      | some scount =>
        rw [e4] at hs; simp only at hs
        cases hp : syncsendto_chan_pre_spec num_proc num_chan chid vaddr scount d.toIData with
        | none => rw [hp] at hs; cases hs
        | some pr =>
          obtain ⟨i1, r1⟩ := pr
          rw [hp] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨hd, hr⟩ := hs
          subst hd; subst hr
          obtain ⟨σ1, hst, hpid, hva, hsc⟩ := args3_run (ida := ida) (cidb := cidb) εR c i0 hL
            (F := IPF ipb num_chan) "scount" (by decide) (by decide) (by decide) (by decide) (σ := σ) hcp e2 e3 e4
          obtain ⟨l1, b1, r1', c1, m1, f1⟩ := hst.2 l b hlk hcs hM
          obtain ⟨σ2, l2, b2, u2, r2, c2, m2, k2, f2, i2, hu2, r', hq, hr2⟩ :=
            liftIU εR c i0 hL (syncSendPre_triple εR c i0 hL.ilay hnpc chid vaddr scount (arg_val e3).2
              (arg_val e4).2) (fun k hk => Or.inl (by unfold IPF at hk; omega)) σ1 l1 b1 d
              (by rw [hst.1]; exact hlk) c1 m1 ⟨hpid, hva, hsc, by omega, i1, r1, hp⟩
          rw [hp] at hq
          simp only [Option.some.injEq, Prod.mk.injEq] at hq
          obtain ⟨e1, e2'⟩ := hq
          subst e1; subst e2'; subst hu2
          exact ⟨σ2, l2, b2, _, Runs.seq r1' r2, c2, m2, k2.trans hst.1,
            fun k hk => (f2 k hk).trans (f1 k hk), _, hs0, hr2⟩

/-- **`sys_receive_chan` refines `trap_receivechan_spec`.** -/
theorem trapReceive_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hnpc : num_proc ≤ num_chan) :
    Triple εR c i0 MU (fun k => RecvF tb num_proc qb num_chan ipb fb k ∨ UCF ucb num_proc k)
      (fun _ d => d.cid < num_proc ∧ AInv num_proc num_chan d.toAData ∧
        ∃ d1, trap_receivechan_spec num_proc num_chan d = some d1)
      (trapReceiveS tb qb cidb pb fb ipb ucb num_proc num_chan)
      (fun _ d _ d' => trap_receivechan_spec num_proc num_chan d = some d') := by
  intro σ l b d hlk hcs hM ⟨hcp, hI, d', hs⟩
  have hCL := hL.ilay.clay
  have hLay := hCL.qlay.tlay.slay.lay
  have := hL.hub0; have := hL.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb; have := hLay.hib
  have := hLay.hfb
  have hRF : ∀ k, RecvF tb num_proc qb num_chan ipb fb k → k < ucb ∨ pb ≤ k := by
    intro k hk
    rcases hk with (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) | h1 <;> omega
  have hs0 := hs
  unfold trap_receivechan_spec at hs
  cases e2 : uctx_arg2_spec d with
  | none => rw [e2] at hs; cases hs
  | some fromid =>
    rw [e2] at hs; simp only at hs
    cases e3 : uctx_arg3_spec d with
    | none => rw [e3] at hs; cases hs
    | some vaddr =>
      rw [e3] at hs; simp only at hs
      cases e4 : uctx_arg4_spec d with
      | none => rw [e4] at hs; cases hs
      | some rcount =>
        rw [e4] at hs; simp only at hs
        cases hp : syncreceive_chan_spec num_proc num_chan fromid vaddr rcount d.toIData with
        | none => rw [hp] at hs; cases hs
        | some pr =>
          obtain ⟨i1, r⟩ := pr
          rw [hp] at hs
          simp only at hs
          cases h1 : uctx_set_retval1_spec r { d with toIData := i1 } with
          | none => rw [h1] at hs; cases hs
          | some d1 =>
            rw [h1] at hs
            simp only at hs
            obtain ⟨σ1, hst, hpid, hva, hrc⟩ := args3_run (ida := ida) (cidb := cidb) εR c i0 hL
              (F := fun k => RecvF tb num_proc qb num_chan ipb fb k ∨ UCF ucb num_proc k) "rcount" (by decide)
              (by decide) (by decide) (by decide) (σ := σ) hcp e2 e3 e4
            obtain ⟨l1, b1, r1', c1, m1, f1⟩ := hst.2 l b hlk hcs hM
            obtain ⟨σ2, l2, b2, u2, r2, c2, m2, k2, f2, i2, hu2, r', hq, hr2⟩ :=
              liftIU εR c i0 hL (syncReceive_triple εR c i0 hL.ilay hnpc fromid vaddr rcount (arg_val e3).2
                (arg_val e4).2) hRF σ1 l1 b1 d (by rw [hst.1]; exact hlk) c1 m1 ⟨hpid, hva, hrc, hI, i1, r, hp⟩
            rw [hp] at hq
            simp only [Option.some.injEq, Prod.mk.injEq] at hq
            obtain ⟨e1, e2'⟩ := hq
            subst e1; subst e2'; subst hu2
            have hcid2 : ({ d with toIData := i1 } : UData).cid < num_proc := by
              show i1.cid < num_proc
              rw [recv_cid hp]; exact hcp
            obtain ⟨σ3, hst3, hlk3⟩ := retDone_step (ida := ida) (cidb := cidb) εR c i0 hL
              (F := fun k => RecvF tb num_proc qb num_chan ipb fb k ∨ UCF ucb num_proc k) (fun _ h => Or.inr h)
              (ve := .var "r") (σ := σ2) (by simp [Expr.eval, Locals.set, hr2]) hcid2 h1 hs
            obtain ⟨l3, b3, r3, c3, m3, f3⟩ := hst3.2 l2 b2 (by rw [k2, hst.1]; exact hlk) c2 m2
            exact ⟨σ3, l3, b3, d', Runs.seq r1' (Runs.seq r2 r3), c3, m3, hlk3.trans (k2.trans hst.1),
              fun k hk => by rw [f3 k hk, f2 k (fun h => hk (Or.inl h)), f1 k hk], hs0⟩

theorem ofNat_sub_le {q u : Nat} (h : u ≤ q) :
    (BitVec.ofNat 32 q : Val) - BitVec.ofNat 32 u = BitVec.ofNat 32 (q - u) := by
  have e : (BitVec.ofNat 32 q : Val) = BitVec.ofNat 32 (q - u) + BitVec.ofNat 32 u := by
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  rw [e, BitVec.add_sub_cancel]

/-- **`sys_get_quota` refines `trap_get_quota_spec`.** -/
theorem trapGetQuota_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hnum : cb + 5 * num_id < 2 ^ 32) :
    Triple εR c i0 MU (UCF ucb num_proc)
      (fun _ d => d.cid < num_proc ∧ d.cid < num_id ∧ (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota ∧
        ∃ d1, trap_get_quota_spec d = some d1)
      (trapGetQuotaS cb cidb ucb)
      (fun _ d _ d' => trap_get_quota_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, hci, hle, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_get_quota_spec get_curid_spec container_get_quota_spec container_get_usage_spec at hs
  by_cases hpg : d.pg = true
  · rw [if_pos hpg] at hs
    simp only at hs
    by_cases hu : (d.AC d.cid).cused = true
    · simp only [if_pos hu] at hs
      cases h1 : uctx_set_retval1_spec ((d.AC d.cid).cquota - (d.AC d.cid).cusage) d with
      | none => rw [h1] at hs; cases hs
      | some d1 =>
        rw [h1] at hs
        simp only at hs
        have s1 := getCuridU (ida := ida) εR c i0 hL (F := UCF ucb num_proc) "curid" (by decide) σ d
        have s2 := ctGetQuotaU (ida := ida) (ipb := ipb) (ucb := ucb) (cidb := cidb) (tb := tb) (qb := qb)
          (sb := sb) (num_chan := num_chan) (num_proc := num_proc) (pb := pb) (ib := ib) (fb := fb)
          (maxpage := maxpage) εR c i0 (F := UCF ucb num_proc) hnum "quota" "curid" (by decide)
          (σ := σ.set "curid" (BitVec.ofNat 32 d.cid)) (d := d) (i := d.cid) (by simp) hci hu
        have s3 := ctGetUsageU (ida := ida) (ipb := ipb) (ucb := ucb) (cidb := cidb) (tb := tb) (qb := qb)
          (sb := sb) (num_chan := num_chan) (num_proc := num_proc) (pb := pb) (ib := ib) (fb := fb)
          (maxpage := maxpage) εR c i0 (F := UCF ucb num_proc) hnum "usage" "curid" (by decide)
          (σ := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "quota" (BitVec.ofNat 32 (d.AC d.cid).cquota))
          (d := d) (i := d.cid) (by simp [Locals.set]) hci hu
        obtain ⟨σ4, s4, -⟩ := retDone_step (ida := ida) (cidb := cidb) εR c i0 hL (F := UCF ucb num_proc)
          (fun _ h => h) (ve := .bin .sub (.var "quota") (.var "usage"))
          (σ := ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "quota"
            (BitVec.ofNat 32 (d.AC d.cid).cquota)).set "usage" (BitVec.ofNat 32 (d.AC d.cid).cusage))
          (r := (d.AC d.cid).cquota - (d.AC d.cid).cusage)
          (by simp [Expr.eval, BinOp.eval, Locals.set]; exact ofNat_sub_le hle) hcp h1 hs
        exact ⟨σ4, d', Step.seq s1 (Step.seq s2 (Step.seq s3 s4)), hs0⟩
    · simp only [if_neg hu] at hs
      cases hs
  · rw [if_neg hpg] at hs; cases hs

/-! ### The page-fault handler's body -/

local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb

/-- `liftPC` for a triple that may change `pg` only from on to on. -/
theorem liftPC' (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb)
    {P : Locals → PTData → Prop} {s : Stmt APrim} {Q : Locals → PTData → Locals → PTData → Prop}
    (h : Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) F P s Q)
    (hF : ∀ k, F k → k < cb + 5 * num_id ∨ pb ≤ k)
    (hpg : ∀ σ d σ' d', P σ d → Q σ d σ' d' → d'.pg = true → d.pg = true) :
    Triple εR c i0 MC F (fun σ d => P σ d.toPTData) s
      (fun σ d σ' d' => ∃ p : PTData, d' = { d with toPTData := p } ∧ Q σ d.toPTData σ' p) := by
  intro σ l b d hlk hcs hM hp
  have := hL.qlay.tlay.slay.hsb
  obtain ⟨σ', l', b', p, hr, hcs', hA', hlk', hf, hq⟩ := h σ l b d.toPTData hlk hcs (matchC_all hM) hp
  exact ⟨σ', l', b', _, hr, hcs', matchC_setPT hL hM hA'
    (fun k h1 h2 => hf k (fun hk => by have := hF k hk; omega)) (hpg σ _ σ' p hp hq), hlk', hf, p, rfl, hq⟩

/-- **`ptfault_resv` refines `ptfault_resv_spec`.** The faulting address is
in `vaddr`. -/
theorem ptfaultResv_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (vadr : Nat) (hv : vadr < 2 ^ 32) :
    Triple εR c i0 MU (fun k => k < cb + 5 * num_id ∨ pb ≤ k)
      (fun σ d => σ "vaddr" = BitVec.ofNat 32 vadr ∧ d.cid < num_id ∧ ATInv maxpage kl kh d.toPData ∧
        (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota ∧ ∃ d1, ptfault_resv_spec maxpage num_proc vadr d = some d1)
      (ptfaultResvS cb cidb maxpage pb fb)
      (fun _ d _ d' => ptfault_resv_spec maxpage num_proc vadr d = some d') := by
  intro σ l b d hlk hcs hM ⟨hva, hci, hAT, hq, d', hs⟩
  have hCL := hL.ilay.clay
  have hLay := hCL.qlay.tlay.slay.lay
  have := hL.hub0; have := hL.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb; have := hCL.qlay.tlay.htb
  have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse
  have hs0 := hs
  unfold ptfault_resv_spec at hs
  by_cases hc : d.ikern = true ∧ d.ihost = true ∧ d.pg = true
  · rw [if_pos hc] at hs
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (getCuridU εR c i0 hL (F := fun k => k < cb + 5 * num_id ∨ pb ≤ k)
      "curid" (by decide) σ d).2 l b hlk hcs hM
    have hva1 : (σ.set "curid" (BitVec.ofNat 32 d.cid)) "vaddr" = BitVec.ofNat 32 vadr := by
      rw [Locals.set_other _ _ (by decide)]; exact hva
    have hg1 := ltu_eval (σ := σ.set "curid" (BitVec.ofNat 32 d.cid)) (ea := .var "vaddr")
      (eb := .const 1073741824) (a := vadr) (b := 1073741824) hva1 rfl hv (by decide)
    have hg2 := ltu_eval (σ := σ.set "curid" (BitVec.ofNat 32 d.cid)) (ea := .var "vaddr")
      (eb := .const 4026531840) (a := vadr) (b := 4026531840) hva1 rfl hv (by decide)
    by_cases hr : 1073741824 ≤ vadr ∧ vadr < 4026531840
    · rw [if_pos hr] at hs
      rw [if_neg (by omega)] at hg1
      rw [if_pos hr.2] at hg2
      cases hp : ptResv_spec maxpage num_proc d.cid vadr 7 d.toPTData with
      | none => rw [hp] at hs; cases hs
      | some pr =>
        obtain ⟨p, rr⟩ := pr
        rw [hp] at hs
        simp only [Option.some.injEq] at hs
        subst hs
        have T := liftIU εR c i0 hL (liftCI εR c i0 hL.ilay (liftPC' εR c i0 hCL
          ((ptResv_triple εR c i0 hLay hmax hnum hmp hnn (kl := kl) (kh := kh) d.cid vadr 7 hci
            (ida := ida)).conseq (P' := fun σ (e : PTData) => (σ "n" = BitVec.ofNat 32 d.cid ∧
              σ "vaddr" = BitVec.ofNat 32 vadr ∧ σ "perm" = BitVec.ofNat 32 7 ∧
              ATInv maxpage kl kh e.toPData ∧ (e.AC d.cid).cusage ≤ (e.AC d.cid).cquota ∧
              ∃ d1 r, ptResv_spec maxpage num_proc d.cid vadr 7 e = some (d1, r)) ∧ e.pg = true)
            (fun _ _ h => h.1) (fun _ _ _ _ _ h => h))
          (fun _ h => h) (fun _ _ _ _ hP _ _ => hP.2)) (fun k hk => by omega)) (fun k hk => by omega)
        obtain ⟨σ2, l2, b2, u2, r2, c2, m2, k2, f2, i2, hu2, cc, hi2, p2, hcc, r', hq2, -⟩ :=
          T (((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "n" (BitVec.ofNat 32 d.cid)).set "perm" 7) l1 b1 d
            (by simpa [Locals.set] using hlk) c1 m1
            ⟨⟨by simp [Locals.set], by simp [Locals.set, hva], by simp [Locals.set], hAT, hq, p, rr, hp⟩,
              hc.2.2⟩
        rw [hp] at hq2
        simp only [Option.some.injEq, Prod.mk.injEq] at hq2
        obtain ⟨e1, -⟩ := hq2
        subst e1; subst hcc; subst hi2; subst hu2
        refine ⟨σ2, l2, b2, _, Runs.seq r1 (Runs.ite_false hg1 (Runs.ite_true (by rw [hg2]; decide)
          (Runs.seq (asg_run "n" (.var "curid") (by simp [Expr.eval]))
            (Runs.seq (asg_run "perm" (.const 7) rfl) r2)))), c2, m2, ?_, fun k hk => ?_, hs0⟩
        · rw [k2]; simp [Locals.set]
        · rw [f2 k hk, f1 k hk]
    · rw [if_neg hr] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      by_cases hlo : vadr < 1073741824
      · rw [if_pos hlo] at hg1
        exact ⟨_, l1, b1, d, Runs.seq r1 (Runs.ite_true (by rw [hg1]; decide) Runs.skip), c1, m1,
          by simp [Locals.set], f1, hs0⟩
      · rw [if_neg hlo] at hg1
        rw [if_neg (by omega)] at hg2
        exact ⟨_, l1, b1, d, Runs.seq r1 (Runs.ite_false hg1 (Runs.ite_false hg2 Runs.skip)), c1, m1,
          by simp [Locals.set], f1, hs0⟩
  · rw [if_neg hc] at hs; cases hs

end Code

end TTrap
