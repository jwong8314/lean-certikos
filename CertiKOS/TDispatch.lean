import CertiKOS.TTrap

/-!
# mCertiKOS `TTrap`, `TDispatch`: `sys_proc_create` and the dispatcher, ported

Ported from `objects/ObjTrap.v`: `trap_proc_create_spec`,
`sys_dispatch_c_spec`. Ported from `objects/ObjContainer.v` and
`mm/MALTCSource.v`: `container_can_consume`. Ported from
`trap/TTrapArgCSource.v`: `sys_proc_create`. Ported from
`trap/TTrapCSource.v`: `syscall_dispatch_c`.

* `ctCanConsumeU`: **`container_can_consume` refines its specification**
  (it was the one container primitive left).
* `MatchELF`: the table of entry points (`ELF_ENTRY_LOC`), `num_id` words at
  `elb`, written by the boot loader.
* `spcChecks_step`: the three tests of `sys_proc_create` (quota, room for
  children's ids, number of children).
* `sysProcCreate_run`: **`sys_proc_create` on the kernel machine does what
  `trap_proc_create_spec` says**: an error code if a test fails, else a new
  process and its id.
* `sysDispatch_run`: **`syscall_dispatch_c` does what `sys_dispatch_c_spec`
  says.**

What differs:
* The dispatcher handles `SYS_spawn` and `SYS_get_quota`. mCertiKOS's also
  handles `SYS_share` (shared memory) and `SYS_print` (device output), which
  are not ported to the top state.
* `ELF_ident`: mCertiKOS's specification is defined only for image 0, because
  an entry point is a pointer there and must be a known symbol. Here an entry
  point is a number and every image below `num_id` is allowed.
* ClightL has no `||`. The test `qok == 0 || NUM_ID < … || nc == MAX_CHILDREN`
  is evaluated into a flag `ok` by three nested conditionals.
* `container_can_consume` is `if (quota < n) 0 else if (quota - n < usage) 0
  else 1`, the verified Clight with `<=` turned around.
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

/-- **`trap_proc_create_spec`**: argument 3 is the child's quota and argument
2 the image to run. `elf` is the table of entry points. -/
def trap_proc_create_spec (num_id mc num_chan : Nat) (code : Nat → Stmt KPrim) (pstart : Nat) (elf : Nat → Nat)
    (d : UData) : Option UData :=
  match uctx_arg3_spec d with
  | some arg3 =>
    if arg3 + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota then
      if d.cid * mc + 1 + mc ≤ num_id then
        if (d.AC d.cid).cchildren.length < mc then
          match uctx_arg2_spec d with
          | some arg1 =>
            if arg1 < num_id then
              match proc_create_spec num_id mc num_chan code pstart (elf arg1) arg3 d with
              | some (d1, n) =>
                match uctx_set_retval1_spec n d1 with
                | some d2 => uctx_set_errno_spec E_SUCC d2
                | none => none
              | none => none
            else none
          | none => none
        else uctx_set_errno_spec E_MEM d
      else uctx_set_errno_spec E_MEM d
    else uctx_set_errno_spec E_MEM d
  | none => none

/-- **`sys_dispatch_c_spec`**: argument 1 is the system-call number. -/
def sys_dispatch_c_spec (num_id mc num_chan : Nat) (code : Nat → Stmt KPrim) (pstart : Nat) (elf : Nat → Nat)
    (d : UData) : Option UData :=
  match uctx_arg1_spec d with
  | some arg1 =>
    if arg1 = 2 then trap_proc_create_spec num_id mc num_chan code pstart elf d
    else if arg1 = 26 then trap_get_quota_spec d
    else uctx_set_errno_spec E_INVAL_CALLNR d
  | none => none

/-! ## The code -/

/-- `qok = container_can_consume(curid, quota)`:
`if (quota_of < n) return 0; if (quota_of - n < usage_of) return 0; return 1;` -/
def ctCanConsumeS (cb : Nat) : Stmt APrim :=
  .seq (ctGetS cb "cq" "curid" 0)
    (.seq (ctGetS cb "cu" "curid" 1)
      (.ite (.bin .ltu (.var "cq") (.var "quota")) (.assign "qok" (.const 0))
        (.ite (.bin .ltu (.bin .sub (.var "cq") (.var "quota")) (.var "cu")) (.assign "qok" (.const 0))
          (.assign "qok" (.const 1)))))

/-- The tests of `sys_proc_create`, into the flag `ok`:
```
curid = get_curid(); quota = uctx_arg3();
qok = container_can_consume(curid, quota); nc = container_get_nchildren(curid);
ok = !(qok == 0 || NUM_ID < curid * MAX_CHILDREN + 1 + MAX_CHILDREN || nc == MAX_CHILDREN);
``` -/
def spcChecksS (cb cidb ucb num_id mc : Nat) : Stmt APrim :=
  .seq (getCuridS cidb "curid")
  (.seq (uctxArgS cidb ucb "quota" U_ECX)
  (.seq (ctCanConsumeS cb)
  (.seq (ctGetS cb "nc" "curid" 3)
    (.ite (.bin .eq (.var "qok") (.const 0)) (.assign "ok" (.const 0))
      (.ite (.bin .ltu (.const (BitVec.ofNat 32 num_id))
          (.bin .add (.bin .add (.bin .mul (.var "curid") (.const (BitVec.ofNat 32 mc))) (.const 1))
            (.const (BitVec.ofNat 32 mc))))
        (.assign "ok" (.const 0))
        (.ite (.bin .eq (.var "nc") (.const (BitVec.ofNat 32 mc))) (.assign "ok" (.const 0))
          (.assign "ok" (.const 1))))))))

/-- `elf_id = uctx_arg2(); fun_adr = ELF_ENTRY_LOC[elf_id];` -/
def spcArgsS (cidb ucb elb : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "elf_id" U_EBX)
    (.call "fun_adr" .pull [lkE, .bin .add (.const (BitVec.ofNat 32 elb)) (.var "elf_id")])

/-- `sys_proc_create`:
```
(the tests)
if (!ok) uctx_set_errno(E_MEM);
else {
  elf_id = uctx_arg2();
  proc_index = proc_create(ELF_LOC, ELF_ENTRY_LOC[elf_id], quota);
  uctx_set_retval1(proc_index); uctx_set_errno(0);
}
``` -/
def sysProcCreateK (cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart : Nat) : Stmt KPrim :=
  .seq (mapS .base (spcChecksS cb cidb ucb num_id mc))
    (.ite (.bin .eq (.var "ok") (.const 0))
      (mapS .base (uctxSetRegS cidb ucb U_EAX (.const 1)))
      (.seq (mapS .base (spcArgsS cidb ucb elb))
        (.seq (procCreateK cb mc tb qb num_proc num_chan cidb ucb pstart)
          (mapS .base (retDoneS cidb ucb (.var "r"))))))

/-- `syscall_dispatch_c`:
```
arg1 = uctx_arg1();
if (arg1 == SYS_spawn) sys_proc_create();
else if (arg1 == SYS_get_quota) sys_get_quota();
else uctx_set_errno(E_INVAL_CALLNR);
``` -/
def sysDispatchK (cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart : Nat) : Stmt KPrim :=
  .seq (mapS .base (uctxArgS cidb ucb "arg1" U_EAX))
    (.ite (.bin .eq (.var "arg1") (.const 2))
      (sysProcCreateK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart)
      (mapS .base (.ite (.bin .eq (.var "arg1") (.const 26)) (trapGetQuotaS cb cidb ucb)
        (uctxSetRegS cidb ucb U_EAX (.const 3)))))

/-- The table of entry points in the region. -/
def MatchELF (num_id elb : Nat) (elf : Nat → Nat) (b : Region) : Prop :=
  ∀ i, i < num_id → b (elb + i) = BitVec.ofNat 32 (elf i)

/-! ## Shapes of the specifications -/

/-- Writing a register changes only the user contexts. -/
theorem set_reg_shape {reg n : Nat} {d d' : UData} (h : uctx_set_reg_spec reg n d = some d') :
    ∃ U, d' = { d with uctxt := U } := by
  unfold uctx_set_reg_spec at h
  split at h
  · simp only [Option.some.injEq] at h
    exact ⟨_, h.symm⟩
  · cases h

theorem proc_create_cid {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart uentry q : Nat}
    {d d' : UData} {i : Nat} (h : proc_create_spec num_id mc num_chan code pstart uentry q d = some (d', i)) :
    d'.cid = d.cid := by
  unfold proc_create_spec at h
  simp only at h
  repeat' split at h
  all_goals first | (cases h; rfl) | cases h

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb elb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb

/-! ### `container_can_consume` -/

/-- **`container_can_consume` refines `container_can_consume_spec`.** The
container is in `curid`, the amount in `quota`, the answer in `qok`. -/
theorem ctCanConsumeU (hnum : cb + 5 * num_id < 2 ^ 32) {σ : Locals} {d : UData} {i n : Nat}
    (hid : σ "curid" = BitVec.ofNat 32 i) (hn : σ "quota" = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32)
    (hi : i < num_id) (hu : (d.AC i).cused = true) :
    Step εR c i0 MU F (ctCanConsumeS cb) σ d
      (((σ.set "cq" (BitVec.ofNat 32 (d.AC i).cquota)).set "cu" (BitVec.ofNat 32 (d.AC i).cusage)).set "qok"
        (BitVec.ofNat 32 (if n + (d.AC i).cusage ≤ (d.AC i).cquota then 1 else 0))) d := by
  refine ⟨by simp [Locals.set], fun l b hlk hcs hM => ?_⟩
  have hused := (matchC_all hM.1.1).mm.mAC.used hi hu
  have hq32 : (d.AC i).cquota < 2 ^ 32 := by rw [← hused.1]; exact (b _).isLt
  have hu32 : (d.AC i).cusage < 2 ^ 32 := by rw [← hused.2.1]; exact (b _).isLt
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (ctGetQuotaU (ida := ida) (ipb := ipb) (ucb := ucb) (cidb := cidb)
    (tb := tb) (qb := qb) (sb := sb) (num_chan := num_chan) (num_proc := num_proc) (pb := pb) (ib := ib)
    (fb := fb) (maxpage := maxpage) εR c i0 (F := fun _ => False) hnum "cq" "curid" (by decide) hid hi hu).2
    l b hlk hcs hM
  obtain ⟨l2, b2, r2, c2, m2, f2⟩ := (ctGetUsageU (ida := ida) (ipb := ipb) (ucb := ucb) (cidb := cidb)
    (tb := tb) (qb := qb) (sb := sb) (num_chan := num_chan) (num_proc := num_proc) (pb := pb) (ib := ib)
    (fb := fb) (maxpage := maxpage) εR c i0 (F := fun _ => False) hnum "cu" "curid" (by decide)
    (σ := σ.set "cq" (BitVec.ofNat 32 (d.AC i).cquota)) (d := d) (i := i) (by simp [Locals.set, hid]) hi
    hu).2 l1 b1 (by simpa [Locals.set] using hlk) c1 m1
  have hfr : ∀ k, ¬ F k → b2 k = b k := fun k _ => (f2 k (fun h => h)).trans (f1 k (fun h => h))
  have g1 := ltu_eval
    (σ := (σ.set "cq" (BitVec.ofNat 32 (d.AC i).cquota)).set "cu" (BitVec.ofNat 32 (d.AC i).cusage))
    (ea := .var "cq") (eb := .var "quota") (a := (d.AC i).cquota) (b := n) (by simp [Expr.eval, Locals.set])
    (by simp [Expr.eval, Locals.set, hn]) hq32 hn32
  by_cases h1 : (d.AC i).cquota < n
  · rw [if_pos h1] at g1
    rw [if_neg (by omega)]
    exact ⟨l2, b2, Runs.seq r1 (Runs.seq r2 (Runs.ite_true (by rw [g1]; decide)
      (asg_run "qok" (.const 0) rfl))), c2, m2, hfr⟩
  · rw [if_neg h1] at g1
    have g2 := ltu_eval
      (σ := (σ.set "cq" (BitVec.ofNat 32 (d.AC i).cquota)).set "cu" (BitVec.ofNat 32 (d.AC i).cusage))
      (ea := .bin .sub (.var "cq") (.var "quota")) (eb := .var "cu") (a := (d.AC i).cquota - n)
      (b := (d.AC i).cusage)
      (by simp [Expr.eval, BinOp.eval, Locals.set, hn]; exact ofNat_sub_le (by omega))
      (by simp [Expr.eval, Locals.set]) (by omega) hu32
    by_cases h2 : (d.AC i).cquota - n < (d.AC i).cusage
    · rw [if_pos h2] at g2
      rw [if_neg (by omega)]
      exact ⟨l2, b2, Runs.seq r1 (Runs.seq r2 (Runs.ite_false g1 (Runs.ite_true (by rw [g2]; decide)
        (asg_run "qok" (.const 0) rfl)))), c2, m2, hfr⟩
    · rw [if_neg h2] at g2
      rw [if_pos (by omega)]
      exact ⟨l2, b2, Runs.seq r1 (Runs.seq r2 (Runs.ite_false g1 (Runs.ite_false g2
        (asg_run "qok" (.const 1) rfl)))), c2, m2, hfr⟩

/-! ### `sys_proc_create` -/

/-- **The tests of `sys_proc_create`.** -/
theorem spcChecks_step (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hnum : cb + 5 * num_id < 2 ^ 32) {mc : Nat} (hov : num_id * mc + mc + 1 < 2 ^ 32) {σ : Locals} {d : UData}
    {q : Nat} (hcp : d.cid < num_proc) (hci : d.cid < num_id) (hu : (d.AC d.cid).cused = true)
    (hlen : (d.AC d.cid).cchildren.length ≤ mc) (e3 : uctx_arg3_spec d = some q) :
    ∃ σ', Step εR c i0 MU F (spcChecksS cb cidb ucb num_id mc) σ d σ' d ∧
      σ' "ok" = BitVec.ofNat 32 (if q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota ∧
        d.cid * mc + 1 + mc ≤ num_id ∧ (d.AC d.cid).cchildren.length < mc then 1 else 0) ∧
      σ' "quota" = BitVec.ofNat 32 q ∧ σ' "lk" = σ "lk" := by
  have hmul : d.cid * mc ≤ num_id * mc := Nat.mul_le_mul_right _ (Nat.le_of_lt hci)
  have hmc32 : mc < 2 ^ 32 := by omega
  have hnid32 : num_id < 2 ^ 32 := by omega
  obtain ⟨hq, hq32⟩ := arg_val e3
  let σ2 : Locals := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "curid" (BitVec.ofNat 32 d.cid) |>.set "quota"
    (BitVec.ofNat 32 q)
  let σ3 : Locals := ((σ2.set "cq" (BitVec.ofNat 32 (d.AC d.cid).cquota)).set "cu"
    (BitVec.ofNat 32 (d.AC d.cid).cusage)).set "qok"
    (BitVec.ofNat 32 (if q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota then 1 else 0))
  let σ4 : Locals := σ3.set "nc" (BitVec.ofNat 32 (d.AC d.cid).cchildren.length)
  have s1 := getCuridU (ida := ida) εR c i0 hL (F := F) "curid" (by decide) σ d
  have s2 : Step εR c i0 MU F (uctxArgS cidb ucb "quota" U_ECX) (σ.set "curid" (BitVec.ofNat 32 d.cid)) d σ2 d :=
    uctxArgU εR c i0 hL "quota" (by decide) (reg := U_ECX) (by decide) hcp hq
  have s3 : Step εR c i0 MU F (ctCanConsumeS cb) σ2 d σ3 d :=
    ctCanConsumeU εR c i0 hnum (σ := σ2) (d := d) (i := d.cid) (n := q) (by simp [σ2, Locals.set])
      (by simp [σ2]) hq32 hci hu
  have s4 : Step εR c i0 MU F (ctGetS cb "nc" "curid" 3) σ3 d σ4 d :=
    ctGetNchildrenU εR c i0 hnum "nc" "curid" (by decide) (σ := σ3) (d := d) (i := d.cid)
      (by simp [σ3, σ2, Locals.set]) hci hu
  have hqok : σ4 "qok" = BitVec.ofNat 32 (if q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota then 1 else 0) := by
    simp [σ4, σ3, Locals.set]
  have hnc : σ4 "nc" = BitVec.ofNat 32 (d.AC d.cid).cchildren.length := by simp [σ4]
  have hcur : σ4 "curid" = BitVec.ofNat 32 d.cid := by simp [σ4, σ3, σ2, Locals.set]
  have hlk4 : σ4 "lk" = σ "lk" := by simp [σ4, σ3, σ2, Locals.set]
  have hquo : σ4 "quota" = BitVec.ofNat 32 q := by simp [σ4, σ3, σ2, Locals.set]
  -- the second test, as a number
  have hsum : (Expr.bin .add (.bin .add (.bin .mul (.var "curid") (.const (BitVec.ofNat 32 mc))) (.const 1))
      (.const (BitVec.ofNat 32 mc))).eval σ4 = BitVec.ofNat 32 (d.cid * mc + 1 + mc) := by
    show σ4 "curid" * BitVec.ofNat 32 mc + (1 : Val) + BitVec.ofNat 32 mc = _
    rw [hcur, show (1 : Val) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_mul, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add]
  have g2 := ltu_eval (σ := σ4) (ea := .const (BitVec.ofNat 32 num_id))
    (eb := .bin .add (.bin .add (.bin .mul (.var "curid") (.const (BitVec.ofNat 32 mc))) (.const 1))
      (.const (BitVec.ofNat 32 mc))) (a := num_id) (b := d.cid * mc + 1 + mc) rfl hsum hnid32 (by omega)
  have pre := Step.seq s1 (Step.seq s2 (Step.seq s3 s4))
  have fin : ∀ (v : Nat) (tail : Step εR c i0 MU F
      (.ite (.bin .eq (.var "qok") (.const 0)) (.assign "ok" (.const 0))
        (.ite (.bin .ltu (.const (BitVec.ofNat 32 num_id))
            (.bin .add (.bin .add (.bin .mul (.var "curid") (.const (BitVec.ofNat 32 mc))) (.const 1))
              (.const (BitVec.ofNat 32 mc))))
          (.assign "ok" (.const 0))
          (.ite (.bin .eq (.var "nc") (.const (BitVec.ofNat 32 mc))) (.assign "ok" (.const 0))
            (.assign "ok" (.const 1))))) σ4 d (σ4.set "ok" (BitVec.ofNat 32 v)) d),
      ∃ σ', Step εR c i0 MU F (spcChecksS cb cidb ucb num_id mc) σ d σ' d ∧ σ' "ok" = BitVec.ofNat 32 v ∧
        σ' "quota" = BitVec.ofNat 32 q ∧ σ' "lk" = σ "lk" := fun v tail =>
    ⟨_, Step.seq s1 (Step.seq s2 (Step.seq s3 (Step.seq s4 tail))), by simp,
      by rw [Locals.set_other _ _ (by decide)]; exact hquo,
      by rw [Locals.set_other _ _ (by decide)]; exact hlk4⟩
  by_cases h1 : q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota
  · rw [if_pos h1] at hqok
    by_cases h2 : d.cid * mc + 1 + mc ≤ num_id
    · rw [if_neg (by omega)] at g2
      by_cases h3 : (d.AC d.cid).cchildren.length < mc
      · rw [if_pos ⟨h1, h2, h3⟩]
        exact fin 1 (Step.ite_false (eqc_false (b := 0) hqok (by decide) (by decide) (by decide))
          (Step.ite_false g2 (Step.ite_false (eqc_false hnc (by omega) hmc32 (by omega))
            (Step.assign' "ok" (by decide) (.const 1) rfl))))
      · rw [if_neg (fun h => h3 h.2.2)]
        exact fin 0 (Step.ite_false (eqc_false (b := 0) hqok (by decide) (by decide) (by decide))
          (Step.ite_false g2 (Step.ite_true (eqc_true hnc (by omega))
            (Step.assign' "ok" (by decide) (.const 0) rfl))))
    · rw [if_pos (by omega)] at g2
      rw [if_neg (fun h => h2 h.2.1)]
      exact fin 0 (Step.ite_false (eqc_false (b := 0) hqok (by decide) (by decide) (by decide))
        (Step.ite_true (by rw [g2]; decide) (Step.assign' "ok" (by decide) (.const 0) rfl)))
  · rw [if_neg h1] at hqok
    rw [if_neg (fun h => h1 h.1)]
    exact fin 0 (Step.ite_true (eqc_true (b := 0) hqok rfl) (Step.assign' "ok" (by decide) (.const 0) rfl))

/-- Writing a register of the caller, against the specification. -/
theorem setReg_step (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hF : ∀ k, UCF ucb num_proc k → F k) {reg : Nat} (hreg : reg < 17) {ve : Expr} {σ : Locals} {d d' : UData}
    {n : Nat} (hve : ve.eval (σ.set "curid" (BitVec.ofNat 32 d.cid)) = BitVec.ofNat 32 n)
    (hcid : d.cid < num_proc) (h : uctx_set_reg_spec reg n d = some d') :
    Step εR c i0 MU F (uctxSetRegS cidb ucb reg ve) σ d ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "_" 0)
      d' := by
  unfold uctx_set_reg_spec at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact uctxSetRegU εR c i0 hL hF hreg hve hcid
  · cases h

/-- Reading an entry point. -/
theorem elf_run (hel : elb + num_id ≤ 2 ^ 32) {l : RLog} {b : Region} (hcs : CS1 c i0 l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i0) {i : Nat} (hi : i < num_id) (he : σ "elf_id" = BitVec.ofNat 32 i)
    {elf : Nat → Nat} (hE : MatchELF num_id elb elf b) :
    Runs (rprimsA εR c) (.call "fun_adr" .pull [lkE, .bin .add (.const (BitVec.ofNat 32 elb)) (.var "elf_id")])
      σ l (σ.set "fun_adr" (BitVec.ofNat 32 (elf i))) l := by
  have hr := rd_run (εR := εR) hcs hlk "fun_adr"
    (.bin .add (.const (BitVec.ofNat 32 elb)) (.var "elf_id")) (n := elb + i) (by
      show (BitVec.ofNat 32 elb + σ "elf_id").toNat = _
      rw [he, ← BitVec.ofNat_add, tn (by omega)])
  rw [hE i hi] at hr
  exact hr

/-- **`sys_proc_create` on the kernel machine.** -/
theorem sysProcCreate_run (code : Nat → Stmt KPrim)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hnn : num_id ≤ num_proc) (hel0 : cb + 5 * num_id ≤ elb)
    (hel1 : elb + num_id ≤ sb) {mc pstart : Nat} {elf : Nat → Nat} (hov : num_id * mc + mc + 1 < 2 ^ 32)
    (hps : pstart < 2 ^ 32) {σ : Locals} {K : Cont KPrim} {l : RLog} {b : Region} {d d' : UData}
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MU d b) (hE : MatchELF num_id elb elf b)
    (hcp : d.cid < num_proc) (hI : AInv num_proc num_chan d.toAData) (hCV : Container_valid num_id mc d.AC)
    (hcu : (d.AC d.cid).cused = true)
    (hs : trap_proc_create_spec num_id mc num_chan code pstart elf d = some d') :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      KStar εR c code
        ⟨⟨sysProcCreateK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart, K, σ⟩, d.kctxt, l⟩
        ⟨⟨.skip, K, σ'⟩, d'.kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MU d' b' ∧ MatchELF num_id elb elf b' ∧ σ' "lk" = σ "lk" ∧
      (∀ k, ¬ CreateF cb num_id tb num_proc qb num_chan ucb k → b' k = b k) ∧ d'.cid = d.cid := by
  have hCL := hL.ilay.clay
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb
  have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse
  have hpb32 := ucb_lt hL
  have hci := hCV.cvalid_id d.cid hcu
  have hlen := hCV.cvalid_max_children d.cid hcu
  have hs0 := hs
  unfold trap_proc_create_spec at hs
  cases e3 : uctx_arg3_spec d with
  | none => rw [e3] at hs; cases hs
  | some q =>
    rw [e3] at hs
    simp only at hs
    obtain ⟨σ1, hst, hok, hquo, hlk1⟩ := spcChecks_step (ida := ida) (cidb := cidb) εR c i0 hL
      (F := fun _ => False) hnum hov (σ := σ) hcp hci hcu hlen e3
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := hst.2 l b hlk hcs hM
    have hb1 : b = b1 := (funext (fun k => f1 k (fun h => h))).symm
    subst hb1
    have hlk1' : (σ1 "lk").toNat = i0 := by rw [hlk1]; exact hlk
    have k1 := kstar_seq (εR := εR) (c := c) (code := code) r1
      (.ite (.bin .eq (.var "ok") (.const 0)) (mapS .base (uctxSetRegS cidb ucb U_EAX (.const 1)))
        (.seq (mapS .base (spcArgsS cidb ucb elb))
          (.seq (procCreateK cb mc tb qb num_proc num_chan cidb ucb pstart)
            (mapS .base (retDoneS cidb ucb (.var "r")))))) K d.kctxt
    have k2 := kstep_ite (εR := εR) (c := c) (code := code) (.bin .eq (.var "ok") (.const 0))
      (mapS .base (uctxSetRegS cidb ucb U_EAX (.const 1)))
      (.seq (mapS .base (spcArgsS cidb ucb elb))
        (.seq (procCreateK cb mc tb qb num_proc num_chan cidb ucb pstart)
          (mapS .base (retDoneS cidb ucb (.var "r"))))) K σ1 d.kctxt l1
    by_cases hall : q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota ∧ d.cid * mc + 1 + mc ≤ num_id ∧
        (d.AC d.cid).cchildren.length < mc
    · rw [if_pos hall] at hok
      obtain ⟨h1, h2, h3⟩ := hall
      rw [if_pos h1, if_pos h2, if_pos h3] at hs
      cases e2 : uctx_arg2_spec d with
      | none => rw [e2] at hs; cases hs
      | some a1 =>
        rw [e2] at hs
        simp only at hs
        by_cases ha : a1 < num_id
        · rw [if_pos ha] at hs
          cases hpc : proc_create_spec num_id mc num_chan code pstart (elf a1) q d with
          | none => rw [hpc] at hs; cases hs
          | some pr =>
            obtain ⟨d1, n⟩ := pr
            rw [hpc] at hs
            simp only at hs
            cases hr1 : uctx_set_retval1_spec n d1 with
            | none => rw [hr1] at hs; cases hs
            | some d2 =>
              rw [hr1] at hs
              simp only at hs
              have hg : (Expr.bin .eq (.var "ok") (.const 0)).eval σ1 = 0 :=
                eqc_false (b := 0) hok (by decide) (by decide) (by decide)
              rw [if_pos hg] at k2
              -- `elf_id = uctx_arg2(); fun_adr = ELF_ENTRY_LOC[elf_id];`
              obtain ⟨l2, b2, r2, c2, m2, f2⟩ := (uctxArgU (ida := ida) (cidb := cidb) εR c i0 hL
                (F := fun _ => False) "elf_id" (by decide) (reg := U_EBX) (by decide) (σ := σ1) hcp
                (arg_val e2).1).2 l1 b hlk1' c1 m1
              have hb2 : b = b2 := (funext (fun k => f2 k (fun h => h))).symm
              subst hb2
              have r3 := elf_run (elb := elb) εR c i0 (by omega) c2
                (σ := (σ1.set "curid" (BitVec.ofNat 32 d.cid)).set "elf_id" (BitVec.ofNat 32 a1))
                (by simpa [Locals.set] using hlk1') ha (by simp) hE
              have hargs : Runs (rprimsA εR c) (spcArgsS cidb ucb elb) σ1 l1
                  (((σ1.set "curid" (BitVec.ofNat 32 d.cid)).set "elf_id" (BitVec.ofNat 32 a1)).set "fun_adr"
                    (BitVec.ofNat 32 (elf a1))) l2 := Runs.seq r2 r3
              -- `proc_create`
              obtain ⟨σ4, l4, b4, hks, c4, m4, k4, hr4, hI4, f4⟩ := proc_create_run εR c i0 code hL hnum hnn
                (σ := ((σ1.set "curid" (BitVec.ofNat 32 d.cid)).set "elf_id" (BitVec.ofNat 32 a1)).set "fun_adr"
                  (BitVec.ofNat 32 (elf a1))) (K := .seq (mapS .base (retDoneS cidb ucb (.var "r"))) K) hps
                (by simpa [Locals.set] using hlk1') c2 m2 (by simp [Locals.set, hquo]) (by simp) hI hCV hcu hpc
              -- `uctx_set_retval1(proc_index); uctx_set_errno(0);`
              have hcid1 : d1.cid < num_proc := by rw [proc_create_cid hpc]; exact hcp
              obtain ⟨σ5, hst5, hlk5⟩ := retDone_step (ida := ida) (cidb := cidb) εR c i0 hL
                (F := UCF ucb num_proc) (fun _ h => h) (ve := .var "r") (σ := σ4)
                (by simp [Expr.eval, Locals.set, hr4]) hcid1 hr1 hs
              obtain ⟨l5, b5, r5, c5, m5, f5⟩ := hst5.2 l4 b4
                (by rw [k4]; simpa [Locals.set] using hlk1') c4 m4
              have hk' : d'.kctxt = d1.kctxt := by
                obtain ⟨U1, e1⟩ := set_reg_shape hr1
                obtain ⟨U2, e2'⟩ := set_reg_shape hs
                rw [e2', e1]
              have hcid' : d'.cid = d.cid := by
                obtain ⟨U1, e1⟩ := set_reg_shape hr1
                obtain ⟨U2, e2'⟩ := set_reg_shape hs
                rw [e2', e1]
                show d1.cid = d.cid
                exact proc_create_cid hpc
              refine ⟨σ5, l5, b5, ?_, c5, m5, fun i hi => ?_, ?_, fun k hk => ?_, hcid'⟩
              · rw [hk']
                exact k1.trans (.step k2 ((kstar_seq hargs _ K d.kctxt).trans
                  ((KStar.single (kstep_seq _ _ K _ d.kctxt l2)).trans (hks.trans
                    ((KStar.single (kstep_skip_seq _ K σ4 d1.kctxt l4)).trans (kstar_base r5 K d1.kctxt))))))
              · rw [f5 _ (fun h => by unfold UCF at h; omega), f4 _ (fun h => by
                  rcases h with (⟨h3', h4'⟩ | ⟨h3', h4'⟩ | ⟨h3', h4'⟩) | ⟨h3', h4'⟩ <;> omega)]
                exact hE i hi
              · rw [hlk5, k4]; simp [Locals.set, hlk1]
              · rw [f5 k (fun h => hk (Or.inr h)), f4 k hk]
        · rw [if_neg ha] at hs; cases hs
    · rw [if_neg hall] at hok
      have hs' : uctx_set_errno_spec E_MEM d = some d' := by
        by_cases h1 : q + (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota
        · rw [if_pos h1] at hs
          by_cases h2 : d.cid * mc + 1 + mc ≤ num_id
          · rw [if_pos h2] at hs
            by_cases h3 : (d.AC d.cid).cchildren.length < mc
            · exact absurd ⟨h1, h2, h3⟩ hall
            · rw [if_neg h3] at hs; exact hs
          · rw [if_neg h2] at hs; exact hs
        · rw [if_neg h1] at hs; exact hs
      have hg : ¬ (Expr.bin .eq (.var "ok") (.const 0)).eval σ1 = 0 := eqc_true (b := 0) hok rfl
      rw [if_neg hg] at k2
      obtain ⟨l2, b2, r2, c2, m2, f2⟩ := (setReg_step (ida := ida) (cidb := cidb) εR c i0 hL
        (F := UCF ucb num_proc) (fun _ h => h) (reg := U_EAX) (by decide) (ve := .const 1) (σ := σ1)
        (n := E_MEM) rfl hcp hs').2 l1 b hlk1' c1 m1
      have hk' : d'.kctxt = d.kctxt := by
        obtain ⟨U1, e1⟩ := set_reg_shape hs'
        rw [e1]
      have hcid' : d'.cid = d.cid := by
        obtain ⟨U1, e1⟩ := set_reg_shape hs'
        rw [e1]
      refine ⟨(σ1.set "curid" (BitVec.ofNat 32 d.cid)).set "_" 0, l2, b2, ?_, c2, m2, fun i hi => ?_, ?_,
        fun k hk => f2 k (fun h => hk (Or.inr h)), hcid'⟩
      · rw [hk']
        exact k1.trans (.step k2 (kstar_base r2 K d.kctxt))
      · rw [f2 _ (fun h => by unfold UCF at h; omega)]
        exact hE i hi
      · simp [Locals.set, hlk1]

/-- `sys_get_quota` changes only the user contexts. -/
theorem get_quota_shape {d d' : UData} (h : trap_get_quota_spec d = some d') : ∃ U, d' = { d with uctxt := U } := by
  unfold trap_get_quota_spec at h
  repeat' split at h
  all_goals first
    | cases h
    | (rename_i d1 h1
       obtain ⟨U1, e1⟩ := set_reg_shape h1
       obtain ⟨U2, e2⟩ := set_reg_shape h
       exact ⟨U2, by rw [e2, e1]⟩)

/-- **`syscall_dispatch_c` on the kernel machine.** -/
theorem sysDispatch_run (code : Nat → Stmt KPrim)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hnn : num_id ≤ num_proc) (hel0 : cb + 5 * num_id ≤ elb)
    (hel1 : elb + num_id ≤ sb) {mc pstart : Nat} {elf : Nat → Nat} (hov : num_id * mc + mc + 1 < 2 ^ 32)
    (hps : pstart < 2 ^ 32) {σ : Locals} {K : Cont KPrim} {l : RLog} {b : Region} {d d' : UData}
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MU d b) (hE : MatchELF num_id elb elf b)
    (hcp : d.cid < num_proc) (hI : AInv num_proc num_chan d.toAData) (hCV : Container_valid num_id mc d.AC)
    (hcu : (d.AC d.cid).cused = true)
    (hs : sys_dispatch_c_spec num_id mc num_chan code pstart elf d = some d') :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      KStar εR c code
        ⟨⟨sysDispatchK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart, K, σ⟩, d.kctxt, l⟩
        ⟨⟨.skip, K, σ'⟩, d'.kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MU d' b' ∧ MatchELF num_id elb elf b' ∧ σ' "lk" = σ "lk" ∧
      (∀ k, ¬ CreateF cb num_id tb num_proc qb num_chan ucb k → b' k = b k) ∧ d'.cid = d.cid := by
  have hCL := hL.ilay.clay
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb
  have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse
  have hci := hCV.cvalid_id d.cid hcu
  unfold sys_dispatch_c_spec at hs
  cases e1 : uctx_arg1_spec d with
  | none => rw [e1] at hs; cases hs
  | some a =>
    rw [e1] at hs
    simp only at hs
    obtain ⟨ha, ha32⟩ := arg_val e1
    -- `arg1 = uctx_arg1()`
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (uctxArgU (ida := ida) (cidb := cidb) εR c i0 hL (F := fun _ => False)
      "arg1" (by decide) (reg := U_EAX) (by decide) (σ := σ) hcp ha).2 l b hlk hcs hM
    have hb1 : b = b1 := (funext (fun k => f1 k (fun h => h))).symm
    subst hb1
    have harg : ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "arg1" (BitVec.ofNat 32 a)) "arg1" =
        BitVec.ofNat 32 a := by simp
    have hlk1 : (((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "arg1" (BitVec.ofNat 32 a)) "lk").toNat = i0 := by
      simpa [Locals.set] using hlk
    have k1 := kstar_seq (εR := εR) (c := c) (code := code) r1
      (.ite (.bin .eq (.var "arg1") (.const 2))
        (sysProcCreateK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart)
        (mapS .base (.ite (.bin .eq (.var "arg1") (.const 26)) (trapGetQuotaS cb cidb ucb)
          (uctxSetRegS cidb ucb U_EAX (.const 3))))) K d.kctxt
    have k2 := kstep_ite (εR := εR) (c := c) (code := code) (.bin .eq (.var "arg1") (.const 2))
      (sysProcCreateK cb mc tb qb num_proc num_chan cidb ucb elb num_id pstart)
      (mapS .base (.ite (.bin .eq (.var "arg1") (.const 26)) (trapGetQuotaS cb cidb ucb)
        (uctxSetRegS cidb ucb U_EAX (.const 3)))) K
      ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "arg1" (BitVec.ofNat 32 a)) d.kctxt l1
    by_cases h2 : a = 2
    · rw [if_pos h2] at hs
      have hg : ¬ (Expr.bin .eq (.var "arg1") (.const 2)).eval
          ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "arg1" (BitVec.ofNat 32 a)) = 0 :=
        eqc_true (b := 2) harg h2
      rw [if_neg hg] at k2
      obtain ⟨σ', l', b', hks, hcs', hM', hE', hlk', hf', hc'⟩ := sysProcCreate_run εR c i0 code hL hnum hnn
        hel0 hel1 hov hps (K := K) hlk1 c1 m1 hE hcp hI hCV hcu hs
      exact ⟨σ', l', b', k1.trans (.step k2 hks), hcs', hM', hE', by rw [hlk']; simp [Locals.set], hf', hc'⟩
    · rw [if_neg h2] at hs
      have hg : (Expr.bin .eq (.var "arg1") (.const 2)).eval
          ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "arg1" (BitVec.ofNat 32 a)) = 0 :=
        eqc_false (b := 2) harg ha32 (by decide) h2
      rw [if_pos hg] at k2
      by_cases h26 : a = 26
      · rw [if_pos h26] at hs
        obtain ⟨σ2, l2, b2, d2, r2, c2, m2, k2', f2, hq2⟩ := trapGetQuota_triple (ida := ida) εR c i0 hL hnum
          ((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "arg1" (BitVec.ofNat 32 a)) l1 b d hlk1 c1 m1
          ⟨hcp, hci, hCV.cvalid_usage d.cid hcu, d', hs⟩
        rw [hs] at hq2
        simp only [Option.some.injEq] at hq2
        subst hq2
        have hk' : d'.kctxt = d.kctxt := by
          obtain ⟨U, e⟩ := get_quota_shape hs
          rw [e]
        refine ⟨σ2, l2, b2, ?_, c2, m2, fun i hi => ?_, by rw [k2']; simp [Locals.set],
          fun k hk => f2 k (fun h => hk (Or.inr h)), by
            obtain ⟨U, e⟩ := get_quota_shape hs
            rw [e]⟩
        · rw [hk']
          exact k1.trans (.step k2 (kstar_base (Runs.ite_true (eqc_true (b := 26) harg h26) r2) K d.kctxt))
        · rw [f2 _ (fun h => by unfold UCF at h; omega)]
          exact hE i hi
      · rw [if_neg h26] at hs
        obtain ⟨l2, b2, r2, c2, m2, f2⟩ := (setReg_step (ida := ida) (cidb := cidb) εR c i0 hL
          (F := UCF ucb num_proc) (fun _ h => h) (reg := U_EAX) (by decide) (ve := .const 3)
          (σ := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "arg1" (BitVec.ofNat 32 a)) (n := E_INVAL_CALLNR)
          rfl hcp hs).2 l1 b hlk1 c1 m1
        have hk' : d'.kctxt = d.kctxt := by
          obtain ⟨U, e⟩ := set_reg_shape hs
          rw [e]
        refine ⟨((((σ.set "curid" (BitVec.ofNat 32 d.cid)).set "arg1" (BitVec.ofNat 32 a)).set "curid"
          (BitVec.ofNat 32 d.cid)).set "_" 0), l2, b2, ?_, c2, m2, fun i hi => ?_, by simp [Locals.set],
          fun k hk => f2 k (fun h => hk (Or.inr h)), by
            obtain ⟨U, e⟩ := set_reg_shape hs
            rw [e]⟩
        · rw [hk']
          exact k1.trans (.step k2 (kstar_base (Runs.ite_false
            (eqc_false (b := 26) harg ha32 (by decide) h26) r2) K d.kctxt))
        · rw [f2 _ (fun h => by unfold UCF at h; omega)]
          exact hE i hi

end Code

end TTrap
