import CertiKOS.UMachine

/-!
# mCertiKOS `PProc`: processes, ported

Ported from `objects/ObjProc.v`: `proc_create_spec`, `proc_exit_user_spec`,
`proc_start_user_spec`. Ported from `proc/PUCtxtIntroCSource.v`: the C code of
`proc_create`. Ported from `proc/ProcGenAsmSource.v`: `proc_start_user` and
`proc_exit_user`, which are assembly there.

* `toK`, `putK`: the scheduler's state (`KData`) as a view of the top state.
  `matchU_putC` carries a result of the scheduler up, using the footprints
  its theorems state.
* `proc_create_factors`: `proc_create_spec` is `thread_spawn_spec` followed
  by the seven writes to the child's user context.
* `proc_create_run`: **`proc_create` on the kernel machine does what
  `proc_create_spec` says.** The child's kernel context starts at
  `proc_start_user`, so the first time it is scheduled it goes to user mode.
* `procExitUser_triple`: **`proc_exit_user` refines its specification**: the
  registers of the trap are saved, and the kernel's page table is loaded.
* `procStartUser_run`: **`proc_start_user` refines its specification**: the
  process's page table is loaded and its registers are in `u0` … `u16`.
* `start_user_ustar`: on the machine with user mode, a kernel computation
  that ends with `proc_start_user` on an empty stack leaves the kernel with
  the process's user context.

What differs:
* `trap_in`, `pt_in` and `pt_out` only change the flags `ikern` and `ipt`,
  which no cell holds. They have no code here; the theorems change the flags
  where mCertiKOS calls them.
* `elf_load` is left out. In mCertiKOS it is a pseudo-instruction that does
  not change the abstract state.
* `proc_create_spec` does not check that the caller's container is in use;
  mCertiKOS has that as an invariant. The theorems assume it.
* `tss_switch` is left out (there is no task-state segment here).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PProc

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt UMach MCPU
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## The scheduler's view of the top state -/

/-- The part of the top state the scheduler works on. -/
def toK (u : UData) : KData := { toCData := u.toCData, kctxt := u.kctxt }

/-- Put a result of the scheduler back. -/
def putK (u : UData) (k : KData) : UData := { u with toCData := k.toCData, kctxt := k.kctxt }

/-! ## Specifications (`ObjProc.v`) -/

/-- The user context of a new process: user segments, the user stack at the
top of user memory, interrupts on, and the entry point. -/
def initUctx (uentry : Nat) (uc : UContext) : UContext :=
  setAt (setAt (setAt (setAt (setAt (setAt (setAt uc U_ES (some 35)) U_DS (some 35)) U_CS (some 27)) U_SS
    (some 35)) U_ESP (some (BitVec.ofNat 32 (983040 * 4096)))) U_EFLAGS (some 512)) U_EIP
    (some (BitVec.ofNat 32 uentry))

/-- **`proc_create_spec`**: a child of the current process with quota `q`,
ready to run, that will start in user mode at `uentry`. `pstart` is
`proc_start_user`, as an index into `code`. -/
def proc_create_spec (num_id mc num_chan : Nat) (code : Nat → Stmt KPrim) (pstart uentry q : Nat) (d : UData) :
    Option (UData × Nat) :=
  let c := d.AC d.cid
  let i := d.cid * mc + 1 + c.cchildren.length
  if d.ikern = true ∧ d.ihost = true ∧ d.pg = true ∧ d.ipt = true ∧ i < num_id ∧ c.cchildren.length < mc ∧
      q + c.cusage ≤ c.cquota then
    match d.abq num_chan with
    | .AbQValid l =>
      some ({ d with
        AC := setAt (setAt d.AC d.cid ⟨c.cquota, c.cusage + q, c.cparent, i :: c.cchildren, c.cused⟩) i
          ⟨q, 0, d.cid, [], true⟩
        kctxt := setAt d.kctxt i { d.kctxt i with cont := .stop, stmt := code pstart }
        abtcb := setAt d.abtcb i (.AbTCBValid .READY num_chan)
        abq := setAt d.abq num_chan (.AbQValid (i :: l))
        uctxt := setAt d.uctxt i (initUctx uentry (d.uctxt i)) }, i)
    | .AbQUndef => none
  else none

/-- **`proc_exit_user_spec`**: entering the kernel. The registers of the trap
are saved, and the kernel's page table is in use. -/
def proc_exit_user_spec (rs : UContext) (d : UData) : Option UData :=
  if d.ikern = false ∧ d.pg = true ∧ d.ihost = true then
    some { d with ikern := true, PT := 0, ipt := true, uctxt := setAt d.uctxt d.cid rs }
  else none

/-- **`proc_start_user_spec`**: leaving the kernel. The current process's page
table is in use, and its user context is returned. -/
def proc_start_user_spec (d : UData) : Option (UData × UContext) :=
  if d.ikern = true ∧ d.pg = true ∧ d.ihost = true ∧ d.ipt = true ∧ d.init = true then
    some ({ d with ikern := false, ipt := false, PT := d.cid }, d.uctxt d.cid)
  else none

/-- `proc_create_spec` is `thread_spawn_spec`, then the child's user context. -/
theorem proc_create_factors {num_id mc num_chan : Nat} {code : Nat → Stmt KPrim} {pstart uentry q : Nat}
    {d d' : UData} {i : Nat} (hcu : (d.AC d.cid).cused = true)
    (hs : proc_create_spec num_id mc num_chan code pstart uentry q d = some (d', i)) :
    ∃ k1, thread_spawn_spec num_id mc num_chan code pstart d.cid q (toK d) = some (k1, i) ∧
      d' = { putK d k1 with uctxt := setAt d.uctxt i (initUctx uentry (d.uctxt i)) } ∧
      d.pg = true ∧ d.ipt = true ∧ i < num_id ∧ d.cid < num_id := by
  unfold proc_create_spec at hs
  simp only at hs
  split at hs
  · rename_i hc
    obtain ⟨hik, hih, hpg, hipt, hi, hlen, hq⟩ := hc
    cases habq : d.abq num_chan with
    | AbQUndef => rw [habq] at hs; cases hs
    | AbQValid l =>
      rw [habq] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨hd, hi'⟩ := hs
      subst hd; subst hi'
      have hcid : d.cid < num_id := by
        have hmul : d.cid ≤ d.cid * mc := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have hsplit : container_split_spec num_id mc d.cid q d.toRData = some (
          { d.toRData with
            AC := setAt (setAt d.AC d.cid ⟨(d.AC d.cid).cquota, (d.AC d.cid).cusage + q, (d.AC d.cid).cparent,
                (d.cid * mc + 1 + (d.AC d.cid).cchildren.length) :: (d.AC d.cid).cchildren, (d.AC d.cid).cused⟩)
              (d.cid * mc + 1 + (d.AC d.cid).cchildren.length) ⟨q, 0, d.cid, [], true⟩ },
          d.cid * mc + 1 + (d.AC d.cid).cchildren.length) := by
        unfold container_split_spec
        simp only
        rw [if_pos ⟨hcu, hi, hlen, hq⟩]
      refine ⟨({ toK d with
          AC := setAt (setAt d.AC d.cid ⟨(d.AC d.cid).cquota, (d.AC d.cid).cusage + q, (d.AC d.cid).cparent,
              (d.cid * mc + 1 + (d.AC d.cid).cchildren.length) :: (d.AC d.cid).cchildren, (d.AC d.cid).cused⟩)
            (d.cid * mc + 1 + (d.AC d.cid).cchildren.length) ⟨q, 0, d.cid, [], true⟩
          kctxt := setAt d.kctxt (d.cid * mc + 1 + (d.AC d.cid).cchildren.length)
            { d.kctxt (d.cid * mc + 1 + (d.AC d.cid).cchildren.length) with cont := .stop, stmt := code pstart }
          abtcb := setAt d.abtcb (d.cid * mc + 1 + (d.AC d.cid).cchildren.length) (.AbTCBValid .READY num_chan)
          abq := setAt d.abq num_chan
            (.AbQValid ((d.cid * mc + 1 + (d.AC d.cid).cchildren.length) :: l)) } : KData),
        ?_, rfl, hpg, hipt, hi, hcid⟩
      unfold thread_spawn_spec kctxt_new_spec pt_new_spec
      have e1 : (toK d).toPTData = d.toPTData := rfl
      rw [e1, if_pos ⟨hpg, hipt⟩, hsplit]
      simp only
      have e2 : (toK d).abq num_chan = d.abq num_chan := rfl
      rw [e2, habq]
      rfl
  · cases hs

/-! ## The code -/

/-- The seven writes to the child's user context
(`uctx_set(r, U_ES, 35); …; uctx_set_eip(r, fun_adr);`). -/
def procCreateTailS (ucb : Nat) : Stmt APrim :=
  .seq (uctxSetS ucb (.var "r") (.const 8) (.const 35))
  (.seq (uctxSetS ucb (.var "r") (.const 9) (.const 35))
  (.seq (uctxSetS ucb (.var "r") (.const 13) (.const 27))
  (.seq (uctxSetS ucb (.var "r") (.const 16) (.const 35))
  (.seq (uctxSetS ucb (.var "r") (.const 15) (.const (BitVec.ofNat 32 (983040 * 4096))))
  (.seq (uctxSetS ucb (.var "r") (.const 14) (.const 512))
    (uctxSetEipS ucb (.var "r") (.var "fun_adr")))))))

/-- The arguments of `thread_spawn`: `id = get_curid(); amt = quota;
entry = proc_start_user;` -/
def procCreatePreS (cidb pstart : Nat) : Stmt APrim :=
  .seq (getCuridS cidb "id")
    (.seq (.assign "amt" (.var "quota")) (.assign "entry" (.const (BitVec.ofNat 32 pstart))))

/-- `proc_create(elf_addr, fun_adr, quota)`, result in `r`:
```
id = get_curid();
r = thread_spawn(proc_start_user, id, quota);
uctx_set(r, U_ES, 35); uctx_set(r, U_DS, 35); uctx_set(r, U_CS, 27); uctx_set(r, U_SS, 35);
uctx_set(r, U_ESP, kern_high * PgSize); uctx_set(r, U_EFLAGS, 512); uctx_set_eip(r, fun_adr);
``` -/
def procCreateK (cb mc tb qb num_proc num_chan cidb ucb pstart : Nat) : Stmt KPrim :=
  .seq (mapS .base (procCreatePreS cidb pstart))
    (.seq (threadSpawnK cb mc tb qb num_proc num_chan) (mapS .base (procCreateTailS ucb)))

/-- `proc_exit_user`: `trap_in; save_uctx(u0, …, u16); set_pt(0); pt_in;` -/
def procExitUserS (cidb ucb pb cpub : Nat) : Stmt APrim :=
  .seq (saveUctxS cidb ucb) (setPTS pb cpub (.const 0))

/-- `proc_start_user`: `cid = get_curid(); pt_out; set_pt(cid);` then
`restore_uctx(cid)`, whose reads are here and whose `trap_out` is the
machine's. -/
def procStartUserS (cidb ucb pb cpub : Nat) : Stmt APrim :=
  .seq (getCuridS cidb "curid") (.seq (setPTS pb cpub (.var "curid")) (loadRegsS ucb 17))

/-- The cells `proc_create` may write. -/
def CreateF (cb num_id tb num_proc qb num_chan ucb : Nat) (k : Nat) : Prop :=
  SpawnF cb num_id tb num_proc qb num_chan k ∨ UCF ucb num_proc k

theorem uset_uset (U : UContextPool) (i : Nat) (A : UContext) (n : Nat) (w : Option Val) :
    setAt (setAt U i A) i (setAt (setAt U i A i) n w) = setAt U i (setAt A n w) := by
  rw [setAt_eq, setAt_setAt]

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub : Nat}

local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb
local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb

/-- The top state with the two register words. -/
def MatchUP (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub : Nat) (d : UData)
    (b : Region) : Prop :=
  MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb d b ∧
    MatchCPU num_proc pb cpub d.toPTData b

local notation "MUP" => MatchUP maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb cpub

/-- **A result of the scheduler, in the top state.** The channels and the
user contexts are after the current-thread word, which is as far as the
scheduler writes. -/
theorem matchU_putC (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    {u : UData} {b b' : Region} {c1 : CData} (κ : Nat → KCtx) (hM : MU u b) (hC : MC c1 b')
    (hf : ∀ k, cidb < k → k < pb → b' k = b k) : MU ({ u with toCData := c1, kctxt := κ } : UData) b' := by
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hL.ilay.hie
  refine ⟨⟨hC, fun j hj => ?_⟩, fun i n hi hn v hv => ?_⟩
  · show MatchCh (u.syncchpool j) _ _ _
    rw [hf _ (by unfold tcell; omega) (by unfold tcell; omega),
      hf _ (by unfold tcell; omega) (by unfold tcell; omega),
      hf _ (by unfold tcell; omega) (by unfold tcell; omega)]
    exact hM.1.2 j hj
  · rw [hf _ (by omega) (by omega)]
    exact hM.2 i n hi hn v hv

/-- **A new page table in `CR3`, and new mode flags.** No cell holds `ipt`
or `ikern`, and only the word at `cpub` holds `PT`. -/
theorem matchUP_cpu (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) {d : UData} {b b' : Region} (hM : MUP d b)
    (n : Nat) (t k : Bool) (hfr : ∀ j, j ≠ cpub → b' j = b j)
    (hc : n < num_proc → b' cpub = BitVec.ofNat 32 (pb + n * 1024)) :
    MUP ({ d with PT := n, ipt := t, ikern := k } : UData) b' := by
  have hCL := hL.ilay.clay
  have hLay := hCL.qlay.tlay.slay.lay
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hL.ilay.hie
  have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse; have := hCL.qlay.tlay.htb
  have := hCL.qlay.tlay.hte; have := hCL.qlay.hqb; have := hCL.qlay.hqe; have := hCL.hcb; have := hCL.hce
  obtain ⟨⟨⟨hC, hS⟩, hU⟩, hP⟩ := hM
  have hA := matchAll_gap hLay (matchC_all hC) (b' := b') (fun j hj => hfr j (by omega))
  have hA' : MatchAll maxpage num_id cb num_proc pb ib fb ida
      ({ d.toPTData with PT := n, ipt := t } : PTData) b' :=
    ⟨hA.mm, ⟨hA.pt.pool, hA.pt.idp, hA.pt.pte, hA.pt.hp, hA.pt.hid⟩⟩
  have hC' := matchC_setPT hCL hC hA' (fun j h1 h2 => hfr j (by omega)) (fun h => h)
  refine ⟨⟨⟨hC', fun j hj => ?_⟩, fun i m hi hm v hv => ?_⟩, hc, ?_⟩
  · show MatchCh (d.syncchpool j) _ _ _
    rw [hfr _ (by unfold tcell; omega), hfr _ (by unfold tcell; omega), hfr _ (by unfold tcell; omega)]
    exact hS j hj
  · rw [hfr _ (by omega)]
    exact hU i m hi hm v hv
  · show d.pg = true ↔ b' (cpub + 1) ≠ 0
    rw [hfr _ (by omega)]
    exact hP.2

variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

/-- `set_pt(n)` writes the word at `cpub`. -/
theorem setPT_run (hcpub : cpub < 2 ^ 32) {l : RLog} {b : Region} (hcs : CS1 c i0 l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i0) {ie : Expr} {n : Nat} (he : ie.eval σ = BitVec.ofNat 32 n) :
    ∃ l', Runs (rprimsA εR c) (setPTS pb cpub ie) σ l (σ.set "_" 0) l' ∧
      CS1 c i0 l' (setCell b cpub (BitVec.ofNat 32 (pb + n * 1024))) := by
  have hv : (Expr.bin .add (.const (BitVec.ofNat 32 pb)) (.bin .mul ie (.const 1024))).eval σ =
      BitVec.ofNat 32 (pb + n * 1024) := by
    show BitVec.ofNat 32 pb + ie.eval σ * (1024 : Val) = _
    rw [he, show (1024 : Val) = BitVec.ofNat 32 1024 from rfl, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  exact wr_run (εR := εR) hcs hlk (.const (BitVec.ofNat 32 cpub)) _ (n := cpub) (tn hcpub) hv

/-! ### `proc_create` -/

/-- The seven writes give the child its first user context. -/
theorem procCreateTail_step (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hF : ∀ k, UCF ucb num_proc k → F k) {σ : Locals} {d : UData} {i uentry : Nat}
    (hr : σ "r" = BitVec.ofNat 32 i) (hfa : σ "fun_adr" = BitVec.ofNat 32 uentry) (hi : i < num_proc) :
    Step εR c i0 MU F (procCreateTailS ucb) σ d (σ.set "_" 0)
      { d with uctxt := setAt d.uctxt i (initUctx uentry (d.uctxt i)) } := by
  have W : ∀ (τ : Locals) (e : UData) (oe ve : Expr) (n : Nat) (w : Val), τ "r" = BitVec.ofNat 32 i →
      oe.eval τ = BitVec.ofNat 32 n → ve.eval τ = w → n < 17 →
      Step εR c i0 MU F (uctxSetS ucb (.var "r") oe ve) τ e (τ.set "_" 0)
        { e with uctxt := setAt e.uctxt i (setAt (e.uctxt i) n (some w)) } :=
    fun τ e oe ve n w hτ ho hve hn => uctxSetU εR c i0 hL hF (ie := .var "r") hτ ho hve hi hn
  have hs : ∀ τ : Locals, τ "r" = BitVec.ofNat 32 i → (τ.set "_" 0) "r" = BitVec.ofNat 32 i := fun τ h => by
    rw [Locals.set_other _ _ (by decide)]; exact h
  have hss : (σ.set "_" 0).set "_" 0 = σ.set "_" 0 := set_set _ _ _ _
  have h1 := hs σ hr
  have W' : ∀ (e : UData) (oe ve : Expr) (n : Nat) (w : Val), oe.eval (σ.set "_" 0) = BitVec.ofNat 32 n →
      ve.eval (σ.set "_" 0) = w → n < 17 →
      Step εR c i0 MU F (uctxSetS ucb (.var "r") oe ve) (σ.set "_" 0) e (σ.set "_" 0)
        { e with uctxt := setAt e.uctxt i (setAt (e.uctxt i) n (some w)) } := fun e oe ve n w ho hve hn => by
    have h := W (σ.set "_" 0) e oe ve n w h1 ho hve hn
    rw [hss] at h
    exact h
  have s1 := W σ d (.const 8) (.const 35) 8 35 hr rfl rfl (by decide)
  have hfa1 : (Expr.var "fun_adr").eval (σ.set "_" 0) = BitVec.ofNat 32 uentry := by
    show (σ.set "_" 0) "fun_adr" = _
    rw [Locals.set_other _ _ (by decide)]; exact hfa
  refine Step.cast (Step.seq s1
    (Step.seq (W' _ (.const 9) (.const 35) 9 35 rfl rfl (by decide))
    (Step.seq (W' _ (.const 13) (.const 27) 13 27 rfl rfl (by decide))
    (Step.seq (W' _ (.const 16) (.const 35) 16 35 rfl rfl (by decide))
    (Step.seq (W' _ (.const 15) (.const (BitVec.ofNat 32 (983040 * 4096))) 15 (BitVec.ofNat 32 (983040 * 4096))
      rfl rfl (by decide))
    (Step.seq (W' _ (.const 14) (.const 512) 14 512 rfl rfl (by decide))
      (W' _ (.const 12) (.var "fun_adr") 12 (BitVec.ofNat 32 uentry) rfl hfa1 (by decide)))))))) rfl ?_
  exact congrArg (fun U => ({ d with uctxt := U } : UData)) (by
    simp only [setAt_eq, setAt_setAt]
    rfl)

/-- **`proc_create` on the kernel machine.** The entry point is in `fun_adr`,
the quota in `quota`; the new process's id is in `r`. -/
theorem proc_create_run (code : Nat → Stmt KPrim)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hnum : cb + 5 * num_id < 2 ^ 32) (hnn : num_id ≤ num_proc) {mc pstart uentry q i : Nat} {σ : Locals}
    {K : Cont KPrim} {l : RLog} {b : Region} {d d' : UData} (hps : pstart < 2 ^ 32)
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MU d b)
    (hq : σ "quota" = BitVec.ofNat 32 q) (hfa : σ "fun_adr" = BitVec.ofNat 32 uentry)
    (hI : AInv num_proc num_chan d.toAData) (hCV : Container_valid num_id mc d.AC)
    (hcu : (d.AC d.cid).cused = true)
    (hs : proc_create_spec num_id mc num_chan code pstart uentry q d = some (d', i)) :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      KStar εR c code ⟨⟨procCreateK cb mc tb qb num_proc num_chan cidb ucb pstart, K, σ⟩, d.kctxt, l⟩
        ⟨⟨.skip, K, σ'⟩, d'.kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MU d' b' ∧ σ' "lk" = σ "lk" ∧ σ' "r" = BitVec.ofNat 32 i ∧
      AInv num_proc num_chan d'.toAData ∧
      ∀ k, ¬ CreateF cb num_id tb num_proc qb num_chan ucb k → b' k = b k := by
  have hCL := hL.ilay.clay
  have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.htb; have := hCL.qlay.hqb; have := hCL.hcb
  have := hCL.qlay.tlay.slay.hse
  obtain ⟨k1, hts, hd', hpg, hipt, hi, hcid⟩ := proc_create_factors hcu hs
  subst hd'
  -- the arguments of `thread_spawn`
  let σ1 : Locals := ((σ.set "id" (BitVec.ofNat 32 d.cid)).set "amt" (BitVec.ofNat 32 q)).set "entry"
    (BitVec.ofNat 32 pstart)
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (getCuridU εR c i0 hL (F := fun _ => False) "id" (by decide) σ d).2 l b
    hlk hcs hM
  have hb1 : b1 = b := funext (fun k => f1 k (fun h => h))
  subst hb1
  have hpre : Runs (rprimsA εR c) (procCreatePreS cidb pstart) σ l σ1 l1 :=
    Runs.seq r1 (Runs.seq (asg_run "amt" (.var "quota") (by simp [Expr.eval, Locals.set, hq]))
      (asg_run "entry" _ rfl))
  have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
  -- `thread_spawn`
  obtain ⟨σ2, l2, b2, hks, c2, m2, k2, hr2, hI2, f2, fr2⟩ := thread_spawn_run εR c i0 code hCL hnum hnn
    (σ := σ1) (K := .seq (mapS .base (procCreateTailS ucb)) K) (d := toK d) hcid hps hlk1 c1 m1.1.1
    (by simp [σ1, Locals.set]) (by simp [σ1, Locals.set]) (by simp [σ1]) hI hCV hts
  have hMU2 : MU (putK d k1) b2 := matchU_putC hL k1.kctxt m1 m2 (fun k h1 h2 => f2 k (fun hk => by
    rcases hk with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega))
  have hlk2 : (σ2 "lk").toNat = i0 := by rw [k2]; exact hlk1
  -- the child's user context
  have hfa2 : σ2 "fun_adr" = BitVec.ofNat 32 uentry := by
    rw [fr2 "fun_adr" rfl rfl (by decide)]; simp [σ1, Locals.set, hfa]
  obtain ⟨l3, b3, r3, c3, m3, f3⟩ := (procCreateTail_step εR c i0 hL (F := UCF ucb num_proc) (fun _ h => h)
    (σ := σ2) (d := putK d k1) (uentry := uentry) hr2 hfa2 (by omega)).2 l2 b2 hlk2 c2 hMU2
  refine ⟨σ2.set "_" 0, l3, b3, ?_, c3, m3, ?_, ?_, hI2, fun k hk => ?_⟩
  · exact (kstar_seq hpre _ K d.kctxt).trans ((KStar.single (kstep_seq _ _ K σ1 d.kctxt l1)).trans
      (hks.trans ((KStar.single (kstep_skip_seq _ K σ2 k1.kctxt l2)).trans (kstar_base r3 K k1.kctxt))))
  · rw [Locals.set_other _ _ (by decide), k2]; simp [σ1, Locals.set]
  · rw [Locals.set_other _ _ (by decide)]; exact hr2
  · rw [f3 k (fun h => hk (Or.inr h)), f2 k (fun h => hk (Or.inl h))]

/-! ### `proc_exit_user` and `proc_start_user` -/

/-- **`proc_exit_user` refines `proc_exit_user_spec`.** The registers of the
trap are in the locals `u0` … `u16`. -/
theorem procExitUser_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) (rs : UContext) :
    Triple εR c i0 MUP (fun k => UCF ucb num_proc k ∨ k = cpub)
      (fun σ d => d.cid < num_proc ∧ (∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) ∧
        ∃ d1, proc_exit_user_spec rs d = some d1)
      (procExitUserS cidb ucb pb cpub)
      (fun σ d σ' d' => proc_exit_user_spec rs d = some d' ∧ ∀ z, z ≠ "_" → z ≠ "curid" → σ' z = σ z) := by
  intro σ l b d hlk hcs hM ⟨hcid, hrs, d1, hs⟩
  have hCL := hL.ilay.clay
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hL.ilay.hie
  have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse; have := hCL.qlay.tlay.htb
  have := hCL.qlay.tlay.hte; have := hCL.qlay.hqb; have := hCL.qlay.hqe; have := hCL.hcb; have := hCL.hce
  have hcpub : cpub < 2 ^ 32 := by have := ucb_lt hL; omega
  have hs0 := hs
  unfold proc_exit_user_spec at hs
  split at hs
  · rename_i hc
    simp only [Option.some.injEq] at hs
    subst hs
    -- `trap_in`: now in kernel mode
    have hM0 : MUP ({ d with ikern := true } : UData) b :=
      matchUP_cpu hL hcp0 hcp1 hM d.PT d.ipt true (fun _ _ => rfl) hM.2.1
    -- `save_uctx`
    obtain ⟨σ1, l1, b1, d1, r1, c1, m1, k1, f1, hd1, fr1⟩ := saveUctx_triple εR c i0 hL rs σ l b
      ({ d with ikern := true } : UData) hlk hcs hM0.1
      ⟨hcid, hrs, _, by unfold save_uctx_spec; rw [if_pos ⟨rfl, hc.2.1, hc.2.2⟩]⟩
    unfold save_uctx_spec at hd1
    rw [if_pos ⟨rfl, hc.2.1, hc.2.2⟩] at hd1
    simp only [Option.some.injEq] at hd1
    subst hd1
    have hcpu1 : MatchCPU num_proc pb cpub d.toPTData b1 :=
      ⟨fun h => by rw [f1 cpub (fun hk => by unfold UCF at hk; omega)]; exact hM.2.1 h,
        by rw [f1 (cpub + 1) (fun hk => by unfold UCF at hk; omega)]; exact hM.2.2⟩
    -- `set_pt(0)`, `pt_in`
    have hlk1 : (σ1 "lk").toNat = i0 := by rw [k1]; exact hlk
    obtain ⟨l2, r2, c2⟩ := setPT_run (pb := pb) εR c i0 hcpub c1 hlk1 (ie := .const 0) (n := 0) rfl
    refine ⟨σ1.set "_" 0, l2, _, _, Runs.seq r1 r2, c2,
      matchUP_cpu hL hcp0 hcp1 (d := ({ d with ikern := true, uctxt := setAt d.uctxt d.cid rs } : UData))
        ⟨m1, hcpu1⟩ 0 true true (fun j hj => sc_ne _ _ hj) (fun _ => sc_eq _ _ _), ?_, fun k hk => ?_, hs0,
      fun z h1 h2 => ?_⟩
    · rw [Locals.set_other _ _ (by decide)]; exact k1
    · rw [sc_ne _ _ (fun e => hk (Or.inr e))]
      exact f1 k (fun h => hk (Or.inl h))
    · rw [Locals.set_other _ _ h1]; exact fr1 z h1 h2
  · cases hs

/-- **`proc_start_user` refines `proc_start_user_spec`.** Afterwards the
process's page table is in `CR3` and its registers are in the locals `u0` …
`u16`. -/
theorem procStartUser_run (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) {σ : Locals} {l : RLog} {b : Region}
    {d d' : UData} {rs : UContext} (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MUP d b)
    (hcid : d.cid < num_proc) (hs : proc_start_user_spec d = some (d', rs)) :
    ∃ (σ' : Locals) (l' : RLog) (b' : Region),
      Runs (rprimsA εR c) (procStartUserS cidb ucb pb cpub) σ l σ' l' ∧ CS1 c i0 l' b' ∧ MUP d' b' ∧
      (∀ n, n < 17 → ∀ v, rs n = some v → σ' (ureg n) = v) ∧ ∀ k, k ≠ cpub → b' k = b k := by
  have hCL := hL.ilay.clay
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hL.ilay.hie
  have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse; have := hCL.qlay.tlay.htb
  have := hCL.qlay.tlay.hte; have := hCL.qlay.hqb; have := hCL.qlay.hqe; have := hCL.hcb; have := hCL.hce
  have hcpub : cpub < 2 ^ 32 := by have := ucb_lt hL; omega
  unfold proc_start_user_spec at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hd, hr⟩ := hs
    subst hd; subst hr
    -- `cid = get_curid()`
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (getCuridU εR c i0 hL (F := fun _ => False) "curid" (by decide) σ d).2
      l b hlk hcs hM.1
    have hb1 : b1 = b := funext (fun k => f1 k (fun h => h))
    subst hb1
    -- `set_pt(cid)`
    obtain ⟨l2, r2, c2⟩ := setPT_run (pb := pb) εR c i0 hcpub c1
      (σ := σ.set "curid" (BitVec.ofNat 32 d.cid)) (by simpa [Locals.set] using hlk) (ie := .var "curid")
      (n := d.cid) (by simp [Expr.eval])
    -- the registers
    obtain ⟨σ3, r3, v3, fr3⟩ := loadRegs_run εR c i0 hL c2
      (σ := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "_" 0) (cid := d.cid)
      (by simpa [Locals.set] using hlk) (by simp [Locals.set]) hcid 17 (Nat.le_refl _)
    refine ⟨σ3, l2, _, Runs.seq r1 (Runs.seq r2 r3), c2,
      matchUP_cpu hL hcp0 hcp1 hM d.cid false false (fun j hj => sc_ne _ _ hj) (fun _ => sc_eq _ _ _),
      fun n hn v hv => ?_, fun k hk => sc_ne _ _ hk⟩
    rw [v3 n hn, sc_ne _ _ (by omega)]
    exact hM.1.2 d.cid n hcid hn v hv
  · cases hs

/-- **Leaving the kernel.** A kernel computation that is `proc_start_user` on
an empty stack ends in user mode, with registers that are the process's user
context wherever that is known. -/
theorem start_user_ustar (code : Nat → Stmt KPrim) (entry : Nat → Nat) (lk : Val)
    (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hcp0 : cb + 5 * num_id ≤ cpub) (hcp1 : cpub + 2 ≤ sb) {σ : Locals} {l : RLog} {b : Region}
    {d d' : UData} {rs : UContext} (pool : Nat → KCtx) (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b)
    (hM : MUP d b) (hcid : d.cid < num_proc) (hs : proc_start_user_spec d = some (d', rs)) :
    ∃ (ur : Nat → Val) (l' : RLog) (b' : Region),
      UStar εR c code entry lk (.kern ⟨⟨mapS .base (procStartUserS cidb ucb pb cpub), .stop, σ⟩, pool, l⟩)
        (.user ur pool l') ∧
      CS1 c i0 l' b' ∧ MUP d' b' ∧ (∀ n, n < 17 → ∀ v, rs n = some v → ur n = v) ∧
      ∀ k, k ≠ cpub → b' k = b k := by
  obtain ⟨σ', l', b', hr, hcs', hM', hreg, hf⟩ := procStartUser_run εR c i0 hL hcp0 hcp1 hlk hcs hM hcid hs
  exact ⟨regsOf σ', l', b', UStar.iret (kstar_base hr .stop pool), hcs', hM', hreg, hf⟩

end Code

end PProc
