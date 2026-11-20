import CertiKOS.PProcInit

/-!
# mCertiKOS `PUCtxtIntro`: user contexts, ported

A user context is the seventeen registers saved when a process traps into the
kernel. Each process has one.

Ported from `layerlib/AuxStateDataType.v`: `UContext`, `UContextPool`,
`is_UCTXT_ptr`. Ported from `objects/ObjProc.v`: `uctx_get_spec`,
`uctx_set_spec`, `uctx_set_eip_spec`, `save_uctx_spec`, `restore_uctx_spec`.
Ported from `proc/UCtxtIntroGenDef.v`: `match_UCtxt`. Ported from
`proc/PIPCCSource.v`: the C code of `uctx_get`, `uctx_set`, `uctx_set_eip`,
`save_uctx`.

* `UData`: **the top state.** `IData` (everything up to the channels) with
  the kernel contexts, the user contexts, and the two mode flags `ikern` and
  `ihost`. From this layer on the specifications check the flags, as
  mCertiKOS's do.
* `MatchU`, `ULayout`: the user contexts are seventeen cells per process at
  `ucb`, after the channels.
* `stepIU`, `liftIU`: steps and triples of the layers below hold in `UData`,
  if they do not write the user contexts.
* `uctxGet_triple`, `uctxSet_triple`, `uctxSetEip_triple`: the accessors
  refine their specifications.
* `saveUctx_triple`: **`save_uctx` refines `save_uctx_spec`.** Its seventeen
  arguments are the locals `u0` … `u16`.
* `loadRegs_run`: the seventeen reads that `restore_uctx` does.

What differs: a register value is a machine word or unknown (`none`, for
`Vundef`). mCertiKOS also has pointers there (`EIP` is a pointer to the
entry function); here the entry is a number. `restore_uctx` ends by leaving
the kernel, so its theorem is in `PProc.lean`, on the machine with user mode.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PUCtxt

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## Abstract data (`AuxStateDataType.v`) -/

/-- `UContext`: the saved registers. `none` is an unknown value. -/
abbrev UContext := Nat → Option Val
abbrev UContextPool := Nat → UContext

def U_EDI : Nat := 0
def U_ESI : Nat := 1
def U_EBP : Nat := 2
def U_OESP : Nat := 3
def U_EBX : Nat := 4
def U_EDX : Nat := 5
def U_ECX : Nat := 6
def U_EAX : Nat := 7
def U_ES : Nat := 8
def U_DS : Nat := 9
def U_TRAPNO : Nat := 10
def U_ERR : Nat := 11
def U_EIP : Nat := 12
def U_CS : Nat := 13
def U_EFLAGS : Nat := 14
def U_ESP : Nat := 15
def U_SS : Nat := 16

/-- `is_UCTXT_ptr`: the registers that hold pointers (`EBP`, the old `ESP`,
`EIP`), and every index out of range. -/
def is_UCTXT_ptr (ofs : Nat) : Bool := !(ofs ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16])

theorem is_UCTXT_ptr_range {ofs : Nat} (h : is_UCTXT_ptr ofs = false) : ofs < 17 := by
  unfold is_UCTXT_ptr at h
  simp at h
  omega

/-- **The top state**: `IData` with the kernel contexts, the user contexts and
the mode flags. `ikern`: the CPU is in kernel mode. `ihost`: it is in host
mode (always, until virtualization). -/
structure UData extends IData where
  kctxt : Nat → KCtx
  uctxt : UContextPool
  ikern : Bool
  ihost : Bool

/-! ## Specifications (`ObjProc.v`) -/

section Specs
variable (num_proc : Nat)

def uctx_get_spec (i ofs : Nat) (d : UData) : Option Nat :=
  if d.ikern = true ∧ d.pg = true ∧ d.ihost = true ∧ d.ipt = true ∧ i < num_proc ∧
      is_UCTXT_ptr ofs = false then
    match d.uctxt i ofs with
    | some n => some n.toNat
    | none => none
  else none

def uctx_set_spec (i ofs n : Nat) (d : UData) : Option UData :=
  if d.ikern = true ∧ d.pg = true ∧ d.ihost = true ∧ d.ipt = true ∧ i < num_proc ∧
      is_UCTXT_ptr ofs = false then
    some { d with uctxt := setAt d.uctxt i (setAt (d.uctxt i) ofs (some (BitVec.ofNat 32 n))) }
  else none

/-- `uctx_set_eip_spec`: where the process starts in user mode. -/
def uctx_set_eip_spec (i v : Nat) (d : UData) : Option UData :=
  if d.ikern = true ∧ d.pg = true ∧ d.ihost = true ∧ d.ipt = true ∧ i < num_proc then
    some { d with uctxt := setAt d.uctxt i (setAt (d.uctxt i) U_EIP (some (BitVec.ofNat 32 v))) }
  else none

end Specs

/-- `save_uctx_spec`: the registers of the trap become the current process's
user context. -/
def save_uctx_spec (rs : UContext) (d : UData) : Option UData :=
  if d.ikern = true ∧ d.pg = true ∧ d.ihost = true then
    some { d with uctxt := setAt d.uctxt d.cid rs }
  else none

/-- `restore_uctx_spec`: leave the kernel with the current process's user
context. -/
def restore_uctx_spec (d : UData) : Option (UData × UContext) :=
  if d.ikern = true ∧ d.ipt = false ∧ d.pg = true ∧ d.ihost = true ∧ d.init = true then
    some ({ d with ikern := false }, d.uctxt d.cid)
  else none

/-! ## The user contexts in the region (`UCtxtIntroGenDef.v`) -/

/-- `match_UCtxt`: register `n` of process `i` is the cell `ucb + 17 * i + n`,
when the register is known. -/
def MatchUC (num_proc ucb : Nat) (p : UContextPool) (b : Region) : Prop :=
  ∀ i n, i < num_proc → n < 17 → ∀ v, p i n = some v → b (ucb + i * 17 + n) = v

/-- The layout with the user contexts after the channels. -/
structure ULayout (maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb : Nat) : Prop where
  ilay : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb
  hub0 : ipb + 3 * num_chan ≤ ucb
  hue : ucb + 17 * num_proc ≤ pb

def MatchU (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb : Nat) (d : UData)
    (b : Region) : Prop :=
  MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb d.toIData b ∧
    MatchUC num_proc ucb d.uctxt b

/-- The cells of the user contexts. -/
def UCF (ucb num_proc : Nat) (k : Nat) : Prop := ucb ≤ k ∧ k < ucb + 17 * num_proc

/-! ## The C code (`PIPCCSource.v`) -/

/-- `&UCTX_LOC[i][ofs]` -/
def uE (ucb : Nat) (ie oe : Expr) : Expr :=
  .bin .add (.const (BitVec.ofNat 32 ucb)) (.bin .add (.bin .mul ie (.const 17)) oe)

/-- `x = uctx_get(i, ofs)`: `return UCTX_LOC[i][ofs];` -/
def uctxGetS (ucb : Nat) (x : Ident) (ie oe : Expr) : Stmt APrim := .call x .pull [lkE, uE ucb ie oe]

/-- `uctx_set(i, ofs, v)`: `UCTX_LOC[i][ofs] = v;` -/
def uctxSetS (ucb : Nat) (ie oe ve : Expr) : Stmt APrim := .call "_" .push [lkE, uE ucb ie oe, ve]

/-- `uctx_set_eip(i, v)`: `UCTX_LOC[i][U_EIP] = v;` -/
def uctxSetEipS (ucb : Nat) (ie ve : Expr) : Stmt APrim := uctxSetS ucb ie (.const 12) ve

/-- The locals that carry the seventeen registers across the kernel's
boundary. -/
def uregs : List Ident :=
  ["u0", "u1", "u2", "u3", "u4", "u5", "u6", "u7", "u8", "u9", "u10", "u11", "u12", "u13", "u14", "u15", "u16"]

def ureg (k : Nat) : Ident := uregs.getD k "u0"

/-- `UCTX_LOC[curid][0] = u0; …; UCTX_LOC[curid][k-1] = u(k-1);` -/
def saveRegsS (ucb : Nat) : Nat → Stmt APrim
  | 0 => .skip
  | k + 1 => .seq (saveRegsS ucb k) (uctxSetS ucb (.var "curid") (.const (BitVec.ofNat 32 k)) (.var (ureg k)))

/-- `save_uctx(u0, …, u16)`: `curid = get_curid();` then the seventeen
stores. -/
def saveUctxS (cidb ucb : Nat) : Stmt APrim := .seq (getCuridS cidb "curid") (saveRegsS ucb 17)

/-- `u0 = UCTX_LOC[curid][0]; …; u(k-1) = UCTX_LOC[curid][k-1];` -/
def loadRegsS (ucb : Nat) : Nat → Stmt APrim
  | 0 => .skip
  | k + 1 => .seq (loadRegsS ucb k) (uctxGetS ucb (ureg k) (.var "curid") (.const (BitVec.ofNat 32 k)))

set_option maxRecDepth 4000 in
theorem ureg_ne : ∀ k, k < 17 → ureg k ≠ "_" ∧ ureg k ≠ "lk" ∧ ureg k ≠ "curid" := by decide

set_option maxRecDepth 8000 in
theorem ureg_inj : ∀ a, a < 17 → ∀ b, b < 17 → ureg a = ureg b → a = b := by decide

theorem u_eval {ucb num_proc : Nat} (hend : ucb + 17 * num_proc ≤ 2 ^ 32) {σ : Locals} {ie oe : Expr} {i n : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 i) (ho : oe.eval σ = BitVec.ofNat 32 n) (hi : i < num_proc)
    (hn : n < 17) : ((uE ucb ie oe).eval σ).toNat = ucb + i * 17 + n := by
  have e : (uE ucb ie oe).eval σ = BitVec.ofNat 32 ucb + (ie.eval σ * (17 : Val) + oe.eval σ) := rfl
  rw [e, he, ho, show (17 : Val) = BitVec.ofNat 32 17 from rfl, ← BitVec.ofNat_mul, ← BitVec.ofNat_add,
    ← BitVec.ofNat_add, tn (by omega)]
  omega

section Region
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb : Nat}

theorem ucb_lt (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb) :
    ucb + 17 * num_proc ≤ 2 ^ 32 := by
  have := hL.hue; have := hL.ilay.clay.qlay.tlay.slay.lay.hib; have := hL.ilay.clay.qlay.tlay.slay.lay.hfb
  have := hL.ilay.clay.qlay.tlay.slay.lay.hend; omega

/-- The layers up to the channels depend only on the cells below the user
contexts and from the page-table pool on. -/
theorem matchI_frame (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    {d : IData} {b b' : Region}
    (hM : MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb d b)
    (hfr : ∀ k, k < ucb ∨ pb ≤ k → b' k = b k) :
    MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb d b' := by
  have := hL.hub0; have := hL.hue; have := hL.ilay.hib0; have := hL.ilay.hie
  refine ⟨matchC_frame hL.ilay.clay hM.1 (fun k hk => hfr k (by omega)), fun j hj => ?_⟩
  show MatchCh (d.syncchpool j) _ _ _
  rw [hfr _ (by unfold tcell; omega), hfr _ (by unfold tcell; omega), hfr _ (by unfold tcell; omega)]
  exact hM.2 j hj

variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MI" => MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb
local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb

/-! ### The layers below, in the top state -/

/-- **A step of the layers below is a step in the top state**, if it writes
no user context. -/
theorem stepIU (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    {s : Stmt APrim} {σ σ' : Locals} {d : UData} {i1 : IData} (h : Step εR c i0 MI F s σ d.toIData σ' i1)
    (hF : ∀ k, F k → k < ucb ∨ pb ≤ k) : Step εR c i0 MU F s σ d σ' { d with toIData := i1 } := by
  have := hL.hue
  refine Step.lift (π := UData.toIData)
    (put := fun (d' : UData) (i' : IData) => ({ d' with toIData := i' } : UData))
    (M2 := fun d' b => MatchUC num_proc ucb d'.uctxt b) h rfl (fun b b' h2 _ _ hf i n hi hn v hv => ?_)
  rw [hf _ (fun hk => by have := hF _ hk; omega)]
  exact h2 i n hi hn v hv

/-- **A triple of the layers below holds in the top state.** -/
theorem liftIU (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    {P : Locals → IData → Prop} {s : Stmt APrim} {Q : Locals → IData → Locals → IData → Prop}
    (h : Triple εR c i0 MI F P s Q) (hF : ∀ k, F k → k < ucb ∨ pb ≤ k) :
    Triple εR c i0 MU F (fun σ d => P σ d.toIData) s
      (fun σ d σ' d' => ∃ i1 : IData, d' = { d with toIData := i1 } ∧ Q σ d.toIData σ' i1) := by
  have := hL.hue
  refine h.lift (π := UData.toIData)
    (put := fun (d' : UData) (i' : IData) => ({ d' with toIData := i' } : UData))
    (M2 := fun d' b => MatchUC num_proc ucb d'.uctxt b) (fun _ _ => rfl)
    (fun d' b σ σ' d1 b' h2 _ _ _ hf i n hi hn v hv => ?_)
  rw [hf _ (fun hk => by have := hF _ hk; omega)]
  exact h2 i n hi hn v hv

/-- `get_curid` in the top state. -/
theorem getCuridU (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb) (x : Ident)
    (hx : x ≠ "lk") (σ : Locals) (d : UData) :
    Step εR c i0 MU F (getCuridS cidb x) σ d (σ.set x (BitVec.ofNat 32 d.cid)) d :=
  (stepIU εR c i0 hL (getCuridI εR c i0 hL.ilay (F := fun _ => False) x hx σ d.toIData)
    (fun _ h => h.elim)).widen (fun _ h => h.elim)

/-! ### The accessors, as steps -/

/-- Reading a register that is known. -/
theorem uctxGetU (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb) (x : Ident)
    (hx : x ≠ "lk") {ie oe : Expr} {σ : Locals} {d : UData} {i n : Nat} {v : Val}
    (he : ie.eval σ = BitVec.ofNat 32 i) (ho : oe.eval σ = BitVec.ofNat 32 n) (hi : i < num_proc) (hn : n < 17)
    (hv : d.uctxt i n = some v) : Step εR c i0 MU F (uctxGetS ucb x ie oe) σ d (σ.set x v) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk x (uE ucb ie oe) (u_eval (ucb_lt hL) he ho hi hn)
  rw [hM.2 i n hi hn v hv] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

/-- Writing a register. -/
theorem uctxSetU (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (hF : ∀ k, UCF ucb num_proc k → F k) {ie oe ve : Expr} {σ : Locals} {d : UData} {i n : Nat} {w : Val}
    (he : ie.eval σ = BitVec.ofNat 32 i) (ho : oe.eval σ = BitVec.ofNat 32 n) (hve : ve.eval σ = w)
    (hi : i < num_proc) (hn : n < 17) :
    Step εR c i0 MU F (uctxSetS ucb ie oe ve) σ d (σ.set "_" 0)
      { d with uctxt := setAt d.uctxt i (setAt (d.uctxt i) n (some w)) } := by
  have := hL.hub0; have := hL.hue
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (uE ucb ie oe) ve (u_eval (ucb_lt hL) he ho hi hn) hve
  refine ⟨l', _, hr, hcs', ⟨matchI_frame hL hM.1 (fun k hk => sc_ne _ _ (by omega)),
    fun i' n' hi' hn' v hv => ?_⟩, fun k hk => sc_ne _ _ (fun e => hk (hF k ⟨by omega, by omega⟩))⟩
  have hv' : setAt d.uctxt i (setAt (d.uctxt i) n (some w)) i' n' = some v := hv
  by_cases e1 : i' = i
  · subst e1
    rw [setAt_eq] at hv'
    by_cases e2 : n' = n
    · subst e2
      rw [setAt_eq] at hv'
      injection hv' with hv'
      rw [sc_eq]; exact hv'
    · rw [setAt_ne _ _ e2] at hv'
      rw [sc_ne _ _ (by omega)]
      exact hM.2 i' n' hi' hn' v hv'
  · rw [setAt_ne _ _ e1] at hv'
    rw [sc_ne _ _ (by omega)]
    exact hM.2 i' n' hi' hn' v hv'

/-! ### Each accessor refines its specification -/

/-- **`uctx_get` refines `uctx_get_spec`.** -/
theorem uctxGet_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (x : Ident) (hx : x ≠ "lk") (ie oe : Expr) (i ofs : Nat) :
    Triple εR c i0 MU (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 i ∧ oe.eval σ = BitVec.ofNat 32 ofs ∧
        ∃ v, uctx_get_spec num_proc i ofs d = some v)
      (uctxGetS ucb x ie oe)
      (fun σ d σ' d' => d' = d ∧ ∃ v, uctx_get_spec num_proc i ofs d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  refine Step.triple (fun σ d ⟨he, ho, v, hs⟩ => ?_)
  have hs0 := hs
  unfold uctx_get_spec at hs
  split at hs
  · rename_i hc
    cases hu : d.uctxt i ofs with
    | none => rw [hu] at hs; cases hs
    | some w =>
      rw [hu] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, d, uctxGetU εR c i0 hL x hx he ho hc.2.2.2.2.1 (is_UCTXT_ptr_range hc.2.2.2.2.2) hu, rfl, _,
        hs0, by simp⟩
  · cases hs

/-- **`uctx_set` refines `uctx_set_spec`.** -/
theorem uctxSet_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (ie oe ve : Expr) (i ofs n : Nat) :
    Triple εR c i0 MU (UCF ucb num_proc)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 i ∧ oe.eval σ = BitVec.ofNat 32 ofs ∧
        ve.eval σ = BitVec.ofNat 32 n ∧ ∃ d1, uctx_set_spec num_proc i ofs n d = some d1)
      (uctxSetS ucb ie oe ve)
      (fun σ d σ' d' => uctx_set_spec num_proc i ofs n d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨he, ho, hve, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold uctx_set_spec at hs
  split at hs
  · rename_i hc
    simp only [Option.some.injEq] at hs
    subst hs
    exact ⟨_, _, uctxSetU εR c i0 hL (fun _ h => h) he ho hve hc.2.2.2.2.1 (is_UCTXT_ptr_range hc.2.2.2.2.2),
      hs0, rfl⟩
  · cases hs

/-- **`uctx_set_eip` refines `uctx_set_eip_spec`.** -/
theorem uctxSetEip_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (ie ve : Expr) (i v : Nat) :
    Triple εR c i0 MU (UCF ucb num_proc)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 i ∧ ve.eval σ = BitVec.ofNat 32 v ∧
        ∃ d1, uctx_set_eip_spec num_proc i v d = some d1)
      (uctxSetEipS ucb ie ve)
      (fun σ d σ' d' => uctx_set_eip_spec num_proc i v d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨he, hve, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold uctx_set_eip_spec at hs
  split at hs
  · rename_i hc
    simp only [Option.some.injEq] at hs
    subst hs
    exact ⟨_, _, uctxSetU εR c i0 hL (fun _ h => h) (oe := .const 12) (n := 12) he rfl hve hc.2.2.2.2
      (by decide), hs0, rfl⟩
  · cases hs

/-! ### `save_uctx` and the reads of `restore_uctx` -/

/-- The first `k` stores of `save_uctx`. -/
theorem saveRegs_run (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    {σ : Locals} {cid : Nat} (hlk : (σ "lk").toNat = i0) (hcur : σ "curid" = BitVec.ofNat 32 cid)
    (hcid : cid < num_proc) :
    ∀ k, k ≤ 17 → ∀ {l : RLog} {b : Region}, CS1 c i0 l b →
      ∃ (σ' : Locals) (l' : RLog) (b' : Region), Runs (rprimsA εR c) (saveRegsS ucb k) σ l σ' l' ∧
        CS1 c i0 l' b' ∧ (∀ z, z ≠ "_" → σ' z = σ z) ∧
        (∀ n, n < k → b' (ucb + cid * 17 + n) = σ (ureg n)) ∧
        ∀ j, ¬ (ucb + cid * 17 ≤ j ∧ j < ucb + cid * 17 + k) → b' j = b j
  | 0, _, l, b, hcs => ⟨σ, l, b, Runs.skip, hcs, fun _ _ => rfl, fun n hn => absurd hn (Nat.not_lt_zero n),
      fun _ _ => rfl⟩
  | k + 1, hk, l, b, hcs => by
    obtain ⟨σ1, l1, b1, r1, c1, fr1, v1, f1⟩ := saveRegs_run hL hlk hcur hcid k (by omega) hcs
    obtain ⟨h1, h2, h3⟩ := ureg_ne k (by omega)
    have hlk1 : (σ1 "lk").toNat = i0 := by rw [fr1 "lk" (by decide)]; exact hlk
    obtain ⟨l2, r2, c2⟩ := wr_run (εR := εR) c1 hlk1
      (uE ucb (.var "curid") (.const (BitVec.ofNat 32 k))) (.var (ureg k)) (v := σ (ureg k))
      (u_eval (i := cid) (n := k) (ucb_lt hL) ((fr1 "curid" (by decide)).trans hcur) rfl hcid (by omega))
      (fr1 (ureg k) h1)
    refine ⟨σ1.set "_" 0, l2, _, Runs.seq r1 r2, c2, fun z hz => ?_, fun n hn => ?_, fun j hj => ?_⟩
    · rw [Locals.set_other _ _ hz]; exact fr1 z hz
    · by_cases e : n = k
      · subst e; exact sc_eq _ _ _
      · rw [sc_ne _ _ (by omega)]; exact v1 n (by omega)
    · rw [sc_ne _ _ (by omega)]; exact f1 j (by omega)

/-- **`save_uctx` refines `save_uctx_spec`.** The registers come in the
locals `u0` … `u16`. -/
theorem saveUctx_triple (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    (rs : UContext) :
    Triple εR c i0 MU (UCF ucb num_proc)
      (fun σ d => d.cid < num_proc ∧ (∀ n, n < 17 → ∀ v, rs n = some v → σ (ureg n) = v) ∧
        ∃ d1, save_uctx_spec rs d = some d1)
      (saveUctxS cidb ucb)
      (fun σ d σ' d' => save_uctx_spec rs d = some d' ∧ ∀ z, z ≠ "_" → z ≠ "curid" → σ' z = σ z) := by
  intro σ l b d hlk hcs hM ⟨hcid, hrs, d1, hs⟩
  have := hL.hub0; have := hL.hue
  have hs0 := hs
  unfold save_uctx_spec at hs
  split at hs
  · simp only [Option.some.injEq] at hs
    subst hs
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (getCuridU εR c i0 hL (F := fun _ => False) "curid" (by decide) σ d).2
      l b hlk hcs hM
    have hb1 : b1 = b := funext (fun k => f1 k (fun h => h))
    subst hb1
    obtain ⟨σ2, l2, b2, r2, c2, fr2, v2, f2⟩ := saveRegs_run εR c i0 hL
      (σ := σ.set "curid" (BitVec.ofNat 32 d.cid)) (cid := d.cid) (by simpa [Locals.set] using hlk)
      (by simp) hcid 17 (Nat.le_refl _) c1
    refine ⟨σ2, l2, b2, ({ d with uctxt := setAt d.uctxt d.cid rs } : UData), Runs.seq r1 r2, c2,
      ⟨matchI_frame hL hM.1 (fun k hk => f2 k (by omega)),
      fun i n hi hn v hv => ?_⟩, ?_, fun k hk => f2 k (fun h => hk ⟨by omega, by omega⟩), hs0,
      fun z h1 h2 => ?_⟩
    · have hv' : setAt d.uctxt d.cid rs i n = some v := hv
      by_cases e : i = d.cid
      · subst e
        rw [setAt_eq] at hv'
        rw [v2 n hn, Locals.set_other _ _ (ureg_ne n hn).2.2]
        exact hrs n hn v hv'
      · rw [setAt_ne _ _ e] at hv'
        rw [f2 _ (by omega)]
        exact hM.2 i n hi hn v hv'
    · rw [fr2 "lk" (by decide)]; simp [Locals.set]
    · rw [fr2 z h1, Locals.set_other _ _ h2]
  · cases hs

/-- The first `k` reads of `restore_uctx`: the registers of process `cid` go
to the locals `u0` … `u(k-1)`. -/
theorem loadRegs_run (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb)
    {σ : Locals} {l : RLog} {b : Region} {cid : Nat} (hcs : CS1 c i0 l b) (hlk : (σ "lk").toNat = i0)
    (hcur : σ "curid" = BitVec.ofNat 32 cid) (hcid : cid < num_proc) :
    ∀ k, k ≤ 17 →
      ∃ σ' : Locals, Runs (rprimsA εR c) (loadRegsS ucb k) σ l σ' l ∧
        (∀ n, n < k → σ' (ureg n) = b (ucb + cid * 17 + n)) ∧
        ∀ z, (∀ n, n < k → z ≠ ureg n) → σ' z = σ z
  | 0, _ => ⟨σ, Runs.skip, fun n hn => absurd hn (Nat.not_lt_zero n), fun _ _ => rfl⟩
  | k + 1, hk => by
    obtain ⟨σ1, r1, v1, fr1⟩ := loadRegs_run hL hcs hlk hcur hcid k (by omega)
    have hne : ∀ z, z = "lk" ∨ z = "curid" → ∀ n, n < k → z ≠ ureg n := by
      intro z hz n hn e
      obtain ⟨-, h2, h3⟩ := ureg_ne n (by omega)
      rcases hz with hz | hz
      · exact h2 (e.symm.trans hz)
      · exact h3 (e.symm.trans hz)
    have hlk1 : (σ1 "lk").toNat = i0 := by rw [fr1 "lk" (hne "lk" (Or.inl rfl))]; exact hlk
    have r2 := rd_run (εR := εR) hcs hlk1 (ureg k) (uE ucb (.var "curid") (.const (BitVec.ofNat 32 k)))
      (u_eval (i := cid) (n := k) (ucb_lt hL) ((fr1 "curid" (hne "curid" (Or.inr rfl))).trans hcur) rfl hcid
        (by omega))
    refine ⟨_, Runs.seq r1 r2, fun n hn => ?_, fun z hz => ?_⟩
    · by_cases e : n = k
      · subst e; exact Locals.set_same _ _ _
      · rw [Locals.set_other _ _ (fun h => e (ureg_inj n (by omega) k (by omega) h))]
        exact v1 n (by omega)
    · rw [Locals.set_other _ _ (hz k (by omega))]
      exact fr1 z (fun n hn => hz n (by omega))

end Region

end PUCtxt
