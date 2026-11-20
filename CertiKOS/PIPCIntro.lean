import CertiKOS.PThreadSpawn

/-!
# mCertiKOS `PIPCIntro`: the synchronous IPC channels, ported

Each thread has a channel: who it is sending to, where its buffer is, and how
many words. A receiver reads the sender's channel and copies the buffer.

Ported from `layerlib/AuxStateDataType.v`: `SyncChannel`, `SyncChanPool`.
Ported from `objects/ObjSyncIPC.v`: `get_sync_chan_to_spec`,
`get_sync_chan_paddr_spec`, `get_sync_chan_count_spec`,
`set_sync_chan_to_spec`, `set_sync_chan_paddr_spec`,
`set_sync_chan_count_spec`, `init_sync_chan_spec`, `get_kernel_pa_spec`.
Ported from `proc/IPCIntroGenDef.v`: `match_Chan`, `match_ChanPool`.
Ported from `proc/PThreadCSource.v`: the C code of the accessors and of
`get_kernel_pa`. From `proc/PIPCIntroCSource.v`: the loop of `proc_init`.

* `getSyncTo_triple` … `initSync_triple`: each accessor refines its
  specification.
* `getKernelPa_triple`: `get_kernel_pa` refines `get_kernel_pa_spec`. It
  calls `pt_read` through its triple, carried up by `liftPC` and `liftCI`.
* `syncInit_step`: the loop of `proc_init` gives `real_syncchpool`.
* `stepCI`, `liftCI`: the layers below keep their interfaces in the state
  with the channels.

What differs: the pool is in the kernel region, after the current-thread
word (`ILayout`), three cells per channel. The fields are machine words, as
in mCertiKOS (`int`).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PIPC

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## Abstract data (`AuxStateDataType.v`) -/

/-- `SyncChanValid to paddr count`. -/
inductive SyncChannel
  | SyncChanUndef
  | SyncChanValid (to paddr count : Val)

abbrev SyncChanPool := Nat → SyncChannel

/-- `CData` with the synchronous IPC channels. -/
structure IData extends CData where
  syncchpool : SyncChanPool

/-! ## Specifications (`ObjSyncIPC.v`) -/

section Specs
variable (num_chan : Nat)

def get_sync_chan_to_spec (i : Nat) (d : IData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ i < num_chan then
    match d.syncchpool i with
    | .SyncChanValid to _ _ => some to.toNat
    | .SyncChanUndef => none
  else none

def get_sync_chan_paddr_spec (i : Nat) (d : IData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ i < num_chan then
    match d.syncchpool i with
    | .SyncChanValid _ p _ => some p.toNat
    | .SyncChanUndef => none
  else none

def get_sync_chan_count_spec (i : Nat) (d : IData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ i < num_chan then
    match d.syncchpool i with
    | .SyncChanValid _ _ c => some c.toNat
    | .SyncChanUndef => none
  else none

def set_sync_chan_to_spec (i to : Nat) (d : IData) : Option IData :=
  if d.pg = true ∧ d.ipt = true ∧ i < num_chan then
    match d.syncchpool i with
    | .SyncChanValid _ p c =>
      some { d with syncchpool := setAt d.syncchpool i (.SyncChanValid (BitVec.ofNat 32 to) p c) }
    | .SyncChanUndef => none
  else none

def set_sync_chan_paddr_spec (i vaddr : Nat) (d : IData) : Option IData :=
  if d.pg = true ∧ d.ipt = true ∧ i < num_chan then
    match d.syncchpool i with
    | .SyncChanValid t _ c =>
      some { d with syncchpool := setAt d.syncchpool i (.SyncChanValid t (BitVec.ofNat 32 vaddr) c) }
    | .SyncChanUndef => none
  else none

def set_sync_chan_count_spec (i count : Nat) (d : IData) : Option IData :=
  if d.pg = true ∧ d.ipt = true ∧ i < num_chan then
    match d.syncchpool i with
    | .SyncChanValid t p _ =>
      some { d with syncchpool := setAt d.syncchpool i (.SyncChanValid t p (BitVec.ofNat 32 count)) }
    | .SyncChanUndef => none
  else none

/-- A channel that sends to nobody: `num_chan` stands for "none". -/
def init_sync_chan_spec (i : Nat) (d : IData) : Option IData :=
  if d.pg = true ∧ d.ipt = true ∧ i < num_chan then
    some { d with syncchpool := setAt d.syncchpool i (.SyncChanValid (BitVec.ofNat 32 num_chan) 0 0) }
  else none

end Specs

/-- **`get_kernel_pa_spec`**: the kernel's address of user address `vaddr`
of process `pid`. -/
def get_kernel_pa_spec (num_proc pid vaddr : Nat) (d : IData) : Option Nat :=
  if d.pg = true then
    match ptRead_spec num_proc pid vaddr d.toPTData with
    | some paddr => if paddr = 0 then none else some (paddr / 4096 * 4096 + vaddr % 4096)
    | none => none
  else none

/-- `real_syncchpool`: every channel sends to nobody. -/
def real_syncchpool (num_chan : Nat) (p : SyncChanPool) : SyncChanPool :=
  init_zmap num_chan (.SyncChanValid (BitVec.ofNat 32 num_chan) 0 0) p

/-! ## The channels in the region (`IPCIntroGenDef.v`) -/

/-- `match_Chan`. -/
def MatchCh : SyncChannel → Val → Val → Val → Prop
  | .SyncChanUndef, _, _, _ => True
  | .SyncChanValid t p c, v1, v2, v3 => v1 = t ∧ v2 = p ∧ v3 = c

/-- `match_ChanPool`. Channel `i` is three cells at `ipb + 3 * i`. -/
def MatchSCP (num_chan ipb : Nat) (p : SyncChanPool) (b : Region) : Prop :=
  ∀ i, i < num_chan → MatchCh (p i) (b (tcell ipb i 0)) (b (tcell ipb i 1)) (b (tcell ipb i 2))

/-- The layout with the channel pool after the current-thread word. -/
structure ILayout (maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb : Nat) : Prop where
  clay : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb
  hib0 : cidb < ipb
  hie : ipb + 3 * num_chan ≤ pb

def MatchI (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb : Nat) (d : IData) (b : Region) :
    Prop :=
  MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb d.toCData b ∧
    MatchSCP num_chan ipb d.syncchpool b

/-- The cells of the channel pool. -/
def IPF (ipb num_chan : Nat) (k : Nat) : Prop := ipb ≤ k ∧ k < ipb + 3 * num_chan

section Region
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb : Nat}

/-- The layers up to the current thread depend only on the cells up to that
word and from the page-table pool on. -/
theorem matchC_frame (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {d : CData}
    {b b' : Region} (hM : MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb d b)
    (hfr : ∀ k, k ≤ cidb ∨ pb ≤ k → b' k = b k) :
    MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb d b' := by
  have := hL.hcb
  refine ⟨matchA_frame hL.qlay hM.1 (fun k hk => hfr k (by omega)), ?_⟩
  rw [hfr cidb (Or.inl (Nat.le_refl _))]; exact hM.2

theorem sc_get {p : SyncChanPool} {b : Region} (hM : MatchSCP num_chan ipb p b) {i : Nat} (hi : i < num_chan)
    {t pa c : Val} (he : p i = .SyncChanValid t pa c) :
    b (tcell ipb i 0) = t ∧ b (tcell ipb i 1) = pa ∧ b (tcell ipb i 2) = c := by
  have h := hM i hi
  rw [he] at h
  exact h

/-- **Rewriting a channel.** -/
theorem sc_put (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb) {d : IData}
    {b b' : Region} (hM : MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb d b)
    {i : Nat} (hi : i < num_chan) (t pa c : Val)
    (hfr : ∀ k, k < tcell ipb i 0 ∨ tcell ipb i 2 < k → b' k = b k)
    (e0 : b' (tcell ipb i 0) = t) (e1 : b' (tcell ipb i 1) = pa) (e2 : b' (tcell ipb i 2) = c) :
    MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb
      { d with syncchpool := setAt d.syncchpool i (.SyncChanValid t pa c) } b' := by
  have := hL.hib0; have := hL.hie
  refine ⟨matchC_frame hL.clay hM.1 (fun k hk => hfr k (by unfold tcell; omega)), fun j hj => ?_⟩
  show MatchCh (setAt d.syncchpool i (.SyncChanValid t pa c) j) _ _ _
  by_cases e : j = i
  · subst e
    rw [setAt_eq, e0, e1, e2]
    exact ⟨rfl, rfl, rfl⟩
  · rw [setAt_ne _ _ e, hfr _ (by unfold tcell; omega), hfr _ (by unfold tcell; omega),
      hfr _ (by unfold tcell; omega)]
    exact hM.2 j hj

theorem ipb_lt (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb) :
    ipb + 3 * num_chan ≤ 2 ^ 32 := by
  have := hL.hie; have := hL.clay.qlay.tlay.slay.lay.hib; have := hL.clay.qlay.tlay.slay.lay.hfb
  have := hL.clay.qlay.tlay.slay.lay.hend; omega

end Region

/-! ## The C code (`PThreadCSource.v`) -/

/-- `x = get_sync_chan_to(e)`: `return SYNCCHPOOL_LOC[e].to;` -/
def getSyncToS (ipb : Nat) (x : Ident) (ie : Expr) : Stmt APrim := tGetS ipb x ie 0
/-- `x = get_sync_chan_paddr(e)` -/
def getSyncPaddrS (ipb : Nat) (x : Ident) (ie : Expr) : Stmt APrim := tGetS ipb x ie 1
/-- `x = get_sync_chan_count(e)` -/
def getSyncCountS (ipb : Nat) (x : Ident) (ie : Expr) : Stmt APrim := tGetS ipb x ie 2
/-- `set_sync_chan_to(e, v)`: `SYNCCHPOOL_LOC[e].to = v;` -/
def setSyncToS (ipb : Nat) (ie ve : Expr) : Stmt APrim := tSetS ipb ie 0 ve
/-- `set_sync_chan_paddr(e, v)` -/
def setSyncPaddrS (ipb : Nat) (ie ve : Expr) : Stmt APrim := tSetS ipb ie 1 ve
/-- `set_sync_chan_count(e, v)` -/
def setSyncCountS (ipb : Nat) (ie ve : Expr) : Stmt APrim := tSetS ipb ie 2 ve

/-- `init_sync_chan(e)`: `.to = num_chan; .vaddr = 0; .count = 0;` -/
def initSyncS (ipb num_chan : Nat) (ie : Expr) : Stmt APrim :=
  .seq (setSyncToS ipb ie (.const (BitVec.ofNat 32 num_chan)))
    (.seq (setSyncPaddrS ipb ie (.const 0)) (setSyncCountS ipb ie (.const 0)))

/-- `get_kernel_pa(n, vaddr)`:
`kpa = pt_read(n, vaddr); kpa = kpa / PAGESIZE * PAGESIZE + vaddr % PAGESIZE;` Result in `r`. -/
def getKernelPaS (pb fb : Nat) : Stmt APrim :=
  .seq (ptReadS pb fb)
    (.assign "r" (.bin .add (.bin .mul (.bin .div (.var "r") (.const 4096)) (.const 4096))
      (.bin .mod (.var "vaddr") (.const 4096))))

section Steps
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb : Nat}

theorem iGet_run (εR : REnv) {c : CPU} {i0 : Nat}
    (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb) {l : RLog} {b : Region}
    (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) (x : Ident) {ie : Expr} {i k : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < num_chan) (hk : k < 3) :
    Runs (rprimsA εR c) (tGetS ipb x ie k) σ l (σ.set x (b (tcell ipb i k))) l :=
  rd_run (εR := εR) hcs hlk x _ (tcb_eval (ipb_lt hL) he hi hk)

theorem iSet_run (εR : REnv) {c : CPU} {i0 : Nat}
    (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb) {l : RLog} {b : Region}
    (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) {ie ve : Expr} {i k : Nat} {w : Val}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < num_chan) (hk : k < 3) (hw : ve.eval σ = w) :
    ∃ l', Runs (rprimsA εR c) (tSetS ipb ie k ve) σ l (σ.set "_" 0) l' ∧
      CS1 c i0 l' (setCell b (tcell ipb i k) w) :=
  wr_run (εR := εR) hcs hlk _ ve (tcb_eval (ipb_lt hL) he hi hk) hw

variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb
local notation "MI" => MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb

/-! ### The channels, as steps -/

/-- Reading the three words of a channel. -/
theorem getSyncI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb) (x : Ident)
    (hx : x ≠ "lk") {ie : Expr} {σ : Locals} {d : IData} {i : Nat} {t pa cn : Val}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < num_chan) (hch : d.syncchpool i = .SyncChanValid t pa cn) :
    Step εR c i0 MI F (getSyncToS ipb x ie) σ d (σ.set x t) d ∧
    Step εR c i0 MI F (getSyncPaddrS ipb x ie) σ d (σ.set x pa) d ∧
    Step εR c i0 MI F (getSyncCountS ipb x ie) σ d (σ.set x cn) d := by
  refine ⟨⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩,
    ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩,
    ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩⟩
  · obtain ⟨a0, -, -⟩ := sc_get hM.2 hi hch
    have hr := iGet_run εR hL hcs hlk x he hi (show 0 < 3 by decide)
    rw [a0] at hr
    exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩
  · obtain ⟨-, a1, -⟩ := sc_get hM.2 hi hch
    have hr := iGet_run εR hL hcs hlk x he hi (show 1 < 3 by decide)
    rw [a1] at hr
    exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩
  · obtain ⟨-, -, a2⟩ := sc_get hM.2 hi hch
    have hr := iGet_run εR hL hcs hlk x he hi (show 2 < 3 by decide)
    rw [a2] at hr
    exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem ipf_foot {b : Region} {i k : Nat} (hi : i < num_chan) (hk : k < 3) (w : Val) (k' : Nat)
    (hk' : ¬ IPF ipb num_chan k') : setCell b (tcell ipb i k) w k' = b k' := by
  refine sc_ne _ _ (fun e => hk' ?_)
  subst e
  unfold tcell; exact ⟨by omega, by omega⟩

theorem setSyncToI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hF : ∀ k, IPF ipb num_chan k → F k) {ie ve : Expr} {σ : Locals} {d : IData} {i : Nat} {w t pa cn : Val}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hve : ve.eval σ = w) (hi : i < num_chan)
    (hch : d.syncchpool i = .SyncChanValid t pa cn) :
    Step εR c i0 MI F (setSyncToS ipb ie ve) σ d (σ.set "_" 0)
      { d with syncchpool := setAt d.syncchpool i (.SyncChanValid w pa cn) } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨-, a1, a2⟩ := sc_get hM.2 hi hch
  obtain ⟨l', hr, hcs'⟩ := iSet_run εR hL hcs hlk he hi (show 0 < 3 by decide) hve
  exact ⟨l', _, hr, hcs', sc_put hL hM hi w pa cn (fun k hk => sc_ne _ _ (by unfold tcell at *; omega))
      (sc_eq _ _ _) (by rw [sc_ne _ _ (by unfold tcell; omega)]; exact a1)
      (by rw [sc_ne _ _ (by unfold tcell; omega)]; exact a2),
    fun k hk => ipf_foot hi (by decide) _ k (fun h => hk (hF k h))⟩

theorem setSyncPaddrI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hF : ∀ k, IPF ipb num_chan k → F k) {ie ve : Expr} {σ : Locals} {d : IData} {i : Nat} {w t pa cn : Val}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hve : ve.eval σ = w) (hi : i < num_chan)
    (hch : d.syncchpool i = .SyncChanValid t pa cn) :
    Step εR c i0 MI F (setSyncPaddrS ipb ie ve) σ d (σ.set "_" 0)
      { d with syncchpool := setAt d.syncchpool i (.SyncChanValid t w cn) } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨a0, -, a2⟩ := sc_get hM.2 hi hch
  obtain ⟨l', hr, hcs'⟩ := iSet_run εR hL hcs hlk he hi (show 1 < 3 by decide) hve
  exact ⟨l', _, hr, hcs', sc_put hL hM hi t w cn (fun k hk => sc_ne _ _ (by unfold tcell at *; omega))
      (by rw [sc_ne _ _ (by unfold tcell; omega)]; exact a0) (sc_eq _ _ _)
      (by rw [sc_ne _ _ (by unfold tcell; omega)]; exact a2),
    fun k hk => ipf_foot hi (by decide) _ k (fun h => hk (hF k h))⟩

theorem setSyncCountI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hF : ∀ k, IPF ipb num_chan k → F k) {ie ve : Expr} {σ : Locals} {d : IData} {i : Nat} {w t pa cn : Val}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hve : ve.eval σ = w) (hi : i < num_chan)
    (hch : d.syncchpool i = .SyncChanValid t pa cn) :
    Step εR c i0 MI F (setSyncCountS ipb ie ve) σ d (σ.set "_" 0)
      { d with syncchpool := setAt d.syncchpool i (.SyncChanValid t pa w) } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨a0, a1, -⟩ := sc_get hM.2 hi hch
  obtain ⟨l', hr, hcs'⟩ := iSet_run εR hL hcs hlk he hi (show 2 < 3 by decide) hve
  exact ⟨l', _, hr, hcs', sc_put hL hM hi t pa w (fun k hk => sc_ne _ _ (by unfold tcell at *; omega))
      (by rw [sc_ne _ _ (by unfold tcell; omega)]; exact a0)
      (by rw [sc_ne _ _ (by unfold tcell; omega)]; exact a1) (sc_eq _ _ _),
    fun k hk => ipf_foot hi (by decide) _ k (fun h => hk (hF k h))⟩

/-- `init_sync_chan`: the channel need not be valid before. The argument is
a local other than `_`. -/
theorem initSyncI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hF : ∀ k, IPF ipb num_chan k → F k) (a : Ident) (ha : a ≠ "_") {σ : Locals} {d : IData} {n : Nat}
    (hp : σ a = BitVec.ofNat 32 n) (hn : n < num_chan) :
    Step εR c i0 MI F (initSyncS ipb num_chan (.var a)) σ d (σ.set "_" 0)
      { d with syncchpool := setAt d.syncchpool n (.SyncChanValid (BitVec.ofNat 32 num_chan) 0 0) } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  let σ1 := σ.set "_" 0
  have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
  have hq : (Expr.var a).eval σ1 = BitVec.ofNat 32 n := (Locals.set_other _ _ ha).trans hp
  have hss : σ1.set "_" 0 = σ1 := set_set _ _ _ _
  obtain ⟨l1, r1, c1⟩ := iSet_run εR hL hcs hlk (ie := .var a) (ve := .const (BitVec.ofNat 32 num_chan))
    (w := BitVec.ofNat 32 num_chan) hp hn (show 0 < 3 by decide) rfl
  obtain ⟨l2, r2, c2⟩ := iSet_run εR hL c1 hlk1 (ie := .var a) (ve := .const 0) (w := 0) hq hn
    (show 1 < 3 by decide) rfl
  rw [hss] at r2
  obtain ⟨l3, r3, c3⟩ := iSet_run εR hL c2 hlk1 (ie := .var a) (ve := .const 0) (w := 0) hq hn
    (show 2 < 3 by decide) rfl
  rw [hss] at r3
  refine ⟨l3, _, Runs.seq r1 (Runs.seq r2 r3), c3, sc_put hL hM hn _ _ _ (fun k hk => ?_) ?_ ?_ ?_,
    fun k hk => ?_⟩
  · rw [sc_ne _ _ (by unfold tcell at *; omega), sc_ne _ _ (by unfold tcell at *; omega),
      sc_ne _ _ (by unfold tcell at *; omega)]
  · rw [sc_ne _ _ (by unfold tcell; omega), sc_ne _ _ (by unfold tcell; omega), sc_eq]
  · rw [sc_ne _ _ (by unfold tcell; omega), sc_eq]
  · rw [sc_eq]
  · rw [ipf_foot hn (by decide) _ k (fun h => hk (hF k h)), ipf_foot hn (by decide) _ k (fun h => hk (hF k h)),
      ipf_foot hn (by decide) _ k (fun h => hk (hF k h))]

/-! ### The layers below, in this state -/

/-- **A step of the layers below is a step in the state with the channels**,
if it writes no cell of the pool. -/
theorem stepCI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb) {s : Stmt APrim}
    {σ σ' : Locals} {d : IData} {c1 : CData} (h : Step εR c i0 MC F s σ d.toCData σ' c1)
    (hF : ∀ k, F k → k ≤ cidb ∨ pb ≤ k) :
    Step εR c i0 MI F s σ d σ' { d with toCData := c1 } := by
  have := hL.hib0; have := hL.hie
  refine Step.lift (π := IData.toCData)
    (put := fun (d' : IData) (c' : CData) => ({ d' with toCData := c' } : IData))
    (M2 := fun d' b => MatchSCP num_chan ipb d'.syncchpool b) h rfl (fun b b' h2 _ _ hf j hj => ?_)
  have e : ∀ k, k < 3 → b' (tcell ipb j k) = b (tcell ipb j k) := fun k hk =>
    hf _ (fun hk' => by have := hF _ hk'; unfold tcell at this; omega)
  show MatchCh (d.syncchpool j) _ _ _
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
  exact h2 j hj

/-- **A triple of the layers below holds in the state with the channels.** -/
theorem liftCI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    {P : Locals → CData → Prop} {s : Stmt APrim} {Q : Locals → CData → Locals → CData → Prop}
    (h : Triple εR c i0 MC F P s Q) (hF : ∀ k, F k → k ≤ cidb ∨ pb ≤ k) :
    Triple εR c i0 MI F (fun σ d => P σ d.toCData) s
      (fun σ d σ' d' => ∃ c1 : CData, d' = { d with toCData := c1 } ∧ Q σ d.toCData σ' c1) := by
  have := hL.hib0; have := hL.hie
  refine h.lift (π := IData.toCData)
    (put := fun (d' : IData) (c' : CData) => ({ d' with toCData := c' } : IData))
    (M2 := fun d' b => MatchSCP num_chan ipb d'.syncchpool b) (fun _ _ => rfl)
    (fun d' b σ σ' d1 b' h2 _ _ _ hf j hj => ?_)
  have e : ∀ k, k < 3 → b' (tcell ipb j k) = b (tcell ipb j k) := fun k hk =>
    hf _ (fun hk' => by have := hF _ hk'; unfold tcell at this; omega)
  show MatchCh (d'.syncchpool j) _ _ _
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
  exact h2 j hj

/-! ### Each accessor refines its specification -/

theorem getSyncTo_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (x : Ident) (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 MI (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_sync_chan_to_spec num_chan n d = some v)
      (getSyncToS ipb x ie)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_sync_chan_to_spec num_chan n d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  refine Step.triple (fun σ d ⟨he, v, hs⟩ => ?_)
  have hs0 := hs
  unfold get_sync_chan_to_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_chan
  · rw [if_pos hc] at hs
    cases hch : d.syncchpool n with
    | SyncChanUndef => rw [hch] at hs; cases hs
    | SyncChanValid t pa cn =>
      rw [hch] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, d, (getSyncI εR c i0 hL x hx he hc.2.2 hch).1, rfl, _, hs0, by simp⟩
  · rw [if_neg hc] at hs; cases hs

theorem getSyncPaddr_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (x : Ident) (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 MI (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_sync_chan_paddr_spec num_chan n d = some v)
      (getSyncPaddrS ipb x ie)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_sync_chan_paddr_spec num_chan n d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  refine Step.triple (fun σ d ⟨he, v, hs⟩ => ?_)
  have hs0 := hs
  unfold get_sync_chan_paddr_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_chan
  · rw [if_pos hc] at hs
    cases hch : d.syncchpool n with
    | SyncChanUndef => rw [hch] at hs; cases hs
    | SyncChanValid t pa cn =>
      rw [hch] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, d, (getSyncI εR c i0 hL x hx he hc.2.2 hch).2.1, rfl, _, hs0, by simp⟩
  · rw [if_neg hc] at hs; cases hs

theorem getSyncCount_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (x : Ident) (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 MI (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_sync_chan_count_spec num_chan n d = some v)
      (getSyncCountS ipb x ie)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_sync_chan_count_spec num_chan n d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  refine Step.triple (fun σ d ⟨he, v, hs⟩ => ?_)
  have hs0 := hs
  unfold get_sync_chan_count_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_chan
  · rw [if_pos hc] at hs
    cases hch : d.syncchpool n with
    | SyncChanUndef => rw [hch] at hs; cases hs
    | SyncChanValid t pa cn =>
      rw [hch] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, d, (getSyncI εR c i0 hL x hx he hc.2.2 hch).2.2, rfl, _, hs0, by simp⟩
  · rw [if_neg hc] at hs; cases hs

theorem setSyncTo_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (ie ve : Expr) (n sv : Nat) :
    Triple εR c i0 MI (IPF ipb num_chan)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧
        ∃ d1, set_sync_chan_to_spec num_chan n sv d = some d1)
      (setSyncToS ipb ie ve)
      (fun σ d σ' d' => set_sync_chan_to_spec num_chan n sv d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨he, hve, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold set_sync_chan_to_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_chan
  · rw [if_pos hc] at hs
    cases hch : d.syncchpool n with
    | SyncChanUndef => rw [hch] at hs; cases hs
    | SyncChanValid t pa cn =>
      rw [hch] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, _, setSyncToI εR c i0 hL (fun _ h => h) he hve hc.2.2 hch, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem setSyncPaddr_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (ie ve : Expr) (n sv : Nat) :
    Triple εR c i0 MI (IPF ipb num_chan)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧
        ∃ d1, set_sync_chan_paddr_spec num_chan n sv d = some d1)
      (setSyncPaddrS ipb ie ve)
      (fun σ d σ' d' => set_sync_chan_paddr_spec num_chan n sv d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨he, hve, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold set_sync_chan_paddr_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_chan
  · rw [if_pos hc] at hs
    cases hch : d.syncchpool n with
    | SyncChanUndef => rw [hch] at hs; cases hs
    | SyncChanValid t pa cn =>
      rw [hch] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, _, setSyncPaddrI εR c i0 hL (fun _ h => h) he hve hc.2.2 hch, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem setSyncCount_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (ie ve : Expr) (n sv : Nat) :
    Triple εR c i0 MI (IPF ipb num_chan)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧
        ∃ d1, set_sync_chan_count_spec num_chan n sv d = some d1)
      (setSyncCountS ipb ie ve)
      (fun σ d σ' d' => set_sync_chan_count_spec num_chan n sv d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨he, hve, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold set_sync_chan_count_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_chan
  · rw [if_pos hc] at hs
    cases hch : d.syncchpool n with
    | SyncChanUndef => rw [hch] at hs; cases hs
    | SyncChanValid t pa cn =>
      rw [hch] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨_, _, setSyncCountI εR c i0 hL (fun _ h => h) he hve hc.2.2 hch, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`init_sync_chan` refines `init_sync_chan_spec`.** -/
theorem initSync_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (a : Ident) (ha : a ≠ "_") (n : Nat) :
    Triple εR c i0 MI (IPF ipb num_chan)
      (fun σ d => σ a = BitVec.ofNat 32 n ∧ ∃ d1, init_sync_chan_spec num_chan n d = some d1)
      (initSyncS ipb num_chan (.var a))
      (fun σ d σ' d' => init_sync_chan_spec num_chan n d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨hp, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold init_sync_chan_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_chan
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    exact ⟨_, _, initSyncI εR c i0 hL (fun _ h => h) a ha hp hc.2.2, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-! ## `proc_init`'s loop (`PIPCIntroCSource.v`) -/

/-- `i = 0; while (i < num_chan) { init_sync_chan(i); i++; }` -/
def syncInitLoop (ipb num_chan : Nat) : Stmt APrim :=
  .seq (.assign "i" (.const 0))
    (.while (.bin .ltu (.var "i") (.const (BitVec.ofNat 32 num_chan)))
      (.seq (initSyncS ipb num_chan (.var "i")) (.assign "i" (.bin .add (.var "i") (.const 1)))))

/-- **The loop of `proc_init` resets every channel** (`real_syncchpool`). -/
theorem syncInit_step (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hF : ∀ k, IPF ipb num_chan k → F k) (σ : Locals) (d : IData) :
    ∃ σ', Step εR c i0 MI F (syncInitLoop ipb num_chan) σ d σ'
      { d with syncchpool := real_syncchpool num_chan d.syncchpool } := by
  have hnc : num_chan < 2 ^ 32 := by have := ipb_lt hL; omega
  let x0 : SyncChannel := .SyncChanValid (BitVec.ofNat 32 num_chan) 0 0
  let I : Locals → IData → Prop := fun τ e => ∃ m, m ≤ num_chan ∧ τ "i" = BitVec.ofNat 32 m ∧
    e = { d with syncchpool := init_zmap m x0 d.syncchpool }
  have hbody : ∀ τ e, I τ e →
      ¬ (Expr.bin .ltu (.var "i") (.const (BitVec.ofNat 32 num_chan))).eval τ = 0 →
      ∃ τ' e', Step εR c i0 MI F (.seq (initSyncS ipb num_chan (.var "i"))
          (.assign "i" (.bin .add (.var "i") (.const 1)))) τ e τ' e' ∧ I τ' e' ∧
        num_chan - (τ' "i").toNat < num_chan - (τ "i").toNat := by
    rintro τ e ⟨m, hm, hiτ, rfl⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .const (BitVec.ofNat 32 num_chan)) hiτ rfl
      (by omega) hnc] at hg
    have hmlt : m < num_chan := by
      by_cases h : m < num_chan
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    refine ⟨_, _, (initSyncI εR c i0 hL hF "i" (by decide) hiτ hmlt).seq
      (Step.assign' "i" (by decide) _ (inc_eval (m := m)
        (by rw [Locals.set_other _ _ (by decide)]; exact hiτ))), ⟨m + 1, hmlt, by simp, rfl⟩, ?_⟩
    rw [Locals.set_same, hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', e', hr, ⟨m, hm, hi', rfl⟩, h0⟩ :=
    Step.while_inv (εR := εR) (c := c) (i := i0) (M := MI) (F := F) I
      (fun τ => num_chan - (τ "i").toNat) hbody num_chan (σ.set "i" 0) d (by omega)
      ⟨0, by omega, by simp, rfl⟩
  rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .const (BitVec.ofNat 32 num_chan)) hi' rfl
    (by omega) hnc] at h0
  have hme : m = num_chan := by
    by_cases h : m < num_chan
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  exact ⟨σ', (Step.assign "i" (by decide) (.const 0)).seq hr⟩

/-! ## `get_kernel_pa` -/

/-- A page-table entry read from the region is a machine word. -/
theorem ptRead_lt {d : PTData} {b : Region} (hM : MatchAll maxpage num_id cb num_proc pb ib fb ida d b)
    {n vadr v : Nat} (hs : ptRead_spec num_proc n vadr d = some v) : v < 2 ^ 32 := by
  unfold ptRead_spec getPTE_spec at hs
  by_cases hc : d.init = true ∧ d.ipt = true ∧ PTE_Arg num_proc n (PDX vadr) (PTX vadr)
  · rw [if_pos hc] at hs
    obtain ⟨-, -, ⟨hnp, hi1⟩, hv1⟩ := hc
    cases hp : d.ptpool n (PDX vadr) with
    | PDEID => rw [hp] at hs; cases hs
    | PDEUnPresent => rw [hp] at hs; cases hs
    | PDEUndef => rw [hp] at hs; cases hs
    | PDEValid pi pdt =>
      rw [hp] at hs
      simp only at hs
      have hrel := hM.pt.pte n (PDX vadr) pi pdt hnp hi1 hp (PTX vadr) hv1
      cases hv : pdt (PTX vadr) with
      | PTEUndef => rw [hv] at hs; cases hs
      | PTEUnPresent =>
        rw [hv] at hs
        simp only [Option.some.injEq] at hs
        omega
      | PTEValid padr pm =>
        rw [hv] at hs hrel
        simp only [Option.some.injEq] at hs
        have hrel' : (b (fb + pi * 1024 + PTX vadr)).toNat = padr * 4096 + PermtoZ pm := hrel
        have := (b (fb + pi * 1024 + PTX vadr)).isLt
        omega
  · rw [if_neg hc] at hs; cases hs

theorem kpa_eval {a v : Nat} (ha : a < 2 ^ 32) (hv : v < 2 ^ 32) :
    ((BitVec.ofNat 32 a : Val) / 4096) * 4096 + (BitVec.ofNat 32 v : Val) % 4096 =
      BitVec.ofNat 32 (a / 4096 * 4096 + v % 4096) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod, tn ha, tn hv,
    tn (show a / 4096 * 4096 + v % 4096 < 2 ^ 32 by omega)]
  show (a / 4096 * 4096 % 2 ^ 32 + v % 4096) % 2 ^ 32 = _
  omega

/-- **`get_kernel_pa` refines `get_kernel_pa_spec`.** The process is in `n`,
the address in `vaddr`, the result in `r`. -/
theorem getKernelPa_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (pid vaddr : Nat) (hva : vaddr < 2 ^ 32) :
    Triple εR c i0 MI (fun _ => False)
      (fun σ d => σ "n" = BitVec.ofNat 32 pid ∧ σ "vaddr" = BitVec.ofNat 32 vaddr ∧
        ∃ v, get_kernel_pa_spec num_proc pid vaddr d = some v)
      (getKernelPaS pb fb)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_kernel_pa_spec num_proc pid vaddr d = some v ∧ v < 2 ^ 32 ∧
        σ' "r" = BitVec.ofNat 32 v ∧ ∀ z, frS z (getKernelPaS pb fb) = true → σ' z = σ z) := by
  intro σ l b d hlk hcs hM ⟨hn, hvaddr, v, hs⟩
  have hLay := hL.clay.qlay.tlay.slay.lay
  have hs0 := hs
  unfold get_kernel_pa_spec at hs
  by_cases hpg : d.pg = true
  · rw [if_pos hpg] at hs
    cases hp : ptRead_spec num_proc pid vaddr d.toPTData with
    | none => rw [hp] at hs; cases hs
    | some paddr =>
      rw [hp] at hs
      simp only at hs
      by_cases h0 : paddr = 0
      · rw [if_pos h0] at hs; cases hs
      · rw [if_neg h0] at hs
        simp only [Option.some.injEq] at hs
        obtain ⟨⟨q, hQ, hS, -, -⟩, -⟩ := hM.1
        have eP : d.toPTData = q.toPTData := congrArg SData.toPTData hS
        have hp' : ptRead_spec num_proc pid vaddr q.toPTData = some paddr := by rw [← eP]; exact hp
        have hplt : paddr < 2 ^ 32 := ptRead_lt hQ.t.s.all hp'
        have T := liftCI εR c i0 hL (liftPC εR c i0 hL.clay
          (ptRead_triple εR c i0 (by have := hLay.hib; have := hLay.hfb; have := hLay.hend; omega) hLay.hend
            pid vaddr hva (ida := ida)) (fun _ h => h.elim) (fun _ _ _ _ _ hq => by rw [hq.1]))
          (fun _ h => h.elim)
        obtain ⟨σ1, l1, b1, d1, hr, hcs1, hM1, hlk1, hf, c1, hd1, p, hc1, hpe, v', hv', hr1⟩ :=
          T σ l b d hlk hcs hM ⟨hn, hvaddr, paddr, hp⟩
        rw [hp] at hv'
        simp only [Option.some.injEq] at hv'
        subst hv'
        have hb : b1 = b := funext (fun k => hf k (fun h => h))
        have hd : d1 = d := by rw [hd1, hc1, hpe]
        subst hb; subst hd
        have hva1 : σ1 "vaddr" = BitVec.ofNat 32 vaddr := (hr.frame rfl).trans hvaddr
        have hval : (Expr.bin .add (.bin .mul (.bin .div (.var "r") (.const 4096)) (.const 4096))
            (.bin .mod (.var "vaddr") (.const 4096))).eval σ1 = BitVec.ofNat 32 v := by
          show (σ1 "r" / 4096) * 4096 + σ1 "vaddr" % 4096 = _
          rw [hr1, hva1, kpa_eval hplt hva, hs]
        have hrun : Runs (rprimsA εR c) (getKernelPaS pb fb) σ l (σ1.set "r" (BitVec.ofNat 32 v)) l1 :=
          Runs.seq hr (asg_run "r" _ hval)
        refine ⟨_, l1, b1, d1, hrun, hcs1, hM1, by simp [Locals.set, hlk1], fun _ _ => rfl, rfl, v, hs0, ?_,
          by simp, fun z hz => hrun.frame hz⟩
        rw [← hs]; omega
  · rw [if_neg hpg] at hs; cases hs

end Steps

end PIPC
