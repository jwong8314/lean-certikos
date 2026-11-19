import CertiKOS.MPTResv2
import CertiKOS.MALInitC

/-!
# mCertiKOS `MShareIntro`: the shared-memory table, ported

Two processes share a page through a small protocol. For each ordered pair
of processes the kernel keeps a state (ready, pending, dead), whether the
first has seen the latest state, and the address the first offered.

Ported from `layerlib/AuxStateDataType.v`: `SharedMemInfo`, `SharedMemState`,
`SharedMemSTPool`, `SharedMemInfo2Z`, `Z2SharedMemInfo`.

Ported from `objects/ObjShareMem.v`: `shared_mem_arg`, the three getters, the
three setters, `clear_shared_mem_spec`.

Ported from `mm/ShareIntroGenDef.v`: `match_SharedMem`, `match_SharedMemSTPool`
(`MatchSMS`, `MatchSP`).

Ported from `mm/MPTNewCSource.v`: the C code of the seven accessors.

Each accessor refines its specification (`getState_triple`, …,
`clear_triple`).

What differs: the table is in the memory-management region, between the
containers and the page-table pool (`SLayout`), with entry `(p1, p2)` at cell
`sb + (p1 * num_proc + p2) * 3`: location, state, seen. Calls are inlined
statements whose two process arguments are expressions.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MShare

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew
open MALInit (rd_run wr_run asg_run tn)

/-! ## Abstract data (`AuxStateDataType.v`) -/

inductive SharedMemInfo
  | SHRDREADY | SHRDPEND | SHRDDEAD
  deriving DecidableEq

/-- `SHRDValid info seen vadr`. -/
inductive SharedMemState
  | SHRDValid (info : SharedMemInfo) (seen : Bool) (vadr : Nat)
  | SHRDUndef

abbrev SharedMemSTPool := Nat → Nat → SharedMemState

/-- `SHARED_MEM_READY = 0`, `SHARED_MEM_PEND = 1`, `SHARED_MEM_DEAD = 2`. -/
def SharedMemInfo2Z : SharedMemInfo → Nat
  | .SHRDREADY => 0
  | .SHRDPEND => 1
  | .SHRDDEAD => 2

def Z2SharedMemInfo : Nat → Option SharedMemInfo
  | 0 => some .SHRDREADY
  | 1 => some .SHRDPEND
  | 2 => some .SHRDDEAD
  | _ => none

theorem Z2SharedMemInfo_correct {st : Nat} {i : SharedMemInfo} (h : Z2SharedMemInfo st = some i) :
    SharedMemInfo2Z i = st := by
  match st, h with
  | 0, h => simp [Z2SharedMemInfo] at h; subst h; rfl
  | 1, h => simp [Z2SharedMemInfo] at h; subst h; rfl
  | 2, h => simp [Z2SharedMemInfo] at h; subst h; rfl
  | n + 3, h => simp [Z2SharedMemInfo] at h

theorem SharedMemInfo2Z_correct (i : SharedMemInfo) : Z2SharedMemInfo (SharedMemInfo2Z i) = some i := by
  cases i <;> rfl

theorem SharedMemInfo2Z_range (i : SharedMemInfo) : SharedMemInfo2Z i < 3 := by
  cases i <;> decide

/-- `PTData` with the shared-memory table. -/
structure SData extends PTData where
  smspool : SharedMemSTPool

/-- Replace entry `(p1, p2)`. -/
def smSet (sp : SharedMemSTPool) (p1 p2 : Nat) (x : SharedMemState) : SharedMemSTPool :=
  setAt sp p1 (setAt (sp p1) p2 x)

theorem smSet_eq (sp : SharedMemSTPool) (p1 p2 : Nat) (x : SharedMemState) : smSet sp p1 p2 x p1 p2 = x := by
  unfold smSet; rw [setAt_eq, setAt_eq]

theorem smSet_ne (sp : SharedMemSTPool) {p1 p2 q1 q2 : Nat} (x : SharedMemState) (h : ¬ (q1 = p1 ∧ q2 = p2)) :
    smSet sp p1 p2 x q1 q2 = sp q1 q2 := by
  unfold smSet
  by_cases h1 : q1 = p1
  · subst h1
    rw [setAt_eq, setAt_ne _ _ (fun e => h ⟨rfl, e⟩)]
  · rw [setAt_ne _ _ h1]

/-! ## Specifications (`ObjShareMem.v`) -/

section Specs
variable (num_proc : Nat)

/-- `shared_mem_arg`: two different processes. -/
def shared_mem_arg (pid1 pid2 : Nat) : Prop := pid1 < num_proc ∧ pid2 < num_proc ∧ pid1 ≠ pid2

/-- `shared_mem_arg'`: two processes. -/
def shared_mem_arg' (pid1 pid2 : Nat) : Prop := pid1 < num_proc ∧ pid2 < num_proc

instance (a b : Nat) : Decidable (shared_mem_arg num_proc a b) := by unfold shared_mem_arg; exact inferInstance
instance (a b : Nat) : Decidable (shared_mem_arg' num_proc a b) := by unfold shared_mem_arg'; exact inferInstance

def get_shared_mem_state_spec (pid1 pid2 : Nat) (d : SData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2 with
    | .SHRDValid i _ _ => some (SharedMemInfo2Z i)
    | .SHRDUndef => none
  else none

def get_shared_mem_seen_spec (pid1 pid2 : Nat) (d : SData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2 with
    | .SHRDValid _ s _ => some (if s then 1 else 0)
    | .SHRDUndef => none
  else none

def get_shared_mem_loc_spec (pid1 pid2 : Nat) (d : SData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2 with
    | .SHRDValid _ _ vadr => some vadr
    | .SHRDUndef => none
  else none

def set_shared_mem_state_spec (pid1 pid2 n : Nat) (d : SData) : Option SData :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2, Z2SharedMemInfo n with
    | .SHRDValid _ s vadr, some i => some { d with smspool := smSet d.smspool pid1 pid2 (.SHRDValid i s vadr) }
    | _, _ => none
  else none

def set_shared_mem_seen_spec (pid1 pid2 n : Nat) (d : SData) : Option SData :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2, ZtoBool n with
    | .SHRDValid i _ vadr, some s => some { d with smspool := smSet d.smspool pid1 pid2 (.SHRDValid i s vadr) }
    | _, _ => none
  else none

def set_shared_mem_loc_spec (pid1 pid2 vadr : Nat) (d : SData) : Option SData :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc pid1 pid2 then
    match d.smspool pid1 pid2 with
    | .SHRDValid i s _ => some { d with smspool := smSet d.smspool pid1 pid2 (.SHRDValid i s vadr) }
    | .SHRDUndef => none
  else none

def clear_shared_mem_spec (pid1 pid2 : Nat) (d : SData) : Option SData :=
  if d.pg = true ∧ d.ipt = true ∧ shared_mem_arg' num_proc pid1 pid2 then
    some { d with smspool := smSet d.smspool pid1 pid2 (.SHRDValid .SHRDDEAD true 0) }
  else none

end Specs

/-! ## The table in the region (`ShareIntroGenDef.v`) -/

/-- Cell `k` of entry `(p1, p2)`: 0 location, 1 state, 2 seen. -/
def scell (sb num_proc p1 p2 k : Nat) : Nat := sb + (p1 * num_proc + p2) * 3 + k

/-- `match_SharedMem`: an entry and its three words. -/
def MatchSMS : SharedMemState → Val → Val → Val → Prop
  | .SHRDUndef, _, _, _ => True
  | .SHRDValid si b vadr, vloc, vst, vseen =>
    Z2SharedMemInfo vst.toNat = some si ∧ ZtoBool vseen.toNat = some b ∧ vadr = vloc.toNat

/-- `match_SharedMemSTPool`. -/
def MatchSP (num_proc sb : Nat) (sp : SharedMemSTPool) (b : Region) : Prop :=
  ∀ p1 p2, p1 < num_proc → p2 < num_proc →
    MatchSMS (sp p1 p2) (b (scell sb num_proc p1 p2 0)) (b (scell sb num_proc p1 p2 1))
      (b (scell sb num_proc p1 p2 2))

/-- The memory-management layout with the shared-memory table between the
containers and the page-table pool. -/
structure SLayout (maxpage num_id cb num_proc pb ib fb sb : Nat) : Prop where
  lay : Layout maxpage num_id cb num_proc pb ib fb
  hsb : cb + 5 * num_id ≤ sb
  hse : sb + 3 * (num_proc * num_proc) ≤ pb

/-- The whole region against the whole state. -/
structure MatchS (maxpage num_id cb num_proc pb ib fb ida sb : Nat) (d : SData) (b : Region) : Prop where
  all : MatchAll maxpage num_id cb num_proc pb ib fb ida d.toPTData b
  sp : MatchSP num_proc sb d.smspool b

theorem sm_lt {n p1 p2 : Nat} (h1 : p1 < n) (h2 : p2 < n) : p1 * n + p2 < n * n := by
  have e : (p1 + 1) * n = p1 * n + n := Nat.succ_mul p1 n
  have : (p1 + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
  omega

theorem sm_inj {n p1 p2 q1 q2 : Nat} (h2 : p2 < n) (g2 : q2 < n) (h : p1 * n + p2 = q1 * n + q2) :
    p1 = q1 ∧ p2 = q2 := by
  have key : ∀ a b a2 b2 : Nat, a2 < n → b2 < n → a < b → a * n + a2 ≠ b * n + b2 := by
    intro a b a2 b2 ha hb hab e
    have e1 : (a + 1) * n = a * n + n := Nat.succ_mul a n
    have : (a + 1) * n ≤ b * n := Nat.mul_le_mul_right n hab
    omega
  have hp : p1 = q1 := by
    rcases Nat.lt_trichotomy p1 q1 with h' | h' | h'
    · exact absurd h (key p1 q1 p2 q2 h2 g2 h')
    · exact h'
    · exact absurd h.symm (key q1 p1 q2 p2 g2 h2 h')
  subst hp
  exact ⟨rfl, by omega⟩

theorem scell_lt {sb n p1 p2 k : Nat} (h1 : p1 < n) (h2 : p2 < n) (hk : k < 3) :
    scell sb n p1 p2 k < sb + 3 * (n * n) := by
  have := sm_lt h1 h2
  unfold scell; omega

/-- Different entries have different cells. -/
theorem scell_ne {sb n p1 p2 q1 q2 k j : Nat} (h2 : p2 < n) (g2 : q2 < n) (hk : k < 3) (hj : j < 3)
    (h : ¬ (q1 = p1 ∧ q2 = p2)) : scell sb n q1 q2 j ≠ scell sb n p1 p2 k := by
  intro e
  unfold scell at e
  have : q1 * n + q2 = p1 * n + p2 := by omega
  exact h (sm_inj g2 h2 this)

section Region
variable {maxpage num_id cb num_proc pb ib fb ida sb : Nat}

/-- The page tables, the allocation table and the containers do not depend on
the cells of the shared-memory table. -/
theorem matchAll_frame (hL : SLayout maxpage num_id cb num_proc pb ib fb sb) {d : PTData} {b b' : Region}
    (hM : MatchAll maxpage num_id cb num_proc pb ib fb ida d b)
    (hfr : ∀ k, k < sb ∨ sb + 3 * (num_proc * num_proc) ≤ k → b' k = b k) :
    MatchAll maxpage num_id cb num_proc pb ib fb ida d b' := by
  have := hL.lay.hcb; have := hL.lay.hpb; have := hL.hsb; have := hL.hse
  have hb : ∀ k, k < cb + 5 * num_id → b' k = b k := fun k hk => hfr k (Or.inl (by omega))
  refine ⟨⟨⟨fun j hj => ?_, ?_⟩, fun j hj => ?_⟩,
    matchpt_transfer hL.lay hM.pt (fun k hk => hfr k (Or.inr (by omega))) rfl rfl rfl (fun _ _ _ _ => rfl)⟩
  · rw [hb _ (by omega), hb _ (by omega), hb _ (by omega)]; exact hM.mm.mAT.mat j hj
  · rw [hb _ (by omega)]; exact hM.mm.mAT.mnps
  · rw [hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]
    exact hM.mm.mAC j hj

/-- What the three words of a valid entry are. -/
theorem sm_get {sp : SharedMemSTPool} {b : Region} (hM : MatchSP num_proc sb sp b) {p1 p2 : Nat}
    (h1 : p1 < num_proc) (h2 : p2 < num_proc) {i : SharedMemInfo} {s : Bool} {v : Nat}
    (he : sp p1 p2 = .SHRDValid i s v) :
    b (scell sb num_proc p1 p2 0) = BitVec.ofNat 32 v ∧
    b (scell sb num_proc p1 p2 1) = BitVec.ofNat 32 (SharedMemInfo2Z i) ∧
    b (scell sb num_proc p1 p2 2) = BitVec.ofNat 32 (if s then 1 else 0) ∧ v < 2 ^ 32 := by
  have h := hM p1 p2 h1 h2
  rw [he] at h
  obtain ⟨a1, a2, a3⟩ := h
  have hv : v < 2 ^ 32 := by rw [a3]; exact (b (scell sb num_proc p1 p2 0)).isLt
  refine ⟨val_of_toNat a3.symm hv, ?_, ?_, hv⟩
  · have := SharedMemInfo2Z_range i
    exact val_of_toNat (Z2SharedMemInfo_correct a1).symm (by omega)
  · rcases zbool_cases a2 with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact val_of_toNat e (by decide)
    · exact val_of_toNat e (by decide)

/-- **Rewriting an entry.** If the region changes only in the three words of
entry `(p1, p2)`, and they now hold a valid entry, the relation holds for the
table with that entry replaced. -/
theorem sm_put (hL : SLayout maxpage num_id cb num_proc pb ib fb sb) {d : SData} {b b' : Region}
    (hM : MatchS maxpage num_id cb num_proc pb ib fb ida sb d b) {p1 p2 : Nat} (h1 : p1 < num_proc)
    (h2 : p2 < num_proc) {i : SharedMemInfo} {s : Bool} {v : Nat} (hv : v < 2 ^ 32)
    (hfr : ∀ k, k < scell sb num_proc p1 p2 0 ∨ scell sb num_proc p1 p2 2 < k → b' k = b k)
    (e0 : b' (scell sb num_proc p1 p2 0) = BitVec.ofNat 32 v)
    (e1 : b' (scell sb num_proc p1 p2 1) = BitVec.ofNat 32 (SharedMemInfo2Z i))
    (e2 : b' (scell sb num_proc p1 p2 2) = BitVec.ofNat 32 (if s then 1 else 0)) :
    MatchS maxpage num_id cb num_proc pb ib fb ida sb
      { d with smspool := smSet d.smspool p1 p2 (.SHRDValid i s v) } b' := by
  have hlt := scell_lt (sb := sb) h1 h2 (show 2 < 3 by decide)
  refine ⟨matchAll_frame hL hM.all (fun k hk => hfr k ?_), fun q1 q2 g1 g2 => ?_⟩
  · unfold scell at hlt ⊢; omega
  · show MatchSMS (smSet d.smspool p1 p2 (.SHRDValid i s v) q1 q2) _ _ _
    by_cases e : q1 = p1 ∧ q2 = p2
    · obtain ⟨rfl, rfl⟩ := e
      rw [smSet_eq, e0, e1, e2]
      have := SharedMemInfo2Z_range i
      refine ⟨by rw [tn (by omega)]; exact SharedMemInfo2Z_correct i, ?_, (tn hv).symm⟩
      cases s
      · exact rfl
      · exact rfl
    · rw [smSet_ne _ _ e]
      have n0 := scell_ne (sb := sb) (k := 0) (j := 0) h2 g2 (by decide) (by decide) e
      have n1 := scell_ne (sb := sb) (k := 0) (j := 1) h2 g2 (by decide) (by decide) e
      have n2 := scell_ne (sb := sb) (k := 0) (j := 2) h2 g2 (by decide) (by decide) e
      have m0 := scell_ne (sb := sb) (k := 2) (j := 0) h2 g2 (by decide) (by decide) e
      have m1 := scell_ne (sb := sb) (k := 2) (j := 1) h2 g2 (by decide) (by decide) e
      have m2 := scell_ne (sb := sb) (k := 2) (j := 2) h2 g2 (by decide) (by decide) e
      have k0 := scell_ne (sb := sb) (k := 1) (j := 0) h2 g2 (by decide) (by decide) e
      have k1 := scell_ne (sb := sb) (k := 1) (j := 1) h2 g2 (by decide) (by decide) e
      have k2 := scell_ne (sb := sb) (k := 1) (j := 2) h2 g2 (by decide) (by decide) e
      rw [hfr _ (by unfold scell at *; omega), hfr _ (by unfold scell at *; omega),
        hfr _ (by unfold scell at *; omega)]
      exact hM.sp q1 q2 g1 g2

end Region

/-! ## The C code (`MPTNewCSource.v`) -/

/-- `&SHRDMEMPOOL_LOC[e1][e2]`, field `k`. -/
def smE (sb num_proc : Nat) (e1 e2 : Expr) (k : Nat) : Expr :=
  .bin .add (.const (BitVec.ofNat 32 (sb + k)))
    (.bin .mul (.bin .add (.bin .mul e1 (.const (BitVec.ofNat 32 num_proc))) e2) (.const 3))

theorem sm_eval {sb n : Nat} (hend : sb + 3 * (n * n) ≤ 2 ^ 32) {σ : Locals} {e1 e2 : Expr} {p1 p2 k : Nat}
    (he1 : e1.eval σ = BitVec.ofNat 32 p1) (he2 : e2.eval σ = BitVec.ofNat 32 p2) (h1 : p1 < n)
    (h2 : p2 < n) (hk : k < 3) : ((smE sb n e1 e2 k).eval σ).toNat = scell sb n p1 p2 k := by
  have e : (smE sb n e1 e2 k).eval σ =
      BitVec.ofNat 32 (sb + k) + (e1.eval σ * BitVec.ofNat 32 n + e2.eval σ) * (3 : Val) := rfl
  have hlt := sm_lt h1 h2
  rw [e, he1, he2, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, show (3 : Val) = BitVec.ofNat 32 3 from rfl,
    ← BitVec.ofNat_mul, ← BitVec.ofNat_add, tn (by omega)]
  unfold scell; omega

def smGetS (sb num_proc : Nat) (x : Ident) (e1 e2 : Expr) (k : Nat) : Stmt APrim :=
  .call x .pull [lkE, smE sb num_proc e1 e2 k]

def smSetS (sb num_proc : Nat) (e1 e2 : Expr) (k : Nat) (ve : Expr) : Stmt APrim :=
  .call "_" .push [lkE, smE sb num_proc e1 e2 k, ve]

/-- `x = get_shared_mem_loc(e1, e2)`: `return SHRDMEMPOOL_LOC[e1][e2].smsp_loc;` -/
def getLocS (sb num_proc : Nat) (x : Ident) (e1 e2 : Expr) : Stmt APrim := smGetS sb num_proc x e1 e2 0
/-- `x = get_shared_mem_state(e1, e2)` -/
def getStateS (sb num_proc : Nat) (x : Ident) (e1 e2 : Expr) : Stmt APrim := smGetS sb num_proc x e1 e2 1
/-- `x = get_shared_mem_seen(e1, e2)` -/
def getSeenS (sb num_proc : Nat) (x : Ident) (e1 e2 : Expr) : Stmt APrim := smGetS sb num_proc x e1 e2 2
/-- `set_shared_mem_loc(e1, e2, v)`: `SHRDMEMPOOL_LOC[e1][e2].smsp_loc = v;` -/
def setLocS (sb num_proc : Nat) (e1 e2 ve : Expr) : Stmt APrim := smSetS sb num_proc e1 e2 0 ve
/-- `set_shared_mem_state(e1, e2, v)` -/
def setStateS (sb num_proc : Nat) (e1 e2 ve : Expr) : Stmt APrim := smSetS sb num_proc e1 e2 1 ve
/-- `set_shared_mem_seen(e1, e2, v)` -/
def setSeenS (sb num_proc : Nat) (e1 e2 ve : Expr) : Stmt APrim := smSetS sb num_proc e1 e2 2 ve

/-- `clear_shared_mem(e1, e2)`: `.smsp_loc = 0; .smsp_state = 2; .smsp_seen = 1;` -/
def clearS (sb num_proc : Nat) (e1 e2 : Expr) : Stmt APrim :=
  .seq (setLocS sb num_proc e1 e2 (.const 0))
    (.seq (setStateS sb num_proc e1 e2 (.const 2)) (setSeenS sb num_proc e1 e2 (.const 1)))

section Runs
variable {maxpage num_id cb num_proc pb ib fb ida sb : Nat}

theorem smGet_run (εR : REnv) {c : CPU} {i0 : Nat} (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    {l : RLog} {b : Region} (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) (x : Ident)
    {e1 e2 : Expr} {p1 p2 k : Nat} (he1 : e1.eval σ = BitVec.ofNat 32 p1)
    (he2 : e2.eval σ = BitVec.ofNat 32 p2) (h1 : p1 < num_proc) (h2 : p2 < num_proc) (hk : k < 3) :
    Runs (rprimsA εR c) (smGetS sb num_proc x e1 e2 k) σ l (σ.set x (b (scell sb num_proc p1 p2 k))) l := by
  have := hL.hse; have := hL.lay.hib; have := hL.lay.hfb; have := hL.lay.hend
  exact rd_run (εR := εR) hcs hlk x _ (sm_eval (by omega) he1 he2 h1 h2 hk)

theorem smSet_run (εR : REnv) {c : CPU} {i0 : Nat} (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    {l : RLog} {b : Region} (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0)
    {e1 e2 ve : Expr} {p1 p2 k : Nat} {w : Val} (he1 : e1.eval σ = BitVec.ofNat 32 p1)
    (he2 : e2.eval σ = BitVec.ofNat 32 p2) (h1 : p1 < num_proc) (h2 : p2 < num_proc) (hk : k < 3)
    (hw : ve.eval σ = w) :
    ∃ l', Runs (rprimsA εR c) (smSetS sb num_proc e1 e2 k ve) σ l (σ.set "_" 0) l' ∧
      CS1 c i0 l' (setCell b (scell sb num_proc p1 p2 k) w) := by
  have := hL.hse; have := hL.lay.hib; have := hL.lay.hfb; have := hL.lay.hend
  exact wr_run (εR := εR) hcs hlk _ ve (sm_eval (by omega) he1 he2 h1 h2 hk) hw

end Runs

end MShare
