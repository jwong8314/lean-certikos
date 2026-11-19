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

/-! ## The accessors refine their specifications -/

section Triples
variable {maxpage num_id cb num_proc pb ib fb ida sb : Nat}

/-- One word of a valid entry is overwritten, and the entry it now encodes. -/
theorem sm_set1 (hL : SLayout maxpage num_id cb num_proc pb ib fb sb) {d : SData} {b : Region}
    (hM : MatchS maxpage num_id cb num_proc pb ib fb ida sb d b) {p1 p2 : Nat} (h1 : p1 < num_proc)
    (h2 : p2 < num_proc) {i : SharedMemInfo} {s : Bool} {v : Nat} (he : d.smspool p1 p2 = .SHRDValid i s v)
    {k : Nat} (hk : k < 3) (w : Val) {i' : SharedMemInfo} {s' : Bool} {v' : Nat} (hv' : v' < 2 ^ 32)
    (c0 : k = 0 → w = BitVec.ofNat 32 v') (c0' : k ≠ 0 → v' = v)
    (c1 : k = 1 → w = BitVec.ofNat 32 (SharedMemInfo2Z i')) (c1' : k ≠ 1 → i' = i)
    (c2 : k = 2 → w = BitVec.ofNat 32 (if s' then 1 else 0)) (c2' : k ≠ 2 → s' = s) :
    MatchS maxpage num_id cb num_proc pb ib fb ida sb
      { d with smspool := smSet d.smspool p1 p2 (.SHRDValid i' s' v') }
      (setCell b (scell sb num_proc p1 p2 k) w) := by
  obtain ⟨a0, a1, a2, -⟩ := sm_get hM.sp h1 h2 he
  refine sm_put hL hM h1 h2 hv' (fun k' hk' => sc_ne _ _ (by unfold scell at *; omega)) ?_ ?_ ?_
  · by_cases e : k = 0
    · subst e; rw [sc_eq]; exact c0 rfl
    · rw [sc_ne _ _ (by unfold scell; omega), c0' e]; exact a0
  · by_cases e : k = 1
    · subst e; rw [sc_eq]; exact c1 rfl
    · rw [sc_ne _ _ (by unfold scell; omega), c1' e]; exact a1
  · by_cases e : k = 2
    · subst e; rw [sc_eq]; exact c2 rfl
    · rw [sc_ne _ _ (by unfold scell; omega), c2' e]; exact a2

theorem getState_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (x : Ident) (hx : x ≠ "lk") (e1 e2 : Expr) (p1 p2 : Nat) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb) (fun _ => False)
      (fun σ d => e1.eval σ = BitVec.ofNat 32 p1 ∧ e2.eval σ = BitVec.ofNat 32 p2 ∧
        ∃ v, get_shared_mem_state_spec num_proc p1 p2 d = some v)
      (getStateS sb num_proc x e1 e2)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_shared_mem_state_spec num_proc p1 p2 d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  intro σ l b d hlk hcs hM ⟨he1, he2, v, hs⟩
  have hs0 := hs
  unfold get_shared_mem_state_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he : d.smspool p1 p2 with
    | SHRDUndef => rw [he] at hs; cases hs
    | SHRDValid i s va =>
      rw [he] at hs; simp only [Option.some.injEq] at hs
      obtain ⟨-, a1, -, -⟩ := sm_get hM.sp h1 h2 he
      have hr := smGet_run εR hL hcs hlk x he1 he2 h1 h2 (show 1 < 3 by decide)
      rw [a1, hs] at hr
      exact ⟨_, l, b, d, hr, hcs, hM, Locals.set_other _ _ (Ne.symm hx), fun _ _ => rfl, rfl, v, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem getSeen_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (x : Ident) (hx : x ≠ "lk") (e1 e2 : Expr) (p1 p2 : Nat) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb) (fun _ => False)
      (fun σ d => e1.eval σ = BitVec.ofNat 32 p1 ∧ e2.eval σ = BitVec.ofNat 32 p2 ∧
        ∃ v, get_shared_mem_seen_spec num_proc p1 p2 d = some v)
      (getSeenS sb num_proc x e1 e2)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_shared_mem_seen_spec num_proc p1 p2 d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  intro σ l b d hlk hcs hM ⟨he1, he2, v, hs⟩
  have hs0 := hs
  unfold get_shared_mem_seen_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he : d.smspool p1 p2 with
    | SHRDUndef => rw [he] at hs; cases hs
    | SHRDValid i s va =>
      rw [he] at hs; simp only [Option.some.injEq] at hs
      obtain ⟨-, -, a2, -⟩ := sm_get hM.sp h1 h2 he
      have hr := smGet_run εR hL hcs hlk x he1 he2 h1 h2 (show 2 < 3 by decide)
      rw [a2, hs] at hr
      exact ⟨_, l, b, d, hr, hcs, hM, Locals.set_other _ _ (Ne.symm hx), fun _ _ => rfl, rfl, v, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem getLoc_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (x : Ident) (hx : x ≠ "lk") (e1 e2 : Expr) (p1 p2 : Nat) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb) (fun _ => False)
      (fun σ d => e1.eval σ = BitVec.ofNat 32 p1 ∧ e2.eval σ = BitVec.ofNat 32 p2 ∧
        ∃ v, get_shared_mem_loc_spec num_proc p1 p2 d = some v)
      (getLocS sb num_proc x e1 e2)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_shared_mem_loc_spec num_proc p1 p2 d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  intro σ l b d hlk hcs hM ⟨he1, he2, v, hs⟩
  have hs0 := hs
  unfold get_shared_mem_loc_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he : d.smspool p1 p2 with
    | SHRDUndef => rw [he] at hs; cases hs
    | SHRDValid i s va =>
      rw [he] at hs; simp only [Option.some.injEq] at hs
      obtain ⟨a0, -, -, -⟩ := sm_get hM.sp h1 h2 he
      have hr := smGet_run εR hL hcs hlk x he1 he2 h1 h2 (show 0 < 3 by decide)
      rw [a0, hs] at hr
      exact ⟨_, l, b, d, hr, hcs, hM, Locals.set_other _ _ (Ne.symm hx), fun _ _ => rfl, rfl, v, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- A write to a word of entry `(p1, p2)` is inside the table. -/
theorem sm_foot {b : Region} {p1 p2 k : Nat} (h1 : p1 < num_proc) (h2 : p2 < num_proc) (hk : k < 3) (w : Val)
    (k' : Nat) (hk' : ¬ (sb ≤ k' ∧ k' < sb + 3 * (num_proc * num_proc))) :
    setCell b (scell sb num_proc p1 p2 k) w k' = b k' := by
  refine sc_ne _ _ (fun e => hk' ?_)
  subst e
  exact ⟨by unfold scell; omega, scell_lt h1 h2 hk⟩

theorem setState_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (e1 e2 ve : Expr) (p1 p2 nv : Nat) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb)
      (fun k => sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc))
      (fun σ d => e1.eval σ = BitVec.ofNat 32 p1 ∧ e2.eval σ = BitVec.ofNat 32 p2 ∧
        ve.eval σ = BitVec.ofNat 32 nv ∧ ∃ d1, set_shared_mem_state_spec num_proc p1 p2 nv d = some d1)
      (setStateS sb num_proc e1 e2 ve)
      (fun σ d σ' d' => set_shared_mem_state_spec num_proc p1 p2 nv d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨he1, he2, hve, d1, hs⟩
  have hs0 := hs
  unfold set_shared_mem_state_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he : d.smspool p1 p2 with
    | SHRDUndef => rw [he] at hs; cases hs
    | SHRDValid i s va =>
      cases hz : Z2SharedMemInfo nv with
      | none => rw [he, hz] at hs; cases hs
      | some i' =>
        rw [he, hz] at hs; simp only [Option.some.injEq] at hs
        obtain ⟨-, -, -, hva⟩ := sm_get hM.sp h1 h2 he
        obtain ⟨l', hr, hcs'⟩ := smSet_run εR hL hcs hlk he1 he2 h1 h2 (show 1 < 3 by decide) hve
        have hM' := sm_set1 hL hM h1 h2 he (show 1 < 3 by decide) (BitVec.ofNat 32 nv) (i' := i') (s' := s)
          (v' := va) hva (fun e => by cases e) (fun _ => rfl)
          (fun _ => by rw [Z2SharedMemInfo_correct hz]) (fun e => absurd rfl e)
          (fun e => by cases e) (fun _ => rfl)
        rw [hs] at hM'
        exact ⟨_, l', _, d1, hr, hcs', hM', Locals.set_other _ _ (by decide),
          sm_foot h1 h2 (by decide) _, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem setSeen_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (e1 e2 ve : Expr) (p1 p2 nv : Nat) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb)
      (fun k => sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc))
      (fun σ d => e1.eval σ = BitVec.ofNat 32 p1 ∧ e2.eval σ = BitVec.ofNat 32 p2 ∧
        ve.eval σ = BitVec.ofNat 32 nv ∧ ∃ d1, set_shared_mem_seen_spec num_proc p1 p2 nv d = some d1)
      (setSeenS sb num_proc e1 e2 ve)
      (fun σ d σ' d' => set_shared_mem_seen_spec num_proc p1 p2 nv d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨he1, he2, hve, d1, hs⟩
  have hs0 := hs
  unfold set_shared_mem_seen_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he : d.smspool p1 p2 with
    | SHRDUndef => rw [he] at hs; cases hs
    | SHRDValid i s va =>
      cases hz : ZtoBool nv with
      | none => rw [he, hz] at hs; cases hs
      | some s' =>
        rw [he, hz] at hs; simp only [Option.some.injEq] at hs
        obtain ⟨-, -, -, hva⟩ := sm_get hM.sp h1 h2 he
        obtain ⟨l', hr, hcs'⟩ := smSet_run εR hL hcs hlk he1 he2 h1 h2 (show 2 < 3 by decide) hve
        have hM' := sm_set1 hL hM h1 h2 he (show 2 < 3 by decide) (BitVec.ofNat 32 nv) (i' := i) (s' := s')
          (v' := va) hva (fun e => by cases e) (fun _ => rfl) (fun e => by cases e) (fun _ => rfl)
          (fun _ => by rcases zbool_cases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl) (fun e => absurd rfl e)
        rw [hs] at hM'
        exact ⟨_, l', _, d1, hr, hcs', hM', Locals.set_other _ _ (by decide),
          sm_foot h1 h2 (by decide) _, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- The location is a 32-bit value. -/
theorem setLoc_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (e1 e2 ve : Expr) (p1 p2 va' : Nat) (hva' : va' < 2 ^ 32) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb)
      (fun k => sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc))
      (fun σ d => e1.eval σ = BitVec.ofNat 32 p1 ∧ e2.eval σ = BitVec.ofNat 32 p2 ∧
        ve.eval σ = BitVec.ofNat 32 va' ∧ ∃ d1, set_shared_mem_loc_spec num_proc p1 p2 va' d = some d1)
      (setLocS sb num_proc e1 e2 ve)
      (fun σ d σ' d' => set_shared_mem_loc_spec num_proc p1 p2 va' d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨he1, he2, hve, d1, hs⟩
  have hs0 := hs
  unfold set_shared_mem_loc_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg num_proc p1 p2
  · rw [if_pos hc] at hs
    obtain ⟨-, -, h1, h2, -⟩ := hc
    cases he : d.smspool p1 p2 with
    | SHRDUndef => rw [he] at hs; cases hs
    | SHRDValid i s va =>
      rw [he] at hs; simp only [Option.some.injEq] at hs
      obtain ⟨l', hr, hcs'⟩ := smSet_run εR hL hcs hlk he1 he2 h1 h2 (show 0 < 3 by decide) hve
      have hM' := sm_set1 hL hM h1 h2 he (show 0 < 3 by decide) (BitVec.ofNat 32 va') (i' := i) (s' := s)
        (v' := va') hva' (fun _ => rfl) (fun e => absurd rfl e) (fun e => by cases e) (fun _ => rfl)
        (fun e => by cases e) (fun _ => rfl)
      rw [hs] at hM'
      exact ⟨_, l', _, d1, hr, hcs', hM', Locals.set_other _ _ (by decide),
        sm_foot h1 h2 (by decide) _, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- **Three writes to one entry**, in any order of the fields: the entry they
leave. The two process arguments are locals other than `_`. -/
theorem sm_write3 (εR : REnv) {c : CPU} {i0 : Nat} (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    {l : RLog} {b : Region} (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) {d : SData}
    (hM : MatchS maxpage num_id cb num_proc pb ib fb ida sb d b) {a1 a2 : Ident} (ha1 : a1 ≠ "_")
    (ha2 : a2 ≠ "_") {p1 p2 : Nat} (hp1 : σ a1 = BitVec.ofNat 32 p1) (hp2 : σ a2 = BitVec.ofNat 32 p2)
    (h1 : p1 < num_proc) (h2 : p2 < num_proc) {k1 k2 k3 : Nat} (hk1 : k1 < 3) (hk2 : k2 < 3) (hk3 : k3 < 3)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h23 : k2 ≠ k3) {v1 v2 v3 : Expr} {w1 w2 w3 : Val}
    (hw1 : v1.eval σ = w1) (hw2 : v2.eval (σ.set "_" 0) = w2) (hw3 : v3.eval (σ.set "_" 0) = w3)
    {i : SharedMemInfo} {s : Bool} {v : Nat} (hv : v < 2 ^ 32)
    (hval : ∀ k w, (k = k1 ∧ w = w1) ∨ (k = k2 ∧ w = w2) ∨ (k = k3 ∧ w = w3) →
      (k = 0 → w = BitVec.ofNat 32 v) ∧ (k = 1 → w = BitVec.ofNat 32 (SharedMemInfo2Z i)) ∧
      (k = 2 → w = BitVec.ofNat 32 (if s then 1 else 0))) :
    ∃ l' b', Runs (rprimsA εR c) (.seq (smSetS sb num_proc (.var a1) (.var a2) k1 v1)
        (.seq (smSetS sb num_proc (.var a1) (.var a2) k2 v2) (smSetS sb num_proc (.var a1) (.var a2) k3 v3)))
        σ l (σ.set "_" 0) l' ∧ CS1 c i0 l' b' ∧
      MatchS maxpage num_id cb num_proc pb ib fb ida sb
        { d with smspool := smSet d.smspool p1 p2 (.SHRDValid i s v) } b' ∧
      (∀ k, ¬ (sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc)) → b' k = b k) ∧
      ∀ (R : Stmt APrim) (τ : Locals) (lt : RLog), Runs (rprimsA εR c) R (σ.set "_" 0) l' τ lt →
        Runs (rprimsA εR c) (.seq (smSetS sb num_proc (.var a1) (.var a2) k1 v1)
          (.seq (smSetS sb num_proc (.var a1) (.var a2) k2 v2)
            (.seq (smSetS sb num_proc (.var a1) (.var a2) k3 v3) R))) σ l τ lt := by
  let σ1 := σ.set "_" 0
  have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
  have hq1 : (Expr.var a1).eval σ1 = BitVec.ofNat 32 p1 := (Locals.set_other _ _ ha1).trans hp1
  have hq2 : (Expr.var a2).eval σ1 = BitVec.ofNat 32 p2 := (Locals.set_other _ _ ha2).trans hp2
  have hss : σ1.set "_" 0 = σ1 := set_set _ _ _ _
  obtain ⟨l1, r1, c1⟩ := smSet_run εR hL hcs hlk (e1 := .var a1) (e2 := .var a2) (ve := v1) hp1 hp2 h1 h2 hk1 hw1
  obtain ⟨l2, r2, c2⟩ := smSet_run εR hL c1 hlk1 (e1 := .var a1) (e2 := .var a2) (ve := v2) hq1 hq2 h1 h2 hk2 hw2
  rw [hss] at r2
  obtain ⟨l3, r3, c3⟩ := smSet_run εR hL c2 hlk1 (e1 := .var a1) (e2 := .var a2) (ve := v3) hq1 hq2 h1 h2 hk3 hw3
  rw [hss] at r3
  have n12 : scell sb num_proc p1 p2 k1 ≠ scell sb num_proc p1 p2 k2 := by unfold scell; omega
  have n13 : scell sb num_proc p1 p2 k1 ≠ scell sb num_proc p1 p2 k3 := by unfold scell; omega
  have n23 : scell sb num_proc p1 p2 k2 ≠ scell sb num_proc p1 p2 k3 := by unfold scell; omega
  -- the value each of the three cells ends with
  have rd : ∀ k w, (k = k1 ∧ w = w1) ∨ (k = k2 ∧ w = w2) ∨ (k = k3 ∧ w = w3) →
      setCell (setCell (setCell b (scell sb num_proc p1 p2 k1) w1) (scell sb num_proc p1 p2 k2) w2)
        (scell sb num_proc p1 p2 k3) w3 (scell sb num_proc p1 p2 k) = w := by
    rintro k w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [sc_ne _ _ n13, sc_ne _ _ n12, sc_eq]
    · rw [sc_ne _ _ n23, sc_eq]
    · rw [sc_eq]
  -- each field is written by one of them
  have cover : ∀ k, k < 3 → ∃ w, (k = k1 ∧ w = w1) ∨ (k = k2 ∧ w = w2) ∨ (k = k3 ∧ w = w3) := by
    intro k hk
    by_cases e1 : k = k1
    · exact ⟨w1, Or.inl ⟨e1, rfl⟩⟩
    · by_cases e2 : k = k2
      · exact ⟨w2, Or.inr (Or.inl ⟨e2, rfl⟩)⟩
      · exact ⟨w3, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩
  refine ⟨l3, _, Runs.seq r1 (Runs.seq r2 r3), c3, sm_put hL hM h1 h2 hv (fun k hk => ?_) ?_ ?_ ?_,
    fun k hk => ?_, fun R τ lt hR => Runs.seq r1 (Runs.seq r2 (Runs.seq r3 hR))⟩
  · rw [sc_ne _ _ (by unfold scell at *; omega), sc_ne _ _ (by unfold scell at *; omega),
      sc_ne _ _ (by unfold scell at *; omega)]
  · obtain ⟨w, hw⟩ := cover 0 (by decide)
    rw [rd 0 w hw]; exact (hval 0 w hw).1 rfl
  · obtain ⟨w, hw⟩ := cover 1 (by decide)
    rw [rd 1 w hw]; exact (hval 1 w hw).2.1 rfl
  · obtain ⟨w, hw⟩ := cover 2 (by decide)
    rw [rd 2 w hw]; exact (hval 2 w hw).2.2 rfl
  · rw [sm_foot h1 h2 hk3 _ k hk, sm_foot h1 h2 hk2 _ k hk, sm_foot h1 h2 hk1 _ k hk]

/-- **`clear_shared_mem` refines `clear_shared_mem_spec`.** -/
theorem clear_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (a1 a2 : Ident) (ha1 : a1 ≠ "_") (ha2 : a2 ≠ "_") (p1 p2 : Nat) :
    Triple εR c i0 (MatchS maxpage num_id cb num_proc pb ib fb ida sb)
      (fun k => sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc))
      (fun σ d => σ a1 = BitVec.ofNat 32 p1 ∧ σ a2 = BitVec.ofNat 32 p2 ∧
        ∃ d1, clear_shared_mem_spec num_proc p1 p2 d = some d1)
      (clearS sb num_proc (.var a1) (.var a2))
      (fun σ d σ' d' => clear_shared_mem_spec num_proc p1 p2 d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨hp1, hp2, d1, hs⟩
  have hs0 := hs
  unfold clear_shared_mem_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ shared_mem_arg' num_proc p1 p2
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    obtain ⟨-, -, h1, h2⟩ := hc
    obtain ⟨l', b', hr, hcs', hM', hf, -⟩ := sm_write3 εR hL hcs hlk hM ha1 ha2 hp1 hp2 h1 h2
      (k1 := 0) (k2 := 1) (k3 := 2) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (v1 := .const 0) (v2 := .const 2) (v3 := .const 1) (w1 := BitVec.ofNat 32 0) (w2 := BitVec.ofNat 32 2)
      (w3 := BitVec.ofNat 32 1) rfl rfl rfl (i := .SHRDDEAD) (s := true) (v := 0) (by decide)
      (by
        rintro k w (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨fun _ => rfl, (fun e => by cases e), (fun e => by cases e)⟩
        · exact ⟨(fun e => by cases e), fun _ => rfl, (fun e => by cases e)⟩
        · exact ⟨(fun e => by cases e), (fun e => by cases e), fun _ => rfl⟩)
    rw [hs] at hM'
    exact ⟨_, l', b', d1, hr, hcs', hM', Locals.set_other _ _ (by decide), hf, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

end Triples

end MShare
