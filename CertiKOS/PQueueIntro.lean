import CertiKOS.PThreadIntro
import CertiKOS.LayerStep

/-!
# mCertiKOS `PQueueIntro`: the thread queues, ported

Threads wait in queues: one per channel and one of ready threads. A queue is
a head and a tail; the links between its threads are the `prev` and `next`
of their control blocks (`PThreadIntro.lean`).

Ported from `layerlib/AuxStateDataType.v`: `TDQueue`, `TDQueuePool`.

Ported from `objects/ObjQueue.v`: `get_head_spec`, `get_tail_spec`,
`set_head_spec`, `set_tail_spec`, `tdq_init_spec`. Ported from
`clib/CalRealProcModule.v`: `real_tdq`. Ported from `proc/PQueueIntro.v`:
`tdqueue_init_spec`.

Ported from `proc/QueueIntroGenDef.v`: `match_TDQ`, `match_TDQPool`
(`MatchTDQ`, `MatchQP`).

Ported from `proc/PThreadInitCSource.v`: the C code of `get_head`,
`get_tail`, `set_head`, `set_tail`, `tdq_init`. From
`proc/PQueueIntroCSource.v`: the loop of `tdqueue_init`.

* `getHead_triple` … `tdqInit_triple`: each accessor refines its
  specification.
* `tdqueueInit_triple`: the loop of `tdqueue_init` gives `real_tdq`.
* `liftT`: every primitive of the layers below keeps its interface in the
  state with the queues, if it does not write the queue pool.

The file also states the layer's primitives as steps (`LayerStep.lean`):
`getPrevQ`, `setNextQ`, `getTailQ`, `setHeadQ`, and so on. The queue
operations of `PQueueInit.lean` are run through these.

What differs: the queue pool is in the memory-management region, after the
control blocks (`QLayout`), two cells per queue. `tdqueue_init` first calls
`thread_init`, which reaches `pmap_init` (machine model), so
`tdqueue_init_spec` is stated and only its loop is verified.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PQueue

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval while_inv)

/-! ## Abstract data (`AuxStateDataType.v`) -/

/-- `TDQValid head tail`. -/
inductive TDQueue
  | TDQUndef
  | TDQValid (head tail : Nat)

abbrev TDQueuePool := Nat → TDQueue

/-- `TData` with the thread queues. -/
structure QData extends TData where
  tdq : TDQueuePool

/-! ## Specifications (`ObjQueue.v`) -/

section Specs
variable (num_chan : Nat)

def get_head_spec (n : Nat) (d : QData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan then
    match d.tdq n with
    | .TDQValid h _ => some h
    | .TDQUndef => none
  else none

def get_tail_spec (n : Nat) (d : QData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan then
    match d.tdq n with
    | .TDQValid _ t => some t
    | .TDQUndef => none
  else none

def set_head_spec (n s : Nat) (d : QData) : Option QData :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan then
    match d.tdq n with
    | .TDQValid _ t => some { d with tdq := setAt d.tdq n (.TDQValid s t) }
    | .TDQUndef => none
  else none

def set_tail_spec (n s : Nat) (d : QData) : Option QData :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan then
    match d.tdq n with
    | .TDQValid h _ => some { d with tdq := setAt d.tdq n (.TDQValid h s) }
    | .TDQUndef => none
  else none

/-- An empty queue. `num_proc` stands for "none". -/
def tdq_init_spec (num_proc n : Nat) (d : QData) : Option QData :=
  if d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan then
    some { d with tdq := setAt d.tdq n (.TDQValid num_proc num_proc) }
  else none

end Specs

/-- `real_tdq`: queues `0 … num_chan` empty. -/
def real_tdq (num_proc num_chan : Nat) (q : TDQueuePool) : TDQueuePool :=
  init_zmap (num_chan + 1) (.TDQValid num_proc num_proc) q

/-- **`tdqueue_init_spec`** (`PQueueIntro.v`). -/
def tdqueue_init_spec (num_proc num_chan kl kh : Nat) (mm : MALInit.MMTable) (size : Nat) (d : QData) :
    Option QData :=
  match thread_init_spec num_proc kl kh mm size d.toTData with
  | some t => some { toTData := t, tdq := real_tdq num_proc num_chan d.tdq }
  | none => none

/-! ## The queues in the region (`QueueIntroGenDef.v`) -/

/-- Cell `k` of queue `n`: 0 head, 1 tail. -/
def qcell (qb n k : Nat) : Nat := qb + n * 2 + k

/-- `match_TDQ`. -/
def MatchTDQ : TDQueue → Val → Val → Prop
  | .TDQUndef, _, _ => True
  | .TDQValid h t, v1, v2 => h = v1.toNat ∧ t = v2.toNat

/-- `match_TDQPool`. -/
def MatchQP (num_chan qb : Nat) (q : TDQueuePool) (b : Region) : Prop :=
  ∀ i, i ≤ num_chan → MatchTDQ (q i) (b (qcell qb i 0)) (b (qcell qb i 1))

/-- The layout with the queue pool after the control blocks. -/
structure QLayout (maxpage num_id cb num_proc pb ib fb sb tb num_chan qb : Nat) : Prop where
  tlay : TLayout maxpage num_id cb num_proc pb ib fb sb tb
  hqb : tb + 3 * num_proc ≤ qb
  hqe : qb + 2 * (num_chan + 1) ≤ pb

structure MatchQ (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb : Nat) (d : QData) (b : Region) :
    Prop where
  t : MatchT maxpage num_id cb num_proc pb ib fb ida sb tb d.toTData b
  qp : MatchQP num_chan qb d.tdq b

section Region
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb : Nat}

/-- What the two words of a valid queue are. -/
theorem tdq_get {q : TDQueuePool} {b : Region} (hM : MatchQP num_chan qb q b) {i : Nat} (hi : i ≤ num_chan)
    {h t : Nat} (he : q i = .TDQValid h t) :
    b (qcell qb i 0) = BitVec.ofNat 32 h ∧ b (qcell qb i 1) = BitVec.ofNat 32 t ∧ h < 2 ^ 32 ∧ t < 2 ^ 32 := by
  have hm := hM i hi
  rw [he] at hm
  obtain ⟨a1, a2⟩ := hm
  have hh : h < 2 ^ 32 := by rw [a1]; exact (b (qcell qb i 0)).isLt
  have ht : t < 2 ^ 32 := by rw [a2]; exact (b (qcell qb i 1)).isLt
  exact ⟨val_of_toNat a1.symm hh, val_of_toNat a2.symm ht, hh, ht⟩

/-- **Rewriting a queue.** -/
theorem tdq_put (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {d : QData} {b b' : Region}
    (hM : MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb d b) {i : Nat} (hi : i ≤ num_chan)
    {h t : Nat} (hh : h < 2 ^ 32) (ht : t < 2 ^ 32)
    (hfr : ∀ k, k < qcell qb i 0 ∨ qcell qb i 1 < k → b' k = b k)
    (e0 : b' (qcell qb i 0) = BitVec.ofNat 32 h) (e1 : b' (qcell qb i 1) = BitVec.ofNat 32 t) :
    MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb
      { d with tdq := setAt d.tdq i (.TDQValid h t) } b' := by
  have := hL.hqb; have := hL.hqe
  refine ⟨matchT_frame hL.tlay hM.t (fun k hk => hfr k (by unfold qcell; omega)), fun j hj => ?_⟩
  show MatchTDQ (setAt d.tdq i (.TDQValid h t) j) _ _
  by_cases e : j = i
  · subst e
    rw [setAt_eq, e0, e1]
    exact ⟨(tn hh).symm, (tn ht).symm⟩
  · rw [setAt_ne _ _ e, hfr _ (by unfold qcell; omega), hfr _ (by unfold qcell; omega)]
    exact hM.qp j hj

/-- One word of a valid queue is overwritten. -/
theorem tdq_set1 (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {d : QData} {b : Region}
    (hM : MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb d b) {i : Nat} (hi : i ≤ num_chan)
    {h t : Nat} (he : d.tdq i = .TDQValid h t) {k : Nat} (hk : k < 2) (w : Val) {h' t' : Nat}
    (hh' : h' < 2 ^ 32) (ht' : t' < 2 ^ 32)
    (c0 : k = 0 → w = BitVec.ofNat 32 h') (c0' : k ≠ 0 → h' = h)
    (c1 : k = 1 → w = BitVec.ofNat 32 t') (c1' : k ≠ 1 → t' = t) :
    MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb
      { d with tdq := setAt d.tdq i (.TDQValid h' t') } (setCell b (qcell qb i k) w) := by
  obtain ⟨a0, a1, -, -⟩ := tdq_get hM.qp hi he
  refine tdq_put hL hM hi hh' ht' (fun k' hk' => sc_ne _ _ (by unfold qcell at *; omega)) ?_ ?_
  · by_cases e : k = 0
    · subst e; rw [sc_eq]; exact c0 rfl
    · rw [sc_ne _ _ (by unfold qcell; omega), c0' e]; exact a0
  · by_cases e : k = 1
    · subst e; rw [sc_eq]; exact c1 rfl
    · rw [sc_ne _ _ (by unfold qcell; omega), c1' e]; exact a1

/-- A write to a word of queue `i` is inside the pool. -/
theorem tdq_foot {b : Region} {i k : Nat} (hi : i ≤ num_chan) (hk : k < 2) (w : Val) (k' : Nat)
    (hk' : ¬ (qb ≤ k' ∧ k' < qb + 2 * (num_chan + 1))) : setCell b (qcell qb i k) w k' = b k' := by
  refine sc_ne _ _ (fun e => hk' ?_)
  subst e
  unfold qcell; omega

/-- A write to a control block leaves the queues alone. -/
theorem tcbQ_set1 (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {d : QData} {b : Region}
    (hM : MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb d b) {i : Nat} (hi : i < num_proc)
    {ts : ThreadState} {p nx : Nat} (he : d.tcb i = .TCBValid ts p nx) {k : Nat} (hk : k < 3) (w : Val)
    {ts' : ThreadState} {p' nx' : Nat} (hp' : p' < 2 ^ 32) (hnx' : nx' < 2 ^ 32)
    (c0 : k = 0 → w = BitVec.ofNat 32 (ThreadStatetoZ ts')) (c0' : k ≠ 0 → ts' = ts)
    (c1 : k = 1 → w = BitVec.ofNat 32 p') (c1' : k ≠ 1 → p' = p)
    (c2 : k = 2 → w = BitVec.ofNat 32 nx') (c2' : k ≠ 2 → nx' = nx) :
    MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb
      { d with tcb := setAt d.tcb i (.TCBValid ts' p' nx') } (setCell b (tcell tb i k) w) := by
  have := hL.hqb
  refine ⟨tcb_set1 hL.tlay hM.t hi he hk w hp' hnx' c0 c0' c1 c1' c2 c2', fun j hj => ?_⟩
  show MatchTDQ (d.tdq j) _ _
  rw [sc_ne _ _ (by unfold tcell qcell; omega), sc_ne _ _ (by unfold tcell qcell; omega)]
  exact hM.qp j hj

end Region

/-! ## The C code (`PThreadInitCSource.v`) -/

/-- `&TDQPool_LOC[e]`, field `k`. -/
def tdqE (qb : Nat) (ie : Expr) (k : Nat) : Expr :=
  .bin .add (.const (BitVec.ofNat 32 (qb + k))) (.bin .mul ie (.const 2))

theorem tdq_eval {qb n : Nat} (hend : qb + 2 * n ≤ 2 ^ 32) {σ : Locals} {ie : Expr} {i k : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < n) (hk : k < 2) :
    ((tdqE qb ie k).eval σ).toNat = qcell qb i k := by
  have e : (tdqE qb ie k).eval σ = BitVec.ofNat 32 (qb + k) + ie.eval σ * (2 : Val) := rfl
  rw [e, he, show (2 : Val) = BitVec.ofNat 32 2 from rfl, ← BitVec.ofNat_mul, ← BitVec.ofNat_add,
    tn (by omega)]
  unfold qcell; omega

def qGetS (qb : Nat) (x : Ident) (ie : Expr) (k : Nat) : Stmt APrim := .call x .pull [lkE, tdqE qb ie k]
def qSetS (qb : Nat) (ie : Expr) (k : Nat) (ve : Expr) : Stmt APrim := .call "_" .push [lkE, tdqE qb ie k, ve]

/-- `x = get_head(e)`: `return TDQPool_LOC[e].head;` -/
def getHeadS (qb : Nat) (x : Ident) (ie : Expr) : Stmt APrim := qGetS qb x ie 0
/-- `x = get_tail(e)` -/
def getTailS (qb : Nat) (x : Ident) (ie : Expr) : Stmt APrim := qGetS qb x ie 1
/-- `set_head(e, v)`: `TDQPool_LOC[e].head = v;` -/
def setHeadS (qb : Nat) (ie ve : Expr) : Stmt APrim := qSetS qb ie 0 ve
/-- `set_tail(e, v)` -/
def setTailS (qb : Nat) (ie ve : Expr) : Stmt APrim := qSetS qb ie 1 ve

/-- `tdq_init(e)`: `.head = num_proc; .tail = num_proc;` -/
def tdqInitS (qb num_proc : Nat) (ie : Expr) : Stmt APrim :=
  .seq (setHeadS qb ie (.const (BitVec.ofNat 32 num_proc))) (setTailS qb ie (.const (BitVec.ofNat 32 num_proc)))

/-- The cells of the queue pool. -/
def QF (qb num_chan : Nat) (k : Nat) : Prop := qb ≤ k ∧ k < qb + 2 * (num_chan + 1)

/-- The cells of the control blocks. -/
def TF (tb num_proc : Nat) (k : Nat) : Prop := tb ≤ k ∧ k < tb + 3 * num_proc

section Steps
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb : Nat}

theorem qGet_run (εR : REnv) {c : CPU} {i0 : Nat}
    (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {l : RLog} {b : Region}
    (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) (x : Ident) {ie : Expr} {i k : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i ≤ num_chan) (hk : k < 2) :
    Runs (rprimsA εR c) (qGetS qb x ie k) σ l (σ.set x (b (qcell qb i k))) l := by
  have := hL.hqe; have := hL.tlay.slay.lay.hib; have := hL.tlay.slay.lay.hfb; have := hL.tlay.slay.lay.hend
  exact rd_run (εR := εR) hcs hlk x _ (tdq_eval (n := num_chan + 1) (by omega) he (by omega) hk)

theorem qSet_run (εR : REnv) {c : CPU} {i0 : Nat}
    (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) {l : RLog} {b : Region}
    (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) {ie ve : Expr} {i k : Nat} {w : Val}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i ≤ num_chan) (hk : k < 2) (hw : ve.eval σ = w) :
    ∃ l', Runs (rprimsA εR c) (qSetS qb ie k ve) σ l (σ.set "_" 0) l' ∧
      CS1 c i0 l' (setCell b (qcell qb i k) w) := by
  have := hL.hqe; have := hL.tlay.slay.lay.hib; have := hL.tlay.slay.lay.hfb; have := hL.tlay.slay.lay.hend
  exact wr_run (εR := εR) hcs hlk _ ve (tdq_eval (n := num_chan + 1) (by omega) he (by omega) hk) hw

variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MQ" => MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb

/-! ### The control blocks, as steps -/

theorem getTStateQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (x : Ident)
    (hx : x ≠ "lk") {ie : Expr} {σ : Locals} {d : QData} {i : Nat} {ts : ThreadState} {p nx : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < num_proc) (ht : d.tcb i = .TCBValid ts p nx) :
    Step εR c i0 MQ F (getTStateS tb x ie) σ d (σ.set x (BitVec.ofNat 32 (ThreadStatetoZ ts))) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  obtain ⟨a0, -, -, -, -⟩ := tcb_get hM.t.tp hi ht
  have hr := tGet_run εR hL.tlay hcs hlk x he hi (show 0 < 3 by decide)
  rw [a0] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem getPrevQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (x : Ident)
    (hx : x ≠ "lk") {ie : Expr} {σ : Locals} {d : QData} {i : Nat} {ts : ThreadState} {p nx : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < num_proc) (ht : d.tcb i = .TCBValid ts p nx) :
    Step εR c i0 MQ F (getPrevS tb x ie) σ d (σ.set x (BitVec.ofNat 32 p)) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  obtain ⟨-, a1, -, -, -⟩ := tcb_get hM.t.tp hi ht
  have hr := tGet_run εR hL.tlay hcs hlk x he hi (show 1 < 3 by decide)
  rw [a1] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem getNextQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (x : Ident)
    (hx : x ≠ "lk") {ie : Expr} {σ : Locals} {d : QData} {i : Nat} {ts : ThreadState} {p nx : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < num_proc) (ht : d.tcb i = .TCBValid ts p nx) :
    Step εR c i0 MQ F (getNextS tb x ie) σ d (σ.set x (BitVec.ofNat 32 nx)) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  obtain ⟨-, -, a2, -, -⟩ := tcb_get hM.t.tp hi ht
  have hr := tGet_run εR hL.tlay hcs hlk x he hi (show 2 < 3 by decide)
  rw [a2] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem setTStateQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb)
    (hF : ∀ k, TF tb num_proc k → F k) {ie ve : Expr} {σ : Locals} {d : QData} {i sv : Nat}
    {ts ts' : ThreadState} {p nx : Nat} (he : ie.eval σ = BitVec.ofNat 32 i)
    (hve : ve.eval σ = BitVec.ofNat 32 sv) (hi : i < num_proc) (hsv : ZtoThreadState sv = some ts')
    (ht : d.tcb i = .TCBValid ts p nx) :
    Step εR c i0 MQ F (setTStateS tb ie ve) σ d (σ.set "_" 0)
      { d with tcb := setAt d.tcb i (.TCBValid ts' p nx) } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨-, -, -, hp, hnx⟩ := tcb_get hM.t.tp hi ht
  obtain ⟨l', hr, hcs'⟩ := tSet_run εR hL.tlay hcs hlk he hi (show 0 < 3 by decide) hve
  exact ⟨l', _, hr, hcs', tcbQ_set1 hL hM hi ht (show 0 < 3 by decide) _ hp hnx
      (fun _ => by rw [ZtoThreadState_correct hsv]) (fun e => absurd rfl e) (fun e => by cases e)
      (fun _ => rfl) (fun e => by cases e) (fun _ => rfl),
    fun k hk => tcb_foot hi (by decide) _ k (fun h => hk (hF k h))⟩

theorem setPrevQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb)
    (hF : ∀ k, TF tb num_proc k → F k) {ie ve : Expr} {σ : Locals} {d : QData} {i sv : Nat}
    {ts : ThreadState} {p nx : Nat} (he : ie.eval σ = BitVec.ofNat 32 i)
    (hve : ve.eval σ = BitVec.ofNat 32 sv) (hi : i < num_proc) (hsv : sv < 2 ^ 32)
    (ht : d.tcb i = .TCBValid ts p nx) :
    Step εR c i0 MQ F (setPrevS tb ie ve) σ d (σ.set "_" 0)
      { d with tcb := setAt d.tcb i (.TCBValid ts sv nx) } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨-, -, -, hp, hnx⟩ := tcb_get hM.t.tp hi ht
  obtain ⟨l', hr, hcs'⟩ := tSet_run εR hL.tlay hcs hlk he hi (show 1 < 3 by decide) hve
  exact ⟨l', _, hr, hcs', tcbQ_set1 hL hM hi ht (show 1 < 3 by decide) _ hsv hnx
      (fun e => by cases e) (fun _ => rfl) (fun _ => rfl) (fun e => absurd rfl e) (fun e => by cases e)
      (fun _ => rfl),
    fun k hk => tcb_foot hi (by decide) _ k (fun h => hk (hF k h))⟩

theorem setNextQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb)
    (hF : ∀ k, TF tb num_proc k → F k) {ie ve : Expr} {σ : Locals} {d : QData} {i sv : Nat}
    {ts : ThreadState} {p nx : Nat} (he : ie.eval σ = BitVec.ofNat 32 i)
    (hve : ve.eval σ = BitVec.ofNat 32 sv) (hi : i < num_proc) (hsv : sv < 2 ^ 32)
    (ht : d.tcb i = .TCBValid ts p nx) :
    Step εR c i0 MQ F (setNextS tb ie ve) σ d (σ.set "_" 0)
      { d with tcb := setAt d.tcb i (.TCBValid ts p sv) } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨-, -, -, hp, hnx⟩ := tcb_get hM.t.tp hi ht
  obtain ⟨l', hr, hcs'⟩ := tSet_run εR hL.tlay hcs hlk he hi (show 2 < 3 by decide) hve
  exact ⟨l', _, hr, hcs', tcbQ_set1 hL hM hi ht (show 2 < 3 by decide) _ hp hsv
      (fun e => by cases e) (fun _ => rfl) (fun e => by cases e) (fun _ => rfl) (fun _ => rfl)
      (fun e => absurd rfl e),
    fun k hk => tcb_foot hi (by decide) _ k (fun h => hk (hF k h))⟩

/-! ### The queues, as steps -/

theorem getHeadQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (x : Ident)
    (hx : x ≠ "lk") {ie : Expr} {σ : Locals} {d : QData} {n h t : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 n) (hn : n ≤ num_chan) (hq : d.tdq n = .TDQValid h t) :
    Step εR c i0 MQ F (getHeadS qb x ie) σ d (σ.set x (BitVec.ofNat 32 h)) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  obtain ⟨a0, -, -, -⟩ := tdq_get hM.qp hn hq
  have hr := qGet_run εR hL hcs hlk x he hn (show 0 < 2 by decide)
  rw [a0] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem getTailQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (x : Ident)
    (hx : x ≠ "lk") {ie : Expr} {σ : Locals} {d : QData} {n h t : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 n) (hn : n ≤ num_chan) (hq : d.tdq n = .TDQValid h t) :
    Step εR c i0 MQ F (getTailS qb x ie) σ d (σ.set x (BitVec.ofNat 32 t)) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  obtain ⟨-, a1, -, -⟩ := tdq_get hM.qp hn hq
  have hr := qGet_run εR hL hcs hlk x he hn (show 1 < 2 by decide)
  rw [a1] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

theorem setHeadQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb)
    (hF : ∀ k, QF qb num_chan k → F k) {ie ve : Expr} {σ : Locals} {d : QData} {n sv h t : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 n) (hve : ve.eval σ = BitVec.ofNat 32 sv) (hn : n ≤ num_chan)
    (hsv : sv < 2 ^ 32) (hq : d.tdq n = .TDQValid h t) :
    Step εR c i0 MQ F (setHeadS qb ie ve) σ d (σ.set "_" 0)
      { d with tdq := setAt d.tdq n (.TDQValid sv t) } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨-, -, hh, ht⟩ := tdq_get hM.qp hn hq
  obtain ⟨l', hr, hcs'⟩ := qSet_run εR hL hcs hlk he hn (show 0 < 2 by decide) hve
  exact ⟨l', _, hr, hcs', tdq_set1 hL hM hn hq (show 0 < 2 by decide) _ hsv ht
      (fun _ => rfl) (fun e => absurd rfl e) (fun e => by cases e) (fun _ => rfl),
    fun k hk => tdq_foot hn (by decide) _ k (fun h => hk (hF k h))⟩

theorem setTailQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb)
    (hF : ∀ k, QF qb num_chan k → F k) {ie ve : Expr} {σ : Locals} {d : QData} {n sv h t : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 n) (hve : ve.eval σ = BitVec.ofNat 32 sv) (hn : n ≤ num_chan)
    (hsv : sv < 2 ^ 32) (hq : d.tdq n = .TDQValid h t) :
    Step εR c i0 MQ F (setTailS qb ie ve) σ d (σ.set "_" 0)
      { d with tdq := setAt d.tdq n (.TDQValid h sv) } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨-, -, hh, ht⟩ := tdq_get hM.qp hn hq
  obtain ⟨l', hr, hcs'⟩ := qSet_run εR hL hcs hlk he hn (show 1 < 2 by decide) hve
  exact ⟨l', _, hr, hcs', tdq_set1 hL hM hn hq (show 1 < 2 by decide) _ hh hsv
      (fun e => by cases e) (fun _ => rfl) (fun _ => rfl) (fun e => absurd rfl e),
    fun k hk => tdq_foot hn (by decide) _ k (fun h => hk (hF k h))⟩

/-- `tdq_init`: the queue need not be valid before. The argument is a local
other than `_`. -/
theorem tdqInitQ (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb)
    (hF : ∀ k, QF qb num_chan k → F k) (a : Ident) (ha : a ≠ "_") {σ : Locals} {d : QData} {n : Nat}
    (hp : σ a = BitVec.ofNat 32 n) (hn : n ≤ num_chan) :
    Step εR c i0 MQ F (tdqInitS qb num_proc (.var a)) σ d (σ.set "_" 0)
      { d with tdq := setAt d.tdq n (.TDQValid num_proc num_proc) } := by
  have hnp : num_proc < 2 ^ 32 := by
    have := hL.tlay.hte; have := hL.tlay.slay.lay.hib; have := hL.tlay.slay.lay.hfb
    have := hL.tlay.slay.lay.hend; omega
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  let σ1 := σ.set "_" 0
  have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
  have hq : (Expr.var a).eval σ1 = BitVec.ofNat 32 n := (Locals.set_other _ _ ha).trans hp
  have hss : σ1.set "_" 0 = σ1 := set_set _ _ _ _
  obtain ⟨l1, r1, c1⟩ := qSet_run εR hL hcs hlk (ie := .var a) (ve := .const (BitVec.ofNat 32 num_proc))
    (w := BitVec.ofNat 32 num_proc) hp hn (show 0 < 2 by decide) rfl
  obtain ⟨l2, r2, c2⟩ := qSet_run εR hL c1 hlk1 (ie := .var a) (ve := .const (BitVec.ofNat 32 num_proc))
    (w := BitVec.ofNat 32 num_proc) hq hn (show 1 < 2 by decide) rfl
  rw [hss] at r2
  refine ⟨l2, _, Runs.seq r1 r2, c2, tdq_put hL hM hn hnp hnp (fun k hk => ?_) ?_ ?_, fun k hk => ?_⟩
  · rw [sc_ne _ _ (by unfold qcell at *; omega), sc_ne _ _ (by unfold qcell at *; omega)]
  · rw [sc_ne _ _ (by unfold qcell; omega), sc_eq]
  · rw [sc_eq]
  · rw [tdq_foot hn (by decide) _ k (fun h => hk (hF k h)), tdq_foot hn (by decide) _ k (fun h => hk (hF k h))]

/-! ### Each accessor refines its specification -/

theorem getHead_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (x : Ident)
    (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 MQ (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_head_spec num_chan n d = some v)
      (getHeadS qb x ie)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_head_spec num_chan n d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  refine Step.triple (fun σ d ⟨he, v, hs⟩ => ?_)
  have hs0 := hs
  unfold get_head_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan
  · rw [if_pos hc] at hs
    cases hq : d.tdq n with
    | TDQUndef => rw [hq] at hs; cases hs
    | TDQValid h t =>
      rw [hq] at hs; simp only [Option.some.injEq] at hs; subst hs
      exact ⟨_, d, getHeadQ εR c i0 hL x hx he hc.2.2 hq, rfl, _, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem getTail_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (x : Ident)
    (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 MQ (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_tail_spec num_chan n d = some v)
      (getTailS qb x ie)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_tail_spec num_chan n d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  refine Step.triple (fun σ d ⟨he, v, hs⟩ => ?_)
  have hs0 := hs
  unfold get_tail_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan
  · rw [if_pos hc] at hs
    cases hq : d.tdq n with
    | TDQUndef => rw [hq] at hs; cases hs
    | TDQValid h t =>
      rw [hq] at hs; simp only [Option.some.injEq] at hs; subst hs
      exact ⟨_, d, getTailQ εR c i0 hL x hx he hc.2.2 hq, rfl, _, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- The value written is a machine word, as every C argument is. -/
theorem setHead_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (ie ve : Expr)
    (n sv : Nat) :
    Triple εR c i0 MQ (QF qb num_chan)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧ sv < 2 ^ 32 ∧
        ∃ d1, set_head_spec num_chan n sv d = some d1)
      (setHeadS qb ie ve)
      (fun σ d σ' d' => set_head_spec num_chan n sv d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨he, hve, hsv, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold set_head_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan
  · rw [if_pos hc] at hs
    cases hq : d.tdq n with
    | TDQUndef => rw [hq] at hs; cases hs
    | TDQValid h t =>
      rw [hq] at hs; simp only [Option.some.injEq] at hs; subst hs
      exact ⟨_, _, setHeadQ εR c i0 hL (fun _ h => h) he hve hc.2.2 hsv hq, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem setTail_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (ie ve : Expr)
    (n sv : Nat) :
    Triple εR c i0 MQ (QF qb num_chan)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧ sv < 2 ^ 32 ∧
        ∃ d1, set_tail_spec num_chan n sv d = some d1)
      (setTailS qb ie ve)
      (fun σ d σ' d' => set_tail_spec num_chan n sv d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨he, hve, hsv, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold set_tail_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan
  · rw [if_pos hc] at hs
    cases hq : d.tdq n with
    | TDQUndef => rw [hq] at hs; cases hs
    | TDQValid h t =>
      rw [hq] at hs; simp only [Option.some.injEq] at hs; subst hs
      exact ⟨_, _, setTailQ εR c i0 hL (fun _ h => h) he hve hc.2.2 hsv hq, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- **`tdq_init` refines `tdq_init_spec`.** -/
theorem tdqInit_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) (a : Ident)
    (ha : a ≠ "_") (n : Nat) :
    Triple εR c i0 MQ (QF qb num_chan)
      (fun σ d => σ a = BitVec.ofNat 32 n ∧ ∃ d1, tdq_init_spec num_chan num_proc n d = some d1)
      (tdqInitS qb num_proc (.var a))
      (fun σ d σ' d' => tdq_init_spec num_chan num_proc n d = some d' ∧ σ' = σ.set "_" 0) := by
  refine Step.triple (fun σ d ⟨hp, d1, hs⟩ => ?_)
  have hs0 := hs
  unfold tdq_init_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n ≤ num_chan
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs; subst hs
    exact ⟨_, _, tdqInitQ εR c i0 hL (fun _ h => h) a ha hp hc.2.2, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-! ## `tdqueue_init`'s loop (`PQueueIntroCSource.v`) -/

/-- `i = 0; while (i < num_chan + 1) { tdq_init(i); i++; }` -/
def tdqInitLoop (qb num_proc num_chan : Nat) : Stmt APrim :=
  .seq (.assign "i" (.const 0))
    (.while (.bin .ltu (.var "i") (.const (BitVec.ofNat 32 (num_chan + 1))))
      (.seq (tdqInitS qb num_proc (.var "i")) (.assign "i" (.bin .add (.var "i") (.const 1)))))

/-- **The loop of `tdqueue_init` empties every queue** (`real_tdq`). -/
theorem tdqueueInit_step (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb)
    (hF : ∀ k, QF qb num_chan k → F k) (σ : Locals) (d : QData) :
    ∃ σ', Step εR c i0 MQ F (tdqInitLoop qb num_proc num_chan) σ d σ'
      { d with tdq := real_tdq num_proc num_chan d.tdq } := by
  have hnc : num_chan + 1 < 2 ^ 32 := by
    have := hL.hqe; have := hL.tlay.slay.lay.hib; have := hL.tlay.slay.lay.hfb
    have := hL.tlay.slay.lay.hend; omega
  let x0 : TDQueue := .TDQValid num_proc num_proc
  let I : Locals → QData → Prop := fun τ e => ∃ m, m ≤ num_chan + 1 ∧ τ "i" = BitVec.ofNat 32 m ∧
    e = { d with tdq := init_zmap m x0 d.tdq }
  have hbody : ∀ τ e, I τ e →
      ¬ (Expr.bin .ltu (.var "i") (.const (BitVec.ofNat 32 (num_chan + 1)))).eval τ = 0 →
      ∃ τ' e', Step εR c i0 MQ F (.seq (tdqInitS qb num_proc (.var "i"))
          (.assign "i" (.bin .add (.var "i") (.const 1)))) τ e τ' e' ∧ I τ' e' ∧
        num_chan + 1 - (τ' "i").toNat < num_chan + 1 - (τ "i").toNat := by
    rintro τ e ⟨m, hm, hiτ, rfl⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .const (BitVec.ofNat 32 (num_chan + 1))) hiτ rfl
      (by omega) hnc] at hg
    have hmlt : m < num_chan + 1 := by
      by_cases h : m < num_chan + 1
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    refine ⟨_, _, (tdqInitQ εR c i0 hL hF "i" (by decide) hiτ (by omega)).seq
      (Step.assign' "i" (by decide) _ (inc_eval (m := m)
        (by rw [Locals.set_other _ _ (by decide)]; exact hiτ))), ⟨m + 1, hmlt, by simp, rfl⟩, ?_⟩
    rw [Locals.set_same, hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', e', hr, ⟨m, hm, hi', rfl⟩, h0⟩ :=
    Step.while_inv (εR := εR) (c := c) (i := i0) (M := MQ) (F := F) I
      (fun τ => num_chan + 1 - (τ "i").toNat) hbody (num_chan + 1) (σ.set "i" 0) d (by omega)
      ⟨0, by omega, by simp, rfl⟩
  rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .const (BitVec.ofNat 32 (num_chan + 1))) hi' rfl
    (by omega) hnc] at h0
  have hme : m = num_chan + 1 := by
    by_cases h : m < num_chan + 1
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  exact ⟨σ', (Step.assign "i" (by decide) (.const 0)).seq hr⟩

theorem tdqueueInit_triple (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb) :
    Triple εR c i0 MQ (QF qb num_chan) (fun _ _ => True) (tdqInitLoop qb num_proc num_chan)
      (fun _ d _ d' => d' = { d with tdq := real_tdq num_proc num_chan d.tdq }) :=
  Step.triple (fun σ d _ => by
    obtain ⟨σ', h⟩ := tdqueueInit_step εR c i0 hL (fun _ h => h) σ d
    exact ⟨σ', _, h, rfl⟩)

/-! ## The layers below, in this state -/

/-- **Every primitive below keeps its interface in the state with the
queues**, if its footprint stays out of the queue pool. -/
theorem liftT (hL : QLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb)
    {P : Locals → TData → Prop} {s : Stmt APrim} {Q : Locals → TData → Locals → TData → Prop}
    (h : Triple εR c i0 (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb) F P s Q)
    (hF : ∀ k, F k → k < tb + 3 * num_proc ∨ pb ≤ k) :
    Triple εR c i0 MQ F (fun σ d => P σ d.toTData) s
      (fun σ d σ' d' => ∃ t : TData, d' = { d with toTData := t } ∧ Q σ d.toTData σ' t) := by
  have := hL.hqb; have := hL.hqe
  refine (h.lift (π := QData.toTData)
    (put := fun (d' : QData) (t : TData) => ({ d' with toTData := t } : QData))
    (M2 := fun d' b => MatchQP num_chan qb d'.tdq b) (fun _ _ => rfl) ?_).iffM
    (fun d b => ⟨fun h => ⟨h.t, h.qp⟩, fun h => ⟨h.1, h.2⟩⟩)
  intro d' b σ σ' d1 b' h2 hM hP hQ hf j hj
  show MatchTDQ (d'.tdq j) _ _
  rw [hf _ (fun hk => by have := hF _ hk; unfold qcell at this; omega),
    hf _ (fun hk => by have := hF _ hk; unfold qcell at this; omega)]
  exact h2 j hj

end Steps

end PQueue
