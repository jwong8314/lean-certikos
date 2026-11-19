import CertiKOS.MShare

/-!
# mCertiKOS `PThreadIntro`: thread control blocks, ported

The first layer of thread management. Each process has a control block: its
state, and its neighbours in whatever queue it is on.

Ported from `layerlib/AuxStateDataType.v`: `ThreadState`, `ZtoThreadState`,
`ThreadStatetoZ`, `TCB`, `TCBPool`.

Ported from `objects/ObjQueue.v`: `get_state_spec`, `get_prev_spec`,
`get_next_spec`, `set_state_spec`, `set_prev_spec`, `set_next_spec`,
`tcb_init_spec`, `thread_init_spec`. Ported from `clib/CalRealProcModule.v`:
`init_zmap`, `real_tcb`.

Ported from `proc/ThreadIntroGenDef.v`: `match_TCB`, `match_TCBPool`
(`MatchTCB`, `MatchTP`).

Ported from `proc/PKContextNewCSource.v` and `proc/PThreadIntroCSource.v`: the
C code of the seven accessors and the loop of `thread_init`.

Each accessor refines its specification, and `threadInit_triple` shows the
loop of `thread_init` gives `real_tcb`.

What differs: the control blocks are in the memory-management region, after
the shared-memory table (`TLayout`), three cells each: state, prev, next.
`thread_init` first calls `sharedmem_init`, whose own first call is
`pmap_init` (machine model), so `thread_init_spec` is stated and only its
loop is verified. The kernel-context layers below this one in mCertiKOS
(`PKContext`, `PKContextNew`) are about registers and come with the machine
model.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PThread

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval while_inv)

/-! ## Abstract data (`AuxStateDataType.v`) -/

inductive ThreadState
  | READY | RUN | SLEEP | DEAD
  deriving DecidableEq

def ZtoThreadState : Nat → Option ThreadState
  | 0 => some .READY
  | 1 => some .RUN
  | 2 => some .SLEEP
  | 3 => some .DEAD
  | _ => none

def ThreadStatetoZ : ThreadState → Nat
  | .READY => 0
  | .RUN => 1
  | .SLEEP => 2
  | .DEAD => 3

theorem ZtoThreadState_correct {i : Nat} {t : ThreadState} (h : ZtoThreadState i = some t) :
    ThreadStatetoZ t = i := by
  match i, h with
  | 0, h => simp [ZtoThreadState] at h; subst h; rfl
  | 1, h => simp [ZtoThreadState] at h; subst h; rfl
  | 2, h => simp [ZtoThreadState] at h; subst h; rfl
  | 3, h => simp [ZtoThreadState] at h; subst h; rfl
  | n + 4, h => simp [ZtoThreadState] at h

theorem ThreadStatetoZ_correct (t : ThreadState) : ZtoThreadState (ThreadStatetoZ t) = some t := by
  cases t <;> rfl

theorem ThreadStatetoZ_range (t : ThreadState) : ThreadStatetoZ t < 4 := by
  cases t <;> decide

/-- `TCBValid state prev next`. -/
inductive TCB
  | TCBUndef
  | TCBValid (tds : ThreadState) (prev next : Nat)

abbrev TCBPool := Nat → TCB

/-- `SData` with the thread control blocks. -/
structure TData extends SData where
  tcb : TCBPool

/-! ## Specifications (`ObjQueue.v`) -/

section Specs
variable (num_proc : Nat)

def get_state_spec (n : Nat) (d : TData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_proc then
    match d.tcb n with
    | .TCBValid s _ _ => some (ThreadStatetoZ s)
    | .TCBUndef => none
  else none

def get_prev_spec (n : Nat) (d : TData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_proc then
    match d.tcb n with
    | .TCBValid _ prev _ => some prev
    | .TCBUndef => none
  else none

def get_next_spec (n : Nat) (d : TData) : Option Nat :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_proc then
    match d.tcb n with
    | .TCBValid _ _ next => some next
    | .TCBUndef => none
  else none

def set_state_spec (n s : Nat) (d : TData) : Option TData :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_proc then
    match d.tcb n, ZtoThreadState s with
    | .TCBValid _ prev next, some i => some { d with tcb := setAt d.tcb n (.TCBValid i prev next) }
    | _, _ => none
  else none

def set_prev_spec (n s : Nat) (d : TData) : Option TData :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_proc then
    if s ≤ num_proc then
      match d.tcb n with
      | .TCBValid ts _ next => some { d with tcb := setAt d.tcb n (.TCBValid ts s next) }
      | .TCBUndef => none
    else none
  else none

def set_next_spec (n s : Nat) (d : TData) : Option TData :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_proc then
    if s ≤ num_proc then
      match d.tcb n with
      | .TCBValid ts prev _ => some { d with tcb := setAt d.tcb n (.TCBValid ts prev s) }
      | .TCBUndef => none
    else none
  else none

/-- A dead thread on no queue. `num_proc` stands for "none". -/
def tcb_init_spec (n : Nat) (d : TData) : Option TData :=
  if d.pg = true ∧ d.ipt = true ∧ n < num_proc then
    some { d with tcb := setAt d.tcb n (.TCBValid .DEAD num_proc num_proc) }
  else none

end Specs

/-- `init_zmap n x f`: `f` with entries `0 … n-1` set to `x`. -/
def init_zmap {α : Type} : Nat → α → (Nat → α) → Nat → α
  | 0, _, f => f
  | n + 1, x, f => setAt (init_zmap n x f) n x

/-- `real_tcb`. -/
def real_tcb (num_proc : Nat) (t : TCBPool) : TCBPool :=
  init_zmap num_proc (.TCBValid .DEAD num_proc num_proc) t

/-- **`thread_init_spec`**, with the allocation table in place of the owner
lists. -/
def thread_init_spec (num_proc kl kh : Nat) (mm : MALInit.MMTable) (size : Nat) (d : TData) : Option TData :=
  if d.init = false ∧ d.pg = false ∧ d.ipt = true then
    some { d with
      pg := true
      AT := MALInit.real_AT kl kh mm size d.AT
      nps := MALInit.real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := MPTInit.real_pt num_proc d.ptpool
      idpde := MPTInit.real_idpde d.idpde
      smspool := real_smspool num_proc d.smspool
      tcb := real_tcb num_proc d.tcb }
  else none

/-! ## The control blocks in the region (`ThreadIntroGenDef.v`) -/

/-- Cell `k` of control block `n`: 0 state, 1 prev, 2 next. -/
def tcell (tb n k : Nat) : Nat := tb + n * 3 + k

/-- `match_TCB`. -/
def MatchTCB : TCB → Val → Val → Val → Prop
  | .TCBUndef, _, _, _ => True
  | .TCBValid ts p nx, v1, v2, v3 => ZtoThreadState v1.toNat = some ts ∧ p = v2.toNat ∧ nx = v3.toNat

/-- `match_TCBPool`. -/
def MatchTP (num_proc tb : Nat) (t : TCBPool) (b : Region) : Prop :=
  ∀ i, i < num_proc → MatchTCB (t i) (b (tcell tb i 0)) (b (tcell tb i 1)) (b (tcell tb i 2))

/-- The layout with the control blocks after the shared-memory table. -/
structure TLayout (maxpage num_id cb num_proc pb ib fb sb tb : Nat) : Prop where
  slay : SLayout maxpage num_id cb num_proc pb ib fb sb
  htb : sb + 3 * (num_proc * num_proc) ≤ tb
  hte : tb + 3 * num_proc ≤ pb

structure MatchT (maxpage num_id cb num_proc pb ib fb ida sb tb : Nat) (d : TData) (b : Region) : Prop where
  s : MatchS maxpage num_id cb num_proc pb ib fb ida sb d.toSData b
  tp : MatchTP num_proc tb d.tcb b

section Region
variable {maxpage num_id cb num_proc pb ib fb ida sb tb : Nat}

/-- Everything below this layer ignores the control blocks' cells. -/
theorem matchS_frame (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) {d : SData} {b b' : Region}
    (hM : MatchS maxpage num_id cb num_proc pb ib fb ida sb d b)
    (hfr : ∀ k, k < tb ∨ tb + 3 * num_proc ≤ k → b' k = b k) :
    MatchS maxpage num_id cb num_proc pb ib fb ida sb d b' := by
  have := hL.slay.lay.hcb; have := hL.slay.lay.hpb; have := hL.slay.hsb; have := hL.slay.hse
  have := hL.htb; have := hL.hte
  have hb : ∀ k, k < cb + 5 * num_id → b' k = b k := fun k hk => hfr k (Or.inl (by omega))
  refine ⟨⟨⟨⟨fun j hj => ?_, ?_⟩, fun j hj => ?_⟩,
    matchpt_transfer hL.slay.lay hM.all.pt (fun k hk => hfr k (Or.inr (by omega))) rfl rfl rfl
      (fun _ _ _ _ => rfl)⟩, fun q1 q2 g1 g2 => ?_⟩
  · rw [hb _ (by omega), hb _ (by omega), hb _ (by omega)]; exact hM.all.mm.mAT.mat j hj
  · rw [hb _ (by omega)]; exact hM.all.mm.mAT.mnps
  · rw [hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega), hb _ (by omega)]
    exact hM.all.mm.mAC j hj
  · have hlt := scell_lt (sb := sb) g1 g2 (show 2 < 3 by decide)
    have e : ∀ k, k < 3 → b' (scell sb num_proc q1 q2 k) = b (scell sb num_proc q1 q2 k) := fun k hk =>
      hfr _ (Or.inl (by unfold scell at *; omega))
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
    exact hM.sp q1 q2 g1 g2

/-- What the three words of a valid control block are. -/
theorem tcb_get {t : TCBPool} {b : Region} (hM : MatchTP num_proc tb t b) {i : Nat} (hi : i < num_proc)
    {ts : ThreadState} {p nx : Nat} (he : t i = .TCBValid ts p nx) :
    b (tcell tb i 0) = BitVec.ofNat 32 (ThreadStatetoZ ts) ∧ b (tcell tb i 1) = BitVec.ofNat 32 p ∧
    b (tcell tb i 2) = BitVec.ofNat 32 nx ∧ p < 2 ^ 32 ∧ nx < 2 ^ 32 := by
  have h := hM i hi
  rw [he] at h
  obtain ⟨a1, a2, a3⟩ := h
  have hp : p < 2 ^ 32 := by rw [a2]; exact (b (tcell tb i 1)).isLt
  have hn : nx < 2 ^ 32 := by rw [a3]; exact (b (tcell tb i 2)).isLt
  have := ThreadStatetoZ_range ts
  exact ⟨val_of_toNat (ZtoThreadState_correct a1).symm (by omega), val_of_toNat a2.symm hp,
    val_of_toNat a3.symm hn, hp, hn⟩

/-- **Rewriting a control block.** -/
theorem tcb_put (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) {d : TData} {b b' : Region}
    (hM : MatchT maxpage num_id cb num_proc pb ib fb ida sb tb d b) {i : Nat} (hi : i < num_proc)
    {ts : ThreadState} {p nx : Nat} (hp : p < 2 ^ 32) (hnx : nx < 2 ^ 32)
    (hfr : ∀ k, k < tcell tb i 0 ∨ tcell tb i 2 < k → b' k = b k)
    (e0 : b' (tcell tb i 0) = BitVec.ofNat 32 (ThreadStatetoZ ts))
    (e1 : b' (tcell tb i 1) = BitVec.ofNat 32 p) (e2 : b' (tcell tb i 2) = BitVec.ofNat 32 nx) :
    MatchT maxpage num_id cb num_proc pb ib fb ida sb tb
      { d with tcb := setAt d.tcb i (.TCBValid ts p nx) } b' := by
  refine ⟨matchS_frame hL hM.s (fun k hk => hfr k (by unfold tcell; omega)), fun j hj => ?_⟩
  show MatchTCB (setAt d.tcb i (.TCBValid ts p nx) j) _ _ _
  by_cases e : j = i
  · subst e
    rw [setAt_eq, e0, e1, e2]
    have := ThreadStatetoZ_range ts
    exact ⟨by rw [tn (by omega)]; exact ThreadStatetoZ_correct ts, (tn hp).symm, (tn hnx).symm⟩
  · rw [setAt_ne _ _ e, hfr _ (by unfold tcell; omega), hfr _ (by unfold tcell; omega),
      hfr _ (by unfold tcell; omega)]
    exact hM.tp j hj

/-- One word of a valid control block is overwritten. -/
theorem tcb_set1 (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) {d : TData} {b : Region}
    (hM : MatchT maxpage num_id cb num_proc pb ib fb ida sb tb d b) {i : Nat} (hi : i < num_proc)
    {ts : ThreadState} {p nx : Nat} (he : d.tcb i = .TCBValid ts p nx) {k : Nat} (hk : k < 3) (w : Val)
    {ts' : ThreadState} {p' nx' : Nat} (hp' : p' < 2 ^ 32) (hnx' : nx' < 2 ^ 32)
    (c0 : k = 0 → w = BitVec.ofNat 32 (ThreadStatetoZ ts')) (c0' : k ≠ 0 → ts' = ts)
    (c1 : k = 1 → w = BitVec.ofNat 32 p') (c1' : k ≠ 1 → p' = p)
    (c2 : k = 2 → w = BitVec.ofNat 32 nx') (c2' : k ≠ 2 → nx' = nx) :
    MatchT maxpage num_id cb num_proc pb ib fb ida sb tb
      { d with tcb := setAt d.tcb i (.TCBValid ts' p' nx') } (setCell b (tcell tb i k) w) := by
  obtain ⟨a0, a1, a2, -, -⟩ := tcb_get hM.tp hi he
  refine tcb_put hL hM hi hp' hnx' (fun k' hk' => sc_ne _ _ (by unfold tcell at *; omega)) ?_ ?_ ?_
  · by_cases e : k = 0
    · subst e; rw [sc_eq]; exact c0 rfl
    · rw [sc_ne _ _ (by unfold tcell; omega), c0' e]; exact a0
  · by_cases e : k = 1
    · subst e; rw [sc_eq]; exact c1 rfl
    · rw [sc_ne _ _ (by unfold tcell; omega), c1' e]; exact a1
  · by_cases e : k = 2
    · subst e; rw [sc_eq]; exact c2 rfl
    · rw [sc_ne _ _ (by unfold tcell; omega), c2' e]; exact a2

/-- A write to a word of control block `i` is inside the pool. -/
theorem tcb_foot {b : Region} {i k : Nat} (hi : i < num_proc) (hk : k < 3) (w : Val) (k' : Nat)
    (hk' : ¬ (tb ≤ k' ∧ k' < tb + 3 * num_proc)) : setCell b (tcell tb i k) w k' = b k' := by
  refine sc_ne _ _ (fun e => hk' ?_)
  subst e
  unfold tcell; omega

end Region

/-! ## The C code (`PKContextNewCSource.v`) -/

/-- `&TCBPool_LOC[e]`, field `k`. -/
def tcbE (tb : Nat) (ie : Expr) (k : Nat) : Expr :=
  .bin .add (.const (BitVec.ofNat 32 (tb + k))) (.bin .mul ie (.const 3))

theorem tcb_eval {tb n : Nat} (hend : tb + 3 * n ≤ 2 ^ 32) {σ : Locals} {ie : Expr} {i k : Nat}
    (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < n) (hk : k < 3) :
    ((tcbE tb ie k).eval σ).toNat = tcell tb i k := by
  have e : (tcbE tb ie k).eval σ = BitVec.ofNat 32 (tb + k) + ie.eval σ * (3 : Val) := rfl
  rw [e, he, show (3 : Val) = BitVec.ofNat 32 3 from rfl, ← BitVec.ofNat_mul, ← BitVec.ofNat_add,
    tn (by omega)]
  unfold tcell; omega

def tGetS (tb : Nat) (x : Ident) (ie : Expr) (k : Nat) : Stmt APrim := .call x .pull [lkE, tcbE tb ie k]
def tSetS (tb : Nat) (ie : Expr) (k : Nat) (ve : Expr) : Stmt APrim := .call "_" .push [lkE, tcbE tb ie k, ve]

/-- `x = get_state(e)`: `return TCBPool_LOC[e].state;` -/
def getTStateS (tb : Nat) (x : Ident) (ie : Expr) : Stmt APrim := tGetS tb x ie 0
/-- `x = get_prev(e)` -/
def getPrevS (tb : Nat) (x : Ident) (ie : Expr) : Stmt APrim := tGetS tb x ie 1
/-- `x = get_next(e)` -/
def getNextS (tb : Nat) (x : Ident) (ie : Expr) : Stmt APrim := tGetS tb x ie 2
/-- `set_state(e, v)`: `TCBPool_LOC[e].state = v;` -/
def setTStateS (tb : Nat) (ie ve : Expr) : Stmt APrim := tSetS tb ie 0 ve
/-- `set_prev(e, v)` -/
def setPrevS (tb : Nat) (ie ve : Expr) : Stmt APrim := tSetS tb ie 1 ve
/-- `set_next(e, v)` -/
def setNextS (tb : Nat) (ie ve : Expr) : Stmt APrim := tSetS tb ie 2 ve

/-- `tcb_init(e)`: `.state = 3; .prev = num_proc; .next = num_proc;` -/
def tcbInitS (tb num_proc : Nat) (ie : Expr) : Stmt APrim :=
  .seq (setTStateS tb ie (.const 3))
    (.seq (setPrevS tb ie (.const (BitVec.ofNat 32 num_proc))) (setNextS tb ie (.const (BitVec.ofNat 32 num_proc))))

section Triples
variable {maxpage num_id cb num_proc pb ib fb ida sb tb : Nat}

theorem tGet_run (εR : REnv) {c : CPU} {i0 : Nat} (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb)
    {l : RLog} {b : Region} (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) (x : Ident)
    {ie : Expr} {i k : Nat} (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < num_proc) (hk : k < 3) :
    Runs (rprimsA εR c) (tGetS tb x ie k) σ l (σ.set x (b (tcell tb i k))) l := by
  have := hL.hte; have := hL.slay.lay.hib; have := hL.slay.lay.hfb; have := hL.slay.lay.hend
  exact rd_run (εR := εR) hcs hlk x _ (tcb_eval (by omega) he hi hk)

theorem tSet_run (εR : REnv) {c : CPU} {i0 : Nat} (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb)
    {l : RLog} {b : Region} (hcs : CS1 c i0 l b) {σ : Locals} (hlk : (σ "lk").toNat = i0) {ie ve : Expr}
    {i k : Nat} {w : Val} (he : ie.eval σ = BitVec.ofNat 32 i) (hi : i < num_proc) (hk : k < 3)
    (hw : ve.eval σ = w) :
    ∃ l', Runs (rprimsA εR c) (tSetS tb ie k ve) σ l (σ.set "_" 0) l' ∧
      CS1 c i0 l' (setCell b (tcell tb i k) w) := by
  have := hL.hte; have := hL.slay.lay.hib; have := hL.slay.lay.hfb; have := hL.slay.lay.hend
  exact wr_run (εR := εR) hcs hlk _ ve (tcb_eval (by omega) he hi hk) hw

theorem getTState_triple (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) (x : Ident) (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb) (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_state_spec num_proc n d = some v)
      (getTStateS tb x ie)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_state_spec num_proc n d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  intro σ l b d hlk hcs hM ⟨he, v, hs⟩
  have hs0 := hs
  unfold get_state_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn⟩ := hc
    cases ht : d.tcb n with
    | TCBUndef => rw [ht] at hs; cases hs
    | TCBValid ts p nx =>
      rw [ht] at hs; simp only [Option.some.injEq] at hs
      obtain ⟨a0, -, -, -, -⟩ := tcb_get hM.tp hn ht
      have hr := tGet_run εR hL hcs hlk x he hn (show 0 < 3 by decide)
      rw [a0, hs] at hr
      exact ⟨_, l, b, d, hr, hcs, hM, Locals.set_other _ _ (Ne.symm hx), fun _ _ => rfl, rfl, v, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem getPrev_triple (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) (x : Ident) (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb) (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_prev_spec num_proc n d = some v)
      (getPrevS tb x ie)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_prev_spec num_proc n d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  intro σ l b d hlk hcs hM ⟨he, v, hs⟩
  have hs0 := hs
  unfold get_prev_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn⟩ := hc
    cases ht : d.tcb n with
    | TCBUndef => rw [ht] at hs; cases hs
    | TCBValid ts p nx =>
      rw [ht] at hs; simp only [Option.some.injEq] at hs
      obtain ⟨-, a1, -, -, -⟩ := tcb_get hM.tp hn ht
      have hr := tGet_run εR hL hcs hlk x he hn (show 1 < 3 by decide)
      rw [a1, hs] at hr
      exact ⟨_, l, b, d, hr, hcs, hM, Locals.set_other _ _ (Ne.symm hx), fun _ _ => rfl, rfl, v, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem getNext_triple (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) (x : Ident) (hx : x ≠ "lk") (ie : Expr) (n : Nat) :
    Triple εR c i0 (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb) (fun _ => False)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ∃ v, get_next_spec num_proc n d = some v)
      (getNextS tb x ie)
      (fun σ d σ' d' => d' = d ∧ ∃ v, get_next_spec num_proc n d = some v ∧
        σ' = σ.set x (BitVec.ofNat 32 v)) := by
  intro σ l b d hlk hcs hM ⟨he, v, hs⟩
  have hs0 := hs
  unfold get_next_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn⟩ := hc
    cases ht : d.tcb n with
    | TCBUndef => rw [ht] at hs; cases hs
    | TCBValid ts p nx =>
      rw [ht] at hs; simp only [Option.some.injEq] at hs
      obtain ⟨-, -, a2, -, -⟩ := tcb_get hM.tp hn ht
      have hr := tGet_run εR hL hcs hlk x he hn (show 2 < 3 by decide)
      rw [a2, hs] at hr
      exact ⟨_, l, b, d, hr, hcs, hM, Locals.set_other _ _ (Ne.symm hx), fun _ _ => rfl, rfl, v, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem setTState_triple (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) (ie ve : Expr) (n sv : Nat) :
    Triple εR c i0 (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb)
      (fun k => tb ≤ k ∧ k < tb + 3 * num_proc)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧
        ∃ d1, set_state_spec num_proc n sv d = some d1)
      (setTStateS tb ie ve)
      (fun σ d σ' d' => set_state_spec num_proc n sv d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨he, hve, d1, hs⟩
  have hs0 := hs
  unfold set_state_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn⟩ := hc
    cases ht : d.tcb n with
    | TCBUndef => rw [ht] at hs; cases hs
    | TCBValid ts p nx =>
      cases hz : ZtoThreadState sv with
      | none => rw [ht, hz] at hs; cases hs
      | some ts' =>
        rw [ht, hz] at hs; simp only [Option.some.injEq] at hs
        obtain ⟨-, -, -, hp, hnx⟩ := tcb_get hM.tp hn ht
        obtain ⟨l', hr, hcs'⟩ := tSet_run εR hL hcs hlk he hn (show 0 < 3 by decide) hve
        have hM' := tcb_set1 hL hM hn ht (show 0 < 3 by decide) (BitVec.ofNat 32 sv) (ts' := ts') (p' := p)
          (nx' := nx) hp hnx (fun _ => by rw [ZtoThreadState_correct hz]) (fun e => absurd rfl e)
          (fun e => by cases e) (fun _ => rfl) (fun e => by cases e) (fun _ => rfl)
        rw [hs] at hM'
        exact ⟨_, l', _, d1, hr, hcs', hM', Locals.set_other _ _ (by decide),
          tcb_foot hn (by decide) _, hs0, rfl⟩
  · rw [if_neg hc] at hs; cases hs

theorem setPrev_triple (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) (ie ve : Expr) (n sv : Nat) :
    Triple εR c i0 (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb)
      (fun k => tb ≤ k ∧ k < tb + 3 * num_proc)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧
        ∃ d1, set_prev_spec num_proc n sv d = some d1)
      (setPrevS tb ie ve)
      (fun σ d σ' d' => set_prev_spec num_proc n sv d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨he, hve, d1, hs⟩
  have := hL.hte; have := hL.slay.lay.hib; have := hL.slay.lay.hfb; have := hL.slay.lay.hend
  have hs0 := hs
  unfold set_prev_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn⟩ := hc
    by_cases hsv : sv ≤ num_proc
    · rw [if_pos hsv] at hs
      cases ht : d.tcb n with
      | TCBUndef => rw [ht] at hs; cases hs
      | TCBValid ts p nx =>
        rw [ht] at hs; simp only [Option.some.injEq] at hs
        obtain ⟨-, -, -, hp, hnx⟩ := tcb_get hM.tp hn ht
        obtain ⟨l', hr, hcs'⟩ := tSet_run εR hL hcs hlk he hn (show 1 < 3 by decide) hve
        have hM' := tcb_set1 hL hM hn ht (show 1 < 3 by decide) (BitVec.ofNat 32 sv) (ts' := ts) (p' := sv)
          (nx' := nx) (by omega) hnx (fun e => by cases e) (fun _ => rfl) (fun _ => rfl)
          (fun e => absurd rfl e) (fun e => by cases e) (fun _ => rfl)
        rw [hs] at hM'
        exact ⟨_, l', _, d1, hr, hcs', hM', Locals.set_other _ _ (by decide),
          tcb_foot hn (by decide) _, hs0, rfl⟩
    · rw [if_neg hsv] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

theorem setNext_triple (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) (ie ve : Expr) (n sv : Nat) :
    Triple εR c i0 (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb)
      (fun k => tb ≤ k ∧ k < tb + 3 * num_proc)
      (fun σ d => ie.eval σ = BitVec.ofNat 32 n ∧ ve.eval σ = BitVec.ofNat 32 sv ∧
        ∃ d1, set_next_spec num_proc n sv d = some d1)
      (setNextS tb ie ve)
      (fun σ d σ' d' => set_next_spec num_proc n sv d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨he, hve, d1, hs⟩
  have := hL.hte; have := hL.slay.lay.hib; have := hL.slay.lay.hfb; have := hL.slay.lay.hend
  have hs0 := hs
  unfold set_next_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨-, -, hn⟩ := hc
    by_cases hsv : sv ≤ num_proc
    · rw [if_pos hsv] at hs
      cases ht : d.tcb n with
      | TCBUndef => rw [ht] at hs; cases hs
      | TCBValid ts p nx =>
        rw [ht] at hs; simp only [Option.some.injEq] at hs
        obtain ⟨-, -, -, hp, hnx⟩ := tcb_get hM.tp hn ht
        obtain ⟨l', hr, hcs'⟩ := tSet_run εR hL hcs hlk he hn (show 2 < 3 by decide) hve
        have hM' := tcb_set1 hL hM hn ht (show 2 < 3 by decide) (BitVec.ofNat 32 sv) (ts' := ts) (p' := p)
          (nx' := sv) hp (by omega) (fun e => by cases e) (fun _ => rfl) (fun e => by cases e)
          (fun _ => rfl) (fun _ => rfl) (fun e => absurd rfl e)
        rw [hs] at hM'
        exact ⟨_, l', _, d1, hr, hcs', hM', Locals.set_other _ _ (by decide),
          tcb_foot hn (by decide) _, hs0, rfl⟩
    · rw [if_neg hsv] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

/-- **`tcb_init` refines `tcb_init_spec`.** The argument is a local other
than `_`. -/
theorem tcbInit_triple (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) (a : Ident) (ha : a ≠ "_") (n : Nat) :
    Triple εR c i0 (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb)
      (fun k => tb ≤ k ∧ k < tb + 3 * num_proc)
      (fun σ d => σ a = BitVec.ofNat 32 n ∧ ∃ d1, tcb_init_spec num_proc n d = some d1)
      (tcbInitS tb num_proc (.var a))
      (fun σ d σ' d' => tcb_init_spec num_proc n d = some d' ∧ σ' = σ.set "_" 0) := by
  intro σ l b d hlk hcs hM ⟨hp, d1, hs⟩
  have := hL.hte; have := hL.slay.lay.hib; have := hL.slay.lay.hfb; have := hL.slay.lay.hend
  have hs0 := hs
  unfold tcb_init_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ n < num_proc
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    obtain ⟨-, -, hn⟩ := hc
    let σ1 := σ.set "_" 0
    have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
    have hq : (Expr.var a).eval σ1 = BitVec.ofNat 32 n := (Locals.set_other _ _ ha).trans hp
    have hss : σ1.set "_" 0 = σ1 := set_set _ _ _ _
    obtain ⟨l1, r1, c1⟩ := tSet_run εR hL hcs hlk (ie := .var a) (ve := .const 3) (w := BitVec.ofNat 32 3)
      hp hn (show 0 < 3 by decide) rfl
    obtain ⟨l2, r2, c2⟩ := tSet_run εR hL c1 hlk1 (ie := .var a) (ve := .const (BitVec.ofNat 32 num_proc))
      (w := BitVec.ofNat 32 num_proc) hq hn (show 1 < 3 by decide) rfl
    rw [hss] at r2
    obtain ⟨l3, r3, c3⟩ := tSet_run εR hL c2 hlk1 (ie := .var a) (ve := .const (BitVec.ofNat 32 num_proc))
      (w := BitVec.ofNat 32 num_proc) hq hn (show 2 < 3 by decide) rfl
    rw [hss] at r3
    have hM' := tcb_put hL hM hn (ts := .DEAD) (p := num_proc) (nx := num_proc) (by omega) (by omega)
      (b' := setCell (setCell (setCell b (tcell tb n 0) (BitVec.ofNat 32 3)) (tcell tb n 1)
        (BitVec.ofNat 32 num_proc)) (tcell tb n 2) (BitVec.ofNat 32 num_proc))
      (fun k hk => by
        rw [sc_ne _ _ (by unfold tcell at *; omega), sc_ne _ _ (by unfold tcell at *; omega),
          sc_ne _ _ (by unfold tcell at *; omega)])
      (by rw [sc_ne _ _ (by unfold tcell; omega), sc_ne _ _ (by unfold tcell; omega), sc_eq]; rfl)
      (by rw [sc_ne _ _ (by unfold tcell; omega), sc_eq])
      (by rw [sc_eq])
    rw [hs] at hM'
    refine ⟨_, l3, _, d1, Runs.seq r1 (Runs.seq r2 r3), c3, hM', Locals.set_other _ _ (by decide),
      fun k hk => ?_, hs0, rfl⟩
    rw [tcb_foot hn (by decide) _ k hk, tcb_foot hn (by decide) _ k hk, tcb_foot hn (by decide) _ k hk]
  · rw [if_neg hc] at hs; cases hs

/-! ## `thread_init`'s loop -/

def Dt (d : TData) (t : TCBPool) : TData := { d with tcb := t }

/-- `i = 0; while (i < num_proc) { tcb_init(i); i++; }` -/
def threadInitLoop (tb num_proc : Nat) : Stmt APrim :=
  .seq (.assign "i" (.const 0))
    (.while (.bin .ltu (.var "i") (.const (BitVec.ofNat 32 num_proc)))
      (.seq (tcbInitS tb num_proc (.var "i")) (.assign "i" (.bin .add (.var "i") (.const 1)))))

/-- **The loop of `thread_init` initialises every control block**
(`real_tcb`), through `tcb_init`'s specification. -/
theorem threadInit_triple (εR : REnv) (c : CPU) (i0 : Nat)
    (hL : TLayout maxpage num_id cb num_proc pb ib fb sb tb) :
    Triple εR c i0 (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb)
      (fun k => tb ≤ k ∧ k < tb + 3 * num_proc)
      (fun _ d => d.pg = true ∧ d.ipt = true)
      (threadInitLoop tb num_proc)
      (fun _ d _ d' => d' = { d with tcb := real_tcb num_proc d.tcb }) := by
  rintro σ l b d hlk hcs hM ⟨hpg, hipt⟩
  have hnp : num_proc < 2 ^ 32 := by
    have := hL.hte; have := hL.slay.lay.hib; have := hL.slay.lay.hfb; have := hL.slay.lay.hend; omega
  let x0 : TCB := .TCBValid .DEAD num_proc num_proc
  let σ0 := σ.set "i" 0
  have h0r : Runs (rprimsA εR c) (.assign "i" (.const 0)) σ l σ0 l := Runs.assign _ _
  let Inv : Locals → RLog → Prop := fun τ l' => τ "lk" = σ "lk" ∧ ∃ m b', m ≤ num_proc ∧
    τ "i" = BitVec.ofNat 32 m ∧ CS1 c i0 l' b' ∧
    MatchT maxpage num_id cb num_proc pb ib fb ida sb tb (Dt d (init_zmap m x0 d.tcb)) b' ∧
    ∀ k, ¬ (tb ≤ k ∧ k < tb + 3 * num_proc) → b' k = b k
  have hbody : ∀ τ l', Inv τ l' → ¬ (Expr.bin .ltu (.var "i") (.const (BitVec.ofNat 32 num_proc))).eval τ = 0 →
      ∃ τ' l'', Runs (rprimsA εR c) (.seq (tcbInitS tb num_proc (.var "i"))
          (.assign "i" (.bin .add (.var "i") (.const 1)))) τ l' τ' l'' ∧ Inv τ' l'' ∧
        num_proc - (τ' "i").toNat < num_proc - (τ "i").toNat := by
    rintro τ l' ⟨hlkτ, m, b', hm, hiτ, hcs', hM', hfr⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .const (BitVec.ofNat 32 num_proc)) hiτ rfl (by omega) hnp] at hg
    have hmlt : m < num_proc := by
      by_cases h : m < num_proc
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    have hstep : tcb_init_spec num_proc m (Dt d (init_zmap m x0 d.tcb)) =
        some (Dt d (init_zmap (m + 1) x0 d.tcb)) := by
      unfold tcb_init_spec
      rw [if_pos ⟨hpg, hipt, hmlt⟩]; rfl
    obtain ⟨τ2, l2, b2, d2, hr2, hcs2, hM2, hlk2, hf2, hq, hτ2⟩ :=
      tcbInit_triple εR c i0 hL "i" (by decide) m τ l' b' (Dt d (init_zmap m x0 d.tcb))
        (by rw [hlkτ]; exact hlk) hcs' hM' ⟨hiτ, _, hstep⟩
    rw [hstep] at hq
    simp only [Option.some.injEq] at hq
    rw [← hq] at hM2
    have h3 := asg_run (εR := εR) (c := c) (σ := τ2) (l := l2) "i" (.bin .add (.var "i") (.const 1))
      (inc_eval (m := m) (by rw [hτ2, Locals.set_other _ _ (by decide)]; exact hiτ))
    refine ⟨_, l2, Runs.seq hr2 h3, ⟨?_, m + 1, b2, hmlt, by simp, hcs2, hM2, fun k hk => ?_⟩, ?_⟩
    · simp [Locals.set, hlk2, hlkτ]
    · rw [hf2 k hk, hfr k hk]
    · rw [Locals.set_same, hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', l', hr, ⟨hlk', m, b', hm, hi', hcs', hM', hfr⟩, h0⟩ :=
    while_inv (εR := εR) (c := c) Inv (fun τ => num_proc - (τ "i").toNat) hbody num_proc σ0 l
      (by omega) ⟨by simp [σ0, Locals.set], 0, b, by omega, by simp [σ0], hcs, hM, fun _ _ => rfl⟩
  rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .const (BitVec.ofNat 32 num_proc)) hi' rfl (by omega) hnp] at h0
  have hme : m = num_proc := by
    by_cases h : m < num_proc
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  exact ⟨σ', l', b', _, Runs.seq h0r hr, hcs', hM', hlk', hfr, rfl⟩

end Triples

end PThread
