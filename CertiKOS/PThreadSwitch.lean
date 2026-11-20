import CertiKOS.PKContext

/-!
# mCertiKOS `thread_sched`, `thread_yield`, `thread_sleep`, ported

The scheduler functions that switch threads.

Ported from `objects/ObjThread.v`: `thread_sched_spec`, `thread_yield_spec`,
`thread_sleep_spec`. Ported from `layerlib/AuxStateDataType.v`: `CurIDValid`.
Ported from `proc/ThreadSchedGenAsmSource.v` and `proc/ThreadGenAsmSource.v`:
the code, which mCertiKOS writes in assembly:

```
thread_sched:  new = dequeue(num_chan); set_state(new, RUN); old = get_curid();
               set_curid(new); kctxt_switch(old, new)
thread_yield:  cid = get_curid(); set_state(cid, READY); enqueue(num_chan, cid); thread_sched()
thread_sleep:  cid = get_curid(); set_state(cid, SLEEP); enqueue(chan, cid); thread_sched()
```

* `thread_sched_run`, `thread_yield_run`, `thread_sleep_run`: **each function,
  run on the kernel machine, does what its specification says.** The machine
  ends up running the context of the thread at the head of the ready queue;
  the caller is parked in its own slot as a computation about to return from
  the call; the region matches the new state.
* `thread_sched_eq`, `thread_yield_eq`, `thread_sleep_eq`: the state reached
  is the specification's.
* Each run theorem also gives the invariants of the new state: `AInv`,
  `CurIDValid`, and the current thread in range.

The proofs go through the triples of the list view (`dequeue0`,
`set_state0`, `enqueue0`, `get_curid`, `set_curid`) and one machine step for
the switch.

As in mCertiKOS, `thread_yield` and `thread_sleep` are undefined when the
ready queue is empty.

What differs: the lock is held across the switch, so the thread resumed
finds it held (the CPU holds it, not the thread). `clear_cr2` is left out
(the trap state is not modelled). The context saved has the locals as the
scheduler's code left them, not as they were on entry: the frame conditions
of the theorems say which locals that code writes.

Not here: that a parked thread is resumed, and reasoning about one thread
alone with the others as its environment.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PSched

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID KMach PKCtx
open MALInit (tn)

/-! ## Specifications (`ObjThread.v`) -/

/-- `CurIDValid`: the current thread has a container, is running, and is on
no queue. -/
def CurIDValid (d : CData) : Prop := (d.AC d.cid).cused = true ∧ d.abtcb d.cid = .AbTCBValid .RUN (-1)

/-- What `thread_sched` leaves: `la` runs, the caller's context `rs` is saved. -/
def schedOut (nc la : Nat) (l : List Nat) (rs : KCtx) (d : KData) : KData :=
  { d with
    kctxt := setAt d.kctxt d.cid rs
    abtcb := setAt d.abtcb la (.AbTCBValid .RUN (-1))
    abq := setAt d.abq nc (.AbQValid (remove la l))
    cid := la }

def thread_sched_at (nc la : Nat) (l : List Nat) (rs : KCtx) (d : KData) : Option (KData × KCtx) :=
  if (d.AC la).cused = true then
    match d.abtcb la with
    | .AbTCBUndef => none
    | .AbTCBValid _ _ =>
      match d.abtcb d.cid with
      | .AbTCBUndef => none
      | .AbTCBValid st _ =>
        if st = .RUN then none
        else if d.cid = la then none
        else some (schedOut nc la l rs d, d.kctxt la)
  else none

/-- **`thread_sched_spec`**: the head of the ready queue becomes the current
thread. -/
def thread_sched_spec (np nc : Nat) (rs : KCtx) (d : KData) : Option (KData × KCtx) :=
  if d.pg = true ∧ d.ipt = true then
    match d.abq nc with
    | .AbQUndef => none
    | .AbQValid l =>
      if l.getLastD np = np then none else thread_sched_at nc (l.getLastD np) l rs d
  else none

def yieldOut (nc la : Nat) (l : List Nat) (rs : KCtx) (d : KData) : KData :=
  { d with
    kctxt := setAt d.kctxt d.cid rs
    abtcb := setAt (setAt d.abtcb d.cid (.AbTCBValid .READY nc)) la (.AbTCBValid .RUN (-1))
    abq := setAt d.abq nc (.AbQValid (remove la (d.cid :: l)))
    cid := la }

/-- **`thread_yield_spec`**: the current thread goes to the back of the
ready queue and the head of the queue runs. -/
def thread_yield_spec (np nc : Nat) (rs : KCtx) (d : KData) : Option (KData × KCtx) :=
  if d.pg = true ∧ d.ipt = true then
    match d.abq nc with
    | .AbQUndef => none
    | .AbQValid l =>
      if l.getLastD np = np then none
      else some (yieldOut nc (l.getLastD np) l rs d, d.kctxt (l.getLastD np))
  else none

def sleepOut (nc n la : Nat) (l l' : List Nat) (rs : KCtx) (d : KData) : KData :=
  { d with
    kctxt := setAt d.kctxt d.cid rs
    abtcb := setAt (setAt d.abtcb d.cid (.AbTCBValid .SLEEP n)) la (.AbTCBValid .RUN (-1))
    abq := setAt (setAt d.abq n (.AbQValid (d.cid :: l'))) nc (.AbQValid (remove la l))
    cid := la }

/-- **`thread_sleep_spec`**: the current thread goes to sleep queue `n` and
the head of the ready queue runs. -/
def thread_sleep_spec (np nc n : Nat) (rs : KCtx) (d : KData) : Option (KData × KCtx) :=
  if d.pg = true ∧ d.ipt = true ∧ n < nc then
    match d.abq nc, d.abq n with
    | .AbQValid l, .AbQValid l' =>
      if l.getLastD np = np then none
      else some (sleepOut nc n (l.getLastD np) l l' rs d, d.kctxt (l.getLastD np))
    | _, _ => none
  else none

/-- What `thread_sched` needs of the state. -/
structure SchedPre (np nc : Nat) (d : CData) (l : List Nat) (la : Nat) : Prop where
  pg : d.pg = true
  ipt : d.ipt = true
  hq : d.abq nc = .AbQValid l
  hla : l.getLastD np = la
  hne : la ≠ np
  hcu : (d.AC la).cused = true
  hv : ∃ s b, d.abtcb la = .AbTCBValid s b
  hcur : ∃ st b, d.abtcb d.cid = .AbTCBValid st b ∧ st ≠ .RUN
  hd : d.cid ≠ la

section Spec
variable {np nc : Nat}

/-- **The state `thread_sched` reaches is the specification's.** -/
theorem thread_sched_eq {d : KData} {l : List Nat} {la : Nat} (hP : SchedPre np nc d.toCData l la)
    (rs : KCtx) : thread_sched_spec np nc rs d = some (schedOut nc la l rs d, d.kctxt la) := by
  obtain ⟨hpg, hipt, hq, hla, hne, hcu, ⟨s, b, hai⟩, ⟨st, b', hcur, hst⟩, hd⟩ := hP
  unfold thread_sched_spec
  rw [if_pos ⟨hpg, hipt⟩, hq]
  simp only
  rw [hla, if_neg hne]
  unfold thread_sched_at
  rw [if_pos hcu, hai]
  simp only
  rw [hcur]
  simp only
  rw [if_neg hst, if_neg hd]

/-- **The state `thread_yield` reaches is the specification's.** -/
theorem thread_yield_eq {d : KData} {l : List Nat} {la : Nat} (hpg : d.pg = true) (hipt : d.ipt = true)
    (hq : d.abq nc = .AbQValid l) (hla : l.getLastD np = la) (hne : la ≠ np) (rs : KCtx) :
    thread_yield_spec np nc rs d = some (yieldOut nc la l rs d, d.kctxt la) := by
  unfold thread_yield_spec
  rw [if_pos ⟨hpg, hipt⟩, hq]
  simp only
  rw [hla, if_neg hne]

/-- **The state `thread_sleep` reaches is the specification's.** -/
theorem thread_sleep_eq {d : KData} {n : Nat} {l l' : List Nat} {la : Nat} (hpg : d.pg = true)
    (hipt : d.ipt = true) (hn : n < nc) (hq : d.abq nc = .AbQValid l) (hq' : d.abq n = .AbQValid l')
    (hla : l.getLastD np = la) (hne : la ≠ np) (rs : KCtx) :
    thread_sleep_spec np nc n rs d = some (sleepOut nc n la l l' rs d, d.kctxt la) := by
  unfold thread_sleep_spec
  rw [if_pos ⟨hpg, hipt, hn⟩, hq, hq']
  simp only
  rw [hla, if_neg hne]

/-- `dequeue` of the ready queue, then `set_state(RUN)`. -/
theorem sched_factors {a : AData} {ql : List Nat} {la : Nat} {s : ThreadState} {b0 : Int} (hpg : a.pg = true)
    (hipt : a.ipt = true) (hq : a.abq nc = .AbQValid ql) (hla : ql.getLastD np = la) (hne : la ≠ np)
    (hlt : la < np) (hcu : (a.AC la).cused = true) (hai : a.abtcb la = .AbTCBValid s b0) :
    ∃ a1, dequeue0_spec np nc nc a = some (a1, la) ∧
      set_state0_spec np la 1 a1 = some { a with
        abtcb := setAt a.abtcb la (.AbTCBValid .RUN (-1))
        abq := setAt a.abq nc (.AbQValid (remove la ql)) } := by
  refine ⟨{ a with
    abtcb := setAt a.abtcb la (.AbTCBValid s (-1))
    abq := setAt a.abq nc (.AbQValid (remove la ql)) }, ?_, ?_⟩
  · unfold dequeue0_spec
    rw [if_pos ⟨hpg, hipt, Nat.le_refl _⟩, hq]
    simp only
    rw [hla, if_neg hne, hai]
  · have h1 : setAt a.abtcb la (.AbTCBValid s (-1)) la = .AbTCBValid s (-1) := setAt_eq _ _ _
    unfold set_state0_spec
    simp only
    rw [if_pos ⟨hpg, hipt, hlt⟩, if_pos hcu, h1]
    exact congrArg some (AData.ext3 rfl (by
      show setAt (setAt a.abtcb la _) la _ = setAt a.abtcb la _
      rw [setAt_setAt]) rfl)

/-- `set_state`, then `enqueue`: a thread on no queue goes to queue `q` in
state `ts`. -/
theorem park_factors {a : AData} {cid q sv : Nat} {st ts : ThreadState} {lq : List Nat} (hpg : a.pg = true)
    (hipt : a.ipt = true) (hcid : cid < np) (hq : q ≤ nc) (hcu : (a.AC cid).cused = true)
    (hrun : a.abtcb cid = .AbTCBValid st (-1)) (hts : ZtoThreadState sv = some ts)
    (hlq : a.abq q = .AbQValid lq) :
    ∃ a1, set_state0_spec np cid sv a = some a1 ∧
      enqueue0_spec np nc q cid a1 = some { a with
        abtcb := setAt a.abtcb cid (.AbTCBValid ts q)
        abq := setAt a.abq q (.AbQValid (cid :: lq)) } := by
  refine ⟨{ a with abtcb := setAt a.abtcb cid (.AbTCBValid ts (-1)) }, ?_, ?_⟩
  · unfold set_state0_spec
    rw [if_pos ⟨hpg, hipt, hcid⟩, if_pos hcu, hrun, hts]
  · have h1 : setAt a.abtcb cid (.AbTCBValid ts (-1)) cid = .AbTCBValid ts (-1) := setAt_eq _ _ _
    unfold enqueue0_spec
    simp only
    rw [if_pos ⟨hpg, hipt, hq, hcid⟩, hlq]
    simp only
    rw [if_pos hcu, h1]
    simp only
    rw [if_pos trivial]
    exact congrArg some (AData.ext3 rfl (by
      show setAt (setAt a.abtcb cid _) cid _ = setAt a.abtcb cid _
      rw [setAt_setAt]) rfl)

theorem last_mem {l : List Nat} {d la : Nat} (hla : l.getLastD d = la) (hne : la ≠ d) : la ∈ l := by
  rcases List.eq_nil_or_concat l with e | ⟨r0, x, e⟩
  · subst e; exact absurd hla.symm hne
  · rw [List.concat_eq_append] at e
    subst e
    rw [List.getLastD_concat] at hla
    subst hla
    exact List.mem_append_right _ List.mem_cons_self

theorem last_cons {l : List Nat} {d la : Nat} (hla : l.getLastD d = la) (hne : la ≠ d) (x : Nat) :
    (x :: l).getLastD d = la := by
  cases l with
  | nil => exact absurd hla.symm hne
  | cons y r => rw [List.getLastD_cons, List.getLastD_cons]; rw [List.getLastD_cons] at hla; exact hla

/-- A thread on a queue has a container. -/
theorem cused_of_inq {a : AData} (hI : AInv np nc a) {i q : Nat} {s : ThreadState} (hi : i < np)
    (hai : a.abtcb i = .AbTCBValid s q) : (a.AC i).cused = true := by
  cases hcb : (a.AC i).cused with
  | true => rfl
  | false =>
    have := hI.niq i s q hi hcb hai
    omega

end Spec

/-! ## The code -/

/-- The C part of `thread_sched`:
`new = dequeue(num_chan); set_state(new, RUN); old = get_curid(); set_curid(new);` -/
def schedBodyS (tb qb num_proc num_chan cidb : Nat) : Stmt APrim :=
  .seq (.assign "chan_index" (.const (BitVec.ofNat 32 num_chan)))
    (.seq (dequeueS tb qb num_proc)
      (.seq (setTStateS tb (.var "proc_index") (.const 1))
        (.seq (getCuridS cidb "old") (setCuridS cidb (.var "proc_index")))))

/-- `thread_sched`: the C part, then `kctxt_switch(old, new)`. -/
def threadSchedK (tb qb num_proc num_chan cidb : Nat) : Stmt KPrim :=
  .seq (mapS .base (schedBodyS tb qb num_proc num_chan cidb)) (.call "_" .cswitch [.var "old", .var "proc_index"])

/-- `cid = get_curid(); set_state(cid, sv); enqueue(chan_index, cid);` -/
def parkS (tb qb num_proc cidb sv : Nat) : Stmt APrim :=
  .seq (getCuridS cidb "proc_index")
    (.seq (setTStateS tb (.var "proc_index") (.const (BitVec.ofNat 32 sv))) (enqueueS tb qb num_proc))

/-- The C part of `thread_yield`. -/
def yieldBodyS (tb qb num_proc num_chan cidb : Nat) : Stmt APrim :=
  .seq (.assign "chan_index" (.const (BitVec.ofNat 32 num_chan))) (parkS tb qb num_proc cidb 0)

/-- `thread_yield`. -/
def threadYieldK (tb qb num_proc num_chan cidb : Nat) : Stmt KPrim :=
  .seq (mapS .base (yieldBodyS tb qb num_proc num_chan cidb)) (threadSchedK tb qb num_proc num_chan cidb)

/-- `thread_sleep(chan_index)`. -/
def threadSleepK (tb qb num_proc num_chan cidb : Nat) : Stmt KPrim :=
  .seq (mapS .base (parkS tb qb num_proc cidb 2)) (threadSchedK tb qb num_proc num_chan cidb)

/-- The current thread parked on queue `q` in state `ts`. -/
def parkOut (q : Nat) (ts : ThreadState) (lq : List Nat) (d : KData) : KData :=
  { d with
    abtcb := setAt d.abtcb d.cid (.AbTCBValid ts q)
    abq := setAt d.abq q (.AbQValid (d.cid :: lq)) }

theorem KData.ext5 {d1 d2 : KData} (h1 : d1.toSData = d2.toSData) (h2 : d1.abtcb = d2.abtcb)
    (h3 : d1.abq = d2.abq) (h4 : d1.cid = d2.cid) (h5 : d1.kctxt = d2.kctxt) : d1 = d2 := by
  obtain ⟨⟨⟨s1, t1, q1⟩, c1⟩, k1⟩ := d1
  obtain ⟨⟨⟨s2, t2, q2⟩, c2⟩, k2⟩ := d2
  change s1 = s2 at h1; change t1 = t2 at h2; change q1 = q2 at h3; change c1 = c2 at h4
  change k1 = k2 at h5
  subst h1; subst h2; subst h3; subst h4; subst h5; rfl

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb

theorem qtf_ne (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) :
    ∀ k, QTF tb num_proc qb num_chan k → k ≠ cidb := by
  intro k hk
  have := hL.hcb; have := hL.qlay.hqb
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem tf_ne (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) :
    ∀ k, TF tb num_proc k → k ≠ cidb := fun k hk => qtf_ne hL k (Or.inl hk)

/-! ### The list view's primitives, in the state with the current thread -/

theorem dequeueC (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {σ : Locals}
    {l : RLog} {b : Region} {d : CData} {n : Nat} {a1 : AData} {r : Nat} (hlk : (σ "lk").toNat = i0)
    (hcs : CS1 c i0 l b) (hM : MC d b) (hcn : σ "chan_index" = BitVec.ofNat 32 n)
    (hI : AInv num_proc num_chan d.toAData) (hs : dequeue0_spec num_proc num_chan n d.toAData = some (a1, r)) :
    ∃ σ' l' b', Runs (rprimsA εR c) (dequeueS tb qb num_proc) σ l σ' l' ∧ CS1 c i0 l' b' ∧
      MC ({ d with toAData := a1 } : CData) b' ∧ σ' "lk" = σ "lk" ∧ σ' "proc_index" = BitVec.ofNat 32 r := by
  obtain ⟨σ', l', b', d', hr, hcs', hM', hlk', -, a, hd', r', hq, hpi⟩ :=
    liftA εR c i0 hL (dequeue0_triple εR c i0 hL.qlay n) (qtf_ne hL) σ l b d hlk hcs hM ⟨hcn, hI, a1, r, hs⟩
  rw [hs] at hq
  injection hq with e
  injection e with e1 e2
  subst e1; subst e2; subst hd'
  exact ⟨σ', l', b', hr, hcs', hM', hlk', hpi⟩

theorem setStateC (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {σ : Locals}
    {l : RLog} {b : Region} {d : CData} {ie ve : Expr} {n sv : Nat} {a1 : AData} (hlk : (σ "lk").toNat = i0)
    (hcs : CS1 c i0 l b) (hM : MC d b) (he : ie.eval σ = BitVec.ofNat 32 n)
    (hve : ve.eval σ = BitVec.ofNat 32 sv) (hs : set_state0_spec num_proc n sv d.toAData = some a1) :
    ∃ l' b', Runs (rprimsA εR c) (setTStateS tb ie ve) σ l (σ.set "_" 0) l' ∧ CS1 c i0 l' b' ∧
      MC ({ d with toAData := a1 } : CData) b' := by
  obtain ⟨σ', l', b', d', hr, hcs', hM', hlk', -, a, hd', hq, hσ⟩ :=
    liftA εR c i0 hL (setState0_triple εR c i0 hL.qlay ie ve num_proc n sv (Nat.le_refl _)) (tf_ne hL) σ l b d
      hlk hcs hM ⟨he, hve, a1, hs⟩
  rw [hs] at hq
  injection hq with e
  subst e; subst hd'; subst hσ
  exact ⟨l', b', hr, hcs', hM'⟩

theorem enqueueC (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {σ : Locals}
    {l : RLog} {b : Region} {d : CData} {n i : Nat} {a1 : AData} (hlk : (σ "lk").toNat = i0)
    (hcs : CS1 c i0 l b) (hM : MC d b) (hcn : σ "chan_index" = BitVec.ofNat 32 n)
    (hpi : σ "proc_index" = BitVec.ofNat 32 i) (hI : AInv num_proc num_chan d.toAData)
    (hs : enqueue0_spec num_proc num_chan n i d.toAData = some a1) :
    ∃ σ' l' b', Runs (rprimsA εR c) (enqueueS tb qb num_proc) σ l σ' l' ∧ CS1 c i0 l' b' ∧
      MC ({ d with toAData := a1 } : CData) b' ∧ σ' "lk" = σ "lk" := by
  obtain ⟨σ', l', b', d', hr, hcs', hM', hlk', -, a, hd', hq⟩ :=
    liftA εR c i0 hL (enqueue0_triple εR c i0 hL.qlay n i) (qtf_ne hL) σ l b d hlk hcs hM
      ⟨hcn, hpi, hI, a1, hs⟩
  rw [hs] at hq
  injection hq with e
  subst e; subst hd'
  exact ⟨σ', l', b', hr, hcs', hM', hlk'⟩

/-! ### `thread_sched` -/

/-- The C part of `thread_sched`. -/
theorem schedBody_run (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {σ : Locals}
    {l : RLog} {b : Region} {d : CData} {ql : List Nat} {la : Nat} (hlk : (σ "lk").toNat = i0)
    (hcs : CS1 c i0 l b) (hM : MC d b) (hI : AInv num_proc num_chan d.toAData) (hcid : d.cid < num_proc)
    (hP : SchedPre num_proc num_chan d ql la) :
    ∃ σ' l' b', Runs (rprimsA εR c) (schedBodyS tb qb num_proc num_chan cidb) σ l σ' l' ∧ CS1 c i0 l' b' ∧
      MC ({ d with
        abtcb := setAt d.abtcb la (.AbTCBValid .RUN (-1))
        abq := setAt d.abq num_chan (.AbQValid (remove la ql))
        cid := la } : CData) b' ∧
      σ' "lk" = σ "lk" ∧ σ' "old" = BitVec.ofNat 32 d.cid ∧ σ' "proc_index" = BitVec.ofNat 32 la ∧
      AInv num_proc num_chan ({ d.toAData with
        abtcb := setAt d.abtcb la (.AbTCBValid .RUN (-1))
        abq := setAt d.abq num_chan (.AbQValid (remove la ql)) } : AData) ∧ la < num_proc := by
  have hnp : num_proc < 2 ^ 32 := np_lt hL.qlay
  obtain ⟨hpg, hipt, hq, hla, hne, hcu, ⟨s, b0, hai⟩, -, -⟩ := hP
  have hlt : la < num_proc := q_lt hI.qc (Nat.le_refl _) hq (last_mem hla hne)
  obtain ⟨a1, hdq, hss⟩ := sched_factors (np := num_proc) (nc := num_chan) (a := d.toAData) hpg hipt hq hla
    hne hlt hcu hai
  obtain ⟨σ2, l2, b2, r2, c2, m2, k2, p2⟩ := dequeueC εR c i0 hL
    (σ := σ.set "chan_index" (BitVec.ofNat 32 num_chan)) (by simpa [Locals.set] using hlk) hcs hM
    (by simp [Locals.set]) hI hdq
  have hI1 := (dequeue0_keeps hdq hI).1
  have hlk2 : (σ2 "lk").toNat = i0 := by rw [k2]; simpa [Locals.set] using hlk
  obtain ⟨l3, b3, r3, c3, m3⟩ := setStateC εR c i0 hL (σ := σ2) (ie := .var "proc_index") (ve := .const 1)
    (n := la) (sv := 1) hlk2 c2 m2 p2 rfl hss
  obtain ⟨l4, b4, r4, c4, m4, -⟩ := (getCuridC εR c i0 hL (F := fun _ => False) "old" (by decide)
    (σ2.set "_" 0) _).2 l3 b3 (by simpa [Locals.set] using hlk2) c3 m3
  obtain ⟨l5, b5, r5, c5, m5, -⟩ := (setCuridC εR c i0 hL (F := fun k => k = cidb) (fun _ h => h)
    (ve := .var "proc_index") (σ := (σ2.set "_" 0).set "old" (BitVec.ofNat 32 d.cid)) (i := la)
    (by simp [Expr.eval, Locals.set, p2]) (by omega)).2 l4 b4
    (by simpa [Locals.set] using hlk2) c4 m4
  exact ⟨_, l5, b5, Runs.seq (Runs.assign _ _) (Runs.seq r2 (Runs.seq r3 (Runs.seq r4 r5))), c5, m5,
    by simp [Locals.set, k2], by simp [Locals.set], by simp [Locals.set, p2], set_state0_keeps hss hI1, hlt⟩

/-- **`thread_sched` on the kernel machine.** The head `la` of the ready
queue runs; the caller is parked in its slot; the region matches
`schedOut`. `σf` is the caller's locals as saved. -/
theorem thread_sched_run (code : Nat → Stmt KPrim)
    (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {σ : Locals} {K : Cont KPrim}
    {l : RLog} {b : Region} {d : KData} {ql : List Nat} {la : Nat} (hlk : (σ "lk").toNat = i0)
    (hcs : CS1 c i0 l b) (hM : MC d.toCData b) (hI : AInv num_proc num_chan d.toAData)
    (hcid : d.cid < num_proc) (hP : SchedPre num_proc num_chan d.toCData ql la) :
    ∃ (σf : Locals) (l' : RLog) (b' : Region), (∀ z, frS z (schedBodyS tb qb num_proc num_chan cidb) = true → σf z = σ z) ∧
      KStar εR c code ⟨⟨threadSchedK tb qb num_proc num_chan cidb, K, σ⟩, d.kctxt, l⟩
        ⟨d.kctxt la, (schedOut num_chan la ql ⟨.skip, K, σf.set "_" 0⟩ d).kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MC (schedOut num_chan la ql ⟨.skip, K, σf.set "_" 0⟩ d).toCData b' ∧
      AInv num_proc num_chan (schedOut num_chan la ql ⟨.skip, K, σf.set "_" 0⟩ d).toAData ∧
      CurIDValid (schedOut num_chan la ql ⟨.skip, K, σf.set "_" 0⟩ d).toCData ∧ la < num_proc := by
  have hnp : num_proc < 2 ^ 32 := np_lt hL.qlay
  obtain ⟨σ', l', b', hr, hcs', hM', hlk', hold, hpi, hI', hlt⟩ := schedBody_run εR c i0 hL hlk hcs hM hI hcid hP
  refine ⟨σ', l', b', fun z hz => hr.frame hz, ?_, hcs', hM', hI', ⟨hP.hcu, setAt_eq _ _ _⟩, hlt⟩
  refine (kstar_seq hr _ K d.kctxt).trans (.single ?_)
  have e1 : ((Expr.var "old").eval σ').toNat = d.cid := by
    show (σ' "old").toNat = _
    rw [hold, tn (by omega)]
  have e2 : ((Expr.var "proc_index").eval σ').toNat = la := by
    show (σ' "proc_index").toNat = _
    rw [hpi, tn (by omega)]
  rw [kstep_cswitch, e1, e2, setAt_ne _ _ (fun e => hP.hd e.symm)]
  rfl

/-! ### Parking the current thread -/

/-- `cid = get_curid(); set_state(cid, sv); enqueue(chan_index, cid);` -/
theorem park_run (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {σ : Locals}
    {l : RLog} {b : Region} {d : CData} {q sv : Nat} {ts : ThreadState} {lq : List Nat}
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : MC d b)
    (hcn : σ "chan_index" = BitVec.ofNat 32 q) (hq : q ≤ num_chan) (hI : AInv num_proc num_chan d.toAData)
    (hcid : d.cid < num_proc) (hpg : d.pg = true) (hipt : d.ipt = true) (hcv : CurIDValid d)
    (hts : ZtoThreadState sv = some ts) (hlq : d.abq q = .AbQValid lq) :
    ∃ σ' l' b', Runs (rprimsA εR c) (parkS tb qb num_proc cidb sv) σ l σ' l' ∧ CS1 c i0 l' b' ∧
      MC ({ d with
        abtcb := setAt d.abtcb d.cid (.AbTCBValid ts q)
        abq := setAt d.abq q (.AbQValid (d.cid :: lq)) } : CData) b' ∧
      σ' "lk" = σ "lk" ∧
      AInv num_proc num_chan ({ d.toAData with
        abtcb := setAt d.abtcb d.cid (.AbTCBValid ts q)
        abq := setAt d.abq q (.AbQValid (d.cid :: lq)) } : AData) := by
  have hnp : num_proc < 2 ^ 32 := np_lt hL.qlay
  obtain ⟨a1, hss, henq⟩ := park_factors (np := num_proc) (nc := num_chan) (a := d.toAData) hpg hipt hcid hq
    hcv.1 hcv.2 hts hlq
  obtain ⟨l1, b1, r1, c1, m1, -⟩ := (getCuridC εR c i0 hL (F := fun _ => False) "proc_index" (by decide)
    σ d).2 l b hlk hcs hM
  obtain ⟨l2, b2, r2, c2, m2⟩ := setStateC εR c i0 hL (σ := σ.set "proc_index" (BitVec.ofNat 32 d.cid))
    (ie := .var "proc_index") (ve := .const (BitVec.ofNat 32 sv)) (n := d.cid) (sv := sv)
    (by simpa [Locals.set] using hlk) c1 m1 (by simp [Expr.eval, Locals.set]) rfl hss
  have hI1 := set_state0_keeps hss hI
  obtain ⟨σ3, l3, b3, r3, c3, m3, k3⟩ := enqueueC εR c i0 hL
    (σ := (σ.set "proc_index" (BitVec.ofNat 32 d.cid)).set "_" 0) (n := q) (i := d.cid)
    (by simpa [Locals.set] using hlk) c2 m2 (by simp [Locals.set, hcn]) (by simp [Locals.set]) hI1 henq
  exact ⟨σ3, l3, b3, Runs.seq r1 (Runs.seq r2 r3), c3, m3, by rw [k3]; simp [Locals.set],
    enqueue0_keeps henq hI1⟩

/-! ### `thread_yield` and `thread_sleep` -/

/-- **`thread_yield` on the kernel machine.** -/
theorem thread_yield_run (code : Nat → Stmt KPrim)
    (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {σ : Locals} {K : Cont KPrim}
    {l : RLog} {b : Region} {d : KData} {ql : List Nat} {la : Nat} (hlk : (σ "lk").toNat = i0)
    (hcs : CS1 c i0 l b) (hM : MC d.toCData b) (hI : AInv num_proc num_chan d.toAData)
    (hcid : d.cid < num_proc) (hcv : CurIDValid d.toCData) (hpg : d.pg = true) (hipt : d.ipt = true)
    (hq : d.abq num_chan = .AbQValid ql) (hla : ql.getLastD num_proc = la) (hne : la ≠ num_proc) :
    ∃ (σf : Locals) (l' : RLog) (b' : Region),
      (∀ z, frS z (yieldBodyS tb qb num_proc num_chan cidb) = true →
        frS z (schedBodyS tb qb num_proc num_chan cidb) = true → σf z = σ z) ∧
      KStar εR c code ⟨⟨threadYieldK tb qb num_proc num_chan cidb, K, σ⟩, d.kctxt, l⟩
        ⟨d.kctxt la, (yieldOut num_chan la ql ⟨.skip, K, σf.set "_" 0⟩ d).kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MC (yieldOut num_chan la ql ⟨.skip, K, σf.set "_" 0⟩ d).toCData b' ∧
      AInv num_proc num_chan (yieldOut num_chan la ql ⟨.skip, K, σf.set "_" 0⟩ d).toAData ∧
      CurIDValid (yieldOut num_chan la ql ⟨.skip, K, σf.set "_" 0⟩ d).toCData ∧ la < num_proc := by
  have hmem := last_mem hla hne
  have hlt : la < num_proc := q_lt hI.qc (Nat.le_refl _) hq hmem
  obtain ⟨s, hai⟩ := hI.inq la num_chan ql hlt (Nat.le_refl _) hq hmem
  have hcu := cused_of_inq hI hlt hai
  have hne2 : d.cid ≠ la := by
    intro e
    have h := hcv.2
    rw [e, hai] at h
    injection h with e1 e2
    omega
  obtain ⟨σ1, l1, b1, r1, c1, m1, k1, hI1⟩ := park_run εR c i0 hL
    (σ := σ.set "chan_index" (BitVec.ofNat 32 num_chan)) (sv := 0) (ts := .READY) (q := num_chan) (lq := ql)
    (by simpa [Locals.set] using hlk) hcs hM (by simp [Locals.set]) (Nat.le_refl _) hI hcid hpg hipt hcv rfl hq
  have hP : SchedPre num_proc num_chan (parkOut num_chan .READY ql d).toCData (d.cid :: ql) la :=
    ⟨hpg, hipt, setAt_eq _ _ _, last_cons hla hne _, hne, hcu,
      ⟨s, num_chan, by show setAt d.abtcb d.cid _ la = _; rw [setAt_ne _ _ (Ne.symm hne2)]; exact hai⟩,
      ⟨.READY, num_chan, setAt_eq _ _ _, by decide⟩, hne2⟩
  have hlk1 : (σ1 "lk").toNat = i0 := by rw [k1]; simpa [Locals.set] using hlk
  obtain ⟨σf, l', b', hfr, hks, hcs', hM', hI', hcv', hlt'⟩ :=
    thread_sched_run εR c i0 code hL (σ := σ1) (K := K) (d := parkOut num_chan .READY ql d) hlk1 c1 m1 hI1
      hcid hP
  have e : ∀ rs, schedOut num_chan la (d.cid :: ql) rs (parkOut num_chan .READY ql d) =
      yieldOut num_chan la ql rs d := fun rs =>
    KData.ext5 rfl rfl (by
      show setAt (setAt d.abq num_chan _) num_chan _ = setAt d.abq num_chan _
      rw [setAt_setAt]) rfl rfl
  rw [e] at hks hM' hI' hcv'
  have hbody : Runs (rprimsA εR c) (yieldBodyS tb qb num_proc num_chan cidb) σ l σ1 l1 :=
    Runs.seq (Runs.assign _ _) r1
  refine ⟨σf, l', b', fun z hz1 hz2 => (hfr z hz2).trans (hbody.frame hz1), ?_, hcs', hM', hI', hcv', hlt⟩
  exact (kstar_seq hbody _ K d.kctxt).trans hks

/-- **`thread_sleep` on the kernel machine.** The channel is in `chan_index`. -/
theorem thread_sleep_run (code : Nat → Stmt KPrim)
    (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {σ : Locals} {K : Cont KPrim}
    {l : RLog} {b : Region} {d : KData} {n : Nat} {ql ql' : List Nat} {la : Nat} (hlk : (σ "lk").toNat = i0)
    (hcs : CS1 c i0 l b) (hM : MC d.toCData b) (hcn : σ "chan_index" = BitVec.ofNat 32 n)
    (hn : n < num_chan) (hI : AInv num_proc num_chan d.toAData) (hcid : d.cid < num_proc)
    (hcv : CurIDValid d.toCData) (hpg : d.pg = true) (hipt : d.ipt = true)
    (hq : d.abq num_chan = .AbQValid ql) (hq' : d.abq n = .AbQValid ql') (hla : ql.getLastD num_proc = la)
    (hne : la ≠ num_proc) :
    ∃ (σf : Locals) (l' : RLog) (b' : Region),
      (∀ z, frS z (parkS tb qb num_proc cidb 2) = true →
        frS z (schedBodyS tb qb num_proc num_chan cidb) = true → σf z = σ z) ∧
      KStar εR c code ⟨⟨threadSleepK tb qb num_proc num_chan cidb, K, σ⟩, d.kctxt, l⟩
        ⟨d.kctxt la, (sleepOut num_chan n la ql ql' ⟨.skip, K, σf.set "_" 0⟩ d).kctxt, l'⟩ ∧
      CS1 c i0 l' b' ∧ MC (sleepOut num_chan n la ql ql' ⟨.skip, K, σf.set "_" 0⟩ d).toCData b' ∧
      AInv num_proc num_chan (sleepOut num_chan n la ql ql' ⟨.skip, K, σf.set "_" 0⟩ d).toAData ∧
      CurIDValid (sleepOut num_chan n la ql ql' ⟨.skip, K, σf.set "_" 0⟩ d).toCData ∧ la < num_proc := by
  have hmem := last_mem hla hne
  have hlt : la < num_proc := q_lt hI.qc (Nat.le_refl _) hq hmem
  obtain ⟨s, hai⟩ := hI.inq la num_chan ql hlt (Nat.le_refl _) hq hmem
  have hcu := cused_of_inq hI hlt hai
  have hne2 : d.cid ≠ la := by
    intro e
    have h := hcv.2
    rw [e, hai] at h
    injection h with e1 e2
    omega
  obtain ⟨σ1, l1, b1, r1, c1, m1, k1, hI1⟩ := park_run εR c i0 hL (σ := σ) (sv := 2) (ts := .SLEEP) (q := n)
    (lq := ql') hlk hcs hM hcn (Nat.le_of_lt hn) hI hcid hpg hipt hcv rfl hq'
  have hP : SchedPre num_proc num_chan (parkOut n .SLEEP ql' d).toCData ql la :=
    ⟨hpg, hipt, by show setAt d.abq n _ num_chan = _; rw [setAt_ne _ _ (Nat.ne_of_gt hn)]; exact hq,
      hla, hne, hcu,
      ⟨s, num_chan, by show setAt d.abtcb d.cid _ la = _; rw [setAt_ne _ _ (Ne.symm hne2)]; exact hai⟩,
      ⟨.SLEEP, n, setAt_eq _ _ _, by decide⟩, hne2⟩
  have hlk1 : (σ1 "lk").toNat = i0 := by rw [k1]; exact hlk
  obtain ⟨σf, l', b', hfr, hks, hcs', hM', hI', hcv', hlt'⟩ :=
    thread_sched_run εR c i0 code hL (σ := σ1) (K := K) (d := parkOut n .SLEEP ql' d) hlk1 c1 m1 hI1 hcid hP
  refine ⟨σf, l', b', fun z hz1 hz2 => (hfr z hz2).trans (r1.frame hz1), ?_, hcs', hM', hI', hcv', hlt⟩
  exact (kstar_seq r1 _ K d.kctxt).trans hks

end Code

end PSched
