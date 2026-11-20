import CertiKOS.PIPC
import CertiKOS.FlatMem

/-!
# mCertiKOS `PIPC`: synchronous receive, ported

Ported from `objects/ObjSyncIPC.v`: `syncreceive_chan_spec`. Ported from
`proc/PIPCIntroCSource.v`: the code of `syncreceive_chan`.

The receiver looks at the sender's channel. If the sender is sending to it,
it copies the sender's buffer into its own (`flatmem_copy`), writes the count
received into the sender's channel, marks the channel as answered, and wakes
the sender, which sleeps on its own queue.

* `matchC_all`, `matchC_setPT`, `stepPC`: a step of the page-table layers is a
  step in the state with threads (the step form of `liftPC`).
* `flatmemCopyI`: `flatmem_copy` in the state with the channels.
* `recvPre_step`: the copy and the three channel writes.
* `syncReceive_triple`: **`syncreceive_chan` refines its specification.** It
  calls `get_curid`, `get_state`, the channel accessors, `get_kernel_pa`,
  `flatmem_copy` and `thread_wakeup` through their steps and triples.

The code follows the Clight that mCertiKOS verifies: `flatmem_copy` gets the
sender's buffer as its source. The C in the comment has the two swapped.

What differs: as for the send, the theorem assumes `num_proc ≤ num_chan` (one
constant in mCertiKOS). It also assumes the invariants of the queues
(`AInv`), which `thread_wakeup` needs; mCertiKOS has them as invariants of
the layer.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PIPC

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched FlatMem
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## Specification (`ObjSyncIPC.v`) -/

/-- The state after the copy: flat memory is `p`'s, and the sender's channel
says "answered, `arecv` words received". -/
def recvDone (num_chan fromid arecv : Nat) (p : PTData) (d : IData) : IData :=
  { d with
    toPTData := p
    syncchpool := setAt d.syncchpool fromid
      (.SyncChanValid (BitVec.ofNat 32 num_chan) 0 (BitVec.ofNat 32 arecv)) }

/-- **`syncreceive_chan_spec`**: receive from `fromid` into the buffer at
`vaddr`, at most `rcount` words. -/
def syncreceive_chan_spec (num_proc num_chan fromid vaddr rcount : Nat) (d : IData) : Option (IData × Nat) :=
  if d.pg = true ∧ d.ipt = true ∧ fromid < num_proc then
    match d.abtcb fromid with
    | .AbTCBUndef => none
    | .AbTCBValid st _ =>
      if st = .DEAD then some (d, 1024 + 2)
      else
        match d.syncchpool fromid with
        | .SyncChanUndef => none
        | .SyncChanValid to spaddr scount =>
          if to.toNat = d.cid then
            match get_kernel_pa_spec num_proc d.cid vaddr d with
            | none => none
            | some rbuffpa =>
              match flatmem_copy_spec (min scount.toNat rcount) spaddr.toNat rbuffpa d.toPTData with
              | none => none
              | some p =>
                match thread_wakeup_spec num_proc num_chan fromid
                    (recvDone num_chan fromid (min scount.toNat rcount) p d).toAData with
                | none => none
                | some a3 =>
                  some ({ recvDone num_chan fromid (min scount.toNat rcount) p d with toAData := a3 },
                    min scount.toNat rcount)
          else some (d, 1024 + 3)
  else none

/-! ## The code (`PIPCIntroCSource.v`) -/

/-- The copy and the answer in the sender's channel:
```
rbuffpa = r;
flatmem_copy(arecvcount, sbuffpa, rbuffpa);
set_sync_chan_to(pid, NUM_CHAN); set_sync_chan_paddr(pid, 0); set_sync_chan_count(pid, arecvcount);
```
then the argument of `thread_wakeup`. -/
def recvPreS (fb ipb num_chan : Nat) : Stmt APrim :=
  .seq (.assign "rbuffpa" (.var "r"))
  (.seq (.assign "len" (.var "arecvcount"))
  (.seq (.assign "from" (.var "sbuffpa"))
  (.seq (.assign "to" (.var "rbuffpa"))
  (.seq (flatmemCopyS fb)
  (.seq (setSyncToS ipb (.var "pid") (.const (BitVec.ofNat 32 num_chan)))
  (.seq (setSyncPaddrS ipb (.var "pid") (.const 0))
  (.seq (setSyncCountS ipb (.var "pid") (.var "arecvcount"))
    (.assign "chan_index" (.var "pid")))))))))

/-- `…; thread_wakeup(pid); r = arecvcount;` -/
def recvCopyS (tb qb fb ipb num_proc num_chan : Nat) : Stmt APrim :=
  .seq (recvPreS fb ipb num_chan)
    (.seq (threadWakeupS tb qb num_proc num_chan) (.assign "r" (.var "arecvcount")))

/-- ```
myid = get_curid(); sender_state = get_state(pid);
if (sender_state == TCB_STATE_DEAD) r = MAX_BUFFSIZE + 2;
else {
  sender_to = get_sync_chan_to(pid);
  if (sender_to == myid) {
    sender_count = get_sync_chan_count(pid); sbuffpa = get_sync_chan_paddr(pid);
    arecvcount = (sender_count < rcount) ? sender_count : rcount;
    rbuffpa = get_kernel_pa(myid, vaddr);
    flatmem_copy(arecvcount, sbuffpa, rbuffpa);
    set_sync_chan_to(pid, NUM_CHAN); set_sync_chan_paddr(pid, 0); set_sync_chan_count(pid, arecvcount);
    thread_wakeup(pid);
    r = arecvcount;
  } else r = MAX_BUFFSIZE + 3;
}
``` -/
def syncReceiveS (tb qb cidb pb fb ipb num_proc num_chan : Nat) : Stmt APrim :=
  .seq (getCuridS cidb "myid")
    (.seq (getTStateS tb "sender_state" (.var "pid"))
      (.ite (.bin .eq (.var "sender_state") (.const 3))
        (.assign "r" (.const 1026))
        (.seq (getSyncToS ipb "sender_to" (.var "pid"))
          (.ite (.bin .eq (.var "sender_to") (.var "myid"))
            (.seq (getSyncCountS ipb "sender_count" (.var "pid"))
              (.seq (getSyncPaddrS ipb "sbuffpa" (.var "pid"))
                (.seq (.ite (.bin .ltu (.var "sender_count") (.var "rcount"))
                    (.assign "arecvcount" (.var "sender_count")) (.assign "arecvcount" (.var "rcount")))
                  (.seq (.assign "n" (.var "myid"))
                    (.seq (getKernelPaS pb fb) (recvCopyS tb qb fb ipb num_proc num_chan))))))
            (.assign "r" (.const 1027))))))

/-- The cells `syncreceive_chan` may write: the channels, the control blocks
and queues, and flat memory. -/
def RecvF (tb num_proc qb num_chan ipb fb : Nat) (k : Nat) : Prop :=
  (IPF ipb num_chan k ∨ QTF tb num_proc qb num_chan k) ∨ fb ≤ k

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb : Nat}

local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb
local notation "MI" => MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb

/-! ### The page-table layers, as steps in the state with threads -/

theorem matchC_all {d : CData} {b : Region} (hM : MC d b) :
    MatchAll maxpage num_id cb num_proc pb ib fb ida d.toPTData b := by
  obtain ⟨⟨q, hQ, hS, -, -⟩, -⟩ := hM
  have eP : d.toPTData = q.toPTData := congrArg SData.toPTData hS
  rw [eP]; exact hQ.t.s.all

/-- A new page-table state under the same threads, queues and current thread.
The cells between the containers and the shared-memory table (the memory map
and the two register words) may change. -/
theorem matchC_setPT (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {d : CData}
    {b b' : Region} {p : PTData} (hM : MC d b)
    (hA' : MatchAll maxpage num_id cb num_proc pb ib fb ida p b')
    (hgap : ∀ k, sb ≤ k → k < pb → b' k = b k) (hpg : p.pg = true → d.pg = true) :
    MC { d with toPTData := p } b' := by
  obtain ⟨⟨q, hQ, hS, hR, hInv⟩, hcid⟩ := hM
  have hSL := hL.qlay.tlay.slay
  have := hSL.hsb; have := hSL.hse; have := hL.qlay.tlay.htb; have := hL.qlay.tlay.hte
  have := hL.qlay.hqb; have := hL.qlay.hqe; have := hL.hcb; have := hL.hce
  have eP : d.toPTData = q.toPTData := congrArg SData.toPTData hS
  refine ⟨⟨({ q with toPTData := p } : QData), ⟨⟨⟨hA', fun q1 q2 g1 g2 => ?_⟩, fun j hj => ?_⟩, fun j hj => ?_⟩,
      ?_, hR, fun hpg' => hInv ?_⟩, ?_⟩
  · have hlt := scell_lt (sb := sb) g1 g2 (show 2 < 3 by decide)
    have e : ∀ k, k < 3 → b' (scell sb num_proc q1 q2 k) = b (scell sb num_proc q1 q2 k) := fun k hk =>
      hgap _ (by unfold scell at *; omega) (by unfold scell at *; omega)
    show MatchSMS (q.smspool q1 q2) _ _ _
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
    exact hQ.t.s.sp q1 q2 g1 g2
  · show MatchTCB (q.tcb j) _ _ _
    rw [hgap _ (by unfold tcell; omega) (by unfold tcell; omega),
      hgap _ (by unfold tcell; omega) (by unfold tcell; omega),
      hgap _ (by unfold tcell; omega) (by unfold tcell; omega)]
    exact hQ.t.tp j hj
  · show MatchTDQ (q.tdq j) _ _
    rw [hgap _ (by unfold qcell; omega) (by unfold qcell; omega),
      hgap _ (by unfold qcell; omega) (by unfold qcell; omega)]
    exact hQ.qp j hj
  · show ({ d.toSData with toPTData := p } : SData) = { q.toSData with toPTData := p }
    rw [hS]
  · show q.toPTData.pg = true
    rw [← eP]; exact hpg hpg'
  · show d.cid = (b' cidb).toNat
    rw [hgap cidb (by omega) (by omega)]; exact hcid

variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

/-- **A step of the page-table layers is a step in the state with threads**,
if it writes only their cells and keeps `pg`. -/
theorem stepPC (hL : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb) {s : Stmt APrim}
    {σ σ' : Locals} {d : CData} {p : PTData}
    (h : Step εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) F s σ d.toPTData σ' p)
    (hF : ∀ k, F k → k < cb + 5 * num_id ∨ pb ≤ k) (hpg : p.pg = d.pg) :
    Step εR c i0 MC F s σ d σ' { d with toPTData := p } := by
  have := hL.qlay.tlay.slay.hsb
  refine ⟨h.1, fun l b hlk hcs hM => ?_⟩
  obtain ⟨l', b', hr, hcs', hA', hf⟩ := h.2 l b hlk hcs (matchC_all hM)
  exact ⟨l', b', hr, hcs', matchC_setPT hL hM hA' (fun k h1 h2 => hf k (fun hk => by have := hF k hk; omega))
    (fun h' => by rw [← hpg]; exact h'), hf⟩

/-- **`flatmem_copy` in the state with the channels.** -/
theorem flatmemCopyI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hF : ∀ k, fb ≤ k → F k) {σ : Locals} {d : IData} {p : PTData} {count src dst : Nat}
    (hlen : σ "len" = BitVec.ofNat 32 count) (hsrc : σ "from" = BitVec.ofNat 32 src)
    (hdst : σ "to" = BitVec.ofNat 32 dst) (hs : flatmem_copy_spec count src dst d.toPTData = some p) :
    ∃ σ', Step εR c i0 MI F (flatmemCopyS fb) σ d σ' { d with toPTData := p } ∧
      ∀ z, z ≠ "i" → z ≠ "v" → z ≠ "_" → σ' z = σ z := by
  have hLay := hL.clay.qlay.tlay.slay.lay
  obtain ⟨σ', h, hfr⟩ := flatmemCopy_step (ida := ida) εR c i0 hLay (F := fun k => fb ≤ k) (fun _ h => h) hlen
    hsrc hdst hs
  obtain ⟨hp, rfl⟩ := flatmem_copy_HP hs
  have hfp : ∀ k, fb ≤ k → pb ≤ k := fun k hk => by have := hLay.hib; have := hLay.hfb; omega
  exact ⟨σ', (stepCI εR c i0 hL (stepPC εR c i0 hL.clay (d := d.toCData) h (fun k hk => Or.inr (hfp k hk)) rfl)
    (fun k hk => Or.inr (hfp k hk))).widen hF, hfr⟩

/-! ### The copy and the answer -/

/-- **The copy and the three channel writes.** The receiver's buffer is in
`r`, the sender's in `sbuffpa`, the count in `arecvcount`. -/
theorem recvPre_step (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hF1 : ∀ k, IPF ipb num_chan k → F k) (hF2 : ∀ k, fb ≤ k → F k) {σ : Locals} {d : IData}
    {fromid rbuffpa arecv : Nat} {t pa cn : Val} {p : PTData} (hfc : fromid < num_chan)
    (hpid : σ "pid" = BitVec.ofNat 32 fromid) (hr : σ "r" = BitVec.ofNat 32 rbuffpa)
    (har : σ "arecvcount" = BitVec.ofNat 32 arecv) (hsb : σ "sbuffpa" = pa)
    (hch : d.syncchpool fromid = .SyncChanValid t pa cn)
    (hcp : flatmem_copy_spec arecv pa.toNat rbuffpa d.toPTData = some p) :
    ∃ σ', Step εR c i0 MI F (recvPreS fb ipb num_chan) σ d σ' (recvDone num_chan fromid arecv p d) ∧
      σ' "chan_index" = BitVec.ofNat 32 fromid ∧ σ' "arecvcount" = BitVec.ofNat 32 arecv := by
  let σ1 := σ.set "rbuffpa" (BitVec.ofNat 32 rbuffpa)
  let σ2 := σ1.set "len" (BitVec.ofNat 32 arecv)
  let σ3 := σ2.set "from" (BitVec.ofNat 32 pa.toNat)
  let σ4 := σ3.set "to" (BitVec.ofNat 32 rbuffpa)
  have s1 : Step εR c i0 MI F (.assign "rbuffpa" (.var "r")) σ d σ1 d :=
    Step.assign' "rbuffpa" (by decide) _ hr
  have s2 : Step εR c i0 MI F (.assign "len" (.var "arecvcount")) σ1 d σ2 d :=
    Step.assign' "len" (by decide) _ (by simp [σ1, Expr.eval, Locals.set, har])
  have s3 : Step εR c i0 MI F (.assign "from" (.var "sbuffpa")) σ2 d σ3 d :=
    Step.assign' "from" (by decide) _ (by simp [σ2, σ1, Expr.eval, Locals.set, hsb])
  have s4 : Step εR c i0 MI F (.assign "to" (.var "rbuffpa")) σ3 d σ4 d :=
    Step.assign' "to" (by decide) _ (by simp [σ3, σ2, σ1, Expr.eval, Locals.set])
  obtain ⟨σ5, s5, hfr5⟩ := flatmemCopyI (ida := ida) εR c i0 hL hF2 (σ := σ4) (d := d) (count := arecv)
    (src := pa.toNat) (dst := rbuffpa) (by simp [σ4, σ3, σ2, Locals.set]) (by simp [σ4, σ3, Locals.set])
    (by simp [σ4]) hcp
  have hpid5 : σ5 "pid" = BitVec.ofNat 32 fromid := by
    rw [hfr5 "pid" (by decide) (by decide) (by decide)]; simp [σ4, σ3, σ2, σ1, Locals.set, hpid]
  have har5 : σ5 "arecvcount" = BitVec.ofNat 32 arecv := by
    rw [hfr5 "arecvcount" (by decide) (by decide) (by decide)]; simp [σ4, σ3, σ2, σ1, Locals.set, har]
  have hch1 : ({ d with toPTData := p } : IData).syncchpool fromid = .SyncChanValid t pa cn := hch
  have s6 := setSyncToI (ida := ida) εR c i0 hL hF1 (ie := .var "pid") (ve := .const (BitVec.ofNat 32 num_chan))
    (w := BitVec.ofNat 32 num_chan) (σ := σ5) (d := { d with toPTData := p }) hpid5 rfl hfc hch1
  have e6 : (Expr.var "pid").eval (σ5.set "_" 0) = BitVec.ofNat 32 fromid := by
    simp [Expr.eval, Locals.set, hpid5]
  have e7 : (Expr.var "pid").eval ((σ5.set "_" 0).set "_" 0) = BitVec.ofNat 32 fromid := by
    simp [Expr.eval, Locals.set, hpid5]
  have e7' : (Expr.var "arecvcount").eval ((σ5.set "_" 0).set "_" 0) = BitVec.ofNat 32 arecv := by
    simp [Expr.eval, Locals.set, har5]
  have e8 : (Expr.var "pid").eval (((σ5.set "_" 0).set "_" 0).set "_" 0) = BitVec.ofNat 32 fromid := by
    simp [Expr.eval, Locals.set, hpid5]
  refine ⟨_, Step.cast (s1.seq (s2.seq (s3.seq (s4.seq (s5.seq (Step.seq s6 (Step.seq
      (setSyncPaddrI εR c i0 hL hF1 (ie := .var "pid") (ve := .const 0) (w := 0) e6 rfl hfc (setAt_eq _ _ _))
      (Step.seq (setSyncCountI εR c i0 hL hF1 (ie := .var "pid") (ve := .var "arecvcount")
          (w := BitVec.ofNat 32 arecv) e7 e7' hfc (setAt_eq _ _ _))
        (Step.assign' "chan_index" (by decide) (.var "pid") (v := BitVec.ofNat 32 fromid) e8))))))))) rfl
    (IData.ext2 rfl ?_), by simp [Locals.set], by simp [Locals.set, har5]⟩
  show setAt (setAt (setAt d.syncchpool fromid _) fromid _) fromid _ = setAt d.syncchpool fromid _
  rw [setAt_setAt, setAt_setAt]

/-! ### `syncreceive_chan` -/

/-- **`syncreceive_chan` refines `syncreceive_chan_spec`.** The sender is in
`pid`, the receiver's buffer in `vaddr`, its length in `rcount`; the result is
in `r`. -/
theorem syncReceive_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hnpc : num_proc ≤ num_chan) (fromid vaddr rcount : Nat) (hva : vaddr < 2 ^ 32) (hrc32 : rcount < 2 ^ 32) :
    Triple εR c i0 MI (RecvF tb num_proc qb num_chan ipb fb)
      (fun σ d => σ "pid" = BitVec.ofNat 32 fromid ∧ σ "vaddr" = BitVec.ofNat 32 vaddr ∧
        σ "rcount" = BitVec.ofNat 32 rcount ∧ AInv num_proc num_chan d.toAData ∧
        ∃ d1 r, syncreceive_chan_spec num_proc num_chan fromid vaddr rcount d = some (d1, r))
      (syncReceiveS tb qb cidb pb fb ipb num_proc num_chan)
      (fun _ d σ' d' => ∃ r, syncreceive_chan_spec num_proc num_chan fromid vaddr rcount d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hpid, hvaddr, hrcount, hI, d', r, hs⟩
  have hnc : num_chan < 2 ^ 32 := by have := ipb_lt hL; omega
  have hcid32 : d.cid < 2 ^ 32 := by rw [hM.1.2]; exact (b cidb).isLt
  have hs0 := hs
  unfold syncreceive_chan_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ fromid < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨hpg, hipt, hfrom⟩ := hc
    have hfc : fromid < num_chan := by omega
    -- myid = get_curid()
    let σ1 := σ.set "myid" (BitVec.ofNat 32 d.cid)
    obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (getCuridI εR c i0 hL (F := RecvF tb num_proc qb num_chan ipb fb) "myid"
      (by decide) σ d).2 l b hlk hcs hM
    have hlk1 : (σ1 "lk").toNat = i0 := by simpa [σ1, Locals.set] using hlk
    cases ha : d.abtcb fromid with
    | AbTCBUndef => rw [ha] at hs; cases hs
    | AbTCBValid st b0 =>
      rw [ha] at hs
      simp only at hs
      have hsr := ThreadStatetoZ_range st
      -- sender_state = get_state(pid)
      let σ2 := σ1.set "sender_state" (BitVec.ofNat 32 (ThreadStatetoZ st))
      obtain ⟨l2, b2, r2, c2, m2, f2⟩ := (getStateI εR c i0 hL (F := RecvF tb num_proc qb num_chan ipb fb)
        "sender_state" (by decide) (ie := .var "pid") (σ := σ1) (by simp [σ1, Expr.eval, Locals.set, hpid])
        hpg hipt hfrom ha).2 l1 b1 hlk1 c1 m1
      have hts : σ2 "sender_state" = BitVec.ofNat 32 (ThreadStatetoZ st) := by simp [σ2]
      have hlk2 : (σ2 "lk").toNat = i0 := by simpa [σ2, σ1, Locals.set] using hlk
      by_cases hdead : st = .DEAD
      · rw [if_pos hdead] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨hd, hr⟩ := hs
        subst hd; subst hr
        refine ⟨_, l2, b2, d, Runs.seq r1 (Runs.seq r2 (Runs.ite_true (eqc_true hts (tsz_dead.2 hdead))
          (Runs.assign _ _))), c2, m2, by simp [σ2, σ1, Locals.set], fun k hk => (f2 k hk).trans (f1 k hk), _,
          hs0, by simp [Locals.set, Expr.eval]⟩
      · rw [if_neg hdead] at hs
        have g1 : (Expr.bin .eq (.var "sender_state") (.const 3)).eval σ2 = 0 :=
          eqc_false (b := 3) hts (by omega) (by decide) (fun e => hdead (tsz_dead.1 e))
        cases hch : d.syncchpool fromid with
        | SyncChanUndef => rw [hch] at hs; cases hs
        | SyncChanValid t pa cn =>
          rw [hch] at hs
          simp only at hs
          -- sender_to = get_sync_chan_to(pid)
          let σ3 := σ2.set "sender_to" t
          obtain ⟨l3, b3, r3, c3, m3, f3⟩ := (getSyncI εR c i0 hL (F := RecvF tb num_proc qb num_chan ipb fb)
            "sender_to" (by decide) (ie := .var "pid") (σ := σ2)
            (by simp [σ2, σ1, Expr.eval, Locals.set, hpid]) hfc hch).1.2 l2 b2 hlk2 c2 m2
          have hlk3 : (σ3 "lk").toNat = i0 := by simpa [σ3, σ2, σ1, Locals.set] using hlk
          by_cases hto : t.toNat = d.cid
          · rw [if_pos hto] at hs
            have ht : t = BitVec.ofNat 32 d.cid := val_of_toNat hto hcid32
            have g2 : ¬ (Expr.bin .eq (.var "sender_to") (.var "myid")).eval σ3 = 0 := by
              simp [Expr.eval, BinOp.eval, σ3, σ2, σ1, Locals.set, ht]
            cases hk : get_kernel_pa_spec num_proc d.cid vaddr d with
            | none => rw [hk] at hs; cases hs
            | some rbuffpa =>
              rw [hk] at hs
              simp only at hs
              cases hcp : flatmem_copy_spec (min cn.toNat rcount) pa.toNat rbuffpa d.toPTData with
              | none => rw [hcp] at hs; cases hs
              | some p =>
                rw [hcp] at hs
                simp only at hs
                cases hwk : thread_wakeup_spec num_proc num_chan fromid
                    (recvDone num_chan fromid (min cn.toNat rcount) p d).toAData with
                | none => rw [hwk] at hs; cases hs
                | some a3 =>
                  rw [hwk] at hs
                  simp only [Option.some.injEq, Prod.mk.injEq] at hs
                  obtain ⟨hd, hr⟩ := hs
                  subst hd; subst hr
                  -- sender_count, sbuffpa
                  let σ4 := σ3.set "sender_count" cn
                  obtain ⟨l4, b4, r4, c4, m4, f4⟩ := (getSyncI εR c i0 hL
                    (F := RecvF tb num_proc qb num_chan ipb fb) "sender_count" (by decide) (ie := .var "pid")
                    (σ := σ3) (by simp [σ3, σ2, σ1, Expr.eval, Locals.set, hpid]) hfc hch).2.2.2 l3 b3 hlk3 c3 m3
                  have hlk4 : (σ4 "lk").toNat = i0 := by simpa [σ4, σ3, σ2, σ1, Locals.set] using hlk
                  let σ5 := σ4.set "sbuffpa" pa
                  obtain ⟨l5, b5, r5, c5, m5, f5⟩ := (getSyncI εR c i0 hL
                    (F := RecvF tb num_proc qb num_chan ipb fb) "sbuffpa" (by decide) (ie := .var "pid")
                    (σ := σ4) (by simp [σ4, σ3, σ2, σ1, Expr.eval, Locals.set, hpid]) hfc hch).2.1.2 l4 b4 hlk4
                    c4 m4
                  -- arecvcount = min(sender_count, rcount)
                  let σ6 := σ5.set "arecvcount" (BitVec.ofNat 32 (min cn.toNat rcount))
                  have r6 : Runs (rprimsA εR c) (.ite (.bin .ltu (.var "sender_count") (.var "rcount"))
                      (.assign "arecvcount" (.var "sender_count")) (.assign "arecvcount" (.var "rcount")))
                      σ5 l5 σ6 l5 := by
                    have hcn : σ5 "sender_count" = BitVec.ofNat 32 cn.toNat := by simp [σ5, σ4, Locals.set]
                    have hrc5 : σ5 "rcount" = BitVec.ofNat 32 rcount := by
                      simp [σ5, σ4, σ3, σ2, σ1, Locals.set, hrcount]
                    have hg := ltu_eval (σ := σ5) (ea := .var "sender_count") (eb := .var "rcount") hcn hrc5
                      cn.isLt hrc32
                    by_cases hlt : cn.toNat < rcount
                    · rw [if_pos hlt] at hg
                      have hmin : min cn.toNat rcount = cn.toNat := by omega
                      show Runs _ _ σ5 l5 (σ5.set "arecvcount" (BitVec.ofNat 32 (min cn.toNat rcount))) l5
                      rw [hmin]
                      exact Runs.ite_true (by rw [hg]; decide) (asg_run "arecvcount" _ hcn)
                    · rw [if_neg hlt] at hg
                      have hmin : min cn.toNat rcount = rcount := by omega
                      show Runs _ _ σ5 l5 (σ5.set "arecvcount" (BitVec.ofNat 32 (min cn.toNat rcount))) l5
                      rw [hmin]
                      exact Runs.ite_false hg (asg_run "arecvcount" _ hrc5)
                  -- rbuffpa = get_kernel_pa(myid, vaddr)
                  let σ7 := σ6.set "n" (BitVec.ofNat 32 d.cid)
                  have r7 : Runs (rprimsA εR c) (.assign "n" (.var "myid")) σ6 l5 σ7 l5 :=
                    asg_run "n" _ (by simp [σ6, σ5, σ4, σ3, σ2, σ1, Expr.eval, Locals.set])
                  have hlk7 : (σ7 "lk").toNat = i0 := by
                    simpa [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Locals.set] using hlk
                  obtain ⟨σ8, l8, b8, d8, r8, c8, m8, k8, f8, hd8, v8, hv8, hv832, hr8, hfr8⟩ :=
                    getKernelPa_triple εR c i0 hL d.cid vaddr hva σ7 l5 b5 d hlk7 c5 m5
                      ⟨by simp [σ7], by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Locals.set, hvaddr], rbuffpa, hk⟩
                  rw [hk] at hv8
                  simp only [Option.some.injEq] at hv8
                  subst hv8
                  have e8 := hd8.symm
                  subst e8
                  have hlk8 : (σ8 "lk").toNat = i0 := by rw [k8]; exact hlk7
                  -- the copy and the answer
                  obtain ⟨σ9, hst, hci9, har9⟩ := recvPre_step (ida := ida) εR c i0 hL
                    (F := RecvF tb num_proc qb num_chan ipb fb) (fun k h => Or.inl (Or.inl h))
                    (fun k h => Or.inr h) (σ := σ8) (d := d) (fromid := fromid) (rbuffpa := rbuffpa)
                    (arecv := min cn.toNat rcount) hfc
                    (by rw [hfr8 "pid" rfl]; simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Locals.set, hpid]) hr8
                    (by rw [hfr8 "arecvcount" rfl]; simp [σ7, σ6, Locals.set])
                    (by rw [hfr8 "sbuffpa" rfl]; simp [σ7, σ6, σ5, Locals.set]) hch hcp
                  obtain ⟨l9, b9, r9, c9, m9, f9⟩ := hst.2 l8 b8 hlk8 c8 m8
                  have hlk9 : (σ9 "lk").toNat = i0 := by rw [hst.1]; exact hlk8
                  -- thread_wakeup(pid)
                  obtain ⟨hp, hpe⟩ := flatmem_copy_HP hcp
                  have hAC : p.AC = d.AC := by rw [hpe]
                  have hI' : AInv num_proc num_chan (recvDone num_chan fromid (min cn.toNat rcount) p d).toAData :=
                    ⟨hI.tc, hI.qc, by show NotInQ num_proc p.AC d.abtcb; rw [hAC]; exact hI.niq, hI.cnt, hI.inq⟩
                  have T := liftCI (ida := ida) εR c i0 hL (liftA εR c i0 hL.clay
                    (thread_wakeup_triple εR c i0 hL.clay.qlay fromid) (qtf_ne hL.clay))
                    (fun k hk => Or.inl (by
                      have := hL.clay.hcb; have := hL.clay.qlay.hqb
                      rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega))
                  obtain ⟨σ10, l10, b10, d10, r10, c10, m10, k10, f10, cc, hd10, a, hcc, ha10⟩ :=
                    T σ9 l9 b9 _ hlk9 c9 m9 ⟨hci9, hI', a3, hwk⟩
                  have ea : a = a3 := Option.some.inj (ha10.symm.trans hwk)
                  subst ea; subst hcc; subst hd10
                  -- r = arecvcount
                  have har10 : σ10 "arecvcount" = BitVec.ofNat 32 (min cn.toNat rcount) :=
                    (r10.frame rfl).trans har9
                  refine ⟨σ10.set "r" (BitVec.ofNat 32 (min cn.toNat rcount)), l10, b10, _,
                    Runs.seq r1 (Runs.seq r2 (Runs.ite_false g1 (Runs.seq r3 (Runs.ite_true g2 (Runs.seq r4
                      (Runs.seq r5 (Runs.seq r6 (Runs.seq r7 (Runs.seq r8 (Runs.seq r9 (Runs.seq r10
                        (asg_run "r" _ har10)))))))))))), c10, m10, ?_, fun k hk => ?_, _, hs0, by simp⟩
                  · rw [Locals.set_other _ _ (by decide), k10, hst.1, k8]
                    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, Locals.set]
                  · rw [f10 k (fun h => hk (Or.inl (Or.inr h))), f9 k hk, f8 k (fun h => h), f5 k hk, f4 k hk,
                      f3 k hk, f2 k hk, f1 k hk]
          · rw [if_neg hto] at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨hd, hr⟩ := hs
            subst hd; subst hr
            have ht : t ≠ BitVec.ofNat 32 d.cid := fun e => hto (by rw [e]; exact tn hcid32)
            have g2 : (Expr.bin .eq (.var "sender_to") (.var "myid")).eval σ3 = 0 := by
              simp [Expr.eval, BinOp.eval, σ3, σ2, σ1, Locals.set, ht]
            refine ⟨_, l3, b3, d, Runs.seq r1 (Runs.seq r2 (Runs.ite_false g1 (Runs.seq r3 (Runs.ite_false g2
              (Runs.assign _ _))))), c3, m3, by simp [σ3, σ2, σ1, Locals.set],
              fun k hk => (f3 k hk).trans ((f2 k hk).trans (f1 k hk)), _, hs0, by simp [Locals.set, Expr.eval]⟩
  · rw [if_neg hc] at hs; cases hs

end Code

end PIPC
