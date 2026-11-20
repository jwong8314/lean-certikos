import CertiKOS.PIPCIntro

/-!
# mCertiKOS `PIPC`: synchronous send, ported

Ported from `objects/ObjSyncIPC.v`: `syncsendto_chan_pre_spec`,
`syncsendto_chan_post_spec`. Ported from `proc/PIPCIntroCSource.v`: the code
of `syncsendto_chan_pre` and `syncsendto_chan_post`.

A send is in two halves around a sleep. `syncsendto_chan_pre` publishes the
buffer in the sender's channel: the receiver, the kernel's address of the
buffer, and the length (at most 1024 words). After the sender is woken,
`syncsendto_chan_post` reads back what the receiver left: the count
received, or an error if nobody received.

* `syncSendPre_triple`: **`syncsendto_chan_pre` refines its specification.**
  It calls `get_state`, `get_curid`, `get_kernel_pa` and the channel
  accessors through their triples and steps.
* `syncSendPost_triple`: **`syncsendto_chan_post` refines its
  specification.**

The code follows the Clight that mCertiKOS verifies, which differs from the C
in its comment: it returns the sender's id, not 0.

What differs: the code compares the receiver with `num_chan` and the
specification bounds it by `num_proc`; they are one constant in mCertiKOS,
and the theorem assumes `num_proc ≤ num_chan`. The current thread is assumed
below `num_chan` (mCertiKOS's `valid_curid`).

`syncreceive_chan`, which copies the buffer, is in `PIPCRecv.lean`.
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

/-! ## Specifications (`ObjSyncIPC.v`) -/

/-- **`syncsendto_chan_post_spec`**: what the receiver left in the sender's
channel. -/
def syncsendto_chan_post_spec (num_chan : Nat) (d : IData) : Option (IData × Nat) :=
  if d.pg = true ∧ d.ipt = true then
    match d.syncchpool d.cid with
    | .SyncChanUndef => none
    | .SyncChanValid to paddr count =>
      if to.toNat = num_chan then some (d, count.toNat)
      else some ({ d with
        syncchpool := setAt d.syncchpool d.cid (.SyncChanValid (BitVec.ofNat 32 num_chan) paddr count) },
        1024 + 3)
  else none

/-- **`syncsendto_chan_pre_spec`**: publish the buffer for `chid`. -/
def syncsendto_chan_pre_spec (num_proc num_chan chid vaddr scount : Nat) (d : IData) : Option (IData × Nat) :=
  if d.pg = true ∧ d.ipt = true ∧ chid < num_proc then
    match d.abtcb chid with
    | .AbTCBUndef => none
    | .AbTCBValid st _ =>
      if st = .DEAD then some (d, 1024 + 2)
      else
        match d.syncchpool d.cid with
        | .SyncChanUndef => none
        | .SyncChanValid to _ _ =>
          match get_kernel_pa_spec num_proc d.cid vaddr d with
          | none => none
          | some skpa =>
            if skpa ≤ 2 ^ 32 - 1 then
              if to.toNat = num_chan then
                some ({ d with
                  syncchpool := setAt d.syncchpool d.cid (.SyncChanValid (BitVec.ofNat 32 chid)
                    (BitVec.ofNat 32 skpa) (BitVec.ofNat 32 (min scount 1024))) }, d.cid)
              else none
            else none
  else none

/-! ## The code (`PIPCIntroCSource.v`) -/

/-- ```
myid = get_curid(); to = get_sync_chan_to(myid);
if (to == NUM_CHAN) r = get_sync_chan_count(myid);
else { set_sync_chan_to(myid, NUM_CHAN); r = MAX_BUFFSIZE + 3; }
``` -/
def syncSendPostS (cidb ipb num_chan : Nat) : Stmt APrim :=
  .seq (getCuridS cidb "myid")
    (.seq (getSyncToS ipb "to" (.var "myid"))
      (.ite (.bin .eq (.var "to") (.const (BitVec.ofNat 32 num_chan)))
        (getSyncCountS ipb "r" (.var "myid"))
        (.seq (setSyncToS ipb (.var "myid") (.const (BitVec.ofNat 32 num_chan))) (.assign "r" (.const 1027)))))

/-- The part of `syncsendto_chan_pre` after `get_kernel_pa`. -/
def sendPreTailS (ipb num_chan : Nat) : Stmt APrim :=
  .seq (.ite (.bin .ltu (.var "scount") (.const 1024))
      (.seq (setSyncPaddrS ipb (.var "myid") (.var "sender_kpa"))
        (setSyncCountS ipb (.var "myid") (.var "scount")))
      (.seq (setSyncPaddrS ipb (.var "myid") (.var "sender_kpa"))
        (setSyncCountS ipb (.var "myid") (.const 1024))))
    (.seq (getSyncToS ipb "tmp1" (.var "myid"))
      (.seq (.ite (.bin .eq (.var "tmp1") (.const (BitVec.ofNat 32 num_chan)))
          (setSyncToS ipb (.var "myid") (.var "pid")) .skip)
        (.assign "r" (.var "myid"))))

/-- ```
target_state = get_state(pid);
if (target_state == 3) r = MAX_BUFFSIZE + 2;
else if (pid < NUM_CHAN) {
  myid = get_curid(); sender_kpa = get_kernel_pa(myid, vaddr);
  if (scount < MAX_BUFFSIZE) { set_sync_chan_paddr(myid, sender_kpa); set_sync_chan_count(myid, scount); }
  else { set_sync_chan_paddr(myid, sender_kpa); set_sync_chan_count(myid, MAX_BUFFSIZE); }
  tmp1 = get_sync_chan_to(myid);
  if (tmp1 == NUM_CHAN) set_sync_chan_to(myid, pid);
  r = myid;
} else r = MAX_BUFFSIZE + 1;
``` -/
def syncSendPreS (tb cidb pb fb ipb num_chan : Nat) : Stmt APrim :=
  .seq (getTStateS tb "target_state" (.var "pid"))
    (.ite (.bin .eq (.var "target_state") (.const 3))
      (.assign "r" (.const 1026))
      (.ite (.bin .ltu (.var "pid") (.const (BitVec.ofNat 32 num_chan)))
        (.seq (getCuridS cidb "myid")
          (.seq (.assign "n" (.var "myid"))
            (.seq (getKernelPaS pb fb)
              (.seq (.assign "sender_kpa" (.var "r")) (sendPreTailS ipb num_chan)))))
        (.assign "r" (.const 1025))))

theorem IData.ext2 {d1 d2 : IData} (h1 : d1.toCData = d2.toCData) (h2 : d1.syncchpool = d2.syncchpool) :
    d1 = d2 := by
  obtain ⟨c1, s1⟩ := d1
  obtain ⟨c2, s2⟩ := d2
  change c1 = c2 at h1; change s1 = s2 at h2
  subst h1; subst h2; rfl

theorem tsz_dead {st : ThreadState} : ThreadStatetoZ st = 3 ↔ st = .DEAD := by
  cases st <;> simp [ThreadStatetoZ]

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MC" => MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb
local notation "MI" => MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb

/-! ### The layers below, as steps in this state -/

/-- `get_curid`. -/
theorem getCuridI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb) (x : Ident)
    (hx : x ≠ "lk") (σ : Locals) (d : IData) :
    Step εR c i0 MI F (getCuridS cidb x) σ d (σ.set x (BitVec.ofNat 32 d.cid)) d :=
  (stepCI εR c i0 hL (getCuridC εR c i0 hL.clay (F := fun _ => False) x hx σ d.toCData)
    (fun _ h => h.elim)).widen (fun _ h => h.elim)

/-- `get_state`. -/
theorem getStateI (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb) (x : Ident)
    (hx : x ≠ "lk") {ie : Expr} {σ : Locals} {d : IData} {n : Nat} {st : ThreadState} {b0 : Int}
    (he : ie.eval σ = BitVec.ofNat 32 n) (hpg : d.pg = true) (hipt : d.ipt = true) (hn : n < num_proc)
    (ha : d.abtcb n = .AbTCBValid st b0) :
    Step εR c i0 MI F (getTStateS tb x ie) σ d (σ.set x (BitVec.ofNat 32 (ThreadStatetoZ st))) d := by
  have hsp : get_state0_spec num_proc n d.toAData = some (ThreadStatetoZ st) := by
    unfold get_state0_spec
    rw [if_pos ⟨hpg, hipt, hn⟩, ha]
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have T := liftCI (ida := ida) εR c i0 hL (liftA εR c i0 hL.clay (getState0_triple εR c i0 hL.clay.qlay x hx ie n)
    (fun _ h => h.elim)) (fun _ h => h.elim)
  obtain ⟨σ', l', b', d', hr, hcs', hM', -, hf, c1, hd', a, hc1, ha', v, hv, hσ'⟩ :=
    T σ l b d hlk hcs hM ⟨he, _, hsp⟩
  rw [hsp] at hv
  simp only [Option.some.injEq] at hv
  subst hv; subst hσ'
  have hd : d' = d := by rw [hd', hc1, ha']
  subst hd
  exact ⟨l', b', hr, hcs', hM', fun k _ => hf k (fun h => h)⟩

/-! ### `syncsendto_chan_post` -/

/-- **`syncsendto_chan_post` runs as its specification says.** -/
theorem syncSendPost_step (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    {σ : Locals} {d d' : IData} {r : Nat} (hcid : d.cid < num_chan)
    (hs : syncsendto_chan_post_spec num_chan d = some (d', r)) :
    ∃ σ', Step εR c i0 MI (IPF ipb num_chan) (syncSendPostS cidb ipb num_chan) σ d σ' d' ∧
      σ' "r" = BitVec.ofNat 32 r := by
  have hnc : num_chan < 2 ^ 32 := by have := ipb_lt hL; omega
  unfold syncsendto_chan_post_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true
  · rw [if_pos hc] at hs
    cases hch : d.syncchpool d.cid with
    | SyncChanUndef => rw [hch] at hs; cases hs
    | SyncChanValid t pa cn =>
      rw [hch] at hs
      simp only at hs
      have s1 := getCuridI (ida := ida) εR c i0 hL (F := IPF ipb num_chan) "myid" (by decide) σ d
      have e1 : (Expr.var "myid").eval ((σ.set "myid" (BitVec.ofNat 32 d.cid)).set "to" t) =
          BitVec.ofNat 32 d.cid := by simp [Expr.eval, Locals.set]
      have s2 := (getSyncI (ida := ida) εR c i0 hL (F := IPF ipb num_chan) "to" (by decide) (ie := .var "myid")
        (σ := σ.set "myid" (BitVec.ofNat 32 d.cid)) (by simp [Expr.eval, Locals.set]) hcid hch).1
      by_cases hto : t.toNat = num_chan
      · rw [if_pos hto] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨hd, hr⟩ := hs
        subst hd; subst hr
        have ht : t = BitVec.ofNat 32 num_chan := val_of_toNat hto hnc
        refine ⟨_, Step.seq s1 (Step.seq s2 (Step.ite_true (eq_true (by simp [Locals.set, ht]))
          (getSyncI εR c i0 hL "r" (by decide) e1 hcid hch).2.2)), ?_⟩
        simp [Locals.set]
      · rw [if_neg hto] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨hd, hr⟩ := hs
        subst hd; subst hr
        have ht : t ≠ BitVec.ofNat 32 num_chan := fun e => hto (by rw [e]; exact tn hnc)
        refine ⟨_, Step.seq s1 (Step.seq s2 (Step.ite_false (eq_false (by simp [Locals.set, ht]))
          (Step.seq (setSyncToI εR c i0 hL (fun _ h => h) e1 rfl hcid hch)
            (Step.assign "r" (by decide) (.const 1027))))), ?_⟩
        simp [Locals.set, Expr.eval]
  · rw [if_neg hc] at hs; cases hs

/-- **`syncsendto_chan_post` refines `syncsendto_chan_post_spec`.** -/
theorem syncSendPost_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb) :
    Triple εR c i0 MI (IPF ipb num_chan)
      (fun _ d => d.cid < num_chan ∧ ∃ d1 r, syncsendto_chan_post_spec num_chan d = some (d1, r))
      (syncSendPostS cidb ipb num_chan)
      (fun _ d σ' d' => ∃ r, syncsendto_chan_post_spec num_chan d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) :=
  Step.triple (fun σ d ⟨hcid, d1, r, hs⟩ => by
    obtain ⟨σ', h, hr⟩ := syncSendPost_step εR c i0 hL hcid hs
    exact ⟨σ', d1, h, r, hs, hr⟩)

/-! ### `syncsendto_chan_pre` -/

/-- The tail of `syncsendto_chan_pre`: the three channel writes. -/
theorem sendPreTail_step (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    {σ : Locals} {d : IData} {chid skpa scount : Nat} {t pa cn : Val} (hcid : d.cid < num_chan)
    (hmy : σ "myid" = BitVec.ofNat 32 d.cid) (hpid : σ "pid" = BitVec.ofNat 32 chid)
    (hkpa : σ "sender_kpa" = BitVec.ofNat 32 skpa) (hsc : σ "scount" = BitVec.ofNat 32 scount)
    (hsc32 : scount < 2 ^ 32) (hch : d.syncchpool d.cid = .SyncChanValid t pa cn)
    (hto : t.toNat = num_chan) :
    ∃ σ', Step εR c i0 MI (IPF ipb num_chan) (sendPreTailS ipb num_chan) σ d σ'
      { d with syncchpool := setAt d.syncchpool d.cid (.SyncChanValid (BitVec.ofNat 32 chid)
        (BitVec.ofNat 32 skpa) (BitVec.ofNat 32 (min scount 1024))) } ∧
      σ' "r" = BitVec.ofNat 32 d.cid := by
  have hnc : num_chan < 2 ^ 32 := by have := ipb_lt hL; omega
  have ht : t = BitVec.ofNat 32 num_chan := val_of_toNat hto hnc
  have hF : ∀ k, IPF ipb num_chan k → IPF ipb num_chan k := fun _ h => h
  -- the first two writes, whichever branch
  have hfirst : Step εR c i0 MI (IPF ipb num_chan)
      (.ite (.bin .ltu (.var "scount") (.const 1024))
        (.seq (setSyncPaddrS ipb (.var "myid") (.var "sender_kpa"))
          (setSyncCountS ipb (.var "myid") (.var "scount")))
        (.seq (setSyncPaddrS ipb (.var "myid") (.var "sender_kpa"))
          (setSyncCountS ipb (.var "myid") (.const 1024)))) σ d ((σ.set "_" 0).set "_" 0)
      { d with syncchpool := setAt d.syncchpool d.cid (.SyncChanValid t (BitVec.ofNat 32 skpa)
        (BitVec.ofNat 32 (min scount 1024))) } := by
    have hg := ltu_eval (σ := σ) (ea := .var "scount") (eb := .const 1024) (b := 1024) hsc rfl hsc32 (by decide)
    have w1 := setSyncPaddrI (ida := ida) εR c i0 hL hF (ie := .var "myid") (ve := .var "sender_kpa") (σ := σ) hmy hkpa
      hcid hch
    have e1 : (Expr.var "myid").eval (σ.set "_" 0) = BitVec.ofNat 32 d.cid := by
      simp [Expr.eval, Locals.set, hmy]
    by_cases hlt : scount < 1024
    · rw [if_pos hlt] at hg
      have hmin : min scount 1024 = scount := by omega
      rw [hmin]
      refine Step.cast (Step.ite_true (by rw [hg]; decide) (Step.seq w1
        (setSyncCountI εR c i0 hL hF e1 (ve := .var "scount") (by simp [Expr.eval, Locals.set, hsc]) hcid
          (setAt_eq _ _ _)))) rfl (IData.ext2 rfl (setAt_setAt _ _ _ _))
    · rw [if_neg hlt] at hg
      have hmin : min scount 1024 = 1024 := by omega
      rw [hmin]
      refine Step.cast (Step.ite_false hg (Step.seq w1
        (setSyncCountI εR c i0 hL hF e1 (ve := .const 1024) rfl hcid (setAt_eq _ _ _)))) rfl
        (IData.ext2 rfl (setAt_setAt _ _ _ _))
  have e2 : (Expr.var "myid").eval ((σ.set "_" 0).set "_" 0) = BitVec.ofNat 32 d.cid := by
    simp [Expr.eval, Locals.set, hmy]
  have s3 := (getSyncI (ida := ida) εR c i0 hL (F := IPF ipb num_chan) "tmp1" (by decide) (ie := .var "myid")
    (d := { d with syncchpool := setAt d.syncchpool d.cid (.SyncChanValid t (BitVec.ofNat 32 skpa)
      (BitVec.ofNat 32 (min scount 1024))) }) e2 hcid (setAt_eq _ _ _)).1
  have e3 : (Expr.var "myid").eval (((σ.set "_" 0).set "_" 0).set "tmp1" t) = BitVec.ofNat 32 d.cid := by
    simp [Expr.eval, Locals.set, hmy]
  have s4 := setSyncToI (ida := ida) εR c i0 hL hF (ie := .var "myid") (ve := .var "pid")
    (w := BitVec.ofNat 32 chid) (σ := ((σ.set "_" 0).set "_" 0).set "tmp1" t)
    (d := { d with syncchpool := setAt d.syncchpool d.cid (.SyncChanValid t (BitVec.ofNat 32 skpa)
      (BitVec.ofNat 32 (min scount 1024))) }) e3 (by simp [Expr.eval, Locals.set, hpid]) hcid (setAt_eq _ _ _)
  refine ⟨_, Step.cast (Step.seq hfirst (Step.seq s3 (Step.seq
    (Step.ite_true (eq_true (by simp [Locals.set, ht])) s4) (Step.assign "r" (by decide) (.var "myid"))))) rfl
    (IData.ext2 rfl (setAt_setAt _ _ _ _)), ?_⟩
  simp [Locals.set, Expr.eval, hmy]

/-- **`syncsendto_chan_pre` refines `syncsendto_chan_pre_spec`.** The
receiver is in `pid`, the buffer's address in `vaddr`, its length in
`scount`; the result is in `r`. -/
theorem syncSendPre_triple (hL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hnpc : num_proc ≤ num_chan) (chid vaddr scount : Nat) (hva : vaddr < 2 ^ 32) (hsc32 : scount < 2 ^ 32) :
    Triple εR c i0 MI (IPF ipb num_chan)
      (fun σ d => σ "pid" = BitVec.ofNat 32 chid ∧ σ "vaddr" = BitVec.ofNat 32 vaddr ∧
        σ "scount" = BitVec.ofNat 32 scount ∧ d.cid < num_chan ∧
        ∃ d1 r, syncsendto_chan_pre_spec num_proc num_chan chid vaddr scount d = some (d1, r))
      (syncSendPreS tb cidb pb fb ipb num_chan)
      (fun _ d σ' d' => ∃ r, syncsendto_chan_pre_spec num_proc num_chan chid vaddr scount d = some (d', r) ∧
        σ' "r" = BitVec.ofNat 32 r) := by
  intro σ l b d hlk hcs hM ⟨hpid, hvaddr, hscount, hcid, d', r, hs⟩
  have hnc : num_chan < 2 ^ 32 := by have := ipb_lt hL; omega
  have hs0 := hs
  unfold syncsendto_chan_pre_spec at hs
  by_cases hc : d.pg = true ∧ d.ipt = true ∧ chid < num_proc
  · rw [if_pos hc] at hs
    obtain ⟨hpg, hipt, hch⟩ := hc
    cases ha : d.abtcb chid with
    | AbTCBUndef => rw [ha] at hs; cases hs
    | AbTCBValid st b0 =>
      rw [ha] at hs
      simp only at hs
      have hsr := ThreadStatetoZ_range st
      obtain ⟨l1, b1, r1, c1, m1, f1⟩ := (getStateI εR c i0 hL (F := IPF ipb num_chan) "target_state"
        (by decide) (ie := .var "pid") (σ := σ) hpid hpg hipt hch ha).2 l b hlk hcs hM
      have hts : (σ.set "target_state" (BitVec.ofNat 32 (ThreadStatetoZ st))) "target_state" =
          BitVec.ofNat 32 (ThreadStatetoZ st) := by simp [Locals.set]
      by_cases hdead : st = .DEAD
      · rw [if_pos hdead] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨hd, hr⟩ := hs
        subst hd; subst hr
        refine ⟨_, l1, b1, d, Runs.seq r1 (Runs.ite_true (eqc_true hts (tsz_dead.2 hdead)) (Runs.assign _ _)),
          c1, m1, by simp [Locals.set], f1, _, hs0, by simp [Locals.set, Expr.eval]⟩
      · rw [if_neg hdead] at hs
        cases hchn : d.syncchpool d.cid with
        | SyncChanUndef => rw [hchn] at hs; cases hs
        | SyncChanValid t pa cn =>
          rw [hchn] at hs
          simp only at hs
          cases hk : get_kernel_pa_spec num_proc d.cid vaddr d with
          | none => rw [hk] at hs; cases hs
          | some skpa =>
            rw [hk] at hs
            simp only at hs
            by_cases hsk : skpa ≤ 2 ^ 32 - 1
            · rw [if_pos hsk] at hs
              by_cases hto : t.toNat = num_chan
              · rw [if_pos hto] at hs
                simp only [Option.some.injEq, Prod.mk.injEq] at hs
                obtain ⟨hd, hr⟩ := hs
                subst hd; subst hr
                -- guards
                have g1 : (Expr.bin .eq (.var "target_state") (.const 3)).eval
                    (σ.set "target_state" (BitVec.ofNat 32 (ThreadStatetoZ st))) = 0 :=
                  eqc_false (b := 3) hts (by omega) (by decide) (fun e => hdead (tsz_dead.1 e))
                have g2 : ¬ (Expr.bin .ltu (.var "pid") (.const (BitVec.ofNat 32 num_chan))).eval
                    (σ.set "target_state" (BitVec.ofNat 32 (ThreadStatetoZ st))) = 0 := by
                  rw [ltu_eval (a := chid) (b := num_chan) (by simp [Expr.eval, Locals.set, hpid]) rfl
                    (by omega) hnc, if_pos (by omega)]
                  decide
                -- myid = get_curid(); n = myid
                have hlk1 : ((σ.set "target_state" (BitVec.ofNat 32 (ThreadStatetoZ st))) "lk").toNat = i0 := by
                  simpa [Locals.set] using hlk
                obtain ⟨l2, b2, r2, c2, m2, f2⟩ := (getCuridI εR c i0 hL (F := IPF ipb num_chan) "myid"
                  (by decide) (σ.set "target_state" (BitVec.ofNat 32 (ThreadStatetoZ st))) d).2 l1 b1 hlk1 c1 m1
                -- get_kernel_pa
                obtain ⟨σ4, l4, b4, d4, r4, c4, m4, k4, f4, hd4, v4, hv4, hv432, hr4, hfr4⟩ :=
                  getKernelPa_triple εR c i0 hL d.cid vaddr hva
                    ((((σ.set "target_state" (BitVec.ofNat 32 (ThreadStatetoZ st))).set "myid"
                      (BitVec.ofNat 32 d.cid)).set "n" (BitVec.ofNat 32 d.cid))) l2 b2 d
                    (by simpa [Locals.set] using hlk) c2 m2
                    ⟨by simp [Locals.set], by simp [Locals.set, hvaddr], skpa, hk⟩
                rw [hk] at hv4
                simp only [Option.some.injEq] at hv4
                subst hv4
                have e4 := hd4.symm
                subst e4
                -- the tail
                have hmy4 : σ4 "myid" = BitVec.ofNat 32 d.cid := by rw [hfr4 "myid" rfl]; simp [Locals.set]
                have hpid4 : σ4 "pid" = BitVec.ofNat 32 chid := by
                  rw [hfr4 "pid" rfl]; simp [Locals.set, hpid]
                have hsc4 : σ4 "scount" = BitVec.ofNat 32 scount := by
                  rw [hfr4 "scount" rfl]; simp [Locals.set, hscount]
                have hlk4 : (σ4 "lk").toNat = i0 := by rw [k4]; simpa [Locals.set] using hlk
                obtain ⟨σ6, hst, hr6⟩ := sendPreTail_step εR c i0 hL (σ := σ4.set "sender_kpa" (BitVec.ofNat 32 skpa))
                  (d := d) (chid := chid) (skpa := skpa) (scount := scount) hcid
                  (by simp [Locals.set, hmy4]) (by simp [Locals.set, hpid4]) (by simp [Locals.set])
                  (by simp [Locals.set, hsc4]) hsc32 hchn hto
                obtain ⟨l6, b6, r6, c6, m6, f6⟩ := hst.2 l4 b4 (by simpa [Locals.set] using hlk4) c4 m4
                have ras : Runs (rprimsA εR c) (.assign "sender_kpa" (.var "r")) σ4 l4
                    (σ4.set "sender_kpa" (BitVec.ofNat 32 skpa)) l4 := asg_run _ _ hr4
                refine ⟨σ6, l6, b6, _, Runs.seq r1 (Runs.ite_false g1 (Runs.ite_true g2
                  (Runs.seq r2 (Runs.seq (Runs.assign _ _) (Runs.seq r4 (Runs.seq ras r6)))))), c6, m6, ?_,
                  fun k hk => ?_, _, hs0, hr6⟩
                · rw [hst.1]; simp [Locals.set, k4]
                · rw [f6 k hk, f4 k (fun h => h), f2 k hk, f1 k hk]
              · rw [if_neg hto] at hs; cases hs
            · rw [if_neg hsk] at hs; cases hs
  · rw [if_neg hc] at hs; cases hs

end Code

end PIPC
