import CertiKOS.PIPCRecv
import CertiKOS.PSchedBoot

/-!
# mCertiKOS `proc_init`: initialisation up to the channels, ported

Ported from `objects/ObjProc.v`: `proc_init_spec`. Ported from
`proc/PIPCIntroCSource.v`: the code of `proc_init`,

```
sched_init(mbi_adr); i = 0; while (i < num_chan) { init_sync_chan(i); i++; }
```

* `proc_init_eq`: the specification is `sched_init_spec` followed by
  `real_syncchpool`.
* `proc_init_triple`: **`proc_init` refines `proc_init_spec`**, from the
  region as the boot loader leaves it. It runs `sched_init` through its
  triple and the loop through `syncInit_step`; the channels are outside what
  `sched_init` writes, and the registers and the memory map are outside what
  the loop writes.
* `proc_init_inv`: after it, the queues satisfy their invariants, thread 0 is
  the current thread and is running, and every channel is valid and sends to
  nobody.

What differs: as for `sched_init`, the allocation table stands in for
mCertiKOS's owner lists (`LAT`), and there is no `vmxinfo`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PIPC

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MPTInit MShare PThread PQueue PAbQueue PCurID PSched
open MCPU MInit MALInit

/-- **`proc_init_spec`**: everything `sched_init_spec` does, and every channel
sends to nobody. -/
def proc_init_spec (num_proc num_chan kl kh : Nat) (mm : MMTable) (size : Nat) (d : IData) : Option IData :=
  if d.init = false ∧ d.pg = false ∧ d.ipt = true then
    some { d with
      pg := true
      AT := real_AT kl kh mm size d.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := real_pt num_proc d.ptpool
      idpde := real_idpde d.idpde
      smspool := real_smspool num_proc d.smspool
      abtcb := setAt (real_abtcb num_proc d.abtcb) 0 (.AbTCBValid .RUN (-1))
      abq := real_abq num_chan d.abq
      cid := 0
      syncchpool := real_syncchpool num_chan d.syncchpool }
  else none

/-- `proc_init(mbi_adr)` -/
def procInitCS (mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan cidb ipb : Nat) : Stmt APrim :=
  .seq (schedInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan cidb)
    (syncInitLoop ipb num_chan)

/-- `proc_init_spec` is `sched_init_spec`, then the channels. -/
theorem proc_init_eq (num_proc num_chan kl kh : Nat) (mm : MMTable) (size : Nat) (d : IData) :
    proc_init_spec num_proc num_chan kl kh mm size d =
      (sched_init_spec num_proc num_chan kl kh mm size d.toCData).map (fun c1 =>
        ({ toCData := c1, syncchpool := real_syncchpool num_chan d.syncchpool } : IData)) := by
  unfold proc_init_spec sched_init_spec
  by_cases hc : d.init = false ∧ d.pg = false ∧ d.ipt = true
  · rw [if_pos hc, if_pos hc]; rfl
  · rw [if_neg hc, if_neg hc]; rfl

/-- **After `proc_init`**: the invariants of the queues, thread 0 current and
running, and every channel valid and idle. -/
theorem proc_init_inv {num_proc num_chan kl kh : Nat} {mm : MMTable} {size : Nat} {d d' : IData}
    (hnp : 0 < num_proc) (hs : proc_init_spec num_proc num_chan kl kh mm size d = some d') :
    AInv num_proc num_chan d'.toAData ∧ d'.pg = true ∧ d'.cid = 0 ∧
      d'.abtcb 0 = .AbTCBValid .RUN (-1) ∧
      ∀ i, i < num_chan → d'.syncchpool i = .SyncChanValid (BitVec.ofNat 32 num_chan) 0 0 := by
  rw [proc_init_eq] at hs
  cases hc : sched_init_spec num_proc num_chan kl kh mm size d.toCData with
  | none => rw [hc] at hs; cases hs
  | some c1 =>
    rw [hc] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    subst hs
    refine ⟨sched_init_inv hnp hc, ?_, ?_, ?_, fun i hi => init_zmap_inside _ _ _ _ hi⟩
    all_goals
      unfold sched_init_spec at hc
      split at hc
      · simp only [Option.some.injEq] at hc
        subst hc
        first | rfl | exact setAt_eq _ _ _
      · cases hc

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb mmb size cpub : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

/-- **`proc_init` refines `proc_init_spec`.** -/
theorem proc_init_triple
    (hK : KLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb mmb size cpub)
    (hIL : ILayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb)
    (hida : ida + 2 ^ 22 + 7 ≤ 2 ^ 32) (hnp : 0 < num_proc) {kl kh : Nat} {mm : MMTable} (hnum : 0 < num_id)
    (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size)
    (hv : MM_valid mm size) (hc : MM_correct mm size) :
    Triple εR c i0
      (fun (d : IData) b => (MatchI maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb d b ∧
        MatchCPU num_proc pb cpub d.toPTData b) ∧ MatchMMap mmb mm size b)
      (fun k => (IF cb num_id pb cpub sb num_proc tb qb num_chan k ∨ k = cidb) ∨ IPF ipb num_chan k)
      (fun _ d => d.init = false ∧ d.pg = false ∧ d.ipt = true ∧ (∀ j, (d.AC j).cused = false) ∧ NV d.ptpool)
      (procInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan cidb ipb)
      (fun _ d _ d' => proc_init_spec num_proc num_chan kl kh mm size d = some d') := by
  rintro σ l b d hlk hcs ⟨⟨⟨hC, hSCP⟩, hCPU⟩, hMM⟩ hP
  have hCL := hK.clay
  have := hK.hmm0; have := hK.hmm1; have := hK.hcpu; have := hCL.qlay.tlay.slay.hse
  have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.hte
  have := hCL.qlay.hqb; have := hCL.qlay.hqe; have := hCL.hcb; have := hCL.hce
  have := hIL.hib0; have := hIL.hie
  -- sched_init
  obtain ⟨σ1, l1, b1, c1, hr1, hcs1, ⟨⟨hC1, hCPU1⟩, hMM1⟩, hlk1, hf1, hq1⟩ :=
    sched_init_triple (ida := ida) εR c i0 hK hida hnp hnum hmp hkl hkl' hkh hsz hv hc σ l b d.toCData hlk hcs
      ⟨⟨hC, hCPU⟩, hMM⟩ hP
  -- it leaves the channels alone
  have hSCP1 : MatchSCP num_chan ipb d.syncchpool b1 := fun j hj => by
    have e : ∀ k, k < 3 → b1 (tcell ipb j k) = b (tcell ipb j k) := fun k hk =>
      hf1 _ (fun hk' => by
        simp only [IF, PF, CF, SF, TF, QF, tcell] at hk'
        omega)
    show MatchCh (d.syncchpool j) _ _ _
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
    exact hSCP j hj
  -- the loop
  obtain ⟨σ2, hst⟩ := syncInit_step (ida := ida) εR c i0 hIL (F := IPF ipb num_chan) (fun _ h => h) σ1
    ({ d with toCData := c1 } : IData)
  obtain ⟨l2, b2, hr2, hcs2, hM2, hf2⟩ := hst.2 l1 b1 (by rw [hlk1]; exact hlk) hcs1 ⟨hC1, hSCP1⟩
  have hout : ∀ k, k < ipb → b2 k = b1 k := fun k hk =>
    hf2 k (fun hk' => by unfold IPF at hk'; omega)
  refine ⟨σ2, l2, b2, _, Runs.seq hr1 hr2, hcs2, ⟨⟨hM2, ?_⟩, ?_⟩, hst.1.trans hlk1,
    fun k hk => ?_, ?_⟩
  · show MatchCPU num_proc pb cpub c1.toPTData b2
    refine ⟨fun h => ?_, ?_⟩
    · rw [hout cpub (by omega)]; exact hCPU1.1 h
    · rw [hout (cpub + 1) (by omega)]; exact hCPU1.2
  · exact matchMM_of_eq hMM1 (fun k h1 h2 => hout k (by omega))
  · rw [hf2 k (fun h => hk (Or.inr h)), hf1 k (fun h => hk (Or.inl h))]
  · show proc_init_spec num_proc num_chan kl kh mm size d = some _
    rw [proc_init_eq, hq1]; rfl

end Code

end PIPC
