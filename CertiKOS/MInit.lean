import CertiKOS.MCPU
import CertiKOS.PCurID

/-!
# Initialisation, as whole functions

Each layer's `*_init` first calls the one below, down to `pt_init`, which
turns paging on (`MCPU.lean`). With that call verified, the chain is verified
as mCertiKOS has it: one function per layer, each refining its
specification.

Ported from `mm/MShareOpCSource.v`, `proc/PThreadIntroCSource.v`,
`proc/PQueueIntroCSource.v`: `sharedmem_init`, `thread_init`, `tdqueue_init`.

* `KLayout`: **one layout for the whole kernel region.** In order: the
  allocation table, the containers, the boot loader's memory map, `CR3` and
  the paging bit, the shared-memory table, the control blocks, the queues,
  the current thread, the page-table pool, the identity map, flat memory.
* `sharedmem_init_triple`, `thread_init_triple`, `tdqueue_init_triple`:
  each function refines its specification, from the state the boot loader
  leaves (`init = false`, paging off, no container in use, no page table).

After `tdqueue_init` the region matches a state with `pg = true`, which is
what every operation of the layers above requires. Until this file that flag
was never established by code.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MInit

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID MCPU
open MALInit (MMTable MatchMMap matchMM_of_eq MM_valid MM_correct real_AT real_nps)
open MPTInit (NV real_pt real_idpde)

/-- **The layout of the whole kernel region.** -/
structure KLayout (maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb mmb size cpub : Nat) : Prop where
  clay : CLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb
  /-- the memory map comes after the containers -/
  hmm0 : cb + 5 * num_id ≤ mmb
  /-- then the control registers -/
  hmm1 : mmb + 1 + 3 * size ≤ cpub
  /-- then the shared-memory table and the rest -/
  hcpu : cpub + 2 ≤ sb

/-- The cells `pt_init` may write. -/
def PF (cb num_id pb cpub : Nat) (k : Nat) : Prop := (k < cb + 5 * num_id ∨ pb ≤ k) ∨ CF cpub k

/-- The shared-memory table. -/
def SF (sb num_proc : Nat) (k : Nat) : Prop := sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc)

/-- `sharedmem_init(mbi_adr)`: `pmap_init(mbi_adr);` then the loops. -/
def sharedmemInitCS (mmb maxpage kl kh cb num_proc pb ib ida cpub sb : Nat) : Stmt APrim :=
  .seq (pmapInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub) (smInitLoop sb num_proc)

/-- `thread_init(mbi_adr)`: `sharedmem_init(mbi_adr);` then the loop. -/
def threadInitCS (mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb : Nat) : Stmt APrim :=
  .seq (sharedmemInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb) (threadInitLoop tb num_proc)

/-- `tdqueue_init(mbi_adr)`: `thread_init(mbi_adr);` then the loop. -/
def tdqueueInitCS (mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan : Nat) : Stmt APrim :=
  .seq (threadInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb) (tdqInitLoop qb num_proc num_chan)

section Chain
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb mmb size cpub : Nat}

theorem KLayout.mlay (hK : KLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb mmb size cpub) :
    MLayout maxpage num_id cb num_proc pb ib fb cpub := by
  have := hK.hmm0; have := hK.hmm1; have := hK.hcpu; have := hK.clay.qlay.tlay.slay.hse
  exact ⟨hK.clay.qlay.tlay.slay.lay, by omega, by omega⟩

variable (εR : REnv) (c : CPU) (i0 : Nat)

/-- **`sharedmem_init` refines `sharedmem_init_spec`.** -/
theorem sharedmem_init_triple
    (hK : KLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb mmb size cpub)
    (hida : ida + 2 ^ 22 + 7 ≤ 2 ^ 32) (hnp : 0 < num_proc) {kl kh : Nat} {mm : MMTable} (hnum : 0 < num_id)
    (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size)
    (hv : MM_valid mm size) (hc : MM_correct mm size) :
    Triple εR c i0
      (fun (d : SData) b => (MatchS maxpage num_id cb num_proc pb ib fb ida sb d b ∧
        MatchCPU num_proc pb cpub d.toPTData b) ∧ MatchMMap mmb mm size b)
      (fun k => PF cb num_id pb cpub k ∨ SF sb num_proc k)
      (fun _ d => d.init = false ∧ d.pg = false ∧ d.ipt = true ∧ (∀ j, (d.AC j).cused = false) ∧ NV d.ptpool)
      (sharedmemInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb)
      (fun _ d _ d' => sharedmem_init_spec num_proc kl kh mm size d = some d') := by
  rintro σ l b d hlk hcs ⟨⟨hS, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have hSL := hK.clay.qlay.tlay.slay
  have := hK.hmm0; have := hK.hmm1; have := hK.hcpu; have := hSL.hse; have := hSL.hsb
  obtain ⟨σ1, l1, b1, p1, hr1, hcs1, ⟨⟨hA1, hC1⟩, hMM1⟩, hlk1, hf1, hq1⟩ :=
    pt_init_triple εR c i0 hK.mlay hida hnp hK.hmm0 hK.hmm1 hnum hmp hkl hkl' hkh hsz hv hc σ l b d.toPTData
      hlk hcs ⟨⟨hS.all, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have hp1 : p1 = { d.toPTData with
      pg := true
      AT := real_AT kl kh mm size d.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := real_pt num_proc d.ptpool
      idpde := real_idpde d.idpde } := by
    have h : pt_init_spec num_proc kl kh mm size d.toPTData = some p1 := hq1
    unfold pt_init_spec at h
    rw [if_pos ⟨hin, hpg, hipt⟩] at h
    exact (Option.some.inj h).symm
  have hS1 : MatchS maxpage num_id cb num_proc pb ib fb ida sb ({ d with toPTData := p1 } : SData) b1 := by
    refine ⟨hA1, fun q1 q2 g1 g2 => ?_⟩
    have hlt := scell_lt (sb := sb) g1 g2 (show 2 < 3 by decide)
    have e : ∀ k, k < 3 → b1 (scell sb num_proc q1 q2 k) = b (scell sb num_proc q1 q2 k) := fun k hk =>
      hf1 _ (by
        unfold scell at *
        rintro ((h | h) | h)
        · omega
        · omega
        · rcases h with h | h <;> omega)
    show MatchSMS (d.smspool q1 q2) _ _ _
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
    exact hS.sp q1 q2 g1 g2
  have hlk1' : (σ1 "lk").toNat = i0 := by rw [hlk1]; exact hlk
  obtain ⟨σ2, l2, b2, d2, hr2, hcs2, hS2, hlk2, hf2, hq2⟩ :=
    smInit_triple εR c i0 hSL hnp σ1 l1 b1 { d with toPTData := p1 } hlk1' hcs1 hS1
      ⟨by rw [hp1], by rw [hp1]; exact hipt⟩
  subst hq2
  have hns : ∀ k, k < sb → ¬ (sb ≤ k ∧ k < sb + 3 * (num_proc * num_proc)) := fun k h h' => by omega
  refine ⟨σ2, l2, b2, _, Runs.seq hr1 hr2, hcs2,
    ⟨⟨hS2, fun h => ?_, ?_⟩, matchMM_of_eq hMM1 (fun k hk hk2 => hf2 k (hns k (by omega)))⟩,
    hlk2.trans hlk1, fun k hk => ?_, ?_⟩
  · rw [hf2 cpub (hns _ (by omega))]; exact hC1.1 h
  · rw [hf2 (cpub + 1) (hns _ (by omega))]; exact hC1.2
  · rw [hf2 k (fun h => hk (Or.inr h)), hf1 k (fun h => hk (Or.inl h))]
  · show sharedmem_init_spec num_proc kl kh mm size d = some _
    unfold sharedmem_init_spec
    rw [if_pos ⟨hin, hpg, hipt⟩, hp1]

/-- **`thread_init` refines `thread_init_spec`.** -/
theorem thread_init_triple
    (hK : KLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb mmb size cpub)
    (hida : ida + 2 ^ 22 + 7 ≤ 2 ^ 32) (hnp : 0 < num_proc) {kl kh : Nat} {mm : MMTable} (hnum : 0 < num_id)
    (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size)
    (hv : MM_valid mm size) (hc : MM_correct mm size) :
    Triple εR c i0
      (fun (d : TData) b => (MatchT maxpage num_id cb num_proc pb ib fb ida sb tb d b ∧
        MatchCPU num_proc pb cpub d.toPTData b) ∧ MatchMMap mmb mm size b)
      (fun k => (PF cb num_id pb cpub k ∨ SF sb num_proc k) ∨ TF tb num_proc k)
      (fun _ d => d.init = false ∧ d.pg = false ∧ d.ipt = true ∧ (∀ j, (d.AC j).cused = false) ∧ NV d.ptpool)
      (threadInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb)
      (fun _ d _ d' => thread_init_spec num_proc kl kh mm size d = some d') := by
  rintro σ l b d hlk hcs ⟨⟨hT, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have hTL := hK.clay.qlay.tlay
  have := hK.hmm0; have := hK.hmm1; have := hK.hcpu; have := hTL.slay.hse; have := hTL.slay.hsb
  have := hTL.htb; have := hTL.hte
  obtain ⟨σ1, l1, b1, s1, hr1, hcs1, ⟨⟨hS1, hC1⟩, hMM1⟩, hlk1, hf1, hq1⟩ :=
    sharedmem_init_triple εR c i0 hK hida hnp hnum hmp hkl hkl' hkh hsz hv hc σ l b d.toSData hlk hcs
      ⟨⟨hT.s, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have hs1 : s1 = { d.toSData with
      pg := true
      AT := real_AT kl kh mm size d.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := real_pt num_proc d.ptpool
      idpde := real_idpde d.idpde
      smspool := real_smspool num_proc d.smspool } := by
    have h : sharedmem_init_spec num_proc kl kh mm size d.toSData = some s1 := hq1
    unfold sharedmem_init_spec at h
    rw [if_pos ⟨hin, hpg, hipt⟩] at h
    exact (Option.some.inj h).symm
  have hnt : ∀ k, tb ≤ k → k < tb + 3 * num_proc →
      ¬ (PF cb num_id pb cpub k ∨ SF sb num_proc k) := by
    intro k h1 h2
    rintro (((h | h) | h) | h)
    · omega
    · omega
    · rcases h with h | h <;> omega
    · obtain ⟨h3, h4⟩ := h; omega
  have hT1 : MatchT maxpage num_id cb num_proc pb ib fb ida sb tb ({ d with toSData := s1 } : TData) b1 := by
    refine ⟨hS1, fun j hj => ?_⟩
    have e : ∀ k, k < 3 → b1 (tcell tb j k) = b (tcell tb j k) := fun k hk =>
      hf1 _ (hnt _ (by unfold tcell; omega) (by unfold tcell; omega))
    show MatchTCB (d.tcb j) _ _ _
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide)]
    exact hT.tp j hj
  have hlk1' : (σ1 "lk").toNat = i0 := by rw [hlk1]; exact hlk
  obtain ⟨σ2, l2, b2, d2, hr2, hcs2, hT2, hlk2, hf2, hq2⟩ :=
    threadInit_triple εR c i0 hTL σ1 l1 b1 { d with toSData := s1 } hlk1' hcs1 hT1
      ⟨by rw [hs1], by rw [hs1]; exact hipt⟩
  subst hq2
  have hnc : ∀ k, k < tb → ¬ (tb ≤ k ∧ k < tb + 3 * num_proc) := fun k h h' => by omega
  refine ⟨σ2, l2, b2, _, Runs.seq hr1 hr2, hcs2,
    ⟨⟨hT2, fun h => ?_, ?_⟩, matchMM_of_eq hMM1 (fun k hk hk2 => hf2 k (hnc k (by omega)))⟩,
    hlk2.trans hlk1, fun k hk => ?_, ?_⟩
  · rw [hf2 cpub (hnc _ (by omega))]; exact hC1.1 h
  · rw [hf2 (cpub + 1) (hnc _ (by omega))]; exact hC1.2
  · rw [hf2 k (fun h => hk (Or.inr h)), hf1 k (fun h => hk (Or.inl h))]
  · show thread_init_spec num_proc kl kh mm size d = some _
    unfold thread_init_spec
    rw [if_pos ⟨hin, hpg, hipt⟩, hs1]

/-- **`tdqueue_init` refines `tdqueue_init_spec`.** -/
theorem tdqueue_init_triple
    (hK : KLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb mmb size cpub)
    (hida : ida + 2 ^ 22 + 7 ≤ 2 ^ 32) (hnp : 0 < num_proc) {kl kh : Nat} {mm : MMTable} (hnum : 0 < num_id)
    (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size)
    (hv : MM_valid mm size) (hc : MM_correct mm size) :
    Triple εR c i0
      (fun (d : QData) b => (MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb d b ∧
        MatchCPU num_proc pb cpub d.toPTData b) ∧ MatchMMap mmb mm size b)
      (fun k => ((PF cb num_id pb cpub k ∨ SF sb num_proc k) ∨ TF tb num_proc k) ∨ QF qb num_chan k)
      (fun _ d => d.init = false ∧ d.pg = false ∧ d.ipt = true ∧ (∀ j, (d.AC j).cused = false) ∧ NV d.ptpool)
      (tdqueueInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan)
      (fun _ d _ d' => tdqueue_init_spec num_proc num_chan kl kh mm size d = some d') := by
  rintro σ l b d hlk hcs ⟨⟨hQ, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have hQL := hK.clay.qlay
  have := hK.hmm0; have := hK.hmm1; have := hK.hcpu; have := hQL.tlay.slay.hse; have := hQL.tlay.slay.hsb
  have := hQL.tlay.htb; have := hQL.tlay.hte; have := hQL.hqb; have := hQL.hqe
  obtain ⟨σ1, l1, b1, t1, hr1, hcs1, ⟨⟨hT1, hC1⟩, hMM1⟩, hlk1, hf1, hq1⟩ :=
    thread_init_triple εR c i0 hK hida hnp hnum hmp hkl hkl' hkh hsz hv hc σ l b d.toTData hlk hcs
      ⟨⟨hQ.t, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have hnq : ∀ k, qb ≤ k → k < qb + 2 * (num_chan + 1) →
      ¬ ((PF cb num_id pb cpub k ∨ SF sb num_proc k) ∨ TF tb num_proc k) := by
    intro k h1 h2
    rintro ((((h | h) | h) | h) | h)
    · omega
    · omega
    · rcases h with h | h <;> omega
    · obtain ⟨h3, h4⟩ := h; omega
    · obtain ⟨h3, h4⟩ := h; omega
  have hQ1 : MatchQ maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb
      ({ d with toTData := t1 } : QData) b1 := by
    refine ⟨hT1, fun j hj => ?_⟩
    have e : ∀ k, k < 2 → b1 (qcell qb j k) = b (qcell qb j k) := fun k hk =>
      hf1 _ (hnq _ (by unfold qcell; omega) (by unfold qcell; omega))
    show MatchTDQ (d.tdq j) _ _
    rw [e 0 (by decide), e 1 (by decide)]
    exact hQ.qp j hj
  have hlk1' : (σ1 "lk").toNat = i0 := by rw [hlk1]; exact hlk
  obtain ⟨σ2, l2, b2, d2, hr2, hcs2, hQ2, hlk2, hf2, hq2⟩ :=
    tdqueueInit_triple εR c i0 hQL σ1 l1 b1 { d with toTData := t1 } hlk1' hcs1 hQ1 trivial
  subst hq2
  have hnc : ∀ k, k < qb → ¬ QF qb num_chan k := fun k h h' => by obtain ⟨h1, h2⟩ := h'; omega
  refine ⟨σ2, l2, b2, _, Runs.seq hr1 hr2, hcs2,
    ⟨⟨hQ2, fun h => ?_, ?_⟩, matchMM_of_eq hMM1 (fun k hk hk2 => hf2 k (hnc k (by omega)))⟩,
    hlk2.trans hlk1, fun k hk => ?_, ?_⟩
  · rw [hf2 cpub (hnc _ (by omega))]; exact hC1.1 h
  · rw [hf2 (cpub + 1) (hnc _ (by omega))]; exact hC1.2
  · rw [hf2 k (fun h => hk (Or.inr h)), hf1 k (fun h => hk (Or.inl h))]
  · show tdqueue_init_spec num_proc num_chan kl kh mm size d = some _
    unfold tdqueue_init_spec
    have h : thread_init_spec num_proc kl kh mm size d.toTData = some t1 := hq1
    rw [h]

end Chain

end MInit
