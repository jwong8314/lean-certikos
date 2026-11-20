import CertiKOS.MInit

/-!
# mCertiKOS `sched_init`: the end of initialisation, ported

Ported from `objects/ObjThread.v`: `sched_init_spec`. Ported from
`proc/PCurIDCSource.v`: the C code of `sched_init`.

* `tdqueue_init0_triple`: **`tdqueue_init` refines `tdqueue_init0_spec`**,
  the specification over lists. The pointer state it reaches is the pointer
  view of the list state (`real_data`).
* `sched_init_triple`: **`sched_init` refines `sched_init_spec`.** It is
  `tdqueue_init(mbi_adr); set_curid(0); set_state(0, TSTATE_RUN);`, and its
  proof goes through the triples of the three.
* `sched_init_inv`: the state it reaches satisfies the invariants of the
  list view.

This is the whole of boot: from the state the boot loader leaves to paging
on, every table initialised, and thread 0 running.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PSched

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID MCPU MInit
open MALInit (MMTable MatchMMap matchMM_of_eq MM_valid MM_correct real_AT real_nps)
open MPTInit (NV real_pt real_idpde)

/-- **`sched_init_spec`**, with the allocation table in place of the owner
lists. -/
def sched_init_spec (num_proc num_chan kl kh : Nat) (mm : MMTable) (size : Nat) (d : CData) : Option CData :=
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
      cid := 0 }
  else none

/-- `sched_init(mbi_adr)`: `tdqueue_init(mbi_adr); set_curid(0); set_state(0, TSTATE_RUN);` -/
def schedInitCS (mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan cidb : Nat) : Stmt APrim :=
  .seq (tdqueueInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan)
    (.seq (setCuridS cidb (.const 0)) (setTStateS tb (.const 0) (.const 1)))

/-- The cells initialisation may write, up to the queues. -/
def IF (cb num_id pb cpub sb num_proc tb qb num_chan : Nat) (k : Nat) : Prop :=
  ((PF cb num_id pb cpub k ∨ SF sb num_proc k) ∨ TF tb num_proc k) ∨ QF qb num_chan k

/-- **`sched_init_spec` establishes the invariants of the list view.** -/
theorem sched_init_inv {num_proc num_chan kl kh : Nat} {mm : MMTable} {size : Nat} {d d' : CData}
    (hnp : 0 < num_proc) (hs : sched_init_spec num_proc num_chan kl kh mm size d = some d') :
    AInv num_proc num_chan d'.toAData := by
  unfold sched_init_spec at hs
  by_cases hc : d.init = false ∧ d.pg = false ∧ d.ipt = true
  · rw [if_pos hc] at hs
    simp only [Option.some.injEq] at hs
    subst hs
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      real_ainv (np := num_proc) (nc := num_chan) (real_AC kl kh mm size) d.abtcb d.abq
    have h0 : real_abtcb num_proc d.abtcb 0 = .AbTCBValid .DEAD (-1) := init_zmap_inside _ _ _ _ hnp
    obtain ⟨g1, g3, g4, g5⟩ := setst_inv (st' := .RUN) h0 h1 h3 h4 h5
    exact ⟨g1, h2, g3, g4, g5⟩
  · rw [if_neg hc] at hs; cases hs

section Chain
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb mmb size cpub : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

/-- **`tdqueue_init` refines `tdqueue_init0_spec`.** -/
theorem tdqueue_init0_triple
    (hK : KLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb mmb size cpub)
    (hida : ida + 2 ^ 22 + 7 ≤ 2 ^ 32) (hnp : 0 < num_proc) {kl kh : Nat} {mm : MMTable} (hnum : 0 < num_id)
    (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size)
    (hv : MM_valid mm size) (hc : MM_correct mm size) :
    Triple εR c i0
      (fun (a : AData) b => (MatchA maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb a b ∧
        MatchCPU num_proc pb cpub a.toPTData b) ∧ MatchMMap mmb mm size b)
      (IF cb num_id pb cpub sb num_proc tb qb num_chan)
      (fun _ a => a.init = false ∧ a.pg = false ∧ a.ipt = true ∧ (∀ j, (a.AC j).cused = false) ∧ NV a.ptpool)
      (tdqueueInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan)
      (fun _ a _ a' => tdqueue_init0_spec num_proc num_chan kl kh mm size a = some a') := by
  rintro σ l b a hlk hcs ⟨⟨⟨q, hQ, hS, hR, hInv⟩, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have eP : a.toPTData = q.toPTData := congrArg SData.toPTData hS
  have qin : q.init = false := by show q.toPTData.init = false; rw [← eP]; exact hin
  have qpg : q.pg = false := by show q.toPTData.pg = false; rw [← eP]; exact hpg
  have qipt : q.ipt = true := by show q.toPTData.ipt = true; rw [← eP]; exact hipt
  have qun : ∀ j, (q.AC j).cused = false := fun j => by
    show (q.toPTData.AC j).cused = false; rw [← eP]; exact hun j
  have qnv : NV q.ptpool := by show NV q.toPTData.ptpool; rw [← eP]; exact hnv
  obtain ⟨σ1, l1, b1, q1, hr1, hcs1, ⟨⟨hQ1, hC1⟩, hMM1⟩, hlk1, hf1, hq1⟩ :=
    tdqueue_init_triple εR c i0 hK hida hnp hnum hmp hkl hkl' hkh hsz hv hc σ l b q hlk hcs
      ⟨⟨hQ, by rw [← eP]; exact hC⟩, hMM⟩ ⟨qin, qpg, qipt, qun, qnv⟩
  have hq1' : q1 = { q with
      pg := true
      AT := real_AT kl kh mm size q.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := real_pt num_proc q.ptpool
      idpde := real_idpde q.idpde
      smspool := real_smspool num_proc q.smspool
      tcb := real_tcb num_proc q.tcb
      tdq := real_tdq num_proc num_chan q.tdq } := by
    have h : tdqueue_init_spec num_proc num_chan kl kh mm size q = some q1 := hq1
    unfold tdqueue_init_spec thread_init_spec at h
    rw [if_pos ⟨qin, qpg, qipt⟩] at h
    exact (Option.some.inj h).symm
  have hsa : tdqueue_init0_spec num_proc num_chan kl kh mm size a = some { a with
      pg := true
      AT := real_AT kl kh mm size a.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := real_pt num_proc a.ptpool
      idpde := real_idpde a.idpde
      smspool := real_smspool num_proc a.smspool
      abtcb := real_abtcb num_proc a.abtcb
      abq := real_abq num_chan a.abq } := by
    unfold tdqueue_init0_spec
    rw [if_pos ⟨hin, hpg, hipt⟩]
  have hS1 : (fun s : SData => ({ s with
      pg := true
      AT := real_AT kl kh mm size s.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := real_pt num_proc s.ptpool
      idpde := real_idpde s.idpde
      smspool := real_smspool num_proc s.smspool } : SData)) a.toSData = q1.toSData := by
    rw [hS, hq1']
  refine ⟨σ1, l1, b1, _, hr1, hcs1, ⟨⟨⟨q1, hQ1, hS1, ?_, fun _ => ?_⟩, ?_⟩, hMM1⟩, hlk1, hf1, hsa⟩
  · rw [hq1']; exact real_data _ _ _ _
  · rw [hq1']; exact ⟨real_tcb_correct _, real_tdq_correct _⟩
  · have e1 : (fun s : SData => ({ s with
        pg := true
        AT := real_AT kl kh mm size s.AT
        nps := real_nps mm size
        AC := real_AC kl kh mm size
        init := true
        PT := 0
        ptpool := real_pt num_proc s.ptpool
        idpde := real_idpde s.idpde
        smspool := real_smspool num_proc s.smspool } : SData)) a.toSData = q1.toSData := hS1
    have e2 := congrArg SData.toPTData e1
    show MatchCPU num_proc pb cpub (SData.toPTData _) b1
    rw [e2]; exact hC1

/-- **`sched_init` refines `sched_init_spec`.** -/
theorem sched_init_triple
    (hK : KLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb mmb size cpub)
    (hida : ida + 2 ^ 22 + 7 ≤ 2 ^ 32) (hnp : 0 < num_proc) {kl kh : Nat} {mm : MMTable} (hnum : 0 < num_id)
    (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size)
    (hv : MM_valid mm size) (hc : MM_correct mm size) :
    Triple εR c i0
      (fun (d : CData) b => (MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb d b ∧
        MatchCPU num_proc pb cpub d.toPTData b) ∧ MatchMMap mmb mm size b)
      (fun k => IF cb num_id pb cpub sb num_proc tb qb num_chan k ∨ k = cidb)
      (fun _ d => d.init = false ∧ d.pg = false ∧ d.ipt = true ∧ (∀ j, (d.AC j).cused = false) ∧ NV d.ptpool)
      (schedInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan cidb)
      (fun _ d _ d' => sched_init_spec num_proc num_chan kl kh mm size d = some d') := by
  rintro σ l b d hlk hcs ⟨⟨⟨hA, hcid⟩, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have hCL := hK.clay
  have := hK.hmm0; have := hK.hmm1; have := hK.hcpu; have := hCL.qlay.tlay.slay.hse
  have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.hte
  have := hCL.qlay.hqb; have := hCL.qlay.hqe; have := hCL.hcb; have := hCL.hce
  obtain ⟨σ1, l1, b1, a1, hr1, hcs1, ⟨⟨hA1, hC1⟩, hMM1⟩, hlk1, hf1, hq1⟩ :=
    tdqueue_init0_triple εR c i0 hK hida hnp hnum hmp hkl hkl' hkh hsz hv hc σ l b d.toAData hlk hcs
      ⟨⟨hA, hC⟩, hMM⟩ ⟨hin, hpg, hipt, hun, hnv⟩
  have ha1 : a1 = { d.toAData with
      pg := true
      AT := real_AT kl kh mm size d.AT
      nps := real_nps mm size
      AC := real_AC kl kh mm size
      init := true
      PT := 0
      ptpool := real_pt num_proc d.ptpool
      idpde := real_idpde d.idpde
      smspool := real_smspool num_proc d.smspool
      abtcb := real_abtcb num_proc d.abtcb
      abq := real_abq num_chan d.abq } := by
    have h : tdqueue_init0_spec num_proc num_chan kl kh mm size d.toAData = some a1 := hq1
    unfold tdqueue_init0_spec at h
    rw [if_pos ⟨hin, hpg, hipt⟩] at h
    exact (Option.some.inj h).symm
  have hncid : ¬ IF cb num_id pb cpub sb num_proc tb qb num_chan cidb := by
    rintro ((((h | h) | h) | h) | h)
    · rcases h with h | h <;> omega
    · rcases h with h | h <;> omega
    · obtain ⟨h3, h4⟩ := h; omega
    · obtain ⟨h3, h4⟩ := h; omega
    · obtain ⟨h3, h4⟩ := h; omega
  have hM1 : MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb
      ({ d with toAData := a1 } : CData) b1 :=
    ⟨hA1, by show d.cid = (b1 cidb).toNat; rw [hf1 cidb hncid]; exact hcid⟩
  have hlk1' : (σ1 "lk").toNat = i0 := by rw [hlk1]; exact hlk
  obtain ⟨l2, b2, hr2, hcs2, hM2, hf2⟩ := (setCuridC εR c i0 hCL (F := fun k => k = cidb) (fun _ h => h)
    (ve := .const 0) (σ := σ1) (d := { d with toAData := a1 }) (i := 0) rfl (by decide)).2 l1 b1 hlk1' hcs1 hM1
  have g1 : a1.pg = true := by rw [ha1]
  have g2 : a1.ipt = true := by rw [ha1]; exact hipt
  have g3 : (a1.AC 0).cused = true := by
    rw [ha1]
    show (real_AC kl kh mm size 0).cused = true
    rw [real_AC_zero]
  have g4 : a1.abtcb 0 = .AbTCBValid .DEAD (-1) := by
    rw [ha1]; exact init_zmap_inside _ _ _ _ hnp
  have hset : set_state0_spec num_proc 0 1 a1 =
      some { a1 with abtcb := setAt a1.abtcb 0 (.AbTCBValid .RUN (-1)) } := by
    unfold set_state0_spec
    rw [if_pos ⟨g1, g2, hnp⟩, if_pos g3, g4]
    rfl
  have hT := liftA (ida := ida) εR c i0 hCL (setState0_triple εR c i0 hCL.qlay (.const 0) (.const 1) num_proc 0 1
    (Nat.le_refl _)) (fun k hk => by obtain ⟨h3, h4⟩ := hk; omega)
  obtain ⟨σ3, l3, b3, d3, hr3, hcs3, hM3, hlk3, hf3, a3, hd3, hq3, hσ3⟩ :=
    hT (σ1.set "_" 0) l2 b2 ({ ({ d with toAData := a1 } : CData) with cid := 0 })
      (by simpa [Locals.set] using hlk1') hcs2 hM2 ⟨rfl, rfl, _, hset⟩
  have ha3 : a3 = { a1 with abtcb := setAt a1.abtcb 0 (.AbTCBValid .RUN (-1)) } := by
    have h : set_state0_spec num_proc 0 1 a1 = some a3 := hq3
    rw [hset] at h
    exact (Option.some.inj h).symm
  have hcf : ∀ k, k ≠ cidb → ¬ TF tb num_proc k → b3 k = b1 k := fun k h1 h2 =>
    (hf3 k h2).trans (hf2 k h1)
  have hnt : ∀ k, k < tb → k ≠ cidb ∧ ¬ TF tb num_proc k := fun k h =>
    ⟨by omega, fun h' => by obtain ⟨h3, h4⟩ := h'; omega⟩
  have e3 : d3.toAData = a3 := by rw [hd3]
  have ePT : a3.PT = a1.PT := by rw [ha3]
  have epg : a3.pg = a1.pg := by rw [ha3]
  refine ⟨σ3, l3, b3, d3, Runs.seq hr1 (Runs.seq hr2 hr3), hcs3, ⟨⟨hM3, fun h => ?_, ?_⟩,
    matchMM_of_eq hMM1 (fun k hk hk2 => hcf k (hnt k (by omega)).1 (hnt k (by omega)).2)⟩, ?_,
    fun k hk => ?_, ?_⟩
  · have h' : d3.toAData.PT < num_proc := h
    rw [e3, ePT] at h'
    show b3 cpub = BitVec.ofNat 32 (pb + d3.toAData.PT * 1024)
    rw [e3, ePT, hcf cpub (hnt _ (by omega)).1 (hnt _ (by omega)).2]
    exact hC1.1 h'
  · show d3.toAData.pg = true ↔ b3 (cpub + 1) ≠ 0
    rw [e3, epg, hcf (cpub + 1) (hnt _ (by omega)).1 (hnt _ (by omega)).2]
    exact hC1.2
  · rw [hlk3]; simp [Locals.set, hlk1]
  · have h1 : k ≠ cidb := fun e => hk (Or.inr e)
    have h2 : ¬ TF tb num_proc k := fun h => hk (Or.inl (Or.inl (Or.inr h)))
    rw [hcf k h1 h2, hf1 k (fun h => hk (Or.inl h))]
  · show sched_init_spec num_proc num_chan kl kh mm size d = some d3
    unfold sched_init_spec
    rw [if_pos ⟨hin, hpg, hipt⟩, hd3, ha3, ha1]

end Chain

end PSched
