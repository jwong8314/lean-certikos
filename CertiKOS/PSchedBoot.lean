import CertiKOS.PSchedInit
import CertiKOS.MMInv

/-!
# Boot under the lock: every invariant established on the log

`MMInv.boot_locked_inv` showed that `pt_init_kern`, run under the lock,
leaves the memory-management invariant on the shared log. This file does the
same for the whole of boot.

* `sched_init_mmi`: `sched_init_spec` establishes the memory-management
  invariant (`MMI`), `pg = true` and `cid = 0`.
* `sched_locked_inv`: **`acquire; sched_init; release` establishes the
  invariants on the log.** On any log whose kernel region is as the boot
  loader leaves it (`PreInit`, the memory map, paging off), the call finishes,
  idle, and the region it releases matches a state with paging on, the
  memory-management invariant, and the invariants of the list view.

After it a CPU that acquires the lock finds a state every ported operation
applies to. The rely on the other CPUs is assumed, as in stage 4.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PSched

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA lkE apull)
open LockRegion (RLog RState HLogR rreplay REnv Region hmemR)
open LockRegionCPU KernFrame Layer LogInv
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID MCPU MInit
open MALInit (MMTable MM_valid MM_kern MM_correct MatchMMap real_AT real_nps mem_init_spec mem_init_inv)
open MPTInit (NV real_pt real_idpde)
open MMInv (MMI PreInit real_AC_uq)

/-- **`sched_init_spec` establishes the memory-management invariant**, with
paging on and thread 0 current. -/
theorem sched_init_mmi {maxpage num_proc num_chan kl kh : Nat} {mm : MMTable} {size : Nat} {d d' : CData}
    (hkl : 0 < kl) (hsz : 0 < size) (hmp : 2 ^ 20 ≤ maxpage) (hv : MM_valid mm size)
    (hk : MM_kern kl mm size) (hP : PreInit d.toPTData)
    (h : sched_init_spec num_proc num_chan kl kh mm size d = some d') :
    MMI maxpage kl kh d'.toPTData ∧ d'.pg = true ∧ d'.cid = 0 := by
  obtain ⟨hin, hpg, hipt, -, -, hpp⟩ := hP
  unfold sched_init_spec at h
  rw [if_pos ⟨hin, hpg, hipt⟩] at h
  simp only [Option.some.injEq] at h
  subst h
  have hm : mem_init_spec kl kh mm size d.toPData =
      some { d.toPData with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, init := true } := by
    unfold mem_init_spec; rw [if_pos hin]
  exact ⟨⟨mem_init_inv hkl hsz hmp hv hk hpp hm, real_AC_uq kl kh mm size⟩, rfl, rfl⟩

section Locked
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb mmb size cpub : Nat}

/-- **Boot under the lock establishes the invariants on the log.** -/
theorem sched_locked_inv {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv)
    (hKL : KLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb mmb size cpub)
    (hida : ida + 2 ^ 22 + 7 ≤ 2 ^ 32) (hnp : 0 < num_proc) {kl kh : Nat} {mm : MMTable} (hnum : 0 < num_id)
    (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size)
    (hv : MM_valid mm size) (hcr : MM_correct mm size) (hk : MM_kern kl mm size)
    (hRJ : RelyJ εR c iv.toNat (fun b => ∃ d : CData,
      ((MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb d b ∧
        MatchCPU num_proc pb cpub d.toPTData b) ∧ MatchMMap mmb mm size b) ∧ PreInit d.toPTData))
    (hJ : ∃ d : CData,
      ((MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb d (hmemR iv.toNat H) ∧
        MatchCPU num_proc pb cpub d.toPTData (hmemR iv.toNat H)) ∧
        MatchMMap mmb mm size (hmemR iv.toNat H)) ∧ PreInit d.toPTData) :
    ∃ (σ2 : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR) (d' : CData),
      Star (rprimsA εR c)
        ⟨.seq acquireA (.seq (schedInitCS mmb maxpage kl kh cb num_proc pb ib ida cpub sb tb qb num_chan cidb)
          relA), .stop, σ, l⟩
        ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      MatchC maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb d' (hmemR iv.toNat H3) ∧
      MatchCPU num_proc pb cpub d'.toPTData (hmemR iv.toNat H3) ∧
      MMI maxpage kl kh d'.toPTData ∧ AInv num_proc num_chan d'.toAData ∧ d'.pg = true ∧ d'.cid = 0 := by
  obtain ⟨σ1, r1, H1, -, -, ⟨d, hM, hP⟩, hall⟩ :=
    Triple.locked_inv hE hRR hc hRA hl hidle bound K hK hF σ hσ
      (sched_init_triple εR c iv.toNat hKL hida hnp hnum hmp hkl hkl' hkh hsz hv hcr)
      (I := fun d : CData => PreInit d.toPTData)
      (I' := fun d : CData => (MMI maxpage kl kh d.toPTData ∧ d.pg = true ∧ d.cid = 0) ∧
        AInv num_proc num_chan d.toAData) hRJ hJ
      (fun _ d _ d' hI _ hQ => ⟨sched_init_mmi hkl hsz hmp hv hk hI hQ, sched_init_inv hnp hQ⟩)
  obtain ⟨σ2, rb, S3, H3, d', hst, hl3, hid, hM3, hI3, -⟩ :=
    hall d hM hP ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1⟩
  exact ⟨σ2, rb, S3, H3, d', hst, hl3, hid, hM3.1.1, hM3.1.2, hI3.1.1, hI3.2, hI3.1.2.1, hI3.1.2.2⟩

end Locked

end PSched
