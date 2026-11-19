import CertiKOS.LogInv
import CertiKOS.MShare

/-!
# The memory-management invariant along the log

`LogInv.lean` carries any invariant along the log. This file instantiates it
for the memory-management lock.

* `MMI`: the allocation-table invariant, and every container within its
  quota.
* `ptResv_keeps`, `offer_keeps`: the specifications preserve it.
* `boot_locked_inv`: **boot establishes the invariant on the log.** From a
  log whose region is as the boot loader left it (`PreInit`), running
  `pt_init_kern` under the lock ends on a log satisfying `MMI`, initialised.
* `ptResv_locked_inv`: **`pt_resv` under the lock keeps it.** The caller
  assumes nothing about the region: only that the log has the invariant, and
  that the specification is defined on the state found.
* `offer_locked_inv`: the same for `offer_shared_mem`.

`ptResv_locked_inv` replaces `MPTNew.ptResv_locked`, whose hypotheses were
about the local `n` after `acquire`. `acquire` uses `n` itself, so here the
process is passed in `pn` and copied to `n` once the lock is held.

`PreInit` is mCertiKOS's set of facts about the state before initialisation
(`valid_preinit_container`, `valid_uninitialized`, `init_pperm`).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MMInv

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA lkE apull)
open LockRegion (RLog RState HLogR rreplay REnv Region hmemR)
open LockRegionCPU KernFrame Layer LogInv
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare
open MALInit (MMTable MM_valid MM_kern MM_correct MatchMMap real_AT real_nps mem_init_spec mem_init_inv)
open MPTInit (NV pt_init_kern_spec ptInitKernCS pt_init_kern_triple real_pt real_idpde)

/-- **The memory-management invariant.** -/
def MMI (maxpage kl kh : Nat) (d : PTData) : Prop := ATInv maxpage kl kh d.toPData ∧ UQ d.AC

/-! ## The specifications preserve it -/

theorem ptResv_keeps {maxpage kl kh num_proc n vadr perm : Nat} {d d' : PTData} {r : Nat}
    (hI : MMI maxpage kl kh d) (h : ptResv_spec maxpage num_proc n vadr perm d = some (d', r)) :
    MMI maxpage kl kh d' := by
  unfold ptResv_spec at h
  cases hA : container_alloc_spec n d.toRData with
  | none => rw [hA] at h; cases h
  | some pr =>
    obtain ⟨r1, b⟩ := pr
    rw [hA] at h; simp only at h
    by_cases hb : b = 0
    · rw [if_pos hb] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hI
    · rw [if_neg hb] at h
      have hI1 : ATInv maxpage kl kh ({ d with toRData := r1 } : PTData).toPData := alloc_at_inv hI.1 hA
      obtain ⟨a, b', -⟩ := ptInsert_keeps hI1 h
      exact ⟨a, b' (alloc_usage hI.2 hA)⟩

theorem offer_keeps {maxpage kl kh num_proc p1 p2 va : Nat} {d d' : SData} {r : Nat}
    (hI : MMI maxpage kl kh d.toPTData)
    (h : offer_shared_mem_spec num_proc maxpage p1 p2 va d = some (d', r)) :
    MMI maxpage kl kh d'.toPTData := by
  obtain ⟨hI1, hu⟩ := hI
  unfold offer_shared_mem_spec at h
  repeat' (split at h)
  all_goals first
    | (cases h; exact ⟨hI1, hu⟩)
    | (cases h; rename_i hR _; obtain ⟨a, b, -⟩ := ptResv2_keeps hI1 hR; exact ⟨a, b hu⟩)
    | cases h

/-! ## Boot establishes it -/

/-- What is known of the state before initialisation. -/
def PreInit (d : PTData) : Prop :=
  d.init = false ∧ d.pg = false ∧ d.ipt = true ∧ (∀ j, (d.AC j).cused = false) ∧ NV d.ptpool ∧
    d.pperm = fun _ => .PGUndef

theorem real_AC_uq (kl kh : Nat) (mm : MMTable) (size : Nat) : UQ (real_AC kl kh mm size) := by
  intro i
  by_cases e : i = 0
  · subst e; rw [real_AC_zero]; exact Nat.zero_le _
  · unfold real_AC; rw [setAt_ne _ _ e]; exact Nat.le_refl _

/-- **`pt_init_kern_spec` establishes the invariant.** -/
theorem boot_inv {maxpage num_proc kl kh : Nat} {mm : MMTable} {size : Nat} {d d' : PTData} (hkl : 0 < kl)
    (hsz : 0 < size) (hmp : 2 ^ 20 ≤ maxpage) (hv : MM_valid mm size) (hk : MM_kern kl mm size)
    (hP : PreInit d) (h : pt_init_kern_spec num_proc kl kh mm size d = some d') :
    MMI maxpage kl kh d' ∧ d'.init = true := by
  obtain ⟨hin, hpg, hipt, -, -, hpp⟩ := hP
  unfold pt_init_kern_spec at h
  rw [if_pos ⟨hin, hpg, hipt⟩] at h
  simp only [Option.some.injEq] at h; subst h
  have hm : mem_init_spec kl kh mm size d.toPData =
      some { d.toPData with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, init := true } := by
    unfold mem_init_spec; rw [if_pos hin]
  exact ⟨⟨mem_init_inv hkl hsz hmp hv hk hpp hm, real_AC_uq kl kh mm size⟩, rfl⟩

section Locked
variable {maxpage num_id cb num_proc pb ib fb ida sb : Nat}

/-- **Boot establishes the invariant on the log.** -/
theorem boot_locked_inv {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hida : ida + 2 ^ 22 + 7 ≤ 2 ^ 32) (hnp : 0 < num_proc) {mmb size kl kh : Nat} {mm : MMTable}
    (hcm : cb + 5 * num_id ≤ mmb) (hmb : mmb + 1 + 3 * size ≤ pb) (hnum : 0 < num_id)
    (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size)
    (hv : MM_valid mm size) (hcr : MM_correct mm size) (hk : MM_kern kl mm size)
    (hRJ : RelyJ εR c iv.toNat (fun b => ∃ d,
      (MatchAll maxpage num_id cb num_proc pb ib fb ida d b ∧ MatchMMap mmb mm size b) ∧ PreInit d))
    (hJ : ∃ d, (MatchAll maxpage num_id cb num_proc pb ib fb ida d (hmemR iv.toNat H) ∧
      MatchMMap mmb mm size (hmemR iv.toNat H)) ∧ PreInit d) :
    ∃ (σ2 : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR) (d' : PTData),
      Star (rprimsA εR c)
        ⟨.seq acquireA (.seq (ptInitKernCS mmb maxpage kl kh cb num_proc pb ib ida) relA), .stop, σ, l⟩
        ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      MatchAll maxpage num_id cb num_proc pb ib fb ida d' (hmemR iv.toNat H3) ∧
      MMI maxpage kl kh d' ∧ d'.init = true := by
  obtain ⟨σ1, r1, H1, -, -, ⟨d, hM, hP⟩, hall⟩ :=
    Triple.locked_inv hE hRR hc hRA hl hidle bound K hK hF σ hσ
      (pt_init_kern_triple εR c iv.toNat hL hida hnp hcm hmb hnum hmp hkl hkl' hkh hsz hv hcr)
      (I := PreInit) (I' := fun d => MMI maxpage kl kh d ∧ d.init = true) hRJ hJ
      (fun _ d _ d' hI _ hQ => boot_inv hkl hsz hmp hv hk hI hQ)
  obtain ⟨σ2, rb, S3, H3, d', hst, hl3, hid, hM3, hI3, -⟩ :=
    hall d hM hP ⟨hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1⟩
  exact ⟨σ2, rb, S3, H3, d', hst, hl3, hid, hM3.1, hI3.1, hI3.2⟩

/-- `n = pn; pt_resv(n, vaddr, perm)`: the call, once the lock is held. -/
def ptResvCall (cb maxpage pb fb : Nat) : Stmt APrim :=
  .seq (.assign "n" (.var "pn")) (ptResvS cb maxpage pb fb)

/-- **`pt_resv` under the lock keeps the invariant.** The log has the
invariant on entry. The region found matches a state with it. If
`ptResv_spec` is defined on that state, the call finishes, and the log has
the invariant on exit. -/
theorem ptResv_locked_inv {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (nn vadr perm : Nat) (hnid : nn < num_id)
    (hn : σ "pn" = BitVec.ofNat 32 nn) (hva : σ "vaddr" = BitVec.ofNat 32 vadr)
    (hpe : σ "perm" = BitVec.ofNat 32 perm)
    (hRJ : RelyJ εR c iv.toNat (fun b => ∃ d,
      MatchAll maxpage num_id cb num_proc pb ib fb ida d b ∧ MMI maxpage kl kh d))
    (hJ : ∃ d, MatchAll maxpage num_id cb num_proc pb ib fb ida d (hmemR iv.toNat H) ∧ MMI maxpage kl kh d) :
    ∃ H1 : HLogR,
      (∃ d, MatchAll maxpage num_id cb num_proc pb ib fb ida d (hmemR iv.toNat H1) ∧ MMI maxpage kl kh d) ∧
      ∀ d, MatchAll maxpage num_id cb num_proc pb ib fb ida d (hmemR iv.toNat H1) → MMI maxpage kl kh d →
        (∃ d1 r, ptResv_spec maxpage num_proc nn vadr perm d = some (d1, r)) →
        ∃ (σ2 : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR) (d' : PTData) (r : Nat),
          Star (rprimsA εR c) ⟨.seq acquireA (.seq (ptResvCall cb maxpage pb fb) relA), .stop, σ, l⟩
            ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          MatchAll maxpage num_id cb num_proc pb ib fb ida d' (hmemR iv.toNat H3) ∧ MMI maxpage kl kh d' ∧
          ptResv_spec maxpage num_proc nn vadr perm d = some (d', r) ∧ σ2 "r" = BitVec.ofNat 32 r := by
  have T := (ptResv_triple εR c iv.toNat hL hmax hnum hmp hnn (ida := ida) (kl := kl) (kh := kh) nn vadr
    perm hnid).assign_pre "n" (by decide) (.var "pn")
  obtain ⟨σ1, r1, H1, -, hfr, hJ1, hall⟩ :=
    Triple.locked_inv hE hRR hc hRA hl hidle bound K hK hF σ hσ T
      (I := MMI maxpage kl kh) (I' := MMI maxpage kl kh) hRJ hJ
      (fun _ d _ d' hI _ hQ => by obtain ⟨r, hs, -⟩ := hQ; exact ptResv_keeps hI hs)
  refine ⟨H1, hJ1, fun d hM hI hdef => ?_⟩
  have e1 : σ1 "pn" = BitVec.ofNat 32 nn := by
    rw [hfr "pn" (by decide) (by decide) (by decide) (by decide)]; exact hn
  have e2 : σ1 "vaddr" = BitVec.ofNat 32 vadr := by
    rw [hfr "vaddr" (by decide) (by decide) (by decide) (by decide)]; exact hva
  have e3 : σ1 "perm" = BitVec.ofNat 32 perm := by
    rw [hfr "perm" (by decide) (by decide) (by decide) (by decide)]; exact hpe
  obtain ⟨σ2, rb, S3, H3, d', hst, hl3, hid, hM3, hI3, r, hs, hr⟩ :=
    hall d hM hI ⟨(Locals.set_same _ _ _).trans e1, (Locals.set_other _ _ (by decide)).trans e2,
      (Locals.set_other _ _ (by decide)).trans e3, hI.1, hI.2 nn, hdef⟩
  exact ⟨σ2, rb, S3, H3, d', r, hst, hl3, hid, hM3, hI3, hs, hr⟩

/-- **`offer_shared_mem` under the lock keeps the invariant.** -/
theorem offer_locked_inv {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (hL : SLayout maxpage num_id cb num_proc pb ib fb sb)
    (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (p1 p2 va : Nat) (hva : va < 2 ^ 32)
    (hp1 : σ "pid1" = BitVec.ofNat 32 p1) (hp2 : σ "pid2" = BitVec.ofNat 32 p2)
    (hsva : σ "sva" = BitVec.ofNat 32 va)
    (hRJ : RelyJ εR c iv.toNat (fun b => ∃ d : SData,
      MatchS maxpage num_id cb num_proc pb ib fb ida sb d b ∧ MMI maxpage kl kh d.toPTData))
    (hJ : ∃ d : SData, MatchS maxpage num_id cb num_proc pb ib fb ida sb d (hmemR iv.toNat H) ∧
      MMI maxpage kl kh d.toPTData) :
    ∃ H1 : HLogR,
      (∃ d : SData, MatchS maxpage num_id cb num_proc pb ib fb ida sb d (hmemR iv.toNat H1) ∧
        MMI maxpage kl kh d.toPTData) ∧
      ∀ d : SData, MatchS maxpage num_id cb num_proc pb ib fb ida sb d (hmemR iv.toNat H1) →
        MMI maxpage kl kh d.toPTData →
        (∃ d1 r, offer_shared_mem_spec num_proc maxpage p1 p2 va d = some (d1, r)) →
        ∃ (σ2 : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR) (d' : SData) (r : Nat),
          Star (rprimsA εR c) ⟨.seq acquireA (.seq (offerS cb maxpage pb fb sb num_proc) relA), .stop, σ, l⟩
            ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          MatchS maxpage num_id cb num_proc pb ib fb ida sb d' (hmemR iv.toNat H3) ∧
          MMI maxpage kl kh d'.toPTData ∧
          offer_shared_mem_spec num_proc maxpage p1 p2 va d = some (d', r) ∧ σ2 "r" = BitVec.ofNat 32 r := by
  obtain ⟨σ1, r1, H1, -, hfr, hJ1, hall⟩ :=
    Triple.locked_inv hE hRR hc hRA hl hidle bound K hK hF σ hσ
      (offer_triple εR c iv.toNat hL hmax hnum hmp hnn (ida := ida) (kl := kl) (kh := kh) p1 p2 va hva)
      (I := fun d : SData => MMI maxpage kl kh d.toPTData) (I' := fun d : SData => MMI maxpage kl kh d.toPTData)
      hRJ hJ (fun _ d _ d' hI _ hQ => by obtain ⟨r, hs, -⟩ := hQ; exact offer_keeps hI hs)
  refine ⟨H1, hJ1, fun d hM hI hdef => ?_⟩
  have e1 : σ1 "pid1" = BitVec.ofNat 32 p1 := by
    rw [hfr "pid1" (by decide) (by decide) (by decide) (by decide)]; exact hp1
  have e2 : σ1 "pid2" = BitVec.ofNat 32 p2 := by
    rw [hfr "pid2" (by decide) (by decide) (by decide) (by decide)]; exact hp2
  have e3 : σ1 "sva" = BitVec.ofNat 32 va := by
    rw [hfr "sva" (by decide) (by decide) (by decide) (by decide)]; exact hsva
  obtain ⟨σ2, rb, S3, H3, d', hst, hl3, hid, hM3, hI3, r, hs, hr⟩ :=
    hall d hM hI ⟨e1, e2, e3, hI.1, hI.2, hdef⟩
  exact ⟨σ2, rb, S3, H3, d', r, hst, hl3, hid, hM3, hI3, hs, hr⟩

end Locked

end MMInv
