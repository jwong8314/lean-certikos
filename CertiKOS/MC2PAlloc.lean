import CertiKOS.MC2Atomic
import CertiKOS.KernPAlloc

/-!
# mC2: the page allocator as an atomic object

mC2's physical memory management ([OSDI16] §4, Fig. 8) keeps the page
allocation table `AT` and the containers `cn` (one per thread, holding its
quota) under one lock, `lock_AT`. `palloc(tid)` refuses when the thread has
no quota left, and otherwise takes the first free page and uses one unit of
the quota:

```
if (cn[tid].quota < 1) return ERROR;
acq_lock(lock_AT);
scan AT for the first free page fp;
if (fp != nps) { AT[fp] taken; cn[tid].quota--; } else fp = ERROR;
rel_lock(lock_AT);
return fp;
```

Here:

* **The region of `lock_AT`**: cells `0 … nps-1` are the table, 0 for a free
  page and nonzero for a taken one, as in `KernPAlloc`; cell `qb + t` is
  thread `t`'s quota.
* `pallocM`: the operation. `ERROR` is `nps`, the scan's "no page" value.
* `AT`: the atomic object. Its state is the region itself.
* `pallocBody`: the code inside the lock, which reuses `KernPAlloc`'s scan.
* `body_impl`: the body implements `pallocM` (an `Impl`).
* `palloc_atomic`: **`palloc(tid)` is one event `(c, tid)` of the allocator.**

**One change from Fig. 8:** the quota is read inside the lock, not before
it. In the push/pull model a shared cell may only be read under its lock,
and `cn` is in `lock_AT`'s region. Reading it outside would be a race unless
`cn[tid]` were private to thread `tid`; the paper does not say which.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MC2PAlloc

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA lkE apull)
open LockRegion (RLog RState HLogR rreplay REnv Region hmemR setCell)
open LockRegionCPU KernFrame Layer LogInv
open KernPAlloc (findFree allocFrom pallocSpec findFree_some pallocCS pallocCS_run)
open MC2

/-! ## The operation -/

/-- **`palloc(t)`** on the region of `lock_AT`: the new region and the page
(`nps` for `ERROR`). -/
def pallocM (nps qb t : Nat) (b : Region) : Region × Nat :=
  if b (qb + t) = 0 then (b, nps)
  else if (pallocSpec nps b).2 = nps then pallocSpec nps b
  else (setCell (pallocSpec nps b).1 (qb + t) (b (qb + t) - 1), (pallocSpec nps b).2)

/-- **The allocator as an atomic object**, from the initial region `b0`. -/
def AT (nps qb : Nat) (b0 : Region) : AObj where
  S := Region
  init := b0
  Op := Nat
  step := fun _ t b => pallocM nps qb t b
  rep := fun s b => s = b

theorem pallocSpec_le (np : Nat) (b : Region) : (pallocSpec np b).2 ≤ np := by
  unfold pallocSpec allocFrom
  cases h : findFree b 0 np with
  | none => exact Nat.le_refl _
  | some j => obtain ⟨-, h2, -⟩ := findFree_some h; simp only; omega

theorem pallocSpec_frame (np : Nat) (b : Region) : ∀ k, np ≤ k → (pallocSpec np b).1 k = b k := by
  intro k hk
  unfold pallocSpec allocFrom
  cases h : findFree b 0 np with
  | none => rfl
  | some j =>
    obtain ⟨-, h2, -⟩ := findFree_some h
    simp only [setCell]
    rw [if_neg (by omega)]

/-! ## The code -/

/-- The quota cell of the thread in `tid`. -/
def qE (qb : Nat) : Expr := .bin .add (.const (BitVec.ofNat 32 qb)) (.var "tid")

/-- The code inside `lock_AT`; the page is in `r`. -/
def pallocBody (nps qb : Nat) : Stmt APrim :=
  .seq (.call "q" .pull [lkE, qE qb])
    (.ite (.bin .eq (.var "q") (.const 0))
      (.assign "r" (.const (BitVec.ofNat 32 nps)))
      (.seq (pallocCS (BitVec.ofNat 32 nps))
        (.ite (.bin .ne (.var "r") (.const (BitVec.ofNat 32 nps)))
          (.call "_" .push [lkE, qE qb, .bin .sub (.var "q") (.const 1)])
          .skip)))

/-- **`palloc(tid)`**: `acq_lock(lock_AT); body; rel_lock(lock_AT)`. -/
def palloc (nps qb : Nat) : Stmt APrim := .seq acquireA (.seq (pallocBody nps qb) relA)

/-- **The body implements `pallocM`.** It writes the table and the caller's
quota cell, and nothing else. -/
theorem body_impl (εR : REnv) (c : CPU) (i : Nat) {nps qb t : Nat} (b0 : Region) (hnps : nps < 2 ^ 32)
    (hq : nps ≤ qb) (hqt : qb + t < 2 ^ 32) :
    Impl εR c i (AT nps qb b0) (fun k => k < nps ∨ k = qb + t) (fun σ => σ "tid" = BitVec.ofNat 32 t) t "r"
      (pallocBody nps qb) := by
  intro σ l b d hlk hcs hM hP
  have hdb : d = b := hM
  subst hdb
  have hqe : ∀ σ' : Locals, σ' "tid" = BitVec.ofNat 32 t → (qE qb).eval σ' = BitVec.ofNat 32 (qb + t) := by
    intro σ' h; simp [qE, Expr.eval, BinOp.eval, h, BitVec.ofNat_add]
  have hqn : (BitVec.ofNat 32 (qb + t) : Val).toNat = qb + t := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hqt
  have r1 := cs1_rd (εR := εR) hcs hlk "q" (qE qb)
  rw [hqe σ hP, hqn] at r1
  let σ1 := σ.set "q" (d (qb + t))
  have hσ1lk : σ1 "lk" = σ "lk" := by simp [σ1, Locals.set]
  have hσ1q : σ1 "q" = d (qb + t) := by simp [σ1, Locals.set]
  have hσ1t : σ1 "tid" = BitVec.ofNat 32 t := by simp [σ1, Locals.set, hP]
  by_cases hq0 : d (qb + t) = 0
  · -- no quota left: `ERROR`
    have hsp : pallocM nps qb t d = (d, nps) := by unfold pallocM; exact if_pos hq0
    refine ⟨σ1.set "r" (BitVec.ofNat 32 nps), l, d, d, ?_, hcs, rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
    · refine Runs.seq r1 (Runs.ite_true (by simp [Expr.eval, BinOp.eval, hσ1q, hq0]) ?_)
      exact Runs.assign "r" (.const (BitVec.ofNat 32 nps))
    · simp [Locals.set, σ1]
    · show d = (pallocM nps qb t d).1; rw [hsp]
    · show (σ1.set "r" (BitVec.ofNat 32 nps)) "r" = BitVec.ofNat 32 (pallocM nps qb t d).2
      rw [hsp]; simp [Locals.set]
  · -- the scan
    obtain ⟨S, H, hl, hh, hmem⟩ := hcs
    subst hlk
    obtain ⟨σ2, l2, S2, hst, hl2, hlkS, hσ2lk, hmem2, hr2⟩ := pallocCS_run εR c (σ1 "lk") nps hnps σ1 l .stop S H
      rfl hl (by rw [hσ1lk]; exact hh)
    rw [hσ1lk, hmem] at hmem2 hr2
    have r2 : Runs (rprimsA εR c) (pallocCS (BitVec.ofNat 32 nps)) σ1 l σ2 l2 := Runs.of_stop hst
    have hσ2q : σ2 "q" = d (qb + t) := by rw [r2.frame (z := "q") rfl]; exact hσ1q
    have hσ2t : σ2 "tid" = BitVec.ofNat 32 t := by rw [r2.frame (z := "tid") rfl]; exact hσ1t
    have hσ2lk' : σ2 "lk" = σ "lk" := by rw [hσ2lk, hσ1lk]
    have hcs2 : CS1 c (σ "lk").toNat l2 (pallocSpec nps d).1 :=
      ⟨S2, H, hl2, by obtain ⟨t', ht'⟩ := hh; exact ⟨t', by rw [hlkS]; exact ht'⟩, by rw [← hσ1lk]; exact hmem2⟩
    have hle := pallocSpec_le nps d
    have hfr0 : ∀ k, ¬ (k < nps ∨ k = qb + t) → (pallocSpec nps d).1 k = d k :=
      fun k hk => pallocSpec_frame nps d k (by omega)
    have hq0' : (Expr.bin .eq (.var "q") (.const 0)).eval σ1 = 0 := by
      simp only [Expr.eval, BinOp.eval, hσ1q]; exact if_neg hq0
    by_cases hfd : (pallocSpec nps d).2 = nps
    · -- no free page: `ERROR`
      have hsp : pallocM nps qb t d = pallocSpec nps d := by
        unfold pallocM; exact (if_neg hq0).trans (if_pos hfd)
      refine ⟨σ2, l2, _, _, ?_, hcs2, rfl, hσ2lk', hfr0, ?_, ?_⟩
      · refine Runs.seq r1 (Runs.ite_false hq0' (Runs.seq r2 (Runs.ite_false ?_ Runs.skip)))
        simp [Expr.eval, BinOp.eval, hr2, hfd]
      · show (pallocSpec nps d).1 = (pallocM nps qb t d).1; rw [hsp]
      · show σ2 "r" = BitVec.ofNat 32 (pallocM nps qb t d).2; rw [hsp, hr2]
    · -- a page: take it, and one unit of the quota
      have hsp : pallocM nps qb t d =
          (setCell (pallocSpec nps d).1 (qb + t) (d (qb + t) - 1), (pallocSpec nps d).2) := by
        unfold pallocM; exact (if_neg hq0).trans (if_neg hfd)
      obtain ⟨l3, r3, hcs3⟩ := cs1_wr (εR := εR) hcs2 (by rw [hσ2lk']) (qE qb) (.bin .sub (.var "q") (.const 1))
        (σ := σ2)
      rw [hqe σ2 hσ2t, hqn] at hcs3
      have hsub : (Expr.bin .sub (.var "q") (.const 1)).eval σ2 = d (qb + t) - 1 := by
        simp [Expr.eval, BinOp.eval, hσ2q]
      rw [hsub] at hcs3
      have hne : ¬ (Expr.bin .ne (.var "r") (.const (BitVec.ofNat 32 nps))).eval σ2 = 0 := by
        have h1 : (pallocSpec nps d).2 < 2 ^ 32 := by omega
        have : (BitVec.ofNat 32 (pallocSpec nps d).2 : Val) ≠ BitVec.ofNat 32 nps :=
          KernPAlloc.ofNat_ne h1 hnps hfd
        simp [Expr.eval, BinOp.eval, hr2, this]
      refine ⟨σ2.set "_" 0, l3, _, _, ?_, hcs3, rfl, ?_, ?_, ?_, ?_⟩
      · exact Runs.seq r1 (Runs.ite_false hq0' (Runs.seq r2 (Runs.ite_true hne r3)))
      · simp [Locals.set, hσ2lk']
      · intro k hk
        simp only [setCell]
        rw [if_neg (fun e => hk (Or.inr e))]
        exact hfr0 k hk
      · show setCell (pallocSpec nps d).1 (qb + t) (d (qb + t) - 1) = (pallocM nps qb t d).1; rw [hsp]
      · show (σ2.set "_" 0) "r" = BitVec.ofNat 32 (pallocM nps qb t d).2
        rw [hsp]; simp [Locals.set, hr2]

/-- **`palloc(tid)` is one event `(c, tid)` of the allocator.** The table and
quotas it finds are the replay of a history `h` of allocations, and the ones
it releases are the replay of `(c, tid) :: h`; the page it returns is what
`pallocM` returns after `h`. -/
theorem palloc_atomic {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    {nps qb t : Nat} (b0 : Region) (hnps : nps < 2 ^ 32) (hq : nps ≤ qb) (hqt : qb + t < 2 ^ 32)
    (σ : Locals) (hσ : σ "lk" = iv) (htid : σ "tid" = BitVec.ofNat 32 t)
    (hRJ : RelyJ εR c iv.toNat (AT nps qb b0).J) (hJ : (AT nps qb b0).J (hmemR iv.toNat H)) :
    ∃ H1 : HLogR, (AT nps qb b0).J (hmemR iv.toNat H1) ∧
      ∀ h, (AT nps qb b0).rep ((AT nps qb b0).replay h) (hmemR iv.toNat H1) →
        ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR),
          Star (rprimsA εR c) ⟨palloc nps qb, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          hmemR iv.toNat H3 = ((AT nps qb b0).replay ((c, t) :: h)) ∧ (AT nps qb b0).J (hmemR iv.toNat H3) ∧
          σ' "r" = BitVec.ofNat 32 (pallocM nps qb t ((AT nps qb b0).replay h)).2 := by
  obtain ⟨H1, hJ1, hrest⟩ := atomic_call hE hRR hc hRA hl hidle bound K hK hF σ hσ
    (body_impl εR c iv.toNat b0 hnps hq hqt (t := t)) (by decide)
    (fun σ1 hfr => by rw [hfr "tid" (by decide) (by decide) (by decide) (by decide)]; exact htid) hRJ hJ
  refine ⟨H1, hJ1, fun h hM => ?_⟩
  obtain ⟨σ', rb, S3, H3, hrun, hl3, hid, hM3, hJ3, hr⟩ := hrest h hM
  exact ⟨σ', rb, S3, H3, hrun, hl3, hid, hM3.symm, hJ3, hr⟩

end MC2PAlloc
