import CertiKOS.LockRegionCPU

/-!
# Kernel, memory management: the physical page allocator

The first kernel module, the bottom of mCertiKOS's memory management
(`MALInit`/`MALOp`/`MALT` in `mcertikos/mm`). It is also the example Kim et
al. use for a lock-protected kernel object (their `palloc`, §5).

The **allocation table** `AT` is a region protected by one lock: cell `j` is 0
when page `j` is free, and nonzero when it is allocated. `palloc` and `pfree`
are critical sections on it.

* `cs_guarantee`: the generic step. For any critical section `C` with a
  verified run on the region (`hC`), the code `acquire(lk); C; release(lk)`
  finishes idle on a valid log, and the region it releases is related by `C`'s
  specification to the region of the last release. Each kernel object below
  is one instance.
* `pallocSpec`: the abstract allocator. It marks the first free page and
  returns it, or returns `np` when no page is free.
* `pallocCS`: the C scan loop over the table (`rd`, test, `wr`).
  `scan_run`: the loop computes `pallocSpec`.
* `palloc_guarantee`: **`palloc` refines the atomic `pallocSpec`.** The
  returned page and the released table are `pallocSpec` of the table the
  previous holder released.
* `palloc_fresh`: the returned page was free, is now allocated, and no other
  entry changed. `pfree_guarantee`: `pfree(j)` clears entry `j`.
-/

namespace KernPAlloc

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR)
open LockRegionCPU

/-! ## A critical section on a region -/

/-- **`acquire(lk); C; release(lk)` for any verified critical section `C`.**
`R b σ b' σ'` is `C`'s specification: from region `b` and locals `σ` it ends
with region `b'` and locals `σ'`. -/
theorem cs_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (C : Stmt APrim) (R : Region → Locals → Region → Locals → Prop)
    (hC : ∀ (σ : Locals) (l : RLog) (K : Cont APrim) (S : RState) (H : HLogR), σ "lk" = iv →
      rreplay l = some (S, H) → LockRegion.Holding S c iv.toNat →
      ∃ σ' l' S', Star (rprimsA εR c) ⟨C, K, σ, l⟩ ⟨.skip, K, σ', l'⟩ ∧ rreplay l' = some (S', H) ∧
        S'.lk = S.lk ∧ σ' "lk" = iv ∧ R (S.mem iv.toNat) σ (S'.mem iv.toNat) σ') :
    ∃ (σ1 σ2 : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨.seq acquireA (.seq C relA), .stop, σ, l⟩ ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) ∧
      R (hmemR iv.toNat H1) σ1 (hmemR iv.toNat H3) σ2 := by
  -- acquire: on the lock array, then lifted
  obtain ⟨SA, HA, hA, hlkA⟩ := rreplay_erase hl
  have hidleA : (SA.lk iv.toNat).phase c = .idle := by rw [hlkA]; exact hidle
  obtain ⟨r, hspec⟩ := LockArray.acquireA_live_bounded hc hRA hA hidleA bound K hK hF
  obtain ⟨r0, σ1, -, -, hσ1, hstA⟩ := LockArray.acquireA_sim ε c _ σ iv (erase l) r .stop hσ hspec
  obtain ⟨-, -, SA1, HA1, hA1, hholdA, -, -⟩ := LockArray.acquireA_guarantee hc hRA hA hidleA hspec
  obtain ⟨⟨s1, k1, σy, r1⟩, hstR, hy⟩ := star_liftR hE c hstA ⟨acquireA, .stop, σ, l⟩ rfl lockS_acquireA trivial
  simp only [erC, Config.mk.injEq] at hy
  obtain ⟨rfl, rfl, rfl, her⟩ := hy
  obtain ⟨S1, H1, hl1, hq1⟩ := lock_run_valid (i := iv.toNat) hRR hstR lockS_acquireA trivial
    ⟨S, H, hl, fun hh => by obtain ⟨t, ht⟩ := hh; rw [hidle] at ht; cases ht⟩ ⟨SA1, HA1, by rw [her]; exact hA1⟩
  have hold1 : LockRegion.Holding S1 c iv.toNat := by
    obtain ⟨SA1', HA1', hA1', hlk1'⟩ := rreplay_erase hl1
    rw [her, hA1] at hA1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hA1'; obtain ⟨rfl, -⟩ := hA1'
    obtain ⟨t, ht⟩ := hholdA; exact ⟨t, by rw [← hlk1']; exact ht⟩
  have hsee : S1.mem iv.toNat = hmemR iv.toNat H1 := LockRegion.acquire_sees hl1 (hq1 hold1)
  have hσlk : σy "lk" = iv := by
    rw [hσ1 "lk" (by decide) (by decide) (by decide) (by decide)]; exact hσ
  -- the critical section
  obtain ⟨σ2, r2, S2, hcrit, hl2, hlk2, hσ2, hR⟩ := hC σy r1 (.seq relA .stop) S1 H1 hσlk hl1 hold1
  have hold2 : LockRegion.Holding S2 c iv.toNat := by
    obtain ⟨t, ht⟩ := hold1; exact ⟨t, by rw [hlk2]; exact ht⟩
  -- release
  obtain ⟨S2', H2', hl2'⟩ := hRR _ S2 H1 hl2
  obtain ⟨g1, g2⟩ := rothers (c := c) (i := iv.toNat) hl2 (εR.query c r2) (εR.noSelf c r2) hl2'
  obtain ⟨t, ht⟩ := hold2
  have ht' : (S2'.lk iv.toNat).phase c = .holding t := by rw [g1 iv.toNat]; exact ht
  have hps : pstep (S2'.lk iv.toNat) ⟨c, .incNow⟩ = some (⟨(S2'.lk iv.toNat).ticket, (S2'.lk iv.toNat).now + 1,
      setPhase (S2'.lk iv.toNat).phase c .idle⟩, some (.rel c)) := by simp [pstep, hc, ht']
  have hrs : rstep S2' (rev c iv.toNat .incNow) = some (⟨upd S2'.lk iv.toNat ⟨(S2'.lk iv.toNat).ticket,
      (S2'.lk iv.toNat).now + 1, setPhase (S2'.lk iv.toNat).phase c .idle⟩, S2'.mem,
      upd S2'.dirty iv.toNat false⟩, some (.relR c iv.toNat (S2'.mem iv.toNat))) := by
    simp [rstep, rev, hps, LockRegion.lift]
  have hl3 := LockRegion.rreplay_cons_of hl2' hrs
  have hmem2' : S2'.mem iv.toNat = S2.mem iv.toNat := (g2 ⟨t, ht⟩).1
  refine ⟨σy, σ2, rev c iv.toNat .incNow :: rpull εR c r2, _, H1, _, ?_, hl3, by simp, hσ1, ?_⟩
  · have hfr := MCSBoundC.star_app hstR (.seq (.seq C relA) .stop) rfl
    refine .step (c' := ⟨acquireA, .seq (.seq C relA) .stop, σ, l⟩) rfl (hfr.trans ?_)
    refine .step (c' := ⟨.seq C relA, .stop, σy, r1⟩) rfl ?_
    refine .step (c' := ⟨C, .seq relA .stop, σy, r1⟩) rfl (hcrit.trans ?_)
    refine .step (c' := ⟨relA, .stop, σ2, r2⟩) rfl ?_
    exact Star.single (by simp [step, rprimsA, relA, Expr.eval, lkE, hσ2])
  · have : hmemR iv.toNat (LockRegion.consO (some (.relR c iv.toNat (S2'.mem iv.toNat))) H2') =
        S2.mem iv.toNat := by simp [LockRegion.consO, hmemR, hmem2']
    rw [this, ← hsee]; exact hR

/-! ## The allocation table and its abstract operations -/

/-- The first free page among `n` pages starting at `m`. -/
def findFree (b : Region) : Nat → Nat → Option Nat
  | _, 0 => none
  | m, n + 1 => if b m = 0 then some m else findFree b (m + 1) n

/-- Allocate from page `m` on: mark the first free page, or return `np`. -/
def allocFrom (np : Nat) (b : Region) (m n : Nat) : Region × Nat :=
  match findFree b m n with
  | some j => (setCell b j 1, j)
  | none => (b, np)

/-- **The abstract `palloc`** on a table of `np` pages. -/
def pallocSpec (np : Nat) (b : Region) : Region × Nat := allocFrom np b 0 np

theorem findFree_some {b : Region} : ∀ {n m j : Nat}, findFree b m n = some j →
    m ≤ j ∧ j < m + n ∧ b j = 0 ∧ ∀ k, m ≤ k → k < j → b k ≠ 0
  | 0, _, _, h => by simp [findFree] at h
  | n + 1, m, j, h => by
    simp only [findFree] at h
    split at h
    · rename_i hz
      simp only [Option.some.injEq] at h; subst h
      exact ⟨Nat.le_refl _, by omega, hz, fun k h1 h2 => by omega⟩
    · rename_i hz
      obtain ⟨h1, h2, h3, h4⟩ := findFree_some h
      refine ⟨by omega, by omega, h3, fun k hk1 hk2 => ?_⟩
      by_cases hkm : k = m
      · subst hkm; exact hz
      · exact h4 k (by omega) hk2

theorem findFree_none {b : Region} : ∀ {n m : Nat}, findFree b m n = none → ∀ k, m ≤ k → k < m + n → b k ≠ 0
  | 0, _, _, k, h1, h2 => by omega
  | n + 1, m, h, k, h1, h2 => by
    simp only [findFree] at h
    split at h
    · simp at h
    · rename_i hz
      by_cases hkm : k = m
      · subst hkm; exact hz
      · exact findFree_none h k (by omega) (by omega)

/-- **`palloc` returns a fresh page.** The returned page was free, is now
allocated, and no other entry changed. If no page is free it returns `np`
and changes nothing. -/
theorem palloc_fresh (np : Nat) (b : Region) :
    let r := pallocSpec np b
    (r.2 < np → b r.2 = 0 ∧ r.1 r.2 = 1 ∧ (∀ k, k ≠ r.2 → r.1 k = b k) ∧ ∀ k, k < r.2 → b k ≠ 0) ∧
    (¬ r.2 < np → r.1 = b ∧ ∀ k, k < np → b k ≠ 0) := by
  simp only [pallocSpec, allocFrom]
  cases h : findFree b 0 np with
  | none =>
    refine ⟨fun hlt => absurd hlt (Nat.lt_irrefl _), fun _ => ⟨rfl, fun k hk => ?_⟩⟩
    exact findFree_none h k (Nat.zero_le _) (by omega)
  | some j =>
    obtain ⟨-, h2, h3, h4⟩ := findFree_some h
    refine ⟨fun _ => ⟨h3, by simp [setCell], fun k hk => by simp [setCell, hk],
      fun k hk => h4 k (Nat.zero_le _) hk⟩, fun hn => absurd (by simpa using h2) hn⟩

/-! ## The C code -/

/-- One iteration: read entry `i`; if free, mark it and stop, else move on. -/
def scanBody (npv : Val) : Stmt APrim :=
  .seq (.call "x" .pull [lkE, .var "i"])
    (.ite (.bin .eq (.var "x") (.const 0))
      (.seq (.call "_" .push [lkE, .var "i", .const 1]) (.seq (.assign "r" (.var "i")) (.assign "i" (.const npv))))
      (.assign "i" (.bin .add (.var "i") (.const 1))))

def scanLoop (npv : Val) : Stmt APrim := .while (.bin .ne (.var "i") (.const npv)) (scanBody npv)

/-- `i = 0; r = np; while (i != np) { x = AT[i]; if (x == 0) { AT[i] = 1; r = i; i = np; } else i++; }` -/
def pallocCS (npv : Val) : Stmt APrim :=
  .seq (.assign "i" (.const 0)) (.seq (.assign "r" (.const npv)) (scanLoop npv))

/-- `palloc()`: the result is in `r`. -/
def palloc (npv : Val) : Stmt APrim := .seq acquireA (.seq (pallocCS npv) relA)

theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : a ≠ b) :
    (BitVec.ofNat 32 a : Val) ≠ BitVec.ofNat 32 b := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact h this

/-- **The scan loop computes the allocator.** -/
theorem scan_run (εR : REnv) (c : CPU) (iv : Val) (np : Nat) (hnp : np < 2 ^ 32) :
    ∀ (n m : Nat), m + n = np → ∀ (σ : Locals) (l : RLog) (K : Cont APrim) (S : RState) (H : HLogR),
      σ "i" = BitVec.ofNat 32 m → σ "r" = BitVec.ofNat 32 np → σ "lk" = iv → rreplay l = some (S, H) →
      LockRegion.Holding S c iv.toNat →
      ∃ σ' l' S', Star (rprimsA εR c) ⟨scanLoop (BitVec.ofNat 32 np), K, σ, l⟩ ⟨.skip, K, σ', l'⟩ ∧
        rreplay l' = some (S', H) ∧ S'.lk = S.lk ∧ σ' "lk" = iv ∧
        S'.mem iv.toNat = (allocFrom np (S.mem iv.toNat) m n).1 ∧
        σ' "r" = BitVec.ofNat 32 (allocFrom np (S.mem iv.toNat) m n).2
  | 0, m, hm, σ, l, K, S, H, hi, hr, hlk, hl, _ => by
    have hmn : m = np := by omega
    subst hmn
    refine ⟨σ, l, S, Star.single ?_, hl, rfl, hlk, by simp [allocFrom, findFree], by simp [allocFrom, findFree, hr]⟩
    simp [step, scanLoop, Expr.eval, BinOp.eval, hi]
  | n + 1, m, hm, σ, l, K, S, H, hi, hr, hlk, hl, hh => by
    have hmlt : m < 2 ^ 32 := by omega
    have hne : (BitVec.ofNat 32 m : Val) ≠ BitVec.ofNat 32 np := ofNat_ne hmlt hnp (by omega)
    have hmm : (BitVec.ofNat 32 m : Val).toNat = m := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hmlt
    let npv : Val := BitVec.ofNat 32 np
    let v : Val := LockRegion.memOf iv.toNat l m
    have hv : v = S.mem iv.toNat m := by
      have := LockRegion.rreplay_mem hl iv.toNat; simp only [v, ← this]
    let σ1 := σ.set "x" v
    let KL : Cont APrim := .loop (.bin .ne (.var "i") (.const npv)) (scanBody npv) K
    let ITE : Stmt APrim := .ite (.bin .eq (.var "x") (.const 0))
      (.seq (.call "_" .push [lkE, .var "i", .const 1]) (.seq (.assign "r" (.var "i")) (.assign "i" (.const npv))))
      (.assign "i" (.bin .add (.var "i") (.const 1)))
    -- up to the test
    have hpre : Star (rprimsA εR c) ⟨scanLoop npv, K, σ, l⟩ ⟨ITE, KL, σ1, l⟩ := by
      refine .step (c' := ⟨scanBody npv, KL, σ, l⟩)
        (by simp [step, scanLoop, Expr.eval, BinOp.eval, hi, hne, KL, npv]) ?_
      refine .step (c' := ⟨.call "x" .pull [lkE, .var "i"], .seq ITE KL, σ, l⟩) rfl ?_
      refine .step (c' := ⟨.skip, .seq ITE KL, σ1, l⟩)
        (by simp [step, rprimsA, Expr.eval, lkE, hlk, hi, hmm, σ1, v]) ?_
      exact Star.single rfl
    by_cases hz : S.mem iv.toNat m = 0#32
    · -- free: mark it, record it, leave the loop
      let e : REvent := ⟨c, iv.toNat, .wr m 1⟩
      let S2 : RState := ⟨S.lk, upd S.mem iv.toNat (setCell (S.mem iv.toNat) m 1), upd S.dirty iv.toNat true⟩
      have hs : rstep S e = some (S2, none) := by simp [rstep, e, hh, S2]
      have hl2 := LockRegion.rreplay_cons_of hl hs
      let σ2 := σ1.set "_" 0
      let σ3 := σ2.set "r" (BitVec.ofNat 32 m)
      let σ4 := σ3.set "i" npv
      have hx0 : σ1 "x" = 0 := by simp [σ1, hv, hz]
      refine ⟨σ4, e :: l, S2, hpre.trans ?_, by simpa [LockRegion.consO] using hl2, rfl,
        by simp [σ4, σ3, σ2, σ1, Locals.set, hlk], ?_, ?_⟩
      · refine .step (c' := ⟨.seq (.call "_" .push [lkE, .var "i", .const 1])
          (.seq (.assign "r" (.var "i")) (.assign "i" (.const npv))), KL, σ1, l⟩)
          (by simp [step, ITE, Expr.eval, BinOp.eval, hx0]) ?_
        refine .step (c' := ⟨.call "_" .push [lkE, .var "i", .const 1],
          .seq (.seq (.assign "r" (.var "i")) (.assign "i" (.const npv))) KL, σ1, l⟩) rfl ?_
        refine .step (c' := ⟨.skip, .seq (.seq (.assign "r" (.var "i")) (.assign "i" (.const npv))) KL, σ2,
          e :: l⟩) (by simp [step, rprimsA, Expr.eval, lkE, σ1, Locals.set, hlk, hi, hmm, σ2, e]) ?_
        refine .step (c' := ⟨.seq (.assign "r" (.var "i")) (.assign "i" (.const npv)), KL, σ2, e :: l⟩) rfl ?_
        refine .step (c' := ⟨.assign "r" (.var "i"), .seq (.assign "i" (.const npv)) KL, σ2, e :: l⟩) rfl ?_
        refine .step (c' := ⟨.skip, .seq (.assign "i" (.const npv)) KL, σ3, e :: l⟩)
          (by simp [step, Expr.eval, σ3, σ2, σ1, Locals.set, hi]) ?_
        refine .step (c' := ⟨.assign "i" (.const npv), KL, σ3, e :: l⟩) rfl ?_
        refine .step (c' := ⟨.skip, KL, σ4, e :: l⟩) (by simp [step, Expr.eval, σ4]) ?_
        refine .step (c' := ⟨scanLoop npv, K, σ4, e :: l⟩) rfl ?_
        exact Star.single (by simp [step, scanLoop, Expr.eval, BinOp.eval, σ4, npv])
      · simp [S2, allocFrom, findFree, hz]
      · simp [σ4, σ3, Locals.set, allocFrom, findFree, hz]
    · -- taken: move on
      let σ2 := σ1.set "i" (BitVec.ofNat 32 (m + 1))
      have hx0 : ¬ σ1 "x" = 0#32 := by simp [σ1, hv, hz]
      have hi2 : σ2 "i" = BitVec.ofNat 32 (m + 1) := by simp [σ2]
      have hr2 : σ2 "r" = BitVec.ofNat 32 np := by simp [σ2, σ1, Locals.set, hr]
      have hlk2 : σ2 "lk" = iv := by simp [σ2, σ1, Locals.set, hlk]
      obtain ⟨σ', l', S', hrun, hl', hlk', hσ', hmem, hres⟩ :=
        scan_run εR c iv np hnp n (m + 1) (by omega) σ2 l K S H hi2 hr2 hlk2 hl hh
      refine ⟨σ', l', S', hpre.trans ?_, hl', hlk', hσ', ?_, ?_⟩
      · refine .step (c' := ⟨.assign "i" (.bin .add (.var "i") (.const 1)), KL, σ1, l⟩)
          (by simp [step, ITE, Expr.eval, BinOp.eval, hx0]) ?_
        refine .step (c' := ⟨.skip, KL, σ2, l⟩)
          (by simp [step, Expr.eval, BinOp.eval, σ2, σ1, Locals.set, hi, BitVec.ofNat_add]) ?_
        exact .step (c' := ⟨scanLoop npv, K, σ2, l⟩) rfl hrun
      · rw [hmem]; simp [allocFrom, findFree, hz]
      · rw [hres]; simp [allocFrom, findFree, hz]

/-- The critical section of `palloc` computes `pallocSpec`. -/
theorem pallocCS_run (εR : REnv) (c : CPU) (iv : Val) (np : Nat) (hnp : np < 2 ^ 32) (σ : Locals) (l : RLog)
    (K : Cont APrim) (S : RState) (H : HLogR) (hlk : σ "lk" = iv) (hl : rreplay l = some (S, H))
    (hh : LockRegion.Holding S c iv.toNat) :
    ∃ σ' l' S', Star (rprimsA εR c) ⟨pallocCS (BitVec.ofNat 32 np), K, σ, l⟩ ⟨.skip, K, σ', l'⟩ ∧
      rreplay l' = some (S', H) ∧ S'.lk = S.lk ∧ σ' "lk" = iv ∧
      (S'.mem iv.toNat = (pallocSpec np (S.mem iv.toNat)).1 ∧
        σ' "r" = BitVec.ofNat 32 (pallocSpec np (S.mem iv.toNat)).2) := by
  let npv : Val := BitVec.ofNat 32 np
  let σ1 := σ.set "i" 0
  let σ2 := σ1.set "r" npv
  obtain ⟨σ', l', S', hrun, hl', hlk', hσ', hmem, hres⟩ :=
    scan_run εR c iv np hnp np 0 (by omega) σ2 l K S H (by simp [σ2, σ1, Locals.set]) (by simp [σ2, npv])
      (by simp [σ2, σ1, Locals.set, hlk]) hl hh
  refine ⟨σ', l', S', ?_, hl', hlk', hσ', hmem, hres⟩
  refine .step (c' := ⟨.assign "i" (.const 0), .seq (.seq (.assign "r" (.const npv)) (scanLoop npv)) K, σ, l⟩)
    rfl ?_
  refine .step (c' := ⟨.skip, .seq (.seq (.assign "r" (.const npv)) (scanLoop npv)) K, σ1, l⟩)
    (by simp [step, Expr.eval, σ1]) ?_
  refine .step (c' := ⟨.seq (.assign "r" (.const npv)) (scanLoop npv), K, σ1, l⟩) rfl ?_
  refine .step (c' := ⟨.assign "r" (.const npv), .seq (scanLoop npv) K, σ1, l⟩) rfl ?_
  refine .step (c' := ⟨.skip, .seq (scanLoop npv) K, σ2, l⟩) (by simp [step, Expr.eval, σ2]) ?_
  exact .step (c' := ⟨scanLoop npv, K, σ2, l⟩) rfl hrun

/-- **`palloc` refines the abstract allocator.** Under an environment that keeps
the region log valid, and the lock's fairness, `palloc()` finishes idle on a
valid log. The page it returns and the table it releases are `pallocSpec` of
the table the previous holder released. -/
theorem palloc_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (np : Nat) (hnp : np < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨palloc (BitVec.ofNat 32 np), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = (pallocSpec np (hmemR iv.toNat H1)).1 ∧
      σ' "r" = BitVec.ofNat 32 (pallocSpec np (hmemR iv.toNat H1)).2 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, -, hR1, hR2⟩ :=
    cs_guarantee hE hRR hc hRA hl hidle bound K hK hF σ hσ (pallocCS (BitVec.ofNat 32 np))
      (fun b _ b' σ' => b' = (pallocSpec np b).1 ∧ σ' "r" = BitVec.ofNat 32 (pallocSpec np b).2)
      (fun σ l K S H hlk hl hh => pallocCS_run εR c iv np hnp σ l K S H hlk hl hh)
  exact ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, hR1, by simp [Locals.set, hR2]⟩

/-! ## `pfree` -/

/-- `pfree(j)`: clear entry `j`. -/
def pfreeCS : Stmt APrim := .call "_" .push [lkE, .var "j", .const 0]

def pfree : Stmt APrim := .seq acquireA (.seq pfreeCS relA)

/-- **`pfree(j)` clears entry `j`** of the table the previous holder released,
and changes nothing else. -/
theorem pfree_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨pfree, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = setCell (hmemR iv.toNat H1) (σ "j").toNat 0 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hfr, hR⟩ :=
    cs_guarantee hE hRR hc hRA hl hidle bound K hK hF σ hσ pfreeCS
      (fun b σ b' _ => b' = setCell b (σ "j").toNat 0)
      (fun σ l K S H hlk hl hh => by
        have hs : rstep S ⟨c, iv.toNat, .wr (σ "j").toNat 0⟩ = some (⟨S.lk, upd S.mem iv.toNat
            (setCell (S.mem iv.toNat) (σ "j").toNat 0), upd S.dirty iv.toNat true⟩, none) := by
          simp [rstep, hh]
        exact ⟨σ.set "_" 0, ⟨c, iv.toNat, .wr (σ "j").toNat 0⟩ :: l, ⟨S.lk, upd S.mem iv.toNat
            (setCell (S.mem iv.toNat) (σ "j").toNat 0), upd S.dirty iv.toNat true⟩,
          Star.single (by simp [step, pfreeCS, rprimsA, Expr.eval, lkE, hlk]),
          by simpa [LockRegion.consO] using LockRegion.rreplay_cons_of hl hs, rfl,
          by simp [Locals.set, hlk], by simp⟩)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, ?_⟩
  rw [hR, hfr "j" (by decide) (by decide) (by decide) (by decide)]

end KernPAlloc
