import CertiKOS.KernContainer

/-!
# Kernel, memory management: page ownership

The allocation table of `KernPAlloc.lean` records only whether a page is free.
mCertiKOS's records who owns it, and the kernel's isolation arguments start
there. This file adds the owner.

Cell `j` of the allocation table is now a **tag**: 0 when page `j` is free, 1
when the kernel owns it (the pages of page tables, which `KernPT.lean`
allocates with `palloc`), and `id + 2` when container `id` owns it.

* `CS1`, `cs_guarantee1`: the one-lock step in the style of `KernFrame`
  (`Runs`, and a state predicate with no second lock).
* `pallocOSpec`, `pallocO_guarantee`: **`palloc` with an owner.** The first
  free page is tagged with the caller's tag `o`.
* `pfreeOSpec`, `pfreeO_guarantee`: **`pfree` checks the owner.** Page `j` is
  freed only if its tag is `o`. The result says whether it was.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace KernOwner

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding)
open LockRegionCPU KernPAlloc KernFrame
open KernPT (setCell_eq setCell_ne)

/-! ## The one-lock step, with `Runs` -/

/-- Inside a critical section on lock `i`: the log is valid, we hold `i`, and
region `i` is `b`. -/
def CS1 (c : CPU) (i : Nat) (l : RLog) (b : Region) : Prop :=
  ∃ S H, rreplay l = some (S, H) ∧ Holding S c i ∧ S.mem i = b

theorem cs1_rd {εR : REnv} {c : CPU} {i : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (x : Ident) (je : Expr) :
    Runs (rprimsA εR c) (.call x .pull [lkE, je]) σ l (σ.set x (b (je.eval σ).toNat)) l := by
  obtain ⟨S, H, hl, -, rfl⟩ := h
  have hm := LockRegion.rreplay_mem hl i
  rw [hm]
  exact Runs.call (by simp [rprimsA, lkE, Expr.eval, hlk])

theorem cs1_wr {εR : REnv} {c : CPU} {i : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (je ve : Expr) :
    ∃ l', Runs (rprimsA εR c) (.call "_" .push [lkE, je, ve]) σ l (σ.set "_" 0) l' ∧
      CS1 c i l' (setCell b (je.eval σ).toNat (ve.eval σ)) := by
  obtain ⟨S, H, hl, hh, rfl⟩ := h
  have hs : rstep S ⟨c, i, .wr (je.eval σ).toNat (ve.eval σ)⟩ = some (⟨S.lk, upd S.mem i
      (setCell (S.mem i) (je.eval σ).toNat (ve.eval σ)), upd S.dirty i true⟩, none) := by simp [rstep, hh]
  have hl2 := LockRegion.rreplay_cons_of hl hs
  exact ⟨⟨c, i, .wr (je.eval σ).toNat (ve.eval σ)⟩ :: l, Runs.call (by simp [rprimsA, lkE, Expr.eval, hlk]),
    ⟨S.lk, upd S.mem i (setCell (S.mem i) (je.eval σ).toNat (ve.eval σ)), upd S.dirty i true⟩, H,
    by simpa [LockRegion.consO] using hl2, hh, by simp⟩

/-- **`acquire(lk); C; release(lk)`** for a critical section `C` verified with
`Runs` and `CS1`. -/
theorem cs_guarantee1 {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (C : Stmt APrim) (R : Region → Locals → Region → Locals → Prop)
    (hC : ∀ (σ : Locals) (l : RLog) (b : Region), σ "lk" = iv → CS1 c iv.toNat l b →
      ∃ σ' l' b', Runs (rprimsA εR c) C σ l σ' l' ∧ CS1 c iv.toNat l' b' ∧ σ' "lk" = iv ∧ R b σ b' σ') :
    ∃ (σ1 σ2 : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨.seq acquireA (.seq C relA), .stop, σ, l⟩ ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) ∧
      R (hmemR iv.toNat H1) σ1 (hmemR iv.toNat H3) σ2 := by
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
  have hold1 : Holding S1 c iv.toNat := by
    obtain ⟨SA1', HA1', hA1', hlk1'⟩ := rreplay_erase hl1
    rw [her, hA1] at hA1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hA1'; obtain ⟨rfl, -⟩ := hA1'
    obtain ⟨t, ht⟩ := hholdA; exact ⟨t, by rw [← hlk1']; exact ht⟩
  have hsee : S1.mem iv.toNat = hmemR iv.toNat H1 := LockRegion.acquire_sees hl1 (hq1 hold1)
  have hσlk : σy "lk" = iv := by
    rw [hσ1 "lk" (by decide) (by decide) (by decide) (by decide)]; exact hσ
  obtain ⟨σ2, r2, b2, hcrit, ⟨S2, H2, hl2, hold2, hb2⟩, hσ2, hR⟩ :=
    hC σy r1 (S1.mem iv.toNat) hσlk ⟨S1, H1, hl1, hold1, rfl⟩
  obtain ⟨S2', H2', hl2'⟩ := hRR _ S2 H2 hl2
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
    refine .step (c' := ⟨C, .seq relA .stop, σy, r1⟩) rfl ((hcrit _).trans ?_)
    refine .step (c' := ⟨relA, .stop, σ2, r2⟩) rfl ?_
    exact Star.single (by simp [step, rprimsA, relA, Expr.eval, lkE, hσ2])
  · have : hmemR iv.toNat (LockRegion.consO (some (.relR c iv.toNat (S2'.mem iv.toNat))) H2') =
        S2.mem iv.toNat := by simp [LockRegion.consO, hmemR, hmem2']
    rw [this, hb2, ← hsee]; exact hR

/-! ## The allocation table with owners -/

/-- Allocate from page `m` on: tag the first free page with `o`, or return `np`. -/
def allocFromO (np : Nat) (o : Val) (b : Region) (m n : Nat) : Region × Nat :=
  match findFree b m n with
  | some j => (setCell b j o, j)
  | none => (b, np)

/-- **The abstract `palloc` for the owner with tag `o`.** -/
def pallocOSpec (np : Nat) (o : Val) (b : Region) : Region × Nat := allocFromO np o b 0 np

/-- `KernPAlloc`'s allocator is this one with the kernel's tag. -/
theorem pallocO_one (np : Nat) (b : Region) : pallocOSpec np 1 b = pallocSpec np b := rfl

/-- **The abstract `pfree` for the owner with tag `o`.** The page is freed only
if `o` owns it. The result is 1 if it was freed. -/
def pfreeOSpec (b : Region) (o : Val) (j : Nat) : Region × Val :=
  if b j = o then (setCell b j 0, 1) else (b, 0)

theorem pallocO_le (np : Nat) (o : Val) (a : Region) : (pallocOSpec np o a).2 ≤ np := by
  simp only [pallocOSpec, allocFromO]
  cases h : findFree a 0 np with
  | none => exact Nat.le_refl _
  | some j => have := (findFree_some h).2.1; simp only; omega

/-- **`palloc` returns a fresh page and tags it.** -/
theorem pallocO_fresh (np : Nat) (o : Val) (b : Region) :
    let r := pallocOSpec np o b
    (r.2 < np → b r.2 = 0 ∧ r.1 r.2 = o ∧ ∀ k, k ≠ r.2 → r.1 k = b k) ∧ (¬ r.2 < np → r.1 = b) := by
  simp only [pallocOSpec, allocFromO]
  cases h : findFree b 0 np with
  | none => exact ⟨fun hlt => absurd hlt (Nat.lt_irrefl _), fun _ => rfl⟩
  | some j =>
    obtain ⟨-, h2, h3, -⟩ := findFree_some h
    exact ⟨fun _ => ⟨h3, by simp [setCell], fun k hk => by simp [setCell, hk]⟩,
      fun hn => absurd (by simpa using h2) hn⟩

/-! ## The C code -/

/-- One iteration: read entry `i`; if free, tag it with `o` and stop, else move on. -/
def scanBodyO (npv : Val) : Stmt APrim :=
  .seq (.call "x" .pull [lkE, .var "i"])
    (.ite (.bin .eq (.var "x") (.const 0))
      (.seq (.call "_" .push [lkE, .var "i", .var "o"])
        (.seq (.assign "r" (.var "i")) (.assign "i" (.const npv))))
      (.assign "i" (.bin .add (.var "i") (.const 1))))

def scanLoopO (npv : Val) : Stmt APrim := .while (.bin .ne (.var "i") (.const npv)) (scanBodyO npv)

/-- `i = 0; r = np; while (i != np) { x = AT[i]; if (x == 0) { AT[i] = o; r = i; i = np; } else i++; }` -/
def pallocOCS (npv : Val) : Stmt APrim :=
  .seq (.assign "i" (.const 0)) (.seq (.assign "r" (.const npv)) (scanLoopO npv))

/-- `palloc(o)`: the result is in `r`. -/
def pallocO (npv : Val) : Stmt APrim := .seq acquireA (.seq (pallocOCS npv) relA)

/-- `x = AT[j]; if (x == o) { AT[j] = 0; r = 1; } else r = 0;` -/
def pfreeOCS : Stmt APrim :=
  .seq (.call "x" .pull [lkE, .var "j"])
    (.ite (.bin .eq (.var "x") (.var "o"))
      (.seq (.call "_" .push [lkE, .var "j", .const 0]) (.assign "r" (.const 1)))
      (.assign "r" (.const 0)))

/-- `pfree(o, j)`: the result is in `r`. -/
def pfreeO : Stmt APrim := .seq acquireA (.seq pfreeOCS relA)

/-- **The scan loop computes the allocator.** -/
theorem scanO_run (εR : REnv) {c : CPU} {i : Nat} (np : Nat) (hnp : np < 2 ^ 32) (ov : Val) :
    ∀ (n m : Nat), m + n = np → ∀ (σ : Locals) (l : RLog) (b : Region),
      σ "i" = BitVec.ofNat 32 m → σ "r" = BitVec.ofNat 32 np → (σ "lk").toNat = i → σ "o" = ov →
      CS1 c i l b →
      ∃ σ' l', Runs (rprimsA εR c) (scanLoopO (BitVec.ofNat 32 np)) σ l σ' l' ∧
        CS1 c i l' (allocFromO np ov b m n).1 ∧ σ' "r" = BitVec.ofNat 32 (allocFromO np ov b m n).2
  | 0, m, hm, σ, l, b, hi, hr, _, _, hcs => by
    have hmn : m = np := by omega
    subst hmn
    exact ⟨σ, l, Runs.while_false (ne_false hi), by simpa [allocFromO, findFree] using hcs,
      by simp [allocFromO, findFree, hr]⟩
  | n + 1, m, hm, σ, l, b, hi, hr, hlk, ho, hcs => by
    have hmlt : m < 2 ^ 32 := by omega
    have hne : (BitVec.ofNat 32 m : Val) ≠ BitVec.ofNat 32 np := ofNat_ne hmlt hnp (by omega)
    have hmm : (BitVec.ofNat 32 m : Val).toNat = m := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hmlt
    let σ1 := σ.set "x" (b m)
    have hrd : Runs (rprimsA εR c) (.call "x" .pull [lkE, .var "i"]) σ l σ1 l := by
      have h := cs1_rd (εR := εR) hcs hlk "x" (.var "i")
      have e : ((Expr.var "i").eval σ).toNat = m := by show (σ "i").toNat = m; rw [hi]; exact hmm
      rw [e] at h; exact h
    have hlk1 : (σ1 "lk").toNat = i := by simpa [σ1, Locals.set] using hlk
    have hg : ¬ (Expr.bin .ne (.var "i") (.const (BitVec.ofNat 32 np))).eval σ = 0 :=
      ne_true (by rw [hi]; exact hne)
    by_cases hz : b m = 0#32
    · have hx : σ1 "x" = 0 := by simp [σ1, hz]
      obtain ⟨l2, hw, hc2⟩ := cs1_wr (εR := εR) hcs hlk1 (.var "i") (.var "o")
      have e1 : ((Expr.var "i").eval σ1).toNat = m := by
        show (σ1 "i").toNat = m; simp [σ1, hi, hmm]
      have e2 : (Expr.var "o").eval σ1 = ov := by show σ1 "o" = ov; simp [σ1, ho]
      rw [e1, e2] at hc2
      let σ2 := σ1.set "_" 0
      let σ3 := σ2.set "r" (BitVec.ofNat 32 m)
      let σ4 := σ3.set "i" (BitVec.ofNat 32 np)
      have ha3 : Runs (rprimsA εR c) (.assign "r" (.var "i")) σ2 l2 σ3 l2 := by
        have h := Runs.assign (P := rprimsA εR c) (σ := σ2) (l := l2) "r" (.var "i")
        have e : (Expr.var "i").eval σ2 = BitVec.ofNat 32 m := by
          show σ2 "i" = _; simp [σ2, σ1, Locals.set, hi]
        rw [e] at h; exact h
      have ha4 : Runs (rprimsA εR c) (.assign "i" (.const (BitVec.ofNat 32 np))) σ3 l2 σ4 l2 :=
        Runs.assign _ _
      refine ⟨σ4, l2, Runs.while_true hg
        (Runs.seq hrd (Runs.ite_true (eq_true hx) (Runs.seq hw (Runs.seq ha3 ha4))))
        (Runs.while_false (ne_false (by simp [σ4]))), ?_, ?_⟩
      · simpa [allocFromO, findFree, hz] using hc2
      · simp [σ4, σ3, Locals.set, allocFromO, findFree, hz]
    · let σ2 := σ1.set "i" (BitVec.ofNat 32 (m + 1))
      have hx : σ1 "x" ≠ 0 := by simp [σ1, hz]
      have ha : Runs (rprimsA εR c) (.assign "i" (.bin .add (.var "i") (.const 1))) σ1 l σ2 l := by
        have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l) "i" (.bin .add (.var "i") (.const 1))
        have e : (Expr.bin .add (.var "i") (.const 1)).eval σ1 = BitVec.ofNat 32 (m + 1) := by
          simp [Expr.eval, BinOp.eval, σ1, hi, BitVec.ofNat_add]
        rw [e] at h; exact h
      obtain ⟨σ', l', hrun, hc', hres⟩ := scanO_run εR np hnp ov n (m + 1) (by omega) σ2 l b
        (by simp [σ2]) (by simp [σ2, σ1, Locals.set, hr]) (by simpa [σ2, σ1, Locals.set] using hlk)
        (by simp [σ2, σ1, Locals.set, ho]) hcs
      refine ⟨σ', l', Runs.while_true hg (Runs.seq hrd (Runs.ite_false (eq_false hx) ha)) hrun, ?_, ?_⟩
      · simpa [allocFromO, findFree, hz] using hc'
      · rw [hres]; simp [allocFromO, findFree, hz]

/-- The critical section of `palloc(o)` computes `pallocOSpec`. -/
theorem pallocOCS_run (εR : REnv) {c : CPU} {i : Nat} (np : Nat) (hnp : np < 2 ^ 32) (σ : Locals) (l : RLog)
    (b : Region) (hlk : (σ "lk").toNat = i) (hcs : CS1 c i l b) :
    ∃ σ' l', Runs (rprimsA εR c) (pallocOCS (BitVec.ofNat 32 np)) σ l σ' l' ∧
      CS1 c i l' (pallocOSpec np (σ "o") b).1 ∧ σ' "r" = BitVec.ofNat 32 (pallocOSpec np (σ "o") b).2 := by
  let σ1 := σ.set "i" 0
  let σ2 := σ1.set "r" (BitVec.ofNat 32 np)
  obtain ⟨σ', l', hrun, hc', hres⟩ := scanO_run εR np hnp (σ "o") np 0 (by omega) σ2 l b
    (by simp [σ2, σ1, Locals.set]) (by simp [σ2]) (by simpa [σ2, σ1, Locals.set] using hlk)
    (by simp [σ2, σ1, Locals.set]) hcs
  have h1 : Runs (rprimsA εR c) (.assign "i" (.const 0)) σ l σ1 l := Runs.assign _ _
  have h2 : Runs (rprimsA εR c) (.assign "r" (.const (BitVec.ofNat 32 np))) σ1 l σ2 l := Runs.assign _ _
  exact ⟨σ', l', Runs.seq h1 (Runs.seq h2 hrun), hc', hres⟩

theorem pallocOCS_fr (npv : Val) (z : Ident) (h3 : z ≠ "_") (h5 : z ≠ "i") (h6 : z ≠ "r") (h7 : z ≠ "x") :
    frS z (pallocOCS npv) = true := by
  simp [frS, pallocOCS, scanLoopO, scanBodyO, Ne.symm h3, Ne.symm h5, Ne.symm h6, Ne.symm h7]

/-- **`palloc(o)` refines the abstract allocator.** The page it returns and the
table it releases are `pallocOSpec` of the table the previous holder released,
with the caller's tag. -/
theorem pallocO_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (np : Nat) (hnp : np < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨pallocO (BitVec.ofNat 32 np), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = (pallocOSpec np (σ "o") (hmemR iv.toNat H1)).1 ∧
      σ' "r" = BitVec.ofNat 32 (pallocOSpec np (σ "o") (hmemR iv.toNat H1)).2 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hfr, hR1, hR2⟩ :=
    cs_guarantee1 hE hRR hc hRA hl hidle bound K hK hF σ hσ (pallocOCS (BitVec.ofNat 32 np))
      (fun b σ b' σ' => b' = (pallocOSpec np (σ "o") b).1 ∧
        σ' "r" = BitVec.ofNat 32 (pallocOSpec np (σ "o") b).2)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', hr, hc', hres⟩ := pallocOCS_run εR np hnp σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', (hr.frame (pallocOCS_fr _ "lk" (by decide) (by decide) (by decide)
          (by decide))).trans hlk, rfl, hres⟩)
  have ho := hfr "o" (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, ?_, ?_⟩
  · rw [hR1, ho]
  · rw [Locals.set_other _ _ (by decide), hR2, ho]

/-- The critical section of `pfree(o, j)` computes `pfreeOSpec`. -/
theorem pfreeOCS_run (εR : REnv) {c : CPU} {i : Nat} (σ : Locals) (l : RLog) (b : Region)
    (hlk : (σ "lk").toNat = i) (hcs : CS1 c i l b) :
    ∃ σ' l', Runs (rprimsA εR c) pfreeOCS σ l σ' l' ∧
      CS1 c i l' (pfreeOSpec b (σ "o") (σ "j").toNat).1 ∧
      σ' "r" = (pfreeOSpec b (σ "o") (σ "j").toNat).2 := by
  let σ1 := σ.set "x" (b (σ "j").toNat)
  have hrd : Runs (rprimsA εR c) (.call "x" .pull [lkE, .var "j"]) σ l σ1 l := cs1_rd hcs hlk "x" (.var "j")
  by_cases hz : b (σ "j").toNat = σ "o"
  · obtain ⟨l2, hw, hc2⟩ := cs1_wr (εR := εR) hcs (σ := σ1) (by simpa [σ1, Locals.set] using hlk)
      (.var "j") (.const 0)
    have e1 : ((Expr.var "j").eval σ1).toNat = (σ "j").toNat := by
      show (σ1 "j").toNat = _; simp [σ1]
    have e2 : (Expr.const 0).eval σ1 = 0 := rfl
    rw [e1, e2] at hc2
    have hg : ¬ (Expr.bin .eq (.var "x") (.var "o")).eval σ1 = 0 := by
      simp [Expr.eval, BinOp.eval, σ1, hz]
    have ha : Runs (rprimsA εR c) (.assign "r" (.const 1)) (σ1.set "_" 0) l2 ((σ1.set "_" 0).set "r" 1) l2 :=
      Runs.assign _ _
    refine ⟨(σ1.set "_" 0).set "r" 1, l2, Runs.seq hrd (Runs.ite_true hg (Runs.seq hw ha)), ?_, ?_⟩
    · simpa [pfreeOSpec, hz] using hc2
    · simp [pfreeOSpec, hz]
  · have hg : (Expr.bin .eq (.var "x") (.var "o")).eval σ1 = 0 := by
      simp [Expr.eval, BinOp.eval, σ1, hz]
    have ha : Runs (rprimsA εR c) (.assign "r" (.const 0)) σ1 l (σ1.set "r" 0) l := Runs.assign _ _
    refine ⟨σ1.set "r" 0, l, Runs.seq hrd (Runs.ite_false hg ha), ?_, ?_⟩
    · simpa [pfreeOSpec, hz] using hcs
    · simp [pfreeOSpec, hz]

theorem pfreeOCS_fr (z : Ident) (h3 : z ≠ "_") (h6 : z ≠ "r") (h7 : z ≠ "x") : frS z pfreeOCS = true := by
  simp [frS, pfreeOCS, Ne.symm h3, Ne.symm h6, Ne.symm h7]

/-- **`pfree(o, j)` refines `pfreeOSpec`**: the page is freed only if the
caller's tag is on it, and `r` says whether it was. -/
theorem pfreeO_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨pfreeO, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = (pfreeOSpec (hmemR iv.toNat H1) (σ "o") (σ "j").toNat).1 ∧
      σ' "r" = (pfreeOSpec (hmemR iv.toNat H1) (σ "o") (σ "j").toNat).2 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hfr, hR1, hR2⟩ :=
    cs_guarantee1 hE hRR hc hRA hl hidle bound K hK hF σ hσ pfreeOCS
      (fun b σ b' σ' => b' = (pfreeOSpec b (σ "o") (σ "j").toNat).1 ∧
        σ' "r" = (pfreeOSpec b (σ "o") (σ "j").toNat).2)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', hr, hc', hres⟩ := pfreeOCS_run εR σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', (hr.frame (pfreeOCS_fr "lk" (by decide) (by decide) (by decide))).trans hlk,
          rfl, hres⟩)
  have ho := hfr "o" (by decide) (by decide) (by decide) (by decide)
  have hj := hfr "j" (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, ?_, ?_⟩
  · rw [hR1, ho, hj]
  · rw [Locals.set_other _ _ (by decide), hR2, ho, hj]

/-! ## Containers that own their pages -/

open KernContainer (nest nest_run cell cellE rd_cell wr_cell ltu_true ltu_false ctAllocSpec)

/-- The tag of container `id`. Tags 0 and 1 are taken (free, kernel). -/
def tag (id : Val) : Val := id + 2

theorem pallocO_lk (npv : Val) : LkS (pallocO npv) := by
  simp [LkS, pallocO, acquireA, loopA, pallocOCS, scanLoopO, scanBodyO, relA]

theorem pallocO_fr (npv : Val) (z : Ident) (h1 : z ≠ "t") (h2 : z ≠ "n") (h3 : z ≠ "_") (h4 : z ≠ "v")
    (h5 : z ≠ "i") (h6 : z ≠ "r") (h7 : z ≠ "x") : frS z (pallocO npv) = true := by
  simp [frS, pallocO, acquireA, loopA, pallocOCS, scanLoopO, scanBodyO, relA, Ne.symm h1, Ne.symm h2,
    Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7]

theorem pfreeO_lk : LkS pfreeO := by simp [LkS, pfreeO, pfreeOCS, acquireA, loopA, relA]

theorem pfreeO_fr (z : Ident) (h1 : z ≠ "t") (h2 : z ≠ "n") (h3 : z ≠ "_") (h4 : z ≠ "v")
    (h6 : z ≠ "r") (h7 : z ≠ "x") : frS z pfreeO = true := by
  simp [frS, pfreeO, pfreeOCS, acquireA, loopA, relA, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4,
    Ne.symm h6, Ne.symm h7]

/-- `u = usage; q = quota; if (u < q) { o = id + 2; r = palloc(o); if (r != np) usage = u + 1; } else r = np;` -/
def ctAllocOCS (atv npv : Val) : Stmt APrim :=
  .seq (.call "u" .pull [lkE, cellE "id" 1]) (.seq (.call "q" .pull [lkE, cellE "id" 0])
    (.ite (.bin .ltu (.var "u") (.var "q"))
      (.seq (.assign "o" (.bin .add (.var "id") (.const 2)))
        (.seq (nest atv (pallocO npv)) (.ite (.bin .ne (.var "r") (.const npv))
          (.call "_" .push [lkE, cellE "id" 1, .bin .add (.var "u") (.const 1)]) .skip)))
      (.assign "r" (.const npv))))

/-- `container_alloc(id)`: the page is tagged with the container. -/
def ctAllocO (atv npv : Val) : Stmt APrim := .seq acquireA (.seq (ctAllocOCS atv npv) relA)

/-- **The abstract `container_free` with the ownership check.** `ok` is what
`pfree` returned: the usage goes down only if the page was the container's. -/
def ctFreeOSpec (b : Region) (id ok : Val) : Region :=
  if ok = 0 then b else setCell b (cell id 1) (b (cell id 1) - 1)

/-- `o = id + 2; r = pfree(o, j); if (r != 0) { u = usage; usage = u - 1; }` -/
def ctFreeOCS (atv : Val) : Stmt APrim :=
  .seq (.assign "o" (.bin .add (.var "id") (.const 2)))
    (.seq (nest atv pfreeO)
      (.ite (.bin .ne (.var "r") (.const 0))
        (.seq (.call "u" .pull [lkE, cellE "id" 1])
          (.call "_" .push [lkE, cellE "id" 1, .bin .sub (.var "u") (.const 1)]))
        .skip))

/-- `container_free(id, j)`: frees page `j` only if the container owns it. -/
def ctFreeO (atv : Val) : Stmt APrim := .seq acquireA (.seq (ctFreeOCS atv) relA)

/-- **The critical section of `container_alloc` computes `ctAllocSpec`**, with
the page `palloc` tagged for this container. -/
theorem ctAllocOCS_run {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    {atv : Val} (hF : ∀ tn, LockArray.FairA ε c atv.toNat tn bound) (np : Nat) (hnp : np < 2 ^ 32)
    {i : Nat} (hi : i ≠ atv.toNat) (σ : Locals) (l : RLog) (b : Region) (hlk : (σ "lk").toNat = i)
    (hcs : CSt c i atv.toNat l b) :
    ∃ σ' l' a, Runs (rprimsA εR c) (ctAllocOCS atv (BitVec.ofNat 32 np)) σ l σ' l' ∧
      CSt c i atv.toNat l' (ctAllocSpec np b (pallocOSpec np (tag (σ "id")) a).2 (σ "id")).1 ∧
      σ' "lk" = σ "lk" ∧
      σ' "r" = BitVec.ofNat 32 (ctAllocSpec np b (pallocOSpec np (tag (σ "id")) a).2 (σ "id")).2 := by
  let U := b (cell (σ "id") 1)
  let Q := b (cell (σ "id") 0)
  let σ0 := σ.set "u" U
  let σ1 := σ0.set "q" Q
  let σo := σ1.set "o" (tag (σ "id"))
  have hr0 : Runs (rprimsA εR c) (.call "u" .pull [lkE, cellE "id" 1]) σ l σ0 l := rd_cell hcs hlk "u" "id" 1 rfl
  have hr1 : Runs (rprimsA εR c) (.call "q" .pull [lkE, cellE "id" 0]) σ0 l σ1 l :=
    rd_cell hcs (σ := σ0) (by simp [σ0, Locals.set, hlk]) "q" "id" 0 (by simp [σ0, Locals.set])
  have hao : Runs (rprimsA εR c) (.assign "o" (.bin .add (.var "id") (.const 2))) σ1 l σo l := by
    have h := Runs.assign (P := rprimsA εR c) (σ := σ1) (l := l) "o" (.bin .add (.var "id") (.const 2))
    have e : (Expr.bin .add (.var "id") (.const 2)).eval σ1 = tag (σ "id") := by
      simp [Expr.eval, BinOp.eval, σ1, σ0, Locals.set, tag]
    rw [e] at h; exact h
  have hlk1 : σ1 "lk" = σ "lk" := by simp [σ1, σ0, Locals.set]
  have hu1 : σ1 "u" = U := by simp [σ1, σ0, Locals.set]
  have hq1 : σ1 "q" = Q := by simp [σ1, σ0, Locals.set]
  have hlko : σo "lk" = σ "lk" := by simp [σo, σ1, σ0, Locals.set]
  have huo : σo "u" = U := by simp [σo, σ1, σ0, Locals.set]
  have hido : σo "id" = σ "id" := by simp [σo, σ1, σ0, Locals.set]
  by_cases hlt : U.ult Q = true
  · obtain ⟨S, H, hl, hh, hid, hb⟩ := hcs
    obtain ⟨σp, rb, S3, H1, H3, hrun, hl3, hid3, -, hr⟩ :=
      pallocO_guarantee hE hRR hc hRA hl (iv := atv) hid bound K hK (hF _)
        ((σo.set "plk" (σo "lk")).set "lk" atv) (by simp) np hnp
    have hot : ((σo.set "plk" (σo "lk")).set "lk" atv) "o" = tag (σ "id") := by simp [σo, Locals.set]
    rw [hot] at hr
    obtain ⟨hnest, hc2⟩ := nest_run (pallocO_lk _)
      (pallocO_fr _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (pallocO_fr _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      hi hl hh hb hrun hl3 hid3
    have hfr : ∀ z : Ident, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → z ≠ "i" → z ≠ "r" → z ≠ "x" →
        σp z = ((σo.set "plk" (σo "lk")).set "lk" atv) z := fun z h1 h2 h3 h4 h5 h6 h7 =>
      (Runs.of_stop hrun).frame (pallocO_fr _ z h1 h2 h3 h4 h5 h6 h7)
    let σ2 := σp.set "lk" (σo "lk")
    have hr2 : σ2 "r" = BitVec.ofNat 32 (pallocOSpec np (tag (σ "id")) (hmemR atv.toNat H1)).2 := by
      simp [σ2, Locals.set, hr]
    have hlk2 : σ2 "lk" = σ "lk" := by simp [σ2, hlko]
    have hid2 : σ2 "id" = σ "id" := by
      simp only [σ2, Locals.set_other _ _ (show ("id" : Ident) ≠ "lk" by decide)]
      rw [hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [Locals.set, hido]
    have hu2 : σ2 "u" = U := by
      simp only [σ2, Locals.set_other _ _ (show ("u" : Ident) ≠ "lk" by decide)]
      rw [hfr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [Locals.set, huo]
    have hguard : ¬ (Expr.bin .ltu (.var "u") (.var "q")).eval σ1 = 0 :=
      ltu_true (by simp only [Expr.eval]; rw [hu1, hq1]; exact hlt)
    by_cases hp : (pallocOSpec np (tag (σ "id")) (hmemR atv.toNat H1)).2 = np
    · have hspec : ctAllocSpec np b (pallocOSpec np (tag (σ "id")) (hmemR atv.toNat H1)).2 (σ "id") =
          (b, np) := by rw [ctAllocSpec, if_pos hlt, if_pos hp]
      refine ⟨σ2, rb, hmemR atv.toNat H1, Runs.seq hr0 (Runs.seq hr1 (Runs.ite_true hguard
        (Runs.seq hao (Runs.seq hnest (Runs.ite_false (ne_false (hr2.trans (by rw [hp]))) Runs.skip))))),
        ?_, hlk2, ?_⟩
      · rw [hspec]; exact hc2
      · rw [hspec, hr2, hp]
    · have hple := pallocO_le np (tag (σ "id")) (hmemR atv.toNat H1)
      obtain ⟨l3, hw, hc3⟩ := wr_cell (εR := εR) hc2 (σ := σ2) (by rw [hlk2]; exact hlk) "id" 1
        (.bin .add (.var "u") (.const 1)) hid2
      have hev : (Expr.bin .add (.var "u") (.const 1)).eval σ2 = U + 1 := by
        simp only [Expr.eval, BinOp.eval]; rw [hu2]
      rw [hev] at hc3
      have hspec : ctAllocSpec np b (pallocOSpec np (tag (σ "id")) (hmemR atv.toNat H1)).2 (σ "id") =
          (setCell b (cell (σ "id") 1) (U + 1), (pallocOSpec np (tag (σ "id")) (hmemR atv.toNat H1)).2) := by
        rw [ctAllocSpec, if_pos hlt, if_neg hp]
      refine ⟨σ2.set "_" 0, l3, hmemR atv.toNat H1, Runs.seq hr0 (Runs.seq hr1 (Runs.ite_true hguard
        (Runs.seq hao (Runs.seq hnest (Runs.ite_true (ne_true (fun h => ofNat_ne (by omega) hnp hp
          (hr2.symm.trans h))) hw))))), ?_, ?_, ?_⟩
      · rw [hspec]; exact hc3
      · rw [Locals.set_other _ _ (by decide)]; exact hlk2
      · rw [hspec, Locals.set_other _ _ (by decide)]; exact hr2
  · have hguard : (Expr.bin .ltu (.var "u") (.var "q")).eval σ1 = 0 :=
      ltu_false (by simp only [Expr.eval]; rw [hu1, hq1]; exact hlt)
    have hspec : ctAllocSpec np b (pallocOSpec np (tag (σ "id")) (fun _ => 0)).2 (σ "id") = (b, np) := by
      rw [ctAllocSpec, if_neg hlt]
    refine ⟨σ1.set "r" (BitVec.ofNat 32 np), l, fun _ => 0, Runs.seq hr0 (Runs.seq hr1
      (Runs.ite_false hguard (Runs.assign _ _))), ?_, ?_, ?_⟩
    · rw [hspec]; exact hcs
    · rw [Locals.set_other _ _ (by decide)]; exact hlk1
    · rw [hspec]; simp

/-- **The critical section of `container_free` computes `ctFreeOSpec`**, with
what `pfree` returned on the allocation table `a` it found. -/
theorem ctFreeOCS_run {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    {atv : Val} (hF : ∀ tn, LockArray.FairA ε c atv.toNat tn bound)
    {i : Nat} (hi : i ≠ atv.toNat) (σ : Locals) (l : RLog) (b : Region) (hlk : (σ "lk").toNat = i)
    (hcs : CSt c i atv.toNat l b) :
    ∃ σ' l' a, Runs (rprimsA εR c) (ctFreeOCS atv) σ l σ' l' ∧
      CSt c i atv.toNat l' (ctFreeOSpec b (σ "id") (pfreeOSpec a (tag (σ "id")) (σ "j").toNat).2) ∧
      σ' "lk" = σ "lk" := by
  let σo := σ.set "o" (tag (σ "id"))
  have hao : Runs (rprimsA εR c) (.assign "o" (.bin .add (.var "id") (.const 2))) σ l σo l := by
    have h := Runs.assign (P := rprimsA εR c) (σ := σ) (l := l) "o" (.bin .add (.var "id") (.const 2))
    have e : (Expr.bin .add (.var "id") (.const 2)).eval σ = tag (σ "id") := by
      simp [Expr.eval, BinOp.eval, tag]
    rw [e] at h; exact h
  have hlko : σo "lk" = σ "lk" := by simp [σo, Locals.set]
  obtain ⟨S, H, hl, hh, hid, hb⟩ := hcs
  obtain ⟨σp, rb, S3, H1, H3, hrun, hl3, hid3, -, hr⟩ :=
    pfreeO_guarantee hE hRR hc hRA hl (iv := atv) hid bound K hK (hF _)
      ((σo.set "plk" (σo "lk")).set "lk" atv) (by simp)
  have hot : ((σo.set "plk" (σo "lk")).set "lk" atv) "o" = tag (σ "id") := by simp [σo, Locals.set]
  have hjt : ((σo.set "plk" (σo "lk")).set "lk" atv) "j" = σ "j" := by simp [σo, Locals.set]
  rw [hot, hjt] at hr
  obtain ⟨hnest, hc2⟩ := nest_run pfreeO_lk
    (pfreeO_fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (pfreeO_fr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hi hl hh hb hrun hl3 hid3
  let σ2 := σp.set "lk" (σo "lk")
  have hr2 : σ2 "r" = (pfreeOSpec (hmemR atv.toNat H1) (tag (σ "id")) (σ "j").toNat).2 := by
    simp [σ2, Locals.set, hr]
  have hlk2 : σ2 "lk" = σ "lk" := by simp [σ2, hlko]
  have hid2 : σ2 "id" = σ "id" := by
    simp only [σ2, Locals.set_other _ _ (show ("id" : Ident) ≠ "lk" by decide)]
    rw [(Runs.of_stop hrun).frame (pfreeO_fr "id" (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))]
    simp [σo, Locals.set]
  by_cases hok : (pfreeOSpec (hmemR atv.toNat H1) (tag (σ "id")) (σ "j").toNat).2 = 0
  · refine ⟨σ2, rb, hmemR atv.toNat H1, Runs.seq hao (Runs.seq hnest
      (Runs.ite_false (ne_false (hr2.trans hok)) Runs.skip)), ?_, hlk2⟩
    have : ctFreeOSpec b (σ "id") (pfreeOSpec (hmemR atv.toNat H1) (tag (σ "id")) (σ "j").toNat).2 = b :=
      if_pos hok
    rw [this]; exact hc2
  · let U := b (cell (σ "id") 1)
    let σ3 := σ2.set "u" U
    have hrd : Runs (rprimsA εR c) (.call "u" .pull [lkE, cellE "id" 1]) σ2 rb σ3 rb :=
      rd_cell hc2 (σ := σ2) (by rw [hlk2]; exact hlk) "u" "id" 1 hid2
    have hlk3 : σ3 "lk" = σ "lk" := by simp [σ3, Locals.set, hlk2]
    obtain ⟨l3, hw, hc3⟩ := wr_cell (εR := εR) hc2 (σ := σ3) (by rw [hlk3]; exact hlk) "id" 1
      (.bin .sub (.var "u") (.const 1)) (id := σ "id") (by simp [σ3, Locals.set, hid2])
    have hev : (Expr.bin .sub (.var "u") (.const 1)).eval σ3 = U - 1 := by
      simp [Expr.eval, BinOp.eval, σ3]
    rw [hev] at hc3
    refine ⟨σ3.set "_" 0, l3, hmemR atv.toNat H1, Runs.seq hao (Runs.seq hnest
      (Runs.ite_true (ne_true (fun h => hok (hr2.symm.trans h))) (Runs.seq hrd hw))), ?_, ?_⟩
    · have : ctFreeOSpec b (σ "id") (pfreeOSpec (hmemR atv.toNat H1) (tag (σ "id")) (σ "j").toNat).2 =
          setCell b (cell (σ "id") 1) (U - 1) := if_neg hok
      rw [this]; exact hc3
    · rw [Locals.set_other _ _ (by decide)]; exact hlk3

/-- **`container_alloc` refines `ctAllocSpec`, and the page is the
container's.** `a` is the allocation table `palloc` found. -/
theorem ctAllocO_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {atv : Val} (hi : iv.toNat ≠ atv.toNat) (hidat : (S.lk atv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (hFat : ∀ tn, LockArray.FairA ε c atv.toNat tn bound)
    (σ : Locals) (hσ : σ "lk" = iv) (np : Nat) (hnp : np < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR) (a : Region),
      Star (rprimsA εR c) ⟨ctAllocO atv (BitVec.ofNat 32 np), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧ (S3.lk atv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 =
        (ctAllocSpec np (hmemR iv.toNat H1) (pallocOSpec np (tag (σ "id")) a).2 (σ "id")).1 ∧
      σ' "r" = BitVec.ofNat 32
        (ctAllocSpec np (hmemR iv.toNat H1) (pallocOSpec np (tag (σ "id")) a).2 (σ "id")).2 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hidj, hfr, a, hR1, hR2⟩ :=
    cs_guarantee2 hE hRR hc hRA hl hidle (j := atv.toNat) (fun h => hi h.symm) hidat bound K hK hF σ hσ
      (ctAllocOCS atv (BitVec.ofNat 32 np))
      (fun b σ b' σ' => ∃ a, b' = (ctAllocSpec np b (pallocOSpec np (tag (σ "id")) a).2 (σ "id")).1 ∧
        σ' "r" = BitVec.ofNat 32 (ctAllocSpec np b (pallocOSpec np (tag (σ "id")) a).2 (σ "id")).2)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', a, hr, hc', hlk', hres⟩ := ctAllocOCS_run hE hRR hc hRA bound K hK hFat np hnp
          hi σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', hlk'.trans hlk, a, rfl, hres⟩)
  have hd := hfr "id" (by decide) (by decide) (by decide) (by decide)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, a, hrun, hl3, hid, hidj, ?_, ?_⟩
  · rw [hR1, hd]
  · rw [Locals.set_other _ _ (by decide), hR2, hd]

/-- **`container_free` refines `ctFreeOSpec`.** The usage goes down only if
`pfree` found the container's tag on page `j` in the allocation table `a`. -/
theorem ctFreeO_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {atv : Val} (hi : iv.toNat ≠ atv.toNat) (hidat : (S.lk atv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (hFat : ∀ tn, LockArray.FairA ε c atv.toNat tn bound)
    (σ : Locals) (hσ : σ "lk" = iv) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR) (a : Region),
      Star (rprimsA εR c) ⟨ctFreeO atv, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧ (S3.lk atv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = ctFreeOSpec (hmemR iv.toNat H1) (σ "id")
        (pfreeOSpec a (tag (σ "id")) (σ "j").toNat).2 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hidj, hfr, a, hR⟩ :=
    cs_guarantee2 hE hRR hc hRA hl hidle (j := atv.toNat) (fun h => hi h.symm) hidat bound K hK hF σ hσ
      (ctFreeOCS atv)
      (fun b σ b' _ => ∃ a, b' = ctFreeOSpec b (σ "id") (pfreeOSpec a (tag (σ "id")) (σ "j").toNat).2)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', a, hr, hc', hlk'⟩ := ctFreeOCS_run hE hRR hc hRA bound K hK hFat hi σ l b
          (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', hlk'.trans hlk, a, rfl⟩)
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, a, hrun, hl3, hid, hidj, ?_⟩
  rw [hR, hfr "id" (by decide) (by decide) (by decide) (by decide),
    hfr "j" (by decide) (by decide) (by decide) (by decide)]

end KernOwner
