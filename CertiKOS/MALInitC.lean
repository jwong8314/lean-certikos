import CertiKOS.MALInit
import CertiKOS.Layer

/-!
# mCertiKOS `mem_init`: the C code, ported and verified

`MALInit.lean` holds what `mem_init` computes. This file holds its C code
(`mm/MALInitCSource.v`), the primitives it calls, and the proof that the code
refines `mem_init_spec`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MALInit

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding)
open LockRegionCPU KernFrame MALOp Layer

/-! ## Proof rules used below -/

/-- **A loop with an invariant and a measure.** -/
theorem while_inv {εR : REnv} {c : CPU} {e : Expr} {body : Stmt APrim} (I : Locals → RLog → Prop)
    (μ : Locals → Nat)
    (hb : ∀ σ l, I σ l → ¬ e.eval σ = 0 →
      ∃ σ' l', Runs (rprimsA εR c) body σ l σ' l' ∧ I σ' l' ∧ μ σ' < μ σ) :
    ∀ (n : Nat) (σ : Locals) (l : RLog), μ σ ≤ n → I σ l →
      ∃ σ' l', Runs (rprimsA εR c) (.while e body) σ l σ' l' ∧ I σ' l' ∧ e.eval σ' = 0 := by
  intro n
  induction n with
  | zero =>
    intro σ l hn hI
    by_cases hg : e.eval σ = 0
    · exact ⟨σ, l, Runs.while_false hg, hI, hg⟩
    · obtain ⟨σ1, l1, -, -, hlt⟩ := hb σ l hI hg
      omega
  | succ n ih =>
    intro σ l hn hI
    by_cases hg : e.eval σ = 0
    · exact ⟨σ, l, Runs.while_false hg, hI, hg⟩
    · obtain ⟨σ1, l1, hr, hI1, hlt⟩ := hb σ l hI hg
      obtain ⟨σ2, l2, hr2, hI2, h0⟩ := ih σ1 l1 (by omega) hI1
      exact ⟨σ2, l2, Runs.while_true hg hr hr2, hI2, h0⟩

theorem rd_run {εR : REnv} {c : CPU} {i : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (x : Ident) (je : Expr) {n : Nat} (he : (je.eval σ).toNat = n) :
    Runs (rprimsA εR c) (.call x .pull [lkE, je]) σ l (σ.set x (b n)) l := by
  have := cs1_rd (εR := εR) h hlk x je
  rw [he] at this; exact this

theorem wr_run {εR : REnv} {c : CPU} {i : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (je ve : Expr) {n : Nat} {v : Val} (he : (je.eval σ).toNat = n)
    (hv : ve.eval σ = v) :
    ∃ l', Runs (rprimsA εR c) (.call "_" .push [lkE, je, ve]) σ l (σ.set "_" 0) l' ∧
      CS1 c i l' (setCell b n v) := by
  have := cs1_wr (εR := εR) h hlk je ve
  rw [he, hv] at this; exact this

theorem asg_run {εR : REnv} {c : CPU} {σ : Locals} {l : RLog} (x : Ident) (e : Expr) {v : Val}
    (h : e.eval σ = v) : Runs (rprimsA εR c) (.assign x e) σ l (σ.set x v) l := by
  have := Runs.assign (P := rprimsA εR c) (σ := σ) (l := l) x e
  rw [h] at this; exact this

theorem tn {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n : Val).toNat = n := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ltu_eval {σ : Locals} {ea eb : Expr} {a b : Nat} (hx : ea.eval σ = BitVec.ofNat 32 a)
    (hy : eb.eval σ = BitVec.ofNat 32 b) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (Expr.bin .ltu ea eb).eval σ = if a < b then 1 else 0 := by
  show (if (ea.eval σ).ult (eb.eval σ) then (1 : Val) else 0) = _
  rw [hx, hy, ult_ofNat ha hb]; simp

theorem inc_eval {σ : Locals} {x : Ident} {m : Nat} (h : σ x = BitVec.ofNat 32 m) :
    (Expr.bin .add (.var x) (.const 1)).eval σ = BitVec.ofNat 32 (m + 1) := by
  simp [Expr.eval, BinOp.eval, h, BitVec.ofNat_add]

/-! ## The memory map in the region (`PreInit`) -/

/-- The boot loader leaves the memory map at `mmb`: the number of regions,
then start, length and "usable" of each. -/
structure MatchMMap (mmb : Nat) (mm : MMTable) (size : Nat) (b : Region) : Prop where
  msize : b mmb = BitVec.ofNat 32 size
  mat : ∀ j, j < size → ∃ s l p, mm j = .MMValid s l p ∧ b (mmb + 1 + 3 * j) = BitVec.ofNat 32 s ∧
    b (mmb + 1 + 3 * j + 1) = BitVec.ofNat 32 l ∧
    b (mmb + 1 + 3 * j + 2) = (if p = .MMUsable then 1 else 0)

/-- `perm_consist`: regions that overlap have the same permission. -/
def perm_consist (s1 s2 l1 l2 : Nat) (p1 p2 : MMPerm) : Prop := s1 < s2 + l2 → s2 < s1 + l1 → p1 = p2

/-- `MM_correct`. -/
def MM_correct (mm : MMTable) (size : Nat) : Prop :=
  ∀ i j s1 s2 l1 l2 p1 p2, i < size → j < size → mm i = .MMValid s1 l1 p1 → mm j = .MMValid s2 l2 p2 →
    perm_consist s1 s2 l1 l2 p1 p2

/-- Cell `k` of region `j` of the memory map. -/
def mmE (mmb : Nat) (je : Expr) (k : Nat) : Expr :=
  .bin .add (.bin .mul je (.const 3)) (.const (BitVec.ofNat 32 (mmb + 1 + k)))

theorem mm_ix {mmb size : Nat} (hmb : mmb + 1 + 3 * size ≤ 2 ^ 32) {σ : Locals} {je : Expr} {j : Nat}
    (hj : j < size) (he : je.eval σ = BitVec.ofNat 32 j) {k : Nat} (hk : k < 3) :
    ((mmE mmb je k).eval σ).toNat = mmb + 1 + 3 * j + k := by
  show (je.eval σ * 3 + BitVec.ofNat 32 (mmb + 1 + k)).toNat = _
  rw [he]
  simp [BitVec.toNat_add, BitVec.toNat_mul]; omega

/-- `x = get_size()` -/
def getSizeS (mmb : Nat) (x : Ident) : Stmt APrim := .call x .pull [lkE, .const (BitVec.ofNat 32 mmb)]
/-- `x = get_mms(j)` -/
def getMmsS (mmb : Nat) (x : Ident) (je : Expr) : Stmt APrim := .call x .pull [lkE, mmE mmb je 0]
/-- `x = get_mml(j)` -/
def getMmlS (mmb : Nat) (x : Ident) (je : Expr) : Stmt APrim := .call x .pull [lkE, mmE mmb je 1]
/-- `x = is_usable(j)` -/
def isUsableS (mmb : Nat) (x : Ident) (je : Expr) : Stmt APrim := .call x .pull [lkE, mmE mmb je 2]

/-! ## `MBoot`: `set_nps`, `set_norm` (`mm/MBootCSource.v`) -/

/-- `set_nps(n)`: `NPS_LOC = n;` -/
def setNpsS (maxpage : Nat) (ve : Expr) : Stmt APrim :=
  .call "_" .push [lkE, .const (BitVec.ofNat 32 (3 * maxpage)), ve]

/-- `set_norm(i, v)`: `AT[i].isnorm = v; AT[i].allocated = 0; AT[i].c = 0;` -/
def setNormS (ie ve : Expr) : Stmt APrim :=
  .seq (.call "_" .push [lkE, ixE ie 0, ve])
    (.seq (.call "_" .push [lkE, ixE ie 1, .const 0]) (.call "_" .push [lkE, ixE ie 2, .const 0]))

/-! ## The first loop: the page count -/

/-- The page count after the first `k` regions. -/
def cnps (mm : MMTable) : Nat → Nat
  | 0 => 0
  | k + 1 => if cnps mm k < maxs_at_i k mm then maxs_at_i k mm else cnps mm k

theorem cnps_calc (mm : MMTable) : ∀ k, cnps mm (k + 1) = Calculate_nps k mm
  | 0 => by
    show (if cnps mm 0 < maxs_at_i 0 mm then maxs_at_i 0 mm else cnps mm 0) = maxs_at_i 0 mm
    have h0 : cnps mm 0 = 0 := rfl
    by_cases h : cnps mm 0 < maxs_at_i 0 mm
    · rw [if_pos h]
    · rw [if_neg h]; omega
  | k + 1 => by
    show (if cnps mm (k + 1) < maxs_at_i (k + 1) mm then maxs_at_i (k + 1) mm else cnps mm (k + 1)) = _
    rw [cnps_calc mm k]; rfl

theorem cnps_real {mm : MMTable} {size : Nat} (h : 0 < size) : cnps mm size = real_nps mm size := by
  obtain ⟨k, rfl⟩ : ∃ k, size = k + 1 := ⟨size - 1, by omega⟩
  rw [cnps_calc]; rfl

theorem cnps_le {mm : MMTable} {size : Nat} (hv : MM_valid mm size) : ∀ m, m ≤ size → cnps mm m ≤ 2 ^ 20
  | 0, _ => by simp [cnps]
  | m + 1, h => by
    have ih := cnps_le hv m (by omega)
    obtain ⟨s, l, p, hm, -, hb⟩ := hv m (by omega)
    have : maxs_at_i m mm ≤ 2 ^ 20 := by
      unfold maxs_at_i; rw [hm]; show (s + l) / 4096 + 1 ≤ 2 ^ 20; omega
    simp only [cnps]; split <;> omega

theorem maxs_val {s l : Nat} (h : s + l < 2 ^ 32 - 1) :
    (BitVec.ofNat 32 s + BitVec.ofNat 32 l) / (4096 : Val) + 1 = BitVec.ofNat 32 ((s + l) / 4096 + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_udiv]
  omega

/-- `s = get_mms(i); l = get_mml(i); maxs = (s + l) / PgSize + 1;
if (maxs > nps) nps = maxs; i++;` -/
def npsBody (mmb : Nat) : Stmt APrim :=
  .seq (getMmsS mmb "s" (.var "i"))
    (.seq (getMmlS mmb "l" (.var "i"))
      (.seq (.assign "maxs" (.bin .add (.bin .div (.bin .add (.var "s") (.var "l")) (.const 4096)) (.const 1)))
        (.seq (.ite (.bin .ltu (.var "nps") (.var "maxs")) (.assign "nps" (.var "maxs")) .skip)
          (.assign "i" (.bin .add (.var "i") (.const 1))))))

def npsLoop (mmb : Nat) : Stmt APrim := .while (.bin .ltu (.var "i") (.var "size")) (npsBody mmb)

/-- **The first loop computes the page count.** It only reads. -/
theorem npsLoop_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b : Region} (hcs : CS1 c i l b)
    {mmb size : Nat} {mm : MMTable} (hmb : mmb + 1 + 3 * size ≤ 2 ^ 32) (hM : MatchMMap mmb mm size b)
    (hv : MM_valid mm size) (σ : Locals) (hlk : (σ "lk").toNat = i) (hi : σ "i" = 0)
    (hsz : σ "size" = BitVec.ofNat 32 size) (hn : σ "nps" = 0) :
    ∃ σ', Runs (rprimsA εR c) (npsLoop mmb) σ l σ' l ∧ σ' "nps" = BitVec.ofNat 32 (cnps mm size) ∧
      σ' "size" = BitVec.ofNat 32 size ∧ σ' "lk" = σ "lk" := by
  have hsize : size < 2 ^ 32 := by omega
  let I : Locals → RLog → Prop := fun τ l' => l' = l ∧ τ "lk" = σ "lk" ∧ τ "size" = BitVec.ofNat 32 size ∧
    ∃ m, m ≤ size ∧ τ "i" = BitVec.ofNat 32 m ∧ τ "nps" = BitVec.ofNat 32 (cnps mm m)
  have hbody : ∀ τ l', I τ l' → ¬ (Expr.bin .ltu (.var "i") (.var "size")).eval τ = 0 →
      ∃ τ' l'', Runs (rprimsA εR c) (npsBody mmb) τ l' τ' l'' ∧ I τ' l'' ∧
        size - (τ' "i").toNat < size - (τ "i").toNat := by
    rintro τ l' ⟨rfl, hlkτ, hszτ, m, hm, hiτ, hnτ⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .var "size") hiτ hszτ (by omega) hsize] at hg
    have hmlt : m < size := by
      by_cases h : m < size
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    obtain ⟨s, ln, p, hmm, hbs, hbl, -⟩ := hM.mat m hmlt
    obtain ⟨s', l', p', hmm', -, hsl⟩ := hv m hmlt
    rw [hmm] at hmm'; cases hmm'
    have hlkτ' : (τ "lk").toNat = i := by rw [hlkτ]; exact hlk
    let τ1 := τ.set "s" (BitVec.ofNat 32 s)
    have h1 : Runs (rprimsA εR c) (getMmsS mmb "s" (.var "i")) τ l' τ1 l' := by
      have h := rd_run (εR := εR) hcs hlkτ' "s" (mmE mmb (.var "i") 0)
        (mm_ix hmb hmlt (σ := τ) (je := .var "i") hiτ (by omega))
      rw [show mmb + 1 + 3 * m + 0 = mmb + 1 + 3 * m from rfl, hbs] at h; exact h
    let τ2 := τ1.set "l" (BitVec.ofNat 32 ln)
    have h2 : Runs (rprimsA εR c) (getMmlS mmb "l" (.var "i")) τ1 l' τ2 l' := by
      have h := rd_run (εR := εR) hcs (σ := τ1) (by simpa [τ1, Locals.set] using hlkτ') "l"
        (mmE mmb (.var "i") 1) (mm_ix hmb hmlt (σ := τ1) (je := .var "i")
          (by show τ1 "i" = _; simp [τ1, Locals.set, hiτ]) (by omega))
      rw [hbl] at h; exact h
    let M := (s + ln) / 4096 + 1
    let τ3 := τ2.set "maxs" (BitVec.ofNat 32 M)
    have h3 : Runs (rprimsA εR c)
        (.assign "maxs" (.bin .add (.bin .div (.bin .add (.var "s") (.var "l")) (.const 4096)) (.const 1)))
        τ2 l' τ3 l' := by
      refine asg_run _ _ ?_
      show (τ2 "s" + τ2 "l") / (4096 : Val) + 1 = _
      have e1 : τ2 "s" = BitVec.ofNat 32 s := by simp [τ2, τ1, Locals.set]
      have e2 : τ2 "l" = BitVec.ofNat 32 ln := by simp [τ2, Locals.set]
      rw [e1, e2]; exact maxs_val hsl
    have hMe : maxs_at_i m mm = M := by unfold maxs_at_i; rw [hmm]
    have hMb : M < 2 ^ 32 := by show (s + ln) / 4096 + 1 < 2 ^ 32; omega
    have hcb := cnps_le hv m hm
    have hgi : (Expr.bin .ltu (.var "nps") (.var "maxs")).eval τ3 = if cnps mm m < M then 1 else 0 :=
      ltu_eval (σ := τ3) (ea := .var "nps") (eb := .var "maxs")
        (by show τ3 "nps" = _; simp [τ3, τ2, τ1, Locals.set, hnτ]) (by show τ3 "maxs" = _; simp [τ3])
        (by omega) hMb
    have hc1 : cnps mm (m + 1) = if cnps mm m < M then M else cnps mm m := by
      show (if cnps mm m < maxs_at_i m mm then maxs_at_i m mm else cnps mm m) = _
      rw [hMe]
    by_cases hlt : cnps mm m < M
    · rw [if_pos hlt] at hgi hc1
      let τ4 := τ3.set "nps" (BitVec.ofNat 32 M)
      have h4 : Runs (rprimsA εR c) (.assign "nps" (.var "maxs")) τ3 l' τ4 l' :=
        asg_run _ _ (by show τ3 "maxs" = _; simp [τ3])
      have h5 := asg_run (εR := εR) (c := c) (σ := τ4) (l := l') "i" (.bin .add (.var "i") (.const 1))
        (inc_eval (m := m) (by simp [τ4, τ3, τ2, τ1, Locals.set, hiτ]))
      refine ⟨_, l', Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq (Runs.ite_true (by rw [hgi]; decide) h4) h5))),
        ⟨rfl, by simp [τ4, τ3, τ2, τ1, Locals.set, hlkτ], by simp [τ4, τ3, τ2, τ1, Locals.set, hszτ],
          m + 1, hmlt, by simp, by simp [τ4, Locals.set, hc1]⟩, ?_⟩
      rw [Locals.set_same, hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
    · rw [if_neg hlt] at hgi hc1
      have h5 := asg_run (εR := εR) (c := c) (σ := τ3) (l := l') "i" (.bin .add (.var "i") (.const 1))
        (inc_eval (m := m) (by simp [τ3, τ2, τ1, Locals.set, hiτ]))
      refine ⟨_, l', Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq (Runs.ite_false hgi Runs.skip) h5))),
        ⟨rfl, by simp [τ3, τ2, τ1, Locals.set, hlkτ], by simp [τ3, τ2, τ1, Locals.set, hszτ],
          m + 1, hmlt, by simp, by simp [τ3, τ2, τ1, Locals.set, hc1, hnτ]⟩, ?_⟩
      rw [Locals.set_same, hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', l', hr, ⟨rfl, hlk', hsz', m, hm, hi', hn'⟩, h0⟩ :=
    while_inv (εR := εR) (c := c) I (fun τ => size - (τ "i").toNat) hbody size σ l (by omega)
      ⟨rfl, rfl, hsz, 0, by omega, hi, by simpa [cnps] using hn⟩
  rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .var "size") hi' hsz' (by omega) hsize] at h0
  have hme : m = size := by
    by_cases h : m < size
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  exact ⟨σ', hr, hn', hsz', hlk'⟩

/-! ## The inner loop: is page `i` inside a region of the memory map? -/

/-- Region `x` of the memory map contains page `p`. -/
def covers (x : MMInfo) (p : Nat) : Prop := ∃ s l q, x = .MMValid s l q ∧ s ≤ p * 4096 ∧ (p + 1) * 4096 ≤ l + s

/-- `s <= i * PgSize && l + s >= (i + 1) * PgSize` -/
def coverE : Expr :=
  .bin .mul (.bin .eq (.bin .ltu (.bin .mul (.var "i") (.const 4096)) (.var "s")) (.const 0))
    (.bin .eq (.bin .ltu (.bin .add (.var "l") (.var "s"))
      (.bin .mul (.bin .add (.var "i") (.const 1)) (.const 4096))) (.const 0))

theorem and0_eval (e1 e2 : Expr) (σ : Locals) :
    (Expr.bin .mul (.bin .eq e1 (.const 0)) (.bin .eq e2 (.const 0))).eval σ =
      (if e1.eval σ = 0 then 1 else 0) * (if e2.eval σ = 0 then 1 else 0) := rfl

theorem cover_eval {σ : Locals} {p s ln : Nat} (hi : σ "i" = BitVec.ofNat 32 p) (hs : σ "s" = BitVec.ofNat 32 s)
    (hl : σ "l" = BitVec.ofNat 32 ln) (hp : (p + 1) * 4096 < 2 ^ 32) (hsl : s + ln < 2 ^ 32) :
    coverE.eval σ = if s ≤ p * 4096 ∧ (p + 1) * 4096 ≤ ln + s then 1 else 0 := by
  have b1 : p * 4096 < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 4096 (Nat.le_succ p)) hp
  have b2 : s < 2 ^ 32 := by omega
  have b3 : ln + s < 2 ^ 32 := by omega
  have e1 : (Expr.bin .mul (.var "i") (.const 4096)).eval σ = BitVec.ofNat 32 (p * 4096) := by
    show σ "i" * (4096 : Val) = _
    rw [hi]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]
  have e2 : (Expr.bin .add (.var "l") (.var "s")).eval σ = BitVec.ofNat 32 (ln + s) := by
    show σ "l" + σ "s" = _
    rw [hl, hs]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  have e3 : (Expr.bin .mul (.bin .add (.var "i") (.const 1)) (.const 4096)).eval σ =
      BitVec.ofNat 32 ((p + 1) * 4096) := by
    show (σ "i" + 1) * (4096 : Val) = _
    rw [hi]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, BitVec.toNat_add]
  have a1 := ltu_eval (σ := σ) (ea := .bin .mul (.var "i") (.const 4096)) (eb := .var "s") e1 hs b1 b2
  have a2 := ltu_eval (σ := σ) (ea := .bin .add (.var "l") (.var "s"))
    (eb := .bin .mul (.bin .add (.var "i") (.const 1)) (.const 4096)) e2 e3 b3 hp
  unfold coverE
  rw [and0_eval, a1, a2]
  by_cases h1 : p * 4096 < s <;> by_cases h2 : ln + s < (p + 1) * 4096
  · have hr : ¬ (s ≤ p * 4096 ∧ (p + 1) * 4096 ≤ ln + s) := by omega
    rw [if_pos h1, if_pos h2, if_neg hr]; decide
  · have hr : ¬ (s ≤ p * 4096 ∧ (p + 1) * 4096 ≤ ln + s) := by omega
    rw [if_pos h1, if_neg h2, if_neg hr]; decide
  · have hr : ¬ (s ≤ p * 4096 ∧ (p + 1) * 4096 ≤ ln + s) := by omega
    rw [if_neg h1, if_pos h2, if_neg hr]; decide
  · have hr : s ≤ p * 4096 ∧ (p + 1) * 4096 ≤ ln + s := by omega
    rw [if_neg h1, if_neg h2, if_pos hr]; decide

/-- `s = get_mms(j); l = get_mml(j); isnorm = is_usable(j);
if (s <= i * PgSize && l + s >= (i + 1) * PgSize) flag = 1; j++;` -/
def scanBody (mmb : Nat) : Stmt APrim :=
  .seq (getMmsS mmb "s" (.var "j"))
    (.seq (getMmlS mmb "l" (.var "j"))
      (.seq (isUsableS mmb "isn" (.var "j"))
        (.seq (.ite coverE (.assign "flag" (.const 1)) .skip)
          (.assign "j" (.bin .add (.var "j") (.const 1))))))

/-- `j < size && flag == 0` -/
def scanGuard : Expr := .bin .mul (.bin .ltu (.var "j") (.var "size")) (.bin .eq (.var "flag") (.const 0))

def scanLoop (mmb : Nat) : Stmt APrim := .while scanGuard (scanBody mmb)

theorem scanGuard_eval {σ : Locals} {m size : Nat} (hj : σ "j" = BitVec.ofNat 32 m)
    (hsz : σ "size" = BitVec.ofNat 32 size) (hm : m < 2 ^ 32) (hs : size < 2 ^ 32) :
    scanGuard.eval σ = (if m < size then 1 else 0) * (if σ "flag" = 0 then 1 else 0) := by
  show (Expr.bin .ltu (.var "j") (.var "size")).eval σ * (if σ "flag" = 0 then (1 : Val) else 0) = _
  rw [ltu_eval (σ := σ) (ea := .var "j") (eb := .var "size") hj hsz hm hs]

/-- What the inner loop leaves: no region contains the page, or `flag` is set
and `isnorm` says whether the first region containing it is usable. -/
def ScanPost (mm : MMTable) (size p : Nat) (m : Nat) (σ : Locals) : Prop :=
  (σ "flag" = 0 ∧ ∀ j, j < m → ¬ covers (mm j) p) ∨
  (σ "flag" = 1 ∧ ∃ j s ln q, j < size ∧ mm j = .MMValid s ln q ∧ s ≤ p * 4096 ∧ (p + 1) * 4096 ≤ ln + s ∧
    σ "isn" = if q = .MMUsable then 1 else 0)

/-- **The inner loop.** It only reads. -/
theorem scanLoop_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b : Region} (hcs : CS1 c i l b)
    {mmb size : Nat} {mm : MMTable} (hmb : mmb + 1 + 3 * size ≤ 2 ^ 32) (hM : MatchMMap mmb mm size b)
    (hv : MM_valid mm size) {p : Nat} (hp : (p + 1) * 4096 < 2 ^ 32) (σ : Locals) (hlk : (σ "lk").toNat = i)
    (hi : σ "i" = BitVec.ofNat 32 p) (hsz : σ "size" = BitVec.ofNat 32 size) (hj : σ "j" = 0)
    (hfl : σ "flag" = 0) :
    ∃ σ', Runs (rprimsA εR c) (scanLoop mmb) σ l σ' l ∧ σ' "lk" = σ "lk" ∧ σ' "i" = σ "i" ∧
      σ' "size" = σ "size" ∧ σ' "nps" = σ "nps" ∧ ScanPost mm size p size σ' := by
  have hsize : size < 2 ^ 32 := by omega
  let I : Locals → RLog → Prop := fun τ l' => l' = l ∧ τ "lk" = σ "lk" ∧ τ "i" = σ "i" ∧
    τ "size" = σ "size" ∧ τ "nps" = σ "nps" ∧ ∃ m, m ≤ size ∧ τ "j" = BitVec.ofNat 32 m ∧ ScanPost mm size p m τ
  have hbody : ∀ τ l', I τ l' → ¬ scanGuard.eval τ = 0 →
      ∃ τ' l'', Runs (rprimsA εR c) (scanBody mmb) τ l' τ' l'' ∧ I τ' l'' ∧
        size - (τ' "j").toNat < size - (τ "j").toNat := by
    rintro τ l' ⟨rfl, hlkτ, hiτ, hszτ, hnτ, m, hm, hjτ, hpost⟩ hg
    rw [scanGuard_eval hjτ (hszτ.trans hsz) (by omega) hsize] at hg
    have hmlt : m < size := by
      by_cases h : m < size
      · exact h
      · rw [if_neg h] at hg; exact absurd (by simp) hg
    have hf0 : τ "flag" = 0 := by
      by_cases h : τ "flag" = 0
      · exact h
      · rw [if_neg h] at hg; exact absurd (by simp) hg
    have hnc : ∀ j, j < m → ¬ covers (mm j) p := by
      rcases hpost with ⟨-, h⟩ | ⟨h1, -⟩
      · exact h
      · rw [hf0] at h1; exact absurd h1 (by decide)
    obtain ⟨s, ln, q, hmm, hbs, hbl, hbu⟩ := hM.mat m hmlt
    obtain ⟨s', l', q', hmm', -, hsl⟩ := hv m hmlt
    rw [hmm] at hmm'; cases hmm'
    have hlkτ' : (τ "lk").toNat = i := by rw [hlkτ]; exact hlk
    let τ1 := τ.set "s" (BitVec.ofNat 32 s)
    have h1 : Runs (rprimsA εR c) (getMmsS mmb "s" (.var "j")) τ l' τ1 l' := by
      have h := rd_run (εR := εR) hcs hlkτ' "s" (mmE mmb (.var "j") 0)
        (mm_ix hmb hmlt (σ := τ) (je := .var "j") hjτ (by omega))
      rw [show mmb + 1 + 3 * m + 0 = mmb + 1 + 3 * m from rfl, hbs] at h; exact h
    let τ2 := τ1.set "l" (BitVec.ofNat 32 ln)
    have h2 : Runs (rprimsA εR c) (getMmlS mmb "l" (.var "j")) τ1 l' τ2 l' := by
      have h := rd_run (εR := εR) hcs (σ := τ1) (by simpa [τ1, Locals.set] using hlkτ') "l"
        (mmE mmb (.var "j") 1) (mm_ix hmb hmlt (σ := τ1) (je := .var "j")
          (by show τ1 "j" = _; simp [τ1, Locals.set, hjτ]) (by omega))
      rw [hbl] at h; exact h
    let u : Val := if q = .MMUsable then 1 else 0
    let τ3 := τ2.set "isn" u
    have h3 : Runs (rprimsA εR c) (isUsableS mmb "isn" (.var "j")) τ2 l' τ3 l' := by
      have h := rd_run (εR := εR) hcs (σ := τ2) (by simpa [τ2, τ1, Locals.set] using hlkτ') "isn"
        (mmE mmb (.var "j") 2) (mm_ix hmb hmlt (σ := τ2) (je := .var "j")
          (by show τ2 "j" = _; simp [τ2, τ1, Locals.set, hjτ]) (by omega))
      rw [hbu] at h; exact h
    have hce := cover_eval (σ := τ3) (p := p) (s := s) (ln := ln)
      (by simp [τ3, τ2, τ1, Locals.set, hiτ, hi]) (by simp [τ3, τ2, τ1, Locals.set])
      (by simp [τ3, τ2, Locals.set]) hp (by omega)
    by_cases hcov : s ≤ p * 4096 ∧ (p + 1) * 4096 ≤ ln + s
    · rw [if_pos hcov] at hce
      let τ4 := τ3.set "flag" 1
      have h4 : Runs (rprimsA εR c) (.assign "flag" (.const 1)) τ3 l' τ4 l' := Runs.assign _ _
      have h5 := asg_run (εR := εR) (c := c) (σ := τ4) (l := l') "j" (.bin .add (.var "j") (.const 1))
        (inc_eval (m := m) (by simp [τ4, τ3, τ2, τ1, Locals.set, hjτ]))
      refine ⟨_, l', Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq
        (Runs.ite_true (by rw [hce]; decide) h4) h5))),
        ⟨rfl, by simp [τ4, τ3, τ2, τ1, Locals.set, hlkτ], by simp [τ4, τ3, τ2, τ1, Locals.set, hiτ],
          by simp [τ4, τ3, τ2, τ1, Locals.set, hszτ], by simp [τ4, τ3, τ2, τ1, Locals.set, hnτ],
          m + 1, hmlt, by simp, Or.inr ⟨by simp [τ4, Locals.set], m, s, ln, q, hmlt, hmm, hcov.1, hcov.2,
            by simp [τ4, τ3, Locals.set, u]⟩⟩, ?_⟩
      rw [Locals.set_same, hjτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
    · rw [if_neg hcov] at hce
      have h5 := asg_run (εR := εR) (c := c) (σ := τ3) (l := l') "j" (.bin .add (.var "j") (.const 1))
        (inc_eval (m := m) (by simp [τ3, τ2, τ1, Locals.set, hjτ]))
      refine ⟨_, l', Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq (Runs.ite_false hce Runs.skip) h5))),
        ⟨rfl, by simp [τ3, τ2, τ1, Locals.set, hlkτ], by simp [τ3, τ2, τ1, Locals.set, hiτ],
          by simp [τ3, τ2, τ1, Locals.set, hszτ], by simp [τ3, τ2, τ1, Locals.set, hnτ],
          m + 1, hmlt, by simp, Or.inl ⟨by simp [τ3, τ2, τ1, Locals.set, hf0], fun j hj hc => ?_⟩⟩, ?_⟩
      · by_cases e : j = m
        · subst e
          obtain ⟨s2, l2, q2, hm2, c1, c2⟩ := hc
          rw [hmm] at hm2; cases hm2; exact hcov ⟨c1, c2⟩
        · exact hnc j (by omega) hc
      · rw [Locals.set_same, hjτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', l', hr, ⟨rfl, hlk', hi', hsz', hn', m, hm, hj', hpost⟩, h0⟩ :=
    while_inv (εR := εR) (c := c) I (fun τ => size - (τ "j").toNat) hbody size σ l (by omega)
      ⟨rfl, rfl, rfl, rfl, rfl, 0, by omega, hj, Or.inl ⟨hfl, fun j hj => by omega⟩⟩
  refine ⟨σ', hr, hlk', hi', hsz', hn', ?_⟩
  rw [scanGuard_eval hj' (hsz'.trans hsz) (by omega) hsize] at h0
  rcases hpost with ⟨hf, hnc⟩ | hw
  · have hme : m = size := by
      by_cases h : m < size
      · rw [if_pos h, if_pos hf] at h0; exact absurd h0 (by decide)
      · omega
    subst hme; exact Or.inl ⟨hf, hnc⟩
  · exact Or.inr hw

/-! ## The second loop: the type of each page -/

/-- The type `mem_init` gives page `p`: 1 kernel, 2 normal, 0 reserved. -/
def entryCode (kl kh : Nat) (mm : MMTable) (size p : Nat) : Nat :=
  if p < kl ∨ kh ≤ p then 1 else if mmKernValidB mm p size then 2 else 0

/-- No region contains the page: it is not inside a usable one. -/
theorem scan_none {mm : MMTable} {size p : Nat} (h : ∀ j, j < size → ¬ covers (mm j) p) :
    mmKernValidB mm p size = false := by
  cases hb : mmKernValidB mm p size with
  | false => rfl
  | true =>
    obtain ⟨j, s, l, hj, hm, h1, h2⟩ := (mmKernValidB_iff mm p size).1 hb
    exact absurd ⟨s, l, _, hm, h1, h2⟩ (h j hj)

/-- Some region contains the page: by `MM_correct`, the page is inside a
usable region exactly when that one is usable. -/
theorem scan_some {mm : MMTable} {size p : Nat} (hc : MM_correct mm size) {j s ln : Nat} {q : MMPerm}
    (hj : j < size) (hm : mm j = .MMValid s ln q) (h1 : s ≤ p * 4096) (h2 : (p + 1) * 4096 ≤ ln + s) :
    mmKernValidB mm p size = decide (q = .MMUsable) := by
  cases hb : mmKernValidB mm p size with
  | true =>
    obtain ⟨j', s', l', hj', hm', h1', h2'⟩ := (mmKernValidB_iff mm p size).1 hb
    have := hc j j' s s' ln l' q .MMUsable hj hj' hm hm' (by omega) (by omega)
    simp [this]
  | false =>
    by_cases hq : q = .MMUsable
    · subst hq
      have := (mmKernValidB_iff mm p size).2 ⟨j, s, ln, hj, hm, h1, h2⟩
      rw [hb] at this; cases this
    · simp [hq]

theorem set3_same (σ : Locals) : ((σ.set "_" 0).set "_" 0).set "_" 0 = σ.set "_" 0 := by
  rw [set_set, set_set]

/-- **`set_norm(i, v)`** writes the three cells of entry `i`. -/
theorem setNorm_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b : Region} (hcs : CS1 c i l b)
    {maxpage : Nat} (hmax : 3 * maxpage < 2 ^ 32) {σ : Locals} (hlk : (σ "lk").toNat = i) {p : Nat}
    (hi : σ "i" = BitVec.ofNat 32 p) (hp : p < maxpage) (v : Val) :
    ∃ l', Runs (rprimsA εR c) (setNormS (.var "i") (.const v)) σ l (σ.set "_" 0) l' ∧
      CS1 c i l' (setCell (setCell (setCell b (3 * p) v) (3 * p + 1) 0) (3 * p + 2) 0) := by
  obtain ⟨l1, h1, c1⟩ := wr_run (εR := εR) hcs hlk (ixE (.var "i") 0) (.const v) (n := 3 * p) (v := v)
    (by show ix (σ "i") 0 = _; rw [hi]; exact ix0 hmax hp) rfl
  let σ1 := σ.set "_" 0
  have hi1 : σ1 "i" = BitVec.ofNat 32 p := by simp [σ1, Locals.set, hi]
  have hlk1 : (σ1 "lk").toNat = i := by simpa [σ1, Locals.set] using hlk
  obtain ⟨l2, h2, c2⟩ := wr_run (εR := εR) c1 hlk1 (ixE (.var "i") 1) (.const 0) (n := 3 * p + 1) (v := 0)
    (by show ix (σ1 "i") 1 = _; rw [hi1]; exact ix1 hmax hp) rfl
  let σ2 := σ1.set "_" 0
  have hi2 : σ2 "i" = BitVec.ofNat 32 p := by simp [σ2, σ1, Locals.set, hi]
  have hlk2 : (σ2 "lk").toNat = i := by simpa [σ2, σ1, Locals.set] using hlk
  obtain ⟨l3, h3, c3⟩ := wr_run (εR := εR) c2 hlk2 (ixE (.var "i") 2) (.const 0) (n := 3 * p + 2) (v := 0)
    (by show ix (σ2 "i") 2 = _; rw [hi2]; exact ix2 hmax hp) rfl
  have hr := Runs.seq h1 (Runs.seq h2 h3)
  rw [show (σ2.set "_" 0) = σ.set "_" 0 from set3_same σ] at hr
  exact ⟨l3, hr, c3⟩

/-- `i < kern_low || i >= kern_high` -/
def kernE (kl kh : Nat) : Expr :=
  .bin .add (.bin .ltu (.var "i") (.const (BitVec.ofNat 32 kl)))
    (.bin .eq (.bin .ltu (.var "i") (.const (BitVec.ofNat 32 kh))) (.const 0))

theorem kern_eval {σ : Locals} {p kl kh : Nat} (hi : σ "i" = BitVec.ofNat 32 p) (hp : p < 2 ^ 32)
    (hkl : kl < 2 ^ 32) (hkh : kh < 2 ^ 32) : (kernE kl kh).eval σ = 0 ↔ ¬ (p < kl ∨ kh ≤ p) := by
  have a1 := ltu_eval (σ := σ) (ea := .var "i") (eb := .const (BitVec.ofNat 32 kl)) hi rfl hp hkl
  have a2 := ltu_eval (σ := σ) (ea := .var "i") (eb := .const (BitVec.ofNat 32 kh)) hi rfl hp hkh
  have e : (kernE kl kh).eval σ = (Expr.bin .ltu (.var "i") (.const (BitVec.ofNat 32 kl))).eval σ +
      (if (Expr.bin .ltu (.var "i") (.const (BitVec.ofNat 32 kh))).eval σ = 0 then 1 else 0) := rfl
  rw [e, a1, a2]
  by_cases h1 : p < kl <;> by_cases h2 : p < kh
  · rw [if_pos h1, if_pos h2]; exact ⟨fun h => absurd h (by decide), fun h => absurd (Or.inl h1) h⟩
  · rw [if_pos h1, if_neg h2]; exact ⟨fun h => absurd h (by decide), fun h => absurd (Or.inl h1) h⟩
  · rw [if_neg h1, if_pos h2]; exact ⟨fun _ => by omega, fun _ => by decide⟩
  · rw [if_neg h1, if_neg h2]; exact ⟨fun h => absurd h (by decide), fun h => absurd (Or.inr (by omega)) h⟩

/-- `flag == 1 && isnorm == 1` -/
def normE : Expr := .bin .mul (.bin .eq (.var "flag") (.const 1)) (.bin .eq (.var "isn") (.const 1))

/-- The body of the second loop:
`if (i < kern_low || i >= kern_high) set_norm(i, 1);
 else { j = 0; flag = 0; isnorm = 0; while (...) {...}
        if (flag == 1 && isnorm == 1) set_norm(i, 2); else set_norm(i, 0); }
 i++;` -/
def fillBody (mmb kl kh : Nat) : Stmt APrim :=
  .seq (.ite (kernE kl kh) (setNormS (.var "i") (.const 1))
      (.seq (.assign "j" (.const 0)) (.seq (.assign "flag" (.const 0)) (.seq (.assign "isn" (.const 0))
        (.seq (scanLoop mmb)
          (.ite normE (setNormS (.var "i") (.const 2)) (setNormS (.var "i") (.const 0))))))))
    (.assign "i" (.bin .add (.var "i") (.const 1)))

def fillLoop (mmb kl kh : Nat) : Stmt APrim := .while (.bin .ltu (.var "i") (.var "nps")) (fillBody mmb kl kh)

/-- Entry `p` after `set_norm(p, v)`. -/
def set3 (b : Region) (p : Nat) (v : Val) : Region :=
  setCell (setCell (setCell b (3 * p) v) (3 * p + 1) 0) (3 * p + 2) 0

/-- **One iteration of the second loop** gives page `i` its type. -/
theorem fillBody_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b : Region} (hcs : CS1 c i l b)
    {mmb size maxpage kl kh : Nat} {mm : MMTable} (hmb : mmb + 1 + 3 * size ≤ 2 ^ 32)
    (hmax : 3 * maxpage < 2 ^ 32) (hkl : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hM : MatchMMap mmb mm size b)
    (hv : MM_valid mm size) (hc : MM_correct mm size) {σ : Locals} (hlk : (σ "lk").toNat = i) {p : Nat}
    (hi : σ "i" = BitVec.ofNat 32 p) (hp : p < maxpage) (hsz : σ "size" = BitVec.ofNat 32 size) :
    ∃ σ' l', Runs (rprimsA εR c) (fillBody mmb kl kh) σ l σ' l' ∧
      CS1 c i l' (set3 b p (BitVec.ofNat 32 (entryCode kl kh mm size p))) ∧
      σ' "i" = BitVec.ofNat 32 (p + 1) ∧ σ' "size" = σ "size" ∧ σ' "nps" = σ "nps" ∧ σ' "lk" = σ "lk" := by
  have hke := kern_eval (σ := σ) (kl := kl) (kh := kh) hi (by omega) hkl (by omega)
  by_cases hk : p < kl ∨ kh ≤ p
  · have hcode : entryCode kl kh mm size p = 1 := by unfold entryCode; rw [if_pos hk]
    obtain ⟨l1, h1, c1⟩ := setNorm_run εR hcs hmax hlk hi hp 1
    have h2 := asg_run (εR := εR) (c := c) (σ := σ.set "_" 0) (l := l1) "i" (.bin .add (.var "i") (.const 1))
      (inc_eval (m := p) (by simp [Locals.set, hi]))
    refine ⟨_, l1, Runs.seq (Runs.ite_true (fun h => hke.1 h hk) h1) h2, by rw [hcode]; exact c1,
      by simp, by simp [Locals.set], by simp [Locals.set], by simp [Locals.set]⟩
  · have hpk : (p + 1) * 4096 < 2 ^ 32 := by omega
    let σ1 := ((σ.set "j" 0).set "flag" 0).set "isn" 0
    have ha : Runs (rprimsA εR c) (.seq (.assign "j" (.const 0)) (.seq (.assign "flag" (.const 0))
        (.assign "isn" (.const 0)))) σ l σ1 l :=
      Runs.seq (Runs.assign _ _) (Runs.seq (Runs.assign _ _) (Runs.assign _ _))
    obtain ⟨σ2, hs, hlk2, hi2, hsz2, hn2, hpost⟩ := scanLoop_run εR hcs hmb hM hv hpk σ1
      (by simpa [σ1, Locals.set] using hlk) (by simp [σ1, Locals.set, hi]) (by simp [σ1, Locals.set, hsz])
      (by simp [σ1, Locals.set]) (by simp [σ1, Locals.set])
    have hlkσ2 : (σ2 "lk").toNat = i := by rw [hlk2]; simpa [σ1, Locals.set] using hlk
    have hiσ2 : σ2 "i" = BitVec.ofNat 32 p := by rw [hi2]; simp [σ1, Locals.set, hi]
    have hne : normE.eval σ2 = (if σ2 "flag" = 1 then 1 else 0) * (if σ2 "isn" = 1 then 1 else 0) := rfl
    have hfin : ∀ (v : Nat), entryCode kl kh mm size p = v →
        (∃ l', Runs (rprimsA εR c) (.ite normE (setNormS (.var "i") (.const 2)) (setNormS (.var "i") (.const 0)))
          σ2 l (σ2.set "_" 0) l' ∧ CS1 c i l' (set3 b p (BitVec.ofNat 32 v))) →
        ∃ σ' l', Runs (rprimsA εR c) (fillBody mmb kl kh) σ l σ' l' ∧
          CS1 c i l' (set3 b p (BitVec.ofNat 32 (entryCode kl kh mm size p))) ∧
          σ' "i" = BitVec.ofNat 32 (p + 1) ∧ σ' "size" = σ "size" ∧ σ' "nps" = σ "nps" ∧ σ' "lk" = σ "lk" := by
      rintro v hv' ⟨l', hr, c'⟩
      have h2 := asg_run (εR := εR) (c := c) (σ := σ2.set "_" 0) (l := l') "i" (.bin .add (.var "i") (.const 1))
        (inc_eval (m := p) (by simp [Locals.set, hiσ2]))
      have hrun : Runs (rprimsA εR c) (fillBody mmb kl kh) σ l _ l' :=
        Runs.seq (Runs.ite_false (hke.2 hk) (Runs.seq (Runs.assign _ _) (Runs.seq (Runs.assign _ _)
          (Runs.seq (Runs.assign _ _) (Runs.seq hs hr))))) h2
      refine ⟨_, l', hrun, by rw [hv']; exact c', by simp, ?_, ?_, ?_⟩
      · simp [Locals.set, hsz2, σ1]
      · simp [Locals.set, hn2, σ1]
      · simp [Locals.set, hlk2, σ1]
    rcases hpost with ⟨hf, hnc⟩ | ⟨hf, j, s, ln, q, hj, hm, c1, c2, hisn⟩
    · have hcode : entryCode kl kh mm size p = 0 := by
        unfold entryCode; rw [if_neg hk, scan_none hnc]; rfl
      obtain ⟨l', hr, c'⟩ := setNorm_run εR hcs hmax hlkσ2 hiσ2 hp 0
      exact hfin 0 hcode ⟨l', Runs.ite_false
        (by rw [hne, hf, if_neg (by decide)]; exact BitVec.zero_mul) hr, c'⟩
    · by_cases hq : q = .MMUsable
      · have hcode : entryCode kl kh mm size p = 2 := by
          unfold entryCode; rw [if_neg hk, scan_some hc hj hm c1 c2]; simp [hq]
        rw [if_pos hq] at hisn
        obtain ⟨l', hr, c'⟩ := setNorm_run εR hcs hmax hlkσ2 hiσ2 hp 2
        exact hfin 2 hcode ⟨l', Runs.ite_true (by rw [hne, hf, hisn]; decide) hr, c'⟩
      · have hcode : entryCode kl kh mm size p = 0 := by
          unfold entryCode; rw [if_neg hk, scan_some hc hj hm c1 c2]; simp [hq]
        rw [if_neg hq] at hisn
        obtain ⟨l', hr, c'⟩ := setNorm_run εR hcs hmax hlkσ2 hiσ2 hp 0
        exact hfin 0 hcode ⟨l', Runs.ite_false (by rw [hne, hf, hisn]; decide) hr, c'⟩

/-- The region once the first `m` pages have their type: those entries are
written, everything from cell `3 * m` on is as in `b0`. -/
def Filled (kl kh : Nat) (mm : MMTable) (size : Nat) (b0 : Region) (m : Nat) (b : Region) : Prop :=
  (∀ k, 3 * m ≤ k → b k = b0 k) ∧
  ∀ p, p < m → b (3 * p) = BitVec.ofNat 32 (entryCode kl kh mm size p) ∧ b (3 * p + 1) = 0 ∧ b (3 * p + 2) = 0

theorem filled_step {kl kh : Nat} {mm : MMTable} {size : Nat} {b0 b : Region} {m : Nat}
    (h : Filled kl kh mm size b0 m b) :
    Filled kl kh mm size b0 (m + 1) (set3 b m (BitVec.ofNat 32 (entryCode kl kh mm size m))) := by
  refine ⟨fun k hk => ?_, fun p hp => ?_⟩
  · simp only [set3, setCell]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact h.1 k (by omega)
  · by_cases e : p = m
    · subst e
      refine ⟨?_, ?_, ?_⟩ <;> simp (disch := omega) only [set3, setCell, if_pos, if_neg, ↓reduceIte]
    · obtain ⟨h1, h2, h3⟩ := h.2 p (by omega)
      refine ⟨?_, ?_, ?_⟩
      · simp only [set3, setCell]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact h1
      · simp only [set3, setCell]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact h2
      · simp only [set3, setCell]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact h3

theorem matchMM_of_eq {mmb size : Nat} {mm : MMTable} {b b' : Region} (hM : MatchMMap mmb mm size b)
    (h : ∀ k, mmb ≤ k → b' k = b k) : MatchMMap mmb mm size b' := by
  refine ⟨by rw [h mmb (Nat.le_refl _)]; exact hM.msize, fun j hj => ?_⟩
  obtain ⟨s, l, p, hm, h1, h2, h3⟩ := hM.mat j hj
  exact ⟨s, l, p, hm, by rw [h _ (by omega)]; exact h1, by rw [h _ (by omega)]; exact h2,
    by rw [h _ (by omega)]; exact h3⟩

/-- **The second loop** gives every page below `nps` its type, and writes
nothing else. -/
theorem fillLoop_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b0 : Region} (hcs : CS1 c i l b0)
    {mmb size maxpage kl kh nps : Nat} {mm : MMTable} (hmb : mmb + 1 + 3 * size ≤ 2 ^ 32)
    (hmax : 3 * maxpage < mmb) (hkl : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hM : MatchMMap mmb mm size b0)
    (hv : MM_valid mm size) (hc : MM_correct mm size) (hnps : nps ≤ maxpage) (σ : Locals)
    (hlk : (σ "lk").toNat = i) (hi : σ "i" = 0) (hsz : σ "size" = BitVec.ofNat 32 size)
    (hn : σ "nps" = BitVec.ofNat 32 nps) :
    ∃ σ' l' b', Runs (rprimsA εR c) (fillLoop mmb kl kh) σ l σ' l' ∧ CS1 c i l' b' ∧
      Filled kl kh mm size b0 nps b' ∧ σ' "lk" = σ "lk" := by
  have hmax' : 3 * maxpage < 2 ^ 32 := by omega
  let I : Locals → RLog → Prop := fun τ l' => τ "lk" = σ "lk" ∧ τ "size" = BitVec.ofNat 32 size ∧
    τ "nps" = BitVec.ofNat 32 nps ∧ ∃ m b', m ≤ nps ∧ τ "i" = BitVec.ofNat 32 m ∧ CS1 c i l' b' ∧
      Filled kl kh mm size b0 m b'
  have hbody : ∀ τ l', I τ l' → ¬ (Expr.bin .ltu (.var "i") (.var "nps")).eval τ = 0 →
      ∃ τ' l'', Runs (rprimsA εR c) (fillBody mmb kl kh) τ l' τ' l'' ∧ I τ' l'' ∧
        nps - (τ' "i").toNat < nps - (τ "i").toNat := by
    rintro τ l' ⟨hlkτ, hszτ, hnτ, m, b', hm, hiτ, hcs', hF⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .var "nps") hiτ hnτ (by omega) (by omega)] at hg
    have hmlt : m < nps := by
      by_cases h : m < nps
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    have hM' : MatchMMap mmb mm size b' := matchMM_of_eq hM (fun k hk => hF.1 k (by omega))
    obtain ⟨τ', l'', hr, hcs'', hi', hsz', hn', hlk'⟩ := fillBody_run εR hcs' hmb hmax' hkl hkh hM' hv hc
      (σ := τ) (by rw [hlkτ]; exact hlk) hiτ (by omega) hszτ
    refine ⟨τ', l'', hr, ⟨hlk'.trans hlkτ, hsz'.trans hszτ, hn'.trans hnτ, m + 1, _, hmlt, hi', hcs'',
      filled_step hF⟩, ?_⟩
    rw [hi', hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', l', hr, ⟨hlk', hsz', hn', m, b', hm, hi', hcs', hF⟩, h0⟩ :=
    while_inv (εR := εR) (c := c) I (fun τ => nps - (τ "i").toNat) hbody nps σ l (by omega)
      ⟨rfl, hsz, hn, 0, b0, by omega, hi, hcs, fun k _ => rfl, fun p hp => by omega⟩
  rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .var "nps") hi' hn' (by omega) (by omega)] at h0
  have hme : m = nps := by
    by_cases h : m < nps
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  exact ⟨σ', l', b', hr, hcs', hF, hlk'⟩

/-! ## `mem_init` -/

/-- The body of **`mem_init`**. The call to `boot_loader` is not here: its
effect, the memory map at `mmb`, is the precondition `MatchMMap`.

`i = 0; size = get_size(); nps = 0; while (i < size) {...}
 set_nps(nps); i = 0; while (i < nps) {...}` -/
def memInitCS (mmb maxpage kl kh : Nat) : Stmt APrim :=
  .seq (.assign "i" (.const 0)) (.seq (getSizeS mmb "size") (.seq (.assign "nps" (.const 0))
    (.seq (npsLoop mmb) (.seq (setNpsS maxpage (.var "nps")) (.seq (.assign "i" (.const 0))
      (fillLoop mmb kl kh))))))

/-- **What `mem_init`'s code does to the region.** -/
theorem memInitCS_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b : Region} (hcs : CS1 c i l b)
    {mmb size maxpage kl kh : Nat} {mm : MMTable} (hmb : mmb + 1 + 3 * size ≤ 2 ^ 32)
    (hmax : 3 * maxpage < mmb) (hmp : 2 ^ 20 ≤ maxpage) (hkl : kl < 2 ^ 32) (hkh : kh < 2 ^ 20)
    (hM : MatchMMap mmb mm size b) (hv : MM_valid mm size) (hc : MM_correct mm size) (σ : Locals)
    (hlk : (σ "lk").toNat = i) :
    ∃ σ' l' b', Runs (rprimsA εR c) (memInitCS mmb maxpage kl kh) σ l σ' l' ∧ CS1 c i l' b' ∧
      Filled kl kh mm size (setCell b (3 * maxpage) (BitVec.ofNat 32 (cnps mm size))) (cnps mm size) b' ∧
      σ' "lk" = σ "lk" := by
  let σ1 := σ.set "i" 0
  let σ2 := σ1.set "size" (BitVec.ofNat 32 size)
  let σ3 := σ2.set "nps" 0
  have h1 : Runs (rprimsA εR c) (.assign "i" (.const 0)) σ l σ1 l := Runs.assign _ _
  have h2 : Runs (rprimsA εR c) (getSizeS mmb "size") σ1 l σ2 l := by
    have h := rd_run (εR := εR) hcs (σ := σ1) (by simpa [σ1, Locals.set] using hlk) "size"
      (.const (BitVec.ofNat 32 mmb)) (n := mmb) (tn (by omega))
    rw [hM.msize] at h; exact h
  have h3 : Runs (rprimsA εR c) (.assign "nps" (.const 0)) σ2 l σ3 l := Runs.assign _ _
  obtain ⟨σ4, h4, hn4, hsz4, hlk4⟩ := npsLoop_run εR hcs hmb hM hv σ3
    (by simpa [σ3, σ2, σ1, Locals.set] using hlk) (by simp [σ3, σ2, σ1, Locals.set])
    (by simp [σ3, σ2, Locals.set]) (by simp [σ3])
  have hlkσ4 : (σ4 "lk").toNat = i := by rw [hlk4]; simpa [σ3, σ2, σ1, Locals.set] using hlk
  obtain ⟨l5, h5, c5⟩ := wr_run (εR := εR) hcs hlkσ4 (.const (BitVec.ofNat 32 (3 * maxpage))) (.var "nps")
    (n := 3 * maxpage) (v := BitVec.ofNat 32 (cnps mm size)) (tn (by omega)) hn4
  let σ6 := (σ4.set "_" 0).set "i" 0
  have h6 : Runs (rprimsA εR c) (.assign "i" (.const 0)) (σ4.set "_" 0) l5 σ6 l5 := Runs.assign _ _
  have hM0 : MatchMMap mmb mm size (setCell b (3 * maxpage) (BitVec.ofNat 32 (cnps mm size))) :=
    matchMM_of_eq hM (fun k hk => by simp only [setCell]; rw [if_neg (by omega)])
  have hcl := cnps_le hv size (Nat.le_refl _)
  obtain ⟨σ7, l7, b7, h7, c7, hF, hlk7⟩ := fillLoop_run εR c5 hmb hmax hkl hkh hM0 hv hc
    (nps := cnps mm size) (by omega) σ6 (by simpa [σ6, Locals.set] using hlkσ4) (by simp [σ6])
    (by simp [σ6, Locals.set, hsz4]) (by simp [σ6, Locals.set, hn4])
  refine ⟨σ7, l7, b7, Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq h4 (Runs.seq h5 (Runs.seq h6 h7))))),
    c7, hF, ?_⟩
  rw [hlk7]; simp [σ6, Locals.set, hlk4, σ3, σ2, σ1]

theorem calAT_frame (kl kh nps : Nat) (mm : MMTable) (size : Nat) (At : ATable) :
    ∀ n i, n < i → Calculate_AT kl kh nps mm size n At i = At i
  | 0, i, h => by simp only [Calculate_AT]; rw [setAt_ne _ _ (by omega)]
  | n + 1, i, h => by
    simp only [Calculate_AT]
    rw [setAt_ne _ _ (by omega)]; exact calAT_frame kl kh nps mm size At n i (by omega)

theorem atEntry_code (kl kh nps : Nat) (mm : MMTable) (size : Nat) {i : Nat} (hi : i < nps) :
    ∃ t, atEntry kl kh nps mm size i = .ATValid false t 0 ∧ ZtoATType (entryCode kl kh mm size i) = some t := by
  unfold atEntry entryCode
  by_cases h1 : kl ≤ i
  · by_cases h2 : i < kh
    · have hk : ¬ (i < kl ∨ kh ≤ i) := by rintro (h | h) <;> omega
      rw [if_pos h1, if_pos (by simp only [Nat.lt_min]; omega), if_neg hk]
      cases mmKernValidB mm i size
      · exact ⟨_, rfl, rfl⟩
      · exact ⟨_, rfl, rfl⟩
    · rw [if_pos h1, if_neg (by simp only [Nat.lt_min]; omega), if_pos (Or.inr (by omega))]
      exact ⟨_, rfl, rfl⟩
  · rw [if_neg h1, if_pos (Or.inl (by omega))]; exact ⟨_, rfl, rfl⟩

/-- **`mem_init` refines `mem_init_spec`.** In a critical section, on a
region holding an allocation table and the boot loader's memory map, the C
code runs to completion and leaves the allocation table of the
specification. It writes only the allocation table's cells. -/
theorem mem_init_triple (εR : REnv) (c : CPU) (i : Nat) {mmb size maxpage kl kh : Nat} {mm : MMTable}
    (hmb : mmb + 1 + 3 * size ≤ 2 ^ 32) (hmax : 3 * maxpage < mmb) (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl)
    (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size) (hv : MM_valid mm size)
    (hc : MM_correct mm size) :
    Triple εR c i (fun (d : PData) b => MatchD maxpage d b ∧ MatchMMap mmb mm size b)
      (fun k => k ≤ 3 * maxpage) (fun _ d => d.init = false) (memInitCS mmb maxpage kl kh)
      (fun _ d _ d' => mem_init_spec kl kh mm size d = some d') := by
  rintro σ l b d hlk hcs ⟨hD, hM⟩ hin
  obtain ⟨σ', l', b', hr, hcs', hF, hlk'⟩ := memInitCS_run εR hcs hmb hmax hmp hkl' hkh hM hv hc σ hlk
  rw [cnps_real hsz] at hF
  have hnb : real_nps mm size ≤ 2 ^ 20 := by rw [← cnps_real hsz]; exact cnps_le hv size (Nat.le_refl _)
  have hn1 : 0 < real_nps mm size := by
    obtain ⟨s, ln, q, hm, -, -⟩ := hv 0 hsz
    have := calnps_ge mm (size - 1) 0 (Nat.zero_le _)
    unfold maxs_at_i at this; rw [hm] at this
    have h1 : 1 ≤ (s + ln) / 4096 + 1 := by omega
    exact Nat.lt_of_lt_of_le h1 this
  have hb0 : ∀ k, k ≠ 3 * maxpage → 3 * real_nps mm size ≤ k → b' k = b k := by
    intro k h1 h2
    rw [hF.1 k h2]; simp only [setCell]; rw [if_neg h1]
  refine ⟨σ', l', b', { d with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, init := true },
    hr, hcs', ⟨⟨fun p hp => ?_, ?_⟩, matchMM_of_eq hM (fun k hk => hb0 k (by omega) (by omega))⟩, hlk',
    fun k hk => hb0 k (by omega) (by omega), by show mem_init_spec kl kh mm size d = some _; unfold mem_init_spec; rw [if_pos hin]⟩
  · show MatchInfo (real_AT kl kh mm size d.AT p) _ _ _
    by_cases hpn : p < real_nps mm size
    · obtain ⟨h1, h2, h3⟩ := hF.2 p hpn
      obtain ⟨t, ht, hz⟩ := atEntry_code kl kh (real_nps mm size) mm size hpn
      unfold real_AT
      rw [calAT_get kl kh _ mm size d.AT hkl _ p (by omega), ht, h1, h2, h3]
      have hcb : entryCode kl kh mm size p < 2 ^ 32 := by
        unfold entryCode; split
        · decide
        · split <;> decide
      exact ⟨by rw [tn hcb]; exact hz, rfl, rfl⟩
    · unfold real_AT
      rw [calAT_frame kl kh _ mm size d.AT (real_nps mm size - 1) p (by omega), hb0 (3 * p + 2) (by omega) (by omega),
        hb0 (3 * p + 1) (by omega) (by omega), hb0 (3 * p) (by omega) (by omega)]
      exact hD.mat p hp
  · show real_nps mm size = (b' (3 * maxpage)).toNat
    rw [hF.1 _ (by omega)]
    simp only [setCell, if_pos]
    exact (tn (by omega)).symm

end MALInit
