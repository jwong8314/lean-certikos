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
structure MatchMM (mmb : Nat) (mm : MMTable) (size : Nat) (b : Region) : Prop where
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
    {mmb size : Nat} {mm : MMTable} (hmb : mmb + 1 + 3 * size ≤ 2 ^ 32) (hM : MatchMM mmb mm size b)
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

end MALInit
