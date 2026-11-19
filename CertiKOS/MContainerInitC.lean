import CertiKOS.MALInitC
import CertiKOS.MContainerInit

/-!
# mCertiKOS `container_init`: the C code, ported and verified

`container_init` (`mm/MALTCSource.v`) calls `mem_init`, counts the free normal
pages, and writes the root container.

* `container_init_triple`: **the C code refines `container_init_spec`.**

As in the sources (`valid_preinit_container`), the proof needs every
container to be unused before initialisation: the code writes only
container 0.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MContainer

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding)
open LockRegionCPU KernFrame MALOp MALInit Layer

theorem and_val (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : Val) else 0) * (if q then 1 else 0) = if (decide p && decide q) = true then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- `norm == 1 && used == 0` -/
def cntE : Expr := .bin .mul (.bin .eq (.var "isn") (.const 1)) (.bin .eq (.var "cur") (.const 0))

/-- `norm = is_norm(i); used = at_get(i); if (norm == 1 && used == 0) real_quota++; i++;` -/
def cntBody : Stmt APrim :=
  .seq (isNormS "isn" (.var "i")) (.seq (atGetS "cur" (.var "i"))
    (.seq (.ite cntE (.assign "rq" (.bin .add (.var "rq") (.const 1))) .skip)
      (.assign "i" (.bin .add (.var "i") (.const 1)))))

def cntLoop : Stmt APrim := .while (.bin .ltu (.var "i") (.var "tnps")) cntBody

theorem unused_succ (A : ATable) {m : Nat} (hm : 0 < m) :
    unused_pages_AT A m = pterm (A m) + unused_pages_AT A (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rfl

/-- **The counting loop** leaves the number of free normal pages in `rq`. It
only reads. -/
theorem cntLoop_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b : Region} (hcs : CS1 c i l b)
    {maxpage : Nat} (hmax : 3 * maxpage < 2 ^ 32) {d : PData} (hD : MatchD maxpage d b)
    (hle : d.nps ≤ maxpage) (hn1 : 0 < d.nps) (hval : ∀ p, p < d.nps → ∃ b0 t n, d.AT p = .ATValid b0 t n)
    (σ : Locals) (hlk : (σ "lk").toNat = i) (hi : σ "i" = 1) (hrq : σ "rq" = 0)
    (htn : σ "tnps" = BitVec.ofNat 32 d.nps) :
    ∃ σ', Runs (rprimsA εR c) cntLoop σ l σ' l ∧
      σ' "rq" = BitVec.ofNat 32 (unused_pages_AT d.AT (d.nps - 1)) ∧ σ' "lk" = σ "lk" := by
  let I : Locals → RLog → Prop := fun τ l' => l' = l ∧ τ "lk" = σ "lk" ∧ τ "tnps" = BitVec.ofNat 32 d.nps ∧
    ∃ m, 0 < m ∧ m ≤ d.nps ∧ τ "i" = BitVec.ofNat 32 m ∧
      τ "rq" = BitVec.ofNat 32 (unused_pages_AT d.AT (m - 1))
  have hbody : ∀ τ l', I τ l' → ¬ (Expr.bin .ltu (.var "i") (.var "tnps")).eval τ = 0 →
      ∃ τ' l'', Runs (rprimsA εR c) cntBody τ l' τ' l'' ∧ I τ' l'' ∧
        d.nps - (τ' "i").toNat < d.nps - (τ "i").toNat := by
    rintro τ l' ⟨rfl, hlkτ, htnτ, m, hm0, hm, hiτ, hrqτ⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .var "tnps") hiτ htnτ (by omega) (by omega)] at hg
    have hmlt : m < d.nps := by
      by_cases h : m < d.nps
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    have hlkτ' : (τ "lk").toNat = i := by rw [hlkτ]; exact hlk
    let τ1 := τ.set "isn" (isNormC b (BitVec.ofNat 32 m))
    have h1 : Runs (rprimsA εR c) (isNormS "isn" (.var "i")) τ l' τ1 l' := by
      have h := isNorm_run (εR := εR) hcs hlkτ' "isn" (.var "i")
      have e : (Expr.var "i").eval τ = BitVec.ofNat 32 m := hiτ
      rw [e] at h; exact h
    let τ2 := τ1.set "cur" (atGetC b (BitVec.ofNat 32 m))
    have h2 : Runs (rprimsA εR c) (atGetS "cur" (.var "i")) τ1 l' τ2 l' := by
      have h := atGet_run (εR := εR) hcs (σ := τ1) (by simpa [τ1, Locals.set] using hlkτ') "cur" (.var "i")
      have e : (Expr.var "i").eval τ1 = BitVec.ofNat 32 m := by show τ1 "i" = _; simp [τ1, Locals.set, hiτ]
      rw [e] at h; exact h
    have hce : cntE.eval τ2 = if freeC b m = true then 1 else 0 := by
      have e : cntE.eval τ2 = (if τ2 "isn" = 1 then (1 : Val) else 0) * (if τ2 "cur" = 0 then 1 else 0) := rfl
      have e1 : τ2 "isn" = isNormC b (BitVec.ofNat 32 m) := by simp [τ2, τ1, Locals.set]
      have e2 : τ2 "cur" = atGetC b (BitVec.ofNat 32 m) := by simp [τ2]
      rw [e, e1, e2, and_val]; rfl
    have hfa : freeC b m = isFree (d.AT m) := free_agree hmax hD (by omega) (hval m hmlt)
    have hus := unused_succ d.AT hm0
    have hub := unused_le d.AT (m - 1)
    by_cases hf : freeC b m = true
    · rw [if_pos hf] at hce
      have hU : unused_pages_AT d.AT m = unused_pages_AT d.AT (m - 1) + 1 := by
        rw [hus]; unfold pterm; rw [← hfa, if_pos hf]; omega
      let τ3 := τ2.set "rq" (BitVec.ofNat 32 (unused_pages_AT d.AT (m - 1) + 1))
      have h3 : Runs (rprimsA εR c) (.assign "rq" (.bin .add (.var "rq") (.const 1))) τ2 l' τ3 l' :=
        asg_run _ _ (inc_eval (by simp [τ2, τ1, Locals.set, hrqτ]))
      have h4 := asg_run (εR := εR) (c := c) (σ := τ3) (l := l') "i" (.bin .add (.var "i") (.const 1))
        (inc_eval (m := m) (by simp [τ3, τ2, τ1, Locals.set, hiτ]))
      refine ⟨_, l', Runs.seq h1 (Runs.seq h2 (Runs.seq (Runs.ite_true (by rw [hce]; decide) h3) h4)),
        ⟨rfl, by simp [τ3, τ2, τ1, Locals.set, hlkτ], by simp [τ3, τ2, τ1, Locals.set, htnτ], m + 1,
          by omega, hmlt, by simp, by simp [τ3, Locals.set, hU]⟩, ?_⟩
      rw [Locals.set_same, hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
    · rw [if_neg hf] at hce
      have hU : unused_pages_AT d.AT m = unused_pages_AT d.AT (m - 1) := by
        rw [hus]; unfold pterm; rw [← hfa, if_neg hf]; omega
      have h4 := asg_run (εR := εR) (c := c) (σ := τ2) (l := l') "i" (.bin .add (.var "i") (.const 1))
        (inc_eval (m := m) (by simp [τ2, τ1, Locals.set, hiτ]))
      refine ⟨_, l', Runs.seq h1 (Runs.seq h2 (Runs.seq (Runs.ite_false hce Runs.skip) h4)),
        ⟨rfl, by simp [τ2, τ1, Locals.set, hlkτ], by simp [τ2, τ1, Locals.set, htnτ], m + 1,
          by omega, hmlt, by simp, by simp [τ2, τ1, Locals.set, hU, hrqτ]⟩, ?_⟩
      rw [Locals.set_same, hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', l', hr, ⟨rfl, hlk', htn', m, hm0, hm, hi', hrq'⟩, h0⟩ :=
    while_inv (εR := εR) (c := c) I (fun τ => d.nps - (τ "i").toNat) hbody d.nps σ l (by omega)
      ⟨rfl, rfl, htn, 1, by omega, hn1, hi, by simpa [unused_pages_AT] using hrq⟩
  rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .var "tnps") hi' htn' (by omega) (by omega)] at h0
  have hme : m = d.nps := by
    by_cases h : m < d.nps
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  exact ⟨σ', hr, hrq', hlk'⟩

/-- `container_LOC[0].f = v;` -/
def rootSetS (cb k : Nat) (ve : Expr) : Stmt APrim :=
  .call "_" .push [lkE, .const (BitVec.ofNat 32 (cb + k)), ve]

/-- The body of **`container_init`**:
`mem_init(mbi_addr); nps = get_nps(); real_quota = 0; i = 1; while (i < nps) {...}
 container_LOC[0].quota = real_quota; .usage = 0; .parent = 0; .nchildren = 0; .used = 1;` -/
def ctInitCS (mmb maxpage kl kh cb : Nat) : Stmt APrim :=
  .seq (memInitCS mmb maxpage kl kh) (.seq (getNpsS maxpage "tnps") (.seq (.assign "rq" (.const 0))
    (.seq (.assign "i" (.const 1)) (.seq cntLoop
      (.seq (rootSetS cb 0 (.var "rq")) (.seq (rootSetS cb 1 (.const 0)) (.seq (rootSetS cb 2 (.const 0))
        (.seq (rootSetS cb 3 (.const 0)) (rootSetS cb 4 (.const 1))))))))))

/-- The root container's five cells after `container_init`. -/
def rootC (b : Region) (cb : Nat) (q : Val) : Region :=
  setCell (setCell (setCell (setCell (setCell b (cb + 0) q) (cb + 1) 0) (cb + 2) 0) (cb + 3) 0) (cb + 4) 1

theorem root_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b : Region} (hcs : CS1 c i l b) {cb : Nat}
    (hcb : cb + 5 ≤ 2 ^ 32) {σ : Locals} (hlk : (σ "lk").toNat = i) :
    ∃ l', Runs (rprimsA εR c) (.seq (rootSetS cb 0 (.var "rq")) (.seq (rootSetS cb 1 (.const 0))
        (.seq (rootSetS cb 2 (.const 0)) (.seq (rootSetS cb 3 (.const 0)) (rootSetS cb 4 (.const 1))))))
        σ l (σ.set "_" 0) l' ∧ CS1 c i l' (rootC b cb (σ "rq")) := by
  have hlk' : ((σ.set "_" 0) "lk").toNat = i := by simpa [Locals.set] using hlk
  have hss : (σ.set "_" 0).set "_" 0 = σ.set "_" 0 := set_set _ _ _ _
  obtain ⟨l1, h1, c1⟩ := wr_run (εR := εR) hcs hlk (.const (BitVec.ofNat 32 (cb + 0))) (.var "rq")
    (n := cb + 0) (v := σ "rq") (tn (by omega)) rfl
  obtain ⟨l2, h2, c2⟩ := wr_run (εR := εR) c1 hlk' (.const (BitVec.ofNat 32 (cb + 1))) (.const 0)
    (n := cb + 1) (v := 0) (tn (by omega)) rfl
  rw [hss] at h2
  obtain ⟨l3, h3, c3⟩ := wr_run (εR := εR) c2 hlk' (.const (BitVec.ofNat 32 (cb + 2))) (.const 0)
    (n := cb + 2) (v := 0) (tn (by omega)) rfl
  rw [hss] at h3
  obtain ⟨l4, h4, c4⟩ := wr_run (εR := εR) c3 hlk' (.const (BitVec.ofNat 32 (cb + 3))) (.const 0)
    (n := cb + 3) (v := 0) (tn (by omega)) rfl
  rw [hss] at h4
  obtain ⟨l5, h5, c5⟩ := wr_run (εR := εR) c4 hlk' (.const (BitVec.ofNat 32 (cb + 4))) (.const 1)
    (n := cb + 4) (v := 1) (tn (by omega)) rfl
  rw [hss] at h5
  exact ⟨l5, Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq h4 h5))), c5⟩

theorem rootC_other (b : Region) (cb : Nat) (q : Val) {k : Nat} (h : k < cb ∨ cb + 5 ≤ k) :
    rootC b cb q k = b k := by
  simp only [rootC, setCell]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **`container_init` refines `container_init_spec`.** In a critical
section, on a region holding the allocation table, the containers and the
boot loader's memory map, with every container unused, the C code runs to
completion and leaves the allocation table and root container of the
specification. -/
theorem container_init_triple (εR : REnv) (c : CPU) (i : Nat) {mmb size maxpage num_id cb kl kh : Nat}
    {mm : MMTable} (hmb : mmb + 1 + 3 * size ≤ 2 ^ 32) (hcb : 3 * maxpage < cb)
    (hcm : cb + 5 * num_id ≤ mmb) (hnum : 0 < num_id) (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl)
    (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20) (hsz : 0 < size) (hv : MM_valid mm size)
    (hc : MM_correct mm size) :
    Triple εR c i (fun (d : RData) b => MatchMM maxpage num_id cb d b ∧ MatchMMap mmb mm size b)
      (fun k => k ≤ 3 * maxpage ∨ (cb ≤ k ∧ k < cb + 5))
      (fun _ d => d.init = false ∧ ∀ j, (d.AC j).cused = false) (ctInitCS mmb maxpage kl kh cb)
      (fun _ d _ d' => container_init_spec kl kh mm size d = some d') := by
  rintro σ l b d hlk hcs ⟨⟨hD, hC⟩, hM⟩ ⟨hin, hun⟩
  have hmax : 3 * maxpage < 2 ^ 32 := by omega
  obtain ⟨σ1, l1, b1, d1, hr1, hcs1, ⟨hD1, hM1⟩, hlk1, hf1, hq1⟩ :=
    mem_init_triple εR c i hmb (by omega) hmp hkl hkl' hkh hsz hv hc σ l b d.toPData hlk hcs ⟨hD, hM⟩ hin
  have hd1 : d1 = { d.toPData with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, init := true } := by
    have h := hq1
    unfold mem_init_spec at h
    rw [if_pos hin] at h
    exact (Option.some.inj h).symm
  have hnb : real_nps mm size ≤ 2 ^ 20 := by rw [← cnps_real hsz]; exact cnps_le hv size (Nat.le_refl _)
  have hn1 : 0 < real_nps mm size := by
    obtain ⟨s, ln, q, hm, -, -⟩ := hv 0 hsz
    have := calnps_ge mm (size - 1) 0 (Nat.zero_le _)
    unfold maxs_at_i at this; rw [hm] at this
    have h1 : 1 ≤ (s + ln) / 4096 + 1 := by omega
    exact Nat.lt_of_lt_of_le h1 this
  have hnps : d1.nps = real_nps mm size := by rw [hd1]
  have hAT : d1.AT = real_AT kl kh mm size d.AT := by rw [hd1]
  have hlkσ1 : (σ1 "lk").toNat = i := by rw [hlk1]; exact hlk
  -- nps = get_nps(); real_quota = 0; i = 1;
  let σ2 := σ1.set "tnps" (BitVec.ofNat 32 d1.nps)
  have h2 : Runs (rprimsA εR c) (getNpsS maxpage "tnps") σ1 l1 σ2 l1 := by
    have h := rd_run (εR := εR) hcs1 hlkσ1 "tnps" (.const (BitVec.ofNat 32 (3 * maxpage))) (n := 3 * maxpage)
      (tn hmax)
    rw [val_of_toNat hD1.mnps.symm (by rw [hnps]; omega)] at h; exact h
  let σ4 := (σ2.set "rq" 0).set "i" 1
  have h34 : Runs (rprimsA εR c) (.seq (.assign "rq" (.const 0)) (.assign "i" (.const 1))) σ2 l1 σ4 l1 :=
    Runs.seq (Runs.assign _ _) (Runs.assign _ _)
  obtain ⟨σ5, h5, hrq5, hlk5⟩ := cntLoop_run εR hcs1 hmax hD1 (by rw [hnps]; omega) (by rw [hnps]; exact hn1)
    (fun p hp => by
      rw [hAT]
      obtain ⟨t, n, h⟩ := real_AT_unalloc (kh := kh) d.AT hkl (by rw [← hnps]; exact hp)
      exact ⟨_, _, _, h⟩)
    σ4 (by simpa [σ4, σ2, Locals.set] using hlkσ1) (by simp [σ4]) (by simp [σ4, Locals.set])
    (by simp [σ4, σ2, Locals.set])
  have hrq : σ5 "rq" = BitVec.ofNat 32 (real_quota kl kh mm size) := by
    rw [hrq5, hAT, hnps, real_quota_unused hkl]
  have hlkσ5 : (σ5 "lk").toNat = i := by rw [hlk5]; simpa [σ4, σ2, Locals.set] using hlkσ1
  obtain ⟨l6, h6, hcs6⟩ := root_run εR hcs1 (cb := cb) (by omega) hlkσ5
  rw [hrq] at hcs6
  have hq : real_quota kl kh mm size < 2 ^ 32 := by
    have : real_quota kl kh mm size ≤ real_nps mm size - 1 := unused_le _ _
    omega
  have hb2 : ∀ k, k < cb ∨ cb + 5 ≤ k → rootC b1 cb (BitVec.ofNat 32 (real_quota kl kh mm size)) k = b1 k :=
    fun k hk => rootC_other _ _ _ hk
  refine ⟨σ5.set "_" 0, l6, _,
    { d with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, init := true,
             AC := real_AC kl kh mm size },
    Runs.seq hr1 (Runs.seq h2 (Runs.seq (Runs.assign _ _) (Runs.seq (Runs.assign _ _) (Runs.seq h5 h6)))),
    hcs6, ⟨⟨⟨fun p hp => ?_, ?_⟩, fun j hj => ?_⟩, matchMM_of_eq hM1 (fun k hk hk2 => hb2 k (by omega))⟩, ?_,
    fun k hk => ?_, by show container_init_spec kl kh mm size d = some _; unfold container_init_spec; rw [if_pos hin]⟩
  · have h := hD1.mat p hp
    rw [hd1] at h
    rw [hb2 (3 * p + 2) (by omega), hb2 (3 * p + 1) (by omega), hb2 (3 * p) (by omega)]
    exact h
  · have h := hD1.mnps
    rw [hd1] at h
    rw [hb2 (3 * maxpage) (by omega)]; exact h
  · show MatchCont (real_AC kl kh mm size j) _ _ _ _ _
    by_cases hj0 : j = 0
    · subst hj0
      rw [real_AC_zero]
      unfold MatchCont
      rw [if_pos rfl]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp (disch := omega) only [rootC, setCell, Nat.mul_zero, Nat.add_zero,
        if_pos, if_neg, ↓reduceIte]
      · exact tn hq
      all_goals rfl
    · have hu : (real_AC kl kh mm size j).cused = false := by
        unfold real_AC; rw [setAt_ne _ _ hj0]; rfl
      have h0 := hC j hj
      unfold MatchCont at h0 ⊢
      rw [hun j] at h0
      rw [hu]
      simp only [Bool.false_eq_true, if_false] at h0 ⊢
      rw [hb2 _ (by omega), hf1 _ (by omega)]; exact h0
  · simp [Locals.set, hlk5, σ4, σ2, hlk1]
  · have hk' : ¬ k ≤ 3 * maxpage ∧ (k < cb ∨ cb + 5 ≤ k) := by
      constructor
      · exact fun h => hk (Or.inl h)
      · by_cases h : k < cb
        · exact Or.inl h
        · exact Or.inr (by
            have : ¬ (cb ≤ k ∧ k < cb + 5) := fun h' => hk (Or.inr h')
            omega)
    rw [hb2 k hk'.2, hf1 k hk'.1]

end MContainer
