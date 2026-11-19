import CertiKOS.MPTCommon
import CertiKOS.MContainerInitC

/-!
# mCertiKOS `idpde_init`: the identity page table at boot, ported

`idpde_init` runs `container_init` and then fills the identity page table:
1024 x 1024 entries, entry `(i, j)` mapping to itself, with the "common"
kernel permission for the low and high parts of the address space and the
plain kernel permission in between.

Ported from `clib/CalRealIDPDE.v`: `Calculate_idpte_at_i`, `Calculate_idpte`,
`Calculate_idpde`, `real_idpde`.

Ported from `objects/ObjVMMFun.v`: `idpde_init_spec`.

Ported from `mm/MPTIntroCSource.v`: the C code of `idpde_init`.

* `idpde_init_triple`: **the C code refines `idpde_init_spec`.** The proof
  goes through the specifications of `container_init` and `set_IDPTE`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MPTInit

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MALInit MContainer MPTIntro MPTOp MPTCommon

abbrev IDPDE := Nat → Nat → IDPTEInfo

/-! ## The calculated identity table (`CalRealIDPDE.v`) -/

def Calculate_idpte_at_i (i x : Nat) (idp : IDPDE) : IDPDE :=
  if x < 256 then setAt idp x (setAt (idp x) i (.IDPTEValid (.PTK true)))
  else if 960 ≤ x then setAt idp x (setAt (idp x) i (.IDPTEValid (.PTK true)))
  else setAt idp x (setAt (idp x) i (.IDPTEValid (.PTK false)))

def Calculate_idpte : Nat → Nat → IDPDE → IDPDE
  | 0, x, idp => Calculate_idpte_at_i 0 x idp
  | k + 1, x, idp => Calculate_idpte_at_i (k + 1) x (Calculate_idpte k x idp)

def Calculate_idpde : Nat → IDPDE → IDPDE
  | 0, idp => Calculate_idpte 1023 0 idp
  | k + 1, idp => Calculate_idpte 1023 (k + 1) (Calculate_idpde k idp)

/-- `real_idpde`. -/
def real_idpde (idp : IDPDE) : IDPDE := Calculate_idpde 1023 idp

/-- **`idpde_init_spec`** (`ObjVMMFun.v`). -/
def idpde_init_spec (kl kh : Nat) (mm : MMTable) (size : Nat) (d : PTData) : Option PTData :=
  if d.init = false ∧ d.pg = false ∧ d.ipt = true then
    some { d with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, AC := real_AC kl kh mm size,
                  init := true, idpde := real_idpde d.idpde }
  else none

/-! ## The table part-way through the loops -/

/-- Row `x` with its first `j` entries written. -/
def rowP (x : Nat) : Nat → IDPDE → IDPDE
  | 0, idp => idp
  | j + 1, idp => Calculate_idpte_at_i j x (rowP x j idp)

theorem rowP_calc (x : Nat) (idp : IDPDE) : ∀ k, Calculate_idpte k x idp = rowP x (k + 1) idp
  | 0 => rfl
  | k + 1 => by
    show Calculate_idpte_at_i (k + 1) x (Calculate_idpte k x idp) = _
    rw [rowP_calc x idp k]; rfl

/-- The first `i` rows written. -/
def allP : Nat → IDPDE → IDPDE
  | 0, idp => idp
  | i + 1, idp => rowP i 1024 (allP i idp)

theorem allP_calc (idp : IDPDE) : ∀ k, Calculate_idpde k idp = allP (k + 1) idp
  | 0 => rowP_calc 0 idp 1023
  | k + 1 => by
    show Calculate_idpte 1023 (k + 1) (Calculate_idpde k idp) = _
    rw [allP_calc idp k, rowP_calc]; rfl

theorem allP_real (idp : IDPDE) : real_idpde idp = allP 1024 idp := allP_calc idp 1023

/-- The permission `idpde_init` gives row `x`: `PT_PERM_PTKT` or `PT_PERM_PTKF`. -/
def permZ (x : Nat) : Nat := if x < 256 then 259 else if 960 ≤ x then 259 else 3

def Di (d : PTData) (I : IDPDE) : PTData := { d with idpde := I }

/-- One call of `set_IDPTE` in the loop. -/
theorem id_step {d : PTData} (hpg : d.pg = false) (hinit : d.init = true) (hipt : d.ipt = true) {x j : Nat}
    (hx : x < 1024) (hj : j < 1024) (I : IDPDE) :
    setIDPTE_spec x j (permZ x) (Di d I) = some (Di d (Calculate_idpte_at_i j x I)) := by
  unfold setIDPTE_spec
  rw [if_pos ⟨hpg, hinit, hipt, hx, hj⟩]
  unfold permZ Calculate_idpte_at_i
  by_cases h1 : x < 256
  · rw [if_pos h1, if_pos h1]; rfl
  · by_cases h2 : 960 ≤ x
    · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2]; rfl
    · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2]; rfl

/-! ## The C code (`MPTIntroCSource.v`) -/

/-- `for (j = 0; j < 1024; j++) set_IDPTE(i, j, perm);` (the loop only) -/
def idInner (ib : Nat) : Stmt APrim :=
  .while (.bin .ltu (.var "j") (.const 1024))
    (.seq (.assign "vadr" (.var "j")) (.seq (setIDPTES ib) (.assign "j" (.bin .add (.var "j") (.const 1)))))

/-- `if (i < 256) perm = PT_PERM_PTKT; else if (i >= 960) perm = PT_PERM_PTKT; else perm = PT_PERM_PTKF;` -/
def permS : Stmt APrim :=
  .ite (.bin .ltu (.var "i") (.const 256)) (.assign "perm" (.const 259))
    (.ite (.bin .eq (.bin .ltu (.var "i") (.const 960)) (.const 0)) (.assign "perm" (.const 259))
      (.assign "perm" (.const 3)))

def idOuterBody (ib : Nat) : Stmt APrim :=
  .seq permS (.seq (.assign "j" (.const 0)) (.seq (idInner ib) (.assign "i" (.bin .add (.var "i") (.const 1)))))

def idOuter (ib : Nat) : Stmt APrim := .while (.bin .ltu (.var "i") (.const 1024)) (idOuterBody ib)

/-- The body of **`idpde_init`**:
`container_init(mbi_adr); for (i = 0; i < 1024; i++) { ... }` -/
def idpdeInitCS (mmb maxpage kl kh cb ib : Nat) : Stmt APrim :=
  .seq (ctInitCS mmb maxpage kl kh cb) (.seq (.assign "i" (.const 0)) (idOuter ib))

section Proofs
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- **The inner loop** writes row `i`, through `set_IDPTE`'s specification. -/
theorem idInner_run (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    {d : PTData} (hpg : d.pg = false) (hinit : d.init = true) (hipt : d.ipt = true) {x : Nat}
    (hx : x < 1024) (I : IDPDE) (σ : Locals) (l : RLog) (b : Region) (hlk : (σ "lk").toNat = i0)
    (hcs : CS1 c i0 l b) (hM : MatchAll maxpage num_id cb num_proc pb ib fb ida (Di d I) b)
    (hi : σ "i" = BitVec.ofNat 32 x) (hpe : σ "perm" = BitVec.ofNat 32 (permZ x)) (hj : σ "j" = 0) :
    ∃ σ' l' b', Runs (rprimsA εR c) (idInner ib) σ l σ' l' ∧ CS1 c i0 l' b' ∧
      MatchAll maxpage num_id cb num_proc pb ib fb ida (Di d (rowP x 1024 I)) b' ∧ σ' "lk" = σ "lk" ∧
      σ' "i" = σ "i" ∧ ∀ k, k < pb → b' k = b k := by
  let Inv : Locals → RLog → Prop := fun τ l' => τ "lk" = σ "lk" ∧ τ "i" = BitVec.ofNat 32 x ∧
    τ "perm" = BitVec.ofNat 32 (permZ x) ∧ ∃ m b', m ≤ 1024 ∧ τ "j" = BitVec.ofNat 32 m ∧ CS1 c i0 l' b' ∧
      MatchAll maxpage num_id cb num_proc pb ib fb ida (Di d (rowP x m I)) b' ∧ ∀ k, k < pb → b' k = b k
  have hbody : ∀ τ l', Inv τ l' → ¬ (Expr.bin .ltu (.var "j") (.const 1024)).eval τ = 0 →
      ∃ τ' l'', Runs (rprimsA εR c) (.seq (.assign "vadr" (.var "j")) (.seq (setIDPTES ib)
          (.assign "j" (.bin .add (.var "j") (.const 1))))) τ l' τ' l'' ∧ Inv τ' l'' ∧
        1024 - (τ' "j").toNat < 1024 - (τ "j").toNat := by
    rintro τ l' ⟨hlkτ, hiτ, hpeτ, m, b', hm, hjτ, hcs', hM', hfr⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "j") (eb := .const 1024) (b := 1024) hjτ rfl (by omega) (by decide)] at hg
    have hmlt : m < 1024 := by
      by_cases h : m < 1024
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    let τ1 := τ.set "vadr" (BitVec.ofNat 32 m)
    have h1 : Runs (rprimsA εR c) (.assign "vadr" (.var "j")) τ l' τ1 l' := asg_run _ _ hjτ
    obtain ⟨τ2, l2, b2, d2, hr2, hcs2, hM2, hlk2, hf2, hq⟩ :=
      setIDPTE_triple εR c i0 hL x m (permZ x) τ1 l' b' (Di d (rowP x m I))
        (by simp [τ1, Locals.set, hlkτ, hlk]) hcs' hM'
        ⟨by simp [τ1, Locals.set, hiτ], by simp [τ1], by simp [τ1, Locals.set, hpeτ], _,
          id_step hpg hinit hipt hx hmlt _⟩
    rw [id_step hpg hinit hipt hx hmlt] at hq
    simp only [Option.some.injEq] at hq
    rw [← hq] at hM2
    have fr2 : ∀ z : Ident, z ≠ "_" → τ2 z = τ1 z := fun z h1 =>
      hr2.frame (by simp [frS, setIDPTES, Ne.symm h1])
    have h3 := asg_run (εR := εR) (c := c) (σ := τ2) (l := l2) "j" (.bin .add (.var "j") (.const 1))
      (inc_eval (m := m) (by rw [fr2 _ (by decide)]; simp [τ1, Locals.set, hjτ]))
    refine ⟨_, l2, Runs.seq h1 (Runs.seq hr2 h3), ⟨?_, ?_, ?_, m + 1, b2, hmlt, by simp, hcs2, hM2,
      fun k hk => ?_⟩, ?_⟩
    · simp [Locals.set, hlk2, τ1, hlkτ]
    · simp [Locals.set, fr2, τ1, hiτ]
    · simp [Locals.set, fr2, τ1, hpeτ]
    · rw [hf2 k (by omega), hfr k hk]
    · rw [Locals.set_same, hjτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', l', hr, ⟨hlk', hi', hpe', m, b', hm, hj', hcs', hM', hfr⟩, h0⟩ :=
    while_inv (εR := εR) (c := c) Inv (fun τ => 1024 - (τ "j").toNat) hbody 1024 σ l (by omega)
      ⟨rfl, hi, hpe, 0, b, by omega, hj, hcs, hM, fun _ _ => rfl⟩
  rw [ltu_eval (σ := σ') (ea := .var "j") (eb := .const 1024) (b := 1024) hj' rfl (by omega) (by decide)] at h0
  have hme : m = 1024 := by
    by_cases h : m < 1024
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  exact ⟨σ', l', b', hr, hcs', hM', hlk', hi'.trans hi.symm, hfr⟩

theorem permS_run (εR : REnv) (c : CPU) {σ : Locals} {l : RLog} {x : Nat} (hx : x < 1024)
    (hi : σ "i" = BitVec.ofNat 32 x) :
    Runs (rprimsA εR c) permS σ l (σ.set "perm" (BitVec.ofNat 32 (permZ x))) l := by
  have e1 := ltu_eval (σ := σ) (ea := .var "i") (eb := .const 256) (b := 256) hi rfl (by omega) (by decide)
  have e2 : (Expr.bin .eq (.bin .ltu (.var "i") (.const 960)) (.const 0)).eval σ =
      if (Expr.bin .ltu (.var "i") (.const 960)).eval σ = 0 then 1 else 0 := rfl
  rw [ltu_eval (σ := σ) (ea := .var "i") (eb := .const 960) (b := 960) hi rfl (by omega) (by decide)] at e2
  by_cases h1 : x < 256
  · have hp : permZ x = 259 := by unfold permZ; rw [if_pos h1]
    rw [hp]
    exact Runs.ite_true (by rw [e1, if_pos h1]; decide) (Runs.assign _ _)
  · by_cases h2 : 960 ≤ x
    · have hp : permZ x = 259 := by unfold permZ; rw [if_neg h1, if_pos h2]
      rw [hp]
      exact Runs.ite_false (by rw [e1, if_neg h1]) (Runs.ite_true
        (by rw [e2, if_neg (show ¬ x < 960 by omega), if_pos rfl]; decide) (Runs.assign _ _))
    · have hp : permZ x = 3 := by unfold permZ; rw [if_neg h1, if_neg h2]
      rw [hp]
      exact Runs.ite_false (by rw [e1, if_neg h1]) (Runs.ite_false
        (by rw [e2, if_pos (show x < 960 by omega), if_neg (by decide)]) (Runs.assign _ _))

/-- **The outer loop** writes all 1024 rows. -/
theorem idOuter_run (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    {d : PTData} (hpg : d.pg = false) (hinit : d.init = true) (hipt : d.ipt = true) (I : IDPDE)
    (σ : Locals) (l : RLog) (b : Region) (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b)
    (hM : MatchAll maxpage num_id cb num_proc pb ib fb ida (Di d I) b) (hi : σ "i" = 0) :
    ∃ σ' l' b', Runs (rprimsA εR c) (idOuter ib) σ l σ' l' ∧ CS1 c i0 l' b' ∧
      MatchAll maxpage num_id cb num_proc pb ib fb ida (Di d (allP 1024 I)) b' ∧ σ' "lk" = σ "lk" ∧
      ∀ k, k < pb → b' k = b k := by
  let Inv : Locals → RLog → Prop := fun τ l' => τ "lk" = σ "lk" ∧ ∃ x b', x ≤ 1024 ∧
    τ "i" = BitVec.ofNat 32 x ∧ CS1 c i0 l' b' ∧
    MatchAll maxpage num_id cb num_proc pb ib fb ida (Di d (allP x I)) b' ∧ ∀ k, k < pb → b' k = b k
  have hbody : ∀ τ l', Inv τ l' → ¬ (Expr.bin .ltu (.var "i") (.const 1024)).eval τ = 0 →
      ∃ τ' l'', Runs (rprimsA εR c) (idOuterBody ib) τ l' τ' l'' ∧ Inv τ' l'' ∧
        1024 - (τ' "i").toNat < 1024 - (τ "i").toNat := by
    rintro τ l' ⟨hlkτ, x, b', hx, hiτ, hcs', hM', hfr⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .const 1024) (b := 1024) hiτ rfl (by omega) (by decide)] at hg
    have hxlt : x < 1024 := by
      by_cases h : x < 1024
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    let τ2 := (τ.set "perm" (BitVec.ofNat 32 (permZ x))).set "j" 0
    have h12 : Runs (rprimsA εR c) (.seq permS (.assign "j" (.const 0))) τ l' τ2 l' :=
      Runs.seq (permS_run εR c hxlt hiτ) (Runs.assign _ _)
    obtain ⟨τ3, l3, b3, hr3, hcs3, hM3, hlk3, hi3, hf3⟩ := idInner_run εR c i0 hL hpg hinit hipt hxlt
      (allP x I) τ2 l' b' (by simp [τ2, Locals.set, hlkτ, hlk]) hcs' hM' (by simp [τ2, Locals.set, hiτ])
      (by simp [τ2, Locals.set]) (by simp [τ2])
    have hiτ3 : τ3 "i" = BitVec.ofNat 32 x := by rw [hi3]; simp [τ2, Locals.set, hiτ]
    have h4 := asg_run (εR := εR) (c := c) (σ := τ3) (l := l3) "i" (.bin .add (.var "i") (.const 1))
      (inc_eval (m := x) hiτ3)
    have hrun : Runs (rprimsA εR c) (idOuterBody ib) τ l' _ l3 :=
      Runs.seq (permS_run εR c hxlt hiτ) (Runs.seq (Runs.assign _ _) (Runs.seq hr3 h4))
    refine ⟨_, l3, hrun, ⟨?_, x + 1, b3, hxlt, by simp, hcs3, hM3, fun k hk => ?_⟩, ?_⟩
    · simp [Locals.set, hlk3, τ2, hlkτ]
    · rw [hf3 k hk, hfr k hk]
    · rw [Locals.set_same, hiτ, tn (show x + 1 < 2 ^ 32 by omega), tn (show x < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', l', hr, ⟨hlk', x, b', hx, hi', hcs', hM', hfr⟩, h0⟩ :=
    while_inv (εR := εR) (c := c) Inv (fun τ => 1024 - (τ "i").toNat) hbody 1024 σ l (by omega)
      ⟨rfl, 0, b, by omega, hi, hcs, hM, fun _ _ => rfl⟩
  rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .const 1024) (b := 1024) hi' rfl (by omega) (by decide)] at h0
  have hme : x = 1024 := by
    by_cases h : x < 1024
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme
  exact ⟨σ', l', b', hr, hcs', hM', hlk', hfr⟩

/-- **`idpde_init` refines `idpde_init_spec`.** The memory map sits between
the containers and the page-table pool. -/
theorem idpde_init_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    {mmb size kl kh : Nat} {mm : MMTable} (hcm : cb + 5 * num_id ≤ mmb) (hmb : mmb + 1 + 3 * size ≤ pb)
    (hnum : 0 < num_id) (hmp : 2 ^ 20 ≤ maxpage) (hkl : 0 < kl) (hkl' : kl < 2 ^ 32) (hkh : kh < 2 ^ 20)
    (hsz : 0 < size) (hv : MM_valid mm size) (hc : MM_correct mm size) :
    Triple εR c i0
      (fun (d : PTData) b => MatchAll maxpage num_id cb num_proc pb ib fb ida d b ∧ MatchMMap mmb mm size b)
      (fun _ => True)
      (fun _ d => d.init = false ∧ d.pg = false ∧ d.ipt = true ∧ ∀ j, (d.AC j).cused = false)
      (idpdeInitCS mmb maxpage kl kh cb ib)
      (fun _ d _ d' => idpde_init_spec kl kh mm size d = some d') := by
  rintro σ l b d hlk hcs ⟨hM, hMM⟩ ⟨hin, hpg, hipt, hun⟩
  have := hL.hcb; have := hL.hpb; have := hL.hib; have := hL.hfb; have := hL.hend
  obtain ⟨σ1, l1, b1, r1, hr1, hcs1, ⟨hmm1, hMM1⟩, hlk1, hf1, hq1⟩ :=
    container_init_triple εR c i0 (by omega) hL.hcb hcm hnum hmp hkl hkl' hkh hsz hv hc σ l b d.toRData
      hlk hcs ⟨hM.mm, hMM⟩ ⟨hin, hun⟩
  have hr1e : r1 = { d.toRData with
      AT := real_AT kl kh mm size d.AT
      nps := real_nps mm size
      init := true
      AC := real_AC kl kh mm size } := by
    have h := hq1
    unfold container_init_spec at h
    rw [if_pos hin] at h
    exact (Option.some.inj h).symm
  let dm : PTData := { d with toRData := r1 }
  have hMm : MatchAll maxpage num_id cb num_proc pb ib fb ida (Di dm d.idpde) b1 :=
    ⟨hmm1, matchpt_transfer hL hM.pt (fun k hk => hf1 k (by omega)) rfl rfl rfl
      (fun pi n i _ => by show r1.pperm pi = d.pperm pi; rw [hr1e])⟩
  let σ2 := σ1.set "i" 0
  have h2 : Runs (rprimsA εR c) (.assign "i" (.const 0)) σ1 l1 σ2 l1 := Runs.assign _ _
  obtain ⟨σ3, l3, b3, hr3, hcs3, hM3, hlk3, hf3⟩ := idOuter_run εR c i0 hL (d := dm) hpg
    (by show r1.init = true; rw [hr1e]) hipt d.idpde σ2 l1 b1
    (by simp [σ2, Locals.set, hlk1, hlk]) hcs1 hMm (by simp [σ2])
  refine ⟨σ3, l3, b3, Di dm (allP 1024 d.idpde), Runs.seq hr1 (Runs.seq h2 hr3), hcs3,
    ⟨hM3, matchMM_of_eq hMM1 (fun k hk hk2 => hf3 k (by omega))⟩, ?_, fun _ hk => absurd trivial hk, ?_⟩
  · rw [hlk3]; simp [σ2, Locals.set, hlk1]
  · show idpde_init_spec kl kh mm size d = some _
    unfold idpde_init_spec
    rw [if_pos ⟨hin, hpg, hipt⟩, allP_real]
    simp only [Di, dm, hr1e]

end Proofs

end MPTInit
