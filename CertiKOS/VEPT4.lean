import CertiKOS.VEPT

/-!
# The EPT's upper tables in memory, ported from the Coq version

Transcribed from `coq/EPT4.v`. `VEPT` keeps the four-level tree in the
abstract state and the leaf entries in memory; this file adds the three upper
tables of mCertiKOS's `struct eptStruct` (`pml4`, `pdpt`, `pdt[4]`) at `ub`.

* `MatchUp`: the upper tables hold what the tree says (for the part a 4 GB
  guest uses): an entry that points to a table holds `ent` of its address, an
  entry with no table holds 0.
* `up_store`: **a leaf write keeps `MatchUp`** (what every `VEPT` function
  that changes the EPT does). `SameShape`, `matchUp_shape`: the same for any
  two trees with the same tables; the top state's relation (`TTop.MatchH`)
  includes `MatchUp`, and every step of the VMX layer keeps the shape.
* `setEPML4_step`, `setEPDPTE_step`, `setEPDTE_step`: **each adds a level and
  refines its specification** (`ObjEPT.v`).
* `fill_run`: a loop that writes `f i` at `base + i`.
* `initUp_run`: **`ept_init`'s upper tables**: afterwards they match
  `real_ept`.

What differs: as in `coq/EPT4.v`, `ent a = 4 a + 7` (the byte address and the
read, write and execute bits), and `setEPML4` clears the four `pdpt` entries
a 4 GB guest uses.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace VEPT

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MPTIntro
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

def ent (a : Nat) : Val := BitVec.ofNat 32 (4 * a + 7)

theorem ent_nz (a : Nat) : ent a ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  simp [ent] at this
  omega

/-! ## The shape of the tree -/

def v4 (e : EPT) : Bool := match e 0 with | .EPML4EValid _ => true | _ => false
def vP (e : EPT) (j : Nat) : Bool :=
  match e 0 with
  | .EPML4EValid a => match a j with | .EPDPTEValid _ => true | _ => false
  | _ => false
def vD (e : EPT) (j k : Nat) : Bool :=
  match e 0 with
  | .EPML4EValid a => match a j with
    | .EPDPTEValid b => match b k with | .EPDTEValid _ => true | _ => false
    | _ => false
  | _ => false

theorem shape_store {e e' : EPT} {g : Nat} {v : Val} (h : ept_store e g v = some e') :
    v4 e' = v4 e ∧ (∀ j, vP e' j = vP e j) ∧ (∀ j k, vD e' j k = vD e j k) := by
  unfold ept_store at h
  split at h
  · rename_i a ea
    split at h
    · rename_i bb eb'
      split at h
      · rename_i cc ec
        simp only [Option.some.injEq] at h; subst h
        refine ⟨?_, fun j => ?_, fun j k => ?_⟩
        · unfold v4; by_cases e0 : (0 : Nat) = PML4' g
          · rw [e0, setAt_eq, ea]
          · rw [setAt_ne _ _ e0]
        · unfold vP; by_cases e0 : (0 : Nat) = PML4' g
          · rw [e0, setAt_eq, ea]; simp only
            by_cases ej : j = PDPT' g
            · rw [ej, setAt_eq, eb']
            · rw [setAt_ne _ _ ej]
          · rw [setAt_ne _ _ e0]
        · unfold vD; by_cases e0 : (0 : Nat) = PML4' g
          · rw [e0, setAt_eq, ea]; simp only
            by_cases ej : j = PDPT' g
            · rw [ej, setAt_eq, eb']; simp only
              by_cases ek : k = PDIR' g
              · rw [ek, setAt_eq, ec]
              · rw [setAt_ne _ _ ek]
            · rw [setAt_ne _ _ ej]
          · rw [setAt_ne _ _ e0]
      · cases h
    · cases h
  · cases h

def emptyP : EPDPT := fun _ => .EPDPTEUndef
def emptyD : EPDT := fun _ => .EPDTEUndef
def emptyT : EPTAB := fun _ => .EPTEUndef

/-! ## Specifications (`ObjEPT.v`) -/

def setEPML4_spec (pml4 : Nat) (d : VData) : Option VData :=
  if flags d ∧ pml4 = 0 then some { d with ept := setAt d.ept 0 (.EPML4EValid emptyP) } else none

def setEPDPTE_spec (pml4 pdpt : Nat) (d : VData) : Option VData :=
  if flags d ∧ pml4 = 0 ∧ pdpt < 4 then
    match d.ept 0 with
    | .EPML4EValid a => some { d with ept := setAt d.ept 0 (.EPML4EValid (setAt a pdpt (.EPDPTEValid emptyD))) }
    | .EPML4EUndef => none
  else none

def setEPDTE_spec (pml4 pdpt pdir : Nat) (d : VData) : Option VData :=
  if flags d ∧ pml4 = 0 ∧ pdpt < 4 ∧ pdir < 512 then
    match d.ept 0 with
    | .EPML4EValid a =>
      match a pdpt with
      | .EPDPTEValid b =>
        some { d with ept := setAt d.ept 0 (.EPML4EValid (setAt a pdpt (.EPDPTEValid (setAt b pdir (.EPDTEValid emptyT))))) }
      | .EPDPTEUndef => none
    | .EPML4EUndef => none
  else none

/-! ## The tables in the region -/

def P2 (ub j : Nat) : Nat := ub + 1024 + 512 * j
def leafT (eb j k : Nat) : Nat := eb + 512 * (512 * j + k)

def MatchUp (ub eb : Nat) (e : EPT) (b : Region) : Prop :=
  b ub = (if v4 e then ent (ub + 512) else 0) ∧
  (v4 e = true → ∀ j, j < 4 → b (ub + 512 + j) = if vP e j then ent (P2 ub j) else 0) ∧
  ∀ j k, j < 4 → k < 512 → vP e j = true → b (P2 ub j + k) = if vD e j k then ent (leafT eb j k) else 0

def InUp (ub : Nat) (a : Nat) : Prop := ub ≤ a ∧ a < ub + 3072

theorem matchUp_frame {ub eb : Nat} {e : EPT} {b b' : Region} (h : MatchUp ub eb e b)
    (hf : ∀ a, InUp ub a → b' a = b a) : MatchUp ub eb e b' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hf ub ⟨by omega, by omega⟩]; exact h1, fun hv j hj => ?_, fun j k hj hk hv => ?_⟩
  · rw [hf _ ⟨by omega, by omega⟩]; exact h2 hv j hj
  · rw [hf _ ⟨by unfold P2; omega, by unfold P2; omega⟩]; exact h3 j k hj hk hv

/-- **A leaf write keeps the upper tables.** -/
theorem up_store {ub eb : Nat} {e e' : EPT} {g : Nat} {v : Val} {b b' : Region} (hs : ept_store e g v = some e')
    (hM : MatchUp ub eb e b) (hf : ∀ a, InUp ub a → b' a = b a) : MatchUp ub eb e' b' := by
  obtain ⟨s4, sP, sD⟩ := shape_store hs
  obtain ⟨h1, h2, h3⟩ := matchUp_frame hM hf
  refine ⟨by rw [s4]; exact h1, fun hv j hj => ?_, fun j k hj hk hv => ?_⟩
  · rw [sP]; exact h2 (by rw [← s4]; exact hv) j hj
  · rw [sD]; exact h3 j k hj hk (by rw [← sP]; exact hv)

/-- Two trees with the same tables (only leaves may differ). -/
def SameShape (e e' : EPT) : Prop := v4 e' = v4 e ∧ (∀ j, vP e' j = vP e j) ∧ ∀ j k, vD e' j k = vD e j k

theorem SameShape.refl (e : EPT) : SameShape e e := ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩

theorem SameShape.of_eq {e e' : EPT} (h : e' = e) : SameShape e e' := by subst h; exact SameShape.refl _

theorem SameShape.trans {e1 e2 e3 : EPT} (h1 : SameShape e1 e2) (h2 : SameShape e2 e3) : SameShape e1 e3 :=
  ⟨h2.1.trans h1.1, fun j => (h2.2.1 j).trans (h1.2.1 j), fun j k => (h2.2.2 j k).trans (h1.2.2 j k)⟩

theorem SameShape.store {e e' : EPT} {g : Nat} {v : Val} (h : ept_store e g v = some e') : SameShape e e' :=
  shape_store h

/-- **The upper tables match a tree with the same tables**, if their cells
are kept. -/
theorem matchUp_shape {ub eb : Nat} {e e' : EPT} {b b' : Region} (hM : MatchUp ub eb e b) (hs : SameShape e e')
    (hf : ∀ a, InUp ub a → b' a = b a) : MatchUp ub eb e' b' := by
  obtain ⟨s4, sP, sD⟩ := hs
  obtain ⟨h1, h2, h3⟩ := matchUp_frame hM hf
  refine ⟨by rw [s4]; exact h1, fun hv j hj => ?_, fun j k hj hk hv => ?_⟩
  · rw [sP]; exact h2 (by rw [← s4]; exact hv) j hj
  · rw [sD]; exact h3 j k hj hk (by rw [← sP]; exact hv)

theorem leaf_emptyP (e : EPT) {g : Nat} (hg : g < NPG) : ept_leaf (setAt e 0 (.EPML4EValid emptyP)) g = none := by
  have : PML4' g = 0 := by unfold PML4' NPG at *; omega
  unfold ept_leaf; rw [this, setAt_eq]; rfl

/-! ## The code -/

section Code
variable {ub eb : Nat}
variable (hue : ub + 3072 ≤ eb) (heb : eb + NPG ≤ 2 ^ 32)
variable (εR : REnv) (c : CPU) (i0 : Nat)

/-- The relation for this file: the leaves and the upper tables. -/
def M4 (ub eb : Nat) (d : VData) (b : Region) : Prop := MatchE eb d b ∧ MatchUp ub eb d.ept b

def K (n : Nat) : Expr := .const (BitVec.ofNat 32 n)
def storeS (a : Nat) (v : Val) : Stmt APrim := .call "_" .push [lkE, K a, .const v]

/-- One store at a constant address, as a run. -/
theorem store_run {l : RLog} {b : Region} {σ : Locals} (hcs : CS1 c i0 l b) (hlk : (σ "lk").toNat = i0)
    {a : Nat} (ha : a < 2 ^ 32) (v : Val) :
    ∃ l', Runs (rprimsA εR c) (storeS a v) σ l (σ.set "_" 0) l' ∧ CS1 c i0 l' (setCell b a v) :=
  wr_run (εR := εR) hcs hlk (K a) (.const v) (tn ha) rfl

/-- `pml4[0] = &pdpt | 7; pdpt[0..3] = 0;` -/
def setEPML4S (ub : Nat) : Stmt APrim :=
  .seq (storeS ub (ent (ub + 512))) (.seq (storeS (ub + 512) 0) (.seq (storeS (ub + 513) 0)
    (.seq (storeS (ub + 514) 0) (storeS (ub + 515) 0))))

include hue heb

/-- **`setEPML4` refines `setEPML4_spec`.** -/
theorem setEPML4_step {σ : Locals} {d d' : VData} {pml4 : Nat} (hs : setEPML4_spec pml4 d = some d') :
    Step εR c i0 (M4 ub eb) (InUp ub) (setEPML4S ub) σ d (((((σ.set "_" 0).set "_" 0).set "_" 0).set "_" 0).set "_" 0)
      d' := by
  unfold setEPML4_spec at hs
  split at hs
  · simp only [Option.some.injEq] at hs; subst hs
    have := heb; unfold NPG at this
    refine ⟨by simp [Locals.set], fun l b hlk hcs hM => ?_⟩
    obtain ⟨l1, r1, c1⟩ := store_run εR c i0 (σ := σ) hcs hlk (a := ub) (by omega) (ent (ub + 512))
    obtain ⟨l2, r2, c2⟩ := store_run εR c i0 (σ := σ.set "_" 0) c1 (by simpa [Locals.set] using hlk)
      (a := ub + 512) (by omega) 0
    obtain ⟨l3, r3, c3⟩ := store_run εR c i0 (σ := (σ.set "_" 0).set "_" 0) c2 (by simpa [Locals.set] using hlk)
      (a := ub + 513) (by omega) 0
    obtain ⟨l4, r4, c4⟩ := store_run εR c i0 (σ := ((σ.set "_" 0).set "_" 0).set "_" 0) c3
      (by simpa [Locals.set] using hlk) (a := ub + 514) (by omega) 0
    obtain ⟨l5, r5, c5⟩ := store_run εR c i0 (σ := (((σ.set "_" 0).set "_" 0).set "_" 0).set "_" 0) c4
      (by simpa [Locals.set] using hlk) (a := ub + 515) (by omega) 0
    let b5 := setCell (setCell (setCell (setCell (setCell b ub (ent (ub + 512))) (ub + 512) 0) (ub + 513) 0)
      (ub + 514) 0) (ub + 515) 0
    have look : ∀ a, b5 a = if a = ub + 515 ∨ a = ub + 514 ∨ a = ub + 513 ∨ a = ub + 512 then 0
        else if a = ub then ent (ub + 512) else b a := by
      intro a; simp only [b5, setCell]
      by_cases h1 : a = ub + 515 <;> by_cases h2 : a = ub + 514 <;> by_cases h3 : a = ub + 513 <;>
        by_cases h4 : a = ub + 512 <;> by_cases h5 : a = ub <;> simp_all <;> omega
    refine ⟨l5, b5, Runs.seq r1 (Runs.seq r2 (Runs.seq r3 (Runs.seq r4 r5))), c5, ⟨fun g v hg hl => ?_, ?_, ?_, ?_⟩,
      fun k hk => ?_⟩
    · have hl' : ept_leaf (setAt d.ept 0 (.EPML4EValid emptyP)) g = some v := hl
      rw [leaf_emptyP _ hg] at hl'; cases hl'
    · show b5 ub = _
      rw [look]; simp [v4, setAt]
    · intro _ j hj
      rw [look, if_pos (by omega)]; simp [vP, setAt, emptyP]
    · intro j k hj hk hv
      simp [vP, setAt, emptyP] at hv
    · rw [look, if_neg (fun h => hk ⟨by omega, by omega⟩), if_neg (fun h => hk ⟨by omega, by omega⟩)]
  · cases hs


omit hue heb in
/-- A loop that writes `v` (which is `f i`) at `base + i`, for `i` up to `n`. -/
def fillS (base n : Nat) (v : Expr) : Stmt APrim :=
  .while (.bin .ltu (.var "i") (K n))
    (.seq (.call "_" .push [lkE, .bin .add (K base) (.var "i"), v]) (.assign "i" (.bin .add (.var "i") (.const 1))))

omit hue heb in
theorem fill_run (base n : Nat) (hbn : base + n < 2 ^ 32) (v : Expr) (f : Nat → Val)
    (hv : ∀ (σ : Locals) i, σ "i" = BitVec.ofNat 32 i → i < n → v.eval σ = f i) :
    ∀ (k : Nat) (σ : Locals) (l : RLog) (b : Region) (i : Nat), σ "i" = BitVec.ofNat 32 i → i + k = n →
      (σ "lk").toNat = i0 → CS1 c i0 l b →
      ∃ σ' l' b', Runs (rprimsA εR c) (fillS base n v) σ l σ' l' ∧ CS1 c i0 l' b' ∧ σ' "lk" = σ "lk" ∧
        (∀ j, i ≤ j → j < n → b' (base + j) = f j) ∧ (∀ a, (a < base + i ∨ base + n ≤ a) → b' a = b a)
  | 0, σ, l, b, i, hi, hk, hlk, hcs => by
    have g := ltu_eval (σ := σ) (ea := .var "i") (eb := K n) (a := i) (b := n) hi rfl (by omega) (by omega)
    rw [if_neg (by omega)] at g
    exact ⟨σ, l, b, Runs.while_false g, hcs, rfl, fun j h1 h2 => by omega, fun _ _ => rfl⟩
  | k + 1, σ, l, b, i, hi, hk, hlk, hcs => by
    have g := ltu_eval (σ := σ) (ea := .var "i") (eb := K n) (a := i) (b := n) hi rfl (by omega) (by omega)
    rw [if_pos (by omega)] at g
    obtain ⟨l1, r1, c1⟩ := wr_run (εR := εR) hcs hlk (.bin .add (K base) (.var "i")) v (n := base + i)
      (v := f i) (by show (BitVec.ofNat 32 base + σ "i").toNat = _
                     rw [hi, BitVec.toNat_add, tn (by omega), tn (by omega)]; omega) (hv σ i hi (by omega))
    have r2 := asg_run (εR := εR) (c := c) (σ := σ.set "_" 0) (l := l1) "i" (.bin .add (.var "i") (.const 1))
      (inc_eval (m := i) (by rw [Locals.set_other _ _ (by decide)]; exact hi))
    obtain ⟨σ', l', b', r3, c3, k3, f3, g3⟩ := fill_run base n hbn v f hv k ((σ.set "_" 0).set "i" (BitVec.ofNat 32 (i + 1)))
      l1 (setCell b (base + i) (f i)) (i + 1) (by simp) (by omega) (by simpa [Locals.set] using hlk) c1
    refine ⟨σ', l', b', Runs.while_true (by rw [g]; decide) (Runs.seq r1 r2) r3, c3, by rw [k3]; simp [Locals.set],
      fun j h1 h2 => ?_, fun a ha => ?_⟩
    · by_cases e : j = i
      · subst e; rw [g3 _ (Or.inl (by omega))]; exact sc_eq _ _ _
      · exact f3 j (by omega) h2
    · rw [g3 a (by omega), sc_ne _ _ (by omega)]

/-- `pdpt[pdpt] = &pdt[pdpt] | 7; for (i = 0; i < 512; i++) pdt[pdpt][i] = 0;` -/
def setEPDPTES (ub pdpt : Nat) : Stmt APrim :=
  .seq (storeS (ub + 512 + pdpt) (ent (P2 ub pdpt))) (.seq (.assign "i" (K 0)) (fillS (P2 ub pdpt) 512 (K 0)))

/-- **`setEPDPTE` refines `setEPDPTE_spec`.** -/
theorem setEPDPTE_run {σ : Locals} {d d' : VData} {pml4 pdpt : Nat} {l : RLog} {b : Region}
    (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) (hM : M4 ub eb d b) (hs : setEPDPTE_spec pml4 pdpt d = some d') :
    ∃ σ' l' b', Runs (rprimsA εR c) (setEPDPTES ub pdpt) σ l σ' l' ∧ CS1 c i0 l' b' ∧ M4 ub eb d' b' ∧
      (∀ a, ¬ InUp ub a → b' a = b a) := by
  unfold setEPDPTE_spec at hs
  split at hs
  · rename_i hc
    have hp := hc.2.2
    cases e0 : d.ept 0 with
    | EPML4EUndef => rw [e0] at hs; cases hs
    | EPML4EValid a =>
      rw [e0] at hs; simp only [Option.some.injEq] at hs; subst hs
      have := heb; unfold NPG at this
      obtain ⟨l1, r1, c1⟩ := store_run εR c i0 (σ := σ) hcs hlk (a := ub + 512 + pdpt) (by omega) (ent (P2 ub pdpt))
      obtain ⟨σ2, l2, b2, r2, c2, k2, f2, g2⟩ := fill_run εR c i0 (P2 ub pdpt) 512 (by unfold P2; omega) (K 0)
        (fun _ => 0) (fun _ _ _ _ => rfl) 512 ((σ.set "_" 0).set "i" 0) l1 _ 0 (by simp) (by omega)
        (by simpa [Locals.set] using hlk) c1
      obtain ⟨hE, U1, U2, U3⟩ := hM
      have V4 : v4 d.ept = true := by unfold v4; rw [e0]
      have fr : ∀ k, ¬ (P2 ub pdpt ≤ k ∧ k < P2 ub pdpt + 512) → k ≠ ub + 512 + pdpt → b2 k = b k := fun k h1 h2 => by
        rw [g2 k (by omega), sc_ne _ _ h2]
      refine ⟨σ2, l2, b2, Runs.seq r1 (Runs.seq (asg_run "i" (K 0) rfl) r2), c2,
        ⟨fun g v hg hl => ?_, ?_, ?_, ?_⟩, fun k hk => fr k (fun h => hk ⟨by unfold P2 at h; omega, by unfold P2 at h; omega⟩)
          (fun h => hk ⟨by omega, by omega⟩)⟩
      · have hl' : ept_leaf (setAt d.ept 0 (.EPML4EValid (setAt a pdpt (.EPDPTEValid emptyD)))) g = some v := hl
        have p0 : PML4' g = 0 := by unfold PML4' NPG at *; omega
        unfold ept_leaf at hl'; rw [p0, setAt_eq] at hl'; simp only at hl'
        by_cases ej : PDPT' g = pdpt
        · rw [ej, setAt_eq] at hl'; simp [emptyD] at hl'
        · rw [setAt_ne _ _ ej] at hl'
          rw [fr _ (fun h => by unfold P2 at h; omega) (by omega)]
          exact hE g v hg (by unfold ept_leaf; rw [p0, e0]; exact hl')
      · show b2 ub = _
        rw [fr _ (fun h => by unfold P2 at h; omega) (by omega), U1, V4]; simp [v4, setAt]
      · intro _ j hj
        by_cases ej : j = pdpt
        · subst ej; rw [g2 _ (Or.inl (by unfold P2; omega)), sc_eq]; simp [vP, setAt]
        · rw [fr _ (fun h => by unfold P2 at h; omega) (by omega), U2 V4 j hj]; simp [vP, setAt, e0, ej]
      · intro j k hj hk hv
        by_cases ej : j = pdpt
        · subst ej; rw [f2 k (by omega) hk]; simp [vD, setAt, emptyD]
        · have hv' : vP d.ept j = true := by simpa [vP, setAt, e0, ej] using hv
          rw [fr _ (fun h => by unfold P2 at *; omega) (by unfold P2; omega), U3 j k hj hk hv']
          simp [vD, setAt, e0, ej]
  · cases hs

/-- `pdt[pdpt][pdir] = &ptab[pdpt][pdir] | 7;` -/
def setEPDTES (ub eb pdpt pdir : Nat) : Stmt APrim := storeS (P2 ub pdpt + pdir) (ent (leafT eb pdpt pdir))

/-- **`setEPDTE` refines `setEPDTE_spec`.** -/
theorem setEPDTE_step {σ : Locals} {d d' : VData} {pml4 pdpt pdir : Nat} (hs : setEPDTE_spec pml4 pdpt pdir d = some d') :
    Step εR c i0 (M4 ub eb) (InUp ub) (setEPDTES ub eb pdpt pdir) σ d (σ.set "_" 0) d' := by
  unfold setEPDTE_spec at hs
  split at hs
  · rename_i hc
    obtain ⟨-, -, hp, hq⟩ := hc
    cases e0 : d.ept 0 with
    | EPML4EUndef => rw [e0] at hs; cases hs
    | EPML4EValid a =>
      rw [e0] at hs; simp only at hs
      cases ea : a pdpt with
      | EPDPTEUndef => rw [ea] at hs; cases hs
      | EPDPTEValid bb =>
        rw [ea] at hs; simp only [Option.some.injEq] at hs; subst hs
        have := heb; unfold NPG at this
        refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
        obtain ⟨l1, r1, c1⟩ := store_run εR c i0 (σ := σ) hcs hlk (a := P2 ub pdpt + pdir) (by unfold P2; omega)
          (ent (leafT eb pdpt pdir))
        obtain ⟨hE, U1, U2, U3⟩ := hM
        have V4 : v4 d.ept = true := by unfold v4; rw [e0]
        refine ⟨l1, _, r1, c1, ⟨fun g v hg hl => ?_, ?_, ?_, ?_⟩,
          fun k hk => sc_ne _ _ (fun h => hk ⟨by unfold P2 at h; omega, by unfold P2 at h; omega⟩)⟩
        · have hl' := hl
          change ept_leaf (setAt d.ept 0 (.EPML4EValid (setAt a pdpt (.EPDPTEValid (setAt bb pdir (.EPDTEValid emptyT))))))
            g = some v at hl'
          have p0 : PML4' g = 0 := by unfold PML4' NPG at *; omega
          unfold ept_leaf at hl'; rw [p0, setAt_eq] at hl'; simp only at hl'
          rw [sc_ne _ _ (by unfold P2; omega)]
          refine hE g v hg ?_
          unfold ept_leaf; rw [p0, e0]; simp only
          by_cases ej : PDPT' g = pdpt
          · rw [ej, setAt_eq] at hl'; rw [ej, ea]; simp only at hl' ⊢
            by_cases ek : PDIR' g = pdir
            · rw [ek, setAt_eq] at hl'; simp [emptyT] at hl'
            · rw [setAt_ne _ _ ek] at hl'; exact hl'
          · rw [setAt_ne _ _ ej] at hl'; exact hl'
        · show setCell b _ _ ub = _
          rw [sc_ne _ _ (by unfold P2; omega), U1, V4]; simp [v4, setAt]
        · intro _ j hj
          rw [sc_ne _ _ (by unfold P2; omega), U2 V4 j hj]
          by_cases ej : j = pdpt
          · subst ej; simp [vP, setAt, e0, ea]
          · simp [vP, setAt, e0, ej]
        · intro j k hj hk hv
          by_cases ej : j = pdpt
          · subst ej
            by_cases ek : k = pdir
            · subst ek; rw [sc_eq]; simp [vD, setAt]
            · rw [sc_ne _ _ (by unfold P2; omega)]
              have hv' : vP d.ept j = true := by simp [vP, e0, ea]
              rw [U3 j k hj hk hv']; simp [vD, setAt, e0, ea, ek]
          · rw [sc_ne _ _ (by unfold P2; omega)]
            have hv' : vP d.ept j = true := by simpa [vP, setAt, e0, ej] using hv
            rw [U3 j k hj hk hv']; simp [vD, setAt, e0, ej]
  · cases hs


/-- `ept_init`'s upper tables: `pml4[0]`, `pdpt[0..3]`, and the 2048 `pdt` entries. -/
def initUpS (ub eb : Nat) : Stmt APrim :=
  .seq (storeS ub (ent (ub + 512))) (.seq (storeS (ub + 512) (ent (P2 ub 0))) (.seq (storeS (ub + 513) (ent (P2 ub 1)))
  (.seq (storeS (ub + 514) (ent (P2 ub 2))) (.seq (storeS (ub + 515) (ent (P2 ub 3)))
  (.seq (.assign "i" (K 0)) (fillS (ub + 1024) 2048 (.bin .add (K (4 * eb + 7)) (.bin .mul (.var "i") (K 2048)))))))))

/-- **`ept_init`'s upper tables match `real_ept`.** -/
theorem initUp_run {σ : Locals} {l : RLog} {b : Region} (e : EPT) (hlk : (σ "lk").toNat = i0) (hcs : CS1 c i0 l b) :
    ∃ σ' l' b', Runs (rprimsA εR c) (initUpS ub eb) σ l σ' l' ∧ CS1 c i0 l' b' ∧ MatchUp ub eb (real_ept e) b' ∧
      (∀ a, ¬ InUp ub a → b' a = b a) := by
  have := heb; unfold NPG at this
  have L : ∀ (σ0 : Locals), (σ0 "lk").toNat = i0 → ((σ0.set "_" 0) "lk").toNat = i0 := fun σ0 h => by
    simpa [Locals.set] using h
  obtain ⟨l1, r1, c1⟩ := store_run εR c i0 (σ := σ) hcs hlk (a := ub) (by omega) (ent (ub + 512))
  obtain ⟨l2, r2, c2⟩ := store_run εR c i0 c1 (L _ hlk) (a := ub + 512) (by omega) (ent (P2 ub 0))
  obtain ⟨l3, r3, c3⟩ := store_run εR c i0 c2 (L _ (L _ hlk)) (a := ub + 513) (by omega) (ent (P2 ub 1))
  obtain ⟨l4, r4, c4⟩ := store_run εR c i0 c3 (L _ (L _ (L _ hlk))) (a := ub + 514) (by omega) (ent (P2 ub 2))
  obtain ⟨l5, r5, c5⟩ := store_run εR c i0 c4 (L _ (L _ (L _ (L _ hlk)))) (a := ub + 515) (by omega) (ent (P2 ub 3))
  let σ5 := ((((σ.set "_" 0).set "_" 0).set "_" 0).set "_" 0).set "_" 0
  obtain ⟨σ6, l6, b6, r6, c6, -, f6, g6⟩ := fill_run εR c i0 (ub + 1024) 2048 (by omega)
    (.bin .add (K (4 * eb + 7)) (.bin .mul (.var "i") (K 2048))) (fun i => ent (eb + 512 * i))
    (fun σ0 i hi _ => by
      show BitVec.ofNat 32 (4 * eb + 7) + σ0 "i" * BitVec.ofNat 32 2048 = _
      rw [hi, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]; unfold ent; congr 1; omega)
    2048 (σ5.set "i" 0) l5 _ 0 (by simp) (by omega) (by simpa [σ5, Locals.set] using hlk) c5
  let b5 := setCell (setCell (setCell (setCell (setCell b ub (ent (ub + 512))) (ub + 512) (ent (P2 ub 0)))
    (ub + 513) (ent (P2 ub 1))) (ub + 514) (ent (P2 ub 2))) (ub + 515) (ent (P2 ub 3))
  have g6' : ∀ a, (a < ub + 1024 ∨ ub + 1024 + 2048 ≤ a) → b6 a = b5 a := fun a h => g6 a (by omega)
  refine ⟨σ6, l6, b6, Runs.seq r1 (Runs.seq r2 (Runs.seq r3 (Runs.seq r4 (Runs.seq r5
    (Runs.seq (asg_run "i" (K 0) rfl) r6))))), c6, ⟨?_, ?_, ?_⟩, fun a ha => ?_⟩
  · rw [g6' _ (Or.inl (by omega))]
    simp only [b5, setCell]; simp [v4, real_ept, setAt]
  · intro _ j hj
    rw [g6' _ (Or.inl (by omega))]
    have hvp : vP (real_ept e) j = true := by simp [vP, real_ept, setAt, hj]
    rw [hvp]; simp only [if_true]
    simp only [b5, setCell]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> simp
  · intro j k hj hk _
    have hvd : vD (real_ept e) j k = true := by simp [vD, real_ept, setAt, hj, hk]
    rw [hvd]; simp only [if_true]
    have e1 : P2 ub j + k = ub + 1024 + (512 * j + k) := by unfold P2; omega
    rw [e1, f6 (512 * j + k) (by omega) (by omega)]
    rfl
  · rw [g6' a (by unfold InUp at ha; omega)]
    simp only [b5, setCell]
    have : a ≠ ub ∧ a ≠ ub + 512 ∧ a ≠ ub + 513 ∧ a ≠ ub + 514 ∧ a ≠ ub + 515 := by
      unfold InUp at ha; omega
    simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]

end Code

end VEPT
