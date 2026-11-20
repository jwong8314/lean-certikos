import CertiKOS.Layer

/-!
# Steps: running a layer's code on its abstract state

A `Triple` hides the log and the region behind the abstract data, but its
pre- and postcondition are predicates, so chaining several calls means writing
every intermediate predicate. A `Step` is the same statement for one starting
point:

* `Step εR c i M F s σ d σ' d'`: inside a critical section on lock `i`, from
  locals `σ` and any region matching `d`, the code `s` runs to completion with
  locals `σ'`, the region then matches `d'`, and only cells in `F` changed.

Steps compose like an interpreter run on `(σ, d)`:

* `Step.seq`, `Step.assign`, `Step.skip`, `Step.ite_true`, `Step.ite_false`,
  `Step.while_true`, `Step.while_false`.
* `Step.while_inv`: a loop with an invariant on `(σ, d)` and a measure.
* `Step.widen`: a larger footprint.
* `Step.triple`: a step from every state satisfying `P`, landing in `Q`, is a
  `Triple`.
* `Step.lift`: frame, as `Triple.lift`.

A layer states one step lemma per primitive of the layer below (what the
primitive's specification does to `d`), and the code of the layer's own
functions is then run through these lemmas, never through the region.
-/

namespace Layer

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding)
open LockRegionCPU KernFrame

/-- From locals `σ` and data `d`, the code `s` ends with locals `σ'` and data
`d'`, writing only inside `F`. -/
def Step (εR : REnv) (c : CPU) (i : Nat) {D : Type} (M : D → Region → Prop) (F : Nat → Prop)
    (s : Stmt APrim) (σ : Locals) (d : D) (σ' : Locals) (d' : D) : Prop :=
  σ' "lk" = σ "lk" ∧ ∀ (l : RLog) (b : Region), (σ "lk").toNat = i → CS1 c i l b → M d b →
    ∃ (l' : RLog) (b' : Region), Runs (rprimsA εR c) s σ l σ' l' ∧ CS1 c i l' b' ∧ M d' b' ∧
      ∀ k, ¬ F k → b' k = b k

section Rules
variable {εR : REnv} {c : CPU} {i : Nat} {D : Type} {M : D → Region → Prop} {F : Nat → Prop}

theorem Step.skip {σ : Locals} {d : D} : Step εR c i M F .skip σ d σ d :=
  ⟨rfl, fun l b _ hcs hM => ⟨l, b, Runs.skip, hcs, hM, fun _ _ => rfl⟩⟩

theorem Step.assign {σ : Locals} {d : D} (x : Ident) (hx : x ≠ "lk") (e : Expr) :
    Step εR c i M F (.assign x e) σ d (σ.set x (e.eval σ)) d :=
  ⟨Locals.set_other _ _ (Ne.symm hx), fun l b _ hcs hM => ⟨l, b, Runs.assign x e, hcs, hM, fun _ _ => rfl⟩⟩

/-- An assignment whose value is known. -/
theorem Step.assign' {σ : Locals} {d : D} (x : Ident) (hx : x ≠ "lk") (e : Expr) {v : Val}
    (hv : e.eval σ = v) : Step εR c i M F (.assign x e) σ d (σ.set x v) d := by
  subst hv; exact Step.assign x hx e

theorem Step.seq {s1 s2 : Stmt APrim} {σ σ1 σ2 : Locals} {d d1 d2 : D}
    (h1 : Step εR c i M F s1 σ d σ1 d1) (h2 : Step εR c i M F s2 σ1 d1 σ2 d2) :
    Step εR c i M F (.seq s1 s2) σ d σ2 d2 := by
  refine ⟨h2.1.trans h1.1, fun l b hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h1.2 l b hlk hcs hM
  obtain ⟨l2, b2, r2, c2, m2, f2⟩ := h2.2 l1 b1 (by rw [h1.1]; exact hlk) c1 m1
  exact ⟨l2, b2, Runs.seq r1 r2, c2, m2, fun k hk => (f2 k hk).trans (f1 k hk)⟩

theorem Step.ite_true {e : Expr} {a b : Stmt APrim} {σ σ' : Locals} {d d' : D} (hne : ¬ e.eval σ = 0)
    (h : Step εR c i M F a σ d σ' d') : Step εR c i M F (.ite e a b) σ d σ' d' := by
  refine ⟨h.1, fun l r hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h.2 l r hlk hcs hM
  exact ⟨l1, b1, Runs.ite_true hne r1, c1, m1, f1⟩

theorem Step.ite_false {e : Expr} {a b : Stmt APrim} {σ σ' : Locals} {d d' : D} (h0 : e.eval σ = 0)
    (h : Step εR c i M F b σ d σ' d') : Step εR c i M F (.ite e a b) σ d σ' d' := by
  refine ⟨h.1, fun l r hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h.2 l r hlk hcs hM
  exact ⟨l1, b1, Runs.ite_false h0 r1, c1, m1, f1⟩

theorem Step.while_false {e : Expr} {body : Stmt APrim} {σ : Locals} {d : D} (h0 : e.eval σ = 0) :
    Step εR c i M F (.while e body) σ d σ d :=
  ⟨rfl, fun l b _ hcs hM => ⟨l, b, Runs.while_false h0, hcs, hM, fun _ _ => rfl⟩⟩

theorem Step.while_true {e : Expr} {body : Stmt APrim} {σ σ1 σ2 : Locals} {d d1 d2 : D}
    (hne : ¬ e.eval σ = 0) (h1 : Step εR c i M F body σ d σ1 d1)
    (h2 : Step εR c i M F (.while e body) σ1 d1 σ2 d2) : Step εR c i M F (.while e body) σ d σ2 d2 := by
  refine ⟨h2.1.trans h1.1, fun l b hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h1.2 l b hlk hcs hM
  obtain ⟨l2, b2, r2, c2, m2, f2⟩ := h2.2 l1 b1 (by rw [h1.1]; exact hlk) c1 m1
  exact ⟨l2, b2, Runs.while_true hne r1 r2, c2, m2, fun k hk => (f2 k hk).trans (f1 k hk)⟩

/-- **A loop with an invariant and a measure**, on locals and abstract data. -/
theorem Step.while_inv {e : Expr} {body : Stmt APrim} (I : Locals → D → Prop) (μ : Locals → Nat)
    (hb : ∀ σ d, I σ d → ¬ e.eval σ = 0 →
      ∃ σ' d', Step εR c i M F body σ d σ' d' ∧ I σ' d' ∧ μ σ' < μ σ) :
    ∀ (n : Nat) (σ : Locals) (d : D), μ σ ≤ n → I σ d →
      ∃ σ' d', Step εR c i M F (.while e body) σ d σ' d' ∧ I σ' d' ∧ e.eval σ' = 0 := by
  intro n
  induction n with
  | zero =>
    intro σ d hn hI
    by_cases hg : e.eval σ = 0
    · exact ⟨σ, d, Step.while_false hg, hI, hg⟩
    · obtain ⟨σ1, d1, -, -, hlt⟩ := hb σ d hI hg
      omega
  | succ n ih =>
    intro σ d hn hI
    by_cases hg : e.eval σ = 0
    · exact ⟨σ, d, Step.while_false hg, hI, hg⟩
    · obtain ⟨σ1, d1, hr, hI1, hlt⟩ := hb σ d hI hg
      obtain ⟨σ2, d2, hr2, hI2, h0⟩ := ih σ1 d1 (by omega) hI1
      exact ⟨σ2, d2, Step.while_true hg hr hr2, hI2, h0⟩

/-- A larger footprint is a weaker claim. -/
theorem Step.widen {F' : Nat → Prop} {s : Stmt APrim} {σ σ' : Locals} {d d' : D}
    (h : Step εR c i M F s σ d σ' d') (hF : ∀ k, F k → F' k) : Step εR c i M F' s σ d σ' d' := by
  refine ⟨h.1, fun l b hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h.2 l b hlk hcs hM
  exact ⟨l1, b1, r1, c1, m1, fun k hk => f1 k (fun h' => hk (hF k h'))⟩

/-- The same step, with the end state named differently. -/
theorem Step.cast {s : Stmt APrim} {σ σ' σ'' : Locals} {d d' d'' : D}
    (h : Step εR c i M F s σ d σ' d') (hσ : σ' = σ'') (hd : d' = d'') : Step εR c i M F s σ d σ'' d'' := by
  subst hσ; subst hd; exact h

/-- **From steps to a triple.** -/
theorem Step.triple {P : Locals → D → Prop} {s : Stmt APrim} {Q : Locals → D → Locals → D → Prop}
    (h : ∀ σ d, P σ d → ∃ σ' d', Step εR c i M F s σ d σ' d' ∧ Q σ d σ' d') : Triple εR c i M F P s Q := by
  intro σ l b d hlk hcs hM hp
  obtain ⟨σ', d', hs, hq⟩ := h σ d hp
  obtain ⟨l', b', hr, hc', hM', hf⟩ := hs.2 l b hlk hcs hM
  exact ⟨σ', l', b', d', hr, hc', hM', hs.1, hf, hq⟩

/-- **Frame.** A step in a smaller state is a step in a larger one, if what
the larger state adds survives writes inside the footprint. -/
theorem Step.lift {D' : Type} {π : D' → D} {put : D' → D → D'} {M2 : D' → Region → Prop}
    {s : Stmt APrim} {σ σ' : Locals} {d' : D'} {d1 : D}
    (h : Step εR c i M F s σ (π d') σ' d1) (hput : π (put d' d1) = d1)
    (hM2 : ∀ b b', M2 d' b → M (π d') b → M d1 b' → (∀ k, ¬ F k → b' k = b k) → M2 (put d' d1) b') :
    Step εR c i (fun d' b => M (π d') b ∧ M2 d' b) F s σ d' σ' (put d' d1) := by
  refine ⟨h.1, fun l b hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h.2 l b hlk hcs hM.1
  exact ⟨l1, b1, r1, c1, ⟨by rw [hput]; exact m1, hM2 b b1 hM.2 hM.1 m1 f1⟩, f1⟩

/-- The same relation, stated another way. -/
theorem Step.iffM {M' : D → Region → Prop} {s : Stmt APrim} {σ σ' : Locals} {d d' : D}
    (h : Step εR c i M F s σ d σ' d') (hM : ∀ d b, M' d b ↔ M d b) : Step εR c i M' F s σ d σ' d' := by
  refine ⟨h.1, fun l b hlk hcs hm => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h.2 l b hlk hcs ((hM d b).1 hm)
  exact ⟨l1, b1, r1, c1, (hM d' b1).2 m1, f1⟩

end Rules

end Layer
