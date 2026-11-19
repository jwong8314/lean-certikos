import CertiKOS.KernPAlloc

/-!
# Kernel: critical sections that take a second lock

`KernPAlloc.cs_guarantee` covers a critical section that touches one region.
Some kernel operations hold one lock and take another inside: mapping a page
holds the page table's lock and calls `palloc`, which takes the allocation
table's lock. This file has what such operations need.

* `Runs`: a statement runs to completion under any continuation. Its
  combinators (`Runs.seq`, `Runs.ite_true`, `Runs.while_true`, …) build runs
  of structured code without stepping through continuations by hand.
* `fr_star`: a run changes only the variables its code assigns.
* `lk_star`: if every primitive call of a piece of code passes `lk` as the
  lock, and the code does not assign `lk`, then all of its own events are on
  that lock (`Ext`).
* `ext_frame`: **the frame.** Events of other CPUs, and our own events on
  another lock, leave our phase on lock `j` alone, and while we hold `j` they
  leave region `j` alone.
* `CSt c i j l b`: the state inside a critical section. The log is valid, we
  hold lock `i`, we are idle on lock `j`, and region `i` is `b`. `cst_rd` and
  `cst_wr` are the rules for reading and writing a cell.
* `cs_guarantee2`: **the two-lock step.** For a critical section `C` on lock
  `i` that may take and release lock `j` inside, `acquire(i); C; release(i)`
  finishes idle on both locks, and the region it releases is related by `C`'s
  specification to the region of the last release.
* `CS1`, `cs1_rd`, `cs1_wr`, `cs_guarantee1`: the same for a critical section
  that takes no second lock.
-/

namespace KernFrame

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding)
open LockRegionCPU KernPAlloc

/-! ## Runs of structured code -/

section Runs
variable {Pn Abs : Type} {P : Prims Pn Abs}

/-- `s` runs from `(σ, l)` to `(σ', l')`, under any continuation. -/
def Runs (P : Prims Pn Abs) (s : Stmt Pn) (σ : Locals) (l : Abs) (σ' : Locals) (l' : Abs) : Prop :=
  ∀ K, Star P ⟨s, K, σ, l⟩ ⟨.skip, K, σ', l'⟩

theorem Runs.skip {σ : Locals} {l : Abs} : Runs P .skip σ l σ l := fun _ => .refl _

theorem Runs.assign {σ : Locals} {l : Abs} (x : Ident) (e : Expr) :
    Runs P (.assign x e) σ l (σ.set x (e.eval σ)) l := fun _ => Star.single rfl

theorem Runs.call {σ : Locals} {l l' : Abs} {x : Ident} {p : Pn} {args : List Expr} {v : Val}
    (h : P p (args.map (·.eval σ)) l = some (v, l')) : Runs P (.call x p args) σ l (σ.set x v) l' :=
  fun _ => Star.single (by simp [step, h])

theorem Runs.seq {a b : Stmt Pn} {σ σ1 σ2 : Locals} {l l1 l2 : Abs} (h1 : Runs P a σ l σ1 l1)
    (h2 : Runs P b σ1 l1 σ2 l2) : Runs P (.seq a b) σ l σ2 l2 :=
  fun K => .step (c' := ⟨a, .seq b K, σ, l⟩) rfl ((h1 _).trans (.step (c' := ⟨b, K, σ1, l1⟩) rfl (h2 K)))

theorem Runs.ite_true {e : Expr} {a b : Stmt Pn} {σ σ' : Locals} {l l' : Abs} (hne : ¬ e.eval σ = 0)
    (h : Runs P a σ l σ' l') : Runs P (.ite e a b) σ l σ' l' :=
  fun K => .step (c' := ⟨a, K, σ, l⟩) (by have h' : ¬ e.eval σ = 0#32 := hne; simp [step, h']) (h K)

theorem Runs.ite_false {e : Expr} {a b : Stmt Pn} {σ σ' : Locals} {l l' : Abs} (h0 : e.eval σ = 0)
    (h : Runs P b σ l σ' l') : Runs P (.ite e a b) σ l σ' l' :=
  fun K => .step (c' := ⟨b, K, σ, l⟩) (by simp [step, h0]) (h K)

theorem Runs.while_false {e : Expr} {b : Stmt Pn} {σ : Locals} {l : Abs} (h0 : e.eval σ = 0) :
    Runs P (.while e b) σ l σ l := fun _ => Star.single (by simp [step, h0])

theorem Runs.while_true {e : Expr} {b : Stmt Pn} {σ σ1 σ2 : Locals} {l l1 l2 : Abs} (hne : ¬ e.eval σ = 0)
    (h1 : Runs P b σ l σ1 l1) (h2 : Runs P (.while e b) σ1 l1 σ2 l2) : Runs P (.while e b) σ l σ2 l2 :=
  fun K => .step (c' := ⟨b, .loop e b K, σ, l⟩) (by have h' : ¬ e.eval σ = 0#32 := hne; simp [step, h'])
    ((h1 _).trans (.step (c' := ⟨.while e b, K, σ1, l1⟩) rfl (h2 K)))

/-- A run to completion with no continuation runs under any continuation. -/
theorem Runs.of_stop {s : Stmt Pn} {σ σ' : Locals} {l l' : Abs}
    (h : Star P ⟨s, .stop, σ, l⟩ ⟨.skip, .stop, σ', l'⟩) : Runs P s σ l σ' l' :=
  fun K => MCSBoundC.star_app h K rfl

theorem ne_true {σ : Locals} {x : Ident} {v : Val} (h : σ x ≠ v) :
    ¬ (Expr.bin .ne (.var x) (.const v)).eval σ = 0 := by simp [Expr.eval, BinOp.eval, h]

theorem ne_false {σ : Locals} {x : Ident} {v : Val} (h : σ x = v) :
    (Expr.bin .ne (.var x) (.const v)).eval σ = 0 := by simp [Expr.eval, BinOp.eval, h]

theorem eq_true {σ : Locals} {x : Ident} {v : Val} (h : σ x = v) :
    ¬ (Expr.bin .eq (.var x) (.const v)).eval σ = 0 := by simp [Expr.eval, BinOp.eval, h]

theorem eq_false {σ : Locals} {x : Ident} {v : Val} (h : σ x ≠ v) :
    (Expr.bin .eq (.var x) (.const v)).eval σ = 0 := by simp [Expr.eval, BinOp.eval, h]

/-! ## A run changes only the variables its code assigns -/

/-- `s` does not assign `z`. -/
def frS (z : Ident) : Stmt Pn → Bool
  | .skip => true
  | .assign x _ => x != z
  | .seq a b => frS z a && frS z b
  | .ite _ a b => frS z a && frS z b
  | .while _ b => frS z b
  | .call x _ _ => x != z

def frK (z : Ident) : Cont Pn → Bool
  | .stop => true
  | .seq s k => frS z s && frK z k
  | .loop _ b k => frS z b && frK z k

theorem fr_step {z : Ident} {x x' : Config Pn Abs} (hS : frS z x.stmt = true) (hK : frK z x.cont = true)
    (hs : step P x = some x') : frS z x'.stmt = true ∧ frK z x'.cont = true ∧ x'.locals z = x.locals z := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  cases stmt with
  | skip =>
    cases cont with
    | stop => simp [step] at hs
    | seq s k =>
      simp only [step, Option.some.injEq] at hs; subst hs
      simp only [frK, Bool.and_eq_true] at hK; exact ⟨hK.1, hK.2, rfl⟩
    | loop e b k =>
      simp only [step, Option.some.injEq] at hs; subst hs
      simp only [frK, Bool.and_eq_true] at hK; exact ⟨hK.1, hK.2, rfl⟩
  | assign y e =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [frS, bne_iff_ne, ne_eq] at hS
    exact ⟨rfl, hK, Locals.set_other _ _ (fun h => hS h.symm)⟩
  | seq a b =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [frS, Bool.and_eq_true] at hS
    exact ⟨hS.1, by simp [frK, hS.2, hK], rfl⟩
  | ite e a b =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [frS, Bool.and_eq_true] at hS
    refine ⟨?_, hK, rfl⟩; simp only; split; exact hS.2; exact hS.1
  | «while» e b =>
    simp only [step] at hs
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst hs
    · exact ⟨rfl, hK, rfl⟩
    · simp only [frS] at hS; exact ⟨hS, by simp [frK, hS, hK], rfl⟩
  | call y p args =>
    simp only [step] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      simp only [frS, bne_iff_ne, ne_eq] at hS
      exact ⟨rfl, hK, Locals.set_other _ _ (fun h => hS h.symm)⟩
    · simp at hs

theorem fr_star {z : Ident} {x y : Config Pn Abs} (h : Star P x y) :
    frS z x.stmt = true → frK z x.cont = true → y.locals z = x.locals z := by
  induction h with
  | refl => intro _ _; rfl
  | step hs _ ih =>
    intro hS hK
    obtain ⟨hS', hK', he⟩ := fr_step hS hK hs
    exact (ih hS' hK').trans he

/-- A complete run leaves alone every variable its code does not assign. -/
theorem Runs.frame {s : Stmt Pn} {σ σ' : Locals} {l l' : Abs} (h : Runs P s σ l σ' l') {z : Ident}
    (hf : frS z s = true) : σ' z = σ z := fr_star (h .stop) hf rfl

end Runs

/-! ## Code that works on one lock: all its events are on that lock -/

/-- `l'` extends `l`, and every new event of CPU `c` is on lock `i`. -/
def Ext (c : CPU) (i : Nat) (l l' : RLog) : Prop :=
  ∃ xs, l' = xs ++ l ∧ ∀ e ∈ xs, e.cpu = c → e.lk = i

theorem Ext.refl (c : CPU) (i : Nat) (l : RLog) : Ext c i l l := ⟨[], rfl, by simp⟩

theorem Ext.trans {c : CPU} {i : Nat} {l l1 l2 : RLog} (h1 : Ext c i l l1) (h2 : Ext c i l1 l2) : Ext c i l l2 := by
  obtain ⟨xs, rfl, hx⟩ := h1
  obtain ⟨ys, rfl, hy⟩ := h2
  refine ⟨ys ++ xs, by simp, fun e he => ?_⟩
  rcases List.mem_append.1 he with h | h
  · exact hy e h
  · exact hx e h

theorem ext_one (c : CPU) {i : Nat} (l : RLog) (e : REvent) (he : e.lk = i) : Ext c i l (e :: l) :=
  ⟨[e], rfl, by simp [he]⟩

theorem ext_pull (εR : REnv) (c : CPU) {i : Nat} (l : RLog) (e : REvent) (he : e.lk = i) :
    Ext c i l (e :: rpull εR c l) := by
  refine ⟨e :: εR.query c l, rfl, fun e' he' hc => ?_⟩
  rcases List.mem_cons.1 he' with rfl | h
  · exact he
  · exact absurd hc (εR.noSelf c l e' h)

/-- Every primitive call passes `lk` as its lock. -/
def LkS : Stmt APrim → Prop
  | .skip => True
  | .assign _ _ => True
  | .seq a b => LkS a ∧ LkS b
  | .ite _ a b => LkS a ∧ LkS b
  | .while _ b => LkS b
  | .call _ _ args => args.head? = some lkE

def LkK : Cont APrim → Prop
  | .stop => True
  | .seq s k => LkS s ∧ LkK k
  | .loop _ b k => LkS b ∧ LkK k

theorem lk_call {εR : REnv} {c : CPU} {p : APrim} {args : List Expr} (ha : args.head? = some lkE)
    {σ : Locals} {l l' : RLog} {v : Val} (h : rprimsA εR c p (args.map (·.eval σ)) l = some (v, l')) :
    Ext c (σ "lk").toNat l l' := by
  match args, ha with
  | a :: rest, ha =>
    simp only [List.head?_cons, Option.some.injEq] at ha; subst ha
    cases p <;> rcases rest with _ | ⟨b, _ | ⟨d, _ | ⟨f, rest⟩⟩⟩ <;>
      simp only [List.map, rprimsA, lkE, Expr.eval, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      first
        | exact h.elim
        | (obtain ⟨-, rfl⟩ := h
           first | exact Ext.refl _ _ _ | exact ext_pull _ _ _ _ rfl | exact ext_one _ _ _ rfl)

theorem lk_step {εR : REnv} {c : CPU} {x x' : Config APrim RLog} (hS : LkS x.stmt) (hK : LkK x.cont)
    (hs : step (rprimsA εR c) x = some x') :
    LkS x'.stmt ∧ LkK x'.cont ∧ Ext c (x.locals "lk").toNat x.abs x'.abs := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  cases stmt with
  | skip =>
    cases cont with
    | stop => simp [step] at hs
    | seq s k => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hK.1, hK.2, Ext.refl _ _ _⟩
    | loop e b k => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hK.1, hK.2, Ext.refl _ _ _⟩
  | assign y e => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨trivial, hK, Ext.refl _ _ _⟩
  | seq a b => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hS.1, ⟨hS.2, hK⟩, Ext.refl _ _ _⟩
  | ite e a b =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨?_, hK, Ext.refl _ _ _⟩; simp only; split; exact hS.2; exact hS.1
  | «while» e b =>
    simp only [step] at hs
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst hs
    · exact ⟨trivial, hK, Ext.refl _ _ _⟩
    · exact ⟨hS, ⟨hS, hK⟩, Ext.refl _ _ _⟩
  | call y p args =>
    simp only [step] at hs
    split at hs
    · rename_i v a' hp
      simp only [Option.some.injEq] at hs; subst hs
      exact ⟨trivial, hK, lk_call hS hp⟩
    · simp at hs

/-- **All of the code's own events are on the lock in `lk`.** -/
theorem lk_star {εR : REnv} {c : CPU} {x y : Config APrim RLog} (h : Star (rprimsA εR c) x y) :
    LkS x.stmt → LkK x.cont → frS "lk" x.stmt = true → frK "lk" x.cont = true →
    Ext c (x.locals "lk").toNat x.abs y.abs := by
  induction h with
  | refl => intro _ _ _ _; exact Ext.refl _ _ _
  | step hs _ ih =>
    intro hS hK hfS hfK
    obtain ⟨hS', hK', he⟩ := lk_step hS hK hs
    obtain ⟨hfS', hfK', hlk⟩ := fr_step hfS hfK hs
    have := ih hS' hK' hfS' hfK'
    rw [hlk] at this
    exact he.trans this

/-! ## The frame -/

/-- An event on another lock leaves lock `j` and its region alone. -/
theorem rstep_lock_other {S S' : RState} {e : REvent} {o : Option HEventR} {j : Nat}
    (hs : rstep S e = some (S', o)) (hne : j ≠ e.lk) : S'.lk j = S.lk j ∧ S'.mem j = S.mem j := by
  obtain ⟨d, i, k⟩ := e
  simp only at hne
  cases k with
  | tk k =>
    simp only [rstep] at hs
    split at hs
    · simp at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs
      exact ⟨upd_other _ _ hne, rfl⟩
  | pull =>
    simp only [rstep] at hs
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs; exact ⟨rfl, rfl⟩
    · simp at hs
  | wr a v =>
    simp only [rstep] at hs
    split at hs
    · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, -⟩ := hs
      exact ⟨rfl, upd_other _ _ hne⟩
    · simp at hs

/-- **The frame.** Over an extension whose own events are all on lock `i`, our
phase on another lock `j` is unchanged, and if we hold `j` its region is
unchanged. -/
theorem ext_frame {c : CPU} {i j : Nat} (hji : j ≠ i) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) :
    ∀ (xs : RLog) {S' : RState} {H' : HLogR}, (∀ e ∈ xs, e.cpu = c → e.lk = i) →
      rreplay (xs ++ l) = some (S', H') →
      (S'.lk j).phase c = (S.lk j).phase c ∧ (Holding S c j → S'.mem j = S.mem j)
  | [], S', H', _, hr => by
    simp only [List.nil_append] at hr; rw [hl] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr
    exact ⟨rfl, fun _ => rfl⟩
  | e :: xs, S', H', hx, hr => by
    obtain ⟨S2, H2, o, hl2, hs, -⟩ := LockRegion.rreplay_cons hr
    obtain ⟨h1, h2⟩ := ext_frame hji hl xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl2
    by_cases hec : e.cpu = c
    · obtain ⟨g1, g2⟩ := rstep_lock_other hs (j := j) (by rw [hx e List.mem_cons_self hec]; exact hji)
      exact ⟨by rw [g1]; exact h1, fun hh => g2.trans (h2 hh)⟩
    · obtain ⟨g1, g2⟩ := rstep_other (c := c) (i := j) (fun d hd hc => LockRegion.rmutex hl2 j hd hc) hs hec
      refine ⟨(g1 j).trans h1, fun hh => ?_⟩
      have hh2 : Holding S2 c j := by obtain ⟨t, ht⟩ := hh; exact ⟨t, by rw [h1]; exact ht⟩
      exact (g2 hh2).1.trans (h2 hh)

theorem ext_frame' {c : CPU} {i j : Nat} (hji : j ≠ i) {l l' : RLog} {S S' : RState} {H H' : HLogR}
    (hl : rreplay l = some (S, H)) (hl' : rreplay l' = some (S', H')) (he : Ext c i l l') :
    (S'.lk j).phase c = (S.lk j).phase c ∧ (Holding S c j → S'.mem j = S.mem j) := by
  obtain ⟨xs, rfl, hx⟩ := he
  exact ext_frame hji hl xs hx hl'

/-! ## The state inside a critical section -/

/-- Inside a critical section on lock `i`: the log is valid, we hold `i`, we
are idle on `j`, and region `i` is `b`. -/
def CSt (c : CPU) (i j : Nat) (l : RLog) (b : Region) : Prop :=
  ∃ S H, rreplay l = some (S, H) ∧ Holding S c i ∧ (S.lk j).phase c = .idle ∧ S.mem i = b

/-- Read a cell of our region. -/
theorem cst_rd {εR : REnv} {c : CPU} {i j : Nat} {l : RLog} {b : Region} (h : CSt c i j l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (x : Ident) (je : Expr) :
    Runs (rprimsA εR c) (.call x .pull [lkE, je]) σ l (σ.set x (b (je.eval σ).toNat)) l := by
  obtain ⟨S, H, hl, -, -, rfl⟩ := h
  have hm := LockRegion.rreplay_mem hl i
  rw [hm]
  exact Runs.call (by simp [rprimsA, lkE, Expr.eval, hlk])

/-- Write a cell of our region. -/
theorem cst_wr {εR : REnv} {c : CPU} {i j : Nat} {l : RLog} {b : Region} (h : CSt c i j l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (je ve : Expr) :
    ∃ l', Runs (rprimsA εR c) (.call "_" .push [lkE, je, ve]) σ l (σ.set "_" 0) l' ∧
      CSt c i j l' (setCell b (je.eval σ).toNat (ve.eval σ)) := by
  obtain ⟨S, H, hl, hh, hj, rfl⟩ := h
  have hs : rstep S ⟨c, i, .wr (je.eval σ).toNat (ve.eval σ)⟩ = some (⟨S.lk, upd S.mem i
      (setCell (S.mem i) (je.eval σ).toNat (ve.eval σ)), upd S.dirty i true⟩, none) := by simp [rstep, hh]
  have hl2 := LockRegion.rreplay_cons_of hl hs
  exact ⟨⟨c, i, .wr (je.eval σ).toNat (ve.eval σ)⟩ :: l, Runs.call (by simp [rprimsA, lkE, Expr.eval, hlk]),
    ⟨S.lk, upd S.mem i (setCell (S.mem i) (je.eval σ).toNat (ve.eval σ)), upd S.dirty i true⟩, H,
    by simpa [LockRegion.consO] using hl2, hh, hj, by simp⟩

/-! ## The two-lock step -/

theorem acquireA_lk : LkS acquireA := by simp [LkS, acquireA, loopA]
theorem acquireA_fr : frS (Pn := APrim) "lk" acquireA = true := by decide

/-- **`acquire(i); C; release(i)` where `C` may take lock `j` inside.**
`R b σ b' σ'` is `C`'s specification on region `i`. -/
theorem cs_guarantee2 {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    {j : Nat} (hji : j ≠ iv.toNat) (hidj : (S.lk j).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) (C : Stmt APrim) (R : Region → Locals → Region → Locals → Prop)
    (hC : ∀ (σ : Locals) (l : RLog) (b : Region), σ "lk" = iv → CSt c iv.toNat j l b →
      ∃ σ' l' b', Runs (rprimsA εR c) C σ l σ' l' ∧ CSt c iv.toNat j l' b' ∧ σ' "lk" = iv ∧ R b σ b' σ') :
    ∃ (σ1 σ2 : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨.seq acquireA (.seq C relA), .stop, σ, l⟩ ⟨.skip, .stop, σ2.set "_" 0, rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧ (S3.lk j).phase c = .idle ∧
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
  have hold1 : Holding S1 c iv.toNat := by
    obtain ⟨SA1', HA1', hA1', hlk1'⟩ := rreplay_erase hl1
    rw [her, hA1] at hA1'
    simp only [Option.some.injEq, Prod.mk.injEq] at hA1'; obtain ⟨rfl, -⟩ := hA1'
    obtain ⟨t, ht⟩ := hholdA; exact ⟨t, by rw [← hlk1']; exact ht⟩
  have hsee : S1.mem iv.toNat = hmemR iv.toNat H1 := LockRegion.acquire_sees hl1 (hq1 hold1)
  have hσlk : σy "lk" = iv := by
    rw [hσ1 "lk" (by decide) (by decide) (by decide) (by decide)]; exact hσ
  have hext : Ext c iv.toNat l r1 := by
    have := lk_star hstR acquireA_lk trivial acquireA_fr rfl
    simpa [hσ] using this
  have hidj1 : (S1.lk j).phase c = .idle := by rw [(ext_frame' hji hl hl1 hext).1]; exact hidj
  -- the critical section
  obtain ⟨σ2, r2, b2, hcrit, ⟨S2, H2, hl2, hold2, hidj2, hb2⟩, hσ2, hR⟩ :=
    hC σy r1 (S1.mem iv.toNat) hσlk ⟨S1, H1, hl1, hold1, hidj1, rfl⟩
  -- release
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
  refine ⟨σy, σ2, rev c iv.toNat .incNow :: rpull εR c r2, _, H1, _, ?_, hl3, by simp, ?_, hσ1, ?_⟩
  · have hfr := MCSBoundC.star_app hstR (.seq (.seq C relA) .stop) rfl
    refine .step (c' := ⟨acquireA, .seq (.seq C relA) .stop, σ, l⟩) rfl (hfr.trans ?_)
    refine .step (c' := ⟨.seq C relA, .stop, σy, r1⟩) rfl ?_
    refine .step (c' := ⟨C, .seq relA .stop, σy, r1⟩) rfl ((hcrit _).trans ?_)
    refine .step (c' := ⟨relA, .stop, σ2, r2⟩) rfl ?_
    exact Star.single (by simp [step, rprimsA, relA, Expr.eval, lkE, hσ2])
  · simp only [upd_other _ _ hji]; rw [g1 j]; exact hidj2
  · have : hmemR iv.toNat (LockRegion.consO (some (.relR c iv.toNat (S2'.mem iv.toNat))) H2') =
        S2.mem iv.toNat := by simp [LockRegion.consO, hmemR, hmem2']
    rw [this, hb2, ← hsee]; exact hR
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

end KernFrame
