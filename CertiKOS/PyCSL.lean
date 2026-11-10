import CertiKOS.PyL

/-!
# Concurrent separation logic for PyL, with a soundness proof

A concurrent separation logic (CSL) in the style of O'Hearn and Brookes.
Soundness is proved against the operational semantics of `PyL.lean`,
following Vafeiadis, *Concurrent Separation Logic and Operational Semantics*
(MFPS 2011).

* Assertions `Assn := Store → Heap → Prop` describe a thread's locals and the
  part of the heap it **owns**. `P ⋆ Q` splits the owned heap into two
  disjoint parts.
* A **resource invariant** `J : Heap → Prop` describes the heap protected by
  the global lock `L` (`with L:` = `atomic`). The heap in `J` belongs to
  nobody while `L` is free. A thread that enters `with L:` gets ownership of
  it, and must re-establish `J` to give it back on leaving. Ownership of
  memory can thus move between threads through the lock. This is CertiKOS's
  `pull`/`push` of lock-protected shared memory ([OSDI16] Fig. 7), here as a
  logic instead of a copy.
* Triples are *semantic*: `Valid J P c Q` is defined from the operational
  semantics (`Safe`). Every proof rule is a theorem (`rule_*`), so there is no
  separate proof system to trust.
* `pool_sound` is the soundness theorem for a whole thread pool. If every
  thread's triple holds and the initial heap splits into the threads'
  preconditions plus `J`, then no execution ever faults or races, and when all
  threads finish the heap splits into their postconditions plus `J`.

Safety is step-indexed (`Safe J n …`), and soundness holds for executions of
every finite length. As usual for CSL this is partial correctness (safety),
not liveness. Liveness of the lock protocol is what the CCAL proofs in
`TicketProtocol.lean`/`FairEnv.lean` provide.
-/

namespace PyL
open Heap

abbrev Assn := Store → Heap → Prop
abbrev Inv := Heap → Prop

def Assn.star (P Q : Assn) : Assn :=
  fun s h => ∃ h₁ h₂, Disj h₁ h₂ ∧ h = h₁ ⊎ h₂ ∧ P s h₁ ∧ Q s h₂

scoped infixr:70 " ⋆ " => Assn.star

def Assn.emp : Assn := fun _ h => h = Heap.emp
/-- `o.f ↦ v`: the owned heap is exactly the one attribute `o.f`, holding `v`. -/
def Assn.pointsTo (o : Expr) (f : String) (v : Expr) : Assn :=
  fun s h => h = single ⟨o.eval s, f⟩ (v.eval s)
def Inv.lift (J : Inv) : Assn := fun _ h => J h
/-- The trivial invariant, used for code already inside `with L:`. -/
def empInv : Inv := fun h => h = Heap.emp

/-- `R` does not mention the variables `xs`. -/
def Indep (R : Assn) (xs : List Var) : Prop :=
  ∀ s s' h, (∀ x, x ∉ xs → s' x = s x) → R s h → R s' h

def entering (c c' : Cmd) : Bool := !c.locked && c'.locked
def leaving (c c' : Cmd) : Bool := c.locked && !c'.locked

theorem if_neg' {b : Bool} {p q : Prop} (hb : b = false) : (if b then p else q) = q := by
  subst hb; rfl
theorem if_pos' {b : Bool} {p q : Prop} (hb : b = true) : (if b then p else q) = p := by
  subst hb; rfl

/-- Decide disjointness goals from disjointness hypotheses. -/
theorem disj_comm_iff {a b : Heap} : Disj a b ↔ Disj b a := ⟨Disj.symm, Disj.symm⟩

macro "disj" : tactic => `(tactic| (
  simp_all only [disj_union_left, disj_union_right, disj_emp_left, disj_emp_right,
    true_and, and_true, and_self, disj_comm_iff]))

theorem swap_mid {a b c d : Heap} (h : Disj b c) : a ⊎ b ⊎ (c ⊎ d) = a ⊎ c ⊎ b ⊎ d := by
  rw [union_assoc a b (c ⊎ d), ← union_assoc b c d, union_comm h, union_assoc c b d,
    ← union_assoc a c (b ⊎ d), ← union_assoc (a ⊎ c) b d]

/-! ## Safety -/

/-- `Safe J n c s h Q`: thread code `c`, with locals `s` and owned heap `h`,
runs for `n` more steps without faulting, whatever the other threads (who own
a disjoint frame `hF`) and the lock invariant `J` contribute. When it is done,
`Q` holds of what it owns. Entering `with L:` hands it a heap satisfying `J`;
leaving takes one back. -/
def Safe (J : Inv) : Nat → Cmd → Store → Heap → Assn → Prop
  | 0, _, _, _, _ => True
  | n + 1, c, s, h, Q =>
    (c = .skip → Q s h) ∧
    (∀ l, c.acc s = some l → h l ≠ none) ∧
    (∀ hJ hF c' s' H', Disj h hJ → Disj (h ⊎ hJ) hF → Step c s (h ⊎ hJ ⊎ hF) c' s' H' →
      (if entering c c' then J hJ else hJ = Heap.emp) →
      ∃ h' hJ', Disj h' hJ' ∧ Disj (h' ⊎ hJ') hF ∧ H' = h' ⊎ hJ' ⊎ hF ∧
        (if leaving c c' then J hJ' else hJ' = Heap.emp) ∧ Safe J n c' s' h' Q)

/-- The CSL triple `J ⊢ {P} c {Q}`, defined semantically. -/
def Valid (J : Inv) (P : Assn) (c : Cmd) (Q : Assn) : Prop :=
  ∀ n s h, P s h → Safe J n c s h Q

theorem safe_mono {J : Inv} : ∀ {n m c s h Q}, m ≤ n → Safe J n c s h Q → Safe J m c s h Q
  | _, 0, _, _, _, _, _, _ => trivial
  | 0, _ + 1, _, _, _, _, hle, _ => absurd hle (by omega)
  | _ + 1, _ + 1, _, _, _, _, hle, ⟨h1, h2, h3⟩ => ⟨h1, h2, fun hJ hF c' s' H' d1 d2 st hj => by
      obtain ⟨h', hJ', a, b, e, f, g⟩ := h3 hJ hF c' s' H' d1 d2 st hj
      exact ⟨h', hJ', a, b, e, f, safe_mono (by omega) g⟩⟩

theorem safe_skip {J : Inv} {n s h Q} (hq : Q s h) : Safe J n .skip s h Q := by
  cases n with
  | zero => trivial
  | succ n =>
    exact ⟨fun _ => hq, fun l e => (by simp [Cmd.acc] at e),
      fun _ _ _ _ _ _ _ st _ => absurd st Step.no_skip⟩

theorem safe_conseq {J : Inv} {Q Q' : Assn} (hQ : ∀ s h, Q s h → Q' s h) :
    ∀ {n c s h}, Safe J n c s h Q → Safe J n c s h Q'
  | 0, _, _, _, _ => trivial
  | _ + 1, _, _, _, ⟨h1, h2, h3⟩ => ⟨fun e => hQ _ _ (h1 e), h2,
      fun hJ hF c' s' H' d1 d2 st hj => by
        obtain ⟨h', hJ', a, b, e, f, g⟩ := h3 hJ hF c' s' H' d1 d2 st hj
        exact ⟨h', hJ', a, b, e, f, safe_conseq hQ g⟩⟩

/-- Safety of a step that does not take or release the lock. -/
theorem safe_local {J : Inv} {n c s h Q} (hns : c ≠ .skip) (hlk : c.locked = false)
    (hacc : ∀ l, c.acc s = some l → h l ≠ none)
    (H : ∀ hF c' s' H', Disj h hF → Step c s (h ⊎ hF) c' s' H' →
       c'.locked = false ∧ ∃ h', Disj h' hF ∧ H' = h' ⊎ hF ∧ Safe J n c' s' h' Q) :
    Safe J (n + 1) c s h Q := by
  refine ⟨fun e => absurd e hns, hacc, fun hJ hF c' s' H' d1 d2 st hj => ?_⟩
  rw [union_assoc] at st
  obtain ⟨hl', h', d3, e, hs⟩ := H (hJ ⊎ hF) c' s' H' (by disj) st
  have en : entering c c' = false := by simp [entering, hlk, hl']
  rw [if_neg' en] at hj
  subst hj
  refine ⟨h', Heap.emp, by simp, by simpa using d3, by simpa using e, ?_, hs⟩
  rw [if_neg' (by simp [leaving, hlk])]

/-! ## Proof rules (each one is a theorem) -/

theorem rule_skip {J : Inv} {P : Assn} : Valid J P .skip P := fun _ _ _ hp => safe_skip hp

theorem rule_conseq {J : Inv} {P P' Q Q' : Assn} {c : Cmd} (hv : Valid J P c Q)
    (hP : ∀ s h, P' s h → P s h) (hQ : ∀ s h, Q s h → Q' s h) : Valid J P' c Q' :=
  fun n s h hp => safe_conseq hQ (hv n s h (hP s h hp))

theorem rule_exists {α : Type} {J : Inv} {P : α → Assn} {Q : Assn} {c : Cmd}
    (hv : ∀ a, Valid J (P a) c Q) : Valid J (fun s h => ∃ a, P a s h) c Q :=
  fun n s h ⟨a, hp⟩ => hv a n s h hp

/-- `{Q[x := e]} x = e {Q}` -/
theorem rule_assign {J : Inv} {x : Var} {e : Expr} {Q : Assn} :
    Valid J (fun s h => Q (s.set x (e.eval s)) h) (.assign x e) Q := by
  intro n s h hq
  cases n with
  | zero => trivial
  | succ n =>
    refine safe_local (by simp) rfl (by simp [Cmd.acc]) fun hF c' s' H' d st => ?_
    cases st
    exact ⟨rfl, h, d, rfl, safe_skip hq⟩

/-- `{∃ v. o.f ↪ v ∧ Q[x := v]} x = o.f {Q}`, in weakest-precondition form.
The usual small-footprint rule follows with the frame rule. -/
theorem rule_load {J : Inv} {x : Var} {o : Expr} {f : String} {Q : Assn} :
    Valid J (fun s h => ∃ v, h ⟨o.eval s, f⟩ = some v ∧ Q (s.set x v) h) (.load x o f) Q := by
  intro n s h ⟨v, hv, hq⟩
  cases n with
  | zero => trivial
  | succ n =>
    refine safe_local (by simp) rfl ?_ fun hF c' s' H' d st => ?_
    · intro l e; simp only [Cmd.acc, Option.some.injEq] at e; subst e; simp [hv]
    · cases st with
      | load hv' =>
        rw [union_some_left hv] at hv'; cases hv'
        exact ⟨rfl, h, d, rfl, safe_skip hq⟩

/-- `{o.f ↪ _ ∧ Q[h := h[o.f := e]]} o.f = e {Q}` -/
theorem rule_store {J : Inv} {o : Expr} {f : String} {e : Expr} {Q : Assn} :
    Valid J (fun s h => h ⟨o.eval s, f⟩ ≠ none ∧ Q s (h.upd ⟨o.eval s, f⟩ (e.eval s)))
      (.store o f e) Q := by
  intro n s h ⟨hne, hq⟩
  cases n with
  | zero => trivial
  | succ n =>
    refine safe_local (by simp) rfl ?_ fun hF c' s' H' d st => ?_
    · intro l el; simp only [Cmd.acc, Option.some.injEq] at el; subst el; exact hne
    · cases st with
      | store _ => exact ⟨rfl, _, disj_upd_left _ d hne, upd_union_left _ hne, safe_skip hq⟩

theorem safe_seq {J : Inv} {c₂ : Cmd} {R Q : Assn} (hl : c₂.locked = false) :
    ∀ {n c₁ s h}, Safe J n c₁ s h R → (∀ s h, R s h → Safe J n c₂ s h Q) →
      Safe J n (.seq c₁ c₂) s h Q
  | 0, _, _, _, _, _ => trivial
  | n + 1, c₁, s, h, ⟨hsk, hacc, hstep⟩, h2 => by
    refine ⟨fun e => (by cases e), fun l e => hacc l e, fun hJ hF c' s' H' d1 d2 st hj => ?_⟩
    cases st with
    | seqSkip =>
      rw [if_neg' (by simp [entering, Cmd.locked, hl])] at hj
      subst hj
      refine ⟨h, Heap.emp, by simp, by simpa using d2, rfl, ?_,
        safe_mono (by omega) (h2 _ _ (hsk rfl))⟩
      rw [if_neg' (by simp [leaving, Cmd.locked])]
    | seq st' =>
      obtain ⟨h', hJ', a, b, e, f, g⟩ := hstep hJ hF _ _ _ d1 d2 st' hj
      exact ⟨h', hJ', a, b, e, f, safe_seq hl g (fun s h r => safe_mono (by omega) (h2 s h r))⟩

/-- Sequencing. (`c₂` is source code, not inside a running `with` block.) -/
theorem rule_seq {J : Inv} {P R Q : Assn} {c₁ c₂ : Cmd} (hl : c₂.locked = false)
    (h₁ : Valid J P c₁ R) (h₂ : Valid J R c₂ Q) : Valid J P (.seq c₁ c₂) Q :=
  fun n s h hp => safe_seq hl (h₁ n s h hp) (fun s h r => h₂ n s h r)

theorem rule_ite {J : Inv} {P Q : Assn} {e : Expr} {c₁ c₂ : Cmd}
    (hl₁ : c₁.locked = false) (hl₂ : c₂.locked = false)
    (h₁ : Valid J (fun s h => P s h ∧ e.eval s ≠ 0) c₁ Q)
    (h₂ : Valid J (fun s h => P s h ∧ e.eval s = 0) c₂ Q) : Valid J P (.ite e c₁ c₂) Q := by
  intro n s h hp
  cases n with
  | zero => trivial
  | succ n =>
    refine safe_local (by simp) rfl (by simp [Cmd.acc]) fun hF c' s' H' d st => ?_
    cases st with
    | iteT he => exact ⟨hl₁, h, d, rfl, h₁ n s h ⟨hp, he⟩⟩
    | iteF he => exact ⟨hl₂, h, d, rfl, h₂ n s h ⟨hp, he⟩⟩

/-- `while` with loop invariant `I`. -/
theorem rule_while {J : Inv} {I : Assn} {e : Expr} {c : Cmd} (hl : c.locked = false)
    (hb : Valid J (fun s h => I s h ∧ e.eval s ≠ 0) c I) :
    Valid J I (.while e c) (fun s h => I s h ∧ e.eval s = 0) := by
  intro n
  induction n with
  | zero => intro _ _ _; trivial
  | succ n ih =>
    intro s h hi
    refine safe_local (by simp) rfl (by simp [Cmd.acc]) fun hF c' s' H' d st => ?_
    cases st
    refine ⟨rfl, h, d, rfl, ?_⟩
    cases n with
    | zero => trivial
    | succ m =>
      refine safe_local (by simp) rfl (by simp [Cmd.acc]) fun hF' c'' s'' H'' d' st' => ?_
      cases st' with
      | iteT he =>
        exact ⟨hl, h, d', rfl, safe_seq rfl (hb m s h ⟨hi, he⟩)
          (fun s h r => safe_mono (by omega) (ih s h r))⟩
      | iteF he => exact ⟨rfl, h, d', rfl, safe_skip ⟨hi, he⟩⟩

theorem safe_inAtomic {J : Inv} {Q : Assn} :
    ∀ {n c s h}, Safe empInv n c s h (Q ⋆ J.lift) → Safe J n (.inAtomic c) s h Q
  | 0, _, _, _, _ => trivial
  | n + 1, c, s, h, ⟨hsk, hacc, hstep⟩ => by
    refine ⟨fun e => (by cases e), fun l e => hacc l e, fun hJ hF c' s' H' d1 d2 st hj => ?_⟩
    cases st with
    | inAtomic st' =>
      rw [if_neg' (by simp [entering, Cmd.locked])] at hj
      subst hj
      obtain ⟨h', hJ', a, b, e, f, g⟩ := hstep Heap.emp hF _ _ _ d1 d2 st' (by split <;> rfl)
      have : hJ' = Heap.emp := by split at f <;> exact f
      subst this
      refine ⟨h', Heap.emp, a, b, e, ?_, safe_inAtomic g⟩
      rw [if_neg' (by simp [leaving, Cmd.locked])]
    | inAtomicSkip =>
      rw [if_neg' (by simp [entering, Cmd.locked])] at hj
      subst hj
      obtain ⟨h₁, h₂, d, rfl, hq, hj2⟩ := hsk rfl
      refine ⟨h₁, h₂, d, by simpa using d2, by simp, ?_, safe_skip hq⟩
      rw [if_pos' (by simp [leaving, Cmd.locked])]; exact hj2

/-- **Critical region.** `J ⊢ {P} with L: c {Q}` if `{P ⋆ J} c {Q ⋆ J}` holds
for the body run alone. -/
theorem rule_atomic {J : Inv} {P Q : Assn} {c : Cmd}
    (hv : Valid empInv (P ⋆ J.lift) c (Q ⋆ J.lift)) : Valid J P (.atomic c) Q := by
  intro n s hh hp
  cases n with
  | zero => trivial
  | succ n =>
    refine ⟨fun e => (by cases e), fun l e => (by simp [Cmd.acc] at e),
      fun hJ hF c' s' H' d1 d2 st hj => ?_⟩
    cases st
    rw [if_pos' (by simp [entering, Cmd.locked])] at hj
    refine ⟨hh ⊎ hJ, Heap.emp, by simp, by simpa using d2, by simp, ?_,
      safe_inAtomic (hv n s _ ⟨hh, hJ, d1, rfl, hp, hj⟩)⟩
    rw [if_neg' (by simp [leaving, Cmd.locked])]

theorem safe_frame {J : Inv} {Q R : Assn} :
    ∀ {n c s h hR}, Safe J n c s h Q → Disj h hR → R s hR → Indep R c.mods →
      Safe J n c s (h ⊎ hR) (Q ⋆ R)
  | 0, _, _, _, _, _, _, _, _ => trivial
  | n + 1, c, s, h, hR, ⟨hsk, hacc, hstep⟩, dR, hr, hind => by
    refine ⟨fun e => ⟨h, hR, dR, rfl, hsk e, hr⟩, fun l e => union_ne_none_left (hacc l e),
      fun hJ hF c' s' H' d1 d2 st hj => ?_⟩
    have dRJ : Disj hR hJ := by disj
    rw [← swap_mid dRJ.symm] at st
    obtain ⟨h', hJ', a, b, e, f, g⟩ := hstep hJ (hR ⊎ hF) c' s' H' (by disj) (by disj) st hj
    have dJR : Disj hJ' hR := by disj
    refine ⟨h' ⊎ hR, hJ', by disj, by disj, by rw [e, swap_mid dJR], f, ?_⟩
    have hm := st.mods
    exact safe_frame g (by disj) (hind s s' hR hm.1 hr)
      (fun s₁ s₂ h₁ ag r => hind s₁ s₂ h₁ (fun x hx => ag x (fun hx' => hx (hm.2 x hx'))) r)

/-- **Frame rule.** -/
theorem rule_frame {J : Inv} {P Q R : Assn} {c : Cmd} (hv : Valid J P c Q)
    (hind : Indep R c.mods) : Valid J (P ⋆ R) c (Q ⋆ R) := by
  rintro n s _ ⟨h₁, h₂, d, rfl, hp, hr⟩
  exact safe_frame (hv n s h₁ hp) d hr hind

/-! ## Soundness for a thread pool -/

/-- The part of `H` that the ownership map `own` gives to `o`
(`some i` = thread `i`, `none` = the lock invariant). -/
def restrict (own : Loc → Option Nat) (H : Heap) (o : Option Nat) : Heap :=
  fun l => if own l = o then H l else none

/-- Everything except thread `i`'s part and the invariant's part. -/
def others (own : Loc → Option Nat) (H : Heap) (i : Nat) : Heap :=
  fun l => if own l = none ∨ own l = some i then none else H l

theorem split_heap (own : Loc → Option Nat) (H : Heap) (i : Nat) :
    H = restrict own H (some i) ⊎ restrict own H none ⊎ others own H i := by
  funext l
  simp only [union_apply, restrict, others]
  rcases ho : own l with _ | k
  · simp
  · by_cases hk : k = i
    · subst hk; cases H l <;> simp
    · simp [hk]

theorem split_disj (own : Loc → Option Nat) (H : Heap) (i : Nat) :
    Disj (restrict own H (some i)) (restrict own H none) ∧
    Disj (restrict own H (some i) ⊎ restrict own H none) (others own H i) := by
  refine ⟨fun l => ?_, fun l => ?_⟩
  · simp only [restrict]; rcases own l with _ | k <;> simp
  · simp only [restrict, others, union_apply]
    rcases own l with _ | k
    · simp
    · by_cases hk : k = i <;> simp [hk]

/-- After thread `i` steps, ownership is reassigned: what it now owns is
`h'`, what it handed back to the lock is `hJ'`, everything else is as before. -/
theorem reassign (own own' : Loc → Option Nat) (H h' hJ' : Heap) (i : Nat) (keep : Bool)
    (hown : ∀ l, own' l = if h' l ≠ none then some i else if hJ' l ≠ none then none
      else if own l = some i then none else own l)
    (d1 : Disj h' hJ')
    (d2 : Disj (h' ⊎ hJ') (if keep then restrict own H none ⊎ others own H i else others own H i)) :
    let H' := h' ⊎ hJ' ⊎ (if keep then restrict own H none ⊎ others own H i else others own H i)
    restrict own' H' (some i) = h' ∧
    (∀ j, j ≠ i → restrict own' H' (some j) = restrict own H (some j)) ∧
    restrict own' H' none = hJ' ⊎ (if keep then restrict own H none else Heap.emp) := by
  intro H'
  refine ⟨funext fun l => ?_, fun j hj => funext fun l => ?_, funext fun l => ?_⟩
  all_goals
    have a := d1 l
    have b := d2 l
    have ho' := hown l
    try have hij : i ≠ j := Ne.symm hj
    simp only [H', restrict, union_apply] at a b ho' ⊢
    cases keep <;> cases hh : h' l <;> cases hk : hJ' l <;> rcases ho : own l with _ | k <;>
      cases hH : H l <;> (try by_cases hki : k = i) <;> (try by_cases hkj : k = j) <;>
      simp_all [restrict, others, union_apply]

/-- The pool invariant at step index `n`. -/
def PoolInv (J : Inv) (Q : Nat → Assn) (n : Nat) (ts : Pool) (H : Heap) : Prop :=
  ∃ own : Loc → Option Nat,
    (∀ i j (hi : i < ts.length) (hj : j < ts.length), i ≠ j →
      ts[i].cmd.locked = true → ts[j].cmd.locked = false) ∧
    ((∀ i (hi : i < ts.length), ts[i].cmd.locked = false) → J (restrict own H none)) ∧
    (∀ i (hi : i < ts.length), ts[i].cmd.locked = true → restrict own H none = Heap.emp) ∧
    (∀ i (hi : i < ts.length), Safe J n ts[i].cmd ts[i].store (restrict own H (some i)) (Q i))

theorem poolInv_step {J : Inv} {Q : Nat → Assn} {n : Nat} {ts ts' : Pool} {H H' : Heap}
    (inv : PoolInv J Q (n + 1) ts H) (st : MStep ts H ts' H') : PoolInv J Q n ts' H' := by
  cases st with
  | step i hi stp hcheck =>
  rename_i c' s'
  obtain ⟨own, hone, hJfree, hJlocked, hsafe⟩ := inv
  obtain ⟨_, _, hstep⟩ := hsafe i hi
  have ⟨sd1, sd2⟩ := split_disj own H i
  -- Thread i takes the step, with the right split of the rest of the heap.
  obtain ⟨keep, h', hJ', d1, d2, e, hleave, hs', hkeep⟩ : ∃ keep : Bool, ∃ h' hJ',
      Disj h' hJ' ∧
      Disj (h' ⊎ hJ') (if keep then restrict own H none ⊎ others own H i else others own H i) ∧
      H' = h' ⊎ hJ' ⊎ (if keep then restrict own H none ⊎ others own H i else others own H i) ∧
      (if leaving ts[i].cmd c' then J hJ' else hJ' = Heap.emp) ∧
      Safe J n c' s' h' (Q i) ∧ (keep = !entering ts[i].cmd c') := by
    rw [split_heap own H i] at stp
    cases hen : entering ts[i].cmd c'
    · rw [union_assoc, ← union_emp (restrict own H (some i))] at stp
      obtain ⟨h', hJ', a, b, e, f, g⟩ := hstep Heap.emp _ c' s' H' (by simp)
        (by disj) stp (by rw [if_neg' hen])
      exact ⟨true, h', hJ', a, b, e, f, g, rfl⟩
    · have hl : ts[i].cmd.locked = false ∧ c'.locked = true := by
        simpa [entering] using hen
      have hJ : J (restrict own H none) := hJfree fun j hj => by
        by_cases hji : j = i
        · subst hji; exact hl.1
        · exact hcheck hl.1 hl.2 j hj hji
      obtain ⟨h', hJ', a, b, e, f, g⟩ := hstep _ _ c' s' H' sd1 sd2 stp
        (by rw [if_pos' hen]; exact hJ)
      exact ⟨false, h', hJ', a, b, e, f, g, rfl⟩
  subst e
  let own' : Loc → Option Nat := fun l => if h' l ≠ none then some i
    else if hJ' l ≠ none then none else if own l = some i then none else own l
  obtain ⟨r1, r2, r3⟩ := reassign own own' H h' hJ' i keep (fun _ => rfl) d1 d2
  -- Lock status of thread i before and after.
  have hlen : (ts.set i ⟨c', s'⟩).length = ts.length := List.length_set ..
  have get_i : ∀ (h : i < (ts.set i ⟨c', s'⟩).length), (ts.set i ⟨c', s'⟩)[i] = ⟨c', s'⟩ :=
    fun _ => List.getElem_set_self ..
  have get_j : ∀ j (hj : j < (ts.set i ⟨c', s'⟩).length), j ≠ i →
      (ts.set i ⟨c', s'⟩)[j] = ts[j]'(by omega) :=
    fun j _ hji => List.getElem_set_ne (Ne.symm hji) ..
  have other_unl : ∀ j (hj : j < ts.length), j ≠ i → ts[j].cmd.locked = true →
      ts[i].cmd.locked = false ∧ c'.locked = false := by
    intro j hj hji hlj
    have hi_unl := hone j i hj hi hji hlj
    refine ⟨hi_unl, ?_⟩
    cases hc : c'.locked
    · rfl
    · exact absurd (hcheck hi_unl hc j hj hji) (by simp [hlj])
  refine ⟨own', ?_, ?_, ?_, ?_⟩
  · -- at most one thread holds the lock
    intro j k hj hk hjk hlj
    by_cases hji : j = i
    · subst hji
      have hki : k ≠ j := Ne.symm hjk
      rw [get_j k hk hki]
      rw [get_i hj] at hlj
      cases hc : ts[j].cmd.locked
      · exact hcheck hc hlj k (by omega) hki
      · exact hone j k hi (by omega) hjk hc
    · rw [get_j j hj hji] at hlj
      by_cases hki : k = i
      · subst hki; rw [get_i hk]; exact (other_unl j (by omega) hji hlj).2
      · rw [get_j k hk hki]; exact hone j k (by omega) (by omega) hjk hlj
  · -- lock free ⇒ the invariant's heap satisfies J
    intro hall
    have hc' : c'.locked = false := by have := hall i (by omega); rwa [get_i] at this
    rw [r3]
    cases hen : entering ts[i].cmd c'
    · simp only [hkeep, hen, Bool.not_false, ite_true]
      cases hlv : leaving ts[i].cmd c'
      · rw [if_neg' hlv] at hleave; subst hleave
        have hci : ts[i].cmd.locked = false := by
          cases hci : ts[i].cmd.locked
          · rfl
          · simp [leaving, hci, hc'] at hlv
        rw [emp_union]
        exact hJfree fun j hj => by
          by_cases hji : j = i
          · subst hji; exact hci
          · have := hall j (by omega); rwa [get_j j (by omega) hji] at this
      · rw [if_pos' hlv] at hleave
        have hci : ts[i].cmd.locked = true := by simp [leaving] at hlv; exact hlv.1
        rw [hJlocked i hi hci, union_emp]; exact hleave
    · simp [entering, hc'] at hen
  · -- lock held ⇒ the invariant's heap is empty
    intro j hj hlj
    rw [r3]
    by_cases hji : j = i
    · subst hji
      rw [get_i] at hlj
      have hlv : leaving ts[j].cmd c' = false := by simp [leaving, hlj]
      rw [if_neg' hlv] at hleave; subst hleave
      cases hen : entering ts[j].cmd c'
      · have hci : ts[j].cmd.locked = true := by simpa [entering, hlj] using hen
        simp [hkeep, hen, hJlocked j hi hci]
      · simp [hkeep, hen]
    · rw [get_j j hj hji] at hlj
      obtain ⟨hci, hc'⟩ := other_unl j (by omega) hji hlj
      have hlv : leaving ts[i].cmd c' = false := by simp [leaving, hci]
      rw [if_neg' hlv] at hleave; subst hleave
      have hen : entering ts[i].cmd c' = false := by simp [entering, hc']
      simp [hkeep, hen, hJlocked j (by omega) hlj]
  · -- every thread is still safe
    intro j hj
    by_cases hji : j = i
    · subst hji; rw [get_i, r1]; exact hs'
    · rw [get_j j hj hji, r2 j hji]
      exact safe_mono (by omega) (hsafe j (by omega))

theorem poolInv_steps {J : Inv} {Q : Nat → Assn} :
    ∀ {k n ts H ts' H'}, PoolInv J Q (n + k) ts H → MSteps k ts H ts' H' → PoolInv J Q n ts' H'
  | 0, _, _, _, _, _, inv, .refl => inv
  | k + 1, n, _, _, _, _, inv, .step st rest =>
    poolInv_steps (n := n) (k := k) (poolInv_step (n := n + k) (by simpa [Nat.add_assoc] using inv) st) rest

/-- **Soundness of CSL for PyL thread pools.**

Suppose each thread `i` satisfies `J ⊢ {P i} cmd_i {Q i}`, no thread starts
inside a `with` block, and the initial heap is divided by an ownership map
`own` so that thread `i`'s part satisfies `P i` and the unowned part satisfies
`J`. Then for every execution of any length:

* no thread faults (every attribute it touches exists);
* no two threads are ever about to touch the same attribute (no data races);
* if all threads have finished, the heap divides into parts satisfying each
  `Q i` and `J`. -/
theorem pool_sound {J : Inv} {P Q : Nat → Assn} {ts : Pool} {H : Heap}
    (own : Loc → Option Nat)
    (hv : ∀ i (hi : i < ts.length), Valid J (P i) ts[i].cmd (Q i))
    (hunl : ∀ i (hi : i < ts.length), ts[i].cmd.locked = false)
    (hJ : J (restrict own H none))
    (hP : ∀ i (hi : i < ts.length), P i ts[i].store (restrict own H (some i))) :
    ∀ k ts' H', MSteps k ts H ts' H' →
      ¬ Faults ts' H' ∧ ¬ Race ts' ∧
      ((∀ i (hi : i < ts'.length), ts'[i].cmd = .skip) →
        ∃ own' : Loc → Option Nat, J (restrict own' H' none) ∧
          ∀ i (hi : i < ts'.length), Q i ts'[i].store (restrict own' H' (some i))) := by
  intro k ts' H' run
  have inv0 : PoolInv J Q (1 + k) ts H :=
    ⟨own, fun i j hi _ _ hl => by simp [hunl i hi] at hl, fun _ => hJ,
      fun i hi hl => by simp [hunl i hi] at hl, fun i hi => hv i hi _ _ _ (hP i hi)⟩
  obtain ⟨own', _, hJf, _, hsafe⟩ := poolInv_steps inv0 run
  have acc_own : ∀ i (hi : i < ts'.length) l, ts'[i].cmd.acc ts'[i].store = some l →
      own' l = some i ∧ H' l ≠ none := by
    intro i hi l e
    obtain ⟨_, hacc, _⟩ := hsafe i hi
    have := hacc l e
    simp only [restrict] at this
    split at this
    · exact ⟨‹_›, this⟩
    · exact absurd rfl this
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, hi, l, e, hn⟩; exact (acc_own i hi l e).2 hn
  · rintro ⟨i, j, hi, hj, hij, l, ei, ej⟩
    have := (acc_own i hi l ei).1.symm.trans (acc_own j hj l ej).1
    exact hij (Option.some.inj this)
  · intro hall
    refine ⟨own', hJf fun i hi => by rw [hall i hi]; rfl, fun i hi => ?_⟩
    obtain ⟨hsk, _, _⟩ := hsafe i hi
    exact hsk (hall i hi)

end PyL
