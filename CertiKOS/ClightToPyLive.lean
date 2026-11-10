import CertiKOS.ClightToPy

/-!
# Carrying liveness from the C machine to the Python pool

`ClightToPy.lean` relates reachable states of the two machines. This file
carries **liveness** across the translation: a termination argument for the C
machine becomes a termination theorem for the Python pool under a fair
scheduler.

**What the C side supplies** (`LiveCert`). A potential `Φ` on C states (`G cs a Φ`)
and a set of *active* CPUs (`Act`):
* no C step increases `Φ`;
* a step of an active CPU strictly decreases it;
* steps of other CPUs leave an active CPU active;
* while some CPU is unfinished, some CPU is active.

This is the global form of the CertiKOS liveness argument. A spinning waiter
is not active and does not decrease `Φ`, but the CPU holding the current turn
is active. The ticket-lock certificate is in `TicketLive.lean`.

**What the translation adds.** A Python thread takes at most `S0 + 2` Python
steps in a row without a C step of its CPU (`mu`): one for the first half of a
`while`, and then the steps of one `with L:` block, whose body is loop-free and
has size at most `S0` (`ImplBound`).

**Fairness** (`Run.Fair K`): in every window of `K` consecutive steps, every
thread that is unfinished at the start of the window takes a step. This is an
assumption about the scheduler *and* about `L`: a thread blocked on `with L:`
must eventually get in.

**Theorems.**
* `fair_bound`: every `K`-fair run of the Python pool has fewer than
  `(S0 + 3) * K * (Φ₀ + 1)` steps.
* `rel_progress`: a reachable Python state where some thread is unfinished can
  always take a step (no deadlock), provided the C primitives never get stuck.

Together with `py_done`, every maximal fair run ends, after a bounded number of
steps, with every thread finished.
-/

namespace ClightToPy

open ClightL (Val Ident Locals Stmt Cont Config Prims)
open PyL (Var Store Heap Cmd Thread Pool MStep MSteps Step)

/-! ## Size, loop-freedom, and the stutter measure -/

def csize : Cmd → Nat
  | .skip => 1
  | .seq a b => csize a + csize b + 1
  | .ite _ a b => csize a + csize b + 1
  | .atomic c => csize c + 2
  | .inAtomic c => csize c + 1
  | _ => 2

def LoopFree : Cmd → Prop
  | .while _ _ => False
  | .seq a b => LoopFree a ∧ LoopFree b
  | .ite _ a b => LoopFree a ∧ LoopFree b
  | .atomic c => LoopFree c
  | .inAtomic c => LoopFree c
  | _ => True

/-- A step of a loop-free command stays loop-free and shrinks it. -/
theorem _root_.PyL.Step.lf_size {c s H c' s' H'} (h : Step c s H c' s' H') (hl : LoopFree c) :
    LoopFree c' ∧ csize c' < csize c := by
  induction h with
  | assign => exact ⟨trivial, by simp [csize]⟩
  | load => exact ⟨trivial, by simp [csize]⟩
  | store => exact ⟨trivial, by simp [csize]⟩
  | seqSkip => exact ⟨hl.2, by simp [csize]; omega⟩
  | seq _ ih =>
    obtain ⟨h1, h2⟩ := ih hl.1
    exact ⟨⟨h1, hl.2⟩, by simp [csize]; omega⟩
  | iteT => exact ⟨hl.1, by simp [csize]; omega⟩
  | iteF => exact ⟨hl.2, by simp [csize]; omega⟩
  | «while» => exact absurd hl id
  | atomic => exact ⟨hl, by simp [csize]⟩
  | inAtomic _ ih =>
    obtain ⟨h1, h2⟩ := ih hl
    exact ⟨h1, by simp [csize]; omega⟩
  | inAtomicSkip => exact ⟨trivial, by simp [csize]⟩

theorem PSteps.lf_size {c s H c' s' H'} (h : PSteps c s H c' s' H') (hl : LoopFree c) :
    LoopFree c' ∧ csize c' ≤ csize c := by
  induction h with
  | refl => exact ⟨hl, Nat.le_refl _⟩
  | step h _ ih =>
    obtain ⟨h1, h2⟩ := h.lf_size hl
    obtain ⟨h3, h4⟩ := ih h1
    exact ⟨h3, by omega⟩

/-- The leftmost command of a `;`-nest: what runs next. -/
def head : Cmd → Cmd
  | .seq a _ => head a
  | c => c

/-- How many more Python steps the thread can take before its CPU must take a
C step. -/
def mu (c : Cmd) : Nat :=
  match head c with
  | .while _ _ => 1
  | .atomic b => csize b + 2
  | .inAtomic b => csize b + 1
  | _ => 0

@[simp] theorem mu_seq (a b : Cmd) : mu (.seq a b) = mu a := rfl

/-- The primitive implementations are loop-free, of size at most `S0`. -/
def ImplBound {Pn : Type} (impl : Pn → List PyL.Expr → Var → Cmd) (S0 : Nat) : Prop :=
  ∀ p args x, LoopFree (impl p args x) ∧ csize (impl p args x) ≤ S0

section Plug
variable {Pn : Type} {impl : Pn → List PyL.Expr → Var → Cmd}

theorem mu_plug (k : Cont Pn) (c : Cmd) : mu (plug impl k c) = mu c := by
  induction k generalizing c with
  | stop => rfl
  | seq _ _ ih => rw [plug, ih]; rfl
  | loop _ _ _ ih => rw [plug, ih]; rfl

theorem mu_tr {S0 : Nat} (hB : ImplBound impl S0) (s : Stmt Pn) : mu (tr impl s) ≤ S0 + 2 := by
  induction s with
  | seq a b iha _ => simpa [tr] using iha
  | call x p args => simp only [tr, mu, head]; have := (hB p (args.map trE) x).2; omega
  | «while» => simp [tr, mu, head]
  | _ => simp [tr, mu, head]

end Plug

/-! ## Counted and labelled C steps -/

section Labelled
variable {Pn Abs : Type}

/-- `n` steps of one ClightL configuration. -/
inductive StarN (Q : Prims Pn Abs) : Nat → Config Pn Abs → Config Pn Abs → Prop
  | refl (c) : StarN Q 0 c c
  | step {n c c₁ c₂} : ClightL.step Q c = some c₁ → StarN Q n c₁ c₂ → StarN Q (n + 1) c c₂

theorem StarN.trans {Q : Prims Pn Abs} {n m : Nat} {a b c : Config Pn Abs}
    (h₁ : StarN Q n a b) (h₂ : StarN Q m b c) : StarN Q (n + m) a c := by
  induction h₁ with
  | refl => simpa using h₂
  | step h _ ih => rw [Nat.add_right_comm]; exact .step h (ih h₂)

theorem StarN.to_star {Q : Prims Pn Abs} {n : Nat} {a b : Config Pn Abs} (h : StarN Q n a b) :
    ClightL.Star Q a b := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step h ih

theorem StarN.of_star {Q : Prims Pn Abs} {a b : Config Pn Abs} (h : ClightL.Star Q a b) :
    ∃ n, StarN Q n a b := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | step h _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step h hn⟩

/-- One step of CPU `i` of the C machine. -/
def CStepI (P : Nat → Prims Pn Abs) (i : Nat) (cs : List (CThread Pn)) (a : Abs)
    (cs' : List (CThread Pn)) (a' : Abs) : Prop :=
  ∃ (hi : i < cs.length) (c' : Config Pn Abs),
    ClightL.step (P i) (cs[i].cfg a) = some c' ∧ cs' = cs.set i (thr c') ∧ a' = c'.abs

/-- `n` steps of CPU `i`. -/
inductive CStepsI (P : Nat → Prims Pn Abs) (i : Nat) :
    Nat → List (CThread Pn) → Abs → List (CThread Pn) → Abs → Prop
  | refl {cs a} : CStepsI P i 0 cs a cs a
  | step {n cs a cs₁ a₁ cs' a'} : CStepI P i cs a cs₁ a₁ → CStepsI P i n cs₁ a₁ cs' a' →
      CStepsI P i (n + 1) cs a cs' a'

theorem starN_csteps {P : Nat → Prims Pn Abs} (i : Nat) {n : Nat} {c c' : Config Pn Abs}
    (h : StarN (P i) n c c') :
    ∀ (cs : List (CThread Pn)) (hi : i < cs.length), c = cs[i].cfg c.abs →
      CStepsI P i n cs c.abs (cs.set i (thr c')) c'.abs := by
  induction h with
  | refl c =>
    intro cs hi he
    have : thr c = cs[i] := by rw [he]; rfl
    rw [this, List.set_getElem_self]; exact .refl
  | @step n c₁ c₂ c₃ hs _ ih =>
    intro cs hi he
    have h1 : CStepI P i cs c₁.abs (cs.set i (thr c₂)) c₂.abs :=
      ⟨hi, c₂, by rw [← he]; exact hs, rfl, rfl⟩
    have h2 := ih (cs.set i (thr c₂)) (by simpa using hi)
      (by simp only [List.getElem_set_self]; rfl)
    rw [List.set_set] at h2
    exact .step h1 h2

theorem CStepI.length {P : Nat → Prims Pn Abs} {i cs a cs' a'} (h : CStepI P i cs a cs' a') :
    cs'.length = cs.length := by
  obtain ⟨_, _, _, rfl, _⟩ := h; simp

theorem CStepI.other {P : Nat → Prims Pn Abs} {i cs a cs' a'} (h : CStepI P i cs a cs' a')
    {d : Nat} (hd : d < cs.length) (hne : i ≠ d) : ∃ hd' : d < cs'.length, cs'[d] = cs[d] := by
  obtain ⟨_, _, _, rfl, _⟩ := h
  exact ⟨by simpa using hd, by simp [hne]⟩

theorem CStep.labelled {P : Nat → Prims Pn Abs} {cs a cs' a'} (h : CStep P cs a cs' a') :
    ∃ i, CStepI P i cs a cs' a' := by
  cases h with
  | step i hi h => exact ⟨i, hi, _, h, rfl, rfl⟩

/-- A CPU has finished its program. -/
def Done (t : CThread Pn) : Prop := t.stmt = .skip ∧ t.cont = .stop

end Labelled

/-! ## The C-side liveness certificate -/

section Cert
variable {Pn Abs : Type}

/-- A termination certificate for the C machine (see the module doc). -/
structure LiveCert (P : Nat → Prims Pn Abs) (G : List (CThread Pn) → Abs → Nat → Prop)
    (Act : List (CThread Pn) → Abs → Nat → Prop) : Prop where
  le : ∀ {cs a Φ i cs' a'}, G cs a Φ → CStepI P i cs a cs' a' → ∃ Φ', Φ' ≤ Φ ∧ G cs' a' Φ'
  lt : ∀ {cs a Φ i cs' a'}, G cs a Φ → Act cs a i → CStepI P i cs a cs' a' →
    ∃ Φ', Φ' < Φ ∧ G cs' a' Φ'
  persist : ∀ {cs a Φ i d cs' a'}, G cs a Φ → Act cs a d → CStepI P i cs a cs' a' → i ≠ d →
    Act cs' a' d
  act : ∀ {cs a Φ}, G cs a Φ → (∃ i, ∃ hi : i < cs.length, ¬ Done cs[i]) → ∃ d, Act cs a d
  act_lt : ∀ {cs a Φ d}, G cs a Φ → Act cs a d → ∃ hd : d < cs.length, ¬ Done cs[d]

variable {P : Nat → Prims Pn Abs} {G : List (CThread Pn) → Abs → Nat → Prop}
  {Act : List (CThread Pn) → Abs → Nat → Prop}

theorem LiveCert.steps (C : LiveCert P G Act) {i n cs a cs' a'} (h : CStepsI P i n cs a cs' a') :
    ∀ {Φ}, G cs a Φ → ∃ Φ', Φ' ≤ Φ ∧ G cs' a' Φ' ∧ (0 < n → Act cs a i → Φ' < Φ) ∧
      (∀ d, d ≠ i → Act cs a d → Act cs' a' d) := by
  induction h with
  | refl => intro Φ hG; exact ⟨Φ, Nat.le_refl _, hG, by omega, fun _ _ h => h⟩
  | @step _ cs a cs₁ a₁ _ _ h₁ _ ih =>
    intro Φ hG
    have hp : ∀ d, d ≠ i → Act cs a d → Act cs₁ a₁ d := fun d hd ha =>
      C.persist hG ha h₁ (Ne.symm hd)
    by_cases ha : Act cs a i
    · obtain ⟨Φ₁, hlt, hG₁⟩ := C.lt hG ha h₁
      obtain ⟨Φ₂, hle₂, hG₂, _, hp₂⟩ := ih hG₁
      exact ⟨Φ₂, by omega, hG₂, fun _ _ => by omega, fun d hd had => hp₂ d hd (hp d hd had)⟩
    · obtain ⟨Φ₁, hle₁, hG₁⟩ := C.le hG h₁
      obtain ⟨Φ₂, hle₂, hG₂, _, hp₂⟩ := ih hG₁
      exact ⟨Φ₂, by omega, hG₂, fun _ h => absurd h ha, fun d hd had => hp₂ d hd (hp d hd had)⟩

end Cert

/-! ## The simulation step, with stutter information -/

section Machine
variable {Pn Abs : Type} {impl : Pn → List PyL.Expr → Var → Cmd}
  {Rsv : Var → Prop} {arity : Pn → Nat} {P : Nat → Prims Pn Abs} {R : Abs → Heap → Prop}

theorem StarN.snoc {Q : Prims Pn Abs} {n : Nat} {a b c : Config Pn Abs} (h : StarN Q n a b)
    (h' : ClightL.step Q b = some c) : StarN Q (n + 1) a c := h.trans (.step h' (.refl _))

theorem mu_embed (t : CThread Pn) : mu (embed impl t) = mu (tr impl t.stmt) := mu_plug _ _

/-- `thread_step_out`, counting the C steps: either at least one, or the
Python step shrank `mu`. -/
theorem thread_step_out' (i : Nat) {t : CThread Pn} {th : Thread} {a : Abs} {H : Heap}
    {c' : Cmd} {s' : Store} {H' : Heap}
    (hwf : CWF Rsv arity t) (hO : Out impl Rsv t th) (hs : Step th.cmd th.store H c' s' H') :
    H' = H ∧ ∃ (t' : CThread Pn) (n : Nat), StarN (P i) n (t.cfg a) (t'.cfg a) ∧
      (0 < n ∨ mu c' < mu th.cmd) ∧
      (Out impl Rsv t' ⟨c', s'⟩ ∨
        (c'.locked = true ∧ (R a H → InBlk impl Rsv R t' a ⟨c', s'⟩ H'))) := by
  cases hO with
  | @here s hA =>
    obtain ⟨⟨stmt, k, σ⟩, hst, he, hl, hn⟩ :=
      normalize (P := P) (impl := impl) i a t.stmt t.cont t.locals
    have hst : ClightL.Star (P i) (t.cfg a) (CThread.cfg ⟨stmt, k, σ⟩ a) := hst
    obtain ⟨n0, hn0⟩ := StarN.of_star hst
    have hw : CWF Rsv arity ⟨stmt, k, σ⟩ := by simpa using star_wf hst (by simpa using hwf)
    simp only at hl; subst hl
    have hmu : mu (embed impl t) = mu (tr impl stmt) := by
      have := congrArg mu he
      simp only [embed, mu_plug] at this ⊢; exact this.symm
    have hs : Step (embed impl ⟨stmt, k, t.locals⟩) s H c' s' H' := by rw [he]; exact hs
    cases stmt with
    | skip =>
      cases k with
      | stop => exact absurd hs Step.no_skip
      | seq s₂ k =>
        obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .seqSkip)
        exact ⟨rfl, ⟨s₂, k, t.locals⟩, _, hn0.snoc rfl, .inl (by omega), .inl (.here hA)⟩
      | loop e b k =>
        obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .seqSkip)
        exact ⟨rfl, ⟨.while e b, k, t.locals⟩, _, hn0.snoc rfl, .inl (by omega), .inl (.here hA)⟩
    | assign x e =>
      obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .assign)
      refine ⟨rfl, ⟨.skip, k, t.locals.set x (e.eval t.locals)⟩, _, hn0.snoc rfl, .inl (by omega),
        .inl ?_⟩
      have := Out.here (impl := impl) (t := ⟨.skip, k, t.locals.set x (e.eval t.locals)⟩)
        (agree_set hA x (e.eval t.locals))
      rwa [← trE_eval hA e hw.1.2] at this
    | seq _ _ => exact absurd rfl (hn _ _)
    | ite e b₁ b₂ =>
      by_cases hz : e.eval t.locals = 0
      · obtain ⟨rfl, rfl, rfl⟩ :=
          Step.det hs (plug_step (impl := impl) k (.iteF ((trE_eval_zero hA hw.1.1).2 hz)))
        exact ⟨rfl, ⟨b₂, k, t.locals⟩, _,
          hn0.snoc (by rw [cstep_ite, ite_eq_left hz]), .inl (by omega), .inl (.here hA)⟩
      · obtain ⟨rfl, rfl, rfl⟩ :=
          Step.det hs (plug_step (impl := impl) k (.iteT (mt (trE_eval_zero hA hw.1.1).1 hz)))
        exact ⟨rfl, ⟨b₁, k, t.locals⟩, _,
          hn0.snoc (by rw [cstep_ite, ite_eq_right hz]), .inl (by omega), .inl (.here hA)⟩
    | «while» e b =>
      obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .while)
      refine ⟨rfl, ⟨.while e b, k, t.locals⟩, _, hn0, .inr ?_, .inl (.wmid rfl hA)⟩
      rw [hmu, mu_plug]; simp [tr, mu, head]
    | call x p args =>
      obtain ⟨rfl, rfl, rfl⟩ := Step.det hs (plug_step (impl := impl) k .atomic)
      refine ⟨rfl, ⟨.call x p args, k, t.locals⟩, _, hn0, .inr ?_,
        .inr ⟨by simp [plug_locked, Cmd.locked], ?_⟩⟩
      · rw [hmu, mu_plug]; simp [tr, mu, head]
      · intro hR
        exact ⟨x, p, args, _, _, _, rfl, rfl, hA, hR, .refl⟩
  | @wmid e b s hwh hA =>
    obtain ⟨stmt, k, σ⟩ := t
    simp only at hwh hA; subst hwh
    have he : EWF Rsv e := hwf.1.1
    by_cases hz : e.eval σ = 0
    · obtain ⟨rfl, rfl, rfl⟩ :=
        Step.det hs (plug_step (impl := impl) k (.iteF ((trE_eval_zero hA he).2 hz)))
      exact ⟨rfl, ⟨.skip, k, σ⟩, 1, .step (by rw [cstep_while, ite_eq_left hz]) (.refl _),
        .inl (by omega), .inl (.here hA)⟩
    · obtain ⟨rfl, rfl, rfl⟩ :=
        Step.det hs (plug_step (impl := impl) k (.iteT (mt (trE_eval_zero hA he).1 hz)))
      exact ⟨rfl, ⟨b, .loop e b k, σ⟩, 1, .step (by rw [cstep_while, ite_eq_right hz]) (.refl _),
        .inl (by omega), .inl (.here hA)⟩

/-- Inside a block, a step that stays inside shrinks `mu`. -/
theorem mu_blk {S0 : Nat} (hB : ImplBound impl S0) {t : CThread Pn} {a : Abs} {th : Thread}
    {H : Heap} {c' : Cmd} {s' : Store} {H' : Heap}
    (hIn : InBlk impl Rsv R t a th H) (hs : Step th.cmd th.store H c' s' H')
    (hl : c'.locked = true) : mu c' < mu th.cmd := by
  obtain ⟨x, p, args, B, s₀, H₀, -, hc, -, -, hps⟩ := hIn
  rw [hc] at hs ⊢
  obtain ⟨c'', hstep, rfl⟩ := plug_inv _ (by simp) hs
  cases hstep with
  | inAtomic h =>
    have hlf := (hps.lf_size (hB p (args.map trE) x).1).1
    have := (h.lf_size hlf).2
    rw [mu_plug, mu_plug]; simp only [mu, head]; omega
  | inAtomicSkip => rw [plug_locked] at hl; cases hl

/-- `mu` is bounded on related states. -/
theorem rel_mu_le {S0 : Nat} (hB : ImplBound impl S0) {cs : List (CThread Pn)} {a : Abs}
    {ts : Pool} {H : Heap} (hR : Rel impl Rsv arity R cs a ts H) (i : Nat) (hi : i < ts.length) :
    mu ts[i].cmd ≤ S0 + 2 := by
  rcases hR.thr i (hR.len ▸ hi) hi with hO | hIn
  · generalize ts[i] = th at hO ⊢
    cases hO with
    | here => rw [mu_embed]; exact mu_tr hB _
    | wmid => rw [mu_plug]; simp [mu, head]
  · obtain ⟨x, p, args, B, s₀, H₀, -, hc, -, -, hps⟩ := hIn
    rw [hc, mu_plug]; simp only [mu, head]
    have h1 := (hps.lf_size (hB p (args.map trE) x).1).2
    have h2 := (hB p (args.map trE) x).2
    omega

/-- A finished Python thread is a finished C CPU. -/
theorem rel_done {cs : List (CThread Pn)} {a : Abs} {ts : Pool} {H : Heap}
    (hR : Rel impl Rsv arity R cs a ts H) (i : Nat) (hi : i < cs.length) (ht : i < ts.length)
    (hd : ts[i].cmd = .skip) : Done cs[i] := by
  rcases hR.thr i hi ht with hO | hB
  · generalize ts[i] = th at hO hd
    cases hO with
    | here hA =>
      obtain ⟨hk, hs⟩ := plug_eq_skip hd
      exact ⟨tr_eq_skip hs, hk⟩
    | wmid => exact absurd (plug_eq_skip hd).2 (by simp)
  · obtain ⟨_, _, _, _, _, _, _, hc, _⟩ := hB
    rw [hd] at hc
    exact absurd (plug_eq_skip hc.symm).2 (by simp)

/-- A finished C CPU is a finished Python thread. -/
theorem rel_done_rev {cs : List (CThread Pn)} {a : Abs} {ts : Pool} {H : Heap}
    (hR : Rel impl Rsv arity R cs a ts H) (i : Nat) (hi : i < cs.length) (ht : i < ts.length)
    (hd : Done cs[i]) : ts[i].cmd = .skip := by
  obtain ⟨h1, h2⟩ := hd
  rcases hR.thr i hi ht with hO | hB
  · generalize cs[i] = t at hO h1 h2
    generalize ts[i] = th at hO
    cases hO with
    | here => obtain ⟨stmt, k, σ⟩ := t; simp only at h1 h2; subst h1; subst h2; rfl
    | wmid hw => rw [h1] at hw; cases hw
  · obtain ⟨_, _, _, _, _, _, hst, _⟩ := hB
    rw [h1] at hst; cases hst

/-- **The simulation step, labelled.** A Python step of thread `i` is matched
by `n` C steps of CPU `i`; if `n = 0`, the thread's `mu` went down. -/
theorem rel_stepI (hP : PrimOK impl Rsv arity P R) {S0 : Nat} (hB : ImplBound impl S0)
    {cs : List (CThread Pn)} {a : Abs} {ts : Pool} {H : Heap}
    (hR : Rel impl Rsv arity R cs a ts H) (i : Nat) (hi : i < ts.length) {c' : Cmd} {s' : Store}
    {H' : Heap} (hs : Step ts[i].cmd ts[i].store H c' s' H')
    (hlk : ts[i].cmd.locked = false → c'.locked = true →
      ∀ j (hj : j < ts.length), j ≠ i → ts[j].cmd.locked = false) :
    ∃ n cs' a', CStepsI P i n cs a cs' a' ∧
      Rel impl Rsv arity R cs' a' (ts.set i ⟨c', s'⟩) H' ∧ (0 < n ∨ mu c' < mu ts[i].cmd) := by
  have hci : i < cs.length := hR.len ▸ hi
  rcases hR.thr i hci hi with hO | hB'
  · -- outside any block
    obtain ⟨rfl, t', n, hst, hprog, hres⟩ := thread_step_out' (P := P) (a := a) i (hR.wf i hci) hO hs
    have hC : CStepsI P i n cs a (cs.set i t') a := starN_csteps i hst cs hci rfl
    have hw' : CWF Rsv arity t' := by simpa using star_wf hst.to_star (by simpa using hR.wf i hci)
    have hil : ts[i].cmd.locked = false := out_locked hO
    refine ⟨n, _, _, hC, ⟨by simp [hR.len], ?_, ?_, ?_, ?_⟩, hprog⟩
    · intro j hj
      rw [List.getElem_set]; split
      · rename_i hij; subst hij; exact hw'
      · exact hR.wf j (by simpa using hj)
    · intro j hj hj'
      simp only [List.getElem_set]; split
      · rename_i hij; subst hij
        rcases hres with h | ⟨hl, hb⟩
        · exact .inl h
        · refine .inr (hb (hR.heap fun j hj => ?_))
          by_cases hji : j = i
          · subst hji; exact hil
          · exact hlk hil hl j hj hji
      · exact hR.thr j (by simpa using hj) (by simpa using hj')
    · intro hall; apply hR.heap; intro j hj
      by_cases hji : j = i
      · subst hji; exact hil
      · have := hall j (by simpa using hj)
        simpa [List.getElem_set, Ne.symm hji] using this
    · intro j l hj hl hjl hll
      rw [List.getElem_set] at hjl hll
      by_cases hij : i = j <;> by_cases hil' : i = l
      · exact hij.symm.trans hil'
      · rw [ite_eq_left hij] at hjl; rw [ite_eq_right hil'] at hll
        rw [hlk hil hjl l (by simpa using hl) (Ne.symm hil')] at hll; cases hll
      · rw [ite_eq_right hij] at hjl; rw [ite_eq_left hil'] at hll
        rw [hlk hil hll j (by simpa using hj) (Ne.symm hij)] at hjl; cases hjl
      · rw [ite_eq_right hij] at hjl; rw [ite_eq_right hil'] at hll
        exact hR.one j l (by simpa using hj) (by simpa using hl) hjl hll
  · -- inside the block
    have hil : ts[i].cmd.locked = true := inBlk_locked hB'
    have hO' : ∀ j (hj : j < cs.length) (hj' : j < ts.length), j ≠ i →
        Out impl Rsv cs[j] ts[j] := by
      intro j hj hj' hne
      rcases hR.thr j hj hj' with h | h
      · exact h
      · exact absurd (hR.one j i hj' hi (inBlk_locked h) hil) hne
    rcases thread_step_blk hP i (hR.wf i hci) hB' hs with hB'' | ⟨c₁, hc₁, hO₁, hR₁⟩
    · refine ⟨0, cs, a, .refl, ⟨by simp [hR.len], hR.wf, ?_, ?_, ?_⟩,
        .inr (mu_blk hB hB' hs (inBlk_locked hB''))⟩
      · intro j hj hj'
        simp only [List.getElem_set]; split
        · rename_i hij; subst hij; exact .inr hB''
        · exact .inl (hO' j hj (by simpa using hj') (Ne.symm ‹_›))
      · intro hall
        have := hall i (by simpa using hi)
        simp only [List.getElem_set_self] at this
        rw [inBlk_locked hB''] at this; cases this
      · intro j l hj hl hjl hll
        rw [List.getElem_set] at hjl hll
        by_cases hij : i = j <;> by_cases hil' : i = l
        · exact hij.symm.trans hil'
        · rw [ite_eq_right hil'] at hll
          exact absurd (hR.one l i (by simpa using hl) hi hll hil) (Ne.symm hil')
        · rw [ite_eq_right hij] at hjl
          exact absurd (hR.one j i (by simpa using hj) hi hjl hil) (Ne.symm hij)
        · rw [ite_eq_right hij] at hjl; rw [ite_eq_right hil'] at hll
          exact hR.one j l (by simpa using hj) (by simpa using hl) hjl hll
    · refine ⟨1, cs.set i (thr c₁), c₁.abs, .step ⟨hci, c₁, hc₁, rfl, rfl⟩ .refl,
        ⟨by simp [hR.len], ?_, ?_, fun _ => hR₁, ?_⟩, .inl Nat.one_pos⟩
      · intro j hj
        rw [List.getElem_set]; split
        · rename_i hij; subst hij; exact step_wf (by simpa using hR.wf i hci) hc₁
        · exact hR.wf j (by simpa using hj)
      · intro j hj hj'
        simp only [List.getElem_set]; split
        · rename_i hij; subst hij; exact .inl hO₁
        · exact .inl (hO' j (by simpa using hj) (by simpa using hj') (Ne.symm ‹_›))
      · intro j l hj hl hjl hll
        rw [List.getElem_set] at hjl hll
        by_cases hij : i = j <;> by_cases hil' : i = l
        · exact hij.symm.trans hil'
        · rw [ite_eq_left hij, out_locked hO₁] at hjl; cases hjl
        · rw [ite_eq_left hil', out_locked hO₁] at hll; cases hll
        · rw [ite_eq_right hij] at hjl; rw [ite_eq_right hil'] at hll
          exact hR.one j l (by simpa using hj) (by simpa using hl) hjl hll

end Machine

/-! ## Runs of the Python pool, and fairness -/

/-- Pool step by thread `i`. -/
def MStepI (i : Nat) (ts : Pool) (H : Heap) (ts' : Pool) (H' : Heap) : Prop :=
  ∃ (hi : i < ts.length) (c' : Cmd) (s' : Store), Step ts[i].cmd ts[i].store H c' s' H' ∧
    (ts[i].cmd.locked = false → c'.locked = true →
      ∀ j (hj : j < ts.length), j ≠ i → ts[j].cmd.locked = false) ∧
    ts' = ts.set i ⟨c', s'⟩

theorem MStepI.mstep {i ts H ts' H'} (h : MStepI i ts H ts' H') : MStep ts H ts' H' := by
  obtain ⟨hi, c', s', hs, hlk, rfl⟩ := h; exact .step i hi hs hlk

theorem MStep.labelled {ts H ts' H'} (h : MStep ts H ts' H') : ∃ i, MStepI i ts H ts' H' := by
  cases h with
  | step i hi hs hlk => exact ⟨i, hi, _, _, hs, hlk, rfl⟩

theorem MStepI.length {i ts H ts' H'} (h : MStepI i ts H ts' H') : ts'.length = ts.length := by
  obtain ⟨_, _, _, _, _, rfl⟩ := h; simp

/-- A finite run of the pool: states `0..len`, and the thread `lab n` that
moves from state `n` to `n + 1`. -/
structure Run where
  pool : Nat → Pool
  heap : Nat → Heap
  lab : Nat → Nat
  len : Nat
  step : ∀ n, n < len → MStepI (lab n) (pool n) (heap n) (pool (n + 1)) (heap (n + 1))

/-- **Fairness.** In every window of `K` consecutive steps, every thread that
is unfinished at the start of the window takes at least one step. -/
def Run.Fair (r : Run) (K : Nat) : Prop :=
  ∀ n, n + K ≤ r.len → ∀ i (hi : i < (r.pool n).length), (r.pool n)[i].cmd ≠ .skip →
    ∃ m, n ≤ m ∧ m < n + K ∧ r.lab m = i

theorem Run.msteps_from (r : Run) : ∀ j m, m + j ≤ r.len →
    MSteps j (r.pool m) (r.heap m) (r.pool (m + j)) (r.heap (m + j))
  | 0, m, _ => .refl
  | j + 1, m, h => by
    have := r.msteps_from j (m + 1) (by omega)
    rw [show m + 1 + j = m + (j + 1) by omega] at this
    exact .step (r.step m (by omega)).mstep this

/-- A run is an execution of the pool. -/
theorem Run.msteps (r : Run) : MSteps r.len (r.pool 0) (r.heap 0) (r.pool r.len) (r.heap r.len) := by
  simpa using r.msteps_from r.len 0 (by omega)

/-- The command of thread `d` (`skip` if there is none). -/
def cmdAt (ts : Pool) (d : Nat) : Cmd := (ts[d]?.map Thread.cmd).getD .skip

theorem cmdAt_eq {ts : Pool} {d : Nat} (h : d < ts.length) : cmdAt ts d = ts[d].cmd := by
  simp [cmdAt, h]

theorem cmdAt_set_ne {ts : Pool} {i d : Nat} (x : Thread) (h : i ≠ d) :
    cmdAt (ts.set i x) d = cmdAt ts d := by
  simp [cmdAt, h]

theorem cmdAt_set_eq {ts : Pool} {d : Nat} (x : Thread) (h : d < ts.length) :
    cmdAt (ts.set d x) d = x.cmd := by
  simp [cmdAt, h]

/-- Steps of thread `d` among the `j` steps from `m`. -/
def cnt (lab : Nat → Nat) (d m : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => cnt lab d m j + if lab (m + j) = d then 1 else 0

theorem cnt_pos {lab : Nat → Nat} {d m k : Nat} (hk : lab k = d) :
    ∀ j, m ≤ k → k < m + j → 1 ≤ cnt lab d m j
  | 0, h1, h2 => by omega
  | j + 1, h1, h2 => by
    simp only [cnt]
    by_cases hkj : k = m + j
    · subst hkj; simp [hk]
    · have := cnt_pos hk j h1 (by omega); omega

/-! ## Rounds: in `(S + 1) * K` steps, the potential goes down -/

section Rounds
variable {Pn Abs : Type} {impl : Pn → List PyL.Expr → Var → Cmd}
  {Rsv : Var → Prop} {arity : Pn → Nat} {P : Nat → Prims Pn Abs} {R : Abs → Heap → Prop}
  {G : List (CThread Pn) → Abs → Nat → Prop} {Act : List (CThread Pn) → Abs → Nat → Prop}

/-- One pool step, seen from the C side. -/
theorem one_step (hP : PrimOK impl Rsv arity P R) {S0 : Nat} (hB : ImplBound impl S0)
    (C : LiveCert P G Act) (r : Run) {m : Nat} (hm : m < r.len) {cs : List (CThread Pn)} {a : Abs}
    {Φ : Nat} (hR : Rel impl Rsv arity R cs a (r.pool m) (r.heap m)) (hG : G cs a Φ) :
    ∃ cs' a' Φ', Rel impl Rsv arity R cs' a' (r.pool (m + 1)) (r.heap (m + 1)) ∧ G cs' a' Φ' ∧
      Φ' ≤ Φ ∧ ∀ d, Act cs a d →
        (r.lab m = d → Φ' < Φ ∨ (Act cs' a' d ∧
          mu (cmdAt (r.pool (m + 1)) d) < mu (cmdAt (r.pool m) d))) ∧
        (r.lab m ≠ d → Act cs' a' d ∧ cmdAt (r.pool (m + 1)) d = cmdAt (r.pool m) d) := by
  obtain ⟨hi, c', s', hs, hlk, heq⟩ := r.step m hm
  obtain ⟨n, cs', a', hC, hR', hprog⟩ := rel_stepI hP hB hR _ hi hs hlk
  obtain ⟨Φ', hle, hG', hlt, hper⟩ := C.steps hC hG
  rw [← heq] at hR'
  refine ⟨cs', a', Φ', hR', hG', hle, fun d ha => ⟨fun hd => ?_, fun hd => ?_⟩⟩
  · subst hd
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      cases hC
      refine .inr ⟨ha, ?_⟩
      rw [heq, cmdAt_set_eq _ hi, cmdAt_eq hi]
      exact hprog.resolve_left (by omega)
    · exact .inl (hlt hpos ha)
  · exact ⟨hper d (Ne.symm hd) ha, by rw [heq, cmdAt_set_ne _ hd]⟩

variable (impl Rsv arity R G Act) in
/-- Already below the starting potential. -/
def St1 (r : Run) (Φn m : Nat) : Prop :=
  ∃ cs a Φ, Rel impl Rsv arity R cs a (r.pool m) (r.heap m) ∧ G cs a Φ ∧ Φ < Φn

variable (impl Rsv arity R G Act) in
/-- Not yet: `d` is still active, and has used `c` of its stutter budget `S`. -/
def St2 (r : Run) (Φn S d m c : Nat) : Prop :=
  ∃ cs a Φ, Rel impl Rsv arity R cs a (r.pool m) (r.heap m) ∧ G cs a Φ ∧ Act cs a d ∧
    Φ ≤ Φn ∧ mu (cmdAt (r.pool m) d) + c ≤ S

theorem prop_one (hP : PrimOK impl Rsv arity P R) {S0 : Nat} (hB : ImplBound impl S0)
    (C : LiveCert P G Act) (r : Run) {Φn S d m c : Nat} (hm : m < r.len)
    (h : St1 impl Rsv arity R G r Φn m ∨ St2 impl Rsv arity R G Act r Φn S d m c) :
    St1 impl Rsv arity R G r Φn (m + 1) ∨
      St2 impl Rsv arity R G Act r Φn S d (m + 1) (c + if r.lab m = d then 1 else 0) := by
  rcases h with ⟨cs, a, Φ, hR, hG, hlt⟩ | ⟨cs, a, Φ, hR, hG, ha, hle, hmu⟩
  · obtain ⟨cs', a', Φ', hR', hG', hle', -⟩ := one_step hP hB C r hm hR hG
    exact .inl ⟨cs', a', Φ', hR', hG', by omega⟩
  · obtain ⟨cs', a', Φ', hR', hG', hle', hd⟩ := one_step hP hB C r hm hR hG
    obtain ⟨hsame, hother⟩ := hd d ha
    by_cases hl : r.lab m = d
    · rcases hsame hl with hlt | ⟨ha', hmu'⟩
      · exact .inl ⟨cs', a', Φ', hR', hG', by omega⟩
      · exact .inr ⟨cs', a', Φ', hR', hG', ha', by omega, by simp only [hl, ite_true]; omega⟩
    · obtain ⟨ha', heq⟩ := hother hl
      exact .inr ⟨cs', a', Φ', hR', hG', ha', by omega, by simp only [hl, ite_false]; rw [heq]; omega⟩

theorem prop_many (hP : PrimOK impl Rsv arity P R) {S0 : Nat} (hB : ImplBound impl S0)
    (C : LiveCert P G Act) (r : Run) {Φn S d : Nat} :
    ∀ j m c, m + j ≤ r.len →
      (St1 impl Rsv arity R G r Φn m ∨ St2 impl Rsv arity R G Act r Φn S d m c) →
      St1 impl Rsv arity R G r Φn (m + j) ∨
        St2 impl Rsv arity R G Act r Φn S d (m + j) (c + cnt r.lab d m j)
  | 0, m, c, _, h => by simpa [cnt] using h
  | j + 1, m, c, hj, h => by
    have ih := prop_many hP hB C r j m c (by omega) h
    have := prop_one hP hB C r (c := c + cnt r.lab d m j) (by omega) ih
    rw [show m + (j + 1) = m + j + 1 by omega]
    simpa only [cnt, Nat.add_assoc] using this

theorem st1_many (hP : PrimOK impl Rsv arity P R) {S0 : Nat} (hB : ImplBound impl S0)
    (C : LiveCert P G Act) (r : Run) {Φn : Nat} :
    ∀ j m, m + j ≤ r.len → St1 impl Rsv arity R G r Φn m → St1 impl Rsv arity R G r Φn (m + j)
  | 0, m, _, h => h
  | j + 1, m, hj, h => by
    obtain ⟨cs, a, Φ, hR, hG, hlt⟩ := st1_many hP hB C r j m (by omega) h
    obtain ⟨cs', a', Φ', hR', hG', hle', -⟩ := one_step hP hB C r (m := m + j) (by omega) hR hG
    exact ⟨cs', a', Φ', by rwa [← Nat.add_assoc], hG', by omega⟩

theorem St2.mono {r : Run} {Φn S d m c c' : Nat} (h : St2 impl Rsv arity R G Act r Φn S d m c)
    (hc : c' ≤ c) : St2 impl Rsv arity R G Act r Φn S d m c' := by
  obtain ⟨cs, a, Φ, hR, hG, ha, hle, hmu⟩ := h
  exact ⟨cs, a, Φ, hR, hG, ha, hle, by omega⟩

/-- One window of `K` steps: an active thread steps at least once. -/
theorem window (hP : PrimOK impl Rsv arity P R) {S0 : Nat} (hB : ImplBound impl S0)
    (C : LiveCert P G Act) (r : Run) {K : Nat} (hF : r.Fair K) {Φn S d m c : Nat}
    (hm : m + K ≤ r.len)
    (h : St1 impl Rsv arity R G r Φn m ∨ St2 impl Rsv arity R G Act r Φn S d m c) :
    St1 impl Rsv arity R G r Φn (m + K) ∨
      St2 impl Rsv arity R G Act r Φn S d (m + K) (c + 1) := by
  rcases h with h1 | h2
  · exact .inl (st1_many hP hB C r K m hm h1)
  · obtain ⟨cs, a, Φ, hR, hG, ha, hle, hmu⟩ := h2
    obtain ⟨hd, hnd⟩ := C.act_lt hG ha
    have ht : d < (r.pool m).length := hR.len ▸ hd
    have hns : (r.pool m)[d].cmd ≠ .skip := fun h => hnd (rel_done hR d hd ht h)
    obtain ⟨k, hk1, hk2, hk⟩ := hF m hm d ht hns
    have hc := cnt_pos hk K hk1 hk2
    rcases prop_many hP hB C r (S := S) (d := d) (c := c) K m hm
      (.inr ⟨cs, a, Φ, hR, hG, ha, hle, hmu⟩) with h | h
    · exact .inl h
    · exact .inr (h.mono (by omega))

theorem windows (hP : PrimOK impl Rsv arity P R) {S0 : Nat} (hB : ImplBound impl S0)
    (C : LiveCert P G Act) (r : Run) {K : Nat} (hF : r.Fair K) {Φn S d n : Nat}
    (h0 : St2 impl Rsv arity R G Act r Φn S d n 0) :
    ∀ j, n + j * K ≤ r.len →
      St1 impl Rsv arity R G r Φn (n + j * K) ∨ St2 impl Rsv arity R G Act r Φn S d (n + j * K) j
  | 0, _ => by simpa using Or.inr h0
  | j + 1, hj => by
    have hK : n + j * K + K ≤ r.len := by rw [Nat.succ_mul] at hj; omega
    have := window hP hB C r hF hK (windows hP hB C r hF h0 j (by omega))
    rwa [show n + j * K + K = n + (j + 1) * K by rw [Nat.succ_mul]; omega] at this

/-- **One round.** If CPU `d` is active, then after `(S + 1) * K` fair steps the
potential has gone down. -/
theorem round (hP : PrimOK impl Rsv arity P R) {S0 : Nat} (hB : ImplBound impl S0)
    (C : LiveCert P G Act) (r : Run) {K : Nat} (hF : r.Fair K) {Φn S d n : Nat}
    (h0 : St2 impl Rsv arity R G Act r Φn S d n 0) (hn : n + (S + 1) * K ≤ r.len) :
    St1 impl Rsv arity R G r Φn (n + (S + 1) * K) := by
  rcases windows hP hB C r hF h0 (S + 1) hn with h | ⟨_, _, _, _, _, _, _, hmu⟩
  · exact h
  · omega

/-- **Liveness carried to Python.** Every `K`-fair run of the pool, started
in a state related to a C state of potential `Φ`, has fewer than
`(S0 + 3) * K * (Φ + 1)` steps. -/
theorem fair_bound (hP : PrimOK impl Rsv arity P R) {S0 : Nat} (hB : ImplBound impl S0)
    (C : LiveCert P G Act) (r : Run) {K : Nat} (hK : 0 < K) (hF : r.Fair K)
    {cs : List (CThread Pn)} {a : Abs} {Φ : Nat}
    (h0 : Rel impl Rsv arity R cs a (r.pool 0) (r.heap 0)) (hG : G cs a Φ) :
    r.len < (S0 + 3) * K * (Φ + 1) := by
  have key : ∀ Φ n (cs : List (CThread Pn)) (a : Abs),
      Rel impl Rsv arity R cs a (r.pool n) (r.heap n) → G cs a Φ →
        r.len < n + (S0 + 3) * K * (Φ + 1) := by
    intro Φ
    induction Φ using Nat.strongRecOn with
    | _ Φ ih =>
    intro n cs a hR hG
    have hRpos : 0 < (S0 + 3) * K := Nat.mul_pos (by omega) hK
    have hge : (S0 + 3) * K ≤ (S0 + 3) * K * (Φ + 1) := Nat.le_mul_of_pos_right _ (by omega)
    by_cases hlt : r.len < n + (S0 + 3) * K
    · omega
    · have hn : n < r.len := by omega
      obtain ⟨hi, c', s', hs, -, -⟩ := r.step n hn
      have hci : r.lab n < cs.length := hR.len ▸ hi
      have hnd : ¬ Done cs[r.lab n] := fun hd =>
        Step.no_skip (rel_done_rev hR _ hci hi hd ▸ hs)
      obtain ⟨d, ha⟩ := C.act hG ⟨_, hci, hnd⟩
      have h0 : St2 impl Rsv arity R G Act r Φ (S0 + 2) d n 0 := by
        obtain ⟨hd, -⟩ := C.act_lt hG ha
        refine ⟨cs, a, Φ, hR, hG, ha, Nat.le_refl _, ?_⟩
        rw [cmdAt_eq (hR.len ▸ hd)]; have := rel_mu_le hB hR d (hR.len ▸ hd); omega
      obtain ⟨cs', a', Φ', hR', hG', hlt'⟩ :=
        round hP hB C r hF h0 (by rw [show S0 + 2 + 1 = S0 + 3 by omega]; omega)
      have := ih Φ' hlt' _ cs' a' hR' hG'
      rw [show S0 + 2 + 1 = S0 + 3 by omega] at this
      have h1 : (S0 + 3) * K * (Φ' + 1) + (S0 + 3) * K ≤ (S0 + 3) * K * (Φ + 1) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega
  simpa using key Φ 0 cs a h0 hG

end Rounds

/-! ## No deadlock -/

/-- Sequential PyL runs from one state are linearly ordered (determinism). -/
theorem psteps_fork {c s H c₁ s₁ H₁ c₂ s₂ H₂} (h₁ : PSteps c s H c₁ s₁ H₁)
    (h₂ : PSteps c s H c₂ s₂ H₂) : PSteps c₁ s₁ H₁ c₂ s₂ H₂ ∨ PSteps c₂ s₂ H₂ c₁ s₁ H₁ := by
  induction h₁ generalizing c₂ s₂ H₂ with
  | refl => exact .inl h₂
  | step h r ih =>
    cases h₂ with
    | refl => exact .inr (.step h r)
    | step h' r' =>
      obtain ⟨rfl, rfl, rfl⟩ := Step.det h h'
      exact ih r'

section Progress
variable {Pn Abs : Type} {impl : Pn → List PyL.Expr → Var → Cmd}
  {Rsv : Var → Prop} {arity : Pn → Nat} {P : Nat → Prims Pn Abs} {R : Abs → Heap → Prop}

/-- A thread outside any block that has not finished can always step. -/
theorem out_progress {t : CThread Pn} {th : Thread} (hO : Out impl Rsv t th)
    (hne : th.cmd ≠ .skip) (H : Heap) : ∃ c' s' H', Step th.cmd th.store H c' s' H' := by
  cases hO with
  | @here s hA =>
    obtain ⟨⟨stmt, k, σ⟩, -, he, -, hn⟩ :=
      normalize (P := fun (_ : Nat) => (fun _ _ _ => none : Prims Pn Unit)) (impl := impl)
        0 () t.stmt t.cont t.locals
    show ∃ c' s' H', Step (embed impl t) s H c' s' H'
    rw [show embed impl t = embed impl ⟨stmt, k, σ⟩ from he.symm]
    rw [show embed impl t = embed impl ⟨stmt, k, σ⟩ from he.symm] at hne
    cases stmt with
    | skip =>
      cases k with
      | stop => exact absurd rfl hne
      | seq s₂ k => exact ⟨_, _, _, plug_step (impl := impl) k .seqSkip⟩
      | loop e b k => exact ⟨_, _, _, plug_step (impl := impl) k .seqSkip⟩
    | assign x e => exact ⟨_, _, _, plug_step (impl := impl) k .assign⟩
    | seq _ _ => exact absurd rfl (hn _ _)
    | ite e b₁ b₂ =>
      by_cases hz : (trE e).eval s = 0
      · exact ⟨_, _, _, plug_step (impl := impl) k (.iteF hz)⟩
      · exact ⟨_, _, _, plug_step (impl := impl) k (.iteT hz)⟩
    | «while» e b => exact ⟨_, _, _, plug_step (impl := impl) k .while⟩
    | call x p args => exact ⟨_, _, _, plug_step (impl := impl) k .atomic⟩
  | @wmid e b s _ _ =>
    by_cases hz : (trE e).eval s = 0
    · exact ⟨_, _, _, plug_step (impl := impl) _ (.iteF hz)⟩
    · exact ⟨_, _, _, plug_step (impl := impl) _ (.iteT hz)⟩

/-- **No deadlock.** In a related state, if some Python thread is unfinished,
the pool can take a step, provided the C primitives never get stuck. -/
theorem rel_progress (hP : PrimOK impl Rsv arity P R)
    (htot : ∀ i p (args : List ClightL.Expr) (σ : Locals) a, args.length = arity p →
      ∃ v a', P i p (args.map (·.eval σ)) a = some (v, a'))
    {cs : List (CThread Pn)} {a : Abs} {ts : Pool} {H : Heap}
    (hR : Rel impl Rsv arity R cs a ts H) (hne : ∃ i, ∃ hi : i < ts.length, ts[i].cmd ≠ .skip) :
    ∃ ts' H', MStep ts H ts' H' := by
  by_cases hb : ∃ i, ∃ hi : i < ts.length, ts[i].cmd.locked = true
  · obtain ⟨i, hi, hl⟩ := hb
    have hci : i < cs.length := hR.len ▸ hi
    rcases hR.thr i hci hi with hO | hIn
    · rw [out_locked hO] at hl; cases hl
    · obtain ⟨x, p, args, B, s₀, H₀, hst, hc, hA, hR0, hps⟩ := hIn
      have hw := (hR.wf i hci).1
      rw [hst] at hw
      obtain ⟨v, a', hv⟩ := htot i p args cs[i].locals a hw.2.1
      obtain ⟨s'', H'', hdone, -, -⟩ := hP.ok i p args x _ s₀ a H₀ v a' hA hw.1 hw.2.2 hR0 hv
      have hstep : ∃ c' s' H', Step (Cmd.inAtomic B) ts[i].store H c' s' H' := by
        rcases psteps_fork hps hdone with h | h
        · cases h with
          | refl => exact ⟨_, _, _, .inAtomicSkip⟩
          | step h _ => exact ⟨_, _, _, .inAtomic h⟩
        · cases h with
          | refl => exact ⟨_, _, _, .inAtomicSkip⟩
          | step h _ => exact absurd h Step.no_skip
      obtain ⟨c', s', H', hs⟩ := hstep
      refine ⟨_, _, .step i hi (c' := plug impl cs[i].cont c') (by rw [hc]; exact plug_step _ hs) ?_⟩
      intro h; rw [hl] at h; cases h
  · obtain ⟨i, hi, hni⟩ := hne
    have hci : i < cs.length := hR.len ▸ hi
    have hun : ∀ j (hj : j < ts.length), ts[j].cmd.locked = false := fun j hj => by
      cases h : ts[j].cmd.locked
      · rfl
      · exact absurd ⟨j, hj, h⟩ hb
    rcases hR.thr i hci hi with hO | hIn
    · obtain ⟨c', s', H', hs⟩ := out_progress hO hni H
      exact ⟨_, _, .step i hi hs (fun _ _ j hj _ => hun j hj)⟩
    · exact absurd (inBlk_locked hIn) (by rw [hun i hi]; simp)

end Progress


end ClightToPy
