import CertiKOS.ClightCall

/-!
# Nested calls: a call stack

`ClightCall.lean` has one level of calls (callees call only primitives).
Here function bodies may call functions, to any depth, on a call stack.

* `FnG`, `ModG`: functions whose bodies are statements over `CP Pn`, so a body
  can call primitives and functions. `linkG` links modules.
* `stepG`: a configuration and a stack of frames. A call pushes the caller's
  frame and starts the callee in a fresh frame; reaching the end of a body pops
  the frame and writes only the result to the caller.
* `star_stack`: a run does not look at the frames below it. `call_simG`: a
  complete run of a body (with whatever calls it makes) lifts to a complete
  call from any caller, at any stack depth.
* Leaf code: `liftS` embeds a statement over the primitives. `lift_star` and
  `callee_split` relate its runs on the call machine and in plain ClightL, in
  both directions.
* `incMod`: a function `inc(lk)` that calls `acquire(lk)` and
  `release(lk, v + 1)`, which are themselves functions. `inc_call`: the
  nested call runs to completion and its log is the atomic `acq; rel(v + 1)`.
-/

namespace CallStack

open ClightL Ticket LockArray ClightCall

variable {Pn Abs : Type}

structure FnG (Pn : Type) where
  params : List Ident
  body : Stmt (CP Pn)
  ret : Ident

abbrev ModG (Pn : Type) := String → Option (FnG Pn)

def linkG (M₁ M₂ : ModG Pn) : ModG Pn := fun f =>
  match M₁ f with
  | some F => some F
  | none => M₂ f

structure GState (Pn Abs : Type) where
  c : Config (CP Pn) Abs
  stack : List (Frame Pn)

def stepG (M : ModG Pn) (P : Prims Pn Abs) (s : GState Pn Abs) : Option (GState Pn Abs) :=
  match s.c.stmt, s.c.cont, s.stack with
  | .call x (.fn f) args, k, st =>
    match M f with
    | some F => some ⟨⟨F.body, .stop, bindArgs F.params (args.map (·.eval s.c.locals)), s.c.abs⟩,
        ⟨x, F.ret, k, s.c.locals⟩ :: st⟩
    | none => none
  | .skip, .stop, fr :: st => some ⟨⟨.skip, fr.k, fr.σ.set fr.x (s.c.locals fr.ret), s.c.abs⟩, st⟩
  | _, _, st => (step (liftP P) s.c).map fun c' => ⟨c', st⟩

inductive StarG (M : ModG Pn) (P : Prims Pn Abs) : GState Pn Abs → GState Pn Abs → Prop
  | refl (s) : StarG M P s s
  | step {s s' s''} : stepG M P s = some s' → StarG M P s' s'' → StarG M P s s''

theorem StarG.trans {M : ModG Pn} {P : Prims Pn Abs} {a b c : GState Pn Abs} :
    StarG M P a b → StarG M P b c → StarG M P a c := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- A step does not look at the frames below. -/
theorem step_stack {M : ModG Pn} {P : Prims Pn Abs} {c c' : Config (CP Pn) Abs} {s1 s1' : List (Frame Pn)}
    (st : List (Frame Pn)) (h : stepG M P ⟨c, s1⟩ = some ⟨c', s1'⟩) :
    stepG M P ⟨c, s1 ++ st⟩ = some ⟨c', s1' ++ st⟩ := by
  obtain ⟨stmt, k, σ, a⟩ := c
  -- the plain-step case
  have plain : ∀ (s2 : List (Frame Pn)),
      (step (liftP P) ⟨stmt, k, σ, a⟩).map (fun c2 => (⟨c2, s2⟩ : GState Pn Abs)) = some ⟨c', s1'⟩ →
      (step (liftP P) ⟨stmt, k, σ, a⟩).map (fun c2 => (⟨c2, s2 ++ st⟩ : GState Pn Abs)) = some ⟨c', s1' ++ st⟩ := by
    intro s2 h2
    cases hs : step (liftP P) ⟨stmt, k, σ, a⟩ with
    | none => rw [hs] at h2; simp at h2
    | some c2 =>
      rw [hs] at h2; simp only [Option.map_some, Option.some.injEq, GState.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2; rfl
  cases stmt with
  | call x p args =>
    cases p with
    | fn f =>
      simp only [stepG] at h ⊢
      cases hF : M f with
      | none => simp [hF] at h
      | some F =>
        simp only [hF, Option.some.injEq, GState.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h; simp
    | prim p => simp only [stepG] at h ⊢; exact plain s1 h
  | skip =>
    cases k with
    | stop =>
      cases s1 with
      | nil => simp [stepG, step] at h
      | cons fr s2 =>
        simp only [stepG, Option.some.injEq, GState.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h; simp
    | seq s k2 => simp only [stepG] at h ⊢; exact plain s1 h
    | loop e b k2 => simp only [stepG] at h ⊢; exact plain s1 h
  | assign x e => simp only [stepG] at h ⊢; exact plain s1 h
  | seq a b => simp only [stepG] at h ⊢; exact plain s1 h
  | ite e a b => simp only [stepG] at h ⊢; exact plain s1 h
  | «while» e b => simp only [stepG] at h ⊢; exact plain s1 h

theorem star_stack {M : ModG Pn} {P : Prims Pn Abs} (st : List (Frame Pn)) :
    ∀ {a b : GState Pn Abs}, StarG M P a b → StarG M P ⟨a.c, a.stack ++ st⟩ ⟨b.c, b.stack ++ st⟩ := by
  intro a b h
  induction h with
  | refl => exact .refl _
  | @step a b d hs _ ih => exact .step (step_stack st (c := a.c) (s1 := a.stack) hs) ih

/-- **Calls link, at any depth.** A complete run of `f`'s body, with whatever
calls it makes, lifts to a complete call from any caller on any stack. -/
theorem call_simG {M : ModG Pn} {P : Prims Pn Abs} {f : String} {F : FnG Pn} (hM : M f = some F)
    {x : Ident} {args : List Expr} {k : Cont (CP Pn)} {σ σ' : Locals} {a a' : Abs} (st : List (Frame Pn))
    (hrun : StarG M P ⟨⟨F.body, .stop, bindArgs F.params (args.map (·.eval σ)), a⟩, []⟩
      ⟨⟨.skip, .stop, σ', a'⟩, []⟩) :
    StarG M P ⟨⟨.call x (.fn f) args, k, σ, a⟩, st⟩ ⟨⟨.skip, k, σ.set x (σ' F.ret), a'⟩, st⟩ := by
  have h1 := star_stack (⟨x, F.ret, k, σ⟩ :: st) hrun
  simp only [List.nil_append] at h1
  refine .step (by simp [stepG, hM]) (h1.trans (.step ?_ (.refl _)))
  simp [stepG]

/-! ## Leaf code -/

def liftS : Stmt Pn → Stmt (CP Pn)
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq a b => .seq (liftS a) (liftS b)
  | .ite e a b => .ite e (liftS a) (liftS b)
  | .while e b => .while e (liftS b)
  | .call x p args => .call x (.prim p) args

def liftK : Cont Pn → Cont (CP Pn)
  | .stop => .stop
  | .seq s k => .seq (liftS s) (liftK k)
  | .loop e b k => .loop e (liftS b) (liftK k)

def liftC (c : Config Pn Abs) : Config (CP Pn) Abs := ⟨liftS c.stmt, liftK c.cont, c.locals, c.abs⟩

theorem step_lift (P : Prims Pn Abs) (c : Config Pn Abs) :
    step (liftP P) (liftC c) = (step P c).map liftC := by
  obtain ⟨stmt, k, σ, a⟩ := c
  cases stmt with
  | skip => cases k <;> rfl
  | assign x e => rfl
  | seq a b => rfl
  | ite e a b => by_cases hz : Expr.eval σ e = 0#32 <;> simp [step, liftC, liftS, hz]
  | «while» e b => by_cases hz : Expr.eval σ e = 0#32 <;> simp [step, liftC, liftS, liftK, hz]
  | call x p args =>
    simp only [step, liftC, liftS, liftP]
    cases P p (args.map (·.eval σ)) a with
    | none => rfl
    | some r => rfl

/-- Leaf code on the call machine steps as in ClightL, unless it is at the end of its body. -/
theorem stepG_lift {M : ModG Pn} {P : Prims Pn Abs} {c c' : Config Pn Abs} (st : List (Frame Pn))
    (h : step P c = some c') : stepG M P ⟨liftC c, st⟩ = some ⟨liftC c', st⟩ := by
  have hl := step_lift P c
  rw [h] at hl
  obtain ⟨stmt, k, σ, a⟩ := c
  cases stmt with
  | call x p args => simp only [stepG, liftC, liftS] at hl ⊢; simp [hl, liftC]
  | skip =>
    cases k with
    | stop => simp [step] at h
    | seq s k2 => simp only [stepG, liftC, liftS, liftK] at hl ⊢; simp [hl, liftC]
    | loop e b k2 => simp only [stepG, liftC, liftS, liftK] at hl ⊢; simp [hl, liftC]
  | assign x e => simp only [stepG, liftC, liftS] at hl ⊢; simp [hl, liftC]
  | seq a b => simp only [stepG, liftC, liftS] at hl ⊢; simp [hl, liftC]
  | ite e a b => simp only [stepG, liftC, liftS] at hl ⊢; simp [hl, liftC]
  | «while» e b => simp only [stepG, liftC, liftS] at hl ⊢; simp [hl, liftC]

theorem lift_star {M : ModG Pn} {P : Prims Pn Abs} (st : List (Frame Pn)) {c c' : Config Pn Abs}
    (h : Star P c c') : StarG M P ⟨liftC c, st⟩ ⟨liftC c', st⟩ := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (stepG_lift st hs) ih

/-- Step-counted runs. -/
inductive StarGN (M : ModG Pn) (P : Prims Pn Abs) : Nat → GState Pn Abs → GState Pn Abs → Prop
  | refl (s) : StarGN M P 0 s s
  | step {n s s' s''} : stepG M P s = some s' → StarGN M P n s' s'' → StarGN M P (n + 1) s s''

theorem StarGN.toStar {M : ModG Pn} {P : Prims Pn Abs} {n : Nat} {a b : GState Pn Abs}
    (h : StarGN M P n a b) : StarG M P a b := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs ih

theorem StarG.toN {M : ModG Pn} {P : Prims Pn Abs} {a b : GState Pn Abs} (h : StarG M P a b) :
    ∃ n, StarGN M P n a b := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | step hs _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step hs hn⟩

/-- A finished state: the end of the program, with an empty stack. -/
def DoneG (s : GState Pn Abs) : Prop := s.c.stmt = .skip ∧ s.c.cont = .stop ∧ s.stack = []

/-- **A leaf callee that finishes ran as plain ClightL.** If a run from inside a
leaf body reaches the end of the program, the body ran to its end in ClightL,
returned, and the rest of the run is shorter. -/
theorem callee_split {M : ModG Pn} {P : Prims Pn Abs} (fr : Frame Pn) (st : List (Frame Pn)) :
    ∀ (n : Nat) (c : Config Pn Abs) {F : GState Pn Abs}, StarGN M P n ⟨liftC c, fr :: st⟩ F → DoneG F →
      ∃ (m : Nat) (σ' : Locals) (a' : Abs), m < n ∧ Star P c ⟨.skip, .stop, σ', a'⟩ ∧
        StarGN M P m ⟨⟨.skip, fr.k, fr.σ.set fr.x (σ' fr.ret), a'⟩, st⟩ F
  | 0, c, F, h, hd => by
    cases h; obtain ⟨-, -, h3⟩ := hd; simp at h3
  | n + 1, c, F, h, hd => by
    cases h with
    | step hs hrest =>
      obtain ⟨stmt, k, σ, a⟩ := c
      by_cases hend : stmt = .skip ∧ k = .stop
      · obtain ⟨rfl, rfl⟩ := hend
        simp only [stepG, liftC, liftS, liftK, Option.some.injEq] at hs
        subst hs
        exact ⟨n, σ, a, Nat.lt_succ_self _, .refl _, hrest⟩
      · cases hst : step P ⟨stmt, k, σ, a⟩ with
        | none =>
          exfalso
          have hl := step_lift P ⟨stmt, k, σ, a⟩
          rw [hst] at hl
          cases stmt with
          | skip =>
            cases k with
            | stop => exact hend ⟨rfl, rfl⟩
            | seq s k2 => simp [step] at hst
            | loop e b k2 => simp [step] at hst
          | call x p args => simp only [stepG, liftC, liftS] at hl hs; simp [hl] at hs
          | assign x e => simp [step] at hst
          | seq a b => simp [step] at hst
          | ite e a b => simp [step] at hst
          | «while» e b => simp only [step] at hst; split at hst <;> simp at hst
        | some c2 =>
          rw [stepG_lift (M := M) (fr :: st) hst] at hs
          simp only [Option.some.injEq] at hs; subst hs
          obtain ⟨m, σ', a', hm, hrun, hrest'⟩ := callee_split fr st n c2 hrest hd
          exact ⟨m, σ', a', by omega, .step hst hrun, hrest'⟩

/-! ## A nested call: `inc(lk)` calls `acquire` and `release` -/

/-- `acquire` and `release` as before, and `inc(lk) { v = acquire(lk); release(lk, v + 1); }`. -/
def incMod : ModG APrim := fun f =>
  if f = "acquire" then some ⟨["lk"], liftS acquireA, "v"⟩
  else if f = "release" then some ⟨["lk", "v"], liftS releaseA, "_"⟩
  else if f = "inc" then
    some ⟨["lk"], .seq (.call "v" (.fn "acquire") [.var "lk"])
      (.call "_" (.fn "release") [.var "lk", .bin .add (.var "v") (.const 1)]), "_"⟩
  else none

/-- **A nested call refines two atomic steps.** `x = inc(e)`, a function that
itself calls `acquire` and `release`, runs to completion from any caller on any
stack. Its log is the atomic `acq` returning `v`, then `rel` storing `v + 1`. -/
theorem inc_call {ε : AEnv} {c : CPU} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) {iv : Val}
    (hidle : (S.lk iv.toNat).phase c = .idle) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : FairA ε c iv.toNat (ticket (projL iv.toNat (apull ε c l))) bound)
    {x : Ident} {e : Expr} {σ : Locals} (he : e.eval σ = iv) (k : Cont (CP APrim)) (st : List (Frame APrim)) :
    ∃ (εH εH' : HEnvA) (r : ALog) (v : Val) (E2 : HLogA) (S1 S2 : AState) (H1 : HLogA),
      HRelyA εH c ∧ HRelyA εH' c ∧
      StarG incMod (aprims ε c) ⟨⟨.call x (.fn "inc") [e], k, σ, l⟩, st⟩
        ⟨⟨.skip, k, σ.set x 0, releaseSpecA ε c iv.toNat (v + 1) r⟩, st⟩ ∧
      hprimsA εH c .acq [iv] H = some (v, .acqA c iv.toNat :: hpullA εH c H) ∧
      areplay r = some (S1, H1) ∧ H1 = E2 ++ .acqA c iv.toNat :: hpullA εH c H ∧
      hprimsA εH' c .rel [iv, v + 1] H1 = some (0, .relA c iv.toNat (v + 1) :: hpullA εH' c H1) ∧
      areplay (releaseSpecA ε c iv.toNat (v + 1) r) =
        some (S2, .relA c iv.toNat (v + 1) :: hpullA εH' c H1) := by
  -- acquire, as plain ClightL in a fresh frame
  obtain ⟨εH, r, σ1, E2, S1, hRH, hst1, hp1, hr1, hhold⟩ :=
    acquireA_refines hc hR hl hidle bound K hK hF (bindArgs ["lk"] [iv]) (bind_lk iv) .stop
  -- release, as plain ClightL in a fresh frame
  obtain ⟨h1, h2⟩ := bind_lkv iv (σ1 "v" + 1)
  obtain ⟨εH', S2, hRH', hst2, hp2, hr2, -⟩ :=
    releaseA_refines hc hR hr1 hhold.2 (bindArgs ["lk", "v"] [iv, σ1 "v" + 1]) h1 .stop
  rw [h2] at hst2 hp2 hr2
  refine ⟨εH, εH', r, σ1 "v", E2, S1, S2, _, hRH, hRH', ?_, hp1, hr1, rfl, hp2, hr2⟩
  -- the body of `inc`, in its own fresh frame
  let σb : Locals := bindArgs ["lk"] [iv]
  have hσb : σb "lk" = iv := bind_lk iv
  have hacq : StarG incMod (aprims ε c) ⟨⟨liftS acquireA, .stop, bindArgs ["lk"] [iv], l⟩, []⟩
      ⟨⟨.skip, .stop, σ1, r⟩, []⟩ := lift_star [] hst1
  have hrel : StarG incMod (aprims ε c)
      ⟨⟨liftS releaseA, .stop, bindArgs ["lk", "v"] [iv, σ1 "v" + 1], r⟩, []⟩
      ⟨⟨.skip, .stop, ((bindArgs ["lk", "v"] [iv, σ1 "v" + 1]).set "_" 0).set "_" 0,
        releaseSpecA ε c iv.toNat (σ1 "v" + 1) r⟩, []⟩ := lift_star [] hst2
  have hbody : StarG incMod (aprims ε c)
      ⟨⟨.seq (.call "v" (.fn "acquire") [.var "lk"])
          (.call "_" (.fn "release") [.var "lk", .bin .add (.var "v") (.const 1)]), .stop, σb, l⟩, []⟩
      ⟨⟨.skip, .stop, (σb.set "v" (σ1 "v")).set "_" 0, releaseSpecA ε c iv.toNat (σ1 "v" + 1) r⟩, []⟩ := by
    refine .step (s' := ⟨⟨.call "v" (.fn "acquire") [.var "lk"],
      .seq (.call "_" (.fn "release") [.var "lk", .bin .add (.var "v") (.const 1)]) .stop, σb, l⟩, []⟩)
      (by simp [stepG, step, liftP]) ?_
    have c1 := call_simG (M := incMod) (P := aprims ε c) (f := "acquire")
      (F := ⟨["lk"], liftS acquireA, "v"⟩) (x := "v") (args := [.var "lk"])
      (k := .seq (.call "_" (.fn "release") [.var "lk", .bin .add (.var "v") (.const 1)]) .stop)
      (σ := σb) (by simp [incMod]) [] (by simpa [Expr.eval, hσb] using hacq)
    refine c1.trans (.step (s' := ⟨⟨.call "_" (.fn "release") [.var "lk", .bin .add (.var "v") (.const 1)],
      .stop, σb.set "v" (σ1 "v"), r⟩, []⟩) (by simp [stepG, step, liftP]) ?_)
    have hlk2 : (σb.set "v" (σ1 "v")) "lk" = iv := by simp [Locals.set, hσb]
    have c2 := call_simG (M := incMod) (P := aprims ε c) (f := "release")
      (F := ⟨["lk", "v"], liftS releaseA, "_"⟩) (x := "_")
      (args := [.var "lk", .bin .add (.var "v") (.const 1)]) (k := .stop) (σ := σb.set "v" (σ1 "v"))
      (by simp [incMod]) []
      (by simpa [Expr.eval, BinOp.eval, hlk2, Locals.set, hσb] using hrel)
    simpa using c2
  have := call_simG (M := incMod) (P := aprims ε c) (f := "inc")
    (F := ⟨["lk"], .seq (.call "v" (.fn "acquire") [.var "lk"])
      (.call "_" (.fn "release") [.var "lk", .bin .add (.var "v") (.const 1)]), "_"⟩)
    (x := x) (args := [e]) (k := k) (σ := σ)
    (by simp [incMod]) st (by simpa [he] using hbody)
  simpa using this

end CallStack
