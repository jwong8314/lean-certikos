import CertiKOS.LockArrayAtomic

/-!
# C-to-C calls and modules

ClightL has primitive calls only, so until now client code was linked with
the lock code by inlining (`ClientRefine.lean`). This file adds real function
calls with call frames, and modules.

* `CP Pn`: what a statement may call. Either a primitive of the layer below
  (`prim p`) or a function of a module (`fn f`).
* `Fn`: a function with parameters, a body and a return variable. Bodies are
  ClightL statements over the primitives (leaf functions: they call
  primitives, not other functions).
* `Module`: named functions. `link M₁ M₂` is their union (`M₁` wins on a
  clash), and `link_left`/`link_right` look functions up in it.
* `stepF`: the machine. Calling `f` saves the caller's continuation and
  locals in a frame and runs the body in a **fresh frame** (parameters bound
  to the arguments, every other local 0). Returning restores the caller's
  locals and sets only the result variable. The callee cannot read or write
  the caller's locals.
* `call_sim`: any run of a callee body lifts to a complete call from any
  caller frame. This is the frame-aware linking step.
* `acquire_call`, `release_call`: the lock-array `acquire(lk)` and
  `release(lk, v)` as real functions of a module `lockMod` refine the atomic
  `acq`/`rel` (`LockArrayAtomic.lean`). The caller's frame changes exactly as
  if it had called the atomic primitive.
-/

namespace ClightCall

open ClightL Ticket LockArray

variable {Pn Abs : Type}

inductive CP (Pn : Type)
  | prim (p : Pn)
  | fn (f : String)

structure Fn (Pn : Type) where
  params : List Ident
  body : Stmt Pn
  ret : Ident

abbrev Module (Pn : Type) := String → Option (Fn Pn)

/-- Linking two modules. -/
def link (M₁ M₂ : Module Pn) : Module Pn := fun f =>
  match M₁ f with
  | some F => some F
  | none => M₂ f

theorem link_left {M₁ M₂ : Module Pn} {f : String} {F : Fn Pn} (h : M₁ f = some F) : link M₁ M₂ f = some F := by
  simp [link, h]

theorem link_right {M₁ M₂ : Module Pn} {f : String} (h : M₁ f = none) : link M₁ M₂ f = M₂ f := by
  simp [link, h]

/-- A fresh frame: parameters bound to the arguments, every other local 0. -/
def bindArgs : List Ident → List Val → Locals
  | x :: xs, v :: vs => (bindArgs xs vs).set x v
  | _, _ => fun _ => 0

structure Frame (Pn : Type) where
  x : Ident
  ret : Ident
  k : Cont (CP Pn)
  σ : Locals

/-- Running the caller, or running a callee with the caller's frame saved. -/
inductive FState (Pn Abs : Type)
  | caller (c : Config (CP Pn) Abs)
  | callee (c : Config Pn Abs) (fr : Frame Pn)

def liftP (P : Prims Pn Abs) : Prims (CP Pn) Abs
  | .prim p => P p
  | .fn _ => fun _ _ => none

def stepF (M : Module Pn) (P : Prims Pn Abs) : FState Pn Abs → Option (FState Pn Abs)
  | .caller c =>
    match c.stmt with
    | .call x (.fn f) args =>
      match M f with
      | some F => some (.callee ⟨F.body, .stop, bindArgs F.params (args.map (·.eval c.locals)), c.abs⟩
          ⟨x, F.ret, c.cont, c.locals⟩)
      | none => none
    | _ => (step (liftP P) c).map .caller
  | .callee c fr =>
    match c.stmt, c.cont with
    | .skip, .stop => some (.caller ⟨.skip, fr.k, fr.σ.set fr.x (c.locals fr.ret), c.abs⟩)
    | _, _ => (step P c).map fun c' => .callee c' fr

inductive StarF (M : Module Pn) (P : Prims Pn Abs) : FState Pn Abs → FState Pn Abs → Prop
  | refl (s) : StarF M P s s
  | step {s s' s''} : stepF M P s = some s' → StarF M P s' s'' → StarF M P s s''

theorem StarF.trans {M : Module Pn} {P : Prims Pn Abs} {a b c : FState Pn Abs} :
    StarF M P a b → StarF M P b c → StarF M P a c := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

/-- A callee's run, in its frame. -/
theorem callee_star {M : Module Pn} {P : Prims Pn Abs} (fr : Frame Pn) {c c' : Config Pn Abs}
    (h : Star P c c') : StarF M P (.callee c fr) (.callee c' fr) := by
  induction h with
  | refl => exact .refl _
  | @step a b d hs _ ih =>
    refine .step ?_ ih
    obtain ⟨st, k, σ, ab⟩ := a
    simp only [stepF]
    split
    · simp_all [step]
    · rw [hs]; rfl

/-- **Calls link.** If `f`'s body, started in a fresh frame on the arguments,
runs to its end, then the call `x = f(args)` runs from any caller frame to the
point after the call. The caller's locals change only at `x`, which gets the
callee's result. -/
theorem call_sim {M : Module Pn} {P : Prims Pn Abs} {f : String} {F : Fn Pn} (hM : M f = some F)
    {x : Ident} {args : List Expr} {k : Cont (CP Pn)} {σ σ' : Locals} {a a' : Abs}
    (hrun : Star P ⟨F.body, .stop, bindArgs F.params (args.map (·.eval σ)), a⟩ ⟨.skip, .stop, σ', a'⟩) :
    StarF M P (.caller ⟨.call x (.fn f) args, k, σ, a⟩) (.caller ⟨.skip, k, σ.set x (σ' F.ret), a'⟩) := by
  refine .step (by simp [stepF, hM]) ((callee_star ⟨x, F.ret, k, σ⟩ hrun).trans (.step ?_ (.refl _)))
  simp [stepF]

/-- A primitive call in the caller runs as in ClightL. -/
theorem prim_step {M : Module Pn} {P : Prims Pn Abs} {c c' : Config (CP Pn) Abs}
    (hnf : ∀ x f args, c.stmt ≠ .call x (.fn f) args) (h : step (liftP P) c = some c') :
    stepF M P (.caller c) = some (.caller c') := by
  obtain ⟨st, k, σ, ab⟩ := c
  simp only at hnf
  cases st with
  | call x p args =>
    cases p with
    | fn f => exact absurd rfl (hnf x f args)
    | prim p => simp [stepF, h]
  | _ => simp [stepF, h]

/-! ## The lock-array module -/

/-- `acquire(lk)` returns the block, and `release(lk, v)` stores `v`. -/
def lockMod : Module APrim := fun f =>
  if f = "acquire" then some ⟨["lk"], acquireA, "v"⟩
  else if f = "release" then some ⟨["lk", "v"], releaseA, "_"⟩
  else none

theorem bind_lk (iv : Val) : bindArgs ["lk"] [iv] "lk" = iv := by simp [bindArgs, Locals.set]

/-- **`x = acquire(e)` as a real call refines the atomic `x = acq(e)`.** The
caller's frame ends with `x` set to the value the atomic `acq` returns, and
nothing else changed. -/
theorem acquire_call {ε : AEnv} {c : CPU} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) {iv : Val}
    (hidle : (S.lk iv.toNat).phase c = .idle) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : FairA ε c iv.toNat (ticket (projL iv.toNat (apull ε c l))) bound)
    {x : Ident} {e : Expr} {σ : Locals} (he : e.eval σ = iv) (k : Cont (CP APrim)) :
    ∃ (εH : HEnvA) (r : ALog) (v : Val) (E2 : HLogA) (S' : AState),
      HRelyA εH c ∧
      StarF lockMod (aprims ε c) (.caller ⟨.call x (.fn "acquire") [e], k, σ, l⟩)
        (.caller ⟨.skip, k, σ.set x v, r⟩) ∧
      hprimsA εH c .acq [iv] H = some (v, .acqA c iv.toNat :: hpullA εH c H) ∧
      areplay r = some (S', E2 ++ .acqA c iv.toNat :: hpullA εH c H) := by
  obtain ⟨εH, r, σ', E2, S', hRH, hst, hp, hr, -⟩ :=
    acquireA_refines hc hR hl hidle bound K hK hF (bindArgs ["lk"] [iv]) (bind_lk iv) .stop
  have hrun : Star (aprims ε c) ⟨(⟨["lk"], acquireA, "v"⟩ : Fn APrim).body, .stop,
      bindArgs ["lk"] ([e].map (·.eval σ)), l⟩ ⟨.skip, .stop, σ', r⟩ := by
    simpa [he] using hst
  exact ⟨εH, r, σ' "v", E2, S', hRH, call_sim (by simp [lockMod]) hrun, hp, hr⟩

theorem bind_lkv (iv w : Val) : bindArgs ["lk", "v"] [iv, w] "lk" = iv ∧ bindArgs ["lk", "v"] [iv, w] "v" = w := by
  simp [bindArgs, Locals.set]

/-- **`x = release(e, ev)` as a real call refines the atomic `x = rel(e, ev)`.** -/
theorem release_call {ε : AEnv} {c : CPU} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) {iv w : Val}
    (hhold : Holding S c iv.toNat) {x : Ident} {e ev : Expr} {σ : Locals} (he : e.eval σ = iv)
    (hev : ev.eval σ = w) (k : Cont (CP APrim)) :
    ∃ (εH : HEnvA) (S' : AState),
      HRelyA εH c ∧
      StarF lockMod (aprims ε c) (.caller ⟨.call x (.fn "release") [e, ev], k, σ, l⟩)
        (.caller ⟨.skip, k, σ.set x 0, releaseSpecA ε c iv.toNat w l⟩) ∧
      hprimsA εH c .rel [iv, w] H = some (0, .relA c iv.toNat w :: hpullA εH c H) ∧
      areplay (releaseSpecA ε c iv.toNat w l) = some (S', .relA c iv.toNat w :: hpullA εH c H) := by
  obtain ⟨h1, h2⟩ := bind_lkv iv w
  obtain ⟨εH, S', hRH, hst, hp, hr, -⟩ := releaseA_refines hc hR hl hhold (bindArgs ["lk", "v"] [iv, w]) h1 .stop
  rw [h2] at hst hp hr
  have hrun : Star (aprims ε c) ⟨(⟨["lk", "v"], releaseA, "_"⟩ : Fn APrim).body, .stop,
      bindArgs ["lk", "v"] ([e, ev].map (·.eval σ)), l⟩
      ⟨.skip, .stop, ((bindArgs ["lk", "v"] [iv, w]).set "_" 0).set "_" 0, releaseSpecA ε c iv.toNat w l⟩ := by
    simpa [he, hev] using hst
  have := call_sim (M := lockMod) (f := "release") (x := x) (k := k) (by simp [lockMod]) hrun
  simp only [Locals.set_same] at this
  exact ⟨εH, S', hRH, this, hp, hr⟩

end ClightCall
