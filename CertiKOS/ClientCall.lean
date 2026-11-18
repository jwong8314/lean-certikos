import CertiKOS.CallStack
import CertiKOS.ClientRefine
import CertiKOS.LiveLink

/-!
# Contextual refinement for every client, through real calls

`ClientRefine.lean` proves the lock layer correct for every client program,
linking the client with the lock code by inlining. Here the same holds when
the client **calls** `acquire()` and `release()` as functions of a module, on
the call-stack machine of `CallStack.lean`.

* `MC P`: the client `P` with each atomic `x = acq()` replaced by the call
  `x = acquire()`, and each `x = rel()` by `x = release()`.
* `ticketMod`: the module with the verified C code of `acquire` and `release`.
* `acquire_complete`: a finished run of the `acquire` code meets its
  fuel-based spec. So its log does not depend on the locals it started with,
  and its result is 0.
* `call_to_inline`: a finished run of `MC P` on the call machine gives a
  finished run of the inlined program `M P`, with the same log and the same
  client locals. A call runs in a fresh frame, the inlined code in the
  client's frame, and the two agree off the lock code's own variables.
* `client_final_call`: **every client, linked by real calls, refines the
  atomic layer.** A finished run of `MC P` has a finished atomic run of `P`
  under an `ε_H` satisfying `HRely` (or `P` went wrong at L1).
-/

namespace ClientCall

open ClightL Ticket Link ClientRefine ClightCall CallStack

/-! ## Linking by calls -/

def MC : Stmt HPrim → Stmt (CP Prim)
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq a b => .seq (MC a) (MC b)
  | .ite e a b => .ite e (MC a) (MC b)
  | .while e b => .while e (MC b)
  | .call x .acq _ => .call x (.fn "acquire") []
  | .call x .rel _ => .call x (.fn "release") []

def MCk : Cont HPrim → Cont (CP Prim)
  | .stop => .stop
  | .seq s k => .seq (MC s) (MCk k)
  | .loop e b k => .loop e (MC b) (MCk k)

def ticketMod : ModG Prim := fun f =>
  if f = "acquire" then some ⟨[], liftS acquireCode, "_"⟩
  else if f = "release" then some ⟨[], liftS releaseCode, "_"⟩
  else none

def zeros : Locals := fun _ => 0

/-! ## Finished runs of the lock code -/

theorem final_star {P : Prims Prim Log} {x y : Config Prim Log} (hx : Final x) (h : Star P x y) : y = x := by
  cases h with
  | refl => rfl
  | step hs _ => rw [step_final hx] at hs; cases hs

theorem final_unique {P : Prims Prim Log} {x a b : Config Prim Log} (ha : Star P x a) (hb : Star P x b)
    (fa : Final a) (fb : Final b) : a = b := by
  rcases LiveLink.star_det ha hb with h | h
  · exact (final_star fa h).symm
  · exact final_star fb h

inductive StarN (P : Prims Prim Log) : Nat → Config Prim Log → Config Prim Log → Prop
  | refl (x) : StarN P 0 x x
  | step {n x y z} : step P x = some y → StarN P n y z → StarN P (n + 1) x z

theorem Star.toN {P : Prims Prim Log} {x y : Config Prim Log} (h : Star P x y) : ∃ n, StarN P n x y := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | step hs _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step hs hn⟩

theorem starN_peel {P : Prims Prim Log} {n : Nat} {x F : Config Prim Log} (h : StarN P n x F)
    (hF : Final F) (hx : ¬ Final x) : ∃ m y, n = m + 1 ∧ step P x = some y ∧ StarN P m y F := by
  cases h with
  | refl => exact absurd hF hx
  | step hs h' => exact ⟨_, _, rfl, hs, h'⟩

variable {ε : EnvCtx} {c : CPU}

/-- A wait loop that finishes meets its fuel-based spec. -/
theorem loop_complete (K : Cont Prim) : ∀ (n : Nat) (loc : Locals) (l : Log) {F : Config Prim Log},
    StarN (prims ε c) n ⟨acquireLoop, K, loc, l⟩ F → Final F →
    ∃ r, waitLoop ε c (loc "t") n (loc "n") l = some r := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro loc l F h hF
    by_cases hnt : loc "n" = loc "t"
    · cases n <;> exact ⟨l, by simp [waitLoop, hnt]⟩
    · obtain ⟨n1, y1, rfl, hs1, h1⟩ := starN_peel h hF (by simp [Final, acquireLoop])
      have e1 : y1 = ⟨.call "n" .getNow [], .loop (.bin .ne (.var "n") (.var "t")) (.call "n" .getNow []) K,
          loc, l⟩ := by
        simp [step, acquireLoop, Expr.eval, BinOp.eval, hnt] at hs1; exact hs1.symm
      subst e1
      obtain ⟨n2, y2, rfl, hs2, h2⟩ := starN_peel h1 hF (by simp [Final])
      have e2 : y2 = ⟨.skip, .loop (.bin .ne (.var "n") (.var "t")) (.call "n" .getNow []) K,
          loc.set "n" (BitVec.ofNat 32 (now (pull ε c l))), ⟨c, .getNow⟩ :: pull ε c l⟩ := by
        simp [step, prims] at hs2; exact hs2.symm
      subst e2
      obtain ⟨n3, y3, rfl, hs3, h3⟩ := starN_peel h2 hF (by simp [Final])
      have e3 : y3 = ⟨acquireLoop, K, loc.set "n" (BitVec.ofNat 32 (now (pull ε c l))),
          ⟨c, .getNow⟩ :: pull ε c l⟩ := by
        simp [step, acquireLoop] at hs3; exact hs3.symm
      subst e3
      have hlt : n3 < n3 + 1 + 1 + 1 := by omega
      obtain ⟨r, hr⟩ := ih n3 hlt _ _ h3 hF
      simp only [Locals.set_same, show (loc.set "n" (BitVec.ofNat 32 (now (pull ε c l)))) "t" = loc "t" by
        simp [Locals.set]] at hr
      refine ⟨r, ?_⟩
      simp only [waitLoop, hnt, ite_false]
      exact waitLoop_mono_le ε c _ (f := n3) (f' := n3 + 1 + 1) (by omega) hr

/-- The `acquire` code from any locals: its spec gives a run whose result variable is 0. -/
theorem acquire_run (ε : EnvCtx) (c : CPU) (fuel : Nat) (loc : Locals) (l r : Log)
    (k : Cont Prim) (h : acquireSpec ε c fuel l = some r) :
    ∃ loc' : Locals, (∀ z, ¬ Rsv z → loc' z = loc z) ∧ loc' "_" = 0 ∧
      Star (prims ε c) ⟨acquireCode, k, loc, l⟩ ⟨.skip, k, loc', r⟩ := by
  obtain ⟨r0, hw, rfl⟩ := acquireSpec_some h
  let l1 := pull ε c l
  let t := BitVec.ofNat 32 (ticket l1)
  let l2 : Log := ⟨c, .incTicket⟩ :: l1
  let l3 := pull ε c l2
  let n := BitVec.ofNat 32 (now l3)
  let loc1 := loc.set "t" t
  let loc2 := loc1.set "n" n
  have ht2 : loc2 "t" = t := by simp [loc2, loc1]
  have hn2 : loc2 "n" = n := by simp [loc2]
  obtain ⟨loc', hloc', hstar⟩ :=
    loop_sim_loc ε c t fuel n loc2 (⟨c, .getNow⟩ :: l3) r0 (.seq holdCall k) ht2 hn2 hw
  refine ⟨loc'.set "_" 0, fun z hz => ?_, by simp, ?_⟩
  · have h1 : z ≠ "_" := fun e => hz (.inr (.inr e))
    have h2 : z ≠ "n" := fun e => hz (.inr (.inl e))
    have h3 : z ≠ "t" := fun e => hz (.inl e)
    simp [Locals.set, h1, hloc' z h2, loc2, loc1, h2, h3]
  let rest : Stmt Prim := .seq (.call "n" .getNow []) (.seq acquireLoop holdCall)
  refine .step (c' := ⟨.call "t" .faiTicket [], .seq rest k, loc, l⟩)
      (by simp [step, acquireCode, rest]) ?_
  refine .step (c' := ⟨.skip, .seq rest k, loc1, l2⟩)
      (by simp [step, prims, loc1, t, l2, l1]) ?_
  refine .step (c' := ⟨rest, k, loc1, l2⟩) (by simp [step]) ?_
  refine .step (c' := ⟨.call "n" .getNow [], .seq (.seq acquireLoop holdCall) k, loc1, l2⟩)
      (by simp [step, rest]) ?_
  refine .step (c' := ⟨.skip, .seq (.seq acquireLoop holdCall) k, loc2, ⟨c, .getNow⟩ :: l3⟩)
      (by simp [step, prims, loc2, n, l3]) ?_
  refine .step (c' := ⟨.seq acquireLoop holdCall, k, loc2, ⟨c, .getNow⟩ :: l3⟩)
      (by simp [step]) ?_
  refine .step (c' := ⟨acquireLoop, .seq holdCall k, loc2, ⟨c, .getNow⟩ :: l3⟩)
      (by simp [step]) ?_
  refine Star.trans hstar ?_
  refine .step (c' := ⟨holdCall, k, loc', r0⟩) (by simp [step]) ?_
  exact Star.single (by simp [step, holdCall, prims, holdSpec])

/-- **A finished `acquire` meets its spec.** -/
theorem acquire_complete {loc σ' : Locals} {l r : Log}
    (h : Star (prims ε c) ⟨acquireCode, .stop, loc, l⟩ ⟨.skip, .stop, σ', r⟩) :
    ∃ fuel, acquireSpec ε c fuel l = some r := by
  have hF : Final (⟨.skip, .stop, σ', r⟩ : Config Prim Log) := ⟨rfl, rfl⟩
  -- the run up to the loop
  let l1 := pull ε c l
  let t := BitVec.ofNat 32 (ticket l1)
  let l2 : Log := ⟨c, .incTicket⟩ :: l1
  let l3 := pull ε c l2
  let n := BitVec.ofNat 32 (now l3)
  let loc2 := (loc.set "t" t).set "n" n
  let rest : Stmt Prim := .seq (.call "n" .getNow []) (.seq acquireLoop holdCall)
  have hpre : Star (prims ε c) ⟨acquireCode, .stop, loc, l⟩
      ⟨acquireLoop, .seq holdCall .stop, loc2, ⟨c, .getNow⟩ :: l3⟩ := by
    refine .step (c' := ⟨.call "t" .faiTicket [], .seq rest .stop, loc, l⟩)
        (by simp [step, acquireCode, rest]) ?_
    refine .step (c' := ⟨.skip, .seq rest .stop, loc.set "t" t, l2⟩)
        (by simp [step, prims, t, l2, l1]) ?_
    refine .step (c' := ⟨rest, .stop, loc.set "t" t, l2⟩) (by simp [step]) ?_
    refine .step (c' := ⟨.call "n" .getNow [], .seq (.seq acquireLoop holdCall) .stop, loc.set "t" t, l2⟩)
        (by simp [step, rest]) ?_
    refine .step (c' := ⟨.skip, .seq (.seq acquireLoop holdCall) .stop, loc2, ⟨c, .getNow⟩ :: l3⟩)
        (by simp [step, prims, loc2, n, l3]) ?_
    refine .step (c' := ⟨.seq acquireLoop holdCall, .stop, loc2, ⟨c, .getNow⟩ :: l3⟩)
        (by simp [step]) ?_
    exact Star.single (by simp [step])
  have hloop : Star (prims ε c) ⟨acquireLoop, .seq holdCall .stop, loc2, ⟨c, .getNow⟩ :: l3⟩
      ⟨.skip, .stop, σ', r⟩ := by
    rcases LiveLink.star_det hpre h with h1 | h1
    · exact h1
    · have := final_star hF h1
      simp [acquireLoop] at this
  obtain ⟨m, hm⟩ := Star.toN hloop
  obtain ⟨r0, hr0⟩ := loop_complete (.seq holdCall .stop) m loc2 _ hm hF
  have ht2 : loc2 "t" = t := by simp [loc2]
  have hn2 : loc2 "n" = n := by simp [loc2]
  rw [ht2, hn2] at hr0
  have hspec : acquireSpec ε c m l = some (holdSpec ε c r0) := by
    simp only [acquireSpec]; rw [hr0]; rfl
  obtain ⟨loc', -, -, hrun⟩ := acquire_run ε c m loc l _ .stop hspec
  have := final_unique h hrun hF ⟨rfl, rfl⟩
  simp only [Config.mk.injEq, true_and] at this
  exact ⟨m, this.2 ▸ hspec⟩

/-- A finished `acquire` from a fresh frame, and the same in the client's frame. -/
theorem acquire_both {σc σi : Locals} {l r : Log} (K : Cont Prim)
    (h : Star (prims ε c) ⟨acquireCode, .stop, zeros, l⟩ ⟨.skip, .stop, σc, r⟩) :
    σc "_" = 0 ∧ ∃ σi' : Locals, (∀ z, ¬ Rsv z → σi' z = σi z) ∧
      Star (prims ε c) ⟨acquireCode, K, σi, l⟩ ⟨.skip, K, σi', r⟩ := by
  obtain ⟨fuel, hspec⟩ := acquire_complete h
  obtain ⟨loc', -, h0, hrun⟩ := acquire_run ε c fuel zeros l r .stop hspec
  have := final_unique h hrun ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  simp only [Config.mk.injEq, true_and] at this
  obtain ⟨σi', hσ, -, hrun'⟩ := acquire_run ε c fuel σi l r K hspec
  exact ⟨this.1 ▸ h0, σi', hσ, hrun'⟩

theorem release_both {σc σi : Locals} {l r : Log} (K : Cont Prim)
    (h : Star (prims ε c) ⟨releaseCode, .stop, zeros, l⟩ ⟨.skip, .stop, σc, r⟩) :
    σc "_" = 0 ∧ Star (prims ε c) ⟨releaseCode, K, σi, l⟩ ⟨.skip, K, σi.set "_" 0, r⟩ := by
  have h1 : Star (prims ε c) ⟨releaseCode, .stop, zeros, l⟩
      ⟨.skip, .stop, zeros.set "_" 0, ⟨c, .incNow⟩ :: pull ε c l⟩ :=
    Star.single (by simp [step, prims, releaseCode])
  have := final_unique h h1 ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  simp only [Config.mk.injEq, true_and] at this
  obtain ⟨rfl, rfl⟩ := this
  exact ⟨by simp, Star.single (by simp [step, prims, releaseCode])⟩

/-! ## From the call machine to the inlined program -/

theorem MC_skip {s : Stmt HPrim} (h : MC s = .skip) : s = .skip := by
  cases s with
  | skip => rfl
  | call x p args => cases p <;> simp [MC] at h
  | _ => simp [MC] at h

theorem MCk_stop {k : Cont HPrim} (h : MCk k = .stop) : k = .stop := by
  cases k <;> simp [MCk] at h; rfl

/-- A step of the client's own code is the same on the call machine and inlined. -/
theorem pure_step {P : Prims Prim Log} {ys : Stmt HPrim} {yk : Cont HPrim} {σ σi : Locals} {l : Log}
    {G : GState Prim Log} (hnc : ∀ z p args, ys ≠ .call z p args) (hok : SOK ys) (hkok : KOK yk)
    (hag : ∀ z, ¬ Rsv z → σi z = σ z) (hs : stepG ticketMod P ⟨⟨MC ys, MCk yk, σ, l⟩, []⟩ = some G) :
    ∃ ys' yk' σ' σi', G = ⟨⟨MC ys', MCk yk', σ', l⟩, []⟩ ∧
      step P ⟨M ys, Mk yk, σi, l⟩ = some ⟨M ys', Mk yk', σi', l⟩ ∧ SOK ys' ∧ KOK yk' ∧
      ∀ z, ¬ Rsv z → σi' z = σ' z := by
  cases ys with
  | call z p args => exact absurd rfl (hnc z p args)
  | skip =>
    cases yk with
    | stop => simp [stepG, MC, MCk, step] at hs
    | seq s k =>
      simp only [stepG, MC, MCk, step, Option.map_some, Option.some.injEq] at hs; subst hs
      exact ⟨s, k, σ, σi, rfl, rfl, hkok.1, hkok.2, hag⟩
    | loop e b k =>
      simp only [stepG, MC, MCk, step, Option.map_some, Option.some.injEq] at hs; subst hs
      exact ⟨.while e b, k, σ, σi, rfl, rfl, ⟨hkok.1, hkok.2.1⟩, hkok.2.2, hag⟩
  | assign z e =>
    simp only [stepG, MC, step, Option.map_some, Option.some.injEq] at hs; subst hs
    refine ⟨.skip, yk, _, σi.set z (e.eval σi), rfl, rfl, trivial, hkok, ?_⟩
    rw [eval_agree hag e hok.2]; exact set_agree hag z _
  | seq a b =>
    simp only [stepG, MC, step, Option.map_some, Option.some.injEq] at hs; subst hs
    exact ⟨a, .seq b yk, σ, σi, rfl, rfl, hok.1, ⟨hok.2, hkok⟩, hag⟩
  | ite e a b =>
    simp only [stepG, MC, step, Option.map_some, Option.some.injEq] at hs; subst hs
    have he := eval_agree hag e hok.1
    by_cases hz : e.eval σ = 0#32
    · refine ⟨b, yk, σ, σi, by simp [hz], by simp [M, step, he, hz], hok.2.2, hkok, hag⟩
    · refine ⟨a, yk, σ, σi, by simp [hz], by simp [M, step, he, hz], hok.2.1, hkok, hag⟩
  | «while» e b =>
    have he := eval_agree hag e hok.1
    by_cases hz : e.eval σ = 0#32
    · simp [stepG, MC, step, hz] at hs; subst hs
      exact ⟨.skip, yk, σ, σi, rfl, by simp [M, step, he, hz], trivial, hkok, hag⟩
    · simp [stepG, MC, step, hz] at hs; subst hs
      exact ⟨b, .loop e b yk, σ, σi, rfl, by simp [M, Mk, step, he, hz], hok.2, ⟨hok.1, hok.2, hkok⟩, hag⟩

theorem acq_enter (P : Prims Prim Log) (z : Ident) (k : Cont (CP Prim)) (σ : Locals) (l : Log) :
    stepG ticketMod P ⟨⟨.call z (.fn "acquire") [], k, σ, l⟩, []⟩ =
      some ⟨liftC ⟨acquireCode, .stop, zeros, l⟩, [⟨z, "_", k, σ⟩]⟩ := by
  simp [stepG, ticketMod]; rfl

theorem rel_enter (P : Prims Prim Log) (z : Ident) (k : Cont (CP Prim)) (σ : Locals) (l : Log) :
    stepG ticketMod P ⟨⟨.call z (.fn "release") [], k, σ, l⟩, []⟩ =
      some ⟨liftC ⟨releaseCode, .stop, zeros, l⟩, [⟨z, "_", k, σ⟩]⟩ := by
  simp [stepG, ticketMod]; rfl

/-- **Calls and inlining agree.** A finished run of the client on the call
machine gives a finished run of the inlined program, with the same log and the
same client locals. -/
theorem call_to_inline_aux {σ' : Locals} {l' : Log} :
    ∀ (n : Nat) (ys : Stmt HPrim) (yk : Cont HPrim) (σ σi : Locals) (l : Log) (G0 F : GState Prim Log),
      G0 = ⟨⟨MC ys, MCk yk, σ, l⟩, []⟩ → F = ⟨⟨.skip, .stop, σ', l'⟩, []⟩ →
      StarGN ticketMod (prims ε c) n G0 F → SOK ys → KOK yk → (∀ z, ¬ Rsv z → σi z = σ z) →
      ∃ σi', (∀ z, ¬ Rsv z → σi' z = σ' z) ∧
        Star (prims ε c) ⟨M ys, Mk yk, σi, l⟩ ⟨.skip, .stop, σi', l'⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ys yk σ σi l G0 F hG0 hFe h hok hkok hag
    have hD : DoneG F := by subst hFe; exact ⟨rfl, rfl, rfl⟩
    cases h with
    | refl =>
      subst hG0
      simp only [GState.mk.injEq, Config.mk.injEq, and_true] at hFe
      obtain ⟨h1, h2, rfl, rfl⟩ := hFe
      have e1 := MC_skip h1; have e2 := MCk_stop h2
      subst e1; subst e2
      exact ⟨σi, hag, .refl _⟩
    | @step m _ s' _ hs hrest =>
      subst hG0
      by_cases hcall : ∃ z p args, ys = .call z p args
      · obtain ⟨z, p, args, rfl⟩ := hcall
        cases p with
        | acq =>
          have hs' : stepG ticketMod (prims ε c) ⟨⟨.call z (.fn "acquire") [], MCk yk, σ, l⟩, []⟩ = some s' := hs
          rw [acq_enter] at hs'
          simp only [Option.some.injEq] at hs'; subst hs'
          obtain ⟨m', σc, r, hm, hrun, hrest'⟩ := callee_split _ [] _ _ hrest hD
          obtain ⟨h0, σi1, hσ1, hin⟩ := acquire_both (σi := σi) (.seq (.assign z (.const 0)) (Mk yk)) hrun
          simp only [h0] at hrest'
          obtain ⟨σi', hσ', hstar⟩ := ih m' (by omega) .skip yk (σ.set z 0) (σi1.set z 0) r _ _ rfl hFe hrest'
            trivial hkok (set_agree (fun w hw => (hσ1 w hw).trans (hag w hw)) z 0)
          refine ⟨σi', hσ', ?_⟩
          refine .step (c' := ⟨acquireCode, .seq (.assign z (.const 0)) (Mk yk), σi, l⟩)
            (by simp [M, step]) (hin.trans ?_)
          refine .step (c' := ⟨.assign z (.const 0), Mk yk, σi1, r⟩) (by simp [step]) ?_
          exact .step (c' := ⟨.skip, Mk yk, σi1.set z 0, r⟩) (by simp [step, Expr.eval]) hstar
        | rel =>
          have hs' : stepG ticketMod (prims ε c) ⟨⟨.call z (.fn "release") [], MCk yk, σ, l⟩, []⟩ = some s' := hs
          rw [rel_enter] at hs'
          simp only [Option.some.injEq] at hs'; subst hs'
          obtain ⟨m', σc, r, hm, hrun, hrest'⟩ := callee_split _ [] _ _ hrest hD
          obtain ⟨h0, hin⟩ := release_both (σi := σi) (.seq (.assign z (.const 0)) (Mk yk)) hrun
          simp only [h0] at hrest'
          have hag1 : ∀ w, ¬ Rsv w → (σi.set "_" 0) w = σ w := fun w hw => by
            have : w ≠ "_" := fun e => hw (.inr (.inr e))
            simp [Locals.set, this, hag w hw]
          obtain ⟨σi', hσ', hstar⟩ := ih m' (by omega) .skip yk (σ.set z 0) ((σi.set "_" 0).set z 0) r _ _ rfl
            hFe hrest' trivial hkok (set_agree hag1 z 0)
          refine ⟨σi', hσ', ?_⟩
          refine .step (c' := ⟨releaseCode, .seq (.assign z (.const 0)) (Mk yk), σi, l⟩)
            (by simp [M, step]) (hin.trans ?_)
          refine .step (c' := ⟨.assign z (.const 0), Mk yk, σi.set "_" 0, r⟩) (by simp [step]) ?_
          exact .step (c' := ⟨.skip, Mk yk, (σi.set "_" 0).set z 0, r⟩) (by simp [step, Expr.eval]) hstar
      · obtain ⟨ys', yk', σ1, σi1, rfl, hst, hok', hkok', hag'⟩ :=
          pure_step (fun z p args e => hcall ⟨z, p, args, e⟩) hok hkok hag hs
        obtain ⟨σi', hσ', hstar⟩ := ih m (by omega) ys' yk' σ1 σi1 l _ _ rfl hFe hrest hok' hkok' hag'
        exact ⟨σi', hσ', .step hst hstar⟩

theorem call_to_inline {P : Stmt HPrim} (hP : SOK P) {σ σ' : Locals} {l l' : Log}
    (h : StarG ticketMod (prims ε c) ⟨⟨MC P, .stop, σ, l⟩, []⟩ ⟨⟨.skip, .stop, σ', l'⟩, []⟩) :
    ∃ σi', (∀ z, ¬ Rsv z → σi' z = σ' z) ∧
      Star (prims ε c) ⟨M P, .stop, σ, l⟩ ⟨.skip, .stop, σi', l'⟩ := by
  obtain ⟨n, hn⟩ := h.toN
  exact call_to_inline_aux n P .stop σ σ l _ _ rfl rfl hn hP trivial (fun _ _ => rfl)

/-- **Contextual refinement through real calls.** For every client `P`, a
finished run of `P` linked with the lock module by function calls has a
finished atomic run of `P` under an `ε_H` satisfying `HRely`, with the same
client locals and a related log (or `P` went wrong at L1). -/
theorem client_final_call (hc : c < NCPU) (hR : RelyP ε c) (bound : Log → Nat)
    (hF : ∀ tn, FairP ε c tn bound) (P : Stmt HPrim) (hP : SOK P) (σ : Locals) {l : Log}
    {s : PState} {h : HLog} (hl : replay l = some (s, h))
    (hph : s.phase c = .idle ∨ ∃ t, s.phase c = .holding t) {σ' : Locals} {l' : Log}
    (hx : StarG ticketMod (prims ε c) ⟨⟨MC P, .stop, σ, l⟩, []⟩ ⟨⟨.skip, .stop, σ', l'⟩, []⟩) :
    ∃ εH : HEnv, HRely εH c ∧ ∃ y, Star (hprims εH c) ⟨P, .stop, σ, h⟩ y ∧
      ((y.stmt = .skip ∧ y.cont = .stop ∧ (∀ z, ¬ Rsv z → σ' z = y.locals z) ∧ RelLog l' y.abs) ∨
       (ClightL.step (hprims εH c) y = none ∧ ¬ Final y)) := by
  obtain ⟨σi', hσ, hin⟩ := call_to_inline hP hx
  obtain ⟨εH, hRH, y, hy, hcase⟩ := client_final hc hR bound hF P hP σ hl hph hin
  refine ⟨εH, hRH, y, hy, ?_⟩
  rcases hcase with ⟨h1, h2, h3, h4⟩ | hw
  · exact .inl ⟨h1, h2, fun z hz => (hσ z hz).symm.trans (h3 z hz), h4⟩
  · exact .inr hw

end ClientCall
