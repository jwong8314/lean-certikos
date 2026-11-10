import CertiKOS.Link
import CertiKOS.AtomicLayer
import CertiKOS.FairEnv

/-!
# Contextual refinement for every client program

CCAL proves the lock layer correct *for every client program* `P`
([PLDI18] (2.2)). Running `P` over the C implementation of `acq`/`rel` on
`L0[c]` refines running `P` over the atomic primitives of `L1[c]`. Until now
this prototype proved refinement per `acquire`, per `release`, and per
critical section (`AtomicLayer.lean`). Here it is proved for an arbitrary
client.

* **Clients.** Any ClightL statement `P : Stmt HPrim` over the atomic
  primitives `acq`/`rel` (loops, conditionals, any number and nesting of
  critical sections). `SOK` asks only that `P` not use the three local
  variables the lock code uses (`t`, `n`, `_`).
* **Linking.** ClightL has no C-to-C calls yet, so `M P` *inlines* the verified
  code. `x := acq()` becomes `acquireCode; x := 0`, and `x := rel()` becomes
  `releaseCode; x := 0`. This is the program CCAL's linking produces, without
  the call frames.
* **Refinement** (`client_sim`): every step of the L0 execution of `M P` is
  matched by the L1 execution of `P` under one environment `ε_H` that
  satisfies `HRely`. `ε_H` is a table built from the run. Each L0
  configuration is in one of three situations:
  1. *related* to an L1 configuration (same program point, same non-reserved
     locals, the L0 log replays to the L1 log);
  2. *inside the C code of one `acq`/`rel`*, whose end is reachable and related
     to the L1 configuration right after that one atomic step;
  3. or `P` has already gone *wrong* at L1 (for example `rel` without holding
     the lock). L1 is then stuck, and CCAL's refinement says nothing more.
* **Termination sensitivity.** Situation 2 always includes a finite path to
  the end of the C block (the liveness of `acquire` under `FairP`), so the C
  code never adds divergence. `client_final`: a finished L0 run has a finished
  related L1 run (or `P` went wrong).
-/

namespace ClientRefine

open ClightL Ticket Link ClightToPy

/-! ## Clients, and their linking with the C lock code -/

def Rsv (z : Ident) : Prop := z = "t" ∨ z = "n" ∨ z = "_"

def EOK : Expr → Prop
  | .const _ => True
  | .var x => ¬ Rsv x
  | .bin _ a b => EOK a ∧ EOK b

def SOK : Stmt HPrim → Prop
  | .skip => True
  | .assign x e => ¬ Rsv x ∧ EOK e
  | .seq a b => SOK a ∧ SOK b
  | .ite e a b => EOK e ∧ SOK a ∧ SOK b
  | .while e b => EOK e ∧ SOK b
  | .call x _ _ => ¬ Rsv x

def KOK : Cont HPrim → Prop
  | .stop => True
  | .seq s k => SOK s ∧ KOK k
  | .loop e b k => EOK e ∧ SOK b ∧ KOK k

/-- Linking a client with the verified lock code (inlined). -/
def M : Stmt HPrim → Stmt Prim
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq a b => .seq (M a) (M b)
  | .ite e a b => .ite e (M a) (M b)
  | .while e b => .while e (M b)
  | .call x .acq _ => .seq acquireCode (.assign x (.const 0))
  | .call x .rel _ => .seq releaseCode (.assign x (.const 0))

def Mk : Cont HPrim → Cont Prim
  | .stop => .stop
  | .seq s k => .seq (M s) (Mk k)
  | .loop e b k => .loop e (M b) (Mk k)

/-- L0 and L1 configurations at the same program point. -/
structure Rel (c : CPU) (x : Config Prim Log) (y : Config HPrim HLog) : Prop where
  stmt : x.stmt = M y.stmt
  cont : x.cont = Mk y.cont
  ok : SOK y.stmt ∧ KOK y.cont
  loc : ∀ z, ¬ Rsv z → x.locals z = y.locals z
  log : ∃ s, replay x.abs = some (s, y.abs) ∧ (s.phase c = .idle ∨ ∃ t, s.phase c = .holding t)

theorem eval_agree {σL σH : Locals} (h : ∀ z, ¬ Rsv z → σL z = σH z) :
    ∀ e, EOK e → e.eval σL = e.eval σH
  | .const _, _ => rfl
  | .var x, hx => h x hx
  | .bin op a b, ⟨ha, hb⟩ => by simp only [Expr.eval, eval_agree h a ha, eval_agree h b hb]

theorem set_agree {σL σH : Locals} (h : ∀ z, ¬ Rsv z → σL z = σH z) (x : Ident) (v : Val) :
    ∀ z, ¬ Rsv z → (σL.set x v) z = (σH.set x v) z := by
  intro z hz
  by_cases e : z = x
  · subst e; simp
  · simp [Locals.set, e, h z hz]

/-! ## Non-lock steps are the same at both levels -/

theorem step_match {c : CPU} {P : Prims Prim Log} {Q : Prims HPrim HLog} {x x' : Config Prim Log}
    {y : Config HPrim HLog} (hR : Rel c x y) (hnc : ∀ z p args, y.stmt ≠ .call z p args)
    (hs : ClightL.step P x = some x') :
    ∃ y', ClightL.step Q y = some y' ∧ Rel c x' y' ∧ y'.abs = y.abs := by
  obtain ⟨xs, xk, xσ, xl⟩ := x
  obtain ⟨ys, yk, yσ, yl⟩ := y
  obtain ⟨hs1, hk1, ⟨hok1, hok2⟩, hloc, hlog⟩ := hR
  simp only at hs1 hk1 hok1 hok2 hloc hlog hnc
  subst hs1 hk1
  cases ys with
  | call z p args => exact absurd rfl (hnc z p args)
  | skip =>
    cases yk with
    | stop => simp [M, Mk, ClightL.step] at hs
    | seq s k =>
      simp only [M, Mk, ClightL.step, Option.some.injEq] at hs; subst hs
      exact ⟨_, rfl, ⟨rfl, rfl, hok2, hloc, hlog⟩, rfl⟩
    | loop e b k =>
      simp only [M, Mk, ClightL.step, Option.some.injEq] at hs; subst hs
      exact ⟨_, rfl, ⟨rfl, rfl, ⟨⟨hok2.1, hok2.2.1⟩, hok2.2.2⟩, hloc, hlog⟩, rfl⟩
  | assign z e =>
    simp only [M, ClightL.step, Option.some.injEq] at hs; subst hs
    refine ⟨_, rfl, ⟨rfl, rfl, ⟨trivial, hok2⟩, ?_, hlog⟩, rfl⟩
    simp only
    rw [eval_agree hloc e hok1.2]
    exact set_agree hloc z _
  | seq a b =>
    simp only [M, ClightL.step, Option.some.injEq] at hs; subst hs
    exact ⟨_, rfl, ⟨rfl, rfl, ⟨hok1.1, hok1.2, hok2⟩, hloc, hlog⟩, rfl⟩
  | ite e a b =>
    simp only [M, ClightL.step, Option.some.injEq] at hs; subst hs
    have he := eval_agree hloc e hok1.1
    refine ⟨_, rfl, ⟨?_, rfl, ⟨?_, hok2⟩, hloc, hlog⟩, rfl⟩
    · simp only [he]; split <;> rfl
    · simp only; split
      · exact hok1.2.2
      · exact hok1.2.1
  | «while» e b =>
    have he := eval_agree hloc e hok1.1
    simp only [M, ClightL.step] at hs
    by_cases hz : e.eval yσ = 0
    · rw [he, if_pos hz, Option.some.injEq] at hs; subst hs
      refine ⟨⟨.skip, yk, yσ, yl⟩, ?_, ⟨rfl, rfl, ⟨trivial, hok2⟩, hloc, hlog⟩, rfl⟩
      show ClightL.step Q (CThread.cfg ⟨.while e b, yk, yσ⟩ yl) = _
      rw [cstep_while, if_pos hz]; rfl
    · rw [he, if_neg hz, Option.some.injEq] at hs; subst hs
      refine ⟨⟨b, .loop e b yk, yσ, yl⟩, ?_, ⟨rfl, rfl, ⟨hok1.2, hok1.1, hok1.2, hok2⟩, hloc, hlog⟩, rfl⟩
      show ClightL.step Q (CThread.cfg ⟨.while e b, yk, yσ⟩ yl) = _
      rw [cstep_while, if_neg hz]; rfl

/-! ## The C lock code, with the locals it touches -/

theorem loop_sim_loc (ε : EnvCtx) (c : CPU) (t : Val) :
    ∀ (fuel : Nat) (n : Val) (loc : Locals) (l r : Log) (k : Cont Prim),
      loc "t" = t → loc "n" = n → waitLoop ε c t fuel n l = some r →
      ∃ loc' : Locals, (∀ z, z ≠ "n" → loc' z = loc z) ∧
        Star (prims ε c) ⟨acquireLoop, k, loc, l⟩ ⟨.skip, k, loc', r⟩ := by
  intro fuel
  induction fuel with
  | zero =>
    intro n loc l r k ht hn hw
    by_cases hnt : n = t
    · simp [waitLoop, hnt] at hw
      subst hw
      refine ⟨loc, fun _ _ => rfl, Star.single ?_⟩
      simp [step, acquireLoop, Expr.eval, BinOp.eval, ht, hn, hnt]
    · simp [waitLoop, hnt] at hw
  | succ f ih =>
    intro n loc l r k ht hn hw
    by_cases hnt : n = t
    · simp [waitLoop, hnt] at hw
      subst hw
      refine ⟨loc, fun _ _ => rfl, Star.single ?_⟩
      simp [step, acquireLoop, Expr.eval, BinOp.eval, ht, hn, hnt]
    · simp only [waitLoop, hnt, ite_false] at hw
      let l1 := pull ε c l
      let v := BitVec.ofNat 32 (now l1)
      let loc1 := loc.set "n" v
      have ht1 : loc1 "t" = t := by simp [loc1, ht]
      have hn1 : loc1 "n" = v := by simp [loc1]
      obtain ⟨loc', hloc', hstar⟩ := ih v loc1 (⟨c, .getNow⟩ :: l1) r k ht1 hn1 hw
      refine ⟨loc', fun z hz => by rw [hloc' z hz]; simp [loc1, hz], ?_⟩
      refine .step (c' := ⟨.call "n" .getNow [], .loop (.bin .ne (.var "n") (.var "t"))
          (.call "n" .getNow []) k, loc, l⟩) ?_ ?_
      · simp [step, acquireLoop, Expr.eval, BinOp.eval, ht, hn, hnt]
      refine .step (c' := ⟨.skip, .loop (.bin .ne (.var "n") (.var "t"))
          (.call "n" .getNow []) k, loc1, ⟨c, .getNow⟩ :: l1⟩) ?_ ?_
      · simp [step, prims, loc1, v, l1]
      refine .step (c' := ⟨acquireLoop, k, loc1, ⟨c, .getNow⟩ :: l1⟩) ?_ hstar
      simp [step, acquireLoop]

theorem acquire_sim_loc (ε : EnvCtx) (c : CPU) (fuel : Nat) (loc : Locals) (l r : Log)
    (k : Cont Prim) (h : acquireSpec ε c fuel l = some r) :
    ∃ loc' : Locals, (∀ z, ¬ Rsv z → loc' z = loc z) ∧
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
  refine ⟨loc'.set "_" 0, fun z hz => ?_, ?_⟩
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

/-! ## Tables for ε_H -/

theorem lookup_short {g : HLog} : ∀ {tbl : List (HLog × List HEvent)},
    (∀ p ∈ tbl, p.1.length < g.length) → lookup g tbl = []
  | [], _ => rfl
  | p :: t, h => by
    have hne : g ≠ p.1 := fun e => by have := h p List.mem_cons_self; rw [e] at this; omega
    simp only [lookup, hne, ite_false]
    exact lookup_short (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem lookup_append_ne {g k : HLog} {E : List HEvent} (hne : g ≠ k) :
    ∀ tbl : List (HLog × List HEvent), lookup g (tbl ++ [(k, E)]) = lookup g tbl
  | [] => by simp [lookup, hne]
  | p :: t => by simp only [List.cons_append, lookup]; rw [lookup_append_ne hne t]

theorem lookup_append_new {k : HLog} {E : List HEvent} :
    ∀ {tbl : List (HLog × List HEvent)}, (∀ p ∈ tbl, p.1.length < k.length) →
      lookup k (tbl ++ [(k, E)]) = E
  | [], _ => by simp [lookup]
  | p :: t, h => by
    have hne : k ≠ p.1 := fun e => by have := h p List.mem_cons_self; rw [e] at this; omega
    simp only [List.cons_append, lookup, hne, ite_false]
    exact lookup_append_new (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem hprims_len {εH : HEnv} {c : CPU} {p : HPrim} {args : List Val} {h h' : HLog} {v : Val}
    (hp : hprims εH c p args h = some (v, h')) : h.length < h'.length := by
  cases p <;> cases args <;> simp [hprims] at hp
  · obtain ⟨-, -, rfl⟩ := hp; simp [hpull]; omega
  · obtain ⟨-, -, rfl⟩ := hp; simp

theorem hprims_congr {ε1 ε2 : HEnv} {c : CPU} {h : HLog} (hq : ε1.query c h = ε2.query c h)
    (p : HPrim) (args : List Val) : hprims ε1 c p args h = hprims ε2 c p args h := by
  have hp : hpull ε1 c h = hpull ε2 c h := by simp [hpull, hq]
  cases p <;> cases args <;> simp only [hprims, hp]

theorem hstar_len {εH : HEnv} {c : CPU} {x y : Config HPrim HLog} (h : Star (hprims εH c) x y) :
    x.abs.length ≤ y.abs.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step a b _ hs _ ih =>
    rcases step_cases (t := thr a) (a := a.abs) hs with ⟨he, -⟩ | ⟨⟨p, args, v, hv⟩, -⟩
    · rw [he] at ih; exact ih
    · exact Nat.le_trans (Nat.le_of_lt (hprims_len hv)) ih

theorem hstar_congr {ε1 ε2 : HEnv} {c : CPU} {x y : Config HPrim HLog} (h : Star (hprims ε1 c) x y)
    (hag : ∀ g : HLog, g.length < y.abs.length → ε2.query c g = ε1.query c g) :
    Star (hprims ε2 c) x y := by
  induction h with
  | refl => exact .refl _
  | @step a b y hs hrest ih =>
    refine .step ?_ (ih hag)
    rcases step_cases (t := thr a) (a := a.abs) hs with ⟨habs, hall⟩ | ⟨⟨p, args, v, hv⟩, hQ⟩
    · have := hall (hprims ε2 c) a.abs
      have h2 : (thr b).cfg a.abs = b := by rw [← habs]; rfl
      rw [h2] at this; exact this
    · have hlt : a.abs.length < y.abs.length := Nat.lt_of_lt_of_le (hprims_len hv) (hstar_len hrest)
      exact hQ (hprims ε2 c) a.abs fun p args => hprims_congr (hag a.abs hlt) p args

/-! ## The simulation -/

variable (ε : EnvCtx) (c : CPU)

/-- What the L0 configuration `x` corresponds to at L1, under a table-built ε_H. -/
def Sim (y0 : Config HPrim HLog) (x : Config Prim Log) : Prop :=
  ∃ (tbl : List (HLog × List HEvent)) (hE : ∀ p ∈ tbl, ∀ e ∈ p.2, e.cpu ≠ c),
    (∀ p ∈ tbl, ∃ o, hreplay (p.2 ++ p.1) = some o) ∧
    ∃ y, Star (hprims (HEnv.table c tbl hE) c) y0 y ∧
      ((Rel c x y ∧ ∀ p ∈ tbl, p.1.length < y.abs.length) ∨
       (∃ y' e, ClightL.step (hprims (HEnv.table c tbl hE) c) y = some y' ∧ Rel c e y' ∧
          Star (prims ε c) x e ∧ x ≠ e ∧ ∀ p ∈ tbl, p.1.length < y'.abs.length) ∨
       (ClightL.step (hprims (HEnv.table c tbl hE) c) y = none ∧ ¬ Final y))

variable {ε c}

theorem sim_step (hc : c < NCPU) (hR : RelyP ε c) (bound : Log → Nat)
    (hF : ∀ tn, FairP ε c tn bound) {y0 : Config HPrim HLog} {x x' : Config Prim Log}
    (hS : Sim ε c y0 x) (hs : ClightL.step (prims ε c) x = some x') : Sim ε c y0 x' := by
  obtain ⟨tbl, hE, htbl, y, hy, hcase⟩ := hS
  rcases hcase with ⟨hRel, hkeys⟩ | ⟨y', e, hy', hRe, hxe, hne, hkeys⟩ | hwrong
  · -- related: look at the L1 statement
    obtain ⟨ys, yk, yσ, yl⟩ := y
    by_cases hcall : ∃ z p args, ys = .call z p args
    · obtain ⟨z, p, args, rfl⟩ := hcall
      obtain ⟨xs, xk, xσ, xl⟩ := x
      obtain ⟨hs1, hk1, ⟨hok1, hok2⟩, hloc, s, hl, hph⟩ := hRel
      simp only at hs1 hk1 hok1 hok2 hloc hl
      subst hs1 hk1
      have hwrong : hprims (HEnv.table c tbl hE) c p (args.map (·.eval yσ)) yl = none →
          Sim ε c y0 x' := fun hnone =>
        ⟨tbl, hE, htbl, _, hy, .inr (.inr ⟨by simp [ClightL.step, CThread.cfg, hnone],
          fun h => by simp [Final] at h⟩)⟩
      cases p with
      | acq =>
        simp only [M, ClightL.step, Option.some.injEq] at hs; subst hs
        cases args with
        | cons a as => exact hwrong (by simp [hprims])
        | nil =>
        rcases hph with hidle | ⟨t, hhold⟩
        · -- the C acquire runs to completion, and one atomic `acq` matches it
          obtain ⟨fuel, r, hspec⟩ := acquire_live_proto hc hR hl hidle bound (hF _)
          obtain ⟨σ', hσ', hstarA⟩ :=
            acquire_sim_loc ε c fuel xσ xl r (.seq (.assign z (.const 0)) (Mk yk)) hspec
          obtain ⟨s', h₁, hr, hhold, hf⟩ := acquire_guarantee hc hR hl hidle hspec
          obtain ⟨xs, rfl⟩ := acquireSpec_ext hspec
          obtain ⟨E, rfl, hE1⟩ := hist_split hl hr rfl hf
          obtain ⟨o, ho, -⟩ := replay_hreplay hr
          have hfree : hreplay (E ++ yl) = some none := hreplay_acq ho
          let tbl' := tbl ++ [(yl, E)]
          have hE' : ∀ p ∈ tbl', ∀ e ∈ p.2, e.cpu ≠ c := by
            intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · exact hE p hp
            · simp only [List.mem_singleton] at hp; subst hp; exact hE1
          have hq : ∀ g : HLog, g ≠ yl → (HEnv.table c tbl' hE').query c g =
              (HEnv.table c tbl hE).query c g := by
            intro g hg; simp [HEnv.table, tbl', lookup_append_ne hg]
          have hy' : Star (hprims (HEnv.table c tbl' hE') c) y0 ⟨.call z .acq [], yk, yσ, yl⟩ :=
            hstar_congr hy fun g hg => hq g (fun e => by subst e; simp at hg)
          have hprim : hprims (HEnv.table c tbl' hE') c .acq [] yl = some (0, .acq c :: (E ++ yl)) := by
            simp [hprims, hpull_table, tbl', lookup_append_new hkeys, hfree]
          refine ⟨tbl', hE', fun p hp => ?_, _, hy', .inr (.inl ⟨⟨.skip, yk, yσ.set z 0, .acq c :: (E ++ yl)⟩,
            ⟨.skip, Mk yk, σ'.set z 0, xs ++ xl⟩, by simp [ClightL.step, CThread.cfg, hprim], ?_, ?_,
            fun h => by simp [acquireCode] at h, ?_⟩)⟩
          · rcases List.mem_append.1 hp with hp | hp
            · exact htbl p hp
            · simp only [List.mem_singleton] at hp; subst hp; exact ⟨_, hfree⟩
          · refine ⟨rfl, rfl, ⟨trivial, hok2⟩, ?_, s', hr, .inr ⟨_, hhold⟩⟩
            exact set_agree (fun w hw => by rw [hσ' w hw]; exact hloc w hw) z 0
          · refine hstarA.trans (.step (c' := ⟨.assign z (.const 0), Mk yk, σ', xs ++ xl⟩)
              (by simp [ClightL.step]) (.single ?_))
            simp [ClightL.step, Expr.eval]
          · intro p hp
            rcases List.mem_append.1 hp with hp | hp
            · have := hkeys p hp; simp only at this; simp; omega
            · simp only [List.mem_singleton] at hp; subst hp
              simp only [List.length_cons, List.length_append]; omega
        · -- `acq` while holding: L1 is stuck
          refine hwrong ?_
          have hh := hreplay_of_holding hl hhold
          simp [hprims, hpull_table, lookup_short hkeys, hh]
      | rel =>
        simp only [M, ClightL.step, Option.some.injEq] at hs; subst hs
        cases args with
        | cons a as => exact hwrong (by simp [hprims])
        | nil =>
        rcases hph with hidle | ⟨t, hhold⟩
        · -- `rel` without the lock: L1 is stuck
          refine hwrong ?_
          obtain ⟨o, ho, hH⟩ := replay_hreplay hl
          have hno : o ≠ some c := fun e => by
            obtain ⟨t, ht⟩ := (hH c).2 e; rw [hidle] at ht; cases ht
          simp [hprims, ho, hno]
        · obtain ⟨-, -, -, hrelLog⟩ := release_refines_atomic hc hR hl hhold xσ
          obtain ⟨s', h₁, hr, hidle', -⟩ := release_guarantee hc hR hl hhold
          obtain ⟨s'', hr'⟩ := hrelLog
          rw [hr] at hr'; simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at hr'
          obtain ⟨-, -, hh1⟩ := hr'
          rw [hh1] at hr
          have hheld := hreplay_of_holding hl hhold
          have hprim : hprims (HEnv.table c tbl hE) c .rel [] yl = some (0, .rel c :: yl) := by
            simp [hprims, hheld]
          refine ⟨tbl, hE, htbl, _, hy, .inr (.inl ⟨⟨.skip, yk, yσ.set z 0, .rel c :: yl⟩,
            ⟨.skip, Mk yk, (xσ.set "_" 0).set z 0, releaseSpec ε c xl⟩,
            by simp [ClightL.step, CThread.cfg, hprim], ?_, ?_, fun h => by simp [releaseCode] at h, ?_⟩)⟩
          · refine ⟨rfl, rfl, ⟨trivial, hok2⟩, ?_, s', hr, .inl hidle'⟩
            refine set_agree (fun w hw => ?_) z 0
            have : w ≠ "_" := fun e => hw (.inr (.inr e))
            simp [Locals.set, this, hloc w hw]
          · refine .step (c' := ⟨.skip, .seq (.assign z (.const 0)) (Mk yk), xσ.set "_" 0,
              releaseSpec ε c xl⟩) (by simp [ClightL.step, releaseCode, prims, releaseSpec]) ?_
            refine .step (c' := ⟨.assign z (.const 0), Mk yk, xσ.set "_" 0, releaseSpec ε c xl⟩)
              (by simp [ClightL.step]) (.single ?_)
            simp [ClightL.step, Expr.eval]
          · intro p hp; have := hkeys p hp; simp only at this; simp; omega
    · have hnc : ∀ z p args, ys ≠ .call z p args := fun z p args e => hcall ⟨z, p, args, e⟩
      obtain ⟨y', hy1, hRel', habs⟩ := step_match (Q := hprims (HEnv.table c tbl hE) c) hRel hnc hs
      refine ⟨tbl, hE, htbl, y', hy.trans (.single hy1), .inl ⟨hRel', ?_⟩⟩
      rw [habs]; exact hkeys
  · -- inside a C block: follow it to its end
    cases hxe with
    | refl => exact absurd rfl hne
    | step hs2 hrest =>
      rw [hs] at hs2; cases hs2
      by_cases hend : x' = e
      · subst hend
        exact ⟨tbl, hE, htbl, y', hy.trans (.single hy'), .inl ⟨hRe, hkeys⟩⟩
      · exact ⟨tbl, hE, htbl, y, hy, .inr (.inl ⟨y', e, hy', hRe, hrest, hend, hkeys⟩)⟩
  · exact ⟨tbl, hE, htbl, y, hy, .inr (.inr hwrong)⟩

/-- **Contextual refinement, step by step.** For every client `P` and every L0
execution of the linked program `M P` under an environment satisfying the
rely and fairness, the execution is explained by the atomic L1 execution of
`P` under one table-built `ε_H`. -/
theorem client_sim (hc : c < NCPU) (hR : RelyP ε c) (bound : Log → Nat)
    (hF : ∀ tn, FairP ε c tn bound) (P : Stmt HPrim) (hP : SOK P) (σ : Locals) {l : Log}
    {s : PState} {h : HLog} (hl : replay l = some (s, h))
    (hph : s.phase c = .idle ∨ ∃ t, s.phase c = .holding t) {x : Config Prim Log}
    (hx : Star (prims ε c) ⟨M P, .stop, σ, l⟩ x) : Sim ε c ⟨P, .stop, σ, h⟩ x := by
  have h0 : Sim ε c ⟨P, .stop, σ, h⟩ ⟨M P, .stop, σ, l⟩ :=
    ⟨[], by simp, by simp, _, .refl _,
      .inl ⟨⟨rfl, rfl, ⟨hP, trivial⟩, fun _ _ => rfl, s, hl, hph⟩, by simp⟩⟩
  suffices ∀ {a b}, Star (prims ε c) a b → Sim ε c ⟨P, .stop, σ, h⟩ a → Sim ε c ⟨P, .stop, σ, h⟩ b from
    this hx h0
  intro a b hab
  induction hab with
  | refl => exact id
  | step hs _ ih => exact fun hS => ih (sim_step hc hR bound hF hS hs)

/-- **Finished runs.** If the linked L0 program finishes, then under an `ε_H`
satisfying `HRely` the L1 client finishes too, with the same non-reserved
locals and a related log (or the client went wrong at L1). -/
theorem client_final (hc : c < NCPU) (hR : RelyP ε c) (bound : Log → Nat)
    (hF : ∀ tn, FairP ε c tn bound) (P : Stmt HPrim) (hP : SOK P) (σ : Locals) {l : Log}
    {s : PState} {h : HLog} (hl : replay l = some (s, h))
    (hph : s.phase c = .idle ∨ ∃ t, s.phase c = .holding t) {σ' : Locals} {l' : Log}
    (hx : Star (prims ε c) ⟨M P, .stop, σ, l⟩ ⟨.skip, .stop, σ', l'⟩) :
    ∃ εH : HEnv, HRely εH c ∧ ∃ y, Star (hprims εH c) ⟨P, .stop, σ, h⟩ y ∧
      ((y.stmt = .skip ∧ y.cont = .stop ∧ (∀ z, ¬ Rsv z → σ' z = y.locals z) ∧ RelLog l' y.abs) ∨
       (ClightL.step (hprims εH c) y = none ∧ ¬ Final y)) := by
  obtain ⟨tbl, hE, htbl, y, hy, hcase⟩ := client_sim hc hR bound hF P hP σ hl hph hx
  refine ⟨HEnv.table c tbl hE, table_rely c tbl hE htbl, y, hy, ?_⟩
  rcases hcase with ⟨⟨hs1, hk1, -, hloc, s', hr, -⟩, -⟩ | ⟨y', e, -, -, hxe, hne, -⟩ | hw
  · left
    obtain ⟨ys, yk, yσ, yl⟩ := y
    simp only at hs1 hk1 hloc hr ⊢
    refine ⟨?_, ?_, hloc, s', hr⟩
    · cases ys with
      | skip => rfl
      | call z p args => cases p <;> simp [M] at hs1
      | _ => simp [M] at hs1
    · cases yk <;> simp [Mk] at hk1 ⊢
  · cases hxe with
    | refl => exact absurd rfl hne
    | step hs2 _ => simp [ClightL.step] at hs2
  · exact .inr hw

/-- **Not vacuous.** Under the concrete fair scheduler `fairEnv` (which
satisfies the rely and fairness for every CPU), every finished run of a linked
client from the empty log is matched at L1. -/
theorem client_final_fair {c : CPU} (hc : c < NCPU) (P : Stmt HPrim) (hP : SOK P) (σ : Locals)
    {σ' : Locals} {l' : Log}
    (hx : Star (prims fairEnv c) ⟨M P, .stop, σ, []⟩ ⟨.skip, .stop, σ', l'⟩) :
    ∃ εH : HEnv, HRely εH c ∧ ∃ y, Star (hprims εH c) ⟨P, .stop, σ, []⟩ y ∧
      ((y.stmt = .skip ∧ y.cont = .stop ∧ (∀ z, ¬ Rsv z → σ' z = y.locals z) ∧ RelLog l' y.abs) ∨
       (ClightL.step (hprims εH c) y = none ∧ ¬ Final y)) :=
  client_final hc (fairEnv_rely c) fairBound (fun tn => fairEnv_fair c tn hc) P hP σ
    (s := PState.init) rfl (.inl rfl) hx

end ClientRefine
