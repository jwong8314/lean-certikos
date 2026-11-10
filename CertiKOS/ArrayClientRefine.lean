import CertiKOS.LockArrayFair
import CertiKOS.ClientRefine

/-!
# Contextual refinement for every client of the lock array

The lock-array version of `ClientRefine.lean`. A client is any ClightL program
over the atomic primitives with data: `x := acq(e)` takes lock `e` and
returns the contents of its block, and `x := rel(e₁, e₂)` stores `e₂` into
block `e₁` and releases. The client may use any number of locks, nested or
interleaved.

* **Linking** (`M`): `x := acq(e)` becomes `lk = e; acquire(lk); x = v`, and
  `x := rel(e₁, e₂)` becomes `lk = e₁; v = e₂; release(lk); x = 0`. These are
  the verified C blocks of `LockArrayCPU.lean`, inlined. Clients may not use
  the five locals of that code (`t`, `n`, `_`, `v`, `lk`).
* **The relation** (`Rel`). Same program point, same client locals, and the
  L0 log replays to the L1 log *plus other CPUs' later events*. While we hold
  a lock, other CPUs keep using other locks, and L1 sees those events at its
  next query. Every lock is idle or held by us, never half-acquired.
* `client_sim`: every L0 configuration is related, or inside one C block
  whose end is reachable and related to the L1 configuration one atomic step
  later, or the client already went wrong at L1. One table-built `ε_H`
  (`HRelyA`) serves the whole run. The data a C `acquire` pulls is the value
  the atomic `acq` returns.
* `client_final`, `client_final_fair` (under the concrete `fairEnvA`).
-/

namespace ArrayClient

open ClightL Ticket Link ClightToPy LockArray

/-! ## Clients and linking -/

def Rsv (z : Ident) : Prop := z = "t" ∨ z = "n" ∨ z = "_" ∨ z = "v" ∨ z = "lk"

def EOK : Expr → Prop
  | .const _ => True
  | .var x => ¬ Rsv x
  | .bin _ a b => EOK a ∧ EOK b

def SOK : Stmt HPrimA → Prop
  | .skip => True
  | .assign x e => ¬ Rsv x ∧ EOK e
  | .seq a b => SOK a ∧ SOK b
  | .ite e a b => EOK e ∧ SOK a ∧ SOK b
  | .while e b => EOK e ∧ SOK b
  | .call x _ args => ¬ Rsv x ∧ ∀ e ∈ args, EOK e

def KOK : Cont HPrimA → Prop
  | .stop => True
  | .seq s k => SOK s ∧ KOK k
  | .loop e b k => EOK e ∧ SOK b ∧ KOK k

def M : Stmt HPrimA → Stmt APrim
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq a b => .seq (M a) (M b)
  | .ite e a b => .ite e (M a) (M b)
  | .while e b => .while e (M b)
  | .call x .acq [e] => .seq (.assign "lk" e) (.seq acquireA (.assign x (.var "v")))
  | .call x .rel [e₁, e₂] =>
      .seq (.assign "lk" e₁) (.seq (.assign "v" e₂) (.seq releaseA (.assign x (.const 0))))
  | .call _ _ _ => .call "_" .faiTicket []   -- ill-formed call: stuck at L0 as at L1

def Mk : Cont HPrimA → Cont APrim
  | .stop => .stop
  | .seq s k => .seq (M s) (Mk k)
  | .loop e b k => .loop e (M b) (Mk k)

def Clean (c : CPU) (S : AState) : Prop := ∀ j, (S.lk j).phase c = .idle ∨ ∃ t, (S.lk j).phase c = .holding t

structure Rel (c : CPU) (x : Config APrim ALog) (y : Config HPrimA HLogA) : Prop where
  stmt : x.stmt = M y.stmt
  cont : x.cont = Mk y.cont
  ok : SOK y.stmt ∧ KOK y.cont
  loc : ∀ z, ¬ Rsv z → x.locals z = y.locals z
  log : ∃ S E, areplay x.abs = some (S, E ++ y.abs) ∧ (∀ e ∈ E, e.cpu ≠ c) ∧ Clean c S

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

theorem step_match {c : CPU} {P : Prims APrim ALog} {Q : Prims HPrimA HLogA} {x x' : Config APrim ALog}
    {y : Config HPrimA HLogA} (hR : Rel c x y) (hnc : ∀ z p args, y.stmt ≠ .call z p args)
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

/-! ## Tables for ε_H -/

def lookupA (h : HLogA) : List (HLogA × List HEventA) → List HEventA
  | [] => []
  | p :: t => if h = p.1 then p.2 else lookupA h t

theorem lookupA_cases (h : HLogA) : ∀ tbl : List (HLogA × List HEventA),
    lookupA h tbl = [] ∨ ∃ p ∈ tbl, p.1 = h ∧ lookupA h tbl = p.2
  | [] => Or.inl rfl
  | p :: t => by
    by_cases hp : h = p.1
    · exact Or.inr ⟨p, List.mem_cons_self, hp.symm, by simp [lookupA, hp]⟩
    · rcases lookupA_cases h t with h1 | ⟨q, hq, h2, h3⟩
      · exact Or.inl (by simp [lookupA, hp, h1])
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h2, by simp [lookupA, hp, h3]⟩

def tableA (c : CPU) (tbl : List (HLogA × List HEventA)) (hE : ∀ p ∈ tbl, ∀ e ∈ p.2, e.cpu ≠ c) :
    HEnvA where
  query d h := if d = c then lookupA h tbl else []
  noSelf := by
    intro d h e he
    by_cases hd : d = c
    · subst hd
      rw [if_pos rfl] at he
      rcases lookupA_cases h tbl with h1 | ⟨p, hp, -, h3⟩
      · rw [h1] at he; simp at he
      · rw [h3] at he; exact hE p hp e he
    · simp [hd] at he

theorem hpullA_table (c : CPU) (tbl) (hE) (h : HLogA) : hpullA (tableA c tbl hE) c h = lookupA h tbl ++ h := by
  simp [hpullA, tableA]

theorem tableA_rely (c : CPU) (tbl) (hE)
    (htbl : ∀ p ∈ tbl, ∀ j, ∃ o, hreplay (projH j (p.2 ++ p.1)) = some o) : HRelyA (tableA c tbl hE) c := by
  intro h hh j
  rw [hpullA_table]
  rcases lookupA_cases h tbl with h1 | ⟨p, hp, h2, h3⟩
  · rw [h1]; exact hh j
  · rw [h3]; subst h2; exact htbl p hp j

theorem lookupA_short {g : HLogA} : ∀ {tbl : List (HLogA × List HEventA)},
    (∀ p ∈ tbl, p.1.length < g.length) → lookupA g tbl = []
  | [], _ => rfl
  | p :: t, h => by
    have hne : g ≠ p.1 := fun e => by have := h p List.mem_cons_self; rw [e] at this; omega
    simp only [lookupA, hne, ite_false]
    exact lookupA_short (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem lookupA_append_ne {g k : HLogA} {E : List HEventA} (hne : g ≠ k) :
    ∀ tbl : List (HLogA × List HEventA), lookupA g (tbl ++ [(k, E)]) = lookupA g tbl
  | [] => by simp [lookupA, hne]
  | p :: t => by simp only [List.cons_append, lookupA]; rw [lookupA_append_ne hne t]

theorem lookupA_append_new {k : HLogA} {E : List HEventA} :
    ∀ {tbl : List (HLogA × List HEventA)}, (∀ p ∈ tbl, p.1.length < k.length) →
      lookupA k (tbl ++ [(k, E)]) = E
  | [], _ => by simp [lookupA]
  | p :: t, h => by
    have hne : k ≠ p.1 := fun e => by have := h p List.mem_cons_self; rw [e] at this; omega
    simp only [List.cons_append, lookupA, hne, ite_false]
    exact lookupA_append_new (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem hprimsA_len {εH : HEnvA} {c : CPU} {p : HPrimA} {args : List Val} {h h' : HLogA} {v : Val}
    (hp : hprimsA εH c p args h = some (v, h')) : h.length < h'.length := by
  unfold hprimsA at hp
  split at hp <;> (try split at hp) <;> simp at hp <;> obtain ⟨-, -, rfl⟩ := hp <;> simp [hpullA] <;> omega

theorem hprimsA_congr {ε1 ε2 : HEnvA} {c : CPU} {h : HLogA} (hq : ε1.query c h = ε2.query c h)
    (p : HPrimA) (args : List Val) : hprimsA ε1 c p args h = hprimsA ε2 c p args h := by
  have hp : hpullA ε1 c h = hpullA ε2 c h := by simp [hpullA, hq]
  unfold hprimsA; split <;> simp only [hp]

theorem hstarA_len {εH : HEnvA} {c : CPU} {x y : Config HPrimA HLogA} (h : Star (hprimsA εH c) x y) :
    x.abs.length ≤ y.abs.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step a b _ hs _ ih =>
    rcases step_cases (t := thr a) (a := a.abs) hs with ⟨he, -⟩ | ⟨⟨p, args, v, hv⟩, -⟩
    · rw [he] at ih; exact ih
    · exact Nat.le_trans (Nat.le_of_lt (hprimsA_len hv)) ih

theorem hstarA_congr {ε1 ε2 : HEnvA} {c : CPU} {x y : Config HPrimA HLogA} (h : Star (hprimsA ε1 c) x y)
    (hag : ∀ g : HLogA, g.length < y.abs.length → ε2.query c g = ε1.query c g) :
    Star (hprimsA ε2 c) x y := by
  induction h with
  | refl => exact .refl _
  | @step a b y hs hrest ih =>
    refine .step ?_ (ih hag)
    rcases step_cases (t := thr a) (a := a.abs) hs with ⟨habs, hall⟩ | ⟨⟨p, args, v, hv⟩, hQ⟩
    · have := hall (hprimsA ε2 c) a.abs
      have h2 : (thr b).cfg a.abs = b := by rw [← habs]; rfl
      rw [h2] at this; exact this
    · have hlt : a.abs.length < y.abs.length := Nat.lt_of_lt_of_le (hprimsA_len hv) (hstarA_len hrest)
      exact hQ (hprimsA ε2 c) a.abs fun p args => hprimsA_congr (hag a.abs hlt) p args

/-! ## A lock block only touches its own lock -/

def OwnOn (c : CPU) (i : Nat) (xs : ALog) : Prop := ∀ e ∈ xs, e.cpu = c → e.lk = i

def ExtOwn (c : CPU) (i : Nat) (r l : ALog) : Prop := ∃ xs, r = xs ++ l ∧ OwnOn c i xs

theorem eo_refl (c : CPU) (i : Nat) (l : ALog) : ExtOwn c i l l := ⟨[], rfl, by simp [OwnOn]⟩

theorem eo_pull (ε : AEnv) {c : CPU} {i : Nat} {r l : ALog} (h : ExtOwn c i r l) :
    ExtOwn c i (apull ε c r) l := by
  obtain ⟨xs, rfl, hown⟩ := h
  refine ⟨ε.query c (xs ++ l) ++ xs, by simp [apull], fun e he hec => ?_⟩
  rcases List.mem_append.1 he with h1 | h2
  · exact absurd hec (ε.noSelf c _ e h1)
  · exact hown e h2 hec

theorem eo_cons {c : CPU} {i : Nat} (e : AEvent) (he : e.cpu = c → e.lk = i) {r l : ALog}
    (h : ExtOwn c i r l) : ExtOwn c i (e :: r) l := by
  obtain ⟨xs, rfl, hown⟩ := h
  refine ⟨e :: xs, rfl, fun e' he' hec => ?_⟩
  rcases List.mem_cons.1 he' with rfl | h2
  · exact he hec
  · exact hown e' h2 hec

theorem eo_waitLoop (ε : AEnv) (c : CPU) (i : Nat) (t : Val) :
    ∀ f n r r' l, waitLoopA ε c i t f n r = some r' → ExtOwn c i r l → ExtOwn c i r' l := by
  intro f
  induction f with
  | zero => intro n r r' l h hr; by_cases hnt : n = t <;> simp_all [waitLoopA]
  | succ f ih =>
    intro n r r' l h hr
    by_cases hnt : n = t
    · simp [waitLoopA, hnt] at h; subst h; exact hr
    · simp only [waitLoopA, hnt, ite_false] at h
      exact ih _ _ _ _ h (eo_cons _ (fun _ => rfl) (eo_pull ε hr))

theorem acquireSpecA_own {ε : AEnv} {c : CPU} {i fuel : Nat} {l r : ALog}
    (h : acquireSpecA ε c i fuel l = some r) : ExtOwn c i r l := by
  simp only [acquireSpecA, Option.map_eq_some_iff] at h
  obtain ⟨r0, hw, rfl⟩ := h
  have h0 := eo_waitLoop ε c i _ _ _ _ _ l hw
    (eo_cons _ (fun _ => rfl) (eo_pull ε (eo_cons _ (fun _ => rfl) (eo_pull ε (eo_refl c i l)))))
  exact eo_cons _ (fun _ => rfl) (eo_pull ε (eo_cons _ (fun _ => rfl) (eo_pull ε h0)))

theorem releaseSpecA_own (ε : AEnv) (c : CPU) (i : Nat) (v : Val) (l : ALog) :
    ExtOwn c i (releaseSpecA ε c i v l) l :=
  eo_cons _ (fun _ => rfl) (eo_pull ε (eo_cons _ (fun _ => rfl) (eo_pull ε (eo_refl c i l))))

/-- Events on other locks, and other CPUs' events, leave our phase on lock `j` alone. -/
theorem phase_frame {c : CPU} {i : Nat} {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) :
    ∀ (xs : ALog), OwnOn c i xs → ∀ {S' : AState} {H' : HLogA}, areplay (xs ++ l) = some (S', H') →
      ∀ j, j ≠ i → (S'.lk j).phase c = (S.lk j).phase c
  | [], _, S', H', hr, j, _ => by simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; rfl
  | e :: xs, hown, S', H', hr, j, hj => by
    obtain ⟨S2, H2, o, hl2, hp, -⟩ := areplay_cons hr
    have ih := phase_frame hl xs (fun e' he' => hown e' (List.mem_cons_of_mem _ he')) hl2 j hj
    rw [← ih]
    obtain ⟨d, j', k⟩ := e
    cases k with
    | tk k =>
      simp only [astep] at hp
      split at hp
      · simp at hp
      · rename_i p' o' hps
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        by_cases hjj : j' = j
        · subst hjj
          have hne : d ≠ c := fun hdc => hj (hown _ List.mem_cons_self hdc)
          simpa using (pstep_other hps hne).1
        · simp [LockArray.upd, Ne.symm hjj]
    | pull =>
      simp only [astep] at hp; split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; rfl
      · simp at hp
    | push v =>
      simp only [astep] at hp; split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; rfl
      · simp at hp

/-! ## The two C blocks, measured against a base log -/

theorem hreplay_held_top : ∀ (A : List HEvent) {B : List HEvent} {c : CPU},
    (∀ e ∈ A, e.cpu ≠ c) → hreplay (A ++ B) = some (some c) → A = []
  | [], _, _, _, _ => rfl
  | a :: A, B, c, hA, h => by
    exfalso
    simp only [List.cons_append, hreplay] at h
    split at h
    · simp at h
    · rename_i o ho
      have hac := hA a List.mem_cons_self
      cases a with
      | acq d => cases o <;> simp [hstep] at h; subst h; exact hac rfl
      | rel d => cases o <;> simp [hstep] at h <;> (try (split at h <;> simp at h))

theorem acquireA_decomp {ε : AEnv} {c : CPU} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {HL : HLogA} (hl : areplay l = some (S, HL)) {iv : Val}
    (hidle : (S.lk iv.toNat).phase c = .idle) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : ∀ tn, FairA ε c iv.toNat tn bound) (σ : Locals) (hlk : σ "lk" = iv) (k : Cont APrim) :
    ∃ (r : ALog) (σ' : Locals) (E2 E1 : HLogA) (S3 : AState),
      Star (aprims ε c) ⟨acquireA, k, σ, l⟩ ⟨.skip, k, σ', r⟩ ∧
      areplay r = some (S3, E2 ++ .acqA c iv.toNat :: (E1 ++ HL)) ∧
      (∀ e ∈ E2, e.cpu ≠ c) ∧ (∀ e ∈ E1, e.cpu ≠ c) ∧ Holding S3 c iv.toNat ∧
      σ' "v" = hmemA iv.toNat (E1 ++ HL) ∧ hreplay (projH iv.toNat (E1 ++ HL)) = some none ∧
      (∀ j, ∃ o, hreplay (projH j (E1 ++ HL)) = some o) ∧
      (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ' z = σ z) ∧
      (∀ j, j ≠ iv.toNat → (S3.lk j).phase c = (S.lk j).phase c) := by
  obtain ⟨r, hspec⟩ := acquireA_live_bounded hc hR hl hidle bound K hK (hF _)
  obtain ⟨r0, σ', hr0, hv, hfr, hstar⟩ := acquireA_sim ε c _ σ iv l r k hlk hspec
  obtain ⟨r0', hr0', S3, H3, hr3, hhold3, hf3, hv3⟩ := acquireA_guarantee hc hR hl hidle hspec
  have hval : σ' "v" = hmemA iv.toNat H3 := by
    have e1 : σ' "v" = memOf iv.toNat r.tail := by rw [hv, hr0]; rfl
    have e2 : memOf iv.toNat (apull ε c (ev c iv.toNat .hold :: apull ε c r0')) = memOf iv.toNat r.tail := by
      rw [hr0']; rfl
    rw [e1, ← e2, hv3]
  obtain ⟨xs, hxs, hown⟩ := acquireSpecA_own hspec
  subst hxs
  have hframe := phase_frame hl xs hown hr3
  obtain ⟨E, hE⟩ := areplay_hext hl xs hr3
  have hfE : cpuFilterA c E = [.acqA c iv.toNat] := by
    rw [hE] at hf3; simp only [cpuFilterA, List.filter_append] at hf3
    exact List.append_cancel_right hf3
  obtain ⟨E2, E1, rfl, hE2, hE1⟩ := filter_single (by rfl) hfE
  have hE' : H3 = E2 ++ (.acqA c iv.toNat :: (E1 ++ HL)) := by rw [hE]; simp
  have hall : ∀ j, ∃ o, hreplay (projH j H3) = some o := fun j =>
    let ⟨o, ho, _⟩ := replay_hreplay (areplay_proj hr3 j); ⟨o, ho⟩
  have hsplit : ∀ j, projH j H3 = (projH j E2 ++ projH j [.acqA c iv.toNat]) ++ projH j (E1 ++ HL) := by
    intro j
    rw [hE', show E2 ++ HEventA.acqA c iv.toNat :: (E1 ++ HL) = E2 ++ ([.acqA c iv.toNat] ++ (E1 ++ HL))
      from rfl, projH_append, projH_append, List.append_assoc]
  have hsuf : ∀ j, ∃ o, hreplay (projH j (E1 ++ HL)) = some o := fun j => by
    obtain ⟨o, ho⟩ := hall j; rw [hsplit j] at ho; exact hreplay_suffix _ ho
  have hi3 : projH iv.toNat H3 = projH iv.toNat E2 ++ (.acq c :: projH iv.toNat (E1 ++ HL)) := by
    rw [hE', projH_append]; simp [projH]
  obtain ⟨o3, ho3⟩ := hall iv.toNat
  rw [hi3] at ho3
  obtain ⟨o4, ho4⟩ := hreplay_suffix _ ho3
  have hfree : hreplay (projH iv.toNat (E1 ++ HL)) = some none := hreplay_acq ho4
  have hheld : hreplay (.acq c :: projH iv.toNat (E1 ++ HL)) = some (some c) := by
    simp [hreplay, hfree, hstep]
  have hE2i : projH iv.toNat E2 = [] := held_no_env hheld _ (projH_cpu hE2) ho3
  have hval' : σ' "v" = hmemA iv.toNat (E1 ++ HL) := by
    rw [hval, hE', hmemA_skip hE2i]; simp [hmemA]
  exact ⟨_, σ', E2, E1, S3, hstar, by rw [← hE']; exact hr3, hE2, hE1, hhold3, hval', hfree, hsuf,
    hfr, hframe⟩

theorem releaseA_decomp {ε : AEnv} {c : CPU} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {HL : HLogA} (hl : areplay l = some (S, HL)) {i : Nat}
    (hhold : Holding S c i) (v : Val) :
    ∃ (E : HLogA) (S' : AState),
      areplay (releaseSpecA ε c i v l) = some (S', .relA c i v :: (E ++ HL)) ∧ (∀ e ∈ E, e.cpu ≠ c) ∧
      (S'.lk i).phase c = .idle ∧ hreplay (projH i (E ++ HL)) = some (some c) ∧
      (∀ j, ∃ o, hreplay (projH j (E ++ HL)) = some o) ∧
      (∀ j, j ≠ i → (S'.lk j).phase c = (S.lk j).phase c) := by
  obtain ⟨S', H', hr, hidle, ⟨E, rfl, hE⟩, -⟩ := releaseA_guarantee hc hR hl hhold v
  obtain ⟨xs, hxs, hown⟩ := releaseSpecA_own ε c i v l
  have hframe := phase_frame hl xs hown (by rw [← hxs]; exact hr)
  have hall : ∀ j, ∃ o, hreplay (projH j (.relA c i v :: (E ++ HL))) = some o := fun j =>
    let ⟨o, ho, _⟩ := replay_hreplay (areplay_proj hr j); ⟨o, ho⟩
  have hsuf : ∀ j, ∃ o, hreplay (projH j (E ++ HL)) = some o := fun j => by
    obtain ⟨o, ho⟩ := hall j
    rw [show HEventA.relA c i v :: (E ++ HL) = [.relA c i v] ++ (E ++ HL) from rfl, projH_append] at ho
    exact hreplay_suffix _ ho
  obtain ⟨o, ho⟩ := hall i
  have hheld : hreplay (projH i (E ++ HL)) = some (some c) := by
    simp only [projH, ite_true] at ho; exact hreplay_rel ho
  exact ⟨E, S', hr, hE, hidle, hheld, hsuf, hframe⟩

/-! ## The simulation -/

variable (ε : AEnv) (c : CPU)

def Sim (y0 : Config HPrimA HLogA) (x : Config APrim ALog) : Prop :=
  ∃ (tbl : List (HLogA × List HEventA)) (hE : ∀ p ∈ tbl, ∀ e ∈ p.2, e.cpu ≠ c),
    (∀ p ∈ tbl, ∀ j, ∃ o, hreplay (projH j (p.2 ++ p.1)) = some o) ∧
    ∃ y, Star (hprimsA (tableA c tbl hE) c) y0 y ∧
      ((Rel c x y ∧ ∀ p ∈ tbl, p.1.length < y.abs.length) ∨
       (∃ y' e, ClightL.step (hprimsA (tableA c tbl hE) c) y = some y' ∧ Rel c e y' ∧
          Star (aprims ε c) x e ∧ x ≠ e ∧ ∀ p ∈ tbl, p.1.length < y'.abs.length) ∨
       (ClightL.step (hprimsA (tableA c tbl hE) c) y = none ∧ ¬ Final y))

variable {ε c}

theorem table_extend {tbl : List (HLogA × List HEventA)} {hE : ∀ p ∈ tbl, ∀ e ∈ p.2, e.cpu ≠ c}
    {y0 y : Config HPrimA HLogA} (hy : Star (hprimsA (tableA c tbl hE) c) y0 y)
    (hkeys : ∀ p ∈ tbl, p.1.length < y.abs.length) {F : List HEventA} (hF : ∀ e ∈ F, e.cpu ≠ c) :
    ∃ hE' : (∀ p ∈ tbl ++ [(y.abs, F)], ∀ e ∈ p.2, e.cpu ≠ c),
      Star (hprimsA (tableA c (tbl ++ [(y.abs, F)]) hE') c) y0 y ∧
      hpullA (tableA c (tbl ++ [(y.abs, F)]) hE') c y.abs = F ++ y.abs := by
  have hE' : ∀ p ∈ tbl ++ [(y.abs, F)], ∀ e ∈ p.2, e.cpu ≠ c := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hE p hp
    · simp only [List.mem_singleton] at hp; subst hp; exact hF
  refine ⟨hE', hstarA_congr hy fun g hg => ?_, by rw [hpullA_table, lookupA_append_new hkeys]⟩
  have hne : g ≠ y.abs := fun e => by subst e; simp at hg
  simp [tableA, lookupA_append_ne hne]

theorem sim_step (hc : c < NCPU) (hR : RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : ∀ i tn, FairA ε c i tn bound) {y0 : Config HPrimA HLogA} {x x' : Config APrim ALog}
    (hS : Sim ε c y0 x) (hs : ClightL.step (aprims ε c) x = some x') : Sim ε c y0 x' := by
  obtain ⟨tbl, hE, htbl, y, hy, hcase⟩ := hS
  rcases hcase with ⟨hRel, hkeys⟩ | ⟨y', e, hy', hRe, hxe, hne, hkeys⟩ | hwrong
  · obtain ⟨ys, yk, yσ, yl⟩ := y
    by_cases hcall : ∃ z p args, ys = .call z p args
    · obtain ⟨z, p, args, rfl⟩ := hcall
      obtain ⟨xs, xk, xσ, xl⟩ := x
      obtain ⟨hs1, hk1, ⟨hok1, hok2⟩, hloc, S, E, hl, hEo, hclean⟩ := hRel
      simp only at hs1 hk1 hok1 hok2 hloc hl
      subst hs1 hk1
      have hwrong : hprimsA (tableA c tbl hE) c p (args.map (·.eval yσ)) yl = none → Sim ε c y0 x' :=
        fun hnone => ⟨tbl, hE, htbl, _, hy, .inr (.inr ⟨by simp [ClightL.step, CThread.cfg, hnone],
          fun h => by simp [Final] at h⟩)⟩
      have hstuck : ∀ {w : Ident}, ClightL.step (aprims ε c)
          ⟨.call w .faiTicket [], Mk yk, xσ, xl⟩ ≠ some x' := by
        intro w h; simp [ClightL.step, aprims] at h
      have hpl0 : hpullA (tableA c tbl hE) c yl = yl := by
        rw [hpullA_table, lookupA_short hkeys]; rfl
      -- what L0's protocol state says about lock `i` at L1
      have hproj : ∀ i, ∃ o, hreplay (projH i E ++ projH i yl) = some o ∧ Holds (S.lk i) o := fun i => by
        obtain ⟨o, ho, hH⟩ := replay_hreplay (areplay_proj hl i)
        rw [projH_append] at ho; exact ⟨o, ho, hH⟩
      cases p with
      | acq =>
        match args, hs, hwrong, hok1 with
        | [], hs, _, _ => exact absurd hs hstuck
        | _ :: _ :: _, hs, _, _ => exact absurd hs hstuck
        | [ea], hs, hwrong, hok1 =>
        simp only [M, ClightL.step, Option.some.injEq] at hs; subst hs
        have hea : ea.eval xσ = ea.eval yσ := eval_agree hloc ea (hok1.2 ea (by simp))
        generalize hiv : ea.eval yσ = iv at hwrong
        rcases hclean iv.toNat with hidle | ⟨t, hhold⟩
        · obtain ⟨r, σ', E2, E1, S3, hstar, hr3, hE2, hE1, hhold3, hval, hfree, hval_all, hfr, hframe⟩ :=
            acquireA_decomp hc hR hl hidle bound K hK (hF _) (xσ.set "lk" iv) (by simp)
              (.seq (.assign z (.var "v")) (Mk yk))
          have hF1 : ∀ e ∈ E1 ++ E, e.cpu ≠ c := fun e he =>
            (List.mem_append.1 he).elim (hE1 e) (hEo e)
          obtain ⟨hE', hy', hpl⟩ := table_extend (y := ⟨.call z .acq [ea], yk, yσ, yl⟩) hy hkeys hF1
          simp only at hpl
          have hprim : hprimsA (tableA c (tbl ++ [(yl, E1 ++ E)]) hE') c .acq [iv] yl =
              some (hmemA iv.toNat (E1 ++ E ++ yl), .acqA c iv.toNat :: (E1 ++ E ++ yl)) := by
            simp only [hprimsA, hpl]; rw [List.append_assoc, if_pos hfree]
          refine ⟨tbl ++ [(yl, E1 ++ E)], hE', fun q hq j => ?_, _, hy', .inr (.inl
            ⟨⟨.skip, yk, yσ.set z (hmemA iv.toNat (E1 ++ E ++ yl)), .acqA c iv.toNat :: (E1 ++ E ++ yl)⟩,
             ⟨.skip, Mk yk, σ'.set z (σ' "v"), r⟩, ?_, ?_, ?_, fun h => by simp at h, ?_⟩)⟩
          · rcases List.mem_append.1 hq with hq | hq
            · exact htbl q hq j
            · simp only [List.mem_singleton] at hq; subst hq
              simpa [List.append_assoc] using hval_all j
          · simp [ClightL.step, CThread.cfg, hiv, hprim]
          · refine ⟨rfl, rfl, ⟨trivial, hok2⟩, fun w hw => ?_, S3, E2, ?_, hE2, fun j => ?_⟩
            · by_cases hwz : w = z
              · subst hwz; simp [hval, List.append_assoc]
              · have h1 : w ≠ "t" := fun e => hw (.inl e)
                have h2 : w ≠ "n" := fun e => hw (.inr (.inl e))
                have h3 : w ≠ "_" := fun e => hw (.inr (.inr (.inl e)))
                have h4 : w ≠ "v" := fun e => hw (.inr (.inr (.inr (.inl e))))
                have h5 : w ≠ "lk" := fun e => hw (.inr (.inr (.inr (.inr e))))
                simp [Locals.set, hwz, hfr w h1 h2 h3 h4, h5, hloc w hw]
            · simpa [List.append_assoc] using hr3
            · by_cases hj : j = iv.toNat
              · subst hj; exact .inr hhold3
              · rw [hframe j hj]; exact hclean j
          · refine .step (c' := ⟨.skip, .seq (.seq acquireA (.assign z (.var "v"))) (Mk yk),
              xσ.set "lk" iv, xl⟩) (by simp [ClightL.step, hea, hiv]) ?_
            refine .step (c' := ⟨.seq acquireA (.assign z (.var "v")), Mk yk, xσ.set "lk" iv, xl⟩)
              (by simp [ClightL.step]) ?_
            refine .step (c' := ⟨acquireA, .seq (.assign z (.var "v")) (Mk yk), xσ.set "lk" iv, xl⟩)
              (by simp [ClightL.step]) ?_
            refine hstar.trans (.step (c' := ⟨.assign z (.var "v"), Mk yk, σ', r⟩)
              (by simp [ClightL.step]) (.single ?_))
            simp [ClightL.step, Expr.eval]
          · intro q hq
            rcases List.mem_append.1 hq with hq | hq
            · have := hkeys q hq; simp only at this; simp; omega
            · simp only [List.mem_singleton] at hq; subst hq; simp; omega
        · -- `acq` of a lock we hold: L1 is stuck
          refine hwrong ?_
          obtain ⟨o, ho, hH⟩ := hproj iv.toNat
          have hoc : o = some c := (hH c).1 ⟨t, hhold⟩
          subst hoc
          have hEi := hreplay_held_top _ (projH_cpu hEo) ho
          rw [hEi, List.nil_append] at ho
          simp [hprimsA, hpl0, hiv, ho]
      | rel =>
        match args, hs, hwrong, hok1 with
        | [], hs, _, _ => exact absurd hs hstuck
        | [_], hs, _, _ => exact absurd hs hstuck
        | _ :: _ :: _ :: _, hs, _, _ => exact absurd hs hstuck
        | [ea, eb], hs, hwrong, hok1 =>
        simp only [M, ClightL.step, Option.some.injEq] at hs; subst hs
        have hea : ea.eval xσ = ea.eval yσ := eval_agree hloc ea (hok1.2 ea (by simp))
        have heb : eb.eval xσ = eb.eval yσ := eval_agree hloc eb (hok1.2 eb (by simp))
        have heb' : eb.eval (xσ.set "lk" (ea.eval yσ)) = eb.eval yσ := by
          rw [← heb]; exact eval_agree (fun w hw => by
            have : w ≠ "lk" := fun e => hw (.inr (.inr (.inr (.inr e))))
            simp [Locals.set, this]) eb (hok1.2 eb (by simp))
        generalize hiv : ea.eval yσ = iv at hwrong heb'
        generalize hvv : eb.eval yσ = vv at hwrong heb'
        rcases hclean iv.toNat with hidle | ⟨t, hhold⟩
        · -- `rel` of a lock we do not hold: L1 is stuck
          refine hwrong ?_
          obtain ⟨o, ho, hH⟩ := hproj iv.toNat
          have hno : hreplay (projH iv.toNat yl) ≠ some (some c) := fun hc' => by
            have hEi := held_no_env hc' _ (projH_cpu hEo) ho
            rw [hEi, List.nil_append, hc'] at ho; cases ho
            obtain ⟨t, ht⟩ := (hH c).2 rfl; rw [hidle] at ht; cases ht
          simp [hprimsA, hpl0, hiv, hno]
        · obtain ⟨E', S', hr', hE', hidle', hheld, hval_all, hframe⟩ :=
            releaseA_decomp hc hR hl ⟨t, hhold⟩ vv
          have hF1 : ∀ e ∈ E' ++ E, e.cpu ≠ c := fun e he =>
            (List.mem_append.1 he).elim (hE' e) (hEo e)
          obtain ⟨hEt, hy', hpl⟩ := table_extend (y := ⟨.call z .rel [ea, eb], yk, yσ, yl⟩) hy hkeys hF1
          simp only at hpl
          have hprim : hprimsA (tableA c (tbl ++ [(yl, E' ++ E)]) hEt) c .rel [iv, vv] yl =
              some (0, .relA c iv.toNat vv :: (E' ++ E ++ yl)) := by
            simp only [hprimsA, hpl]; rw [List.append_assoc, if_pos hheld]
          refine ⟨tbl ++ [(yl, E' ++ E)], hEt, fun q hq j => ?_, _, hy', .inr (.inl
            ⟨⟨.skip, yk, yσ.set z 0, .relA c iv.toNat vv :: (E' ++ E ++ yl)⟩,
             ⟨.skip, Mk yk, ((((xσ.set "lk" iv).set "v" vv).set "_" 0).set "_" 0).set z 0,
               releaseSpecA ε c iv.toNat vv xl⟩, ?_, ?_, ?_, fun h => by simp at h, ?_⟩)⟩
          · rcases List.mem_append.1 hq with hq | hq
            · exact htbl q hq j
            · simp only [List.mem_singleton] at hq; subst hq
              simpa [List.append_assoc] using hval_all j
          · simp [ClightL.step, CThread.cfg, hiv, hvv, hprim]
          · refine ⟨rfl, rfl, ⟨trivial, hok2⟩, fun w hw => ?_, S', [], ?_, by simp, fun j => ?_⟩
            · by_cases hwz : w = z
              · subst hwz; simp
              · have h3 : w ≠ "_" := fun e => hw (.inr (.inr (.inl e)))
                have h4 : w ≠ "v" := fun e => hw (.inr (.inr (.inr (.inl e))))
                have h5 : w ≠ "lk" := fun e => hw (.inr (.inr (.inr (.inr e))))
                simp [Locals.set, hwz, h3, h4, h5, hloc w hw]
            · simpa [List.append_assoc] using hr'
            · by_cases hj : j = iv.toNat
              · subst hj; exact .inl hidle'
              · rw [hframe j hj]; exact hclean j
          · refine .step (c' := ⟨.skip, .seq (.seq (.assign "v" eb) (.seq releaseA (.assign z (.const 0))))
              (Mk yk), xσ.set "lk" iv, xl⟩) (by simp [ClightL.step, hea, hiv]) ?_
            refine .step (c' := ⟨.seq (.assign "v" eb) (.seq releaseA (.assign z (.const 0))), Mk yk,
              xσ.set "lk" iv, xl⟩) (by simp [ClightL.step]) ?_
            refine .step (c' := ⟨.assign "v" eb, .seq (.seq releaseA (.assign z (.const 0))) (Mk yk),
              xσ.set "lk" iv, xl⟩) (by simp [ClightL.step]) ?_
            refine .step (c' := ⟨.skip, .seq (.seq releaseA (.assign z (.const 0))) (Mk yk),
              (xσ.set "lk" iv).set "v" vv, xl⟩) (by simp [ClightL.step, heb']) ?_
            refine .step (c' := ⟨.seq releaseA (.assign z (.const 0)), Mk yk,
              (xσ.set "lk" iv).set "v" vv, xl⟩) (by simp [ClightL.step]) ?_
            refine .step (c' := ⟨releaseA, .seq (.assign z (.const 0)) (Mk yk),
              (xσ.set "lk" iv).set "v" vv, xl⟩) (by simp [ClightL.step]) ?_
            have hrel := releaseA_sim ε c ((xσ.set "lk" iv).set "v" vv) iv xl
              (.seq (.assign z (.const 0)) (Mk yk)) (by simp)
            simp only [Locals.set_same] at hrel
            refine hrel.trans (.step (c' := ⟨.assign z (.const 0), Mk yk,
              ((((xσ.set "lk" iv).set "v" vv).set "_" 0).set "_" 0), releaseSpecA ε c iv.toNat vv xl⟩)
              (by simp [ClightL.step]) (.single ?_))
            simp [ClightL.step, Expr.eval]
          · intro q hq
            rcases List.mem_append.1 hq with hq | hq
            · have := hkeys q hq; simp only at this; simp; omega
            · simp only [List.mem_singleton] at hq; subst hq; simp; omega
    · have hnc : ∀ z p args, ys ≠ .call z p args := fun z p args e => hcall ⟨z, p, args, e⟩
      obtain ⟨y', hy1, hRel', habs⟩ := step_match (Q := hprimsA (tableA c tbl hE) c) hRel hnc hs
      refine ⟨tbl, hE, htbl, y', hy.trans (.single hy1), .inl ⟨hRel', ?_⟩⟩
      rw [habs]; exact hkeys
  · cases hxe with
    | refl => exact absurd rfl hne
    | step hs2 hrest =>
      rw [hs] at hs2; cases hs2
      by_cases hend : x' = e
      · subst hend
        exact ⟨tbl, hE, htbl, y', hy.trans (.single hy'), .inl ⟨hRe, hkeys⟩⟩
      · exact ⟨tbl, hE, htbl, y, hy, .inr (.inl ⟨y', e, hy', hRe, hrest, hend, hkeys⟩)⟩
  · exact ⟨tbl, hE, htbl, y, hy, .inr (.inr hwrong)⟩

/-- **Contextual refinement for every lock-array client.** -/
theorem client_sim (hc : c < NCPU) (hR : RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : ∀ i tn, FairA ε c i tn bound) (P : Stmt HPrimA) (hP : SOK P) (σ : Locals) {l : ALog}
    {S : AState} {h : HLogA} (hl : areplay l = some (S, h)) (hcl : Clean c S) {x : Config APrim ALog}
    (hx : Star (aprims ε c) ⟨M P, .stop, σ, l⟩ x) : Sim ε c ⟨P, .stop, σ, h⟩ x := by
  have h0 : Sim ε c ⟨P, .stop, σ, h⟩ ⟨M P, .stop, σ, l⟩ :=
    ⟨[], by simp, by simp, _, .refl _,
      .inl ⟨⟨rfl, rfl, ⟨hP, trivial⟩, fun _ _ => rfl, S, [], hl, by simp, hcl⟩, by simp⟩⟩
  suffices ∀ {a b}, Star (aprims ε c) a b → Sim ε c ⟨P, .stop, σ, h⟩ a → Sim ε c ⟨P, .stop, σ, h⟩ b from
    this hx h0
  intro a b hab
  induction hab with
  | refl => exact id
  | step hs _ ih => exact fun hS => ih (sim_step hc hR bound K hK hF hS hs)

/-- **Finished runs**: a finished linked L0 run has a finished L1 run of the
client with the same client locals, whose log the L0 log replays to, up to
other CPUs' later events (or the client went wrong at L1). -/
theorem client_final (hc : c < NCPU) (hR : RelyA ε c) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : ∀ i tn, FairA ε c i tn bound) (P : Stmt HPrimA) (hP : SOK P) (σ : Locals) {l : ALog}
    {S : AState} {h : HLogA} (hl : areplay l = some (S, h)) (hcl : Clean c S) {σ' : Locals} {l' : ALog}
    (hx : Star (aprims ε c) ⟨M P, .stop, σ, l⟩ ⟨.skip, .stop, σ', l'⟩) :
    ∃ εH : HEnvA, HRelyA εH c ∧ ∃ y, Star (hprimsA εH c) ⟨P, .stop, σ, h⟩ y ∧
      ((y.stmt = .skip ∧ y.cont = .stop ∧ (∀ z, ¬ Rsv z → σ' z = y.locals z) ∧
          ∃ S' E, areplay l' = some (S', E ++ y.abs) ∧ ∀ e ∈ E, e.cpu ≠ c) ∨
       (ClightL.step (hprimsA εH c) y = none ∧ ¬ Final y)) := by
  obtain ⟨tbl, hE, htbl, y, hy, hcase⟩ := client_sim hc hR bound K hK hF P hP σ hl hcl hx
  refine ⟨tableA c tbl hE, tableA_rely c tbl hE htbl, y, hy, ?_⟩
  rcases hcase with ⟨⟨hs1, hk1, -, hloc, S', E, hr, hEo, -⟩, -⟩ | ⟨y', e, -, -, hxe, hne, -⟩ | hw
  · left
    obtain ⟨ys, yk, yσ, yl⟩ := y
    simp only at hs1 hk1 hloc hr ⊢
    refine ⟨?_, ?_, hloc, S', E, hr, hEo⟩
    · cases ys with
      | skip => rfl
      | call z p args =>
        cases p <;> (match args with
          | [] => simp [M] at hs1
          | [_] => simp [M] at hs1
          | [_, _] => simp [M] at hs1
          | _ :: _ :: _ :: _ => simp [M] at hs1)
      | _ => simp [M] at hs1
    · cases yk <;> simp [Mk] at hk1 ⊢
  · cases hxe with
    | refl => exact absurd rfl hne
    | step hs2 _ => simp [ClightL.step] at hs2
  · exact .inr hw

/-- **Not vacuous**: under the concrete fair array scheduler, from the empty log. -/
theorem client_final_fair {c : CPU} (hc : c < NCPU) (P : Stmt HPrimA) (hP : SOK P) (σ : Locals)
    {σ' : Locals} {l' : ALog}
    (hx : Star (aprims fairEnvA c) ⟨M P, .stop, σ, []⟩ ⟨.skip, .stop, σ', l'⟩) :
    ∃ εH : HEnvA, HRelyA εH c ∧ ∃ y, Star (hprimsA εH c) ⟨P, .stop, σ, []⟩ y ∧
      ((y.stmt = .skip ∧ y.cont = .stop ∧ (∀ z, ¬ Rsv z → σ' z = y.locals z) ∧
          ∃ S' E, areplay l' = some (S', E ++ y.abs) ∧ ∀ e ∈ E, e.cpu ≠ c) ∨
       (ClightL.step (hprimsA εH c) y = none ∧ ¬ Final y)) :=
  client_final hc (fairA_rely c) (fun _ => 0) 0 (fun _ => Nat.le_refl _) (fun i tn => fairA_fair c i tn)
    P hP σ (S := AState.init) rfl (fun _ => .inl rfl) hx

end ArrayClient
