import CertiKOS.MCSBoundC
import CertiKOS.MCSLiveN

/-!
# The bounded MCS lock on the multicore machine

The multicore machine `PGB` runs the bounded primitives (`MCSBoundC.bprims`)
on one global bounded log, with no environment. Each CPU runs
`clientB n = acquire(bound); mem() × n; release()`.

* `cstep_erase`, `cstep_lift`: a bounded multicore step erases to an unbounded
  one, and each unbounded step from an erased state lifts back. Erasing
  `clientB n` gives `MCSLiveN.codeN n`.
* `multicore_cs_exclusiveB`: mutual exclusion on the bounded machine.
* `bounded_fair_terminates`: every `K`-fair bounded run ends within
  `K * (T * (3n + 43) + 1)` steps.
* `bounded_global_valid`: if every CPU's bound exceeds `n`, every reachable
  global bounded log is valid (`bcal` is defined). By `bcal_hbreplay` it is
  then a valid `H_CalLock` log, so no critical section overruns its bound.
  The proof keeps an invariant over the whole machine: the erased state
  satisfies `MCSLiveN.GLM`, which gives MCS validity and phase `holding` in
  the critical section. Per CPU, the recorded bound is the C argument, and
  while holding, the budget exceeds the memory events still to come in that
  CPU's code (`memT`).
-/

namespace MCSBoundMC

open ClightL Ticket ClightToPy MCS LinkM TicketLive FairC MCSBound MCSBoundC MCSLiveN
open MCSLink (REST ITE TAIL KITE RITE KLN holdC linkC gbC hoC)

/-! ## The machine and its erasure -/

def noEnvB : BEnv := ⟨fun _ _ => [], by intro c l e he; simp at he⟩

theorem noEnvB_erases : EnvErases noEnvB noEnvM := fun _ _ => rfl

@[simp] theorem bpull_noEnvB (c : CPU) (l : BLog) : bpull noEnvB c l = l := rfl

abbrev PGB : Nat → Prims BPrim BLog := fun i => bprims noEnvB i

def erT (t : CThread BPrim) : CThread MPrim := ⟨erS t.stmt, erK t.cont, t.locals⟩

theorem erS_critB : ∀ n, erS (critB n) = critM n
  | 0 => rfl
  | n + 1 => by simp [critB, critM, erS, erCall, erS_critB n]

theorem erS_clientB (n : Nat) : erS (clientB n) = codeN n := by
  simp [clientB, codeN, erS, erS_acquireB, erS_releaseB, erS_critB]

def poolB (n T : Nat) (σs : Nat → Locals) : List (CThread BPrim) :=
  (List.range T).map fun i => ⟨clientB n, .stop, σs i⟩

theorem erase_poolB (n T : Nat) (σs : Nat → Locals) : (poolB n T σs).map erT = poolN n T σs := by
  simp [poolB, poolN, erT, erS_clientB, erK]

theorem cstep_erase {i : Nat} {cs cs' : List (CThread BPrim)} {l l' : BLog} (h : CStepI PGB i cs l cs' l') :
    CStepI PGM i (cs.map erT) (erase l) (cs'.map erT) (erase l') := by
  obtain ⟨hi, c', hs, rfl, rfl⟩ := h
  have he := step_erase noEnvB_erases i (cs[i].cfg l)
  rw [hs] at he
  refine ⟨by simpa using hi, erC c', ?_, ?_, rfl⟩
  · simpa [erC, erT, CThread.cfg] using he
  · simp [List.map_set, erT, erC, thr]

theorem cstep_lift {i : Nat} {cs : List (CThread BPrim)} {l : BLog} {ys : List (CThread MPrim)} {m : MLog}
    (h : CStepI PGM i (cs.map erT) (erase l) ys m) :
    ∃ cs' l', CStepI PGB i cs l cs' l' ∧ cs'.map erT = ys ∧ erase l' = m := by
  obtain ⟨hi, c', hs, rfl, rfl⟩ := h
  have hi' : i < cs.length := by simpa using hi
  have he := step_erase noEnvB_erases i (cs[i].cfg l)
  have : step (mprims noEnvM i) (erC (cs[i].cfg l)) = some c' := by
    simpa [erC, erT, CThread.cfg] using hs
  rw [this] at he
  cases hx : step (bprims noEnvB i) (cs[i].cfg l) with
  | none => rw [hx] at he; cases he
  | some x =>
    rw [hx] at he; simp only [Option.map_some, Option.some.injEq] at he
    refine ⟨_, _, ⟨hi', x, hx, rfl, rfl⟩, ?_, by rw [he]; rfl⟩
    rw [he]; simp [List.map_set, erT, erC, thr]

theorem done_erT {t : CThread BPrim} : Done (erT t) ↔ Done t := by
  constructor
  · intro ⟨h1, h2⟩; exact ⟨erS_skip h1, erK_stop h2⟩
  · intro ⟨h1, h2⟩; exact ⟨by simp [erT, h1, erS], by simp [erT, h2, erK]⟩

theorem cstepI_cstep {Pn Abs : Type} {P : Nat → Prims Pn Abs} {i : Nat} {cs cs' : List (CThread Pn)} {a a' : Abs}
    (h : CStepI P i cs a cs' a') : CStep P cs a cs' a' := by
  obtain ⟨hi, c', hs, rfl, rfl⟩ := h; exact .step i hi hs

theorem csteps_erase {cs cs' : List (CThread BPrim)} {l l' : BLog} (h : CSteps PGB cs l cs' l') :
    CSteps PGM (cs.map erT) (erase l) (cs'.map erT) (erase l') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih =>
    obtain ⟨i, hi, hst⟩ := hs
    exact .step (cstepI_cstep (cstep_erase ⟨hi, _, hst, rfl, rfl⟩)) ih

/-! ## Safety and liveness carry over -/

/-- **Mutual exclusion on the bounded machine.** -/
theorem multicore_cs_exclusiveB (n T : Nat) (σs : Nat → Locals) (hT : T ≤ NCPU) {cs : List (CThread BPrim)}
    {l : BLog} (h : CSteps PGB (poolB n T σs) [] cs l) (c d : Nat) (hc : c < cs.length) (hd : d < cs.length)
    (hcc : InCSN n (erT cs[c])) (hdc : InCSN n (erT cs[d])) : c = d := by
  have he := csteps_erase h
  rw [erase_poolB] at he
  exact multicore_cs_exclusiveN n T σs hT he c d (by simpa using hc) (by simpa using hd)
    (by simpa using hcc) (by simpa using hdc)

def erRun (r : GRun PGB) : GRun PGM where
  len := r.len
  cs k := (r.cs k).map erT
  ab k := erase (r.ab k)
  lab := r.lab
  step k hk := cstep_erase (r.step k hk)

theorem erRun_fair {r : GRun PGB} {K : Nat} (hF : r.Fair K) : (erRun r).Fair K := by
  intro m hm d hd hnd
  have hd' : d < (r.cs m).length := by simpa [erRun] using hd
  exact hF m hm d hd' fun h => hnd (by simpa [erRun] using done_erT.2 h)

/-- **Liveness on the bounded machine.** -/
theorem bounded_fair_terminates (n T : Nat) (σs : Nat → Locals) (hT : T ≤ NCPU) (r : GRun PGB)
    (h0 : r.cs 0 = poolB n T σs) (hl0 : r.ab 0 = []) {K : Nat} (hK : 0 < K) (hF : r.Fair K) :
    r.len < K * (T * (41 + (3 * n + 2)) + 1) :=
  mcsN_fair_terminates n T σs hT (erRun r) (by simp [erRun, h0, erase_poolB]) (by simp [erRun, hl0, erase])
    hK (erRun_fair hF)

/-! ## Code shape with memory events -/

def OkCallM : BPrim → List Expr → Prop
  | .m .swap, args => args = [.var "bound"]
  | _, _ => True

/-- Loop bodies have no memory events (`Good`, from `MCSBoundC`). -/
def GoodM : Stmt BPrim → Prop
  | .skip => True
  | .assign x _ => x ≠ "bound"
  | .seq a b => GoodM a ∧ GoodM b
  | .ite _ a b => GoodM a ∧ GoodM b
  | .while _ b => Good b
  | .call x p args => x ≠ "bound" ∧ OkCallM p args

def GoodMK : Cont BPrim → Prop
  | .stop => True
  | .seq s k => GoodM s ∧ GoodMK k
  | .loop _ b k => Good b ∧ GoodMK k

/-- Memory calls still to come. -/
def memS : Stmt BPrim → Nat
  | .seq a b => memS a + memS b
  | .ite _ a b => memS a + memS b
  | .while _ b => memS b
  | .call _ .mem _ => 1
  | _ => 0

def memK : Cont BPrim → Nat
  | .stop => 0
  | .seq s k => memS s + memK k
  | .loop _ b k => memS b + memK k

def memT (t : CThread BPrim) : Nat := memS t.stmt + memK t.cont

theorem memS_good : ∀ {s : Stmt BPrim}, Good s → memS s = 0
  | .skip, _ => rfl
  | .assign _ _, _ => rfl
  | .seq a b, h => by simp [memS, memS_good h.1, memS_good h.2]
  | .ite _ a b, h => by simp [memS, memS_good h.1, memS_good h.2]
  | .while _ b, h => by simp only [memS]; exact memS_good h
  | .call _ p _, h => by cases p with
    | mem => exact h.2.elim
    | m p => rfl

theorem good_goodM : ∀ {s : Stmt BPrim}, Good s → GoodM s
  | .skip, _ => trivial
  | .assign _ _, h => h
  | .seq a b, h => ⟨good_goodM h.1, good_goodM h.2⟩
  | .ite _ a b, h => ⟨good_goodM h.1, good_goodM h.2⟩
  | .while _ b, h => h
  | .call _ p args, h => ⟨h.1, by cases p with
    | mem => exact h.2.elim
    | m p => cases p <;> first | exact h.2 | trivial⟩

/-- A step keeps the shape, keeps `bound`, does not add memory calls, and is
either silent or one primitive call. -/
theorem step_shapeM {P : Prims BPrim BLog} {x x' : Config BPrim BLog} (hG : GoodM x.stmt) (hK : GoodMK x.cont)
    (hs : step P x = some x') :
    GoodM x'.stmt ∧ GoodMK x'.cont ∧ x'.locals "bound" = x.locals "bound" ∧
      memS x'.stmt + memK x'.cont ≤ memS x.stmt + memK x.cont ∧
      (x'.abs = x.abs ∨ ∃ t p args v, x.stmt = .call t p args ∧ x'.cont = x.cont ∧ x'.stmt = .skip ∧
        OkCallM p args ∧ P p (args.map (·.eval x.locals)) x.abs = some (v, x'.abs)) := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  cases stmt with
  | skip =>
    cases cont with
    | stop => simp [step] at hs
    | seq s k => simp only [step, Option.some.injEq] at hs; subst hs
                 exact ⟨hK.1, hK.2, rfl, by simp [memS, memK], .inl rfl⟩
    | loop e b k => simp only [step, Option.some.injEq] at hs; subst hs
                    exact ⟨hK.1, hK.2, rfl, by simp [memS, memK, memS_good hK.1], .inl rfl⟩
  | assign y e =>
    simp only [step, Option.some.injEq] at hs; subst hs
    exact ⟨trivial, hK, by simp [Locals.set, Ne.symm hG], by simp [memS], .inl rfl⟩
  | seq a b => simp only [step, Option.some.injEq] at hs; subst hs
               exact ⟨hG.1, ⟨hG.2, hK⟩, rfl, by simp [memS, memK]; omega, .inl rfl⟩
  | ite e a b =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨?_, hK, rfl, ?_, .inl rfl⟩
    · simp only; split; exact hG.2; exact hG.1
    · simp only [memS]; split <;> omega
  | «while» e b =>
    simp only [step] at hs
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst hs
    · exact ⟨trivial, hK, rfl, by simp [memS], .inl rfl⟩
    · exact ⟨good_goodM hG, ⟨hG, hK⟩, rfl, by simp [memS, memK, memS_good hG], .inl rfl⟩
  | call y p args =>
    simp only [step] at hs
    split at hs
    · rename_i v a' hp
      simp only [Option.some.injEq] at hs; subst hs
      exact ⟨trivial, hK, by simp [Locals.set, Ne.symm hG.1], by simp [memS],
        .inr ⟨y, p, args, v, rfl, rfl, rfl, hG.2, hp⟩⟩
    · simp at hs

/-! ## The global bounded invariant -/

/-- Per CPU: the recorded bound is the C argument, and while holding, the budget
exceeds the memory events still to come. -/
def QA (bs : BS) (i : CPU) (t : CThread BPrim) : Prop :=
  (bs.s.ph i ≠ .idle → bs.bnd i = (t.locals "bound").toNat) ∧ (bs.s.ph i = .holding → memT t < bs.self)

def GB (n T : Nat) (cs : List (CThread BPrim)) (l : BLog) : Prop :=
  (∃ Φ, GLM n T (cs.map erT) (erase l) Φ) ∧ ∃ bs hb, bcal l = some (bs, hb) ∧
    ∀ i (hi : i < cs.length), GoodM cs[i].stmt ∧ GoodMK cs[i].cont ∧
      memT cs[i] ≤ n ∧ n < (cs[i].locals "bound").toNat ∧ QA bs i cs[i]

theorem goodM_critB : ∀ k, GoodM (critB k)
  | 0 => trivial
  | k + 1 => ⟨⟨by decide, trivial⟩, goodM_critB k⟩

theorem gb_init (n T : Nat) (σs : Nat → Locals) (hT : T ≤ NCPU) (hb : ∀ i, i < T → n < (σs i "bound").toNat) :
    GB n T (poolB n T σs) [] := by
  refine ⟨⟨_, by rw [erase_poolB]; exact gl_initN n T σs hT⟩, BS.init, [], rfl, fun i hi => ?_⟩
  have hiT : i < T := by simpa [poolB] using hi
  simp only [poolB, List.getElem_map, List.getElem_range]
  refine ⟨?_, trivial, ?_, hb i hiT, fun h => absurd rfl h, fun h => by simp [BS.init, MS.init] at h⟩
  · simp [clientB, acquireB, releaseB, GoodM, Good, OkCallM, OkCall, loopBB, loopNB, goodM_critB]
  · simp only [memT, clientB, memS, memK]
    have : ∀ k, memS (critB k) = k := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => simp [critB, memS, ih]; omega
    simp [this, acquireB, releaseB, memS, loopBB, loopNB]

/-- Our own memory event: we hold the lock and have budget. -/
theorem own_mem {a : CPU} {l : BLog} {bs : BS} {hb : List HBEvent} (hl : bcal l = some (bs, hb))
    (hh : bs.s.ph a = .holding) (hpos : 0 < bs.self) :
    bcal (⟨a, .mem⟩ :: l) = some (⟨bs.s, bs.bnd, bs.self - 1⟩, hcons (some (.mem a)) hb) :=
  bcal_cons_of hl (by simp [bstep, hh, hpos])

/-- The erased thread at a memory call is in the critical section, holding. -/
theorem mem_holding' {n : Nat} {c : CPU} {s : MS} {u : CThread MPrim} {w : Nat} (hA : AtWN n c s u w)
    {x : Ident} (hu : u.stmt = .assign x (.const 0)) : s.ph c = .holding := by
  cases hA <;> first | assumption | (simp_all [codeN, KRn, KC, critM, KLBn, acquireM, releaseM, REST, ITE,
    TAIL, KITE, RITE, KLN, holdC, linkC, gbC, MCSLink.gnC, hoC, loopB, loopN])

theorem mem_holding {n : Nat} {c : CPU} {s : MS} {t : CThread BPrim} {w : Nat} (hA : AtWN n c s (erT t) w)
    {x : Ident} {args : List Expr} (ht : t.stmt = .call x .mem args) : s.ph c = .holding :=
  mem_holding' hA (x := x) (by simp [erT, ht, erS, erCall])

/-- **The invariant holds along every bounded multicore step.** -/
theorem gb_step {n T : Nat} {a : Nat} {cs cs' : List (CThread BPrim)} {l l' : BLog} (hG : GB n T cs l)
    (hS : CStepI PGB a cs l cs' l') : GB n T cs' l' := by
  obtain ⟨⟨Φ, hGL⟩, bs, hb, hl, hth⟩ := hG
  have hSe := cstep_erase hS
  obtain ⟨Φ', hGL', -⟩ := gstepWM hGL hSe
  obtain ⟨sE, HE, wsE, hlE, hlen, hTN, -, hAtE, -⟩ := hGL
  obtain ⟨sE', HE', -, hlE', -⟩ := id hGL'
  obtain ⟨ha, c', hst, rfl, rfl⟩ := hS
  obtain ⟨g1, g2, g3, g4, q1, q2⟩ := hth a ha
  obtain ⟨g1', g2', gb, gm, hcase⟩ := step_shapeM (x := cs[a].cfg l) g1 g2 hst
  simp only [CThread.cfg] at gm
  have gm' : memT (thr c') ≤ memT cs[a] := by simp only [memT, thr]; exact gm
  have hlenT : cs.length = T := by simpa using hlen
  have haN : a < NCPU := Nat.lt_of_lt_of_le (hlenT ▸ ha) hTN
  have hiE := mreplay_inv hlE
  -- the new thread of `a`
  have hnew : (cs.set a (thr c'))[a]'(by simpa using ha) = thr c' := List.getElem_set_self _
  have hother : ∀ i (hi : i < (cs.set a (thr c')).length), i ≠ a →
      (cs.set a (thr c'))[i] = cs[i]'(by simpa using hi) := fun i hi hia => List.getElem_set_ne (Ne.symm hia) _
  refine ⟨⟨Φ', hGL'⟩, ?_⟩
  rcases hcase with heq | ⟨t, p, args, v, hstm, hcont, hskip, hok, hp⟩
  · -- silent step: the log is unchanged
    refine ⟨bs, hb, heq ▸ hl, fun i hi => ?_⟩
    by_cases hia : i = a
    · subst hia; rw [hnew]
      refine ⟨g1', g2', Nat.le_trans gm' g3, by simp only [thr]; rw [gb]; exact g4, ?_, ?_⟩
      · intro h; simp only [thr]; rw [gb]; exact q1 h
      · intro h; have := q2 h; omega
    · rw [hother i hi hia]; exact hth i (by simpa using hi)
  · -- a primitive call
    simp only [CThread.cfg] at hstm hcont hskip hp
    have hbnd : (cs[a].locals "bound") = (thr c').locals "bound" := gb.symm
    -- other CPUs keep their facts if the new state is reached by one bstep of `a`
    have frame : ∀ (bs' : BS) (hb' : List HBEvent) (e : BEvent), e.cpu = a →
        bcal (e :: l) = some (bs', hb') → QA bs' a (thr c') →
        (∀ i (hi : i < (cs.set a (thr c')).length), GoodM (cs.set a (thr c'))[i].stmt ∧
          GoodMK (cs.set a (thr c'))[i].cont ∧ memT (cs.set a (thr c'))[i] ≤ n ∧
          n < ((cs.set a (thr c'))[i].locals "bound").toNat ∧ QA bs' i (cs.set a (thr c'))[i]) := by
      intro bs' hb' e he hl' hqa i hi
      by_cases hia : i = a
      · subst hia; rw [hnew]
        exact ⟨g1', g2', Nat.le_trans gm' g3, by rw [← hbnd]; exact g4, hqa⟩
      · rw [hother i hi hia]
        have hi' : i < cs.length := by simpa using hi
        obtain ⟨f1, f2, f3, f4, r1, r2⟩ := hth i hi'
        obtain ⟨bs0, hb0, o, hl0, hs0, -⟩ := bcal_cons hl'
        rw [hl] at hl0; simp only [Option.some.injEq, Prod.mk.injEq] at hl0; obtain ⟨rfl, rfl⟩ := hl0
        obtain ⟨e1, e2, e3⟩ := bstep_other (bcal_inv hl) (bcal_inv hl') hs0 (by rw [he]; exact Ne.symm hia)
        exact ⟨f1, f2, f3, f4, fun h => by rw [e2]; exact r1 (e1 ▸ h),
          fun h => by rw [e3 (e1 ▸ h)]; exact r2 (e1 ▸ h)⟩
    have hmok : MOK (erase c'.abs) := ⟨sE', HE', hlE'⟩
    have hmemT : memT (thr c') + memS (.call t p args) = memT cs[a] := by
      simp only [memT, thr, hskip, hcont, hstm, memS]; omega
    cases p with
    | mem =>
      simp only [bprims, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨-, hab⟩ := hp
      have hh : bs.s.ph a = .holding := by
        have hA0 := hAtE a (by simpa using ha)
        rw [List.getElem_map] at hA0
        have := mem_holding hA0 (by simpa using hstm)
        have hs := bcal_mreplay hl; rw [hlE] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact this
      have hlt := q2 hh
      simp only [memS] at hmemT
      rw [← hab]
      refine ⟨_, _, own_mem hl hh (by omega), frame _ _ _ rfl (own_mem hl hh (by omega)) ⟨?_, ?_⟩⟩
      · intro h; rw [← hbnd]; exact q1 h
      · intro _; simp only; omega
    | m p =>
      have hmT : memT (thr c') = memT cs[a] := by simp only [memS] at hmemT; omega
      cases p
      case swap =>
        simp only [OkCallM] at hok; subst hok
        simp only [List.map, Expr.eval, bprims, bpull_noEnvB, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨-, hab⟩ := hp
        rw [← hab] at hmok ⊢
        obtain ⟨s', o, hm⟩ := own_step_of_mok (k := .swap) hl (by simpa [erase, eraseE] using hmok)
        have ho := mstep_swap_none hm; subst ho
        have hs : bstep bs ⟨a, .swap (cs[a].locals "bound").toNat⟩ =
            some (⟨s', fset bs.bnd a (cs[a].locals "bound").toNat, bs.self⟩, none) := by simp [bstep, hm]
        have hl' := bcal_cons_of hl hs
        exact ⟨_, _, hl', frame _ _ _ rfl hl' ⟨fun _ => by simp [hbnd], fun hh => absurd hh (mstep_swap_ph hm)⟩⟩
      all_goals
        cases args <;> simp only [List.map, bprims, bpull_noEnvB, Option.some.injEq, Prod.mk.injEq,
          reduceCtorEq] at hp
        obtain ⟨-, hab⟩ := hp
        rw [← hab] at hmok ⊢
        have hv : ValidQ a (cs[a].locals "bound").toNat (memT cs[a]) l := ⟨bs, hb, hl, q1, q2⟩
        obtain ⟨bs', hb', hl', r1, r2⟩ := own_lk (Nat.lt_of_le_of_lt g3 g4) (by decide) hv hmok
        exact ⟨bs', hb', hl', frame _ _ _ rfl hl' ⟨fun h => by rw [← hbnd]; exact r1 h,
          fun h => by rw [hmT]; exact r2 h⟩⟩

/-- **Global bounded validity.** On the bounded multicore machine, if every CPU's
bound exceeds the `n` memory events of its critical section, every reachable
global log is a valid bounded log. -/
theorem bounded_global_valid (n T : Nat) (σs : Nat → Locals) (hT : T ≤ NCPU)
    (hb : ∀ i, i < T → n < (σs i "bound").toNat) {cs : List (CThread BPrim)} {l : BLog}
    (h : CSteps PGB (poolB n T σs) [] cs l) : ∃ bs hb', bcal l = some (bs, hb') := by
  suffices ∀ {a b la lb}, CSteps PGB a la b lb → GB n T a la → GB n T b lb by
    obtain ⟨-, bs, hb', hl, -⟩ := this h (gb_init n T σs hT hb)
    exact ⟨bs, hb', hl⟩
  intro a b la lb hab
  induction hab with
  | refl => exact id
  | step hs _ ih =>
    obtain ⟨i, hi, hst⟩ := hs
    exact fun hG => ih (gb_step hG ⟨hi, _, hst, rfl, rfl⟩)

/-- So the global log is a valid `H_CalLock` log. -/
theorem bounded_global_hcal (n T : Nat) (σs : Nat → Locals) (hT : T ≤ NCPU)
    (hb : ∀ i, i < T → n < (σs i "bound").toNat) {cs : List (CThread BPrim)} {l : BLog}
    (h : CSteps PGB (poolB n T σs) [] cs l) : ∃ bs hb' o, bcal l = some (bs, hb') ∧ hbreplay hb' = some (bs.self, o) := by
  obtain ⟨bs, hb', hl⟩ := bounded_global_valid n T σs hT hb h
  obtain ⟨o, ho, -⟩ := bcal_hbreplay hl
  exact ⟨bs, hb', o, hl, ho⟩

end MCSBoundMC
