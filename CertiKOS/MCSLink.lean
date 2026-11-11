import CertiKOS.LinkM
import CertiKOS.TicketLive

/-!
# The MCS lock on the multicore machine, from the per-CPU proofs

The instance of `LinkM.lean`. Each CPU runs `acquireM; releaseM` (the verified
MCS C code) once. Everything is derived from per-CPU reasoning.

* `AtM`: the 36 program points of `acquireM; releaseM`, each tied to the CPU's
  MCS phase (and to what the CPU last read of `p`, `busy`, `next` or the
  `cas` result). Safety only: the per-CPU guarantee must hold under every
  rely-respecting environment, fair or not.
* `own_stepM`, `at_otherM`: a step of the CPU, and another CPU's event,
  preserve it. `client_guarM`: the per-CPU guarantee `GuarM`.
* `mcs_linked`: every multicore run is explained by the per-CPU layers, and the
  global MCS log is valid.
* `multicore_cs_exclusiveM`: two CPUs between their `acquire` and their
  `release` are the same CPU.
-/

namespace MCSLink

open ClightL Ticket ClightToPy MCS LinkM TicketLive

/-! ## The program points -/

def holdC : Stmt MPrim := .call "_" .hold []
def linkC : Stmt MPrim := .call "_" .link []
def gbC : Stmt MPrim := .call "b" .getBusy []
def gnC : Stmt MPrim := .call "n" .getNext []
def hoC : Stmt MPrim := .call "_" .handoff []
def ITE : Stmt MPrim := .ite (.bin .ne (.var "p") (.const 0)) (.seq linkC (.seq gbC loopB)) .skip
def REST : Stmt MPrim := .seq ITE holdC
def KR : Cont MPrim := .seq releaseM .stop
def KITE : Stmt MPrim := .ite (.bin .eq (.var "k") (.const 0)) (.seq gnC (.seq loopN hoC)) .skip
def TAIL : Stmt MPrim := .seq (.call "k" .cas []) KITE
def RITE : Stmt MPrim := .ite (.bin .ne (.var "n") (.const 0)) hoC TAIL
def KLB : Cont MPrim := .loop (.bin .ne (.var "b") (.const 0)) gbC (.seq holdC KR)
def KLN : Cont MPrim := .loop (.bin .eq (.var "n") (.const 0)) gnC (.seq hoC .stop)
def codeMC : Stmt MPrim := .seq acquireM releaseM

theorem acquireM_eq : acquireM = .seq (.call "p" .swap []) REST := rfl
theorem releaseM_eq : releaseM = .seq gnC RITE := rfl
theorem loopB_eq : loopB = .while (.bin .ne (.var "b") (.const 0)) gbC := rfl
theorem loopN_eq : loopN = .while (.bin .eq (.var "n") (.const 0)) gnC := rfl

def FrontOrLink (s : MS) (c : CPU) (σ : Locals) : Prop :=
  (s.ph c = .front ∧ σ "p" = 0) ∨ (∃ q, s.ph c = .linking q ∧ σ "p" ≠ 0)
def IsLinking (s : MS) (c : CPU) : Prop := ∃ q, s.ph c = .linking q
def BI (s : MS) (c : CPU) (σ : Locals) : Prop := σ "b" = 0 → s.busy c = false
def Ready (s : MS) (c : CPU) : Prop := s.ph c = .front ∨ (s.ph c = .waiting ∧ s.busy c = false)
def NI (s : MS) (c : CPU) (σ : Locals) : Prop := σ "n" ≠ 0 → s.next c ≠ none
def CasRes (s : MS) (c : CPU) (σ : Locals) : Prop :=
  (σ "k" ≠ 0 ∧ s.ph c = .idle) ∨ (σ "k" = 0 ∧ s.ph c = .holding)

inductive AtM (c : CPU) (s : MS) : CThread MPrim → Prop
  | a0 {σ} : s.ph c = .idle → AtM c s ⟨codeMC, .stop, σ⟩
  | a1 {σ} : s.ph c = .idle → AtM c s ⟨acquireM, KR, σ⟩
  | a2 {σ} : s.ph c = .idle → AtM c s ⟨.call "p" .swap [], .seq REST KR, σ⟩
  | a3 {σ} : FrontOrLink s c σ → AtM c s ⟨.skip, .seq REST KR, σ⟩
  | a4 {σ} : FrontOrLink s c σ → AtM c s ⟨REST, KR, σ⟩
  | a5 {σ} : FrontOrLink s c σ → AtM c s ⟨ITE, .seq holdC KR, σ⟩
  | a6 {σ} : IsLinking s c → AtM c s ⟨.seq linkC (.seq gbC loopB), .seq holdC KR, σ⟩
  | a7 {σ} : IsLinking s c → AtM c s ⟨linkC, .seq (.seq gbC loopB) (.seq holdC KR), σ⟩
  | a8 {σ} : s.ph c = .waiting → AtM c s ⟨.skip, .seq (.seq gbC loopB) (.seq holdC KR), σ⟩
  | a9 {σ} : s.ph c = .waiting → AtM c s ⟨.seq gbC loopB, .seq holdC KR, σ⟩
  | a10 {σ} : s.ph c = .waiting → AtM c s ⟨gbC, .seq loopB (.seq holdC KR), σ⟩
  | a11 {σ} : s.ph c = .waiting → BI s c σ → AtM c s ⟨.skip, .seq loopB (.seq holdC KR), σ⟩
  | a12 {σ} : s.ph c = .waiting → BI s c σ → AtM c s ⟨loopB, .seq holdC KR, σ⟩
  | a13 {σ} : s.ph c = .waiting → AtM c s ⟨gbC, KLB, σ⟩
  | a14 {σ} : s.ph c = .waiting → BI s c σ → AtM c s ⟨.skip, KLB, σ⟩
  | a15 {σ} : Ready s c → AtM c s ⟨.skip, .seq holdC KR, σ⟩
  | a16 {σ} : Ready s c → AtM c s ⟨holdC, KR, σ⟩
  | a17 {σ} : s.ph c = .holding → AtM c s ⟨.skip, KR, σ⟩
  | a18 {σ} : s.ph c = .holding → AtM c s ⟨releaseM, .stop, σ⟩
  | a19 {σ} : s.ph c = .holding → AtM c s ⟨gnC, .seq RITE .stop, σ⟩
  | a20 {σ} : s.ph c = .holding → NI s c σ → AtM c s ⟨.skip, .seq RITE .stop, σ⟩
  | a21 {σ} : s.ph c = .holding → NI s c σ → AtM c s ⟨RITE, .stop, σ⟩
  | a22 {σ} : s.ph c = .holding → s.next c ≠ none → AtM c s ⟨hoC, .stop, σ⟩
  | a23 {σ} : s.ph c = .holding → AtM c s ⟨TAIL, .stop, σ⟩
  | a24 {σ} : s.ph c = .holding → AtM c s ⟨.call "k" .cas [], .seq KITE .stop, σ⟩
  | a25 {σ} : CasRes s c σ → AtM c s ⟨.skip, .seq KITE .stop, σ⟩
  | a26 {σ} : CasRes s c σ → AtM c s ⟨KITE, .stop, σ⟩
  | a27 {σ} : s.ph c = .holding → AtM c s ⟨.seq gnC (.seq loopN hoC), .stop, σ⟩
  | a28 {σ} : s.ph c = .holding → AtM c s ⟨gnC, .seq (.seq loopN hoC) .stop, σ⟩
  | a29 {σ} : s.ph c = .holding → NI s c σ → AtM c s ⟨.skip, .seq (.seq loopN hoC) .stop, σ⟩
  | a30 {σ} : s.ph c = .holding → NI s c σ → AtM c s ⟨.seq loopN hoC, .stop, σ⟩
  | a31 {σ} : s.ph c = .holding → NI s c σ → AtM c s ⟨loopN, .seq hoC .stop, σ⟩
  | a32 {σ} : s.ph c = .holding → AtM c s ⟨gnC, KLN, σ⟩
  | a33 {σ} : s.ph c = .holding → NI s c σ → AtM c s ⟨.skip, KLN, σ⟩
  | a34 {σ} : s.ph c = .holding → s.next c ≠ none → AtM c s ⟨.skip, .seq hoC .stop, σ⟩
  | done {σ} : s.ph c = .idle → AtM c s ⟨.skip, .stop, σ⟩

/-! ## Another CPU's event -/

theorem at_otherM {c : CPU} {s s' : MS} {e : MEvent} {o : Option HEvent} {t : CThread MPrim}
    (hi : MInv s) (hp : mstep s e = some (s', o)) (hne : e.cpu ≠ c) (hA : AtM c s t) : AtM c s' t := by
  obtain ⟨hph, -, -, hb, hn, -⟩ := mstep_other hi hp hne
  have hI : s.ph c = .idle → s'.ph c = .idle := fun h => by rw [hph]; exact h
  have hWt : s.ph c = .waiting → s'.ph c = .waiting := fun h => by rw [hph]; exact h
  have hH : s.ph c = .holding → s'.ph c = .holding := fun h => by rw [hph]; exact h
  have hFL : ∀ {σ}, FrontOrLink s c σ → FrontOrLink s' c σ := fun h => by
    unfold FrontOrLink; rw [hph]; exact h
  have hL : IsLinking s c → IsLinking s' c := fun h => by unfold IsLinking; rw [hph]; exact h
  have hB : ∀ {σ}, BI s c σ → BI s' c σ := fun h h0 => hb (h h0)
  have hR : Ready s c → Ready s' c := fun h => by
    unfold Ready; rw [hph]; rcases h with h | ⟨h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, hb h2⟩
  have hN : ∀ {σ}, NI s c σ → NI s' c σ := fun h h0 => by rw [hn (h h0)]; exact h h0
  have hNx : s.next c ≠ none → s'.next c ≠ none := fun h => by rw [hn h]; exact h
  have hC : ∀ {σ}, CasRes s c σ → CasRes s' c σ := fun h => by unfold CasRes; rw [hph]; exact h
  cases hA with
  | a0 h0 => exact .a0 (hI h0)
  | a1 h0 => exact .a1 (hI h0)
  | a2 h0 => exact .a2 (hI h0)
  | a3 h0 => exact .a3 (hFL h0)
  | a4 h0 => exact .a4 (hFL h0)
  | a5 h0 => exact .a5 (hFL h0)
  | a6 h0 => exact .a6 (hL h0)
  | a7 h0 => exact .a7 (hL h0)
  | a8 h0 => exact .a8 (hWt h0)
  | a9 h0 => exact .a9 (hWt h0)
  | a10 h0 => exact .a10 (hWt h0)
  | a11 h0 h1 => exact .a11 (hWt h0) (hB h1)
  | a12 h0 h1 => exact .a12 (hWt h0) (hB h1)
  | a13 h0 => exact .a13 (hWt h0)
  | a14 h0 h1 => exact .a14 (hWt h0) (hB h1)
  | a15 h0 => exact .a15 (hR h0)
  | a16 h0 => exact .a16 (hR h0)
  | a17 h0 => exact .a17 (hH h0)
  | a18 h0 => exact .a18 (hH h0)
  | a19 h0 => exact .a19 (hH h0)
  | a20 h0 h1 => exact .a20 (hH h0) (hN h1)
  | a21 h0 h1 => exact .a21 (hH h0) (hN h1)
  | a22 h0 h1 => exact .a22 (hH h0) (hNx h1)
  | a23 h0 => exact .a23 (hH h0)
  | a24 h0 => exact .a24 (hH h0)
  | a25 h0 => exact .a25 (hC h0)
  | a26 h0 => exact .a26 (hC h0)
  | a27 h0 => exact .a27 (hH h0)
  | a28 h0 => exact .a28 (hH h0)
  | a29 h0 h1 => exact .a29 (hH h0) (hN h1)
  | a30 h0 h1 => exact .a30 (hH h0) (hN h1)
  | a31 h0 h1 => exact .a31 (hH h0) (hN h1)
  | a32 h0 => exact .a32 (hH h0)
  | a33 h0 h1 => exact .a33 (hH h0) (hN h1)
  | a34 h0 h1 => exact .a34 (hH h0) (hNx h1)
  | done h0 => exact .done (hI h0)

theorem at_othersM {c : CPU} {t : CThread MPrim} :
    ∀ (xs : MLog) {l : MLog} {s s' : MS} {h h' : List HEvent},
      (∀ e ∈ xs, e.cpu ≠ c) → mreplay l = some (s, h) → mreplay (xs ++ l) = some (s', h') →
      AtM c s t → AtM c s' t
  | [], l, s, s', h, h', _, hl, hr, hA => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact hA
  | e :: xs, l, s, s', h, h', hx, hl, hr, hA => by
    obtain ⟨s2, h2, o, hl2, hp, -⟩ := mreplay_cons hr
    exact at_otherM (mreplay_inv hl2) hp (hx e List.mem_cons_self)
      (at_othersM xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2 hA)

theorem at_pullM {ε : MEnv} {c : CPU} (hR : RelyM ε c) {l : MLog} {s : MS} {h : List HEvent}
    {t : CThread MPrim} (hl : mreplay l = some (s, h)) (hA : AtM c s t) :
    ∃ s' h', mreplay (mpull ε c l) = some (s', h') ∧ AtM c s' t := by
  obtain ⟨s', h', hr⟩ := hR.conform l s h hl
  exact ⟨s', h', hr, at_othersM (ε.query c l) (ε.noSelf c l) hl hr hA⟩

/-! ## Our own step -/

local macro "nstep" : tactic => `(tactic| (simp only [ClightL.step, CThread.cfg, codeMC, acquireM_eq,
  releaseM_eq, REST, TAIL, KR, Option.some.injEq] at *; subst_vars))

theorem own_stepM {c : CPU} {l : MLog} {s : MS} {H : List HEvent} {t : CThread MPrim}
    {c' : Config MPrim MLog} (hc : c < NCPU) (hl : mreplay l = some (s, H)) (hA : AtM c s t)
    (hst : ClightL.step (mprims noEnvM c) (t.cfg l) = some c') :
    (c'.abs = l ∧ AtM c s (thr c')) ∨ ∃ s' H', mreplay c'.abs = some (s', H') ∧ AtM c s' (thr c') := by
  have hi := mreplay_inv hl
  have hs0 := stOf_eq hl
  cases hA with
  | a0 h => simp only [ClightL.step, CThread.cfg, codeMC, Option.some.injEq] at hst; subst hst
            exact .inl ⟨rfl, .a1 h⟩
  | a1 h => simp only [ClightL.step, CThread.cfg, acquireM_eq, Option.some.injEq] at hst; subst hst
            exact .inl ⟨rfl, .a2 h⟩
  | @a2 σ h =>
    simp only [ClightL.step, CThread.cfg, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .swap⟩ = some (⟨s.hd, s.tl + 1, fset s.pos c (some s.tl), fset s.busy c true,
        fset s.next c none, fset s.ph c (match tailOf s with | none => .front | some p => .linking p)⟩,
        none) := by simp [mstep, hc, h] <;> rfl
    refine .inr ⟨_, _, mreplay_cons_of hl hp, .a3 ?_⟩
    rw [hs0]
    cases ht : tailOf s with
    | none => left; simp [encC]
    | some q => right; exact ⟨q, by simp, by simpa using encC_some_ne q⟩
  | a3 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact .inl ⟨rfl, .a4 h⟩
  | a4 h => simp only [ClightL.step, CThread.cfg, REST, Option.some.injEq] at hst; subst hst
            exact .inl ⟨rfl, .a5 h⟩
  | @a5 σ h =>
    simp only [ClightL.step, CThread.cfg, ITE, Option.some.injEq] at hst; subst hst
    rcases h with ⟨hf, hp0⟩ | ⟨q, hq, hp0⟩
    · refine .inl ⟨rfl, ?_⟩; simp only [thr, Expr.eval, BinOp.eval, hp0, ite_true]; exact .a15 (.inl hf)
    · refine .inl ⟨rfl, ?_⟩; simp only [thr, Expr.eval, BinOp.eval, hp0, ite_false]; exact .a6 ⟨q, hq⟩
  | a6 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact .inl ⟨rfl, .a7 h⟩
  | @a7 σ h =>
    obtain ⟨q, hq⟩ := h
    simp only [ClightL.step, CThread.cfg, linkC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .link⟩ = some (⟨s.hd, s.tl, s.pos, s.busy, fset s.next q (some c),
        fset s.ph c .waiting⟩, none) := by simp [mstep, hc, hq]
    exact .inr ⟨_, _, mreplay_cons_of hl hp, .a8 (by simp)⟩
  | a8 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact .inl ⟨rfl, .a9 h⟩
  | a9 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact .inl ⟨rfl, .a10 h⟩
  | @a10 σ h =>
    simp only [ClightL.step, CThread.cfg, gbC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getBusy⟩ = some (s, none) := by simp [mstep, hc, h]
    refine .inr ⟨_, _, mreplay_cons_of hl hp, .a11 h fun h0 => ?_⟩
    simp only [Locals.set_same, hs0] at h0; split at h0
    · exact absurd h0 (by decide)
    · simpa using ‹¬ s.busy c = true›
  | a11 h1 h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                 exact .inl ⟨rfl, .a12 h1 h2⟩
  | @a12 σ h1 h2 =>
    change ClightL.step _ (CThread.cfg ⟨.while (.bin .ne (.var "b") (.const 0)) gbC, .seq holdC KR, σ⟩ l) = _
      at hst
    rw [cstep_while] at hst
    by_cases hz : (Expr.bin BinOp.ne (.var "b") (.const 0)).eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have hb0 : σ "b" = 0 := by rw [ne_eval_zero] at hz; simpa [Expr.eval] using hz
      exact .inl ⟨rfl, .a15 (.inr ⟨h1, h2 hb0⟩)⟩
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      exact .inl ⟨rfl, .a13 h1⟩
  | @a13 σ h =>
    simp only [ClightL.step, CThread.cfg, gbC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getBusy⟩ = some (s, none) := by simp [mstep, hc, h]
    refine .inr ⟨_, _, mreplay_cons_of hl hp, .a14 h fun h0 => ?_⟩
    simp only [Locals.set_same, hs0] at h0; split at h0
    · exact absurd h0 (by decide)
    · simpa using ‹¬ s.busy c = true›
  | a14 h1 h2 => simp only [ClightL.step, CThread.cfg, KLB, Option.some.injEq] at hst; subst hst
                 exact .inl ⟨rfl, .a12 h1 h2⟩
  | a15 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
             exact .inl ⟨rfl, .a16 h⟩
  | @a16 σ h =>
    simp only [ClightL.step, CThread.cfg, holdC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .hold⟩ = some (⟨s.hd, s.tl, s.pos, s.busy, s.next, fset s.ph c .holding⟩,
        some (.acq c)) := by
      rcases h with h | ⟨h1, h2⟩
      · simp [mstep, hc, h]
      · simp [mstep, hc, h1, h2]
    exact .inr ⟨_, _, mreplay_cons_of hl hp, .a17 (by simp)⟩
  | a17 h => simp only [ClightL.step, CThread.cfg, KR, Option.some.injEq] at hst; subst hst
             exact .inl ⟨rfl, .a18 h⟩
  | a18 h => simp only [ClightL.step, CThread.cfg, releaseM_eq, Option.some.injEq] at hst; subst hst
             exact .inl ⟨rfl, .a19 h⟩
  | @a19 σ h =>
    simp only [ClightL.step, CThread.cfg, gnC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getNext⟩ = some (s, none) := by simp [mstep, hc, h]
    refine .inr ⟨_, _, mreplay_cons_of hl hp, .a20 h fun h0 hn => ?_⟩
    simp [hs0, hn, encC] at h0
  | a20 h1 h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                 exact .inl ⟨rfl, .a21 h1 h2⟩
  | @a21 σ h1 h2 =>
    simp only [ClightL.step, CThread.cfg, RITE, Option.some.injEq] at hst; subst hst
    by_cases hn0 : σ "n" = 0
    · refine .inl ⟨rfl, ?_⟩; simp only [thr, Expr.eval, BinOp.eval, hn0, ite_true]; exact .a23 h1
    · refine .inl ⟨rfl, ?_⟩; simp only [thr, Expr.eval, BinOp.eval, hn0, ite_false]; exact .a22 h1 (h2 hn0)
  | @a22 σ h1 h2 =>
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 h2
    simp only [ClightL.step, CThread.cfg, hoC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .handoff⟩ = some (⟨s.hd + 1, s.tl, fset s.pos c none, fset s.busy d false, s.next,
        fset s.ph c .idle⟩, some (.rel c)) := by simp [mstep, hc, h1, hd]
    exact .inr ⟨_, _, mreplay_cons_of hl hp, .done (by simp)⟩
  | a23 h => simp only [ClightL.step, CThread.cfg, TAIL, Option.some.injEq] at hst; subst hst
             exact .inl ⟨rfl, .a24 h⟩
  | @a24 σ h =>
    simp only [ClightL.step, CThread.cfg, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    simp only [hs0]
    by_cases htl : s.tl = s.hd + 1
    · have ht : tailOf s = some c := (tail_holding hi h).2 htl
      have hp : mstep s ⟨c, .cas⟩ = some (⟨s.hd + 1, s.tl, fset s.pos c none, s.busy, s.next,
          fset s.ph c .idle⟩, some (.rel c)) := by simp [mstep, hc, h, htl]
      exact .inr ⟨_, _, mreplay_cons_of hl hp, .a25 (.inl ⟨by simp [ht], by simp⟩)⟩
    · have ht : ¬ tailOf s = some c := fun x => htl ((tail_holding hi h).1 x)
      have hp : mstep s ⟨c, .cas⟩ = some (s, none) := by simp [mstep, hc, h, htl]
      exact .inr ⟨_, _, mreplay_cons_of hl hp, .a25 (.inr ⟨by simp [ht], h⟩)⟩
  | a25 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
             exact .inl ⟨rfl, .a26 h⟩
  | @a26 σ h =>
    simp only [ClightL.step, CThread.cfg, KITE, Option.some.injEq] at hst; subst hst
    rcases h with ⟨hk, hidle⟩ | ⟨hk, hh⟩
    · refine .inl ⟨rfl, ?_⟩; simp only [thr, Expr.eval, BinOp.eval, hk, ite_false, ite_true]; exact .done hidle
    · refine .inl ⟨rfl, ?_⟩; simp only [thr, Expr.eval, BinOp.eval, hk, ite_true]
      exact .a27 hh
  | a27 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
             exact .inl ⟨rfl, .a28 h⟩
  | @a28 σ h =>
    simp only [ClightL.step, CThread.cfg, gnC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getNext⟩ = some (s, none) := by simp [mstep, hc, h]
    refine .inr ⟨_, _, mreplay_cons_of hl hp, .a29 h fun h0 hn => ?_⟩
    simp [hs0, hn, encC] at h0
  | a29 h1 h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                 exact .inl ⟨rfl, .a30 h1 h2⟩
  | a30 h1 h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                 exact .inl ⟨rfl, .a31 h1 h2⟩
  | @a31 σ h1 h2 =>
    change ClightL.step _ (CThread.cfg ⟨.while (.bin .eq (.var "n") (.const 0)) gnC, .seq hoC .stop, σ⟩ l) = _
      at hst
    rw [cstep_while] at hst
    by_cases hz : (Expr.bin BinOp.eq (.var "n") (.const 0)).eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have hn0 : σ "n" ≠ 0 := by
        intro h0; simp [Expr.eval, BinOp.eval, h0] at hz
      exact .inl ⟨rfl, .a34 h1 (h2 hn0)⟩
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      exact .inl ⟨rfl, .a32 h1⟩
  | @a32 σ h =>
    simp only [ClightL.step, CThread.cfg, gnC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getNext⟩ = some (s, none) := by simp [mstep, hc, h]
    refine .inr ⟨_, _, mreplay_cons_of hl hp, .a33 h fun h0 hn => ?_⟩
    simp [hs0, hn, encC] at h0
  | a33 h1 h2 => simp only [ClightL.step, CThread.cfg, KLN, Option.some.injEq] at hst; subst hst
                 exact .inl ⟨rfl, .a31 h1 h2⟩
  | a34 h1 h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                 exact .inl ⟨rfl, .a22 h1 h2⟩
  | done h => simp [ClightL.step, CThread.cfg] at hst

/-! ## The per-CPU guarantee -/

def PInvM (ε : MEnv) (c : CPU) (x : Config MPrim MLog) : Prop :=
  (∃ s h, mreplay x.abs = some (s, h)) ∧ ∃ s h, mreplay (mpull ε c x.abs) = some (s, h) ∧ AtM c s (thr x)

theorem pinv_stepM {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) {x y : Config MPrim MLog}
    (hI : PInvM ε c x) (hs : ClightL.step (mprims ε c) x = some y) : PInvM ε c y := by
  obtain ⟨hx0, s, h, hg, hA⟩ := hI
  rcases Link.step_cases (t := thr x) (a := x.abs) hs with ⟨habs, hall⟩ | ⟨-, hQ⟩
  · have hAy : AtM c s (thr y) := by
      rcases own_stepM hc hg hA (hall (mprims noEnvM c) (mpull ε c x.abs)) with ⟨-, hA'⟩ | ⟨s', h', hr, hA'⟩
      · simpa using hA'
      · simp only [CThread.cfg] at hr; rw [hg] at hr; cases hr; simpa using hA'
    exact ⟨habs ▸ hx0, s, h, by rw [habs]; exact hg, hAy⟩
  · have hs' : ClightL.step (mprims noEnvM c) ((thr x).cfg (mpull ε c x.abs)) = some y :=
      hQ _ _ fun p args => mprims_pull (by rw [mpull_noEnvM]) p args
    rcases own_stepM hc hg hA hs' with ⟨he, hA'⟩ | ⟨s', h', hr, hA'⟩
    · exact ⟨⟨s, h, he ▸ hg⟩, at_pullM hR (he ▸ hg) hA'⟩
    · exact ⟨⟨s', h', hr⟩, at_pullM hR hr hA'⟩

theorem pinv_starM {ε : MEnv} {c : CPU} (hc : c < NCPU) (hR : RelyM ε c) :
    ∀ {a b}, Star (mprims ε c) a b → PInvM ε c a → PInvM ε c b := by
  intro a b hab
  induction hab with
  | refl => exact id
  | step hs _ ih => exact fun hI => ih (pinv_stepM hc hR hI hs)

/-- **Per-CPU guarantee** of `acquireM; releaseM`, on `L0[c]` alone. -/
theorem client_guarM {c : CPU} (hc : c < NCPU) (σ : Locals) {l0 : MLog} {S0 : MS} {H0 : List HEvent}
    (hl0 : mreplay l0 = some (S0, H0)) (hidle : S0.ph c = .idle) : GuarM c ⟨codeMC, .stop, σ⟩ l0 := by
  intro ε hR x hx
  exact (pinv_starM hc hR hx ⟨⟨S0, H0, hl0⟩, at_pullM hR hl0 (.a0 hidle)⟩).1

/-- The critical section: between `acquireM` and `releaseM`. -/
def InCSM (t : CThread MPrim) : Prop :=
  (t.stmt = .skip ∧ t.cont = KR) ∨ (t.stmt = releaseM ∧ t.cont = .stop)

theorem at_csM {c : CPU} {s : MS} {t : CThread MPrim} (hA : AtM c s t) (hcs : InCSM t) :
    s.ph c = .holding := by
  cases hA <;> simp_all [InCSM, KR, codeMC, acquireM, releaseM, REST, ITE, TAIL, KITE, RITE, KLB, KLN,
    holdC, linkC, gbC, gnC, hoC, loopB, loopN]

theorem client_csM {c : CPU} (hc : c < NCPU) (σ : Locals) {ε : MEnv} (hR : RelyM ε c)
    {x : Config MPrim MLog} (hx : Star (mprims ε c) (CThread.cfg ⟨codeMC, .stop, σ⟩ []) x)
    (hcs : InCSM (thr x)) : ∃ s h, mreplay x.abs = some (s, h) ∧ s.ph c = .holding := by
  obtain ⟨⟨s, h, hr⟩, s', h', hr', hA⟩ := pinv_starM hc hR hx ⟨⟨_, _, rfl⟩, at_pullM hR rfl (.a0 rfl)⟩
  have hph := (others_eventsM _ (ε.noSelf c x.abs) hr hr').1
  exact ⟨s, h, hr, hph ▸ at_csM hA hcs⟩

/-! ## The multicore machine -/

/-- `T` CPUs, each running `acquireM; releaseM`. -/
def poolM (T : Nat) : List (CThread MPrim) := List.replicate T ⟨codeMC, .stop, fun _ => 0⟩

theorem pool_guarM (T : Nat) (hT : T ≤ NCPU) : ∀ c (hc : c < (poolM T).length), GuarM c (poolM T)[c] [] := by
  intro c hc
  have hcT : c < T := by simpa [poolM] using hc
  simp only [poolM, List.getElem_replicate]
  exact client_guarM (Nat.lt_of_lt_of_le hcT hT) _ rfl rfl

/-- **Multicore linking for the MCS lock.** -/
theorem mcs_linked (T : Nat) (hT : T ≤ NCPU) {cs : List (CThread MPrim)} {l : MLog}
    (h : CSteps PGM (poolM T) [] cs l) : LinkedM (poolM T) [] cs l :=
  composeM (pool_guarM T hT) ⟨_, _, rfl⟩ h

/-- **Mutual exclusion on the multicore machine, by linking.** Two CPUs
between their `acquireM` and `releaseM` are the same CPU. -/
theorem multicore_cs_exclusiveM (T : Nat) (hT : T ≤ NCPU) {cs : List (CThread MPrim)} {l : MLog}
    (h : CSteps PGM (poolM T) [] cs l) (c d : Nat) (hc : c < cs.length) (hd : d < cs.length)
    (hcc : InCSM cs[c]) (hdc : InCSM cs[d]) : c = d := by
  have hQ := transferM (pool_guarM T hT) ⟨_, _, rfl⟩
    (Q := fun c x => InCSM (thr x) → ∃ s h, mreplay x.abs = some (s, h) ∧ s.ph c = .holding)
    (fun c hc ε hR x hx hcs => by
      have hcT : c < T := by simpa [poolM] using hc
      simp only [poolM, List.getElem_replicate] at hx
      exact client_csM (Nat.lt_of_lt_of_le hcT hT) _ hR hx hcs) h
  obtain ⟨⟨Sg, Hg, hl⟩, -⟩ := mcs_linked T hT h
  have glob : ∀ c (hc : c < cs.length), InCSM cs[c] → Sg.ph c = .holding := by
    intro c hc hcs
    obtain ⟨lc, xs, hQc, rfl, hx⟩ := hQ c hc
    obtain ⟨s, h', hr, hph⟩ := hQc hcs
    exact (others_eventsM xs hx hr hl).1 ▸ hph
  exact mutexM hl (glob c hc hcc) (glob d hd hdc)

end MCSLink
