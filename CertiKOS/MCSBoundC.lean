import CertiKOS.MCSBound

/-!
# The bound as a C argument: `acquire(bound)`

In Kim et al.'s development (§4.3), `mcs_acquire` takes one more argument than
the C code needs: the bound number. The C code only passes it to `SWAP_TAIL`,
whose event records it. This file does the same in ClightL.

* `bprims`: the MCS primitives over bounded logs (`MCSBound.BLog`). `swap`
  takes the bound as its argument and appends `swap b`. `mem` is the
  critical section's shared-memory primitive.
* `acquireB`, `releaseB`: the MCS code of `MCSLock.lean`, with
  `p = swap(bound)` in place of `p = swap()`. `clientB n` is
  `acquire(bound); mem() × n; release()`.
* `step_erase`: running bounded code on a bounded log is the same,
  step for step, as running its erasure (`erS`: drop the bound argument, turn
  `mem()` into an assignment) on the erased log (`MCSBound.erase`). This needs
  the bounded environment to erase to an unbounded one (`EnvErases`).
  `liftEnv` builds such an environment from any unbounded one.
* `star_lift`: so every run of the erased code lifts to a run of the bounded
  code. `erS acquireB = acquireM` and `erS releaseB = releaseM` hold by `rfl`,
  so the liveness and simulation results of `MCSLock.lean` carry over:
  `acquireB_terminates` and `clientB_terminates` (under `RelyM`, `FairB`,
  `FairN`).
* `clientB_records_bound`: the bound flows from the C argument into the log.
  The final log has the event `swap (σ "bound")` by this CPU.
* `clientB_guarantee`: **the bounded per-CPU guarantee**. If `n < bound`
  and the environment keeps the bounded log valid (`BRely`), the client
  finishes idle with a valid bounded log, and so (`bcal_hbreplay`) a valid
  `H_CalLock` log. The proof has three phases. In acquire and release, each
  own event is MCS-valid because the erased run is (`phase_valid`). The
  invariant `QB` tracks the recorded bound and the budget. In the critical
  section, each `mem` has budget left (`crit_validB`).
-/

namespace MCSBoundC

open ClightL Ticket MCS MCSBound

/-! ## Bounded primitives -/

inductive BPrim
  | m (p : MPrim)
  | mem

structure BEnv where
  query : CPU → BLog → List BEvent
  noSelf : ∀ c l e, e ∈ query c l → e.cpu ≠ c

def bpull (εB : BEnv) (c : CPU) (l : BLog) : BLog := εB.query c l ++ l

/-- The protocol state of a bounded log. -/
def stB (l : BLog) : MS := stOf (erase l)

def bprims (εB : BEnv) (c : CPU) : Prims BPrim BLog
  | .m .swap, b :: _, l =>
      let l1 := bpull εB c l; some (encC (tailOf (stB l1)), ⟨c, .swap b.toNat⟩ :: l1)
  | .m .link, [], l => some (0, ⟨c, .lk .link⟩ :: bpull εB c l)
  | .m .getBusy, [], l =>
      let l1 := bpull εB c l; some (if (stB l1).busy c then 1 else 0, ⟨c, .lk .getBusy⟩ :: l1)
  | .m .hold, [], l => some (0, ⟨c, .lk .hold⟩ :: bpull εB c l)
  | .m .getNext, [], l =>
      let l1 := bpull εB c l; some (encC ((stB l1).next c), ⟨c, .lk .getNext⟩ :: l1)
  | .m .cas, [], l =>
      let l1 := bpull εB c l; some (if tailOf (stB l1) = some c then 1 else 0, ⟨c, .lk .cas⟩ :: l1)
  | .m .handoff, [], l => some (0, ⟨c, .lk .handoff⟩ :: bpull εB c l)
  | .mem, _, l => some (0, ⟨c, .mem⟩ :: l)
  | _, _, _ => none

/-! ## The C code -/

def loopBB : Stmt BPrim := .while (.bin .ne (.var "b") (.const 0)) (.call "b" (.m .getBusy) [])

/-- `acquire(bound)`: as `acquireM`, but `swap` gets the bound. -/
def acquireB : Stmt BPrim :=
  .seq (.call "p" (.m .swap) [.var "bound"])
    (.seq (.ite (.bin .ne (.var "p") (.const 0))
        (.seq (.call "_" (.m .link) []) (.seq (.call "b" (.m .getBusy) []) loopBB)) .skip)
      (.call "_" (.m .hold) []))

def loopNB : Stmt BPrim := .while (.bin .eq (.var "n") (.const 0)) (.call "n" (.m .getNext) [])

def releaseB : Stmt BPrim :=
  .seq (.call "n" (.m .getNext) [])
    (.ite (.bin .ne (.var "n") (.const 0)) (.call "_" (.m .handoff) [])
      (.seq (.call "k" (.m .cas) [])
        (.ite (.bin .eq (.var "k") (.const 0))
          (.seq (.call "n" (.m .getNext) []) (.seq loopNB (.call "_" (.m .handoff) []))) .skip)))

/-- A critical section of `n` shared-memory events. -/
def critB : Nat → Stmt BPrim
  | 0 => .skip
  | n + 1 => .seq (.call "_" .mem []) (critB n)

def clientB (n : Nat) : Stmt BPrim := .seq acquireB (.seq (critB n) releaseB)

/-! ## Erasure -/

def erCall (x : Ident) : BPrim → List Expr → Stmt MPrim
  | .m .swap, [] => .call x .swap [.const 0]
  | .m .swap, _ :: _ => .call x .swap []
  | .m .link, args => .call x .link args
  | .m .getBusy, args => .call x .getBusy args
  | .m .hold, args => .call x .hold args
  | .m .getNext, args => .call x .getNext args
  | .m .cas, args => .call x .cas args
  | .m .handoff, args => .call x .handoff args
  | .mem, _ => .assign x (.const 0)

def erS : Stmt BPrim → Stmt MPrim
  | .skip => .skip
  | .assign x e => .assign x e
  | .seq a b => .seq (erS a) (erS b)
  | .ite e a b => .ite e (erS a) (erS b)
  | .while e b => .while e (erS b)
  | .call x p args => erCall x p args

def erK : Cont BPrim → Cont MPrim
  | .stop => .stop
  | .seq s k => .seq (erS s) (erK k)
  | .loop e b k => .loop e (erS b) (erK k)

def erC (x : Config BPrim BLog) : Config MPrim MLog := ⟨erS x.stmt, erK x.cont, x.locals, erase x.abs⟩

theorem erS_acquireB : erS acquireB = acquireM := rfl
theorem erS_releaseB : erS releaseB = releaseM := rfl

/-- The bounded environment's events erase to the unbounded environment's. -/
def EnvErases (εB : BEnv) (ε : MEnv) : Prop := ∀ c l, erase (εB.query c l) = ε.query c (erase l)

theorem erase_append (a b : BLog) : erase (a ++ b) = erase a ++ erase b := by
  simp [erase, List.filterMap_append]

theorem erase_bpull {εB : BEnv} {ε : MEnv} (hE : EnvErases εB ε) (c : CPU) (l : BLog) :
    erase (bpull εB c l) = mpull ε c (erase l) := by
  simp [bpull, mpull, erase_append, hE c l]

/-- Give each environment swap a bound. -/
def liftE (bd : CPU → Nat) (e : MEvent) : BEvent :=
  ⟨e.cpu, match e.kind with | .swap => .swap (bd e.cpu) | k => .lk k⟩

theorem erase_liftE (bd : CPU → Nat) : ∀ l : MLog, erase (l.map (liftE bd)) = l
  | [] => rfl
  | ⟨d, k⟩ :: l => by
    have ih := erase_liftE bd l
    cases k <;> simp_all [erase, eraseE, liftE]

/-- A bounded environment from any unbounded one: it acts as `ε` on the erased log. -/
def liftEnv (ε : MEnv) (bd : CPU → Nat) : BEnv where
  query c l := (ε.query c (erase l)).map (liftE bd)
  noSelf c l e he := by
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    exact ε.noSelf c _ e' he'

theorem liftEnv_erases (ε : MEnv) (bd : CPU → Nat) : EnvErases (liftEnv ε bd) ε :=
  fun c l => erase_liftE bd _

/-! ## Step-for-step simulation -/

/-- **Erasure commutes with a step.** -/
theorem step_erase {εB : BEnv} {ε : MEnv} (hE : EnvErases εB ε) (c : CPU) (x : Config BPrim BLog) :
    step (mprims ε c) (erC x) = (step (bprims εB c) x).map erC := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  have hb := erase_bpull hE c l
  cases stmt with
  | skip => cases cont <;> rfl
  | assign x e => rfl
  | seq a b => rfl
  | ite e a b => by_cases hz : Expr.eval σ e = 0#32 <;> simp [step, erC, erS, hz]
  | «while» e b => by_cases hz : Expr.eval σ e = 0#32 <;> simp [step, erC, erS, erK, hz]
  | call x p args =>
    cases p with
    | mem => rfl
    | m p =>
      have hb' : (bpull εB c l).filterMap eraseE = mpull ε c (l.filterMap eraseE) := hb
      cases p <;> cases args <;>
        simp [step, erC, erS, erCall, bprims, mprims, stB, hb', erase, eraseE, List.filterMap_cons]

theorem star_erase {εB : BEnv} {ε : MEnv} (hE : EnvErases εB ε) (c : CPU) {x y : Config BPrim BLog}
    (h : Star (bprims εB c) x y) : Star (mprims ε c) (erC x) (erC y) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (by rw [step_erase hE, hs]; rfl) ih

/-- **Every run of the erased code lifts to a run of the bounded code.** -/
theorem star_lift {εB : BEnv} {ε : MEnv} (hE : EnvErases εB ε) (c : CPU) {a y' : Config MPrim MLog}
    (h : Star (mprims ε c) a y') : ∀ x, erC x = a → ∃ y, Star (bprims εB c) x y ∧ erC y = y' := by
  induction h with
  | refl => intro x hx; exact ⟨x, .refl _, hx⟩
  | step hs _ ih =>
    intro x hx
    rw [← hx, step_erase hE] at hs
    cases hx' : step (bprims εB c) x with
    | none => rw [hx'] at hs; cases hs
    | some x' =>
      rw [hx'] at hs; simp only [Option.map_some, Option.some.injEq] at hs
      obtain ⟨y, h1, h2⟩ := ih x' hs
      exact ⟨y, .step hx' h1, h2⟩

theorem erS_skip {s : Stmt BPrim} (h : erS s = .skip) : s = .skip := by
  cases s with
  | skip => rfl
  | call x p args => cases p with
    | mem => simp [erS, erCall] at h
    | m p => cases p <;> cases args <;> simp [erS, erCall] at h
  | _ => simp [erS] at h

theorem erK_stop {k : Cont BPrim} (h : erK k = .stop) : k = .stop := by
  cases k <;> simp [erK] at h; rfl

/-- A finished run of the erased code from `.stop` lifts to a finished bounded run. -/
theorem lift_final {εB : BEnv} {ε : MEnv} (hE : EnvErases εB ε) (c : CPU) {s : Stmt BPrim} {σ σ' : Locals}
    {l : BLog} {r : MLog} (h : Star (mprims ε c) ⟨erS s, .stop, σ, erase l⟩ ⟨.skip, .stop, σ', r⟩) :
    ∃ rb, Star (bprims εB c) ⟨s, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧ erase rb = r := by
  obtain ⟨⟨s2, k2, σ2, rb⟩, h1, h2⟩ := star_lift hE c h ⟨s, .stop, σ, l⟩ rfl
  simp only [erC, Config.mk.injEq] at h2
  obtain ⟨hs, hk, rfl, hr⟩ := h2
  rw [erS_skip hs, erK_stop hk] at h1
  exact ⟨rb, h1, hr⟩

/-! ## Liveness carries over -/

/-- **`acquire(bound)` terminates** under the same fairness as `acquireM`. -/
theorem acquireB_terminates {εB : BEnv} {ε : MEnv} (hE : EnvErases εB ε) {c : CPU} (hc : c < NCPU)
    (hR : RelyM ε c) {l : BLog} {s : MS} {h : List HEvent} (hl : mreplay (erase l) = some (s, h))
    (hidle : s.ph c = .idle) (bound : MLog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K) (hF : FairB ε c bound)
    (σ : Locals) :
    ∃ σ' rb, Star (bprims εB c) ⟨acquireB, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧ AcqPostM c h (erase rb) := by
  obtain ⟨fuel, r, hspec⟩ := acquireM_live hc hR hl hidle bound K hK hF
  obtain ⟨σ', hst⟩ := acquireM_sim ε c fuel σ (erase l) r .stop hspec
  obtain ⟨rb, h1, rfl⟩ := lift_final hE c (s := acquireB) hst
  exact ⟨σ', rb, h1, acquireM_guarantee hc hR hl hidle hspec⟩

/-- The erased critical section only assigns. -/
theorem crit_run (ε : MEnv) (c : CPU) : ∀ (n : Nat) (σ : Locals) (r : MLog) (k : Cont MPrim),
    ∃ σ', Star (mprims ε c) ⟨erS (critB n), k, σ, r⟩ ⟨.skip, k, σ', r⟩
  | 0, σ, r, k => ⟨σ, .refl _⟩
  | n + 1, σ, r, k => by
    obtain ⟨σ', h⟩ := crit_run ε c n (σ.set "_" 0) r k
    exact ⟨σ', .step rfl (.step rfl (.step rfl h))⟩

/-- **The whole client terminates**: `acquire(bound); mem() × n; release()`. -/
theorem clientB_terminates {εB : BEnv} {ε : MEnv} (hE : EnvErases εB ε) {c : CPU} (hc : c < NCPU)
    (hR : RelyM ε c) {l : BLog} {s : MS} {h : List HEvent} (hl : mreplay (erase l) = some (s, h))
    (hidle : s.ph c = .idle) (bB : MLog → Nat) (K : Nat) (hK : ∀ l, bB l ≤ K) (hFB : FairB ε c bB)
    (bN : MLog → Nat) (hFN : FairN ε c bN) (n : Nat) (σ : Locals) :
    ∃ σ' rb, Star (bprims εB c) ⟨clientB n, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ := by
  obtain ⟨fuel, r1, hspec⟩ := acquireM_live hc hR hl hidle bB K hK hFB
  obtain ⟨σ1, hst1⟩ := acquireM_sim ε c fuel σ (erase l) r1 (.seq (.seq (erS (critB n)) releaseM) .stop) hspec
  obtain ⟨s1, h1, hr1, hh1, -⟩ := acquireM_guarantee hc hR hl hidle hspec
  obtain ⟨σ2, hst2⟩ := crit_run ε c n σ1 r1 (.seq releaseM .stop)
  obtain ⟨fuel2, r2, hspec2⟩ := releaseM_live hc hR hr1 hh1 bN hFN
  obtain ⟨σ3, hst3⟩ := releaseM_sim ε c fuel2 σ2 r1 r2 .stop hspec2
  have hall : Star (mprims ε c) ⟨erS (clientB n), .stop, σ, erase l⟩ ⟨.skip, .stop, σ3, r2⟩ :=
    .step rfl (hst1.trans (.step rfl (.step rfl (hst2.trans (.step rfl hst3)))))
  obtain ⟨rb, hrun, -⟩ := lift_final hE c hall
  exact ⟨σ3, rb, hrun⟩

/-! ## The bound reaches the log -/

theorem bprims_ext {εB : BEnv} {c : CPU} {p : BPrim} {vs : List Val} {l l' : BLog} {v : Val}
    (h : bprims εB c p vs l = some (v, l')) : ∃ ys, l' = ys ++ l := by
  cases p with
  | mem => simp only [bprims, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ⟨[_], rfl⟩
  | m p =>
    cases p <;> cases vs <;> simp only [bprims, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
      first
        | (obtain ⟨-, rfl⟩ := h; exact ⟨_ :: εB.query c l, rfl⟩)

theorem star_ext {εB : BEnv} {c : CPU} {x y : Config BPrim BLog} (h : Star (bprims εB c) x y) :
    ∃ ys, y.abs = ys ++ x.abs := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | @step a b d hs _ ih =>
    obtain ⟨ys, hys⟩ := ih
    obtain ⟨stmt, cont, σ, l⟩ := a
    simp only [step] at hs
    have : ∃ zs, b.abs = zs ++ l := by
      split at hs <;> (try simp only [Option.some.injEq] at hs) <;> (try (subst hs; exact ⟨[], rfl⟩))
      · simp at hs
      · split at hs <;> simp only [Option.some.injEq] at hs <;> subst hs <;> exact ⟨[], rfl⟩
      · split at hs
        · rename_i v a' hp
          simp only [Option.some.injEq] at hs; subst hs
          obtain ⟨zs, rfl⟩ := bprims_ext hp
          exact ⟨zs, rfl⟩
        · simp at hs
    obtain ⟨zs, hzs⟩ := this
    exact ⟨ys ++ zs, by rw [hys, hzs, List.append_assoc]⟩

/-- Stepping out of a non-final configuration: a run to a final one goes through the successor. -/
theorem star_next {P : Prims BPrim BLog} {x x' y : Config BPrim BLog} (h : Star P x y)
    (hs : step P x = some x') (hy : Final y) : Star P x' y := by
  cases h with
  | refl => rw [step_final hy] at hs; cases hs
  | step hs' h' => rw [hs] at hs'; cases hs'; exact h'

/-- **The bound reaches the log**: a finished run of the client has this CPU's
`swap` event carrying the C argument `bound`. -/
theorem clientB_records_bound {εB : BEnv} {c : CPU} {n : Nat} {σ σ' : Locals} {l rb : BLog}
    (h : Star (bprims εB c) ⟨clientB n, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩) :
    (⟨c, .swap (σ "bound").toNat⟩ : BEvent) ∈ rb := by
  have hfin : Final (⟨.skip, .stop, σ', rb⟩ : Config BPrim BLog) := ⟨rfl, rfl⟩
  have h1 := star_next h rfl hfin
  have h2 := star_next h1 rfl hfin
  have h3 := star_next h2 (by simp [step, bprims, Expr.eval]; rfl) hfin
  obtain ⟨ys, hys⟩ := star_ext h3
  simp only at hys
  rw [hys]
  exact List.mem_append_right _ List.mem_cons_self


/-! ## The bounded guarantee

A client that makes fewer memory events than its bound keeps the bounded log
valid. The proof runs in three phases: `acquire(bound)`, the critical section,
and `release()`. For acquire and release, the MCS validity of each own event
comes from the erased run, which `MCSLock.lean` already proves valid. The
bounds are tracked by the invariant `QB`: once this CPU has swapped, its
recorded bound is the C argument, and while it holds the lock it has budget
left. -/

/-- Continuation framing: append `k` below a continuation. -/
def appK {Pn : Type} : Cont Pn → Cont Pn → Cont Pn
  | .stop, k => k
  | .seq s κ, k => .seq s (appK κ k)
  | .loop e b κ, k => .loop e b (appK κ k)

theorem step_app {Pn Abs : Type} {P : Prims Pn Abs} {s s' : Stmt Pn} {κ κ' k : Cont Pn} {σ σ' : Locals}
    {a a' : Abs} (h : step P ⟨s, κ, σ, a⟩ = some ⟨s', κ', σ', a'⟩) :
    step P ⟨s, appK κ k, σ, a⟩ = some ⟨s', appK κ' k, σ', a'⟩ := by
  cases s with
  | skip =>
    cases κ with
    | stop => simp [step] at h
    | seq s2 κ2 => simp only [step, Option.some.injEq, Config.mk.injEq] at h ⊢; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; simp [appK]
    | loop e b κ2 => simp only [step, Option.some.injEq, Config.mk.injEq] at h ⊢; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; simp [appK]
  | assign x e => simp only [step, Option.some.injEq, Config.mk.injEq] at h ⊢; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; simp
  | seq a b => simp only [step, Option.some.injEq, Config.mk.injEq] at h ⊢; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; simp [appK]
  | ite e a b => simp only [step, Option.some.injEq, Config.mk.injEq] at h ⊢; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; simp
  | «while» e b =>
    simp only [step] at h ⊢
    split at h <;> simp only [Option.some.injEq, Config.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;>
      simp_all [appK]
  | call x p args =>
    simp only [step] at h ⊢
    split at h
    · rename_i v a2 hp; simp only [Option.some.injEq, Config.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      simp [hp]
    · simp at h

theorem star_app {Pn Abs : Type} {P : Prims Pn Abs} {x y : Config Pn Abs} (h : Star P x y) (k : Cont Pn)
    {σ' : Locals} {a' : Abs} (hy : y = ⟨.skip, .stop, σ', a'⟩) :
    Star P ⟨x.stmt, appK x.cont k, x.locals, x.abs⟩ ⟨.skip, k, σ', a'⟩ := by
  induction h with
  | refl => subst hy; exact .refl _
  | @step a b d hs _ ih =>
    obtain ⟨s1, κ1, σ1, a1⟩ := a
    obtain ⟨s2, κ2, σ2, a2⟩ := b
    exact .step (step_app hs) (ih hy)

/-! ### Other CPUs' events leave our bound, phase and budget alone -/

theorem bstep_other {bs bs' : BS} {e : BEvent} {o : Option HBEvent} {c : CPU} (hi : MInv bs.s)
    (hi' : MInv bs'.s) (hs : bstep bs e = some (bs', o)) (hne : e.cpu ≠ c) :
    bs'.s.ph c = bs.s.ph c ∧ bs'.bnd c = bs.bnd c ∧ (bs.s.ph c = .holding → bs'.self = bs.self) := by
  obtain ⟨d, k⟩ := e
  simp only at hne
  cases k with
  | mem =>
    simp only [bstep] at hs
    split at hs
    · rename_i h
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      exact ⟨rfl, rfl, fun hh => absurd (hi.mutex h.1 hh) hne⟩
    · simp at hs
  | swap b =>
    simp only [bstep] at hs
    split at hs
    · rename_i s' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      exact ⟨(mstep_other hi hm hne).1, fset_other _ _ (Ne.symm hne), fun _ => rfl⟩
    · simp at hs
  | lk k =>
    have hk : k ≠ .swap := by rintro rfl; simp [bstep] at hs
    simp only [bstep, hk, ite_false, lkstep] at hs
    split at hs
    · rename_i s' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      exact ⟨(mstep_other hi hm hne).1, rfl, fun _ => rfl⟩
    · rename_i s' x hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      have hph := (mstep_other hi hm hne).1
      obtain ⟨rfl, -, hh', -⟩ := mstep_acq_cases hm
      exact ⟨hph, rfl, fun hh => absurd (hi'.mutex hh' (by simp only; rw [hph]; exact hh)) hne⟩
    · rename_i s' x hm
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        have hph := (mstep_other hi hm hne).1
        obtain ⟨rfl, hh0, -⟩ := mstep_rel_cases hm
        exact ⟨hph, rfl, fun hh => absurd (hi.mutex hh0 hh) hne⟩
      · simp at hs
    · simp at hs

theorem bcal_others {c : CPU} {l : BLog} {bs : BS} {hb : List HBEvent} (hl : bcal l = some (bs, hb)) :
    ∀ (xs : BLog) {bs' : BS} {hb' : List HBEvent}, (∀ e ∈ xs, e.cpu ≠ c) → bcal (xs ++ l) = some (bs', hb') →
      bs'.s.ph c = bs.s.ph c ∧ bs'.bnd c = bs.bnd c ∧ (bs.s.ph c = .holding → bs'.self = bs.self)
  | [], bs', hb', _, hr => by
    simp only [List.nil_append] at hr; rw [hl] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr
    exact ⟨rfl, rfl, fun _ => rfl⟩
  | e :: xs, bs', hb', hx, hr => by
    obtain ⟨bs2, hb2, o, hl2, hs, -⟩ := bcal_cons hr
    obtain ⟨h1, h2, h3⟩ := bcal_others hl xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl2
    obtain ⟨g1, g2, g3⟩ := bstep_other (bcal_inv hl2) (bcal_inv hr) hs (hx e List.mem_cons_self)
    exact ⟨g1.trans h1, g2.trans h2, fun hh => (g3 (h1 ▸ hh)).trans (h3 hh)⟩

/-- **The bounded rely**: the environment keeps the bounded log valid. -/
def BRely (εB : BEnv) (c : CPU) : Prop :=
  ∀ l bs hb, bcal l = some (bs, hb) → ∃ x, bcal (bpull εB c l) = some x

/-- After this CPU's swap its recorded bound is the C argument `b`; while it holds
the lock it has more than `m` units of budget. -/
def QB (c : CPU) (b m : Nat) (bs : BS) : Prop :=
  (bs.s.ph c ≠ .idle → bs.bnd c = b) ∧ (bs.s.ph c = .holding → m < bs.self)

def ValidQ (c : CPU) (b m : Nat) (l : BLog) : Prop := ∃ bs hb, bcal l = some (bs, hb) ∧ QB c b m bs

theorem pull_valid {εB : BEnv} {c : CPU} (hB : BRely εB c) {b m : Nat} {l : BLog} (h : ValidQ c b m l) :
    ValidQ c b m (bpull εB c l) := by
  obtain ⟨bs, hb, hl, q1, q2⟩ := h
  obtain ⟨⟨bs1, hb1⟩, hl1⟩ := hB l bs hb hl
  obtain ⟨h1, h2, h3⟩ := bcal_others hl (εB.query c l) (fun e he => εB.noSelf c l e he) hl1
  exact ⟨bs1, hb1, hl1, fun hne => by rw [h2]; exact q1 (h1 ▸ hne),
    fun hh => by rw [h3 (h1 ▸ hh)]; exact q2 (h1 ▸ hh)⟩

def MOK (m : MLog) : Prop := ∃ s h, mreplay m = some (s, h)

theorem mok_suffix : ∀ (ys : MLog) {l : MLog}, MOK (ys ++ l) → MOK l
  | [], l, h => h
  | e :: ys, l, ⟨s, h, hr⟩ => by
    obtain ⟨s2, h2, o, hl2, -, -⟩ := mreplay_cons hr
    exact mok_suffix ys ⟨s2, h2, hl2⟩

theorem own_step_of_mok {c : CPU} {k : MKind} {l1 : BLog} {bs1 : BS} {hb1 : List HBEvent}
    (hl1 : bcal l1 = some (bs1, hb1)) (h : MOK (⟨c, k⟩ :: erase l1)) : ∃ s' o, mstep bs1.s ⟨c, k⟩ = some (s', o) := by
  obtain ⟨s, hh, hr⟩ := h
  obtain ⟨s0, h0, o, hl0, hp, -⟩ := mreplay_cons hr
  rw [bcal_mreplay hl1] at hl0
  simp only [Option.some.injEq, Prod.mk.injEq] at hl0; obtain ⟨rfl, -⟩ := hl0
  exact ⟨s, o, hp⟩

theorem mstep_swap_none {s s' : MS} {c : CPU} {o : Option HEvent} (hm : mstep s ⟨c, .swap⟩ = some (s', o)) :
    o = none := by
  simp only [mstep] at hm
  split at hm
  · cases hph : s.ph c <;> simp only [hph] at hm <;> try simp at hm
    exact hm.2.symm
  · simp at hm

/-- Our own `swap b` keeps the invariant. -/
theorem own_swap {c : CPU} {b m : Nat} {l1 : BLog} (hv : ValidQ c b m l1)
    (hok : MOK (erase (⟨c, .swap b⟩ :: l1))) : ValidQ c b m (⟨c, .swap b⟩ :: l1) := by
  obtain ⟨bs1, hb1, hl1, q1, q2⟩ := hv
  obtain ⟨s', o, hm⟩ := own_step_of_mok (k := .swap) hl1 (by simpa [erase, eraseE] using hok)
  have ho := mstep_swap_none hm; subst ho
  have hs : bstep bs1 ⟨c, .swap b⟩ = some (⟨s', fset bs1.bnd c b, bs1.self⟩, none) := by simp [bstep, hm]
  refine ⟨_, _, bcal_cons_of hl1 hs, fun _ => by simp, fun hh => absurd hh (mstep_swap_ph hm)⟩

/-- Our own lock event (not `swap`) keeps the invariant, if the bound exceeds `m`. -/
theorem own_lk {c : CPU} {b m : Nat} (hbm : m < b) {k : MKind} (hk : k ≠ .swap) {l1 : BLog}
    (hv : ValidQ c b m l1) (hok : MOK (erase (⟨c, .lk k⟩ :: l1))) : ValidQ c b m (⟨c, .lk k⟩ :: l1) := by
  obtain ⟨bs1, hb1, hl1, q1, q2⟩ := hv
  obtain ⟨s', o, hm⟩ := own_step_of_mok (k := k) hl1 (by simpa [erase, eraseE] using hok)
  have hbs : bstep bs1 ⟨c, .lk k⟩ = lkstep bs1 c k := by simp [bstep, hk]
  cases o with
  | none =>
    have hs : bstep bs1 ⟨c, .lk k⟩ = some (⟨s', bs1.bnd, bs1.self⟩, none) := by rw [hbs]; simp [lkstep, hm]
    refine ⟨_, _, bcal_cons_of hl1 hs, ?_, ?_⟩ <;>
      rcases mstep_none_cases hk hm with ⟨rfl, -⟩ | ⟨-, ⟨p, hp⟩, hw, -⟩
    · exact q1
    · intro _; exact q1 (by rw [hp]; simp)
    · exact q2
    · intro hh; simp only at hh; rw [hw] at hh; cases hh
  | some e =>
    cases e with
    | acq d =>
      obtain ⟨hdc, hown, hh', -⟩ := mstep_acq_cases hm
      subst d
      have hs : bstep bs1 ⟨c, .lk k⟩ = some (⟨s', bs1.bnd, bs1.bnd c⟩, some (.wait c (bs1.bnd c))) := by
        rw [hbs]; simp [lkstep, hm]
      have hb1 : bs1.bnd c = b := q1 (by rcases hown with h | ⟨h, -⟩ <;> rw [h] <;> simp)
      exact ⟨_, _, bcal_cons_of hl1 hs, fun _ => hb1, fun _ => by simp only; omega⟩
    | rel d =>
      obtain ⟨hdc, hh, hid⟩ := mstep_rel_cases hm
      subst d
      have hpos : 0 < bs1.self := by have := q2 hh; omega
      have hs : bstep bs1 ⟨c, .lk k⟩ = some (⟨s', bs1.bnd, 0⟩, some (.rel c)) := by
        rw [hbs]; simp [lkstep, hm, hpos]
      exact ⟨_, _, bcal_cons_of hl1 hs, fun hne => absurd hid (by simpa using hne), fun hh2 => by simp only at hh2; rw [hid] at hh2; cases hh2⟩

/-! ### Code shape: no memory events, `bound` never assigned, `swap(bound)` -/

def OkCall : BPrim → List Expr → Prop
  | .m .swap, args => args = [.var "bound"]
  | .mem, _ => False
  | .m _, _ => True

def Good : Stmt BPrim → Prop
  | .skip => True
  | .assign x _ => x ≠ "bound"
  | .seq a b => Good a ∧ Good b
  | .ite _ a b => Good a ∧ Good b
  | .while _ b => Good b
  | .call x p args => x ≠ "bound" ∧ OkCall p args

def GoodK : Cont BPrim → Prop
  | .stop => True
  | .seq s k => Good s ∧ GoodK k
  | .loop _ b k => Good b ∧ GoodK k

theorem step_shape {P : Prims BPrim BLog} {x x' : Config BPrim BLog} (hG : Good x.stmt) (hK : GoodK x.cont)
    (hs : step P x = some x') :
    Good x'.stmt ∧ GoodK x'.cont ∧ x'.locals "bound" = x.locals "bound" ∧
      (x'.abs = x.abs ∨ ∃ t p args v, x.stmt = .call t p args ∧ OkCall p args ∧
        P p (args.map (·.eval x.locals)) x.abs = some (v, x'.abs)) := by
  obtain ⟨stmt, cont, σ, l⟩ := x
  cases stmt with
  | skip =>
    cases cont with
    | stop => simp [step] at hs
    | seq s k => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hK.1, hK.2, rfl, .inl rfl⟩
    | loop e b k => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hK.1, hK.2, rfl, .inl rfl⟩
  | assign y e =>
    simp only [step, Option.some.injEq] at hs; subst hs
    exact ⟨trivial, hK, by simp [Locals.set, Ne.symm hG], .inl rfl⟩
  | seq a b => simp only [step, Option.some.injEq] at hs; subst hs; exact ⟨hG.1, ⟨hG.2, hK⟩, rfl, .inl rfl⟩
  | ite e a b =>
    simp only [step, Option.some.injEq] at hs; subst hs
    refine ⟨?_, hK, rfl, .inl rfl⟩
    simp only; split; exact hG.2; exact hG.1
  | «while» e b =>
    simp only [step] at hs
    split at hs <;> simp only [Option.some.injEq] at hs <;> subst hs
    · exact ⟨trivial, hK, rfl, .inl rfl⟩
    · exact ⟨hG, ⟨hG, hK⟩, rfl, .inl rfl⟩
  | call y p args =>
    simp only [step] at hs
    split at hs
    · rename_i v a' hp
      simp only [Option.some.injEq] at hs; subst hs
      exact ⟨trivial, hK, by simp [Locals.set, Ne.symm hG.1], .inr ⟨y, p, args, v, rfl, hG.2, hp⟩⟩
    · simp at hs

/-- An invariant that every step keeps, given that the final log erases to a valid one. -/
theorem run_inv {εB : BEnv} {c : CPU} (Inv : Config BPrim BLog → Prop)
    (hpres : ∀ x x', Inv x → step (bprims εB c) x = some x' → MOK (erase x'.abs) → Inv x')
    {x z : Config BPrim BLog} (h : Star (bprims εB c) x z) (hx : Inv x) (hz : MOK (erase z.abs)) : Inv z := by
  induction h with
  | refl => exact hx
  | @step a b d hs hst ih =>
    obtain ⟨ys, hys⟩ := star_ext hst
    have hb : MOK (erase b.abs) := by
      rw [hys, erase_append] at hz; exact mok_suffix _ hz
    exact ih (hpres a b hx hs hb) hz

/-- **One phase** (acquire or release): code of the right shape keeps the
invariant along the whole run. -/
theorem phase_valid {εB : BEnv} {c : CPU} (hB : BRely εB c) {bv : Val} {m : Nat} (hbm : m < bv.toNat)
    {x z : Config BPrim BLog} (h : Star (bprims εB c) x z) (hG : Good x.stmt) (hK : GoodK x.cont)
    (hbnd : x.locals "bound" = bv) (hv : ValidQ c bv.toNat m x.abs) (hz : MOK (erase z.abs)) :
    z.locals "bound" = bv ∧ ValidQ c bv.toNat m z.abs := by
  have := run_inv (εB := εB) (c := c)
    (fun y => Good y.stmt ∧ GoodK y.cont ∧ y.locals "bound" = bv ∧ ValidQ c bv.toNat m y.abs)
    (fun y y' ⟨g1, g2, g3, g4⟩ hs hok => by
      obtain ⟨g1', g2', g3', hcase⟩ := step_shape g1 g2 hs
      refine ⟨g1', g2', g3'.trans g3, ?_⟩
      rcases hcase with heq | ⟨t, p, args, v, -, hok', hp⟩
      · rw [heq]; exact g4
      · cases p with
        | mem => exact hok'.elim
        | m p =>
          cases p
          case swap =>
            simp only [OkCall] at hok'; subst hok'
            simp only [List.map, Expr.eval, g3, bprims, Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨-, hp⟩ := hp
            rw [← hp] at hok ⊢
            exact own_swap (pull_valid hB g4) hok
          all_goals
            cases args <;> simp only [List.map, bprims, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hp
            obtain ⟨-, hp⟩ := hp
            rw [← hp] at hok ⊢
            exact own_lk hbm (by decide) (pull_valid hB g4) hok)
    h ⟨hG, hK, hbnd, hv⟩ hz
  exact ⟨this.2.2.1, this.2.2.2⟩

/-! ### The critical section -/

theorem crit_validB (εB : BEnv) (c : CPU) : ∀ (n : Nat) (σ : Locals) (l : BLog) (k : Cont BPrim) {bs : BS}
    {hb : List HBEvent}, bcal l = some (bs, hb) → bs.s.ph c = .holding → n ≤ bs.self →
    ∃ σ' bs' hb', Star (bprims εB c) ⟨critB n, k, σ, l⟩ ⟨.skip, k, σ', List.replicate n ⟨c, .mem⟩ ++ l⟩ ∧
      bcal (List.replicate n ⟨c, .mem⟩ ++ l) = some (bs', hb') ∧ bs'.s = bs.s ∧ bs'.bnd = bs.bnd ∧
      bs'.self = bs.self - n ∧ σ' "bound" = σ "bound"
  | 0, σ, l, k, bs, hb, hl, _, _ => ⟨σ, bs, hb, .refl _, by simpa using hl, rfl, rfl, by simp, rfl⟩
  | n + 1, σ, l, k, bs, hb, hl, hh, hn => by
    have hs : bstep bs ⟨c, .mem⟩ = some (⟨bs.s, bs.bnd, bs.self - 1⟩, some (.mem c)) := by
      simp [bstep, hh, show 0 < bs.self by omega]
    have hl1 := bcal_cons_of hl hs
    obtain ⟨σ', bs', hb', hrun, hl', h1, h2, h3, h4⟩ :=
      crit_validB εB c n (σ.set "_" 0) (⟨c, .mem⟩ :: l) k hl1 hh (by simp only; omega)
    have hrep : List.replicate n (⟨c, .mem⟩ : BEvent) ++ ⟨c, .mem⟩ :: l = List.replicate (n + 1) ⟨c, .mem⟩ ++ l := by
      rw [List.replicate_succ']; simp
    rw [hrep] at hrun hl'
    refine ⟨σ', bs', hb', .step rfl (.step rfl (.step rfl hrun)), hl', h1, h2, by simp only at h3; omega, ?_⟩
    rw [h4]; simp [Locals.set]

theorem erase_mems (c : CPU) (n : Nat) (l : BLog) : erase (List.replicate n ⟨c, .mem⟩ ++ l) = erase l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold erase at ih ⊢
    simp only [List.replicate_succ, List.cons_append, List.filterMap_cons, eraseE]
    exact ih

/-- **The bounded per-CPU guarantee.** A client `acquire(bound); mem() × n;
release()` with `n < bound`, started idle on a valid bounded log, under a
bounded environment that keeps the log valid, finishes with a valid bounded log
(and so, by `bcal_hbreplay`, a valid `H_CalLock` log), idle again. -/
theorem clientB_guarantee {εB : BEnv} {ε : MEnv} {c : CPU} (hE : EnvErases εB ε) (hB : BRely εB c)
    (hc : c < NCPU) (hR : RelyM ε c) {l : BLog} {bs : BS} {hb : List HBEvent} (hl : bcal l = some (bs, hb))
    (hidle : bs.s.ph c = .idle) (bB : MLog → Nat) (K : Nat) (hK : ∀ l, bB l ≤ K) (hFB : FairB ε c bB)
    (bN : MLog → Nat) (hFN : FairN ε c bN) (n : Nat) (σ : Locals) (hn : n < (σ "bound").toNat) :
    ∃ σ' rb bs' hb', Star (bprims εB c) ⟨clientB n, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      bcal rb = some (bs', hb') ∧ bs'.s.ph c = .idle := by
  have hm0 := bcal_mreplay hl
  -- acquire, erased, then lifted
  obtain ⟨fuel, r1, hspec⟩ := acquireM_live hc hR hm0 hidle bB K hK hFB
  obtain ⟨σ1, hst1⟩ := acquireM_sim ε c fuel σ (erase l) r1 .stop hspec
  obtain ⟨s1, h1, hr1, hh1, -⟩ := acquireM_guarantee hc hR hm0 hidle hspec
  obtain ⟨rb1, hA, he1⟩ := lift_final hE c (s := acquireB) hst1
  have hQ0 : ValidQ c (σ "bound").toNat n l := ⟨bs, hb, hl, fun h => absurd hidle h, fun h => by rw [hidle] at h; cases h⟩
  obtain ⟨hb1, bs1, hbl1, hl1, q1, q2⟩ := phase_valid hB hn hA (by simp [erS_acquireB, Good, acquireB, OkCall, loopBB])
    trivial rfl hQ0 ⟨s1, _, by rw [he1]; exact hr1⟩
  simp only at hb1
  have hs1 : bs1.s = s1 := by
    have := bcal_mreplay hl1; rw [he1, hr1] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this; exact this.1.symm
  have hh1' : bs1.s.ph c = .holding := hs1 ▸ hh1
  -- the critical section
  obtain ⟨σ2, bs2, hb2, hC, hl2, e1, e2, e3, e4⟩ :=
    crit_validB εB c n σ1 rb1 (.seq releaseB .stop) hl1 hh1' (Nat.le_of_lt (q2 hh1'))
  -- release, erased, then lifted
  have hm2 : mreplay (erase (List.replicate n ⟨c, .mem⟩ ++ rb1)) = some (s1, .acq c :: h1) := by
    rw [erase_mems, he1]; exact hr1
  obtain ⟨fuel2, r2, hspec2⟩ := releaseM_live hc hR hm2 hh1 bN hFN
  obtain ⟨σ3, hst3⟩ := releaseM_sim ε c fuel2 σ2 _ r2 .stop hspec2
  obtain ⟨s3, h3, hr3, hid3, -⟩ := releaseM_guarantee hc hR hm2 hh1 hspec2
  obtain ⟨rb, hRr, he3⟩ := lift_final hE c (s := releaseB) hst3
  have hQ2 : ValidQ c (σ "bound").toNat 0 (List.replicate n ⟨c, .mem⟩ ++ rb1) :=
    ⟨bs2, hb2, hl2, fun h => by rw [e2]; exact q1 (e1 ▸ h),
      fun h => by have := q2 hh1'; rw [e3]; omega⟩
  obtain ⟨-, bs3, hb3, hl3, -⟩ := phase_valid hB (by omega) hRr
    (by simp [erS_releaseB, Good, releaseB, OkCall, loopNB]) trivial (by show σ2 "bound" = _; rw [e4, hb1]) hQ2
    ⟨s3, _, by rw [he3]; exact hr3⟩
  have hs3 : bs3.s = s3 := by
    have := bcal_mreplay hl3; rw [he3, hr3] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this; exact this.1.symm
  -- the whole run
  have hA' := star_app hA (.seq (.seq (critB n) releaseB) .stop) rfl
  refine ⟨σ3, rb, bs3, hb3, ?_, hl3, hs3 ▸ hid3⟩
  exact .step rfl (hA'.trans (.step rfl (.step rfl (hC.trans (.step rfl hRr)))))

end MCSBoundC
