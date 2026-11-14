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

end MCSBoundC
