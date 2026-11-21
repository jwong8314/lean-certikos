import CertiKOS.LogInv

/-!
# mC2: atomic objects

mC2's shared kernel objects (the page allocator, the shared queues, the
sleeping and pending queues, …) are **atomic objects** ([OSDI16] §3): a set of
operations, an initial state, and a log with one event per call. The object's
state at any point is the replay of its log. Each object is protected by its
own lock, and its implementation `acquire(lk); body; release(lk)` is proved to
behave as one event of the object.

* `AObj`: an object. `step c o s` is operation `o` by CPU `c` on state `s`,
  giving the new state and the result (`none` when the operation's result is
  unspecified, e.g. on a state the object's protocol rules out). `rep s b` says the lock's region `b`
  represents the state `s`.
* `AObj.replay`: the state after a history of events `(c, o)`, newest first,
  as the logs of this repository are.
* `AObj.J`: the region represents a state reached by some history. This is
  the invariant on the log (`LogInv.RelyJ`) that every CPU keeps.
* `Impl`: a body implements operation `o` for CPU `c`: on the region of a
  state `s`, inside the critical section, it ends on the region of
  `(step c o s).1` with `(step c o s).2` in the local `x`.
* `atomic_call`: **`acquire(lk); body; release(lk)` is one event.** The
  region the call finds is the replay of some history `h`. The region it
  releases is the replay of `(c, o) :: h`, and its result is what `o` returns
  on `replay h`. The linearization point is the release, and the history is
  the sequence of releases of the lock.
-/

set_option linter.unusedVariables false

namespace MC2

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA lkE apull)
open LockRegion (RLog RState HLogR rreplay REnv Region hmemR)
open LockRegionCPU KernFrame Layer LogInv

/-- **An atomic object.** -/
structure AObj where
  S : Type
  init : S
  Op : Type
  step : CPU → Op → S → S × Option Nat
  rep : S → Region → Prop

namespace AObj

/-- The state after a history of events, newest first. -/
def replay (O : AObj) : List (CPU × O.Op) → O.S
  | [] => O.init
  | (c, o) :: h => (O.step c o (O.replay h)).1

/-- What operation `o` by `c` returns after history `h`. -/
def result (O : AObj) (h : List (CPU × O.Op)) (c : CPU) (o : O.Op) : Option Nat := (O.step c o (O.replay h)).2

/-- The state is reached by some history. -/
def Hist (O : AObj) (s : O.S) : Prop := ∃ h, O.replay h = s

/-- **The invariant on the log**: the region represents a reachable state. -/
def J (O : AObj) (b : Region) : Prop := ∃ s, O.rep s b ∧ O.Hist s

end AObj

/-- **A body implements operation `o` for CPU `c`**, with its result in the
local `x`, from locals satisfying `pre`. -/
def Impl (εR : REnv) (c : CPU) (i : Nat) (O : AObj) (F : Nat → Prop) (pre : Locals → Prop) (o : O.Op)
    (x : Ident) (s : Stmt APrim) : Prop :=
  Triple εR c i O.rep F (fun σ _ => pre σ) s
    (fun _ d σ' d' => d' = (O.step c o d).1 ∧ ∀ r, (O.step c o d).2 = some r → σ' x = BitVec.ofNat 32 r)

/-- **`acquire(lk); body; release(lk)` is one event of the object.** Under the
rely that other CPUs keep the region a reachable state (`RelyJ`), and the
fairness of the lock, the call takes the lock and finds the replay of some
history `h`; it then finishes idle on a valid log, having released the replay
of `(c, o) :: h`, with the result of `o` on `replay h` in `x`. -/
theorem atomic_call {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) {O : AObj} {F : Nat → Prop} {pre : Locals → Prop} {o : O.Op}
    {x : Ident} {s : Stmt APrim} (hT : Impl εR c iv.toNat O F pre o x s) (hx : x ≠ "_")
    (hpre : ∀ σ1 : Locals, (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ1 z = σ z) → pre σ1)
    (hRJ : RelyJ εR c iv.toNat O.J) (hJ : O.J (hmemR iv.toNat H)) :
    ∃ H1 : HLogR, O.J (hmemR iv.toNat H1) ∧
      ∀ h, O.rep (O.replay h) (hmemR iv.toNat H1) →
        ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H3 : HLogR),
          Star (rprimsA εR c) ⟨.seq acquireA (.seq s relA), .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
          rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
          O.rep (O.replay ((c, o) :: h)) (hmemR iv.toNat H3) ∧ O.J (hmemR iv.toNat H3) ∧
          ∀ r, O.result h c o = some r → σ' x = BitVec.ofNat 32 r := by
  obtain ⟨σ1, r1, H1, hacq, hfr, hJ1, hrest⟩ := Triple.locked_inv hE hRR hc hRA hl hidle bound K hK hF σ hσ
    hT (I := O.Hist) (I' := O.Hist) hRJ hJ (fun σ d σ' d' hI _ hQ => by
      obtain ⟨h0, rfl⟩ := hI; exact ⟨(c, o) :: h0, by rw [hQ.1]; rfl⟩)
  refine ⟨H1, hJ1, fun h hM => ?_⟩
  obtain ⟨σ2, rb, S3, H3, d', hrun, hl3, hid, hM3, hI3, hQ⟩ := hrest (O.replay h) hM ⟨h, rfl⟩ (hpre σ1 hfr)
  refine ⟨σ2.set "_" 0, rb, S3, H3, hrun, hl3, hid, ?_, ⟨d', hM3, hI3⟩, ?_⟩
  · rw [hQ.1] at hM3; exact hM3
  · intro r hr; rw [Locals.set_other _ _ hx]; exact hQ.2 r hr

end MC2
