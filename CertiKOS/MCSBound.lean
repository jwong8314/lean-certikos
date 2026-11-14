import CertiKOS.MCSLock
import CertiKOS.TicketLive

/-!
# Bound numbers in the MCS events

In Kim et al.'s MCS-lock development (APLAS 2017, §3.1, §4.4–4.5), every client
of `mcs_acquire` promises a **bound**: the most events it will add to the log
inside its critical section. The bound has no effect on the compiled code. It is
an argument of the `SWAP_TAIL` event, and the specification says that holding
the lock longer than the bound is invalid. Waiting CPUs use the bounds of the
CPUs ahead of them to work out how long they wait.

This file adds those numbers to the MCS log of `MCSProtocol.lean`.

* `BEvent`: the MCS events, with `swap b` carrying the bound, plus `mem`, a
  shared-memory event inside the critical section (the paper's `TSHARED`).
* `bcal`: the ghost replay. It runs `mstep`, records each CPU's promised bound
  at its `swap`, and keeps the holder's remaining budget `self`. `hold` sets
  `self` to the holder's bound. Each `mem` uses one unit of budget, and a `mem`
  or a release needs at least one unit left (the paper's `S self_c'` pattern).
* `bcal_mreplay`: forgetting the bounds and the memory events gives a valid
  MCS log. So everything already proved about `mreplay` holds for bounded logs.
* `hbreplay`: the paper's bounded atomic layer `H_CalLock`, with events
  `WAIT_LOCK n`, `REL_LOCK` and memory events. `bcal_hbreplay` is R₁ with
  bounds: a valid bounded MCS log maps to a valid `H_CalLock` log with the
  same holder and the same budget.
* `crit_bound`: in an `H_CalLock` log, a CPU that took the lock with bound `n`
  emits fewer than `n` memory events before it releases.
* `waitW`: the waiting measure (the paper's `M_i`), computed from the bounds
  of the CPUs ahead of `i` in the queue. `wait_step`: no event by another CPU
  raises it, and every event other than a poll (`get_busy`, `get_next`, a
  failed `cas`) lowers it. `wait_bound`: while `i` waits, other CPUs can emit at
  most `waitW` events that are not polls. Polls leave the state unchanged, so
  only scheduler fairness is needed for them (as in `MCSLive.lean`).
-/

namespace MCSBound

open Ticket MCS TicketLive

/-! ## Bounded events and the ghost replay -/

inductive BKind
  | swap (b : Nat)
  | lk (k : MKind)
  | mem
  deriving DecidableEq

structure BEvent where
  cpu : CPU
  kind : BKind
  deriving DecidableEq

abbrev BLog := List BEvent

/-- The bounded atomic events: `WAIT_LOCK n`, `REL_LOCK`, and a shared-memory event. -/
inductive HBEvent
  | wait (c : CPU) (n : Nat)
  | rel (c : CPU)
  | mem (c : CPU)
  deriving DecidableEq

structure BS where
  s : MS
  bnd : CPU → Nat
  self : Nat

def BS.init : BS := ⟨MS.init, fun _ => 0, 0⟩

/-- An unbounded lock event (not `swap`, which must carry a bound). -/
def lkstep (bs : BS) (c : CPU) (k : MKind) : Option (BS × Option HBEvent) :=
  match mstep bs.s ⟨c, k⟩ with
  | some (s', none) => some (⟨s', bs.bnd, bs.self⟩, none)
  | some (s', some (.acq d)) => some (⟨s', bs.bnd, bs.bnd d⟩, some (.wait d (bs.bnd d)))
  | some (s', some (.rel d)) => if 0 < bs.self then some (⟨s', bs.bnd, 0⟩, some (.rel d)) else none
  | none => none

def bstep (bs : BS) (e : BEvent) : Option (BS × Option HBEvent) :=
  match e.kind with
  | .swap b =>
      match mstep bs.s ⟨e.cpu, .swap⟩ with
      | some (s', none) => some (⟨s', fset bs.bnd e.cpu b, bs.self⟩, none)
      | _ => none
  | .lk k => if k = .swap then none else lkstep bs e.cpu k
  | .mem =>
      if bs.s.ph e.cpu = .holding ∧ 0 < bs.self then
        some (⟨bs.s, bs.bnd, bs.self - 1⟩, some (.mem e.cpu))
      else none

def hcons (o : Option HBEvent) (h : List HBEvent) : List HBEvent :=
  match o with
  | none => h
  | some e => e :: h

def bcal : BLog → Option (BS × List HBEvent)
  | [] => some (BS.init, [])
  | e :: l =>
    match bcal l with
    | none => none
    | some (bs, h) =>
      match bstep bs e with
      | none => none
      | some (bs', o) => some (bs', hcons o h)

theorem bcal_cons {e : BEvent} {l : BLog} {bs' : BS} {h' : List HBEvent}
    (hr : bcal (e :: l) = some (bs', h')) :
    ∃ bs h o, bcal l = some (bs, h) ∧ bstep bs e = some (bs', o) ∧ h' = hcons o h := by
  simp only [bcal] at hr
  split at hr
  · simp at hr
  · rename_i bs h hl
    split at hr
    · simp at hr
    · rename_i bs2 o hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨bs, h, o, hl, hs, rfl⟩

theorem bcal_cons_of {e : BEvent} {l : BLog} {bs bs' : BS} {h : List HBEvent} {o : Option HBEvent}
    (hl : bcal l = some (bs, h)) (hs : bstep bs e = some (bs', o)) : bcal (e :: l) = some (bs', hcons o h) := by
  simp [bcal, hl, hs]

/-! ## Forgetting the bounds -/

def eraseE (e : BEvent) : Option MEvent :=
  match e.kind with
  | .swap _ => some ⟨e.cpu, .swap⟩
  | .lk k => some ⟨e.cpu, k⟩
  | .mem => none

def erase (l : BLog) : MLog := l.filterMap eraseE

def eraseH : HBEvent → Option HEvent
  | .wait c _ => some (.acq c)
  | .rel c => some (.rel c)
  | .mem _ => none

/-- Forgetting the bounds and the memory events gives a valid MCS log. -/
theorem bcal_mreplay : ∀ {l : BLog} {bs : BS} {hb : List HBEvent},
    bcal l = some (bs, hb) → mreplay (erase l) = some (bs.s, hb.filterMap eraseH)
  | [], bs, hb, hr => by
    simp only [bcal, Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr; rfl
  | e :: l, bs', hb', hr => by
    obtain ⟨bs, hb, o, hl, hs, rfl⟩ := bcal_cons hr
    have ih := bcal_mreplay hl
    obtain ⟨c, k⟩ := e
    cases k with
    | swap b =>
      simp only [bstep] at hs
      split at hs
      · rename_i s' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        simp only [erase, List.filterMap_cons, eraseE] at ih ⊢
        exact mreplay_cons_of ih hm
      · simp at hs
    | lk k =>
      have hk : k ≠ .swap := by rintro rfl; simp [bstep] at hs
      simp only [bstep, hk, ite_false, lkstep] at hs
      · split at hs
        · rename_i s' hm
          simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
          simp only [erase, List.filterMap_cons, eraseE] at ih ⊢
          exact mreplay_cons_of ih hm
        · rename_i s' d hm
          simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
          simp only [erase, List.filterMap_cons, eraseE] at ih ⊢
          simpa [hcons, eraseH, consOpt] using mreplay_cons_of ih hm
        · rename_i s' d hm
          split at hs
          · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
            simp only [erase, List.filterMap_cons, eraseE] at ih ⊢
            simpa [hcons, eraseH, consOpt] using mreplay_cons_of ih hm
          · simp at hs
        · simp at hs
    | mem =>
      simp only [bstep] at hs
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        exact (show mreplay (erase l) = some (bs.s, hb.filterMap eraseH) from ih)
      · simp at hs

theorem bcal_inv {l : BLog} {bs : BS} {hb : List HBEvent} (hr : bcal l = some (bs, hb)) : MInv bs.s :=
  mreplay_inv (bcal_mreplay hr)

/-! ## The bounded atomic layer (`H_CalLock`) -/

/-- One step of `H_CalLock`: the state is the holder's remaining budget and the holder. -/
def hbstep : Nat × Option CPU → HBEvent → Option (Nat × Option CPU)
  | (_, none), .wait c n => some (n, some c)
  | (k + 1, some h), .mem c => if c = h then some (k, some h) else none
  | (_ + 1, some h), .rel c => if c = h then some (0, none) else none
  | _, _ => none

def hbreplay : List HBEvent → Option (Nat × Option CPU)
  | [] => some (0, none)
  | e :: h =>
    match hbreplay h with
    | none => none
    | some st => hbstep st e

theorem hbreplay_cons {e : HBEvent} {h : List HBEvent} {st' : Nat × Option CPU}
    (hr : hbreplay (e :: h) = some st') : ∃ st, hbreplay h = some st ∧ hbstep st e = some st' := by
  simp only [hbreplay] at hr
  split at hr
  · simp at hr
  · exact ⟨_, ‹_›, hr⟩

theorem hcons_hb {o : Option HBEvent} {h : List HBEvent} {st st' : Nat × Option CPU}
    (hh : hbreplay h = some st) (hs : ∀ e, o = some e → hbstep st e = some st') (hn : o = none → st' = st) :
    hbreplay (hcons o h) = some st' := by
  cases o with
  | none => simp only [hcons]; rw [hh, hn rfl]
  | some e => simp only [hcons, hbreplay, hh]; exact hs e rfl

/-- **R₁ with bounds**: a valid bounded MCS log maps to a valid `H_CalLock` log,
with the protocol's holder and the ghost budget. -/
theorem bcal_hbreplay : ∀ {l : BLog} {bs : BS} {hb : List HBEvent},
    bcal l = some (bs, hb) → ∃ o, hbreplay hb = some (bs.self, o) ∧ HoldsM bs.s o
  | [], bs, hb, hr => by
    simp only [bcal, Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    exact ⟨none, rfl, fun d => by simp [BS.init, MS.init]⟩
  | e :: l, bs', hb', hr => by
    obtain ⟨bs, hb, o, hl, hs, rfl⟩ := bcal_cons hr
    obtain ⟨o0, ho0, hH⟩ := bcal_hbreplay hl
    -- the new MCS state's holder, from `mreplay_hreplay`
    have hm' := bcal_mreplay hr
    obtain ⟨o', hro', hH'⟩ := mreplay_hreplay hm'
    have hm := bcal_mreplay hl
    obtain ⟨o1, hro1, hH1⟩ := mreplay_hreplay hm
    -- holders are determined by the state
    have huniq : ∀ {s : MS} {a b : Option CPU}, HoldsM s a → HoldsM s b → a = b := by
      intro s a b ha hb
      cases a with
      | none => cases b with
        | none => rfl
        | some d => exact absurd ((hb d).2 rfl) (fun h => by simpa using (ha d).1 h)
      | some d => exact ((hb d).1 ((ha d).2 rfl)).symm
    have h01 : o0 = o1 := huniq hH hH1
    subst h01
    obtain ⟨c, k⟩ := e
    cases k with
    | swap b =>
      simp only [bstep] at hs
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        refine ⟨o', hcons_hb ho0 (fun e he => by cases he) (fun _ => ?_), hH'⟩
        -- the atomic log did not grow
        have : (hcons none hb).filterMap eraseH = hb.filterMap eraseH := rfl
        rw [this, hro1] at hro'; cases hro'; rfl
      · simp at hs
    | lk k =>
      have hk : k ≠ .swap := by rintro rfl; simp [bstep] at hs
      simp only [bstep, hk, ite_false, lkstep] at hs
      · split at hs
        · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
          refine ⟨o', hcons_hb ho0 (fun e he => by cases he) (fun _ => ?_), hH'⟩
          have : (hcons none hb).filterMap eraseH = hb.filterMap eraseH := rfl
          rw [this, hro1] at hro'; cases hro'; rfl
        · rename_i s' d hmst
          simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
          have : (hcons (some (.wait d (bs.bnd d))) hb).filterMap eraseH = .acq d :: hb.filterMap eraseH := by
            simp [hcons, eraseH]
          rw [this] at hro'
          simp only [hreplay, hro1] at hro'
          cases ho : o0 with
          | some x => rw [ho] at hro'; simp [hstep] at hro'
          | none =>
            rw [ho] at hro'; simp only [hstep, Option.some.injEq] at hro'; subst hro'
            refine ⟨some d, ?_, hH'⟩
            simp only [hcons, hbreplay, ho0, ho, hbstep]
        · rename_i s' d hmst
          split at hs
          · rename_i hpos
            simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
            have : (hcons (some (.rel d)) hb).filterMap eraseH = .rel d :: hb.filterMap eraseH := by
              simp [hcons, eraseH]
            rw [this] at hro'
            simp only [hreplay, hro1] at hro'
            cases ho : o0 with
            | none => rw [ho] at hro'; simp [hstep] at hro'
            | some x =>
              rw [ho] at hro'; simp only [hstep] at hro'
              split at hro'
              · rename_i hxd; subst hxd
                simp only [Option.some.injEq] at hro'; subst hro'
                refine ⟨none, ?_, hH'⟩
                obtain ⟨k, hk⟩ : ∃ k, bs.self = k + 1 := ⟨bs.self - 1, by omega⟩
                simp only [hcons, hbreplay, ho0, ho, hk, hbstep, ite_true]
              · simp at hro'
          · simp at hs
        · simp at hs
    | mem =>
      simp only [bstep] at hs
      split at hs
      · rename_i hc
        obtain ⟨hh, hpos⟩ := hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        have ho : o0 = some c := (hH c).1 hh
        refine ⟨some c, ?_, by rw [← ho]; exact hH⟩
        obtain ⟨k, hk⟩ : ∃ k, bs.self = k + 1 := ⟨bs.self - 1, by omega⟩
        simp only [hcons, hbreplay, ho0, ho, hk, hbstep, ite_true]
        simp
      · simp at hs

/-! ## The critical section respects its bound -/

def memCount : List HBEvent → Nat
  | [] => 0
  | .mem _ :: h => memCount h + 1
  | _ :: h => memCount h

def IsWait : HBEvent → Prop
  | .wait _ _ => True
  | _ => False

/-- **Critical sections respect their bound.** After `c` takes the lock with
bound `n`, and before anyone takes it again: either `c` still holds it and has
used `memCount ys` of its `n` units, or `c` has released it after fewer than
`n` memory events. -/
theorem crit_bound {c : CPU} {n : Nat} {h : List HBEvent} :
    ∀ (ys : List HBEvent) {k : Nat} {o : Option CPU}, (∀ e ∈ ys, ¬ IsWait e) →
      hbreplay (ys ++ .wait c n :: h) = some (k, o) →
      (o = some c ∧ memCount ys + k = n) ∨ (o = none ∧ k = 0 ∧ memCount ys < n)
  | [], k, o, _, hr => by
    obtain ⟨st, -, hs⟩ := hbreplay_cons hr
    obtain ⟨k0, o0⟩ := st
    cases o0 with
    | none => simp only [hbstep, Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
              exact .inl ⟨rfl, by simp [memCount]⟩
    | some x => simp [hbstep] at hs
  | e :: ys, k, o, hw, hr => by
    obtain ⟨⟨k0, o0⟩, hr0, hs⟩ := hbreplay_cons hr
    have ih := crit_bound ys (fun e he => hw e (List.mem_cons_of_mem _ he)) hr0
    have hwe := hw e List.mem_cons_self
    cases e with
    | wait d m => exact absurd trivial hwe
    | mem d =>
      cases o0 with
      | none => cases k0 <;> simp [hbstep] at hs
      | some x =>
        cases k0 with
        | zero => simp [hbstep] at hs
        | succ k1 =>
          simp only [hbstep] at hs
          split at hs
          · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
            rcases ih with ⟨h1, h2⟩ | ⟨h1, -⟩
            · exact .inl ⟨h1, by simp only [memCount]; omega⟩
            · cases h1
          · simp at hs
    | rel d =>
      cases o0 with
      | none => cases k0 <;> simp [hbstep] at hs
      | some x =>
        cases k0 with
        | zero => simp [hbstep] at hs
        | succ k1 =>
          simp only [hbstep] at hs
          split at hs
          · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
            rcases ih with ⟨h1, h2⟩ | ⟨h1, -⟩
            · exact .inr ⟨rfl, rfl, by simp only [memCount]; omega⟩
            · cases h1
          · simp at hs

/-! ## How an MCS step changes the state of the CPU that takes it -/

theorem mstep_acq_cases {s s' : MS} {j d : CPU} {k : MKind} (hm : mstep s ⟨j, k⟩ = some (s', some (.acq d))) :
    d = j ∧ (s.ph j = .front ∨ (s.ph j = .waiting ∧ s.busy j = false)) ∧ s'.ph j = .holding ∧
      s'.pos = s.pos := by
  simp only [mstep] at hm
  split at hm
  case isFalse => simp at hm
  cases k <;> cases hph : s.ph j <;> simp only [hph] at hm <;> try simp at hm
  · obtain ⟨rfl, rfl⟩ := hm; exact ⟨rfl, .inl rfl, by simp, rfl⟩
  · obtain ⟨hb, rfl, rfl⟩ := hm; exact ⟨rfl, .inr ⟨rfl, hb⟩, by simp, rfl⟩
  · split at hm <;> simp at hm
  · split at hm <;> simp at hm

theorem mstep_rel_cases {s s' : MS} {j d : CPU} {k : MKind} (hm : mstep s ⟨j, k⟩ = some (s', some (.rel d))) :
    d = j ∧ s.ph j = .holding ∧ s'.ph j = .idle := by
  simp only [mstep] at hm
  split at hm
  case isFalse => simp at hm
  cases k <;> cases hph : s.ph j <;> simp only [hph] at hm <;> try simp at hm
  · split at hm
    · simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, h⟩ := hm
      simp only [HEvent.rel.injEq] at h; subst h; exact ⟨rfl, rfl, by simp⟩
    · simp at hm
  · split at hm
    · simp only [Option.some.injEq, Prod.mk.injEq] at hm; obtain ⟨rfl, h⟩ := hm
      simp only [HEvent.rel.injEq] at h; subst h; exact ⟨rfl, rfl, by simp⟩
    · simp at hm

/-- The polls: `get_busy`, `get_next` and `cas`. -/
def isPoll : BKind → Bool
  | .lk .getBusy | .lk .getNext | .lk .cas => true
  | _ => false

theorem mstep_none_cases {s s' : MS} {j : CPU} {k : MKind} (hk : k ≠ .swap)
    (hm : mstep s ⟨j, k⟩ = some (s', none)) :
    (s' = s ∧ isPoll (.lk k) = true) ∨
      (k = .link ∧ (∃ p, s.ph j = .linking p) ∧ s'.ph j = .waiting ∧ s'.pos = s.pos) := by
  simp only [mstep] at hm
  split at hm
  case isFalse => simp at hm
  cases k <;> cases hph : s.ph j <;> simp only [hph] at hm <;> try simp at hm
  all_goals first
    | exact absurd rfl hk
    | (subst hm; exact .inl ⟨rfl, rfl⟩)
    | (obtain ⟨rfl, -⟩ := hm; exact .inl ⟨rfl, rfl⟩)
    | (rename_i p; obtain ⟨rfl, -⟩ := hm; exact .inr ⟨rfl, ⟨p, rfl⟩, by simp, rfl⟩)
    | (by_cases htl : s.tl = s.hd + 1 <;> simp [htl] at hm <;> (subst hm; exact .inl ⟨rfl, rfl⟩))
    | (split at hm <;> simp at hm)

/-! ## The waiting measure -/

/-- `d` is ahead of `i` in the queue. -/
def ahead (s : MS) (i d : CPU) : Bool :=
  match s.pos d, s.pos i with
  | some a, some b => decide (a < b)
  | _, _ => false

/-- How many more non-poll events `d` can emit before `i` gets the lock: an
idle CPU can swap in and link behind `i`; a CPU ahead of `i` can link, take the
lock, use its bound, release, and then swap in and link again. -/
def cost (bs : BS) (i d : CPU) : Nat :=
  match bs.s.ph d with
  | .idle => 2
  | .linking _ => if ahead bs.s i d then bs.bnd d + 5 else 1
  | .front => if ahead bs.s i d then bs.bnd d + 4 else 0
  | .waiting => if ahead bs.s i d then bs.bnd d + 4 else 0
  | .holding => bs.self + 3

/-- **The waiting measure** of `i` (the paper's `M_i`), computed from the bound
numbers of the CPUs ahead of `i`. -/
def waitW (bs : BS) (i : CPU) : Nat := sumTo (fun d => if d = i then 0 else cost bs i d) NCPU

/-- `i` is in the queue, waiting for the lock. -/
def Queued (s : MS) (i : CPU) : Prop := s.ph i ≠ .idle ∧ s.ph i ≠ .holding

theorem cost_frame {bs bs' : BS} {i d : CPU} (hph : bs'.s.ph d = bs.s.ph d) (hpd : bs'.s.pos d = bs.s.pos d)
    (hpi : bs'.s.pos i = bs.s.pos i) (hb : bs'.bnd d = bs.bnd d)
    (hself : bs.s.ph d = .holding → bs'.self = bs.self) : cost bs' i d = cost bs i d := by
  unfold cost ahead
  rw [hph, hpd, hpi, hb]
  cases h : bs.s.ph d <;> simp only [h] at hself ⊢ <;> simp_all

theorem combine {bs bs' : BS} {i j : CPU} (hj : j < NCPU) (hji : j ≠ i)
    (hA : ∀ d, d ≠ j → d ≠ i → cost bs' i d = cost bs i d) (hB : cost bs' i j ≤ cost bs i j) :
    waitW bs' i ≤ waitW bs i ∧ (cost bs' i j < cost bs i j → waitW bs' i < waitW bs i) := by
  have hle : ∀ d, d < NCPU → (fun d => if d = i then 0 else cost bs' i d) d ≤
      (fun d => if d = i then 0 else cost bs i d) d := fun d _ => by
    by_cases hdi : d = i
    · simp [hdi]
    · by_cases hdj : d = j
      · subst hdj; simp [hdi, hB]
      · simp [hdi, hA d hdj hdi]
  refine ⟨sumTo_le NCPU hle, fun hlt => sumTo_lt (i := j) NCPU hle hj ?_⟩
  simp [hji, hlt]

/-- **The waiting measure never grows under other CPUs' events, and every
event that is not a poll lowers it.** -/
theorem wait_step {bs bs' : BS} {e : BEvent} {o : Option HBEvent} {i : CPU} (hi : MInv bs.s)
    (hq : Queued bs.s i) (hne : e.cpu ≠ i) (hs : bstep bs e = some (bs', o)) :
    bs'.s.ph i = bs.s.ph i ∧ waitW bs' i ≤ waitW bs i ∧ (isPoll e.kind = false → waitW bs' i < waitW bs i) := by
  obtain ⟨j, k⟩ := e
  simp only at hne
  obtain ⟨n, hn⟩ := (hi.inq i).1 hq.1
  obtain ⟨hn1, hn2⟩ := hi.bnd i n hn
  have hj : j < NCPU := Classical.byContradiction fun hj => by
    cases k with
    | mem =>
      simp only [bstep] at hs
      split at hs
      · rename_i h; exact hj (Nat.lt_of_not_le fun hge => by rw [(hi.range j hge).1] at h; cases h.1)
      · simp at hs
    | swap b => simp [bstep, mstep, hj] at hs
    | lk k => simp [bstep, lkstep, mstep, hj] at hs
  -- the head of the queue is ahead of `i`
  have headAhead : ∀ d, d ≠ i → bs.s.pos d = some bs.s.hd → ahead bs.s i d = true := fun d hd hp => by
    have : n ≠ bs.s.hd := fun h => hd (hi.inj d i _ hp (h ▸ hn))
    simp only [ahead, hp, hn, decide_eq_true_eq]; omega
  cases k with
  | mem =>
    simp only [bstep] at hs
    split at hs
    · rename_i h
      obtain ⟨hh, hpos⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      refine ⟨rfl, ?_⟩
      have hc := combine (bs := bs) (bs' := ⟨bs.s, bs.bnd, bs.self - 1⟩) hj hne
        (fun d hdj _ => cost_frame rfl rfl rfl rfl fun h => absurd (hi.mutex h hh) hdj)
        (by dsimp only [cost]; simp only [hh]; omega)
      exact ⟨hc.1, fun _ => hc.2 (by dsimp only [cost]; simp only [hh]; omega)⟩
    · simp at hs
  | swap b =>
    simp only [bstep] at hs
    split at hs
    · rename_i s' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hph', hpos', -⟩ := mstep_other hi hm hne
      -- unfold the swap: `j` was idle and joins behind the tail
      have hm2 := hm
      simp only [mstep, hj, ite_true] at hm2
      cases hpj : bs.s.ph j <;> simp only [hpj] at hm2 <;> try simp at hm2
      obtain ⟨rfl, -⟩ := hm2
      obtain ⟨p, hp, -⟩ := whoAt_some hi (n := bs.s.tl - 1) (by omega) (by omega)
      have ht : tailOf bs.s = some p := by simp [tailOf, hp, show bs.s.hd < bs.s.tl by omega]
      refine ⟨by simpa using hph', ?_⟩
      have hji : i ≠ j := Ne.symm hne
      have hc := combine (bs := bs) (bs' := ⟨(⟨bs.s.hd, bs.s.tl + 1, fset bs.s.pos j (some bs.s.tl), fset bs.s.busy j true, fset bs.s.next j none, fset bs.s.ph j (match tailOf bs.s with | none => .front | some p => .linking p)⟩ : MS), fset bs.bnd j b, bs.self⟩) hj hne
        (fun d hdj _ => cost_frame (by simp [fset_other _ _ hdj]) (by simp [fset_other _ _ hdj])
          (by simp [fset_other _ _ hji]) (by simp [fset_other _ _ hdj]) fun _ => rfl)
        (by dsimp only [cost, ahead]; simp only [hpj, fset_same, ht, fset_other _ _ hji, hn]; simp [show ¬ bs.s.tl < n by omega])
      refine ⟨hc.1, fun _ => hc.2 ?_⟩
      dsimp only [cost, ahead]; simp only [hpj, fset_same, ht, fset_other _ _ hji, hn]
      simp [show ¬ bs.s.tl < n by omega]
    · simp at hs
  | lk k =>
    have hk : k ≠ .swap := by rintro rfl; simp [bstep] at hs
    simp only [bstep, hk, ite_false, lkstep] at hs
    split at hs
    · rename_i s' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hph', hpos', -⟩ := mstep_other hi hm hne
      refine ⟨hph', ?_⟩
      rcases mstep_none_cases hk hm with ⟨rfl, hpoll⟩ | ⟨rfl, ⟨p, hp⟩, hw, hpe⟩
      · exact ⟨Nat.le_refl _, fun h => by simp [hpoll] at h⟩
      · have hah : ahead s' i j = ahead bs.s i j := by simp [ahead, hpe]
        have hc := combine (bs := bs) (bs' := ⟨s', bs.bnd, bs.self⟩) hj hne
          (fun d hdj _ => by
            obtain ⟨h1, h2, -⟩ := mstep_other hi hm (Ne.symm hdj)
            exact cost_frame h1 h2 hpos' rfl fun _ => rfl)
          (by dsimp only [cost]; simp only [hp, hw, hah]; cases ahead bs.s i j <;> simp)
        refine ⟨hc.1, fun _ => hc.2 ?_⟩
        dsimp only [cost]; simp only [hp, hw, hah]; cases ahead bs.s i j <;> simp
    · rename_i s' d hm
      simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
      obtain ⟨hph', hpos', -⟩ := mstep_other hi hm hne
      obtain ⟨rfl, hown, hh', hpe⟩ := mstep_acq_cases hm
      have hpj := hi.owner_head (by rcases hown with h | h; exact .inl h; exact .inr (.inr h))
      have hah := headAhead d hne hpj
      refine ⟨hph', ?_⟩
      have hB : cost ⟨s', bs.bnd, bs.bnd d⟩ i d < cost bs i d := by
        dsimp only [cost]; simp only [hh']
        rcases hown with h | ⟨h, -⟩ <;> simp only [h, hah, ite_true] <;> omega
      have hc := combine (bs := bs) (bs' := ⟨s', bs.bnd, bs.bnd d⟩) hj hne
        (fun d' hdj _ => by
          obtain ⟨h1, h2, -⟩ := mstep_other hi hm (Ne.symm hdj)
          refine cost_frame h1 h2 hpos' rfl fun hh => ?_
          exact absurd (hi.inj d' d _ (hi.owner_head (.inr (.inl hh))) hpj) hdj)
        (Nat.le_of_lt hB)
      exact ⟨hc.1, fun _ => hc.2 hB⟩
    · rename_i s' d hm
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨hph', hpos', -⟩ := mstep_other hi hm hne
        obtain ⟨rfl, hh, hid⟩ := mstep_rel_cases hm
        refine ⟨hph', ?_⟩
        have hB : cost ⟨s', bs.bnd, 0⟩ i d < cost bs i d := by dsimp only [cost]; simp only [hh, hid]; omega
        have hc := combine (bs := bs) (bs' := ⟨s', bs.bnd, 0⟩) hj hne
          (fun d' hdj _ => by
            obtain ⟨h1, h2, -⟩ := mstep_other hi hm (Ne.symm hdj)
            exact cost_frame h1 h2 hpos' rfl fun h => absurd (hi.mutex h hh) hdj)
          (Nat.le_of_lt hB)
        exact ⟨hc.1, fun _ => hc.2 hB⟩
      · simp at hs
    · simp at hs

/-- The events that are not polls. -/
def nonPolls : BLog → Nat
  | [] => 0
  | e :: l => nonPolls l + (if isPoll e.kind then 0 else 1)

/-- **Bounded waiting.** While `i` waits in the queue, the other CPUs emit at
most `waitW` events that are not polls: the bound numbers of the CPUs ahead of
`i` bound how long `i` waits. -/
theorem wait_bound {i : CPU} :
    ∀ (xs : BLog) {l : BLog} {bs bs' : BS} {hb hb' : List HBEvent},
      (∀ e ∈ xs, e.cpu ≠ i) → bcal l = some (bs, hb) → bcal (xs ++ l) = some (bs', hb') →
      Queued bs.s i → bs'.s.ph i = bs.s.ph i ∧ nonPolls xs + waitW bs' i ≤ waitW bs i
  | [], l, bs, bs', hb, hb', _, hl, hr, _ => by
    simp only [List.nil_append] at hr; rw [hl] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, -⟩ := hr
    exact ⟨rfl, by simp [nonPolls]⟩
  | e :: xs, l, bs, bs', hb, hb', hx, hl, hr, hq => by
    obtain ⟨bs2, hb2, o, hl2, hs, -⟩ := bcal_cons hr
    obtain ⟨hph2, hw2⟩ := wait_bound xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2 hq
    have hq2 : Queued bs2.s i := by unfold Queued; rw [hph2]; exact hq
    obtain ⟨hph', hle, hlt⟩ := wait_step (bcal_inv hl2) hq2 (hx e List.mem_cons_self) hs
    refine ⟨by rw [hph', hph2], ?_⟩
    simp only [nonPolls]
    cases hp : isPoll e.kind
    · have := hlt hp; simp; omega
    · simp; omega

/-! ## The wait, in terms of the bounds alone -/

theorem mstep_swap_ph {s s' : MS} {j : CPU} {o : Option HEvent} (hm : mstep s ⟨j, .swap⟩ = some (s', o)) :
    s'.ph j ≠ .holding := by
  simp only [mstep] at hm
  split at hm
  case isFalse => simp at hm
  cases hph : s.ph j <;> simp only [hph] at hm <;> try simp at hm
  obtain ⟨rfl, -⟩ := hm
  cases tailOf s <;> simp

/-- The holder never has more budget left than it promised. -/
theorem bcal_self : ∀ {l : BLog} {bs : BS} {hb : List HBEvent},
    bcal l = some (bs, hb) → ∀ d, bs.s.ph d = .holding → bs.self ≤ bs.bnd d
  | [], bs, hb, hr, d, hd => by
    simp only [bcal, Option.some.injEq, Prod.mk.injEq] at hr; obtain ⟨rfl, rfl⟩ := hr
    simp [BS.init] at hd ⊢
  | e :: l, bs', hb', hr, d, hd => by
    obtain ⟨bs, hb, o, hl, hs, -⟩ := bcal_cons hr
    have ih := bcal_self hl
    have hi := bcal_inv hl
    have hi' := bcal_inv hr
    obtain ⟨j, k⟩ := e
    cases k with
    | mem =>
      simp only [bstep] at hs
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        have := ih d hd; simp only at this ⊢; omega
      · simp at hs
    | swap b =>
      simp only [bstep] at hs
      split at hs
      · rename_i s' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        have hdj : j ≠ d := fun h => mstep_swap_ph hm (h ▸ hd)
        have hph := (mstep_other hi hm hdj).1
        simp only at hd ⊢
        rw [fset_other _ _ (Ne.symm hdj)]
        exact ih d (hph ▸ hd)
      · simp at hs
    | lk k =>
      have hk : k ≠ .swap := by rintro rfl; simp [bstep] at hs
      simp only [bstep, hk, ite_false, lkstep] at hs
      split at hs
      · rename_i s' hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        simp only at hd ⊢
        by_cases hdj : j = d
        · subst hdj
          rcases mstep_none_cases hk hm with ⟨rfl, -⟩ | ⟨-, -, hw, -⟩
          · exact ih j hd
          · rw [hw] at hd; cases hd
        · exact ih d ((mstep_other hi hm hdj).1 ▸ hd)
      · rename_i s' c hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨rfl, -, hh, -⟩ := mstep_acq_cases hm
        simp only at hd hi' ⊢
        rw [hi'.mutex hd hh]; exact Nat.le_refl _
      · split at hs
        · simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
          exact Nat.zero_le _
        · simp at hs
      · simp at hs

theorem cost_le {l : BLog} {bs : BS} {hb : List HBEvent} (hr : bcal l = some (bs, hb)) (i d : CPU) :
    cost bs i d ≤ bs.bnd d + 5 := by
  unfold cost
  cases h : bs.s.ph d <;> (try simp only)
  · omega
  · split <;> omega
  · split <;> omega
  · split <;> omega
  · have := bcal_self hr d h; omega

/-- The waiting measure is at most the sum, over all CPUs, of the bound plus 5. -/
theorem waitW_le {l : BLog} {bs : BS} {hb : List HBEvent} (hr : bcal l = some (bs, hb)) (i : CPU) :
    waitW bs i ≤ sumTo (fun d => bs.bnd d + 5) NCPU :=
  sumTo_le NCPU fun d _ => by
    by_cases hdi : d = i
    · simp [hdi]
    · simp only [hdi, ite_false]; exact cost_le hr i d

/-- **Bounded waiting, in numbers.** If every promised bound is at most `B`,
then while `i` waits the other CPUs emit at most `NCPU * (B + 5)` events that
are not polls. -/
theorem wait_bound_B {i : CPU} {B : Nat} (xs : BLog) {l : BLog} {bs bs' : BS} {hb hb' : List HBEvent}
    (hx : ∀ e ∈ xs, e.cpu ≠ i) (hl : bcal l = some (bs, hb)) (hr : bcal (xs ++ l) = some (bs', hb'))
    (hq : Queued bs.s i) (hB : ∀ d, bs.bnd d ≤ B) : nonPolls xs ≤ NCPU * (B + 5) := by
  obtain ⟨-, hw⟩ := wait_bound xs hx hl hr hq
  have h1 := waitW_le hl i
  have h2 : sumTo (fun d => bs.bnd d + 5) NCPU ≤ sumTo (fun _ => B + 5) NCPU :=
    sumTo_le NCPU fun d _ => by have := hB d; omega
  rw [sumTo_const] at h2
  omega

/-! ## Example -/

/-- CPU 0 promises bound 2, takes the lock, makes one memory event, and
releases by `cas`. Newest event first. -/
def demoOk : BLog :=
  [⟨0, .lk .cas⟩, ⟨0, .mem⟩, ⟨0, .lk .hold⟩, ⟨0, .swap 2⟩]

/-- Same, but with bound 1: the release finds no budget left, so the log is invalid. -/
def demoOver : BLog :=
  [⟨0, .lk .cas⟩, ⟨0, .mem⟩, ⟨0, .lk .hold⟩, ⟨0, .swap 1⟩]

example : (bcal demoOk).map (·.2) = some [.rel 0, .mem 0, .wait 0 2] := by decide
example : (bcal demoOver).isSome = false := by decide

end MCSBound
