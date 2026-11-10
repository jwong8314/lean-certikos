import CertiKOS.FairEnv

/-!
# The MCS lock: shared log and protocol

The MCS queue lock ([OSDI16], Kim et al. 2017), with the same atomic interface
as the ticket lock. Each CPU `c` owns a queue node with fields `busy[c]` and
`next[c]`. A global `tail` points to the last node.

```
acquire:  busy[c] = 1; next[c] = 0; p = SWAP(tail, c);       // swap
          if (p != 0) { next[p] = c;                           // link
                        while (busy[c]) {} }                   // get_busy
          hold();                                               // linearization point
release:  n = next[c];                                          // get_next
          if (n == 0) { if (CAS(tail, c, 0)) return;            // cas
                        while ((n = next[c]) == 0) {} }
          busy[n] = 0;                                          // handoff
```
The two writes to our own node before the `SWAP` are folded into the `swap`
event: nobody can see our node until the swap publishes it.

**Ghost positions.** Proofs about the MCS queue usually reason about a linked
list. Here every CPU that swaps gets the next position `tl`. The queue is the
CPUs with positions in `[hd, tl)`, and a CPU's predecessor is the CPU at the
position before its own. The real `tail` is the CPU at `tl − 1`. A release
moves `hd` on by one. With this, the invariant (`MInv`) is arithmetic, as for
the ticket lock.

* `mutexM`: at most one CPU holds the lock.
* `mreplay_hreplay`: the high-level log (`acq c` at `hold`, `rel c` at a
  successful `cas` or at `handoff`) is a valid atomic-lock log, and its holder
  is the protocol's. This is CCAL's R₁ for MCS, onto the *same* atomic layer
  as the ticket lock (`AtomicLayer.lean`).
-/

namespace MCS

open Ticket

inductive MKind
  | swap | link | getBusy | hold | getNext | cas | handoff
  deriving DecidableEq

structure MEvent where
  cpu : CPU
  kind : MKind
  deriving DecidableEq

abbrev MLog := List MEvent

inductive MPh
  | idle | front | linking (p : CPU) | waiting | holding
  deriving DecidableEq

structure MS where
  hd : Nat
  tl : Nat
  pos : CPU → Option Nat
  busy : CPU → Bool
  next : CPU → Option CPU
  ph : CPU → MPh

def fset {α : Type} (f : CPU → α) (c : CPU) (a : α) : CPU → α := fun d => if d = c then a else f d

@[simp] theorem fset_same {α : Type} (f : CPU → α) (c : CPU) (a : α) : fset f c a c = a := by simp [fset]
theorem fset_other {α : Type} (f : CPU → α) {c d : CPU} (a : α) (h : d ≠ c) : fset f c a d = f d := by
  simp [fset, h]

def MS.init : MS := ⟨0, 0, fun _ => none, fun _ => false, fun _ => none, fun _ => .idle⟩

/-- The CPU at queue position `n`. -/
def whoAt (s : MS) (n : Nat) : Option CPU := findCPU (fun d => s.pos d == some n) NCPU

/-- The predecessor a CPU gets by swapping now: the current tail. -/
def tailOf (s : MS) : Option CPU := if s.hd < s.tl then whoAt s (s.tl - 1) else none

def mstep (s : MS) (e : MEvent) : Option (MS × Option HEvent) :=
  if e.cpu < NCPU then
    match e.kind, s.ph e.cpu with
    | .swap, .idle =>
        some (⟨s.hd, s.tl + 1, fset s.pos e.cpu (some s.tl), fset s.busy e.cpu true,
          fset s.next e.cpu none,
          fset s.ph e.cpu (match tailOf s with | none => .front | some p => .linking p)⟩, none)
    | .link, .linking p =>
        some (⟨s.hd, s.tl, s.pos, s.busy, fset s.next p (some e.cpu), fset s.ph e.cpu .waiting⟩, none)
    | .getBusy, .waiting => some (s, none)
    | .hold, .front => some (⟨s.hd, s.tl, s.pos, s.busy, s.next, fset s.ph e.cpu .holding⟩, some (.acq e.cpu))
    | .hold, .waiting =>
        if s.busy e.cpu = false then
          some (⟨s.hd, s.tl, s.pos, s.busy, s.next, fset s.ph e.cpu .holding⟩, some (.acq e.cpu))
        else none
    | .getNext, .holding => some (s, none)
    | .cas, .holding =>
        if s.tl = s.hd + 1 then
          some (⟨s.hd + 1, s.tl, fset s.pos e.cpu none, s.busy, s.next, fset s.ph e.cpu .idle⟩,
            some (.rel e.cpu))
        else some (s, none)
    | .handoff, .holding =>
        match s.next e.cpu with
        | some d =>
            some (⟨s.hd + 1, s.tl, fset s.pos e.cpu none, fset s.busy d false, s.next,
              fset s.ph e.cpu .idle⟩, some (.rel e.cpu))
        | none => none
    | _, _ => none
  else none

def mreplay : MLog → Option (MS × List HEvent)
  | [] => some (MS.init, [])
  | e :: l =>
    match mreplay l with
    | none => none
    | some (s, h) =>
      match mstep s e with
      | none => none
      | some (s', o) => some (s', consOpt o h)

theorem mreplay_cons {e : MEvent} {l : MLog} {s' : MS} {h' : List HEvent}
    (hr : mreplay (e :: l) = some (s', h')) :
    ∃ s h o, mreplay l = some (s, h) ∧ mstep s e = some (s', o) ∧ h' = consOpt o h := by
  simp only [mreplay] at hr
  split at hr
  · simp at hr
  · rename_i s h hl
    split at hr
    · simp at hr
    · rename_i s2 o hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨s, h, o, hl, hp, rfl⟩

theorem mreplay_cons_of {e : MEvent} {l : MLog} {s s' : MS} {h : List HEvent} {o : Option HEvent}
    (hl : mreplay l = some (s, h)) (hp : mstep s e = some (s', o)) :
    mreplay (e :: l) = some (s', consOpt o h) := by
  simp [mreplay, hl, hp]

/-! ## The invariant -/

def InQ (p : MPh) : Prop := p ≠ .idle

structure MInv (s : MS) : Prop where
  le : s.hd ≤ s.tl
  range : ∀ c, NCPU ≤ c → s.ph c = .idle ∧ s.pos c = none
  inq : ∀ c, s.ph c ≠ .idle ↔ ∃ n, s.pos c = some n
  bnd : ∀ c n, s.pos c = some n → s.hd ≤ n ∧ n < s.tl
  inj : ∀ c d n, s.pos c = some n → s.pos d = some n → c = d
  cover : ∀ n, s.hd ≤ n → n < s.tl → ∃ c, s.pos c = some n
  head : ∀ c, s.pos c = some s.hd →
    s.ph c = .front ∨ s.ph c = .holding ∨ (s.ph c = .waiting ∧ s.busy c = false)
  tail : ∀ c n, s.pos c = some n → s.hd < n →
    (∃ p, s.ph c = .linking p ∧ s.busy c = true ∧ s.pos p = some (n - 1) ∧ s.next p = none) ∨
    (s.ph c = .waiting ∧ s.busy c = true ∧ ∃ p, s.pos p = some (n - 1) ∧ s.next p = some c)
  nxt : ∀ c n d, s.pos c = some n → s.next c = some d → s.pos d = some (n + 1) ∧ s.ph d = .waiting

theorem minv_init : MInv MS.init where
  le := Nat.le_refl _
  range := fun _ _ => ⟨rfl, rfl⟩
  inq := fun c => by simp [MS.init]
  bnd := fun c n h => by simp [MS.init] at h
  inj := fun c d n h => by simp [MS.init] at h
  cover := fun n h1 h2 => by simp [MS.init] at h1 h2
  head := fun c h => by simp [MS.init] at h
  tail := fun c n h => by simp [MS.init] at h
  nxt := fun c n d h => by simp [MS.init] at h

/-- A CPU that owns the lock (or is about to take it) is at the head. -/
theorem MInv.owner_head {s : MS} (hi : MInv s) {c : CPU}
    (h : s.ph c = .front ∨ s.ph c = .holding ∨ (s.ph c = .waiting ∧ s.busy c = false)) :
    s.pos c = some s.hd := by
  have hne : s.ph c ≠ .idle := by rcases h with h | h | ⟨h, -⟩ <;> rw [h] <;> simp
  obtain ⟨n, hn⟩ := (hi.inq c).1 hne
  obtain ⟨h1, -⟩ := hi.bnd c n hn
  rcases Nat.lt_or_eq_of_le h1 with hlt | rfl
  · exfalso
    rcases hi.tail c n hn hlt with ⟨p, hp, -, -, -⟩ | ⟨hw, hb, -⟩ <;>
      rcases h with h | h | ⟨h, h'⟩ <;> simp_all
  · exact hn

/-- **Mutual exclusion.** -/
theorem MInv.mutex {s : MS} (hi : MInv s) {c d : CPU} (hc : s.ph c = .holding) (hd : s.ph d = .holding) :
    c = d :=
  hi.inj c d s.hd (hi.owner_head (.inr (.inl hc))) (hi.owner_head (.inr (.inl hd)))

theorem whoAt_some {s : MS} (hi : MInv s) {n : Nat} (h1 : s.hd ≤ n) (h2 : n < s.tl) :
    ∃ p, whoAt s n = some p ∧ s.pos p = some n := by
  obtain ⟨c, hc⟩ := hi.cover n h1 h2
  have hcN : c < NCPU := Nat.lt_of_not_le fun hge => by rw [(hi.range c hge).2] at hc; cases hc
  cases hw : whoAt s n with
  | none =>
    exfalso
    have := findCPU_none hw c hcN
    simp [hc] at this
  | some p =>
    obtain ⟨hp, -⟩ := findCPU_some hw
    exact ⟨p, rfl, by simpa using hp⟩

/-! ## Each event preserves the invariant -/

theorem pos_none {s : MS} (hi : MInv s) {c : CPU} (h : s.ph c = .idle) : s.pos c = none := by
  cases hp : s.pos c with
  | none => rfl
  | some n => exact absurd h ((hi.inq c).2 ⟨n, hp⟩)

theorem inv_swap {s : MS} (hi : MInv s) {c : CPU} (hc : c < NCPU) (hid : s.ph c = .idle) :
    MInv ⟨s.hd, s.tl + 1, fset s.pos c (some s.tl), fset s.busy c true, fset s.next c none,
      fset s.ph c (match tailOf s with | none => .front | some p => .linking p)⟩ := by
  have hpc := pos_none hi hid
  have hX : ∀ X : MPh, (match tailOf s with | none => MPh.front | some p => .linking p) ≠ .idle := by
    intro _; cases tailOf s <;> simp
  constructor
  all_goals dsimp only
  · show s.hd ≤ s.tl + 1; have := hi.le; omega
  · intro d hd
    have hdc : d ≠ c := fun e => by subst e; exact absurd hc (Nat.not_lt.2 hd)
    simp only [fset_other _ _ hdc]; exact hi.range d hd
  · intro d
    by_cases hdc : d = c
    · subst hdc; simp only [fset_same]; exact ⟨fun _ => ⟨_, rfl⟩, fun _ => hX .idle⟩
    · simp only [fset_other _ _ hdc]; exact hi.inq d
  · intro d n hn
    by_cases hdc : d = c
    · subst hdc; simp only [fset_same, Option.some.injEq] at hn; subst hn
      exact ⟨hi.le, by show s.tl < s.tl + 1; omega⟩
    · simp only [fset_other _ _ hdc] at hn
      have := hi.bnd d n hn; exact ⟨this.1, by show n < s.tl + 1; omega⟩
  · intro d e n h1 h2
    by_cases hdc : d = c <;> by_cases hec : e = c
    · rw [hdc, hec]
    · subst hdc; simp only [fset_same, Option.some.injEq, fset_other _ _ hec] at h1 h2
      subst h1; have := (hi.bnd e _ h2).2; omega
    · subst hec; simp only [fset_same, Option.some.injEq, fset_other _ _ hdc] at h1 h2
      subst h2; have := (hi.bnd d _ h1).2; omega
    · simp only [fset_other _ _ hdc, fset_other _ _ hec] at h1 h2; exact hi.inj d e n h1 h2
  · intro n h1 h2
    by_cases hn : n = s.tl
    · exact ⟨c, by simp [hn]⟩
    · obtain ⟨d, hd⟩ := hi.cover n h1 (by show n < s.tl; have : n < s.tl + 1 := h2; omega)
      have hdc : d ≠ c := fun e => by rw [e, hpc] at hd; cases hd
      exact ⟨d, by simp only [fset_other _ _ hdc]; exact hd⟩
  · intro d hd
    by_cases hdc : d = c
    · subst hdc; simp only [fset_same, Option.some.injEq] at hd
      have : tailOf s = none := by simp [tailOf, hd]
      left; simp [this]
    · simp only [fset_other _ _ hdc] at hd ⊢; exact hi.head d hd
  · intro d n hd hlt
    by_cases hdc : d = c
    · subst hdc; simp only [fset_same, Option.some.injEq] at hd; subst hd
      obtain ⟨p, hw, hp⟩ := whoAt_some hi (n := s.tl - 1) (by omega) (by have := hi.le; omega)
      have ht : tailOf s = some p := by simp [tailOf, hlt, hw]
      have hpc' : p ≠ d := fun e => by rw [e, hpc] at hp; cases hp
      have hnp : s.next p = none := by
        cases hnx : s.next p with
        | none => rfl
        | some f => have := (hi.nxt p _ f hp hnx).1; have := (hi.bnd f _ this).2; omega
      left
      exact ⟨p, by simp [ht], by simp, by simp only [fset_other _ _ hpc']; exact hp,
        by simp only [fset_other _ _ hpc']; exact hnp⟩
    · simp only [fset_other _ _ hdc] at hd ⊢
      have hold : s.hd < n := hlt
      rcases hi.tail d n hd hold with ⟨p, h1, h2, h3, h4⟩ | ⟨h1, h2, p, h3, h4⟩
      · have hpc' : p ≠ c := fun e => by rw [e, hpc] at h3; cases h3
        left; exact ⟨p, h1, h2, by simp only [fset_other _ _ hpc']; exact h3,
          by simp only [fset_other _ _ hpc']; exact h4⟩
      · have hpc' : p ≠ c := fun e => by rw [e, hpc] at h3; cases h3
        right; exact ⟨h1, h2, p, by simp only [fset_other _ _ hpc']; exact h3,
          by simp only [fset_other _ _ hpc']; exact h4⟩
  · intro d n e hd hn
    by_cases hdc : d = c
    · subst hdc; simp at hn
    · simp only [fset_other _ _ hdc] at hd hn
      obtain ⟨h1, h2⟩ := hi.nxt d n e hd hn
      have hec : e ≠ c := fun x => by rw [x, hpc] at h1; cases h1
      exact ⟨by simp only [fset_other _ _ hec]; exact h1, by simp only [fset_other _ _ hec]; exact h2⟩

theorem inv_link {s : MS} (hi : MInv s) {c p : CPU} (hc : c < NCPU) (hl : s.ph c = .linking p) :
    MInv ⟨s.hd, s.tl, s.pos, s.busy, fset s.next p (some c), fset s.ph c .waiting⟩ := by
  obtain ⟨n, hn⟩ := (hi.inq c).1 (by rw [hl]; simp)
  have hnh : s.hd < n := by
    rcases Nat.lt_or_eq_of_le (hi.bnd c n hn).1 with h | h
    · exact h
    · subst h; rcases hi.head c hn with h | h | ⟨h, -⟩ <;> rw [hl] at h <;> cases h
  obtain ⟨hpc, hbc, hpp, hnp⟩ : s.ph c = .linking p ∧ s.busy c = true ∧ s.pos p = some (n - 1) ∧
      s.next p = none := by
    rcases hi.tail c n hn hnh with ⟨q, h1, h2, h3, h4⟩ | ⟨h1, -⟩
    · rw [hl] at h1; cases h1; exact ⟨hl, h2, h3, h4⟩
    · rw [hl] at h1; cases h1
  constructor
  all_goals dsimp only
  · exact hi.le
  · intro d hd
    have hdc : d ≠ c := fun e => by subst e; exact absurd hc (Nat.not_lt.2 hd)
    simp only [fset_other _ _ hdc]; exact hi.range d hd
  · intro d
    by_cases hdc : d = c
    · subst hdc; simp only [fset_same]; exact ⟨fun _ => ⟨n, hn⟩, fun _ => by simp⟩
    · simp only [fset_other _ _ hdc]; exact hi.inq d
  · exact hi.bnd
  · exact hi.inj
  · exact hi.cover
  · intro d hd
    have hdc : d ≠ c := fun e => by rw [e, hn] at hd; simp only [Option.some.injEq] at hd; omega
    simp only [fset_other _ _ hdc]; exact hi.head d hd
  · intro e m he hlt
    by_cases hec : e = c
    · subst hec; rw [hn] at he; cases he
      right; exact ⟨by simp, hbc, p, hpp, by simp⟩
    · simp only [fset_other _ _ hec]
      rcases hi.tail e m he hlt with ⟨q, h1, h2, h3, h4⟩ | ⟨h1, h2, q, h3, h4⟩
      · have hqp : q ≠ p := fun x => by
          rw [x, hpp] at h3; simp only [Option.some.injEq] at h3
          have : m = n := by omega
          subst this; exact hec (hi.inj e c _ he hn)
        left; exact ⟨q, h1, h2, h3, by simp only [fset_other _ _ hqp]; exact h4⟩
      · have hqp : q ≠ p := fun x => by rw [x, hnp] at h4; cases h4
        right; exact ⟨h1, h2, q, h3, by simp only [fset_other _ _ hqp]; exact h4⟩
  · intro d m e hd hne
    by_cases hdp : d = p
    · subst hdp; simp only [fset_same, Option.some.injEq] at hne; subst hne
      rw [hpp] at hd; cases hd
      exact ⟨by rw [hn]; congr 1; omega, by simp⟩
    · simp only [fset_other _ _ hdp] at hne
      obtain ⟨h1, h2⟩ := hi.nxt d m e hd hne
      have hec : e ≠ c := fun x => by rw [x, hl] at h2; cases h2
      exact ⟨h1, by simp only [fset_other _ _ hec]; exact h2⟩

/-- Taking the lock from the head of the queue. -/
theorem inv_hold {s : MS} (hi : MInv s) {c : CPU} (hc : c < NCPU)
    (hown : s.ph c = .front ∨ (s.ph c = .waiting ∧ s.busy c = false)) :
    MInv ⟨s.hd, s.tl, s.pos, s.busy, s.next, fset s.ph c .holding⟩ := by
  have hh : s.pos c = some s.hd := hi.owner_head (by rcases hown with h | h; exact .inl h; exact .inr (.inr h))
  constructor
  all_goals dsimp only
  · exact hi.le
  · intro d hd
    have hdc : d ≠ c := fun e => by subst e; exact absurd hc (Nat.not_lt.2 hd)
    simp only [fset_other _ _ hdc]; exact hi.range d hd
  · intro d
    by_cases hdc : d = c
    · subst hdc; simp only [fset_same]; exact ⟨fun _ => ⟨_, hh⟩, fun _ => by simp⟩
    · simp only [fset_other _ _ hdc]; exact hi.inq d
  · exact hi.bnd
  · exact hi.inj
  · exact hi.cover
  · intro d hd
    by_cases hdc : d = c
    · subst hdc; simp
    · simp only [fset_other _ _ hdc]; exact hi.head d hd
  · intro e m he hlt
    have hec : e ≠ c := fun x => by rw [x, hh] at he; simp only [Option.some.injEq] at he; omega
    simp only [fset_other _ _ hec]; exact hi.tail e m he hlt
  · intro d m e hd hne
    obtain ⟨h1, h2⟩ := hi.nxt d m e hd hne
    have hec : e ≠ c := fun x => by
      rw [x, hh] at h1; simp only [Option.some.injEq] at h1; have := (hi.bnd d m hd).1; omega
    exact ⟨h1, by simp only [fset_other _ _ hec]; exact h2⟩

theorem inv_cas {s : MS} (hi : MInv s) {c : CPU} (hc : c < NCPU) (hh : s.ph c = .holding)
    (ht : s.tl = s.hd + 1) :
    MInv ⟨s.hd + 1, s.tl, fset s.pos c none, s.busy, s.next, fset s.ph c .idle⟩ := by
  have hpc : s.pos c = some s.hd := hi.owner_head (.inr (.inl hh))
  -- nobody else is in the queue
  have hnone : ∀ d, d ≠ c → s.pos d = none := by
    intro d hdc
    cases hp : s.pos d with
    | none => rfl
    | some n =>
      have := hi.bnd d n hp
      have : n = s.hd := by omega
      subst this; exact absurd (hi.inj d c _ hp hpc) hdc
  constructor
  all_goals dsimp only
  · show s.hd + 1 ≤ s.tl; omega
  · intro d hd
    have hdc : d ≠ c := fun e => by subst e; exact absurd hc (Nat.not_lt.2 hd)
    simp only [fset_other _ _ hdc]; exact hi.range d hd
  · intro d
    by_cases hdc : d = c
    · subst hdc; simp
    · simp only [fset_other _ _ hdc]; rw [hi.inq d, hnone d hdc]
  · intro d n hd
    by_cases hdc : d = c
    · subst hdc; simp at hd
    · simp only [fset_other _ _ hdc, hnone d hdc] at hd; cases hd
  · intro d e n h1 h2
    by_cases hdc : d = c
    · subst hdc; simp at h1
    · simp only [fset_other _ _ hdc, hnone d hdc] at h1; cases h1
  · intro n h1 h2; exfalso; show False; have : s.hd + 1 ≤ n := h1; omega
  · intro d hd
    by_cases hdc : d = c
    · subst hdc; simp at hd
    · simp only [fset_other _ _ hdc, hnone d hdc] at hd; cases hd
  · intro d n hd
    by_cases hdc : d = c
    · subst hdc; simp at hd
    · simp only [fset_other _ _ hdc, hnone d hdc] at hd; cases hd
  · intro d n e hd
    by_cases hdc : d = c
    · subst hdc; simp at hd
    · simp only [fset_other _ _ hdc, hnone d hdc] at hd; cases hd

theorem inv_handoff {s : MS} (hi : MInv s) {c d : CPU} (hc : c < NCPU) (hh : s.ph c = .holding)
    (hn : s.next c = some d) :
    MInv ⟨s.hd + 1, s.tl, fset s.pos c none, fset s.busy d false, s.next, fset s.ph c .idle⟩ := by
  have hpc : s.pos c = some s.hd := hi.owner_head (.inr (.inl hh))
  obtain ⟨hpd, hwd⟩ := hi.nxt c _ d hpc hn
  have hdc : d ≠ c := fun e => by rw [e, hpc] at hpd; simp only [Option.some.injEq] at hpd; omega
  constructor
  all_goals dsimp only
  · show s.hd + 1 ≤ s.tl; have := (hi.bnd d _ hpd).2; omega
  · intro e he
    have hec : e ≠ c := fun x => by subst x; exact absurd hc (Nat.not_lt.2 he)
    simp only [fset_other _ _ hec]; exact hi.range e he
  · intro e
    by_cases hec : e = c
    · subst hec; simp
    · simp only [fset_other _ _ hec]; exact hi.inq e
  · intro e n he
    by_cases hec : e = c
    · subst hec; simp at he
    · simp only [fset_other _ _ hec] at he
      have h1 := hi.bnd e n he
      have : n ≠ s.hd := fun x => by subst x; exact hec (hi.inj e c _ he hpc)
      exact ⟨by show s.hd + 1 ≤ n; omega, h1.2⟩
  · intro e f n h1 h2
    by_cases hec : e = c
    · subst hec; simp at h1
    · by_cases hfc : f = c
      · subst hfc; simp at h2
      · simp only [fset_other _ _ hec, fset_other _ _ hfc] at h1 h2; exact hi.inj e f n h1 h2
  · intro n h1 h2
    obtain ⟨e, he⟩ := hi.cover n (by have : s.hd + 1 ≤ n := h1; omega) h2
    have hec : e ≠ c := fun x => by rw [x, hpc] at he; simp only [Option.some.injEq] at he; omega
    exact ⟨e, by simp only [fset_other _ _ hec]; exact he⟩
  · intro e he
    by_cases hec : e = c
    · subst hec; simp at he
    · simp only [fset_other _ _ hec] at he ⊢
      have hed : e = d := hi.inj e d _ he hpd
      subst hed
      exact .inr (.inr ⟨hwd, by simp⟩)
  · intro e m he hlt
    by_cases hec : e = c
    · subst hec; simp at he
    · simp only [fset_other _ _ hec] at he ⊢
      have hed : e ≠ d := fun x => by rw [x, hpd] at he; simp only [Option.some.injEq] at he; omega
      have hlt' : s.hd < m := by have : s.hd + 1 < m := hlt; omega
      rcases hi.tail e m he hlt' with ⟨q, h1, h2, h3, h4⟩ | ⟨h1, h2, q, h3, h4⟩
      · have hqc : q ≠ c := fun x => by rw [x, hpc] at h3; simp only [Option.some.injEq] at h3; have : s.hd + 1 < m := hlt; omega
        left; exact ⟨q, h1, by simp only [fset_other _ _ hed]; exact h2,
          by simp only [fset_other _ _ hqc]; exact h3, h4⟩
      · have hqc : q ≠ c := fun x => by rw [x, hpc] at h3; simp only [Option.some.injEq] at h3; have : s.hd + 1 < m := hlt; omega
        right; exact ⟨h1, by simp only [fset_other _ _ hed]; exact h2, q,
          by simp only [fset_other _ _ hqc]; exact h3, h4⟩
  · intro e m f he hne
    by_cases hec : e = c
    · subst hec; simp at he
    · simp only [fset_other _ _ hec] at he
      obtain ⟨h1, h2⟩ := hi.nxt e m f he hne
      have hfc : f ≠ c := fun x => by
        rw [x, hpc] at h1; simp only [Option.some.injEq] at h1; have := (hi.bnd e m he).1; omega
      exact ⟨by simp only [fset_other _ _ hfc]; exact h1, by simp only [fset_other _ _ hfc]; exact h2⟩

theorem mstep_inv {s s' : MS} {e : MEvent} {o : Option HEvent} (hi : MInv s)
    (hp : mstep s e = some (s', o)) : MInv s' := by
  obtain ⟨c, k⟩ := e
  simp only [mstep] at hp
  split at hp
  case isFalse => simp at hp
  rename_i hc
  cases k <;> cases hph : s.ph c <;> simp only [hph] at hp <;> try simp at hp
  · obtain ⟨rfl, -⟩ := hp; exact inv_swap hi hc hph
  · obtain ⟨rfl, -⟩ := hp; exact inv_link hi hc hph
  · obtain ⟨rfl, -⟩ := hp; exact hi
  · obtain ⟨rfl, -⟩ := hp; exact inv_hold hi hc (.inl hph)
  · obtain ⟨hb, rfl, -⟩ := hp; exact inv_hold hi hc (.inr ⟨hph, hb⟩)
  · obtain ⟨rfl, -⟩ := hp; exact hi
  · split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp
      rename_i ht; exact inv_cas hi hc hph ht
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact hi
  · split at hp
    · rename_i d hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp
      exact inv_handoff hi hc hph hn
    · simp at hp

theorem mreplay_inv : ∀ {l : MLog} {s : MS} {h : List HEvent}, mreplay l = some (s, h) → MInv s
  | [], s, h, hr => by simp [mreplay] at hr; obtain ⟨rfl, -⟩ := hr; exact minv_init
  | _ :: _, _, _, hr => by
    obtain ⟨s0, h0, o, hl, hp, -⟩ := mreplay_cons hr
    exact mstep_inv (mreplay_inv hl) hp

/-- **Mutual exclusion** for every protocol-conforming MCS log. -/
theorem mutexM {l : MLog} {s : MS} {h : List HEvent} (hr : mreplay l = some (s, h))
    {c d : CPU} (hc : s.ph c = .holding) (hd : s.ph d = .holding) : c = d :=
  (mreplay_inv hr).mutex hc hd

/-! ## The same atomic interface as the ticket lock -/

/-- `o` names the CPU that holds the MCS lock. -/
def HoldsM (s : MS) (o : Option CPU) : Prop := ∀ d, s.ph d = .holding ↔ o = some d

theorem holds_frame {s s' : MS} {c : CPU} {o : Option CPU} (hH : HoldsM s o)
    (hother : ∀ d, d ≠ c → s'.ph d = s.ph d) (hc : s.ph c ≠ .holding) (hc' : s'.ph c ≠ .holding) :
    HoldsM s' o := by
  intro d
  by_cases hdc : d = c
  · subst hdc
    constructor
    · intro h; exact absurd h hc'
    · intro h; exact absurd ((hH d).2 h) hc
  · rw [hother d hdc]; exact hH d

/-- **R₁ for MCS**: the high-level log of any protocol-conforming MCS log is a
valid atomic-lock log, and its holder is the protocol's holder. -/
theorem mreplay_hreplay : ∀ {l : MLog} {s : MS} {h : List HEvent},
    mreplay l = some (s, h) → ∃ o, hreplay h = some o ∧ HoldsM s o
  | [], s, h, hr => by
    simp [mreplay] at hr; obtain ⟨rfl, rfl⟩ := hr
    exact ⟨none, rfl, fun d => by simp [MS.init]⟩
  | e :: l, s', h', hr => by
    obtain ⟨s, h, o, hl, hp, rfl⟩ := mreplay_cons hr
    obtain ⟨o0, ho0, hH⟩ := mreplay_hreplay hl
    have hi := mreplay_inv hl
    obtain ⟨c, k⟩ := e
    simp only [mstep] at hp
    split at hp
    case isFalse => simp at hp
    -- events that touch only `c`'s phase and do not make or end a holder
    have quiet : ∀ (s2 : MS), (∀ d, d ≠ c → s2.ph d = s.ph d) → s.ph c ≠ .holding →
        s2.ph c ≠ .holding → ∃ o', hreplay (consOpt none h) = some o' ∧ HoldsM s2 o' :=
      fun s2 h1 h2 h3 => ⟨o0, ho0, holds_frame hH h1 h2 h3⟩
    -- nobody holds while `c` is about to take the lock
    have nohold : (s.ph c = .front ∨ (s.ph c = .waiting ∧ s.busy c = false)) → o0 = none := by
      intro hown
      cases ho : o0 with
      | none => rfl
      | some d =>
        exfalso
        have hd := (hH d).2 ho
        have h1 := hi.owner_head (.inr (.inl hd))
        have h2 := hi.owner_head (by rcases hown with h | h; exact .inl h; exact .inr (.inr h))
        have := hi.inj d c _ h1 h2
        subst this
        rcases hown with h | ⟨h, -⟩ <;> rw [hd] at h <;> cases h
    cases k <;> cases hph : s.ph c <;> simp only [hph] at hp <;> try simp at hp
    · obtain ⟨rfl, rfl⟩ := hp
      exact quiet _ (fun d hd => fset_other _ _ hd) (by simp [hph]) (by simp; cases tailOf s <;> simp)
    · obtain ⟨rfl, rfl⟩ := hp
      exact quiet _ (fun d hd => fset_other _ _ hd) (by simp [hph]) (by simp)
    · obtain ⟨rfl, rfl⟩ := hp; exact ⟨o0, ho0, hH⟩
    · -- hold from the front
      obtain ⟨rfl, rfl⟩ := hp
      have h0 := nohold (.inl hph); subst h0
      refine ⟨some c, by simp [consOpt, hreplay, ho0, hstep], fun d => ?_⟩
      by_cases hdc : d = c
      · subst hdc; simp
      · simp only [fset_other _ _ hdc]; rw [hH d]; simp [Ne.symm hdc]
    · -- hold after the hand-off
      obtain ⟨hb, rfl, rfl⟩ := hp
      have h0 := nohold (.inr ⟨hph, hb⟩); subst h0
      refine ⟨some c, by simp [consOpt, hreplay, ho0, hstep], fun d => ?_⟩
      by_cases hdc : d = c
      · subst hdc; simp
      · simp only [fset_other _ _ hdc]; rw [hH d]; simp [Ne.symm hdc]
    · obtain ⟨rfl, rfl⟩ := hp; exact ⟨o0, ho0, hH⟩
    · -- cas
      have hoc : o0 = some c := (hH c).1 hph
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
        refine ⟨none, by simp [consOpt, hreplay, ho0, hoc, hstep], fun d => ?_⟩
        by_cases hdc : d = c
        · subst hdc; simp
        · simp only [fset_other _ _ hdc]
          constructor
          · intro hd; exact absurd (hi.mutex hd hph) hdc
          · intro h; cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
        exact ⟨o0, ho0, hH⟩
    · -- handoff
      have hoc : o0 = some c := (hH c).1 hph
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, rfl⟩ := hp
        refine ⟨none, by simp [consOpt, hreplay, ho0, hoc, hstep], fun d => ?_⟩
        by_cases hdc : d = c
        · subst hdc; simp
        · simp only [fset_other _ _ hdc]
          constructor
          · intro hd; exact absurd (hi.mutex hd hph) hdc
          · intro h; cases h
      · simp at hp

end MCS
