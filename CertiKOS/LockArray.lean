import CertiKOS.AtomicLayer

/-!
# Lock arrays with `pull`/`push`: the shared log and its protocol

mC2 has an array of ticket locks `L[NUM_LOCK]` ([OSDI16] Fig. 7). Lock `i`
protects a block of shared memory. Acquiring `i` ends with `pull(i)`, which
moves the block into the CPU, and releasing it starts with `push(i)`, which
moves it back ([OSDI16] Fig. 7, [PLDI18] §2). As in CertiKOS there is one
global log, and every event carries its lock index.

* `AEvent`: `⟨cpu, lock, kind⟩`, where `kind` is a ticket-lock event, `pull`,
  or `push v` (carrying the block's new contents).
* `projL i`: the ticket events of lock `i`, as a single-lock `Log`. Each lock
  runs the single-lock protocol of `TicketProtocol.lean` on its projection
  (`areplay_proj`), so every single-lock lemma (`Inv`, `mutex`, `Cover`, …)
  applies per lock.
* `areplay`: the array protocol. Ticket events step their own lock's state.
  `pull`/`push` are allowed only for the holder of that lock (ownership).
  The high-level events are `acqA c i` at `hold` (CCAL's linearization point)
  and `relA c i v` at `inc_n`, carrying the block's contents `v` at release.
* `DI` (data invariant): unless the holder has pushed since its `hold`, the
  block's contents equal the value of the last `relA` on that lock. So the
  data a CPU pulls is the data the previous holder released.
-/

namespace LockArray

open ClightL Ticket

/-! ## Events and logs -/

inductive AKind
  | tk (k : EvKind) | pull | push (v : Val)
  deriving DecidableEq

structure AEvent where
  cpu : CPU
  lk : Nat
  kind : AKind
  deriving DecidableEq

abbrev ALog := List AEvent

/-- The ticket events of lock `i`. -/
def projL (i : Nat) : ALog → Log
  | [] => []
  | ⟨c, j, .tk k⟩ :: l => if j = i then ⟨c, k⟩ :: projL i l else projL i l
  | _ :: l => projL i l

/-- The contents of block `i`: the last value pushed (0 initially). -/
def memOf (i : Nat) : ALog → Val
  | [] => 0
  | ⟨_, j, .push v⟩ :: l => if j = i then v else memOf i l
  | _ :: l => memOf i l

theorem projL_append (i : Nat) (xs l : ALog) : projL i (xs ++ l) = projL i xs ++ projL i l := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    obtain ⟨c, j, k⟩ := e
    cases k <;> simp only [List.cons_append, projL, ih] <;> split <;> rfl

theorem projL_cpu {i : Nat} {c : CPU} : ∀ {l : ALog}, (∀ e ∈ l, e.cpu ≠ c) → ∀ e ∈ projL i l, e.cpu ≠ c
  | [], _, e, he => by simp [projL] at he
  | ⟨d, j, k⟩ :: l, h, e, he => by
    have ih := projL_cpu (i := i) (l := l) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    cases k with
    | tk k =>
      simp only [projL] at he
      split at he
      · rcases List.mem_cons.1 he with rfl | he
        · exact h _ List.mem_cons_self
        · exact ih e he
      · exact ih e he
    | pull => exact ih e he
    | push v => exact ih e he

/-! ## The array protocol -/

inductive HEventA
  | acqA (c : CPU) (i : Nat) | relA (c : CPU) (i : Nat) (v : Val)
  deriving DecidableEq

def HEventA.cpu : HEventA → CPU
  | .acqA c _ => c
  | .relA c _ _ => c

abbrev HLogA := List HEventA

structure AState where
  lk : Nat → PState
  mem : Nat → Val
  dirty : Nat → Bool

def AState.init : AState := ⟨fun _ => PState.init, fun _ => 0, fun _ => false⟩

def upd {α : Type} (f : Nat → α) (i : Nat) (a : α) : Nat → α := fun j => if j = i then a else f j

@[simp] theorem upd_same {α : Type} (f : Nat → α) (i : Nat) (a : α) : upd f i a i = a := by simp [upd]
theorem upd_other {α : Type} (f : Nat → α) {i j : Nat} (a : α) (h : j ≠ i) : upd f i a j = f j := by
  simp [upd, h]

def lift (i : Nat) (v : Val) : HEvent → HEventA
  | .acq c => .acqA c i
  | .rel c => .relA c i v

def Holding (S : AState) (c : CPU) (i : Nat) : Prop := ∃ t, (S.lk i).phase c = .holding t

instance (S : AState) (c : CPU) (i : Nat) : Decidable (Holding S c i) := by
  unfold Holding
  cases h : (S.lk i).phase c with
  | idle => exact isFalse (fun ⟨t, ht⟩ => by cases ht)
  | waiting t => exact isFalse (fun ⟨t', ht⟩ => by cases ht)
  | holding t => exact isTrue ⟨t, rfl⟩

def astep (S : AState) : AEvent → Option (AState × Option HEventA)
  | ⟨c, i, .tk k⟩ =>
    match pstep (S.lk i) ⟨c, k⟩ with
    | none => none
    | some (p', o) =>
      some (⟨upd S.lk i p', S.mem, if k = .hold ∨ k = .incNow then upd S.dirty i false else S.dirty⟩,
        o.map (lift i (S.mem i)))
  | ⟨c, i, .pull⟩ => if Holding S c i then some (S, none) else none
  | ⟨c, i, .push v⟩ =>
    if Holding S c i then some (⟨S.lk, upd S.mem i v, upd S.dirty i true⟩, none) else none

def consO (o : Option HEventA) (h : HLogA) : HLogA :=
  match o with
  | none => h
  | some e => e :: h

def areplay : ALog → Option (AState × HLogA)
  | [] => some (AState.init, [])
  | e :: l =>
    match areplay l with
    | none => none
    | some (S, H) =>
      match astep S e with
      | none => none
      | some (S', o) => some (S', consO o H)

theorem areplay_cons {e : AEvent} {l : ALog} {S' : AState} {H' : HLogA}
    (hr : areplay (e :: l) = some (S', H')) :
    ∃ S H o, areplay l = some (S, H) ∧ astep S e = some (S', o) ∧ H' = consO o H := by
  simp only [areplay] at hr
  split at hr
  · simp at hr
  · rename_i S H hl
    split at hr
    · simp at hr
    · rename_i S2 o hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨S, H, o, hl, hp, rfl⟩

theorem areplay_cons_of {e : AEvent} {l : ALog} {S S' : AState} {H : HLogA} {o : Option HEventA}
    (hl : areplay l = some (S, H)) (hp : astep S e = some (S', o)) :
    areplay (e :: l) = some (S', consO o H) := by
  simp [areplay, hl, hp]

/-! ## Each lock runs the single-lock protocol on its projection -/

/-- The high-level events of lock `i`, as single-lock events. -/
def projH (i : Nat) : HLogA → List HEvent
  | [] => []
  | .acqA c j :: h => if j = i then .acq c :: projH i h else projH i h
  | .relA c j _ :: h => if j = i then .rel c :: projH i h else projH i h

theorem projH_lift (i j : Nat) (v : Val) (o : Option HEvent) (H : HLogA) :
    projH i (consO (o.map (lift j v)) H) = if j = i then consOpt o (projH i H) else projH i H := by
  cases o with
  | none => split <;> rfl
  | some e => cases e <;> simp [consO, lift, projH, consOpt] <;> split <;> simp_all

theorem areplay_proj : ∀ {l : ALog} {S : AState} {H : HLogA}, areplay l = some (S, H) →
    ∀ i, replay (projL i l) = some (S.lk i, projH i H)
  | [], S, H, hr, i => by
    simp [areplay] at hr; obtain ⟨rfl, rfl⟩ := hr; rfl
  | e :: l, S', H', hr, i => by
    obtain ⟨S, H, o, hl, hp, rfl⟩ := areplay_cons hr
    have ih := areplay_proj hl i
    obtain ⟨c, j, k⟩ := e
    cases k with
    | tk k =>
      simp only [astep] at hp
      split at hp
      · simp at hp
      · rename_i p' o' hps
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        rw [projH_lift]
        by_cases hji : j = i
        · subst hji
          simp only [projL, ite_true, upd_same]
          exact replay_cons_of ih hps
        · simp only [projL, hji, ite_false, upd_other _ _ (Ne.symm hji)]
          exact ih
    | pull =>
      simp only [astep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp; exact ih
      · simp at hp
    | push v =>
      simp only [astep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp; exact ih
      · simp at hp

/-- **Mutual exclusion, per lock.** -/
theorem amutex {l : ALog} {S : AState} {H : HLogA} (hr : areplay l = some (S, H)) (i : Nat)
    {c d : CPU} (hc : Holding S c i) (hd : Holding S d i) : c = d := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨u, hu⟩ := hd
  exact mutex (areplay_proj hr i) ht hu

/-! ## The data invariant -/

/-- The block contents as of the last release of lock `i`. -/
def hmemA (i : Nat) : HLogA → Val
  | [] => 0
  | .relA _ j v :: h => if j = i then v else hmemA i h
  | _ :: h => hmemA i h

def NoHolder (S : AState) (i : Nat) : Prop := ∀ c t, (S.lk i).phase c ≠ .holding t

/-- Unless the holder has pushed since its `hold`, block `i` holds the value
of the last release; a free lock's block is clean. -/
def DI (S : AState) (H : HLogA) : Prop :=
  ∀ i, (S.dirty i = false → S.mem i = hmemA i H) ∧ (NoHolder S i → S.dirty i = false)

theorem hmemA_lift_other {i j : Nat} (hji : j ≠ i) (v : Val) (o : Option HEvent) (H : HLogA) :
    hmemA i (consO (o.map (lift j v)) H) = hmemA i H := by
  cases o with
  | none => rfl
  | some e => cases e <;> simp [consO, lift, hmemA, hji]

theorem areplay_di : ∀ {l : ALog} {S : AState} {H : HLogA}, areplay l = some (S, H) → DI S H
  | [], S, H, hr => by
    simp [areplay] at hr; obtain ⟨rfl, rfl⟩ := hr
    intro i; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | e :: l, S', H', hr => by
    obtain ⟨S, H, o, hl, hp, rfl⟩ := areplay_cons hr
    have ih := areplay_di hl
    have hinv : ∀ i, Inv (S.lk i) := fun i => replay_inv (areplay_proj hl i)
    obtain ⟨c, j, k⟩ := e
    intro i
    cases k with
    | tk k =>
      simp only [astep] at hp
      split at hp
      · simp at hp
      · rename_i p' o' hps
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        by_cases hji : j = i
        · subst hji
          -- the event is on lock `i` itself
          simp only [pstep] at hps
          split at hps
          case isFalse => simp at hps
          cases k <;> cases hph : (S.lk j).phase c <;> simp only [hph] at hps <;> try simp at hps
          · -- FAI_t
            obtain ⟨rfl, rfl⟩ := hps
            refine ⟨fun hd => (ih j).1 (by simpa using hd), fun hn => (ih j).2 fun d t hd => ?_⟩
            by_cases hdc : d = c
            · subst hdc; rw [hph] at hd; cases hd
            · have := hn d t; simp [upd, setPhase, hdc] at this; exact this hd
          · -- get_n
            obtain ⟨rfl, rfl⟩ := hps
            refine ⟨fun hd => (ih j).1 (by simpa using hd), fun hn => (ih j).2 fun d t hd => ?_⟩
            exact hn d t (by simpa [upd] using hd)
          · -- inc_n: the release records the block's contents
            obtain ⟨rfl, rfl⟩ := hps
            refine ⟨fun _ => by simp [consO, lift, hmemA], fun _ => by simp⟩
          · -- hold: the lock was free, so the block was clean
            rename_i t0
            obtain ⟨hnow, rfl, rfl⟩ := hps
            have hfree : NoHolder S j := by
              intro d t hd
              have h1 := (hinv j).holdNow d t hd
              have h2 := (hinv j).uniq d c t (by simp [hd, Phase.tk]) (by simp [hph, Phase.tk]; omega)
              subst h2; rw [hph] at hd; cases hd
            have hcl := (ih j).2 hfree
            refine ⟨fun _ => ?_, fun _ => by simp⟩
            simp [consO, lift, hmemA]; exact (ih j).1 hcl
        · -- another lock: nothing of lock `i` changes
          have hk : ∀ b : Bool, (if k = .hold ∨ k = .incNow then upd S.dirty j false else S.dirty) i =
              S.dirty i := by intro _; split <;> simp [upd, Ne.symm hji]
          refine ⟨fun hd => ?_, fun hn => ?_⟩
          · simp only [hk true] at hd
            simp only [hmemA_lift_other hji]; exact (ih i).1 hd
          · simp only [hk true]
            refine (ih i).2 fun d t hd => hn d t ?_
            simp [upd, Ne.symm hji, hd]
    | pull =>
      simp only [astep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp; exact ih i
      · simp at hp
    | push v =>
      simp only [astep] at hp
      split at hp
      · rename_i hhold
        simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        by_cases hji : j = i
        · subst hji
          refine ⟨fun hd => by simp at hd, fun hn => ?_⟩
          obtain ⟨t, ht⟩ := hhold; exact absurd ht (hn c t)
        · simp only [consO, upd_other _ _ (Ne.symm hji)]
          exact ih i
      · simp at hp

/-- `memOf` reads the block contents of the replayed state. -/
theorem areplay_mem : ∀ {l : ALog} {S : AState} {H : HLogA}, areplay l = some (S, H) →
    ∀ i, S.mem i = memOf i l
  | [], S, H, hr, i => by simp [areplay] at hr; obtain ⟨rfl, -⟩ := hr; rfl
  | e :: l, S', H', hr, i => by
    obtain ⟨S, H, o, hl, hp, rfl⟩ := areplay_cons hr
    have ih := areplay_mem hl i
    obtain ⟨c, j, k⟩ := e
    cases k with
    | tk k =>
      simp only [astep] at hp
      split at hp
      · simp at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp; simpa [memOf] using ih
    | pull =>
      simp only [astep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp; simpa [memOf] using ih
      · simp at hp
    | push v =>
      simp only [astep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        by_cases hji : j = i
        · subst hji; simp [memOf]
        · simp [memOf, hji, upd_other _ _ (Ne.symm hji), ih]
      · simp at hp

end LockArray
