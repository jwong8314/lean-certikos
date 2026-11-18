import CertiKOS.LockArray

/-!
# Lock arrays protecting memory regions

`LockArray.lean` with each lock protecting a **region** (a block of cells,
`Region := Nat → Val`) instead of a single value, as in mC2, where lock `i`
protects a block of shared memory ([OSDI16] Fig. 7).

* `RKind`: a ticket event, `pull` (take ownership of the region), or
  `wr j v` (the holder writes `v` to cell `j`). Only the holder may `pull` or
  write.
* `rreplay`: the protocol. Each lock still runs the single-lock ticket
  protocol on its projection (`rreplay_proj`), so `rmutex` is per lock.
* `HEventR`: `acqR c i` at `hold`, and `relR c i b` at release, carrying the
  **whole region** `b`.
* `RDI`: unless the holder has written since its `hold`, region `i` is exactly
  the region of the last release (`hmemR`). So a CPU that takes the lock sees
  every cell the previous holder left, and no one else's writes.
* `rreplay_hreplay`: R₁. Each lock's high-level log is a valid atomic-lock
  log, and the atomic `acq` returns the region of the last release.
* `rprims`: the C primitives (`rd(lk, j)` and `wr(lk, j, v)` alongside the
  ticket primitives). `demo_region`: two CPUs, one after the other, each
  incrementing three cells of the same region, checked by `decide`.
-/

namespace LockRegion

open ClightL Ticket
open LockArray (upd upd_same upd_other)

/-- A region: a block of cells. -/
abbrev Region := Nat → Val

/-- Write cell `j` of a region. -/
def setCell (b : Region) (j : Nat) (v : Val) : Region := fun k => if k = j then v else b k

/-! ## Events and logs -/

inductive RKind
  | tk (k : EvKind) | pull | wr (j : Nat) (v : Val)
  deriving DecidableEq

structure REvent where
  cpu : CPU
  lk : Nat
  kind : RKind
  deriving DecidableEq

abbrev RLog := List REvent

/-- The ticket events of lock `i`. -/
def projL (i : Nat) : RLog → Log
  | [] => []
  | ⟨c, j, .tk k⟩ :: l => if j = i then ⟨c, k⟩ :: projL i l else projL i l
  | _ :: l => projL i l

/-- The contents of region `i`: every cell written so far (0 initially). -/
def memOf (i : Nat) : RLog → Region
  | [] => fun _ => 0
  | ⟨_, j, .wr k v⟩ :: l => if j = i then setCell (memOf i l) k v else memOf i l
  | _ :: l => memOf i l

theorem projL_append (i : Nat) (xs l : RLog) : projL i (xs ++ l) = projL i xs ++ projL i l := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    obtain ⟨c, j, k⟩ := e
    cases k <;> simp only [List.cons_append, projL, ih] <;> split <;> rfl

theorem projL_cpu {i : Nat} {c : CPU} : ∀ {l : RLog}, (∀ e ∈ l, e.cpu ≠ c) → ∀ e ∈ projL i l, e.cpu ≠ c
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
    | wr k v => exact ih e he

/-! ## The array protocol -/

inductive HEventR
  | acqR (c : CPU) (i : Nat) | relR (c : CPU) (i : Nat) (b : Region)

def HEventR.cpu : HEventR → CPU
  | .acqR c _ => c
  | .relR c _ _ => c

abbrev HLogR := List HEventR

structure RState where
  lk : Nat → PState
  mem : Nat → Region
  dirty : Nat → Bool

def RState.init : RState := ⟨fun _ => PState.init, fun _ _ => 0, fun _ => false⟩


def lift (i : Nat) (b : Region) : HEvent → HEventR
  | .acq c => .acqR c i
  | .rel c => .relR c i b

def Holding (S : RState) (c : CPU) (i : Nat) : Prop := ∃ t, (S.lk i).phase c = .holding t

instance (S : RState) (c : CPU) (i : Nat) : Decidable (Holding S c i) := by
  unfold Holding
  cases h : (S.lk i).phase c with
  | idle => exact isFalse (fun ⟨t, ht⟩ => by cases ht)
  | waiting t => exact isFalse (fun ⟨t', ht⟩ => by cases ht)
  | holding t => exact isTrue ⟨t, rfl⟩

def rstep (S : RState) : REvent → Option (RState × Option HEventR)
  | ⟨c, i, .tk k⟩ =>
    match pstep (S.lk i) ⟨c, k⟩ with
    | none => none
    | some (p', o) =>
      some (⟨upd S.lk i p', S.mem, if k = .hold ∨ k = .incNow then upd S.dirty i false else S.dirty⟩,
        o.map (lift i (S.mem i)))
  | ⟨c, i, .pull⟩ => if Holding S c i then some (S, none) else none
  | ⟨c, i, .wr j v⟩ =>
    if Holding S c i then some (⟨S.lk, upd S.mem i (setCell (S.mem i) j v), upd S.dirty i true⟩, none)
    else none

def consO (o : Option HEventR) (h : HLogR) : HLogR :=
  match o with
  | none => h
  | some e => e :: h

def rreplay : RLog → Option (RState × HLogR)
  | [] => some (RState.init, [])
  | e :: l =>
    match rreplay l with
    | none => none
    | some (S, H) =>
      match rstep S e with
      | none => none
      | some (S', o) => some (S', consO o H)

theorem rreplay_cons {e : REvent} {l : RLog} {S' : RState} {H' : HLogR}
    (hr : rreplay (e :: l) = some (S', H')) :
    ∃ S H o, rreplay l = some (S, H) ∧ rstep S e = some (S', o) ∧ H' = consO o H := by
  simp only [rreplay] at hr
  split at hr
  · simp at hr
  · rename_i S H hl
    split at hr
    · simp at hr
    · rename_i S2 o hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨S, H, o, hl, hp, rfl⟩

theorem rreplay_cons_of {e : REvent} {l : RLog} {S S' : RState} {H : HLogR} {o : Option HEventR}
    (hl : rreplay l = some (S, H)) (hp : rstep S e = some (S', o)) :
    rreplay (e :: l) = some (S', consO o H) := by
  simp [rreplay, hl, hp]

/-! ## Each lock runs the single-lock protocol on its projection -/

/-- The high-level events of lock `i`, as single-lock events. -/
def projH (i : Nat) : HLogR → List HEvent
  | [] => []
  | .acqR c j :: h => if j = i then .acq c :: projH i h else projH i h
  | .relR c j _ :: h => if j = i then .rel c :: projH i h else projH i h

theorem projH_lift (i j : Nat) (v : Region) (o : Option HEvent) (H : HLogR) :
    projH i (consO (o.map (lift j v)) H) = if j = i then consOpt o (projH i H) else projH i H := by
  cases o with
  | none => split <;> rfl
  | some e => cases e <;> simp [consO, lift, projH, consOpt] <;> split <;> simp_all

theorem rreplay_proj : ∀ {l : RLog} {S : RState} {H : HLogR}, rreplay l = some (S, H) →
    ∀ i, replay (projL i l) = some (S.lk i, projH i H)
  | [], S, H, hr, i => by
    simp [rreplay] at hr; obtain ⟨rfl, rfl⟩ := hr; rfl
  | e :: l, S', H', hr, i => by
    obtain ⟨S, H, o, hl, hp, rfl⟩ := rreplay_cons hr
    have ih := rreplay_proj hl i
    obtain ⟨c, j, k⟩ := e
    cases k with
    | tk k =>
      simp only [rstep] at hp
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
      simp only [rstep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp; exact ih
      · simp at hp
    | wr k v =>
      simp only [rstep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp; exact ih
      · simp at hp

/-- **Mutual exclusion, per lock.** -/
theorem rmutex {l : RLog} {S : RState} {H : HLogR} (hr : rreplay l = some (S, H)) (i : Nat)
    {c d : CPU} (hc : Holding S c i) (hd : Holding S d i) : c = d := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨u, hu⟩ := hd
  exact mutex (rreplay_proj hr i) ht hu

/-! ## The data invariant -/

/-- The block contents as of the last release of lock `i`. -/
def hmemR (i : Nat) : HLogR → Region
  | [] => fun _ => 0
  | .relR _ j v :: h => if j = i then v else hmemR i h
  | _ :: h => hmemR i h

def NoHolder (S : RState) (i : Nat) : Prop := ∀ c t, (S.lk i).phase c ≠ .holding t

/-- Unless the holder has pushed since its `hold`, block `i` holds the value
of the last release; a free lock's block is clean. -/
def RDI (S : RState) (H : HLogR) : Prop :=
  ∀ i, (S.dirty i = false → S.mem i = hmemR i H) ∧ (NoHolder S i → S.dirty i = false)

theorem hmemR_lift_other {i j : Nat} (hji : j ≠ i) (v : Region) (o : Option HEvent) (H : HLogR) :
    hmemR i (consO (o.map (lift j v)) H) = hmemR i H := by
  cases o with
  | none => rfl
  | some e => cases e <;> simp [consO, lift, hmemR, hji]

theorem rreplay_di : ∀ {l : RLog} {S : RState} {H : HLogR}, rreplay l = some (S, H) → RDI S H
  | [], S, H, hr => by
    simp [rreplay] at hr; obtain ⟨rfl, rfl⟩ := hr
    intro i; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | e :: l, S', H', hr => by
    obtain ⟨S, H, o, hl, hp, rfl⟩ := rreplay_cons hr
    have ih := rreplay_di hl
    have hinv : ∀ i, Inv (S.lk i) := fun i => replay_inv (rreplay_proj hl i)
    obtain ⟨c, j, k⟩ := e
    intro i
    cases k with
    | tk k =>
      simp only [rstep] at hp
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
            refine ⟨fun _ => by simp [consO, lift, hmemR], fun _ => by simp⟩
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
            simp [consO, lift, hmemR]; exact (ih j).1 hcl
        · -- another lock: nothing of lock `i` changes
          have hk : ∀ b : Bool, (if k = .hold ∨ k = .incNow then upd S.dirty j false else S.dirty) i =
              S.dirty i := by intro _; split <;> simp [upd, Ne.symm hji]
          refine ⟨fun hd => ?_, fun hn => ?_⟩
          · simp only [hk true] at hd
            simp only [hmemR_lift_other hji]; exact (ih i).1 hd
          · simp only [hk true]
            refine (ih i).2 fun d t hd => hn d t ?_
            simp [upd, Ne.symm hji, hd]
    | pull =>
      simp only [rstep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp; exact ih i
      · simp at hp
    | wr k v =>
      simp only [rstep] at hp
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
theorem rreplay_mem : ∀ {l : RLog} {S : RState} {H : HLogR}, rreplay l = some (S, H) →
    ∀ i, S.mem i = memOf i l
  | [], S, H, hr, i => by simp [rreplay] at hr; obtain ⟨rfl, -⟩ := hr; rfl
  | e :: l, S', H', hr, i => by
    obtain ⟨S, H, o, hl, hp, rfl⟩ := rreplay_cons hr
    have ih := rreplay_mem hl i
    obtain ⟨c, j, k⟩ := e
    cases k with
    | tk k =>
      simp only [rstep] at hp
      split at hp
      · simp at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp; simpa [memOf] using ih
    | pull =>
      simp only [rstep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp; simpa [memOf] using ih
      · simp at hp
    | wr k v =>
      simp only [rstep] at hp
      split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        by_cases hji : j = i
        · subst hji; simp [memOf, upd_same, ih]
        · simp [memOf, hji, upd_other _ _ (Ne.symm hji), ih]
      · simp at hp

/-! ## R₁ and what an acquirer sees -/

/-- **R₁ for regions**: each lock's high-level log is a valid atomic-lock log,
with the protocol's holder. -/
theorem rreplay_hreplay {l : RLog} {S : RState} {H : HLogR} (hr : rreplay l = some (S, H)) (i : Nat) :
    ∃ o, hreplay (projH i H) = some o ∧ Holds (S.lk i) o :=
  replay_hreplay (rreplay_proj hr i)

/-- **An acquirer sees the last release.** Until the holder writes, region `i`
is exactly the region the last holder released, every cell of it. -/
theorem acquire_sees {l : RLog} {S : RState} {H : HLogR} (hr : rreplay l = some (S, H)) {i : Nat}
    (hclean : S.dirty i = false) : S.mem i = hmemR i H :=
  (rreplay_di hr i).1 hclean

/-- A free lock's region is the region of its last release. -/
theorem free_region {l : RLog} {S : RState} {H : HLogR} (hr : rreplay l = some (S, H)) {i : Nat}
    (hfree : NoHolder S i) : S.mem i = hmemR i H :=
  (rreplay_di hr i).1 ((rreplay_di hr i).2 hfree)

/-! ## C primitives and a client -/

structure REnv where
  query : CPU → RLog → List REvent
  noSelf : ∀ c l e, e ∈ query c l → e.cpu ≠ c

def rpull (ε : REnv) (c : CPU) (l : RLog) : RLog := ε.query c l ++ l

def noEnvR : REnv := ⟨fun _ _ => [], by intro c l e he; simp at he⟩

inductive RPrim
  | faiTicket | getNow | incNow | hold | pull | rd | wr

def rev (c : CPU) (i : Nat) (k : EvKind) : REvent := ⟨c, i, .tk k⟩

/-- The primitives. `rd(lk, j)` reads cell `j` of the region, and `wr(lk, j, v)`
writes it. Only the holder touches the region, so neither asks the
environment. -/
def rprims (ε : REnv) (c : CPU) : Prims RPrim RLog
  | .faiTicket, [i], l =>
      let l1 := rpull ε c l
      some (BitVec.ofNat 32 (ticket (projL i.toNat l1)), rev c i.toNat .incTicket :: l1)
  | .getNow, [i], l =>
      let l1 := rpull ε c l
      some (BitVec.ofNat 32 (now (projL i.toNat l1)), rev c i.toNat .getNow :: l1)
  | .incNow, [i], l => some (0, rev c i.toNat .incNow :: rpull ε c l)
  | .hold, [i], l => some (0, rev c i.toNat .hold :: rpull ε c l)
  | .pull, [i], l => some (0, ⟨c, i.toNat, .pull⟩ :: rpull ε c l)
  | .rd, [i, j], l => some (memOf i.toNat l j.toNat, l)
  | .wr, [i, j, v], l => some (0, ⟨c, i.toNat, .wr j.toNat v⟩ :: l)
  | _, _, _ => none

def lkR : Expr := .var "lk"
def loopR : Stmt RPrim := .while (.bin .ne (.var "n") (.var "t")) (.call "n" .getNow [lkR])
def acquireR : Stmt RPrim :=
  .seq (.call "t" .faiTicket [lkR])
    (.seq (.call "n" .getNow [lkR]) (.seq loopR (.seq (.call "_" .hold [lkR]) (.call "_" .pull [lkR]))))
def releaseR : Stmt RPrim := .call "_" .incNow [lkR]

/-- Increment cell `j` of the region. -/
def incCell (j : Nat) : Stmt RPrim :=
  .seq (.call "x" .rd [lkR, .const (BitVec.ofNat 32 j)])
    (.call "_" .wr [lkR, .const (BitVec.ofNat 32 j), .bin .add (.var "x") (.const 1)])

/-- Increment cells `0 … k-1`. -/
def incCells : Nat → Stmt RPrim
  | 0 => .skip
  | k + 1 => .seq (incCells k) (incCell k)

/-- A critical section over a whole region: `acquire; cell[j]++ for j < k; release`. -/
def clientR (k : Nat) : Stmt RPrim := .seq acquireR (.seq (incCells k) releaseR)

/-- Run up to `n` steps. -/
def runN (P : Prims RPrim RLog) : Nat → Config RPrim RLog → Config RPrim RLog
  | 0, x => x
  | n + 1, x => match step P x with
    | some y => runN P n y
    | none => x

theorem runN_star (P : Prims RPrim RLog) : ∀ n x, Star P x (runN P n x)
  | 0, x => .refl _
  | n + 1, x => by
    simp only [runN]
    split
    · rename_i y hy; exact .step hy (runN_star P n y)
    · exact .refl _

/-- CPU `c` runs `clientR 3` on lock 0 from log `l`. -/
def runClient (c : CPU) (l : RLog) : Config RPrim RLog :=
  runN (rprims noEnvR c) 60 ⟨clientR 3, .stop, fun x => if x = "lk" then 0 else 0, l⟩

def finished (x : Config RPrim RLog) : Bool :=
  match x.stmt, x.cont with
  | .skip, .stop => true
  | _, _ => false

/-- The log after CPU 0, then CPU 1, each run `clientR 3`. -/
def demoLog : RLog := (runClient 1 (runClient 0 []).abs).abs

/-- **Example**: CPU 0, then CPU 1, each increments the three cells of region 0.
Both finish, the log is valid, and every cell is 2. -/
theorem demo_region :
    (finished (runClient 0 []) && finished (runClient 1 (runClient 0 []).abs) &&
      (rreplay demoLog).isSome && memOf 0 demoLog 0 == 2 && memOf 0 demoLog 1 == 2 &&
      memOf 0 demoLog 2 == 2) = true := by
  decide

end LockRegion
