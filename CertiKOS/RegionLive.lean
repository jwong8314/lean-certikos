import CertiKOS.LockRegionCPU
import CertiKOS.ArrayLive

/-!
# Lock regions on the multicore machine

All CPUs run on one global region log, with no environment. CPU `c` runs
`clientM nc = acquire(L c); cell[j]++ for j < nc; release(L c)` on the lock
`L c`, so CPUs may share locks. This is `ArrayLive.lean` moved to the region
machine: the acquire points are the same, and the critical section now has
points for each cell's read and write.

* `AtW nc`: the program points with a weight (steps left), each tied to the
  lock's ticket state. In the critical section a point also records which
  cell it is at, and that the value just read is the cell's contents.
  `own_stepW`: a CPU's step lowers its weight unless it is spinning, and keeps
  the region log valid (a write is by the holder). `at_otherW`: another CPU's
  event never raises it.
* `reachR`: every multicore run keeps the global invariant `GL`, so **every
  reachable global region log is valid**.
* `region_cs_exclusive`: two CPUs about to read or write the region of the
  same lock are the same CPU.
* `region_fair_terminates`: every `K`-fair run ends within
  `K * (T * (27 + 6 * nc) + 1)` steps.
-/

namespace RegionLive

open ClightL Ticket ClightToPy TicketLive FairC
open LockArray (APrim acquireA loopA lkE upd upd_same upd_other)
open ArrayLinkClient (holdPullS lgEA gnA restS acquireA_eq loopA_eq)
open LockRegion (REvent RLog RState HLogR HEventR RKind Region rreplay rstep rev noEnvR rpull)
open LockRegionCPU (rprimsA incCellA relA)

/-! ## The client and the machine -/

/-- Increment cells `m … m+r-1`. -/
def incFrom : Nat → Nat → Stmt APrim
  | _, 0 => .skip
  | m, r + 1 => .seq (incCellA m) (incFrom (m + 1) r)

def clientM (k : Nat) : Stmt APrim := .seq acquireA (.seq (incFrom 0 k) relA)

/-- What follows `acquire`, the release, and the wait loop's continuation. -/
def KRk (k : Nat) : Cont APrim := .seq (.seq (incFrom 0 k) relA) .stop
def KC : Cont APrim := .seq relA .stop
def KLk (k : Nat) : Cont APrim := .loop lgEA gnA (.seq holdPullS (KRk k))

def rdC (m : Nat) : Stmt APrim := .call "x" .pull [lkE, .const (BitVec.ofNat 32 m)]
def wrC (m : Nat) : Stmt APrim :=
  .call "_" .push [lkE, .const (BitVec.ofNat 32 m), .bin .add (.var "x") (.const 1)]

theorem incCellA_eq (m : Nat) : incCellA m = .seq (rdC m) (wrC m) := rfl

@[simp] theorem rpull_noEnvR (c : CPU) (l : RLog) : rpull noEnvR c l = l := rfl

/-- The multicore region machine: no environment. -/
abbrev PGR : Nat → Prims APrim RLog := fun i => rprimsA noEnvR i

theorem rstep_tk {S : RState} {c : CPU} {i : Nat} {k : EvKind} {p' : PState} {o : Option HEvent}
    (hp : pstep (S.lk i) ⟨c, k⟩ = some (p', o)) :
    rstep S (rev c i k) = some (⟨upd S.lk i p', S.mem,
      if k = .hold ∨ k = .incNow then upd S.dirty i false else S.dirty⟩, o.map (LockRegion.lift i (S.mem i))) := by
  simp [rstep, rev, hp]

theorem rstep_lk {S S' : RState} {e : REvent} {o : Option HEventR} (hp : rstep S e = some (S', o))
    (i : Nat) : S'.lk i = S.lk i ∨ ∃ k o', pstep (S.lk i) ⟨e.cpu, k⟩ = some (S'.lk i, o') := by
  obtain ⟨d, j, k⟩ := e
  cases k with
  | tk k =>
    simp only [rstep] at hp
    split at hp
    · simp at hp
    · rename_i p' o' hps
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      by_cases hji : j = i
      · subst hji; exact .inr ⟨k, o', by simpa using hps⟩
      · exact .inl (by simp [LockArray.upd, Ne.symm hji])
  | pull =>
    simp only [rstep] at hp; split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact .inl rfl
    · simp at hp
  | wr a v =>
    simp only [rstep] at hp; split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact .inl rfl
    · simp at hp

/-- Other CPUs' events leave our phase on every lock alone. -/
theorem others_events {c : CPU} (xs : RLog) {l : RLog} {S S' : RState} {H H' : HLogR}
    (hx : ∀ e ∈ xs, e.cpu ≠ c) (hl : rreplay l = some (S, H)) (hr : rreplay (xs ++ l) = some (S', H')) :
    (∀ i, (S'.lk i).phase c = (S.lk i).phase c) ∧ True :=
  ⟨(LockRegionCPU.rothers (i := 0) hl xs hx hr).1, trivial⟩

variable {nc : Nat}


def wq8 (p : PState) (tn : Nat) (σ : Locals) : Nat :=
  if p.now = tn then (if σ "n" = σ "t" then 14 else 17) else 19
def wq9 (p : PState) (tn : Nat) : Nat := if p.now = tn then 16 else 19
def wq10 (p : PState) (tn : Nat) (σ : Locals) : Nat :=
  if p.now = tn then (if σ "n" = σ "t" then 15 else 18) else 19

/-- CPU `c` on lock `iv` is at a program point consistent with `p`, with weight `w`. -/
inductive AtW (nc : Nat) (iv : Val) (c : CPU) (p : PState) (b : Region) : CThread APrim → Nat → Prop
  | q0 {σ} : σ "lk" = iv → p.phase c = .idle → AtW nc iv c p b ⟨(clientM nc), .stop, σ⟩ (27 + 6 * nc)
  | q1 {σ} : σ "lk" = iv → p.phase c = .idle → AtW nc iv c p b ⟨acquireA, (KRk nc), σ⟩ (26 + 6 * nc)
  | q2 {σ} : σ "lk" = iv → p.phase c = .idle → AtW nc iv c p b ⟨.call "t" .faiTicket [lkE], .seq restS (KRk nc), σ⟩ (25 + 6 * nc)
  | q3 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtW nc iv c p b ⟨.skip, .seq restS (KRk nc), σ⟩ (24 + 6 * nc)
  | q4 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtW nc iv c p b ⟨restS, (KRk nc), σ⟩ (23 + 6 * nc)
  | q5 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtW nc iv c p b ⟨gnA, .seq (.seq loopA holdPullS) (KRk nc), σ⟩ (22 + 6 * nc)
  | q6 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn →
      AtW nc iv c p b ⟨.skip, .seq (.seq loopA holdPullS) (KRk nc), σ⟩ (21 + 6 * nc)
  | q7 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtW nc iv c p b ⟨.seq loopA holdPullS, (KRk nc), σ⟩ (20 + 6 * nc)
  | q8 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn →
      AtW nc iv c p b ⟨loopA, .seq holdPullS (KRk nc), σ⟩ (wq8 p tn σ + 6 * nc)
  | q9 {σ tn} : σ "lk" = iv → Wt c p σ tn → AtW nc iv c p b ⟨gnA, (KLk nc), σ⟩ (wq9 p tn + 6 * nc)
  | q10 {σ tn} : σ "lk" = iv → Wt c p σ tn → NInv σ p tn → AtW nc iv c p b ⟨.skip, (KLk nc), σ⟩ (wq10 p tn σ + 6 * nc)
  | q11 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn → AtW nc iv c p b ⟨.skip, .seq holdPullS (KRk nc), σ⟩ (13 + 6 * nc)
  | q12 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn → AtW nc iv c p b ⟨holdPullS, (KRk nc), σ⟩ (12 + 6 * nc)
  | q13 {σ tn} : σ "lk" = iv → Wt c p σ tn → p.now = tn →
      AtW nc iv c p b ⟨.call "_" .hold [lkE], .seq (.call "v" .pull [lkE]) (KRk nc), σ⟩ (11 + 6 * nc)
  | q14 {σ tn} : σ "lk" = iv → p.phase c = .holding tn →
      AtW nc iv c p b ⟨.skip, .seq (.call "v" .pull [lkE]) (KRk nc), σ⟩ (10 + 6 * nc)
  | q15 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW nc iv c p b ⟨.call "v" .pull [lkE], (KRk nc), σ⟩ (9 + 6 * nc)
  | q16 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW nc iv c p b ⟨.skip, (KRk nc), σ⟩ (8 + 6 * nc)
  | c0 {σ tn} : σ "lk" = iv → p.phase c = .holding tn →
      AtW nc iv c p b ⟨.seq (incFrom 0 nc) relA, .stop, σ⟩ (7 + 6 * nc)
  | c1 {σ tn m r} : σ "lk" = iv → p.phase c = .holding tn → m + r = nc →
      AtW nc iv c p b ⟨incFrom m r, KC, σ⟩ (6 * r + 6)
  | c2 {σ tn m r} : σ "lk" = iv → p.phase c = .holding tn → m + r + 1 = nc →
      AtW nc iv c p b ⟨incCellA m, .seq (incFrom (m + 1) r) KC, σ⟩ (6 * r + 11)
  | c3 {σ tn m r} : σ "lk" = iv → p.phase c = .holding tn → m + r + 1 = nc →
      AtW nc iv c p b ⟨rdC m, .seq (wrC m) (.seq (incFrom (m + 1) r) KC), σ⟩ (6 * r + 10)
  | c4 {σ tn m r} : σ "lk" = iv → p.phase c = .holding tn → m + r + 1 = nc →
      σ "x" = b (BitVec.ofNat 32 m).toNat →
      AtW nc iv c p b ⟨.skip, .seq (wrC m) (.seq (incFrom (m + 1) r) KC), σ⟩ (6 * r + 9)
  | c5 {σ tn m r} : σ "lk" = iv → p.phase c = .holding tn → m + r + 1 = nc →
      σ "x" = b (BitVec.ofNat 32 m).toNat →
      AtW nc iv c p b ⟨wrC m, .seq (incFrom (m + 1) r) KC, σ⟩ (6 * r + 8)
  | c6 {σ tn m r} : σ "lk" = iv → p.phase c = .holding tn → m + r + 1 = nc →
      AtW nc iv c p b ⟨.skip, .seq (incFrom (m + 1) r) KC, σ⟩ (6 * r + 7)
  | q20 {σ tn} : σ "lk" = iv → p.phase c = .holding tn → AtW nc iv c p b ⟨relA, .stop, σ⟩ 1
  | done {σ} : σ "lk" = iv → p.phase c = .idle → AtW nc iv c p b ⟨.skip, .stop, σ⟩ 0

/-- The three points of the wait loop. -/
def InLoopW (t : CThread APrim) : Prop :=
  t.stmt = loopA ∨ ∃ K, t.cont = .loop lgEA gnA K

/-- The region only matters to a holder: it can be replaced by any region that
agrees with it when we hold the lock. -/
theorem atW_mem {iv : Val} {c : CPU} {p : PState} {b b' : Region} {t : CThread APrim} {w : Nat}
    (hb : (∃ tn, p.phase c = .holding tn) → b' = b) (hA : AtW nc iv c p b t w) : AtW nc iv c p b' t w := by
  cases hA with
  | q0 a0 a1 => exact .q0 a0 a1
  | q1 a0 a1 => exact .q1 a0 a1
  | q2 a0 a1 => exact .q2 a0 a1
  | q3 a0 a1 => exact .q3 a0 a1
  | q4 a0 a1 => exact .q4 a0 a1
  | q5 a0 a1 => exact .q5 a0 a1
  | q6 a0 a1 a2 => exact .q6 a0 a1 a2
  | q7 a0 a1 a2 => exact .q7 a0 a1 a2
  | q8 a0 a1 a2 => exact .q8 a0 a1 a2
  | q9 a0 a1 => exact .q9 a0 a1
  | q10 a0 a1 a2 => exact .q10 a0 a1 a2
  | q11 a0 a1 a2 => exact .q11 a0 a1 a2
  | q12 a0 a1 a2 => exact .q12 a0 a1 a2
  | q13 a0 a1 a2 => exact .q13 a0 a1 a2
  | q14 a0 a1 => exact .q14 a0 a1
  | q15 a0 a1 => exact .q15 a0 a1
  | q16 a0 a1 => exact .q16 a0 a1
  | c0 a0 a1 => exact .c0 a0 a1
  | c1 a0 a1 a2 => exact .c1 a0 a1 a2
  | c2 a0 a1 a2 => exact .c2 a0 a1 a2
  | c3 a0 a1 a2 => exact .c3 a0 a1 a2
  | c4 a0 a1 a2 a3 => exact .c4 a0 a1 a2 (by rw [hb ⟨_, a1⟩]; exact a3)
  | c5 a0 a1 a2 a3 => exact .c5 a0 a1 a2 (by rw [hb ⟨_, a1⟩]; exact a3)
  | c6 a0 a1 a2 => exact .c6 a0 a1 a2
  | q20 a0 a1 => exact .q20 a0 a1
  | done a0 a1 => exact .done a0 a1

theorem wq_le (p : PState) (tn : Nat) (σ : Locals) : wq8 p tn σ ≤ 19 ∧ wq9 p tn ≤ 19 ∧ wq10 p tn σ ≤ 19 := by
  unfold wq8 wq9 wq10; refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> omega

theorem at_otherW {iv : Val} {c : CPU} {p p' : PState} {e : Event} {o : Option HEvent}
    {t : CThread APrim} {w : Nat} {b : Region} (hi : Inv p) (hp : pstep p e = some (p', o)) (hne : e.cpu ≠ c)
    (hA : AtW nc iv c p b t w) : ∃ w', w' ≤ w ∧ AtW nc iv c p' b t w' := by
  have hph : p'.phase c = p.phase c := (pstep_other hp hne).1
  have hnow : p.now ≤ p'.now := (pstep_now hp).1
  have hW : ∀ {σ tn}, Wt c p σ tn → Wt c p' σ tn := fun hw => ⟨by rw [hph]; exact hw.1, hw.2⟩
  have hN : ∀ {σ tn}, NInv σ p tn → NInv σ p' tn := fun ⟨v, h1, h2, h3⟩ => ⟨v, by omega, h2, h3⟩
  have hS : ∀ {σ tn}, Wt c p σ tn → p.now = tn → p'.now = tn := fun hw hn =>
    now_stays hi hp hne hw.1 hn
  have hI : p.phase c = .idle → p'.phase c = .idle := fun h => by rw [hph]; exact h
  have hH : ∀ {tn}, p.phase c = .holding tn → p'.phase c = .holding tn := fun h => by rw [hph]; exact h
  have mono : ∀ {σ tn}, Wt c p σ tn → wq8 p' tn σ ≤ wq8 p tn σ ∧ wq9 p' tn ≤ wq9 p tn ∧
      wq10 p' tn σ ≤ wq10 p tn σ := by
    intro σ tn hw
    by_cases h1 : p.now = tn
    · simp [wq8, wq9, wq10, h1, hS hw h1]
    · have := wq_le p' tn σ
      have e8 : wq8 p tn σ = 19 := by simp [wq8, h1]
      have e9 : wq9 p tn = 19 := by simp [wq9, h1]
      have e10 : wq10 p tn σ = 19 := by simp [wq10, h1]
      rw [e8, e9, e10]; exact this
  cases hA with
  | q0 hk h => exact ⟨_, Nat.le_refl _, .q0 hk (hI h)⟩
  | q1 hk h => exact ⟨_, Nat.le_refl _, .q1 hk (hI h)⟩
  | q2 hk h => exact ⟨_, Nat.le_refl _, .q2 hk (hI h)⟩
  | q3 hk hw => exact ⟨_, Nat.le_refl _, .q3 hk (hW hw)⟩
  | q4 hk hw => exact ⟨_, Nat.le_refl _, .q4 hk (hW hw)⟩
  | q5 hk hw => exact ⟨_, Nat.le_refl _, .q5 hk (hW hw)⟩
  | q6 hk hw hn => exact ⟨_, Nat.le_refl _, .q6 hk (hW hw) (hN hn)⟩
  | q7 hk hw hn => exact ⟨_, Nat.le_refl _, .q7 hk (hW hw) (hN hn)⟩
  | q8 hk hw hn => exact ⟨_, Nat.add_le_add_right (mono hw).1 _, .q8 hk (hW hw) (hN hn)⟩
  | q9 hk hw => exact ⟨_, Nat.add_le_add_right (mono hw).2.1 _, .q9 hk (hW hw)⟩
  | q10 hk hw hn => exact ⟨_, Nat.add_le_add_right (mono hw).2.2 _, .q10 hk (hW hw) (hN hn)⟩
  | q11 hk hw h => exact ⟨_, Nat.le_refl _, .q11 hk (hW hw) (hS hw h)⟩
  | q12 hk hw h => exact ⟨_, Nat.le_refl _, .q12 hk (hW hw) (hS hw h)⟩
  | q13 hk hw h => exact ⟨_, Nat.le_refl _, .q13 hk (hW hw) (hS hw h)⟩
  | q14 hk h => exact ⟨_, Nat.le_refl _, .q14 hk (hH h)⟩
  | q15 hk h => exact ⟨_, Nat.le_refl _, .q15 hk (hH h)⟩
  | q16 hk h => exact ⟨_, Nat.le_refl _, .q16 hk (hH h)⟩
  | c0 hk h => exact ⟨_, Nat.le_refl _, .c0 hk (hH h)⟩
  | c1 hk h hm => exact ⟨_, Nat.le_refl _, .c1 hk (hH h) hm⟩
  | c2 hk h hm => exact ⟨_, Nat.le_refl _, .c2 hk (hH h) hm⟩
  | c3 hk h hm => exact ⟨_, Nat.le_refl _, .c3 hk (hH h) hm⟩
  | c4 hk h hm hx => exact ⟨_, Nat.le_refl _, .c4 hk (hH h) hm hx⟩
  | c5 hk h hm hx => exact ⟨_, Nat.le_refl _, .c5 hk (hH h) hm hx⟩
  | c6 hk h hm => exact ⟨_, Nat.le_refl _, .c6 hk (hH h) hm⟩
  | q20 hk h => exact ⟨_, Nat.le_refl _, .q20 hk (hH h)⟩
  | done hk h => exact ⟨_, Nat.le_refl _, .done hk (hI h)⟩

theorem at_othersW {iv : Val} {c : CPU} {t : CThread APrim} :
    ∀ (xs : RLog) {l : RLog} {S S' : RState} {H H' : HLogR} {w : Nat},
      (∀ e ∈ xs, e.cpu ≠ c) → rreplay l = some (S, H) → rreplay (xs ++ l) = some (S', H') →
      AtW nc iv c (S.lk iv.toNat) (S.mem iv.toNat) t w →
      ∃ w', w' ≤ w ∧ AtW nc iv c (S'.lk iv.toNat) (S'.mem iv.toNat) t w'
  | [], l, S, S', H, H', w, _, hl, hr, hA => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact ⟨w, Nat.le_refl _, hA⟩
  | e :: xs, l, S, S', H, H', w, hx, hl, hr, hA => by
    obtain ⟨S2, H2, o, hl2, hp, -⟩ := LockRegion.rreplay_cons hr
    obtain ⟨w2, hw2, hA2⟩ := at_othersW xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2 hA
    obtain ⟨g1, g2⟩ := LockRegionCPU.rstep_other (c := c) (i := iv.toNat)
      (fun d hd hc => LockRegion.rmutex hl2 iv.toNat hd hc) hp (hx e List.mem_cons_self)
    have hmem : (∃ tn, (S2.lk iv.toNat).phase c = .holding tn) → S'.mem iv.toNat = S2.mem iv.toNat :=
      fun hh => (g2 hh).1
    rcases rstep_lk hp iv.toNat with h | ⟨k, o', hps⟩
    · rw [h]; exact ⟨w2, hw2, atW_mem hmem hA2⟩
    · obtain ⟨w', hw', hA'⟩ :=
        at_otherW (replay_inv (LockRegion.rreplay_proj hl2 iv.toNat)) hps (hx e List.mem_cons_self) hA2
      refine ⟨w', by omega, atW_mem (fun hh => ?_) hA'⟩
      exact hmem (by obtain ⟨tn, ht⟩ := hh; exact ⟨tn, by rw [← g1 iv.toNat]; exact ht⟩)

/-! ## Our own step -/

def OutW (nc : Nat) (iv : Val) (c : CPU) (l : RLog) (S : RState) (t : CThread APrim) (w : Nat)
    (c' : Config APrim RLog) : Prop :=
  ∃ S' H' w', rreplay c'.abs = some (S', H') ∧ AtW nc iv c (S'.lk iv.toNat) (S'.mem iv.toNat) (thr c') w' ∧
    (w' < w ∨ (w' = w ∧ ∃ tn, (S.lk iv.toNat).phase c = .waiting tn ∧ (S.lk iv.toNat).now < tn ∧ InLoopW t)) ∧
    ∃ ys, c'.abs = ys ++ l ∧ ∀ e ∈ ys, e.cpu = c ∧ e.lk = iv.toNat

theorem wout_nonev {iv : Val} {c : CPU} {l : RLog} {S : RState} {H : HLogR} {t : CThread APrim}
    {w w' : Nat} {c' : Config APrim RLog} (hl : rreplay l = some (S, H)) (habs : c'.abs = l)
    (hA : AtW nc iv c (S.lk iv.toNat) (S.mem iv.toNat) (thr c') w')
    (hd : w' < w ∨ (w' = w ∧ ∃ tn, (S.lk iv.toNat).phase c = .waiting tn ∧ (S.lk iv.toNat).now < tn ∧ InLoopW t)) :
    OutW nc iv c l S t w c' :=
  ⟨S, H, w', habs ▸ hl, hA, hd, [], by simp [habs], by simp⟩

theorem wout_tk {iv : Val} {c : CPU} {l : RLog} {S : RState} {H : HLogR} {t : CThread APrim}
    {w w' : Nat} {c' : Config APrim RLog} {k : EvKind} {p' : PState} {o : Option HEvent}
    (hl : rreplay l = some (S, H)) (hps : pstep (S.lk iv.toNat) ⟨c, k⟩ = some (p', o))
    (habs : c'.abs = rev c iv.toNat k :: l) (hA : AtW nc iv c p' (S.mem iv.toNat) (thr c') w')
    (hd : w' < w ∨ (w' = w ∧ ∃ tn, (S.lk iv.toNat).phase c = .waiting tn ∧ (S.lk iv.toNat).now < tn ∧ InLoopW t)) :
    OutW nc iv c l S t w c' :=
  ⟨_, _, w', habs ▸ LockRegion.rreplay_cons_of hl (rstep_tk hps), by simpa using hA, hd, [rev c iv.toNat k], habs,
    by simp [rev]⟩

theorem wout_nolk {iv : Val} {c : CPU} {l : RLog} {S S' : RState} {H : HLogR} {t : CThread APrim}
    {w w' : Nat} {c' : Config APrim RLog} {k : RKind} (hl : rreplay l = some (S, H))
    (hps : rstep S ⟨c, iv.toNat, k⟩ = some (S', none)) (hlk : S'.lk = S.lk)
    (habs : c'.abs = ⟨c, iv.toNat, k⟩ :: l) (hA : AtW nc iv c (S.lk iv.toNat) (S'.mem iv.toNat) (thr c') w') (hlt : w' < w) :
    OutW nc iv c l S t w c' :=
  ⟨_, _, w', habs ▸ LockRegion.rreplay_cons_of hl hps, by rw [hlk]; exact hA, .inl hlt, [⟨c, iv.toNat, k⟩], habs,
    by simp⟩

theorem own_stepW {iv : Val} {c : CPU} {l : RLog} {S : RState} {H : HLogR} {t : CThread APrim}
    {w : Nat} {c' : Config APrim RLog} (hc : c < NCPU) (hl : rreplay l = some (S, H))
    (hA : AtW nc iv c (S.lk iv.toNat) (S.mem iv.toNat) t w)
    (hst : ClightL.step (rprimsA noEnvR c) (t.cfg l) = some c') : OutW nc iv c l S t w c' := by
  have hpr := LockRegion.rreplay_proj hl iv.toNat
  have hi := replay_inv hpr
  obtain ⟨hn, htk⟩ := replay_counts hpr
  cases hA with
  | q0 hk hp =>
    simp only [ClightL.step, CThread.cfg, clientM, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q1 hk hp) (.inl (by omega))
  | q1 hk hp =>
    simp only [ClightL.step, CThread.cfg, acquireA_eq, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q2 hk hp) (.inl (by omega))
  | @q2 σ hk hp =>
    simp only [ClightL.step, CThread.cfg, rprimsA, lkE, List.map, Expr.eval, hk, rpull_noEnvR,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .incTicket⟩ = some (⟨(S.lk iv.toNat).ticket + 1,
        (S.lk iv.toNat).now, setPhase (S.lk iv.toNat).phase c (.waiting (S.lk iv.toNat).ticket)⟩, none) := by
      simp [pstep, hc, hp]
    exact wout_tk hl hps rfl (.q3 (tn := (S.lk iv.toNat).ticket) (by simp [hk]) ⟨by simp, by simp [htk]⟩)
      (.inl (by omega))
  | q3 hk hw =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q4 hk hw) (.inl (by omega))
  | q4 hk hw =>
    simp only [ClightL.step, CThread.cfg, restS, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q5 hk hw) (.inl (by omega))
  | @q5 σ tn hk hw =>
    simp only [ClightL.step, CThread.cfg, gnA, rprimsA, lkE, List.map, Expr.eval, hk, rpull_noEnvR,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .getNow⟩ = some (S.lk iv.toNat, none) := by
      simp [pstep, hc, hw.1]
    refine wout_tk hl hps rfl (.q6 (tn := tn) (by simp [hk]) ⟨hw.1, by simp [hw.2]⟩ ?_) (.inl (by omega))
    rw [← hn]; exact nInv_fresh hi hw.1 σ
  | q6 hk hw hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q7 hk hw hni) (.inl (by omega))
  | @q7 σ tn hk hw hni =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q8 hk hw hni) (.inl (Nat.add_lt_add_right (Nat.lt_of_le_of_lt (wq_le _ _ _).1 (by decide)) _))
  | @q8 σ tn hk hw hni =>
    change ClightL.step _ (CThread.cfg ⟨.while lgEA gnA, .seq holdPullS (KRk nc), σ⟩ l) = _ at hst
    rw [cstep_while] at hst
    by_cases hz : lgEA.eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have heq : σ "n" = σ "t" := by rw [lgEA, ne_eval_zero] at hz; simpa [Expr.eval] using hz
      have hnow := nInv_exit hi hw hni heq
      exact wout_nonev hl rfl (.q11 hk hw hnow) (.inl (by simp [wq8, hnow, heq]))
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      have hne : ¬ σ "n" = σ "t" := by
        intro h; apply hz; rw [lgEA, ne_eval_zero]; simpa [Expr.eval] using h
      refine wout_nonev hl rfl (.q9 hk hw) ?_
      by_cases hnow : (S.lk iv.toNat).now = tn
      · left; simp [wq8, wq9, hnow, hne]
      · right; refine ⟨by simp [wq8, wq9, hnow], tn, hw.1, ?_, .inl rfl⟩
        have := hi.waitGe c tn hw.1; omega
  | @q9 σ tn hk hw =>
    simp only [ClightL.step, CThread.cfg, gnA, rprimsA, lkE, List.map, Expr.eval, hk, rpull_noEnvR,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .getNow⟩ = some (S.lk iv.toNat, none) := by
      simp [pstep, hc, hw.1]
    refine wout_tk hl hps rfl (.q10 (tn := tn) (by simp [hk]) ⟨hw.1, by simp [hw.2]⟩
      (by rw [← hn]; exact nInv_fresh hi hw.1 σ)) ?_
    by_cases hnow : (S.lk iv.toNat).now = tn
    · left
      have e2 : BitVec.ofNat 32 (now (LockRegion.projL iv.toNat l)) = σ "t" := by rw [hw.2, ← hn, hnow]
      simp [wq9, wq10, hnow, e2]
    · right; refine ⟨by simp [wq9, wq10, hnow], tn, hw.1, ?_, .inr ⟨_, rfl⟩⟩
      have := hi.waitGe c tn hw.1; omega
  | @q10 σ tn hk hw hni =>
    simp only [ClightL.step, CThread.cfg, KLk, Option.some.injEq] at hst; subst hst
    refine wout_nonev hl rfl (.q8 hk hw hni) ?_
    by_cases hnow : (S.lk iv.toNat).now = tn
    · left; simp only [wq8, wq10, hnow, ite_true]; split <;> omega
    · right; refine ⟨by simp [wq8, wq10, hnow], tn, hw.1, ?_, .inr ⟨_, rfl⟩⟩
      have := hi.waitGe c tn hw.1; omega
  | q11 hk hw h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q12 hk hw h) (.inl (by omega))
  | q12 hk hw h =>
    simp only [ClightL.step, CThread.cfg, holdPullS, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q13 hk hw h) (.inl (by omega))
  | @q13 σ tn hk hw h =>
    simp only [ClightL.step, CThread.cfg, rprimsA, lkE, List.map, Expr.eval, hk, rpull_noEnvR,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .hold⟩ = some (⟨(S.lk iv.toNat).ticket, (S.lk iv.toNat).now,
        setPhase (S.lk iv.toNat).phase c (.holding tn)⟩, some (.acq c)) := by
      simp [pstep, hc, hw.1, h]
    exact wout_tk hl hps rfl (.q14 (tn := tn) (by simp [hk]) (by simp)) (.inl (by omega))
  | q14 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.q15 hk h) (.inl (by omega))
  | @q15 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, rprimsA, lkE, List.map, Expr.eval, hk, rpull_noEnvR,
      Option.some.injEq] at hst
    subst hst
    exact wout_nolk hl (by simp [rstep, LockRegion.Holding, h]) rfl rfl (.q16 (tn := tn) (by simp [hk]) h) (by omega)
  | q16 hk h =>
    simp only [ClightL.step, CThread.cfg, KRk, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.c0 hk h) (.inl (by omega))
  | c0 hk h =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.c1 hk h (by omega)) (.inl (by omega))
  | @c1 σ tn m r hk h hm =>
    cases r with
    | zero =>
      simp only [ClightL.step, CThread.cfg, incFrom, KC, Option.some.injEq] at hst; subst hst
      exact wout_nonev hl rfl (.q20 hk h) (.inl (by omega))
    | succ r =>
      simp only [ClightL.step, CThread.cfg, incFrom, Option.some.injEq] at hst; subst hst
      exact wout_nonev hl rfl (.c2 hk h (by omega)) (.inl (by omega))
  | c2 hk h hm =>
    simp only [ClightL.step, CThread.cfg, incCellA_eq, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.c3 hk h hm) (.inl (by omega))
  | @c3 σ tn m r hk h hm =>
    simp only [ClightL.step, CThread.cfg, rdC, rprimsA, lkE, List.map, Expr.eval, hk,
      Option.some.injEq] at hst
    subst hst
    exact wout_nonev hl rfl (.c4 (tn := tn) (by simp [hk]) h hm
      (by simp [LockRegion.rreplay_mem hl])) (.inl (by omega))
  | c4 hk h hm hx =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.c5 hk h hm hx) (.inl (by omega))
  | @c5 σ tn m r hk h hm hx =>
    simp only [ClightL.step, CThread.cfg, wrC, rprimsA, lkE, List.map, Expr.eval, hk,
      Option.some.injEq] at hst
    subst hst
    exact wout_nolk (S' := ⟨S.lk, upd S.mem iv.toNat (LockRegion.setCell (S.mem iv.toNat)
        (BitVec.ofNat 32 m).toNat (BinOp.eval .add (σ "x") 1)), upd S.dirty iv.toNat true⟩) hl
      (by simp [rstep, LockRegion.Holding, h]) rfl rfl (.c6 (tn := tn) (by simp [hk]) h hm) (by omega)
  | c6 hk h hm =>
    simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
    exact wout_nonev hl rfl (.c1 hk h (by omega)) (.inl (by omega))
  | @q20 σ tn hk h =>
    simp only [ClightL.step, CThread.cfg, relA, rprimsA, lkE, List.map, Expr.eval, hk, rpull_noEnvR,
      Option.some.injEq] at hst
    subst hst
    have hps : pstep (S.lk iv.toNat) ⟨c, .incNow⟩ = some (⟨(S.lk iv.toNat).ticket, (S.lk iv.toNat).now + 1,
        setPhase (S.lk iv.toNat).phase c .idle⟩, some (.rel c)) := by
      simp [pstep, hc, h]
    exact wout_tk hl hps rfl (.done (by simp [hk]) (by simp)) (.inl (by omega))
  | done hk h => simp [ClightL.step, CThread.cfg] at hst

/-! ## Facts about the global log -/

/-- CPUs that never act stay idle on every lock. -/
theorem idle_beyond {T : Nat} : ∀ {l : RLog} {S : RState} {H : HLogR}, (∀ e ∈ l, e.cpu < T) →
    rreplay l = some (S, H) → ∀ d, T ≤ d → ∀ j, (S.lk j).phase d = .idle
  | [], S, H, _, hr, d, _, j => by simp [rreplay] at hr; obtain ⟨rfl, -⟩ := hr; rfl
  | e :: l, S', H', hev, hr, d, hd, j => by
    obtain ⟨S, H, o, hl, hp, -⟩ := LockRegion.rreplay_cons hr
    have ih := idle_beyond (fun e' he' => hev e' (List.mem_cons_of_mem _ he')) hl d hd j
    have hne : e.cpu ≠ d := Nat.ne_of_lt (Nat.lt_of_lt_of_le (hev e List.mem_cons_self) hd)
    rcases rstep_lk hp j with h | ⟨k, o', hps⟩
    · rw [h]; exact ih
    · rw [(pstep_other hps hne).1]; exact ih

theorem now_ext {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) :
    ∀ (ys : RLog) {S' : RState} {H' : HLogR}, rreplay (ys ++ l) = some (S', H') →
      ∀ j, (S.lk j).now ≤ (S'.lk j).now
  | [], S', H', hr, j => by simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact Nat.le_refl _
  | e :: ys, S', H', hr, j => by
    obtain ⟨S2, H2, o, hl2, hp, -⟩ := LockRegion.rreplay_cons hr
    have ih := now_ext hl ys hl2 j
    rcases rstep_lk hp j with h | ⟨k, o', hps⟩
    · rw [h]; exact ih
    · exact Nat.le_trans ih (pstep_now hps).1

theorem lk_frame {i : Nat} {l : RLog} {S : RState} {H : HLogR} (hl : rreplay l = some (S, H)) :
    ∀ (ys : RLog), (∀ e ∈ ys, e.lk = i) → ∀ {S' : RState} {H' : HLogR}, rreplay (ys ++ l) = some (S', H') →
      ∀ j, j ≠ i → S'.lk j = S.lk j
  | [], _, S', H', hr, j, _ => by simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; rfl
  | e :: ys, hy, S', H', hr, j, hj => by
    obtain ⟨S2, H2, o, hl2, hp, -⟩ := LockRegion.rreplay_cons hr
    have ih := lk_frame hl ys (fun e' he' => hy e' (List.mem_cons_of_mem _ he')) hl2 j hj
    rw [← ih]
    obtain ⟨d, j', k⟩ := e
    have hj' : j' = i := hy _ List.mem_cons_self
    cases k with
    | tk k =>
      simp only [rstep] at hp
      split at hp
      · simp at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, -⟩ := hp
        simp [LockArray.upd, hj', hj]
    | pull =>
      simp only [rstep] at hp; split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; rfl
      · simp at hp
    | wr a v =>
      simp only [rstep] at hp; split at hp
      · simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; rfl
      · simp at hp

theorem atW_done {iv : Val} {c : CPU} {p : PState} {t : CThread APrim} {w : Nat} (hA : AtW nc iv c p b t w)
    (hd : Done t) : p.phase c = .idle := by
  obtain ⟨h1, h2⟩ := hd
  cases hA <;> simp_all [KRk, KLk, KC, clientM, incFrom, incCellA_eq, rdC, wrC, relA, acquireA, restS, gnA, holdPullS, loopA, lgEA]

/-! ## The global potential -/

def GL (nc T : Nat) (L : Nat → Val) (cs : List (CThread APrim)) (l : RLog) (Φ : Nat) : Prop :=
  ∃ S H, ∃ ws : Nat → Nat, rreplay l = some (S, H) ∧ cs.length = T ∧ T ≤ NCPU ∧ (∀ e ∈ l, e.cpu < T) ∧
    (∀ c (hc : c < cs.length), AtW nc (L c) c (S.lk (L c).toNat) (S.mem (L c).toNat) cs[c] (ws c)) ∧
    (∀ c, c < T → ∀ j, j ≠ (L c).toNat → (S.lk j).phase c = .idle) ∧ Φ = sumTo ws T

def SpinsW (L : Nat → Val) (cs : List (CThread APrim)) (l : RLog) (d : Nat) : Prop :=
  ∃ (hd : d < cs.length) (S : RState) (H : HLogR) (tn : Nat), rreplay l = some (S, H) ∧
    (S.lk (L d).toNat).phase d = .waiting tn ∧ (S.lk (L d).toNat).now < tn ∧ InLoopW cs[d]

def ActW (L : Nat → Val) (cs : List (CThread APrim)) (l : RLog) (d : Nat) : Prop :=
  ∃ hd : d < cs.length, ¬ Done cs[d] ∧ ¬ SpinsW L cs l d

theorem gstepW {T : Nat} {L : Nat → Val} {cs cs' : List (CThread APrim)} {l l' : RLog} {Φ a : Nat}
    (hG : GL nc T L cs l Φ) (hS : CStepI PGR a cs l cs' l') :
    ∃ Φ', GL nc T L cs' l' Φ' ∧ Φ' ≤ Φ ∧ (¬ SpinsW L cs l a → Φ' < Φ) ∧
      (∀ d, d ≠ a → SpinsW L cs' l' d → SpinsW L cs l d) := by
  obtain ⟨S, H, ws, hl, hlen, hT, hev, hAt, hidle, rfl⟩ := hG
  obtain ⟨ha, c', hst, rfl, rfl⟩ := hS
  have haT : a < T := hlen ▸ ha
  have haN : a < NCPU := Nat.lt_of_lt_of_le haT hT
  obtain ⟨S', H', w', hr', hA', hdec, ys, hys, hown⟩ := own_stepW haN hl (hAt a ha) hst
  have hr'' : rreplay (ys ++ l) = some (S', H') := hys ▸ hr'
  have hx : ∀ d, d ≠ a → ∀ e ∈ ys, e.cpu ≠ d := fun d hd e he => by rw [(hown e he).1]; exact Ne.symm hd
  -- the other CPUs' new weights
  have hch : ∀ d, ∃ w'', ∀ hd : d < cs.length, d ≠ a → w'' ≤ ws d ∧
      AtW nc (L d) d (S'.lk (L d).toNat) (S'.mem (L d).toNat) cs[d] w'' := by
    intro d
    by_cases hd : d < cs.length
    · by_cases hda : d = a
      · exact ⟨0, fun _ h => absurd hda h⟩
      · obtain ⟨w'', h1, h2⟩ := at_othersW ys (hx d hda) hl hr'' (hAt d hd)
        exact ⟨w'', fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hd⟩
  let ws' : Nat → Nat := fun d => if d = a then w' else Classical.choose (hch d)
  have hws' : ∀ d (hd : d < cs.length), d ≠ a → ws' d ≤ ws d ∧ AtW nc (L d) d (S'.lk (L d).toNat) (S'.mem (L d).toNat) cs[d] (ws' d) :=
    fun d hd hda => by simp only [ws', hda, ite_false]; exact Classical.choose_spec (hch d) hd hda
  have hwa : ws' a = w' := by simp [ws']
  have hle : ∀ d, d < T → ws' d ≤ ws d := fun d hd => by
    by_cases hda : d = a
    · subst hda; rw [hwa]; rcases hdec with h | ⟨h, -⟩ <;> omega
    · exact (hws' d (hlen ▸ hd) hda).1
  refine ⟨sumTo ws' T, ⟨S', H', ws', hr', by simpa using hlen, hT, fun e he => ?_, fun c hc => ?_,
    fun c hc j hj => ?_, rfl⟩, sumTo_le T hle, fun hns => ?_, fun d hda hsp => ?_⟩
  · rw [hys] at he
    rcases List.mem_append.1 he with he | he
    · rw [(hown e he).1]; exact haT
    · exact hev e he
  · by_cases hca : c = a
    · subst hca; simp only [List.getElem_set_self]; rw [hwa]; simpa using hA'
    · have hc' : c < cs.length := by simpa using hc
      simp only [List.getElem_set_ne (Ne.symm hca)]
      exact (hws' c hc' hca).2
  · by_cases hca : c = a
    · subst hca
      rw [lk_frame hl ys (fun e he => (hown e he).2) hr'' j hj]
      exact hidle c hc j hj
    · rw [(others_events ys (hx c hca) hl hr'').1 j]
      exact hidle c hc j hj
  · refine sumTo_lt (i := a) T hle haT ?_
    rw [hwa]
    rcases hdec with h | ⟨-, tn, h1, h2, h3⟩
    · exact h
    · exact absurd ⟨ha, S, H, tn, hl, h1, h2, h3⟩ hns
  · obtain ⟨hd', S2, H2, tn, hl2, h1, h2, h3⟩ := hsp
    rw [hr'] at hl2; cases hl2
    have hd : d < cs.length := by simpa using hd'
    have hph := (others_events ys (hx d hda) hl hr'').1 (L d).toNat
    have hnow := now_ext hl ys hr'' (L d).toNat
    refine ⟨hd, S, H, tn, hl, by rw [← hph]; exact h1, by omega, ?_⟩
    simpa [List.getElem_set_ne (Ne.symm hda)] using h3

theorem act_existsW {T : Nat} {L : Nat → Val} {cs : List (CThread APrim)} {l : RLog} {Φ : Nat}
    (hG : GL nc T L cs l Φ) (hu : ∃ i, ∃ hi : i < cs.length, ¬ Done cs[i]) : ∃ d, ActW L cs l d := by
  refine Classical.byContradiction fun hno => ?_
  have hall : ∀ d (hd : d < cs.length), ¬ Done cs[d] → SpinsW L cs l d := fun d hd hnd =>
    Classical.byContradiction fun hs => hno ⟨d, hd, hnd, hs⟩
  obtain ⟨S, H, ws, hl, hlen, hT, hev, hAt, hidle, -⟩ := hG
  obtain ⟨i, hi, hnd⟩ := hu
  obtain ⟨-, S2, H2, tn, hl2, hw, hlt, -⟩ := hall i hi hnd
  rw [hl] at hl2; cases hl2
  -- the owner of the ticket being served on that lock
  obtain ⟨k, hk⟩ : ∃ k, k = (L i).toNat := ⟨_, rfl⟩
  rw [← hk] at hw hlt
  have hp := LockRegion.rreplay_proj hl k
  have hinv := replay_inv hp
  have htk := hinv.tkLt i tn (by simp [hw, Phase.tk])
  obtain ⟨d, hd⟩ := replay_cover hp (S.lk k).now (Nat.le_refl _) (by omega)
  have hdT : d < T := Nat.lt_of_not_le fun hge => by
    rw [idle_beyond hev hl d hge k] at hd; simp [Phase.tk] at hd
  have hkd : k = (L d).toNat := Classical.byContradiction fun hne => by
    rw [hidle d hdT k hne] at hd; simp [Phase.tk] at hd
  have hd' : d < cs.length := by rw [hlen]; exact hdT
  have hndd : ¬ Done cs[d] := fun hdn => by
    have := atW_done (hAt d hd') hdn
    rw [← hkd] at this; rw [this] at hd; simp [Phase.tk] at hd
  obtain ⟨-, S3, H3, tn', hl3, hw', hlt', -⟩ := hall d hd' hndd
  rw [hl] at hl3; cases hl3
  rw [← hkd] at hw' hlt'
  rw [hw'] at hd; simp [Phase.tk] at hd; omega

theorem certR (nc T : Nat) (L : Nat → Val) : LiveCert PGR (GL nc T L) (ActW L) where
  le := fun hG hS => let ⟨Φ', h1, h2, _, _⟩ := gstepW hG hS; ⟨Φ', h2, h1⟩
  lt := fun hG hA hS => by
    obtain ⟨Φ', h1, -, h3, -⟩ := gstepW hG hS
    obtain ⟨_, _, hns⟩ := hA
    exact ⟨Φ', h3 hns, h1⟩
  persist := fun {cs a Φ i d cs' a'} hG hA hS hid => by
    obtain ⟨-, -, -, -, hsp⟩ := gstepW hG hS
    obtain ⟨hd, hnd, hns⟩ := hA
    obtain ⟨hd', hcs⟩ := hS.other hd hid
    exact ⟨hd', by rw [hcs]; exact hnd, fun h => hns (hsp d (Ne.symm hid) h)⟩
  act := fun hG hu => act_existsW hG hu
  act_lt := fun _ hA => let ⟨hd, hnd, _⟩ := hA; ⟨hd, hnd⟩

/-- `T` CPUs; CPU `c` runs the client on lock `L c`. -/
def poolR (nc T : Nat) (L : Nat → Val) : List (CThread APrim) :=
  (List.range T).map fun c => ⟨clientM nc, .stop, fun z => if z = "lk" then L c else 0⟩

theorem gl_init (nc T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) :
    GL nc T L (poolR nc T L) [] (T * (27 + 6 * nc)) := by
  refine ⟨_, _, fun _ => 27 + 6 * nc, rfl, by simp [poolR], hT, by simp, fun c hc => ?_, fun c _ j _ => rfl,
    (sumTo_const _ _).symm⟩
  simp only [poolR, List.getElem_map, List.getElem_range]
  exact .q0 (by simp) rfl

/-- **Liveness of lock regions on the multicore machine.** -/
theorem region_fair_terminates (nc T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) (r : GRun PGR)
    (h0 : r.cs 0 = poolR nc T L) (hl0 : r.ab 0 = []) {K : Nat} (hK : 0 < K) (hF : r.Fair K) :
    r.len < K * (T * (27 + 6 * nc) + 1) :=
  fair_terminates (certR nc T L) r hK (by rw [h0, hl0]; exact gl_init nc T L hT) hF

/-! ## Safety: validity and mutual exclusion -/

/-- **Every multicore run keeps the invariant**, so every reachable log is valid. -/
theorem reachR (nc T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) {cs : List (CThread APrim)} {l : RLog}
    (h : CSteps PGR (poolR nc T L) [] cs l) : ∃ Φ, GL nc T L cs l Φ := by
  suffices ∀ {a b la lb}, CSteps PGR a la b lb → ∀ Φ, GL nc T L a la Φ → ∃ Φ', GL nc T L b lb Φ' from
    this h _ (gl_init nc T L hT)
  intro a b la lb hab
  induction hab with
  | refl => exact fun Φ hG => ⟨Φ, hG⟩
  | step hs _ ih =>
    intro Φ hG
    obtain ⟨i, hi, hst⟩ := hs
    obtain ⟨Φ', hG', -⟩ := gstepW hG ⟨hi, _, hst, rfl, rfl⟩
    exact ih Φ' hG'

/-- About to read or write a cell of the region. -/
def Touching (t : CThread APrim) : Prop :=
  (∃ x a b, t.stmt = .call x .pull [a, b]) ∨ (∃ x a b d, t.stmt = .call x .push [a, b, d])

theorem at_touch {iv : Val} {c : CPU} {p : PState} {b : Region} {t : CThread APrim} {w : Nat}
    (hA : AtW nc iv c p b t w) (ht : Touching t) : ∃ tn, p.phase c = .holding tn := by
  cases hA <;> first
    | exact ⟨_, ‹_›⟩
    | (exfalso; simp_all [Touching, clientM, incFrom, incCellA_eq, relA, acquireA, restS, gnA, holdPullS,
        loopA, lkE])

/-- **Mutual exclusion for regions on the multicore machine.** Two CPUs about
to read or write the region of the same lock are the same CPU. -/
theorem region_cs_exclusive (nc T : Nat) (L : Nat → Val) (hT : T ≤ NCPU) {cs : List (CThread APrim)}
    {l : RLog} (h : CSteps PGR (poolR nc T L) [] cs l) (c d : Nat) (hc : c < cs.length) (hd : d < cs.length)
    (hL : (L c).toNat = (L d).toNat) (hcc : Touching cs[c]) (hdc : Touching cs[d]) : c = d := by
  obtain ⟨Φ, S, H, ws, hl, -, -, -, hAt, -⟩ := reachR nc T L hT h
  have h1 : LockRegion.Holding S c (L c).toNat := at_touch (hAt c hc) hcc
  have h2 : LockRegion.Holding S d (L c).toNat := by rw [hL]; exact at_touch (hAt d hd) hdc
  exact LockRegion.rmutex hl _ h1 h2

end RegionLive
