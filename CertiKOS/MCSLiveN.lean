import CertiKOS.MCSLive

/-!
# The MCS lock on the multicore machine, with a critical section

`MCSLive.lean` with a critical section. Each CPU runs
`acquireM; critM n; releaseM`, where `critM n` is `n` assignments. It is the
erasure of the bounded client's `n` memory calls (`MCSBoundC.critB`).

* `AtWN n`: the program points of `MCSLive.AtWM`, plus four points in the
  critical section (`c0`–`c3`), all in phase `holding`. The weights before
  the critical section go up by `3n + 2`.
* `mcsN_fair_terminates`: every `K`-fair run of `T ≤ NCPU` CPUs ends within
  `K * (T * (3n + 43) + 1)` steps.
* `reachN`: every multicore run keeps the global invariant `GLM`.
  `multicore_cs_exclusiveN`: two CPUs in their critical sections (from the
  end of `acquireM` to the start of `releaseM`) are the same CPU.
-/

namespace MCSLiveN

open ClightL Ticket ClightToPy MCS LinkM TicketLive MCSLink FairC

/-- The erased critical section: `n` assignments. -/
def critM : Nat → Stmt MPrim
  | 0 => .skip
  | k + 1 => .seq (.assign "_" (.const 0)) (critM k)

/-- What follows `acquireM`. -/
def KRn (n : Nat) : Cont MPrim := .seq (.seq (critM n) releaseM) .stop
def KC : Cont MPrim := .seq releaseM .stop
def codeN (n : Nat) : Stmt MPrim := .seq acquireM (.seq (critM n) releaseM)
/-- The `busy` loop's continuation. -/
def KLBn (n : Nat) : Cont MPrim := .loop (.bin .ne (.var "b") (.const 0)) gbC (.seq holdC (KRn n))

variable {n : Nat}


def w5 (σ : Locals) : Nat := if σ "p" = 0 then 24 else 36
def w12 (s : MS) (c : CPU) (σ : Locals) : Nat := if s.busy c then 29 else if σ "b" = 0 then 24 else 27
def w13 (s : MS) (c : CPU) : Nat := if s.busy c then 29 else 26
def w14 (s : MS) (c : CPU) (σ : Locals) : Nat := if s.busy c then 29 else if σ "b" = 0 then 25 else 28
def w21 (σ : Locals) : Nat := if σ "n" = 0 then 17 else 2
def w26 (σ : Locals) : Nat := if σ "k" = 0 then 13 else 1
def w31 (s : MS) (c : CPU) (σ : Locals) : Nat :=
  if s.next c = none then 8 else if σ "n" = 0 then 6 else 3
def w32 (s : MS) (c : CPU) : Nat := if s.next c = none then 8 else 5
def w33 (s : MS) (c : CPU) (σ : Locals) : Nat :=
  if s.next c = none then 8 else if σ "n" = 0 then 7 else 4

/-- The `cas` result, and the queue behind us if it failed. -/
def CasR (s : MS) (c : CPU) (σ : Locals) : Prop :=
  (σ "k" ≠ 0 ∧ s.ph c = .idle) ∨ (σ "k" = 0 ∧ s.ph c = .holding ∧ s.hd + 1 < s.tl)

inductive AtWN (n : Nat) (c : CPU) (s : MS) : CThread MPrim → Nat → Prop
  | a0 {σ} : s.ph c = .idle → AtWN n c s ⟨(codeN n), .stop, σ⟩ (41 + (3 * n + 2))
  | a1 {σ} : s.ph c = .idle → AtWN n c s ⟨acquireM, (KRn n), σ⟩ (40 + (3 * n + 2))
  | a2 {σ} : s.ph c = .idle → AtWN n c s ⟨.call "p" .swap [], .seq REST (KRn n), σ⟩ (39 + (3 * n + 2))
  | a3 {σ} : FrontOrLink s c σ → AtWN n c s ⟨.skip, .seq REST (KRn n), σ⟩ (w5 σ + 2 + (3 * n + 2))
  | a4 {σ} : FrontOrLink s c σ → AtWN n c s ⟨REST, (KRn n), σ⟩ (w5 σ + 1 + (3 * n + 2))
  | a5 {σ} : FrontOrLink s c σ → AtWN n c s ⟨ITE, .seq holdC (KRn n), σ⟩ (w5 σ + (3 * n + 2))
  | a6 {σ} : IsLinking s c → AtWN n c s ⟨.seq linkC (.seq gbC loopB), .seq holdC (KRn n), σ⟩ (35 + (3 * n + 2))
  | a7 {σ} : IsLinking s c → AtWN n c s ⟨linkC, .seq (.seq gbC loopB) (.seq holdC (KRn n)), σ⟩ (34 + (3 * n + 2))
  | a8 {σ} : s.ph c = .waiting → AtWN n c s ⟨.skip, .seq (.seq gbC loopB) (.seq holdC (KRn n)), σ⟩ (33 + (3 * n + 2))
  | a9 {σ} : s.ph c = .waiting → AtWN n c s ⟨.seq gbC loopB, .seq holdC (KRn n), σ⟩ (32 + (3 * n + 2))
  | a10 {σ} : s.ph c = .waiting → AtWN n c s ⟨gbC, .seq loopB (.seq holdC (KRn n)), σ⟩ (31 + (3 * n + 2))
  | a11 {σ} : s.ph c = .waiting → BI s c σ → AtWN n c s ⟨.skip, .seq loopB (.seq holdC (KRn n)), σ⟩ (30 + (3 * n + 2))
  | a12 {σ} : s.ph c = .waiting → BI s c σ → AtWN n c s ⟨loopB, .seq holdC (KRn n), σ⟩ (w12 s c σ + (3 * n + 2))
  | a13 {σ} : s.ph c = .waiting → AtWN n c s ⟨gbC, (KLBn n), σ⟩ (w13 s c + (3 * n + 2))
  | a14 {σ} : s.ph c = .waiting → BI s c σ → AtWN n c s ⟨.skip, (KLBn n), σ⟩ (w14 s c σ + (3 * n + 2))
  | a15 {σ} : Ready s c → AtWN n c s ⟨.skip, .seq holdC (KRn n), σ⟩ (23 + (3 * n + 2))
  | a16 {σ} : Ready s c → AtWN n c s ⟨holdC, (KRn n), σ⟩ (22 + (3 * n + 2))
  | a17 {σ} : s.ph c = .holding → AtWN n c s ⟨.skip, (KRn n), σ⟩ (21 + (3 * n + 2))
  | a18 {σ} : s.ph c = .holding → AtWN n c s ⟨releaseM, .stop, σ⟩ 20
  | a19 {σ} : s.ph c = .holding → AtWN n c s ⟨gnC, .seq RITE .stop, σ⟩ 19
  | a20 {σ} : s.ph c = .holding → NI s c σ → AtWN n c s ⟨.skip, .seq RITE .stop, σ⟩ (w21 σ + 1)
  | a21 {σ} : s.ph c = .holding → NI s c σ → AtWN n c s ⟨RITE, .stop, σ⟩ (w21 σ)
  | a22 {σ} : s.ph c = .holding → s.next c ≠ none → AtWN n c s ⟨hoC, .stop, σ⟩ 1
  | a23 {σ} : s.ph c = .holding → AtWN n c s ⟨TAIL, .stop, σ⟩ 16
  | a24 {σ} : s.ph c = .holding → AtWN n c s ⟨.call "k" .cas [], .seq KITE .stop, σ⟩ 15
  | a25 {σ} : CasR s c σ → AtWN n c s ⟨.skip, .seq KITE .stop, σ⟩ (w26 σ + 1)
  | a26 {σ} : CasR s c σ → AtWN n c s ⟨KITE, .stop, σ⟩ (w26 σ)
  | a27 {σ} : s.ph c = .holding → s.hd + 1 < s.tl → AtWN n c s ⟨.seq gnC (.seq loopN hoC), .stop, σ⟩ 12
  | a28 {σ} : s.ph c = .holding → s.hd + 1 < s.tl → AtWN n c s ⟨gnC, .seq (.seq loopN hoC) .stop, σ⟩ 11
  | a29 {σ} : s.ph c = .holding → s.hd + 1 < s.tl → NI s c σ → AtWN n c s ⟨.skip, .seq (.seq loopN hoC) .stop, σ⟩ 10
  | a30 {σ} : s.ph c = .holding → s.hd + 1 < s.tl → NI s c σ → AtWN n c s ⟨.seq loopN hoC, .stop, σ⟩ 9
  | a31 {σ} : s.ph c = .holding → s.hd + 1 < s.tl → NI s c σ → AtWN n c s ⟨loopN, .seq hoC .stop, σ⟩ (w31 s c σ)
  | a32 {σ} : s.ph c = .holding → s.hd + 1 < s.tl → AtWN n c s ⟨gnC, KLN, σ⟩ (w32 s c)
  | a33 {σ} : s.ph c = .holding → s.hd + 1 < s.tl → NI s c σ → AtWN n c s ⟨.skip, KLN, σ⟩ (w33 s c σ)
  | a34 {σ} : s.ph c = .holding → s.next c ≠ none → AtWN n c s ⟨.skip, .seq hoC .stop, σ⟩ 2
  | c0 {σ} : s.ph c = .holding → AtWN n c s ⟨.seq (critM n) releaseM, .stop, σ⟩ (3 * n + 22)
  | c1 {σ k} : s.ph c = .holding → AtWN n c s ⟨critM k, KC, σ⟩ (3 * k + 21)
  | c2 {σ k} : s.ph c = .holding → AtWN n c s ⟨.assign "_" (.const 0), .seq (critM k) KC, σ⟩ (3 * k + 23)
  | c3 {σ k} : s.ph c = .holding → AtWN n c s ⟨.skip, .seq (critM k) KC, σ⟩ (3 * k + 22)
  | done {σ} : s.ph c = .idle → AtWN n c s ⟨.skip, .stop, σ⟩ 0

/-! ## Another CPU's event -/

/-- While `c` holds the lock, nobody else can move `hd`, and `tl` only grows. -/
theorem mstep_other_hold {s s' : MS} {e : MEvent} {o : Option HEvent} {c : CPU} (hi : MInv s)
    (hp : mstep s e = some (s', o)) (hne : e.cpu ≠ c) (hh : s.ph c = .holding) :
    s'.hd = s.hd ∧ s.tl ≤ s'.tl := by
  obtain ⟨d, k⟩ := e
  simp only at hne
  simp only [mstep] at hp
  split at hp
  case isFalse => simp at hp
  cases k <;> cases hph : s.ph d <;> simp only [hph] at hp <;> try simp at hp
  all_goals first
    | (obtain ⟨rfl, -⟩ := hp; exact ⟨rfl, by simp⟩)
    | (obtain ⟨-, rfl, -⟩ := hp; exact ⟨rfl, Nat.le_refl _⟩)
    | (obtain ⟨rfl, -⟩ := hp; exact ⟨rfl, Nat.le_refl _⟩)
    | skip
  all_goals (split at hp <;> (try simp at hp))
  all_goals first
    | (exfalso; exact hne (hi.mutex hph hh))
    | (simp only [Option.some.injEq, Prod.mk.injEq] at hp; obtain ⟨rfl, -⟩ := hp; exact ⟨rfl, Nat.le_refl _⟩)

theorem at_otherWM {c : CPU} {s s' : MS} {e : MEvent} {o : Option HEvent} {t : CThread MPrim} {w : Nat}
    (hi : MInv s) (hp : mstep s e = some (s', o)) (hne : e.cpu ≠ c) (hA : AtWN n c s t w) :
    ∃ w', w' ≤ w ∧ AtWN n c s' t w' := by
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
  have hQ : s.ph c = .holding → s.hd + 1 < s.tl → s'.hd + 1 < s'.tl := fun h h' => by
    obtain ⟨e1, e2⟩ := mstep_other_hold hi hp hne h; omega
  have hC : ∀ {σ}, CasR s c σ → CasR s' c σ := fun h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact .inl ⟨h1, hI h2⟩
    · exact .inr ⟨h1, hH h2, hQ h2 h3⟩
  -- weights of the spin loops only go down
  have bmono : (s.busy c = false → s'.busy c = false) := hb
  have m12 : ∀ {σ}, s.ph c = .waiting → w12 s' c σ ≤ w12 s c σ := fun _ => by
    unfold w12; cases h1 : s.busy c
    · simp [bmono h1]
    · simp only [ite_true]; split <;> (try split) <;> omega
  have m13 : s.ph c = .waiting → w13 s' c ≤ w13 s c := fun _ => by
    unfold w13; cases h1 : s.busy c
    · simp [bmono h1]
    · simp only [ite_true]; split <;> omega
  have m14 : ∀ {σ}, s.ph c = .waiting → w14 s' c σ ≤ w14 s c σ := fun _ => by
    unfold w14; cases h1 : s.busy c
    · simp [bmono h1]
    · simp only [ite_true]; split <;> (try split) <;> omega
  have m31 : ∀ {σ}, s.ph c = .holding → w31 s' c σ ≤ w31 s c σ := fun _ => by
    unfold w31; by_cases h1 : s.next c = none
    · simp only [h1, ite_true]; split <;> (try split) <;> omega
    · rw [hn h1]; exact Nat.le_refl _
  have m32 : s.ph c = .holding → w32 s' c ≤ w32 s c := fun _ => by
    unfold w32; by_cases h1 : s.next c = none
    · simp only [h1, ite_true]; split <;> omega
    · rw [hn h1]; exact Nat.le_refl _
  have m33 : ∀ {σ}, s.ph c = .holding → w33 s' c σ ≤ w33 s c σ := fun _ => by
    unfold w33; by_cases h1 : s.next c = none
    · simp only [h1, ite_true]; split <;> (try split) <;> omega
    · rw [hn h1]; exact Nat.le_refl _
  cases hA with
  | a0 h0 => exact ⟨_, (Nat.le_refl _), .a0 (hI h0)⟩
  | a1 h0 => exact ⟨_, (Nat.le_refl _), .a1 (hI h0)⟩
  | a2 h0 => exact ⟨_, (Nat.le_refl _), .a2 (hI h0)⟩
  | a3 h0 => exact ⟨_, (Nat.le_refl _), .a3 (hFL h0)⟩
  | a4 h0 => exact ⟨_, (Nat.le_refl _), .a4 (hFL h0)⟩
  | a5 h0 => exact ⟨_, (Nat.le_refl _), .a5 (hFL h0)⟩
  | a6 h0 => exact ⟨_, (Nat.le_refl _), .a6 (hL h0)⟩
  | a7 h0 => exact ⟨_, (Nat.le_refl _), .a7 (hL h0)⟩
  | a8 h0 => exact ⟨_, (Nat.le_refl _), .a8 (hWt h0)⟩
  | a9 h0 => exact ⟨_, (Nat.le_refl _), .a9 (hWt h0)⟩
  | a10 h0 => exact ⟨_, (Nat.le_refl _), .a10 (hWt h0)⟩
  | a11 h0 h1 => exact ⟨_, (Nat.le_refl _), .a11 (hWt h0) (hB h1)⟩
  | a12 h0 h1 => exact ⟨_, (Nat.add_le_add_right (m12 h0) _), .a12 (hWt h0) (hB h1)⟩
  | a13 h0 => exact ⟨_, (Nat.add_le_add_right (m13 h0) _), .a13 (hWt h0)⟩
  | a14 h0 h1 => exact ⟨_, (Nat.add_le_add_right (m14 h0) _), .a14 (hWt h0) (hB h1)⟩
  | a15 h0 => exact ⟨_, (Nat.le_refl _), .a15 (hR h0)⟩
  | a16 h0 => exact ⟨_, (Nat.le_refl _), .a16 (hR h0)⟩
  | a17 h0 => exact ⟨_, (Nat.le_refl _), .a17 (hH h0)⟩
  | a18 h0 => exact ⟨_, (Nat.le_refl _), .a18 (hH h0)⟩
  | a19 h0 => exact ⟨_, (Nat.le_refl _), .a19 (hH h0)⟩
  | a20 h0 h1 => exact ⟨_, (Nat.le_refl _), .a20 (hH h0) (hN h1)⟩
  | a21 h0 h1 => exact ⟨_, (Nat.le_refl _), .a21 (hH h0) (hN h1)⟩
  | a22 h0 h1 => exact ⟨_, (Nat.le_refl _), .a22 (hH h0) (hNx h1)⟩
  | a23 h0 => exact ⟨_, (Nat.le_refl _), .a23 (hH h0)⟩
  | a24 h0 => exact ⟨_, (Nat.le_refl _), .a24 (hH h0)⟩
  | a25 h0 => exact ⟨_, (Nat.le_refl _), .a25 (hC h0)⟩
  | a26 h0 => exact ⟨_, (Nat.le_refl _), .a26 (hC h0)⟩
  | a27 h0 h1 => exact ⟨_, (Nat.le_refl _), .a27 (hH h0) (hQ h0 h1)⟩
  | a28 h0 h1 => exact ⟨_, (Nat.le_refl _), .a28 (hH h0) (hQ h0 h1)⟩
  | a29 h0 h1 h2 => exact ⟨_, (Nat.le_refl _), .a29 (hH h0) (hQ h0 h1) (hN h2)⟩
  | a30 h0 h1 h2 => exact ⟨_, (Nat.le_refl _), .a30 (hH h0) (hQ h0 h1) (hN h2)⟩
  | a31 h0 h1 h2 => exact ⟨_, (m31 h0), .a31 (hH h0) (hQ h0 h1) (hN h2)⟩
  | a32 h0 h1 => exact ⟨_, (m32 h0), .a32 (hH h0) (hQ h0 h1)⟩
  | a33 h0 h1 h2 => exact ⟨_, (m33 h0), .a33 (hH h0) (hQ h0 h1) (hN h2)⟩
  | a34 h0 h1 => exact ⟨_, (Nat.le_refl _), .a34 (hH h0) (hNx h1)⟩
  | c0 h0 => exact ⟨_, Nat.le_refl _, .c0 (hH h0)⟩
  | c1 h0 => exact ⟨_, Nat.le_refl _, .c1 (hH h0)⟩
  | c2 h0 => exact ⟨_, Nat.le_refl _, .c2 (hH h0)⟩
  | c3 h0 => exact ⟨_, Nat.le_refl _, .c3 (hH h0)⟩
  | done h0 => exact ⟨_, (Nat.le_refl _), .done (hI h0)⟩

theorem at_othersWM {c : CPU} {t : CThread MPrim} :
    ∀ (xs : MLog) {l : MLog} {s s' : MS} {h h' : List HEvent} {w : Nat},
      (∀ e ∈ xs, e.cpu ≠ c) → mreplay l = some (s, h) → mreplay (xs ++ l) = some (s', h') →
      AtWN n c s t w → ∃ w', w' ≤ w ∧ AtWN n c s' t w'
  | [], l, s, s', h, h', w, _, hl, hr, hA => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact ⟨w, Nat.le_refl _, hA⟩
  | e :: xs, l, s, s', h, h', w, hx, hl, hr, hA => by
    obtain ⟨s2, h2, o, hl2, hp, -⟩ := mreplay_cons hr
    obtain ⟨w2, hw2, hA2⟩ := at_othersWM xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2 hA
    obtain ⟨w', hw', hA'⟩ := at_otherWM (mreplay_inv hl2) hp (hx e List.mem_cons_self) hA2
    exact ⟨w', by omega, hA'⟩

/-! ## Our own step -/

/-- The three points of the `busy` loop, and of the `next` loop. -/
def InLoopB (t : CThread MPrim) : Prop :=
  t.stmt = loopB ∨ ∃ k, t.cont = .loop (.bin .ne (.var "b") (.const 0)) gbC k
def InLoopN (t : CThread MPrim) : Prop := (t.stmt = loopN ∧ t.cont = .seq hoC .stop) ∨ t.cont = KLN

/-- `c` is spinning at `t`: waiting on a `busy` flag that is still set, or on a
`next` pointer that is still null. -/
def SpinPt (s : MS) (c : CPU) (t : CThread MPrim) : Prop :=
  (s.ph c = .waiting ∧ s.busy c = true ∧ InLoopB t) ∨ (s.ph c = .holding ∧ s.next c = none ∧ InLoopN t)

def OutWM (n : Nat) (c : CPU) (l : MLog) (s : MS) (t : CThread MPrim) (w : Nat) (c' : Config MPrim MLog) : Prop :=
  ∃ s' H' w', mreplay c'.abs = some (s', H') ∧ AtWN n c s' (thr c') w' ∧ (w' < w ∨ (w' = w ∧ SpinPt s c t)) ∧
    ∃ ys, c'.abs = ys ++ l ∧ ∀ e ∈ ys, e.cpu = c

theorem wo_ne {c : CPU} {l : MLog} {s : MS} {H : List HEvent} {t : CThread MPrim} {w w' : Nat}
    {c' : Config MPrim MLog} (hl : mreplay l = some (s, H)) (habs : c'.abs = l) (hA : AtWN n c s (thr c') w')
    (hd : w' < w ∨ (w' = w ∧ SpinPt s c t)) : OutWM n c l s t w c' :=
  ⟨s, H, w', habs ▸ hl, hA, hd, [], by simp [habs], by simp⟩

theorem wo_ev {c : CPU} {l : MLog} {s s' : MS} {H : List HEvent} {t : CThread MPrim} {w w' : Nat}
    {c' : Config MPrim MLog} {k : MKind} {o : Option HEvent} (hl : mreplay l = some (s, H))
    (hp : mstep s ⟨c, k⟩ = some (s', o)) (habs : c'.abs = ⟨c, k⟩ :: l) (hA : AtWN n c s' (thr c') w')
    (hd : w' < w ∨ (w' = w ∧ SpinPt s c t)) : OutWM n c l s t w c' :=
  ⟨_, _, w', habs ▸ mreplay_cons_of hl hp, hA, hd, [⟨c, k⟩], habs, by simp⟩

set_option linter.unusedSimpArgs false

theorem w5_le (σ : Locals) : w5 σ ≤ 36 := by unfold w5; split <;> omega
theorem w21_le (σ : Locals) : w21 σ ≤ 17 := by unfold w21; split <;> omega
theorem w26_le (σ : Locals) : w26 σ ≤ 13 := by unfold w26; split <;> omega
theorem w12_le (s : MS) (c : CPU) (σ : Locals) : w12 s c σ ≤ 29 := by unfold w12; split <;> (try split) <;> omega
theorem w31_le (s : MS) (c : CPU) (σ : Locals) : w31 s c σ ≤ 8 := by unfold w31; split <;> (try split) <;> omega

theorem own_stepWM {c : CPU} {l : MLog} {s : MS} {H : List HEvent} {t : CThread MPrim} {w : Nat}
    {c' : Config MPrim MLog} (hc : c < NCPU) (hl : mreplay l = some (s, H)) (hA : AtWN n c s t w)
    (hst : ClightL.step (mprims noEnvM c) (t.cfg l) = some c') : OutWM n c l s t w c' := by
  have hi := mreplay_inv hl
  have hs0 := stOf_eq hl
  cases hA with
  | a0 h => simp only [ClightL.step, CThread.cfg, codeN, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.a1 h) (.inl (by (try dsimp only) <;> omega))
  | a1 h => simp only [ClightL.step, CThread.cfg, acquireM_eq, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.a2 h) (.inl (by (try dsimp only) <;> omega))
  | @a2 σ h =>
    simp only [ClightL.step, CThread.cfg, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .swap⟩ = some (⟨s.hd, s.tl + 1, fset s.pos c (some s.tl), fset s.busy c true,
        fset s.next c none, fset s.ph c (match tailOf s with | none => .front | some p => .linking p)⟩,
        none) := by simp [mstep, hc, h] <;> rfl
    refine wo_ev hl hp rfl (.a3 ?_) (.inl (Nat.add_lt_add_right (Nat.lt_of_le_of_lt (Nat.add_le_add_right (w5_le _) 2) (by (try dsimp only) <;> omega)) _))
    rw [hs0]
    cases ht : tailOf s with
    | none => left; simp [encC]
    | some q => right; exact ⟨q, by simp, by simpa using encC_some_ne q⟩
  | a3 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.a4 h) (.inl (by (try dsimp only) <;> omega))
  | a4 h => simp only [ClightL.step, CThread.cfg, REST, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.a5 h) (.inl (by (try dsimp only) <;> omega))
  | @a5 σ h =>
    simp only [ClightL.step, CThread.cfg, ITE, Option.some.injEq] at hst; subst hst
    rcases h with ⟨hf, hp0⟩ | ⟨q, hq, hp0⟩
    · refine wo_ne hl rfl ?_ (.inl (Nat.add_lt_add_right ((by (try dsimp only) <;> simp only [w5, hp0, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega : 23 < w5 σ)) _))
      simp only [thr, Expr.eval, BinOp.eval, hp0, ite_true]; exact .a15 (.inl hf)
    · refine wo_ne hl rfl ?_ (.inl (Nat.add_lt_add_right ((by (try dsimp only) <;> simp only [w5, hp0, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega : 35 < w5 σ)) _))
      simp only [thr, Expr.eval, BinOp.eval, hp0, ite_false]; exact .a6 ⟨q, hq⟩
  | a6 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.a7 h) (.inl (by (try dsimp only) <;> omega))
  | @a7 σ h =>
    obtain ⟨q, hq⟩ := h
    simp only [ClightL.step, CThread.cfg, linkC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .link⟩ = some (⟨s.hd, s.tl, s.pos, s.busy, fset s.next q (some c),
        fset s.ph c .waiting⟩, none) := by simp [mstep, hc, hq]
    exact wo_ev hl hp rfl (.a8 (by simp)) (.inl (by (try dsimp only) <;> omega))
  | a8 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.a9 h) (.inl (by (try dsimp only) <;> omega))
  | a9 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.a10 h) (.inl (by (try dsimp only) <;> omega))
  | @a10 σ h =>
    simp only [ClightL.step, CThread.cfg, gbC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getBusy⟩ = some (s, none) := by simp [mstep, hc, h]
    refine wo_ev hl hp rfl (.a11 h fun h0 => ?_) (.inl (by (try dsimp only) <;> omega))
    simp only [Locals.set_same, hs0] at h0; split at h0
    · exact absurd h0 (by decide)
    · simpa using ‹¬ s.busy c = true›
  | a11 h1 h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                 exact wo_ne hl rfl (.a12 h1 h2) (.inl (Nat.add_lt_add_right (Nat.lt_of_le_of_lt (w12_le _ _ _) (by (try dsimp only) <;> omega)) _))
  | @a12 σ h1 h2 =>
    change ClightL.step _ (CThread.cfg ⟨.while (.bin .ne (.var "b") (.const 0)) gbC, .seq holdC (KRn n), σ⟩ l) = _
      at hst
    rw [cstep_while] at hst
    by_cases hz : (Expr.bin BinOp.ne (.var "b") (.const 0)).eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have hb0 : σ "b" = 0 := by rw [ne_eval_zero] at hz; simpa [Expr.eval] using hz
      exact wo_ne hl rfl (.a15 (.inr ⟨h1, h2 hb0⟩)) (.inl (by (try dsimp only) <;> simp only [w12, h2 hb0, hb0, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega))
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      have hb0 : σ "b" ≠ 0 := fun h0 => hz (by rw [ne_eval_zero]; simpa [Expr.eval] using h0)
      cases hb : s.busy c
      · exact wo_ne hl rfl (.a13 h1) (.inl (by (try dsimp only) <;> simp only [w12, w13, hb, hb0, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega))
      · exact wo_ne hl rfl (.a13 h1) (.inr ⟨by (try dsimp only) <;> simp only [w12, w13, hb, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega, .inl ⟨h1, hb, .inl rfl⟩⟩)
  | @a13 σ h =>
    simp only [ClightL.step, CThread.cfg, gbC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getBusy⟩ = some (s, none) := by simp [mstep, hc, h]
    have hBI : BI s c (σ.set "b" (if (stOf l).busy c then 1 else 0)) := fun h0 => by
      simp only [Locals.set_same, hs0] at h0; split at h0
      · exact absurd h0 (by decide)
      · simpa using ‹¬ s.busy c = true›
    cases hb : s.busy c
    · exact wo_ev hl hp rfl (.a14 h hBI) (.inl (by (try dsimp only) <;> simp only [w13, w14, hb, hs0, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega))
    · exact wo_ev hl hp rfl (.a14 h hBI) (.inr ⟨by (try dsimp only) <;> simp only [w13, w14, hb, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega, .inl ⟨h, hb, .inr ⟨_, rfl⟩⟩⟩)
  | @a14 σ h1 h2 =>
    simp only [ClightL.step, CThread.cfg, KLBn, Option.some.injEq] at hst; subst hst
    cases hb : s.busy c
    · refine wo_ne hl rfl (.a12 h1 h2) (.inl ?_)
      by_cases hb0 : σ "b" = 0 <;> simp only [w12, w14, hb, hb0, Bool.false_eq_true, ↓reduceIte] <;> omega
    · exact wo_ne hl rfl (.a12 h1 h2) (.inr ⟨by (try dsimp only) <;> simp only [w12, w14, hb, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega, .inl ⟨h1, hb, .inr ⟨_, rfl⟩⟩⟩)
  | a15 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
             exact wo_ne hl rfl (.a16 h) (.inl (by (try dsimp only) <;> omega))
  | @a16 σ h =>
    simp only [ClightL.step, CThread.cfg, holdC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .hold⟩ = some (⟨s.hd, s.tl, s.pos, s.busy, s.next, fset s.ph c .holding⟩,
        some (.acq c)) := by
      rcases h with h | ⟨h1, h2⟩
      · simp [mstep, hc, h]
      · simp [mstep, hc, h1, h2]
    exact wo_ev hl hp rfl (.a17 (by simp)) (.inl (by (try dsimp only) <;> omega))
  | a17 h => simp only [ClightL.step, CThread.cfg, KRn, Option.some.injEq] at hst; subst hst
             exact wo_ne hl rfl (.c0 h) (.inl (by (try dsimp only) <;> omega))
  | a18 h => simp only [ClightL.step, CThread.cfg, releaseM_eq, Option.some.injEq] at hst; subst hst
             exact wo_ne hl rfl (.a19 h) (.inl (by (try dsimp only) <;> omega))
  | @a19 σ h =>
    simp only [ClightL.step, CThread.cfg, MCSLink.gnC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getNext⟩ = some (s, none) := by simp [mstep, hc, h]
    refine wo_ev hl hp rfl (.a20 h fun h0 hn => ?_)
      (.inl (Nat.lt_of_le_of_lt (Nat.add_le_add_right (w21_le _) 1) (by (try dsimp only) <;> omega)))
    simp [hs0, hn, encC] at h0
  | a20 h1 h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                 exact wo_ne hl rfl (.a21 h1 h2) (.inl (by (try dsimp only) <;> omega))
  | @a21 σ h1 h2 =>
    simp only [ClightL.step, CThread.cfg, RITE, Option.some.injEq] at hst; subst hst
    by_cases hn0 : σ "n" = 0
    · refine wo_ne hl rfl ?_ (.inl (by (try dsimp only) <;> simp only [w21, hn0, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega : 16 < w21 σ))
      simp only [thr, Expr.eval, BinOp.eval, hn0, ite_true]; exact .a23 h1
    · refine wo_ne hl rfl ?_ (.inl (by (try dsimp only) <;> simp only [w21, hn0, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega : 1 < w21 σ))
      simp only [thr, Expr.eval, BinOp.eval, hn0, ite_false]; exact .a22 h1 (h2 hn0)
  | @a22 σ h1 h2 =>
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 h2
    simp only [ClightL.step, CThread.cfg, hoC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .handoff⟩ = some (⟨s.hd + 1, s.tl, fset s.pos c none, fset s.busy d false, s.next,
        fset s.ph c .idle⟩, some (.rel c)) := by simp [mstep, hc, h1, hd]
    exact wo_ev hl hp rfl (.done (by simp)) (.inl (by (try dsimp only) <;> omega))
  | a23 h => simp only [ClightL.step, CThread.cfg, TAIL, Option.some.injEq] at hst; subst hst
             exact wo_ne hl rfl (.a24 h) (.inl (by (try dsimp only) <;> omega))
  | @a24 σ h =>
    simp only [ClightL.step, CThread.cfg, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    simp only [hs0]
    have hlt26 : ∀ σ', w26 σ' + 1 < 15 := fun σ' =>
      Nat.lt_of_le_of_lt (Nat.add_le_add_right (w26_le σ') 1) (by (try dsimp only) <;> omega)
    by_cases htl : s.tl = s.hd + 1
    · have ht : tailOf s = some c := (tail_holding hi h).2 htl
      have hp : mstep s ⟨c, .cas⟩ = some (⟨s.hd + 1, s.tl, fset s.pos c none, s.busy, s.next,
          fset s.ph c .idle⟩, some (.rel c)) := by simp [mstep, hc, h, htl]
      exact wo_ev hl hp rfl (.a25 (.inl ⟨by simp [ht], by simp⟩)) (.inl (hlt26 _))
    · have ht : ¬ tailOf s = some c := fun x => htl ((tail_holding hi h).1 x)
      have hp : mstep s ⟨c, .cas⟩ = some (s, none) := by simp [mstep, hc, h, htl]
      have hpc := hi.owner_head (.inr (.inl h))
      have hlt := (hi.bnd c _ hpc).2
      exact wo_ev hl hp rfl (.a25 (.inr ⟨by simp [ht], h, by omega⟩)) (.inl (hlt26 _))
  | a25 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
             exact wo_ne hl rfl (.a26 h) (.inl (by (try dsimp only) <;> omega))
  | @a26 σ h =>
    simp only [ClightL.step, CThread.cfg, KITE, Option.some.injEq] at hst; subst hst
    rcases h with ⟨hk, hidle⟩ | ⟨hk, hh, hq⟩
    · refine wo_ne hl rfl ?_ (.inl (by (try dsimp only) <;> simp only [w26, hk, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega : 0 < w26 σ))
      simp only [thr, Expr.eval, BinOp.eval, hk, ite_false, ite_true]; exact .done hidle
    · refine wo_ne hl rfl ?_ (.inl (by (try dsimp only) <;> simp only [w26, hk, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega : 12 < w26 σ))
      simp only [thr, Expr.eval, BinOp.eval, hk, ite_true]
      exact .a27 hh hq
  | a27 h hq => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                exact wo_ne hl rfl (.a28 h hq) (.inl (by (try dsimp only) <;> omega))
  | @a28 σ h hq =>
    simp only [ClightL.step, CThread.cfg, MCSLink.gnC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getNext⟩ = some (s, none) := by simp [mstep, hc, h]
    refine wo_ev hl hp rfl (.a29 h hq fun h0 hn => ?_) (.inl (by (try dsimp only) <;> omega))
    simp [hs0, hn, encC] at h0
  | a29 h1 hq h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                    exact wo_ne hl rfl (.a30 h1 hq h2) (.inl (by (try dsimp only) <;> omega))
  | a30 h1 hq h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                    exact wo_ne hl rfl (.a31 h1 hq h2) (.inl (Nat.lt_of_le_of_lt (w31_le _ _ _) (by (try dsimp only) <;> omega)))
  | @a31 σ h1 hq h2 =>
    change ClightL.step _ (CThread.cfg ⟨.while (.bin .eq (.var "n") (.const 0)) MCSLink.gnC, .seq hoC .stop, σ⟩ l) = _
      at hst
    rw [cstep_while] at hst
    by_cases hz : (Expr.bin BinOp.eq (.var "n") (.const 0)).eval σ = 0
    · rw [ite_eq_left hz] at hst; obtain rfl := Option.some.inj hst
      have hn0 : σ "n" ≠ 0 := by
        intro h0; simp [Expr.eval, BinOp.eval, h0] at hz
      exact wo_ne hl rfl (.a34 h1 (h2 hn0)) (.inl (by (try dsimp only) <;> simp only [w31, h2 hn0, hn0, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega))
    · rw [ite_eq_right hz] at hst; obtain rfl := Option.some.inj hst
      have hn0 : σ "n" = 0 := Classical.byContradiction fun h0 => by
        have h0' : ¬ σ "n" = 0#32 := h0
        exact hz (by simp [Expr.eval, BinOp.eval, h0'])
      by_cases hnx : s.next c = none
      · exact wo_ne hl rfl (.a32 h1 hq) (.inr ⟨by (try dsimp only) <;> simp only [w31, w32, hnx, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega, .inr ⟨h1, hnx, .inl ⟨rfl, rfl⟩⟩⟩)
      · exact wo_ne hl rfl (.a32 h1 hq) (.inl (by (try dsimp only) <;> simp only [w31, w32, hnx, hn0, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega))
  | @a32 σ h hq =>
    simp only [ClightL.step, CThread.cfg, MCSLink.gnC, mprims, List.map_nil, mpull_noEnvM, Option.some.injEq] at hst
    subst hst
    have hp : mstep s ⟨c, .getNext⟩ = some (s, none) := by simp [mstep, hc, h]
    have hNI : NI s c (σ.set "n" (encC ((stOf l).next c))) := fun h0 hn => by simp [hs0, hn, encC] at h0
    by_cases hnx : s.next c = none
    · exact wo_ev hl hp rfl (.a33 h hq hNI) (.inr ⟨by (try dsimp only) <;> simp only [w32, w33, hnx, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega, .inr ⟨h, hnx, .inr rfl⟩⟩)
    · obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.1 hnx
      exact wo_ev hl hp rfl (.a33 h hq hNI) (.inl (by (try dsimp only) <;> simp only [w32, w33, hd, hs0, encC_some_ne, reduceCtorEq, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega))
  | @a33 σ h1 hq h2 =>
    simp only [ClightL.step, CThread.cfg, KLN, Option.some.injEq] at hst; subst hst
    by_cases hnx : s.next c = none
    · exact wo_ne hl rfl (.a31 h1 hq h2) (.inr ⟨by (try dsimp only) <;> simp only [w31, w33, hnx, Locals.set_same, Bool.false_eq_true, ↓reduceIte] <;> omega, .inr ⟨h1, hnx, .inr rfl⟩⟩)
    · refine wo_ne hl rfl (.a31 h1 hq h2) (.inl ?_)
      by_cases hn0 : σ "n" = 0 <;> simp only [w31, w33, hnx, hn0, ↓reduceIte] <;> omega
  | a34 h1 h2 => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
                 exact wo_ne hl rfl (.a22 h1 h2) (.inl (by (try dsimp only) <;> omega))
  | c0 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.c1 h) (.inl (by (try dsimp only) <;> omega))
  | @c1 σ k h =>
    cases k with
    | zero => simp only [ClightL.step, CThread.cfg, critM, KC, Option.some.injEq] at hst; subst hst
              exact wo_ne hl rfl (.a18 h) (.inl (by (try dsimp only) <;> omega))
    | succ k => simp only [ClightL.step, CThread.cfg, critM, Option.some.injEq] at hst; subst hst
                exact wo_ne hl rfl (.c2 h) (.inl (by (try dsimp only) <;> omega))
  | c2 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.c3 h) (.inl (by (try dsimp only) <;> omega))
  | c3 h => simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hst; subst hst
            exact wo_ne hl rfl (.c1 h) (.inl (by (try dsimp only) <;> omega))
  | done h => simp [ClightL.step, CThread.cfg] at hst


/-! ## Facts about the global log -/

theorem mreplay_nil : mreplay [] = some (MS.init, []) := rfl

/-- CPUs that never act stay idle. -/
theorem idle_beyondM {T : Nat} {l : MLog} {s : MS} {H : List HEvent} (hev : ∀ e ∈ l, e.cpu < T)
    (hl : mreplay l = some (s, H)) (d : CPU) (hd : T ≤ d) : s.ph d = .idle := by
  have := (others_eventsM (c := d) l (fun e he => Nat.ne_of_lt (Nat.lt_of_lt_of_le (hev e he) hd))
    mreplay_nil (by simpa using hl)).1
  rw [this]; rfl

theorem atWM_done {c : CPU} {s : MS} {t : CThread MPrim} {w : Nat} (hA : AtWN n c s t w) (hd : Done t) :
    s.ph c = .idle := by
  obtain ⟨h1, h2⟩ := hd
  cases hA <;> simp_all [codeN, KRn, KC, critM, KLBn, acquireM, releaseM, REST, ITE, RITE, TAIL, KITE, KLB, KLN,
    MCSLink.gnC, hoC, gbC, holdC, linkC, loopB, loopN]

/-- In the `next` loop, someone is queued behind us. -/
theorem loopN_behind {c : CPU} {s : MS} {t : CThread MPrim} {w : Nat} (hA : AtWN n c s t w) (hL : InLoopN t) :
    s.hd + 1 < s.tl := by
  rcases hL with ⟨h1, h2⟩ | h2 <;> cases hA <;> simp_all [codeN, KRn, KC, critM, KLBn, acquireM, releaseM, REST, ITE,
    RITE, TAIL, KITE, KLB, KLN, MCSLink.gnC, hoC, gbC, holdC, linkC, loopB, loopN]

/-! ## The global potential -/

def GLM (n T : Nat) (cs : List (CThread MPrim)) (l : MLog) (Φ : Nat) : Prop :=
  ∃ s H, ∃ ws : Nat → Nat, mreplay l = some (s, H) ∧ cs.length = T ∧ T ≤ NCPU ∧ (∀ e ∈ l, e.cpu < T) ∧
    (∀ c (hc : c < cs.length), AtWN n c s cs[c] (ws c)) ∧ Φ = sumTo ws T

def SpinsWM (cs : List (CThread MPrim)) (l : MLog) (d : Nat) : Prop :=
  ∃ (hd : d < cs.length) (s : MS) (H : List HEvent), mreplay l = some (s, H) ∧ SpinPt s d cs[d]

def ActWM (cs : List (CThread MPrim)) (l : MLog) (d : Nat) : Prop :=
  ∃ hd : d < cs.length, ¬ Done cs[d] ∧ ¬ SpinsWM cs l d

theorem gstepWM {T : Nat} {cs cs' : List (CThread MPrim)} {l l' : MLog} {Φ a : Nat}
    (hG : GLM n T cs l Φ) (hS : CStepI PGM a cs l cs' l') :
    ∃ Φ', GLM n T cs' l' Φ' ∧ Φ' ≤ Φ ∧ (¬ SpinsWM cs l a → Φ' < Φ) ∧
      (∀ d, d ≠ a → SpinsWM cs' l' d → SpinsWM cs l d) := by
  obtain ⟨s, H, ws, hl, hlen, hT, hev, hAt, rfl⟩ := hG
  obtain ⟨ha, c', hst, rfl, rfl⟩ := hS
  have haT : a < T := hlen ▸ ha
  have haN : a < NCPU := Nat.lt_of_lt_of_le haT hT
  obtain ⟨s', H', w', hr', hA', hdec, ys, hys, hown⟩ := own_stepWM haN hl (hAt a ha) hst
  have hr'' : mreplay (ys ++ l) = some (s', H') := hys ▸ hr'
  have hx : ∀ d, d ≠ a → ∀ e ∈ ys, e.cpu ≠ d := fun d hd e he => by rw [hown e he]; exact Ne.symm hd
  have hch : ∀ d, ∃ w'', ∀ hd : d < cs.length, d ≠ a → w'' ≤ ws d ∧ AtWN n d s' cs[d] w'' := by
    intro d
    by_cases hd : d < cs.length
    · by_cases hda : d = a
      · exact ⟨0, fun _ h => absurd hda h⟩
      · obtain ⟨w'', h1, h2⟩ := at_othersWM ys (hx d hda) hl hr'' (hAt d hd)
        exact ⟨w'', fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hd⟩
  let ws' : Nat → Nat := fun d => if d = a then w' else Classical.choose (hch d)
  have hws' : ∀ d (hd : d < cs.length), d ≠ a → ws' d ≤ ws d ∧ AtWN n d s' cs[d] (ws' d) :=
    fun d hd hda => by simp only [ws', hda, ite_false]; exact Classical.choose_spec (hch d) hd hda
  have hwa : ws' a = w' := by simp [ws']
  have hle : ∀ d, d < T → ws' d ≤ ws d := fun d hd => by
    by_cases hda : d = a
    · subst hda; rw [hwa]; rcases hdec with h | ⟨h, -⟩ <;> omega
    · exact (hws' d (hlen ▸ hd) hda).1
  refine ⟨sumTo ws' T, ⟨s', H', ws', hr', by simpa using hlen, hT, fun e he => ?_, fun c hc => ?_, rfl⟩,
    sumTo_le T hle, fun hns => ?_, fun d hda hsp => ?_⟩
  · rw [hys] at he
    rcases List.mem_append.1 he with he | he
    · rw [hown e he]; exact haT
    · exact hev e he
  · by_cases hca : c = a
    · subst hca; simp only [List.getElem_set_self]; rw [hwa]; simpa using hA'
    · have hc' : c < cs.length := by simpa using hc
      simp only [List.getElem_set_ne (Ne.symm hca)]
      exact (hws' c hc' hca).2
  · refine sumTo_lt (i := a) T hle haT ?_
    rw [hwa]
    rcases hdec with h | ⟨-, hsp⟩
    · exact h
    · exact absurd ⟨ha, s, H, hl, hsp⟩ hns
  · obtain ⟨hd', s2, H2, hl2, hsp⟩ := hsp
    rw [hr'] at hl2; cases hl2
    have hd : d < cs.length := by simpa using hd'
    obtain ⟨hph, -, -, hb, hn, -⟩ := others_eventsM ys (hx d hda) hl hr''
    have ht : (cs.set a (thr c'))[d] = cs[d] := List.getElem_set_ne (Ne.symm hda) _
    refine ⟨hd, s, H, hl, ?_⟩
    rw [ht] at hsp
    rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · refine .inl ⟨by rw [← hph]; exact h1, ?_, h3⟩
      cases hbs : s.busy d
      · rw [hb hbs] at h2; cases h2
      · rfl
    · refine .inr ⟨by rw [← hph]; exact h1, ?_, h3⟩
      exact Classical.byContradiction fun hne => by rw [hn hne] at h2; exact hne h2

theorem act_existsWM {T : Nat} {cs : List (CThread MPrim)} {l : MLog} {Φ : Nat}
    (hG : GLM n T cs l Φ) (hu : ∃ i, ∃ hi : i < cs.length, ¬ Done cs[i]) : ∃ d, ActWM cs l d := by
  refine Classical.byContradiction fun hno => ?_
  have hall : ∀ d (hd : d < cs.length), ¬ Done cs[d] → SpinsWM cs l d := fun d hd hnd =>
    Classical.byContradiction fun hs => hno ⟨d, hd, hnd, hs⟩
  obtain ⟨s, H, ws, hl, hlen, hT, hev, hAt, -⟩ := hG
  have hi := mreplay_inv hl
  -- a queued CPU (not idle, so below `T`) is unfinished, hence spinning
  have hq : ∀ d, s.ph d ≠ .idle → ∃ hd : d < cs.length, SpinPt s d cs[d] := fun d hne => by
    have hdT : d < T := Nat.lt_of_not_le fun hge => hne (idle_beyondM hev hl d hge)
    have hd : d < cs.length := hlen ▸ hdT
    have hnd : ¬ Done cs[d] := fun hdn => hne (atWM_done (hAt d hd) hdn)
    obtain ⟨_, s2, H2, hl2, hsp⟩ := hall d hd hnd
    simp only [hl, Option.some.injEq, Prod.mk.injEq] at hl2; obtain ⟨rfl, rfl⟩ := hl2
    exact ⟨hd, hsp⟩
  obtain ⟨i, hi', hnd⟩ := hu
  obtain ⟨_, s2, H2, hl2, hspi⟩ := hall i hi' hnd
  simp only [hl, Option.some.injEq, Prod.mk.injEq] at hl2; obtain ⟨rfl, rfl⟩ := hl2
  -- the queue is not empty
  have hne_i : s.ph i ≠ .idle := by
    rcases hspi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> simp
  obtain ⟨n, hn⟩ := (hi.inq i).1 hne_i
  obtain ⟨hb1, hb2⟩ := hi.bnd i n hn
  -- its head
  obtain ⟨h, -, hh⟩ := whoAt_some hi (Nat.le_refl s.hd) (by omega)
  have hne_h : s.ph h ≠ .idle := fun hid => by
    obtain ⟨m, hm⟩ := (hi.inq h).1 (by
      rcases hi.head h hh with h' | h' | ⟨h', -⟩ <;> rw [h'] <;> simp)
    have := (hi.inq h).2 ⟨_, hh⟩; exact this hid
  obtain ⟨hhd, hsph⟩ := hq h hne_h
  rcases hsph with ⟨h1, h2, -⟩ | ⟨h1, h2, h3⟩
  · rcases hi.head h hh with h' | h' | ⟨-, h'⟩
    · rw [h1] at h'; cases h'
    · rw [h1] at h'; cases h'
    · rw [h2] at h'; cases h'
  · -- the head waits for its successor, who is still linking: not a spin
    have hbeh := loopN_behind (hAt h hhd) h3
    obtain ⟨q, -, hqp⟩ := whoAt_some hi (Nat.le_succ s.hd) hbeh
    have hlk := succ_linking hi hh h2 hqp
    obtain ⟨_, hspq⟩ := hq q (by rw [hlk]; simp)
    rcases hspq with ⟨h1', -⟩ | ⟨h1', -⟩ <;> rw [hlk] at h1' <;> cases h1'

theorem certN (n T : Nat) : LiveCert PGM (GLM n T) ActWM where
  le := fun hG hS => let ⟨Φ', h1, h2, _, _⟩ := gstepWM hG hS; ⟨Φ', h2, h1⟩
  lt := fun hG hA hS => by
    obtain ⟨Φ', h1, -, h3, -⟩ := gstepWM hG hS
    obtain ⟨_, _, hns⟩ := hA
    exact ⟨Φ', h3 hns, h1⟩
  persist := fun {cs a Φ i d cs' a'} hG hA hS hid => by
    obtain ⟨-, -, -, -, hsp⟩ := gstepWM hG hS
    obtain ⟨hd, hnd, hns⟩ := hA
    obtain ⟨hd', hcs⟩ := hS.other hd hid
    exact ⟨hd', by rw [hcs]; exact hnd, fun h => hns (hsp d (Ne.symm hid) h)⟩
  act := fun hG hu => act_existsWM hG hu
  act_lt := fun _ hA => let ⟨hd, hnd, _⟩ := hA; ⟨hd, hnd⟩

/-- `T` CPUs, each running `acquireM; critM n; releaseM`, CPU `i` with locals `σs i`. -/
def poolN (n T : Nat) (σs : Nat → Locals) : List (CThread MPrim) :=
  (List.range T).map fun i => ⟨codeN n, .stop, σs i⟩

theorem gl_initN (n T : Nat) (σs : Nat → Locals) (hT : T ≤ NCPU) :
    GLM n T (poolN n T σs) [] (T * (41 + (3 * n + 2))) := by
  refine ⟨_, _, fun _ => 41 + (3 * n + 2), mreplay_nil, by simp [poolN], hT, by simp, fun c hc => ?_,
    (sumTo_const _ _).symm⟩
  simp only [poolN, List.getElem_map, List.getElem_range]
  exact .a0 rfl

/-- **Liveness with a critical section.** -/
theorem mcsN_fair_terminates (n T : Nat) (σs : Nat → Locals) (hT : T ≤ NCPU) (r : GRun PGM)
    (h0 : r.cs 0 = poolN n T σs) (hl0 : r.ab 0 = []) {K : Nat} (hK : 0 < K) (hF : r.Fair K) :
    r.len < K * (T * (41 + (3 * n + 2)) + 1) :=
  fair_terminates (certN n T) r hK (by rw [h0, hl0]; exact gl_initN n T σs hT) hF

/-! ## Safety: mutual exclusion -/

theorem reachN (n T : Nat) (σs : Nat → Locals) (hT : T ≤ NCPU) {cs : List (CThread MPrim)} {l : MLog}
    (h : CSteps PGM (poolN n T σs) [] cs l) : ∃ Φ, GLM n T cs l Φ := by
  suffices ∀ {a b la lb}, CSteps PGM a la b lb → ∀ Φ, GLM n T a la Φ → ∃ Φ', GLM n T b lb Φ' from
    this h _ (gl_initN n T σs hT)
  intro a b la lb hab
  induction hab with
  | refl => exact fun Φ hG => ⟨Φ, hG⟩
  | step hs _ ih =>
    intro Φ hG
    obtain ⟨i, hi, hst⟩ := hs
    obtain ⟨Φ', hG', -⟩ := gstepWM hG ⟨hi, _, hst, rfl, rfl⟩
    exact ih Φ' hG'

/-- In the critical section: from the end of `acquireM` to the start of `releaseM`. -/
def InCSN (n : Nat) (t : CThread MPrim) : Prop :=
  (t.stmt = .skip ∧ t.cont = KRn n) ∨ (t.stmt = .seq (critM n) releaseM ∧ t.cont = .stop) ∨
    (∃ k, t.stmt = critM k ∧ t.cont = KC) ∨
    (∃ k, t.stmt = .assign "_" (.const 0) ∧ t.cont = .seq (critM k) KC) ∨
    (∃ k, t.stmt = .skip ∧ t.cont = .seq (critM k) KC) ∨ (t.stmt = releaseM ∧ t.cont = .stop)

theorem at_csN {c : CPU} {s : MS} {t : CThread MPrim} {w : Nat} (hA : AtWN n c s t w) (hcs : InCSN n t) :
    s.ph c = .holding := by
  cases hA <;> simp_all [InCSN, codeN, KRn, KC, critM, KLBn, acquireM, releaseM, REST, ITE, TAIL, KITE, RITE,
    KLB, KLN, holdC, linkC, gbC, MCSLink.gnC, hoC, loopB, loopN]

/-- **Mutual exclusion with a critical section.** -/
theorem multicore_cs_exclusiveN (n T : Nat) (σs : Nat → Locals) (hT : T ≤ NCPU) {cs : List (CThread MPrim)}
    {l : MLog} (h : CSteps PGM (poolN n T σs) [] cs l) (c d : Nat) (hc : c < cs.length) (hd : d < cs.length)
    (hcc : InCSN n cs[c]) (hdc : InCSN n cs[d]) : c = d := by
  obtain ⟨Φ, s, H, ws, hl, -, -, -, hAt, -⟩ := reachN n T σs hT h
  exact mutexM hl (at_csN (hAt c hc) hcc) (at_csN (hAt d hd) hdc)

end MCSLiveN
