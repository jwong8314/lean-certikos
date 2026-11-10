import CertiKOS.LockArray

/-!
# Lock arrays, per CPU: the C code of `acquire(i)` / `release(i)` on `L0[c]`

The per-CPU layer of the lock array. CPU `c` runs against an environment `ε`
that answers with other CPUs' events on *all* locks (one global log, as in
CertiKOS).

* `aprims`: `FAI_t(i)`, `get_n(i)`, `inc_n(i)`, `hold(i)`, `pull(i)`, `push(i, v)`.
  Each primitive is one event, preceded by the environment's events.
* `acquireA`: `t = FAI_t(lk); n = get_n(lk); while (n != t) n = get_n(lk); hold(lk); v = pull(lk);`
  `releaseA`: `push(lk, v); inc_n(lk);`, as in mC2 ([OSDI16] Fig. 7).
* `RelyA`: the other CPUs keep the array log valid (every lock's protocol,
  and ownership of every block). `FairA`: per-lock fairness, the analogue of
  `FairP`.
* `acquireA_guarantee`: started idle on lock `i`, the acquire ends holding
  `i`, its only new high-level event is `acqA c i`, and **the value it pulls
  is the block's value at the last release of `i`** (`hmemA`).
* `acquireA_live_bounded`: under a fairness counter bounded by `K`, the spec
  returns within `(NCPU + 1) * (K + 1)` iterations (Lemma 6, per lock).
* `acquireA_sim`, `releaseA_sim`: the C code runs the spec.
* `releaseA_guarantee`: from holding `i`, `push(i, v); inc_n(i)` ends idle on
  `i`, with the single new high-level event `relA c i v`.
-/

namespace LockArray

open ClightL Ticket

/-! ## The environment and the primitives -/

structure AEnv where
  query : CPU → ALog → List AEvent
  noSelf : ∀ c l e, e ∈ query c l → e.cpu ≠ c

def apull (ε : AEnv) (c : CPU) (l : ALog) : ALog := ε.query c l ++ l

inductive APrim
  | faiTicket | getNow | incNow | hold | pull | push

def ev (c : CPU) (i : Nat) (k : EvKind) : AEvent := ⟨c, i, .tk k⟩

def aprims (ε : AEnv) (c : CPU) : Prims APrim ALog
  | .faiTicket, [i], l =>
      let l1 := apull ε c l
      some (BitVec.ofNat 32 (ticket (projL i.toNat l1)), ev c i.toNat .incTicket :: l1)
  | .getNow, [i], l =>
      let l1 := apull ε c l
      some (BitVec.ofNat 32 (now (projL i.toNat l1)), ev c i.toNat .getNow :: l1)
  | .incNow, [i], l => some (0, ev c i.toNat .incNow :: apull ε c l)
  | .hold, [i], l => some (0, ev c i.toNat .hold :: apull ε c l)
  | .pull, [i], l =>
      let l1 := apull ε c l
      some (memOf i.toNat l1, ⟨c, i.toNat, .pull⟩ :: l1)
  | .push, [i, v], l => some (0, ⟨c, i.toNat, .push v⟩ :: apull ε c l)
  | _, _, _ => none

/-! ## The C code -/

def lkE : Expr := .var "lk"
def loopA : Stmt APrim := .while (.bin .ne (.var "n") (.var "t")) (.call "n" .getNow [lkE])
def acquireA : Stmt APrim :=
  .seq (.call "t" .faiTicket [lkE])
    (.seq (.call "n" .getNow [lkE]) (.seq loopA (.seq (.call "_" .hold [lkE]) (.call "v" .pull [lkE]))))
def releaseA : Stmt APrim := .seq (.call "_" .push [lkE, .var "v"]) (.call "_" .incNow [lkE])

/-! ## Specs -/

section Spec
variable (ε : AEnv) (c : CPU) (i : Nat)

def waitLoopA (t : Val) : Nat → Val → ALog → Option ALog
  | 0, n, l => if n = t then some l else none
  | f + 1, n, l =>
      if n = t then some l
      else waitLoopA t f (BitVec.ofNat 32 (now (projL i (apull ε c l)))) (ev c i .getNow :: apull ε c l)

/-- After the wait loop: `hold(i)` then `pull(i)`. -/
def holdPull (r0 : ALog) : ALog := ⟨c, i, .pull⟩ :: apull ε c (ev c i .hold :: apull ε c r0)

def acquireSpecA (fuel : Nat) (l : ALog) : Option ALog :=
  let l1 := apull ε c l
  let t := BitVec.ofNat 32 (ticket (projL i l1))
  let l3 := apull ε c (ev c i .incTicket :: l1)
  (waitLoopA ε c i t fuel (BitVec.ofNat 32 (now (projL i l3))) (ev c i .getNow :: l3)).map (holdPull ε c i)

def releaseSpecA (v : Val) (l : ALog) : ALog :=
  ev c i .incNow :: apull ε c (⟨c, i, .push v⟩ :: apull ε c l)

end Spec

/-! ## Rely and fairness -/

def Valid (l : ALog) : Prop := ∃ S H, areplay l = some (S, H)

structure RelyA (ε : AEnv) (c : CPU) : Prop where
  conform : ∀ l S H, areplay l = some (S, H) → ∃ S' H', areplay (apull ε c l) = some (S', H')

def FairA (ε : AEnv) (c : CPU) (i tn : Nat) (bound : ALog → Nat) : Prop :=
  ∀ l S H, areplay l = some (S, H) → (S.lk i).phase c = .waiting tn → (S.lk i).now < tn →
    now (projL i l) < now (projL i (apull ε c l)) ∨ bound (ev c i .getNow :: apull ε c l) < bound l

def cpuFilterA (c : CPU) (H : HLogA) : HLogA := H.filter (fun e => decide (e.cpu = c))

theorem cpuFilterA_acq (c : CPU) (i : Nat) (H : HLogA) :
    cpuFilterA c (.acqA c i :: H) = .acqA c i :: cpuFilterA c H := by
  simp [cpuFilterA, HEventA.cpu]

theorem cpuFilterA_rel (c : CPU) (i : Nat) (v : Val) (H : HLogA) :
    cpuFilterA c (.relA c i v :: H) = .relA c i v :: cpuFilterA c H := by
  simp [cpuFilterA, HEventA.cpu]

/-- The high-level log only grows. -/
theorem areplay_hext {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) :
    ∀ (xs : ALog) {S' : AState} {H' : HLogA}, areplay (xs ++ l) = some (S', H') → ∃ E, H' = E ++ H
  | [], S', H', hr => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact ⟨[], rfl⟩
  | e :: xs, S', H', hr => by
    obtain ⟨S2, H2, o, hl2, -, rfl⟩ := areplay_cons hr
    obtain ⟨E, rfl⟩ := areplay_hext hl xs hl2
    cases o with
    | none => exact ⟨E, rfl⟩
    | some he => exact ⟨he :: E, rfl⟩

/-! ## Other CPUs' events -/

theorem astep_other {c : CPU} {l : ALog} {S S' : AState} {H : HLogA} {e : AEvent}
    {o : Option HEventA} (hl : areplay l = some (S, H)) (hp : astep S e = some (S', o))
    (hne : e.cpu ≠ c) :
    (∀ i, (S'.lk i).phase c = (S.lk i).phase c) ∧
      (∀ i, Holding S c i → S'.mem i = S.mem i ∧ (S.dirty i = false → S'.dirty i = false)) ∧
      cpuFilterA c (consO o []) = [] := by
  obtain ⟨d, j, k⟩ := e
  simp only at hne
  cases k with
  | tk k =>
    simp only [astep] at hp
    split at hp
    · simp at hp
    · rename_i p' o' hps
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨hph, hf⟩ := pstep_other hps hne
      refine ⟨fun i => ?_, fun i _ => ⟨rfl, fun hd => ?_⟩, ?_⟩
      · by_cases hji : j = i
        · subst hji; simpa using hph
        · simp [upd, Ne.symm hji]
      · simp only; split
        · by_cases hji : j = i
          · subst hji; simp
          · simp [upd, Ne.symm hji, hd]
        · exact hd
      · cases o' with
        | none => rfl
        | some he =>
          cases he <;> simp_all [cpuFilter, consOpt, HEvent.cpu, cpuFilterA, consO, lift, HEventA.cpu]
  | pull =>
    simp only [astep] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨fun _ => rfl, fun _ _ => ⟨rfl, id⟩, rfl⟩
    · simp at hp
  | push v =>
    simp only [astep] at hp
    split at hp
    · rename_i hhold
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨fun _ => rfl, fun i hci => ?_, rfl⟩
      by_cases hji : j = i
      · subst hji; exact absurd (amutex hl j hhold hci) hne
      · simp [upd, Ne.symm hji]
    · simp at hp

theorem others_events {c : CPU} :
    ∀ (xs : ALog) {l : ALog} {S S' : AState} {H H' : HLogA},
      (∀ e ∈ xs, e.cpu ≠ c) → areplay l = some (S, H) → areplay (xs ++ l) = some (S', H') →
      (∀ i, (S'.lk i).phase c = (S.lk i).phase c) ∧
      (∀ i, Holding S c i → S'.mem i = S.mem i ∧ (S.dirty i = false → S'.dirty i = false)) ∧
      cpuFilterA c H' = cpuFilterA c H
  | [], l, S, S', H, H', _, hl, hr => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr
    exact ⟨fun _ => rfl, fun _ _ => ⟨rfl, id⟩, rfl⟩
  | e :: xs, l, S, S', H, H', hx, hl, hr => by
    obtain ⟨S2, H2, o, hl2, hp, rfl⟩ := areplay_cons hr
    obtain ⟨ih1, ih2, ih3⟩ := others_events xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2
    obtain ⟨h1, h2, h3⟩ := astep_other hl2 hp (hx e List.mem_cons_self)
    refine ⟨fun i => (h1 i).trans (ih1 i), fun i hci => ?_, ?_⟩
    · have hci2 : Holding S2 c i := by obtain ⟨t, ht⟩ := hci; exact ⟨t, by rw [ih1 i]; exact ht⟩
      obtain ⟨m1, d1⟩ := ih2 i hci
      obtain ⟨m2, d2⟩ := h2 i hci2
      exact ⟨m2.trans m1, fun hd => d2 (d1 hd)⟩
    · cases o with
      | none => exact ih3
      | some he =>
        simp only [consO, cpuFilterA, List.filter_cons] at h3 ⊢
        split at h3 <;> simp_all [cpuFilterA]

theorem pull_others {ε : AEnv} {c : CPU} (hR : RelyA ε c) {l : ALog} {S : AState} {H : HLogA}
    (hl : areplay l = some (S, H)) :
    ∃ S' H', areplay (apull ε c l) = some (S', H') ∧
      (∀ i, (S'.lk i).phase c = (S.lk i).phase c) ∧
      (∀ i, Holding S c i → S'.mem i = S.mem i ∧ (S.dirty i = false → S'.dirty i = false)) ∧
      cpuFilterA c H' = cpuFilterA c H := by
  obtain ⟨S', H', hr⟩ := hR.conform l S H hl
  exact ⟨S', H', hr, others_events _ (ε.noSelf c l) hl hr⟩

/-! ## Our own events -/

theorem astep_tk {S : AState} {c : CPU} {i : Nat} {k : EvKind} {p' : PState} {o : Option HEvent}
    (hp : pstep (S.lk i) ⟨c, k⟩ = some (p', o)) :
    astep S (ev c i k) = some (⟨upd S.lk i p', S.mem,
      if k = .hold ∨ k = .incNow then upd S.dirty i false else S.dirty⟩, o.map (lift i (S.mem i))) := by
  simp [astep, ev, hp]

section Loop
variable (ε : AEnv) (c : CPU) (i tn : Nat) (h₀ : HLogA)

def LoopInvA (l : ALog) : Prop :=
  ∃ S H, areplay l = some (S, H) ∧ (S.lk i).phase c = .waiting tn ∧ cpuFilterA c H = cpuFilterA c h₀

theorem after_getNowA (hc : c < NCPU) (hR : RelyA ε c) {l : ALog} (hi : LoopInvA c i tn h₀ l) :
    LoopInvA c i tn h₀ (ev c i .getNow :: apull ε c l) := by
  obtain ⟨S, H, hl, hw, hf⟩ := hi
  obtain ⟨S1, H1, hr1, hph1, -, hf1⟩ := pull_others hR hl
  have hw1 : (S1.lk i).phase c = .waiting tn := by rw [hph1]; exact hw
  have hp : pstep (S1.lk i) ⟨c, .getNow⟩ = some (S1.lk i, none) := by simp [pstep, hc, hw1]
  refine ⟨_, _, areplay_cons_of hr1 (astep_tk hp), ?_, ?_⟩
  · simp [upd, hw1]
  · simpa [consO] using hf1.trans hf

theorem loopInvA_gap {l : ALog} (hi : LoopInvA c i tn h₀ l) :
    now (projL i l) ≤ tn ∧ tn - now (projL i l) < NCPU := by
  obtain ⟨S, H, hr, hph, _⟩ := hi
  have hp := areplay_proj hr i
  have inv := replay_inv hp
  obtain ⟨hn, _⟩ := replay_counts hp
  have hle := inv.waitGe c tn hph
  have hlt := inv.tkLt c tn (by simp [hph, Phase.tk])
  have hout := inv.outstanding_le
  omega

theorem loopInvA_exit {l : ALog} (hi : LoopInvA c i tn h₀ l)
    (heq : BitVec.ofNat 32 (now (projL i l)) = BitVec.ofNat 32 tn) : now (projL i l) = tn := by
  obtain ⟨h1, h2⟩ := loopInvA_gap c i tn h₀ hi
  exact ofNat_eq_of_close h1 (by simp only [NCPU] at h2; omega) heq

theorem loopA_guarantee (hc : c < NCPU) (hR : RelyA ε c) :
    ∀ fuel l r, LoopInvA c i tn h₀ l →
      waitLoopA ε c i (BitVec.ofNat 32 tn) fuel (BitVec.ofNat 32 (now (projL i l))) l = some r →
      LoopInvA c i tn h₀ r ∧ now (projL i r) = tn := by
  intro fuel
  induction fuel with
  | zero =>
    intro l r hi hw
    by_cases heq : BitVec.ofNat 32 (now (projL i l)) = BitVec.ofNat 32 tn
    · simp [waitLoopA, heq] at hw; subst hw; exact ⟨hi, loopInvA_exit c i tn h₀ hi heq⟩
    · simp [waitLoopA, heq] at hw
  | succ f ih =>
    intro l r hi hw
    by_cases heq : BitVec.ofNat 32 (now (projL i l)) = BitVec.ofNat 32 tn
    · simp [waitLoopA, heq] at hw; subst hw; exact ⟨hi, loopInvA_exit c i tn h₀ hi heq⟩
    · simp only [waitLoopA, heq, ite_false] at hw
      refine ih _ r (after_getNowA ε c i tn h₀ hc hR hi) ?_
      simpa [projL, ev, now, countK] using hw

theorem now_pullA_ge (l : ALog) : now (projL i l) ≤ now (projL i (apull ε c l)) := by
  simp only [apull, projL_append, now, countK_append]; omega

theorem loopA_live_bounded (hc : c < NCPU) (hR : RelyA ε c) (bound : ALog → Nat) (K : Nat)
    (hK : ∀ l, bound l ≤ K) (hF : FairA ε c i tn bound) :
    ∀ m b l, tn - now (projL i l) = m → bound l = b → LoopInvA c i tn h₀ l →
      ∃ f r, f ≤ m * (K + 1) + b ∧
        waitLoopA ε c i (BitVec.ofNat 32 tn) f (BitVec.ofNat 32 (now (projL i l))) l = some r := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ihm =>
  intro b
  induction b using Nat.strongRecOn with
  | _ b ihb =>
  intro l hm hb hi
  by_cases heq : BitVec.ofNat 32 (now (projL i l)) = BitVec.ofNat 32 tn
  · exact ⟨0, l, Nat.zero_le _, by simp [waitLoopA, heq]⟩
  · obtain ⟨S, H, hr, hph, hf⟩ := hi
    have hp := areplay_proj hr i
    have inv := replay_inv hp
    obtain ⟨hsn, _⟩ := replay_counts hp
    have hne : now (projL i l) ≠ tn := fun h => heq (by rw [h])
    have hlt : now (projL i l) < tn := by have := inv.waitGe c tn hph; omega
    let l' : ALog := ev c i .getNow :: apull ε c l
    have hi' : LoopInvA c i tn h₀ l' := after_getNowA ε c i tn h₀ hc hR ⟨S, H, hr, hph, hf⟩
    have hnl' : now (projL i l') = now (projL i (apull ε c l)) := by
      simp [l', projL, ev, now, countK]
    have hge : now (projL i l) ≤ now (projL i l') := by rw [hnl']; exact now_pullA_ge ε c i l
    have step_eq : ∀ f, waitLoopA ε c i (BitVec.ofNat 32 tn) (f + 1) (BitVec.ofNat 32 (now (projL i l))) l
        = waitLoopA ε c i (BitVec.ofNat 32 tn) f (BitVec.ofNat 32 (now (projL i l'))) l' := by
      intro f; simp only [waitLoopA, heq, ite_false, l', hnl']
    have hfair := hF l S H hr hph (by omega)
    rcases Nat.lt_or_eq_of_le hge with hgt | hEq
    · obtain ⟨f, r, hfle, hw⟩ := ihm (tn - now (projL i l')) (by omega) (bound l') l' rfl rfl hi'
      have hm' : tn - now (projL i l') + 1 ≤ m := by omega
      have h1 := Nat.mul_le_mul_right (K + 1) hm'
      rw [Nat.succ_mul] at h1
      have h2 := hK l'
      exact ⟨f + 1, r, by omega, by rw [step_eq]; exact hw⟩
    · have hb' : bound l' < b := by
        rcases hfair with h1 | h1
        · rw [hnl'] at hEq; omega
        · rw [← hb]; exact h1
      obtain ⟨f, r, hfle, hw⟩ := ihb (bound l') hb' l' (by omega) rfl hi'
      exact ⟨f + 1, r, by omega, by rw [step_eq]; exact hw⟩

end Loop

theorem waitLoopA_mono (ε : AEnv) (c : CPU) (i : Nat) (t : Val) :
    ∀ f n l r, waitLoopA ε c i t f n l = some r → waitLoopA ε c i t (f + 1) n l = some r
  | 0, n, l, r, h => by by_cases hnt : n = t <;> simp_all [waitLoopA]
  | f + 1, n, l, r, h => by
    by_cases hnt : n = t
    · simp_all [waitLoopA]
    · simp only [waitLoopA, hnt, ite_false] at h ⊢
      exact waitLoopA_mono ε c i t f _ _ _ h

theorem waitLoopA_mono_le (ε : AEnv) (c : CPU) (i : Nat) (t : Val) {f f' : Nat} {n : Val} {l r : ALog}
    (hle : f ≤ f') (h : waitLoopA ε c i t f n l = some r) : waitLoopA ε c i t f' n l = some r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => exact h
  | succ k ih => exact waitLoopA_mono ε c i t _ _ _ _ (ih (by omega))

/-! ## `acquire(i)`: guarantee (with the data it pulls) and bounded liveness -/

/-- After `acquire(i)`: `c` holds `i`; its only new high-level event is
`acqA c i`; the pulled value is the block's value at the last release of `i`. -/
def AcqPostA (c : CPU) (i : Nat) (h₀ : HLogA) (r : ALog) (v : Val) : Prop :=
  ∃ S H, areplay r = some (S, H) ∧ Holding S c i ∧ cpuFilterA c H = .acqA c i :: cpuFilterA c h₀ ∧
    v = hmemA i H

theorem acquireA_enter {ε : AEnv} {c : CPU} {i : Nat} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H))
    (hidle : (S.lk i).phase c = .idle) :
    LoopInvA c i (ticket (projL i (apull ε c l))) H
      (ev c i .getNow :: apull ε c (ev c i .incTicket :: apull ε c l)) := by
  obtain ⟨S1, H1, hr1, hph1, -, hf1⟩ := pull_others hR hl
  obtain ⟨-, ht1⟩ := replay_counts (areplay_proj hr1 i)
  have hidle1 : (S1.lk i).phase c = .idle := by rw [hph1]; exact hidle
  have hp : pstep (S1.lk i) ⟨c, .incTicket⟩ = some (⟨(S1.lk i).ticket + 1, (S1.lk i).now,
      setPhase (S1.lk i).phase c (.waiting (S1.lk i).ticket)⟩, none) := by
    simp [pstep, hc, hidle1]
  have hr2 := areplay_cons_of hr1 (astep_tk hp)
  refine after_getNowA ε c i _ H hc hR ⟨_, _, hr2, ?_, ?_⟩
  · simp [upd, ht1]
  · simpa [consO] using hf1

theorem holdPull_post {ε : AEnv} {c : CPU} {i tn : Nat} {h₀ : HLogA} (hc : c < NCPU) (hR : RelyA ε c)
    {r0 : ALog} (hi : LoopInvA c i tn h₀ r0) (hn : now (projL i r0) = tn) :
    AcqPostA c i h₀ (holdPull ε c i r0) (memOf i (apull ε c (ev c i .hold :: apull ε c r0))) := by
  obtain ⟨S, H, hl, hw, hf⟩ := hi
  -- hold
  obtain ⟨S1, H1, hr1, hph1, -, hf1⟩ := pull_others hR hl
  have hw1 : (S1.lk i).phase c = .waiting tn := by rw [hph1]; exact hw
  have hp1 := areplay_proj hr1 i
  have inv1 := replay_inv hp1
  obtain ⟨hn1, -⟩ := replay_counts hp1
  have hge := now_pullA_ge ε c i r0
  have hle := inv1.waitGe c tn hw1
  have heq : (S1.lk i).now = tn := by omega
  have hps : pstep (S1.lk i) ⟨c, .hold⟩ = some (⟨(S1.lk i).ticket, (S1.lk i).now,
      setPhase (S1.lk i).phase c (.holding tn)⟩, some (.acq c)) := by
    simp [pstep, hc, hw1, heq]
  obtain ⟨S2, H2, hr2, hH2, hhold2, hclean2⟩ : ∃ S2 H2, areplay (ev c i .hold :: apull ε c r0) = some (S2, H2) ∧
      H2 = .acqA c i :: H1 ∧ Holding S2 c i ∧ S2.dirty i = false :=
    ⟨_, _, areplay_cons_of hr1 (astep_tk hps), by simp [consO, lift], ⟨tn, by simp⟩, by simp⟩
  -- pull: others cannot touch block `i`
  obtain ⟨S3, H3, hr3, hph3, hmem3, hf3⟩ := pull_others hR hr2
  have hhold3 : Holding S3 c i := by obtain ⟨t, ht⟩ := hhold2; exact ⟨t, by rw [hph3]; exact ht⟩
  have hclean3 := (hmem3 i hhold2).2 hclean2
  have hpull : astep S3 ⟨c, i, .pull⟩ = some (S3, none) := by simp [astep, hhold3]
  have hr4 := areplay_cons_of hr3 hpull
  refine ⟨S3, H3, hr4, hhold3, ?_, ?_⟩
  · rw [hf3, hH2, cpuFilterA_acq, hf1, hf]
  · rw [← areplay_mem hr3]
    exact ((areplay_di hr3) i).1 hclean3

theorem acquireA_guarantee {ε : AEnv} {c : CPU} {i : Nat} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H))
    (hidle : (S.lk i).phase c = .idle) {fuel : Nat} {r : ALog}
    (hspec : acquireSpecA ε c i fuel l = some r) :
    ∃ r0, r = holdPull ε c i r0 ∧ AcqPostA c i H r (memOf i (apull ε c (ev c i .hold :: apull ε c r0))) := by
  simp only [acquireSpecA, Option.map_eq_some_iff] at hspec
  obtain ⟨r0, hw, rfl⟩ := hspec
  have hi := acquireA_enter hc hR hl hidle
  have hn : now (projL i (ev c i .getNow :: apull ε c (ev c i .incTicket :: apull ε c l))) =
      now (projL i (apull ε c (ev c i .incTicket :: apull ε c l))) := by simp [projL, ev, now, countK]
  obtain ⟨hi', hn'⟩ := loopA_guarantee ε c i _ H hc hR fuel _ r0 hi (by rw [hn]; exact hw)
  exact ⟨r0, rfl, holdPull_post hc hR hi' hn'⟩

theorem acquireA_live_bounded {ε : AEnv} {c : CPU} {i : Nat} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H))
    (hidle : (S.lk i).phase c = .idle) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : FairA ε c i (ticket (projL i (apull ε c l))) bound) :
    ∃ r, acquireSpecA ε c i ((NCPU + 1) * (K + 1)) l = some r := by
  have hi := acquireA_enter hc hR hl hidle
  obtain ⟨hgap1, hgap2⟩ := loopInvA_gap c i _ H hi
  obtain ⟨f, r, hfle, hw⟩ := loopA_live_bounded ε c i _ H hc hR bound K hK hF _ _ _ rfl rfl hi
  have h1 := Nat.mul_le_mul_right (K + 1) (Nat.le_of_lt hgap2)
  have h2 : (NCPU + 1) * (K + 1) = NCPU * (K + 1) + (K + 1) := Nat.succ_mul _ _
  have h3 := hK (ev c i .getNow :: apull ε c (ev c i .incTicket :: apull ε c l))
  have hle : f ≤ (NCPU + 1) * (K + 1) := by omega
  have hw' := waitLoopA_mono_le ε c i _ hle hw
  have hn : now (projL i (ev c i .getNow :: apull ε c (ev c i .incTicket :: apull ε c l))) =
      now (projL i (apull ε c (ev c i .incTicket :: apull ε c l))) := by simp [projL, ev, now, countK]
  rw [hn] at hw'
  exact ⟨_, by simp only [acquireSpecA]; rw [hw']; rfl⟩

/-! ## `release(i)`: `push(i, v); inc_n(i)` -/

theorem releaseA_guarantee {ε : AEnv} {c : CPU} {i : Nat} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) (hhold : Holding S c i)
    (v : Val) :
    ∃ S' H', areplay (releaseSpecA ε c i v l) = some (S', H') ∧ (S'.lk i).phase c = .idle ∧
      (∃ E, H' = .relA c i v :: (E ++ H) ∧ ∀ e ∈ E, e.cpu ≠ c) ∧ hmemA i H' = v := by
  obtain ⟨S1, H1, hr1, hph1, -, hf1⟩ := pull_others hR hl
  have hhold1 : Holding S1 c i := by obtain ⟨t, ht⟩ := hhold; exact ⟨t, by rw [hph1]; exact ht⟩
  have hpush : astep S1 ⟨c, i, .push v⟩ = some (⟨S1.lk, upd S1.mem i v, upd S1.dirty i true⟩, none) := by
    simp [astep, hhold1]
  have hr2 := areplay_cons_of hr1 hpush
  have hhold2 : Holding ⟨S1.lk, upd S1.mem i v, upd S1.dirty i true⟩ c i := hhold1
  obtain ⟨S3, H3, hr3, hph3, hmem3, hf3⟩ := pull_others hR hr2
  obtain ⟨t, ht3⟩ : Holding S3 c i := by obtain ⟨t, ht⟩ := hhold2; exact ⟨t, by rw [hph3]; exact ht⟩
  have hm3 : S3.mem i = v := by rw [(hmem3 i hhold2).1]; simp
  have hps : pstep (S3.lk i) ⟨c, .incNow⟩ = some (⟨(S3.lk i).ticket, (S3.lk i).now + 1,
      setPhase (S3.lk i).phase c .idle⟩, some (.rel c)) := by simp [pstep, hc, ht3]
  have hr4 := areplay_cons_of hr3 (astep_tk hps)
  -- the high-level log only grew by other CPUs' events, then our release
  obtain ⟨E, hE⟩ := areplay_hext hl (ε.query c (⟨c, i, .push v⟩ :: apull ε c l) ++ [⟨c, i, .push v⟩] ++
    ε.query c l) (by simpa [apull, List.append_assoc] using hr3)
  have hfE : cpuFilterA c E = [] := by
    have := hf3.trans (by simpa [consO] using hf1)
    rw [hE] at this; simp only [cpuFilterA, List.filter_append] at this
    have h2 := congrArg List.length this; simp only [List.length_append] at h2
    simp only [cpuFilterA]; exact List.eq_nil_of_length_eq_zero (by omega)
  refine ⟨_, _, hr4, by simp, ⟨E, by simp [consO, lift, hm3, hE], fun e he hec => ?_⟩, by
    simp [consO, lift, hmemA, hm3]⟩
  have : e ∈ cpuFilterA c E := by simp [cpuFilterA, he, hec]
  rw [hfE] at this; simp at this

/-! ## The C code runs the specs -/

theorem loopA_sim (ε : AEnv) (c : CPU) (iv t : Val) :
    ∀ (fuel : Nat) (n : Val) (loc : Locals) (l r : ALog) (k : Cont APrim),
      loc "t" = t → loc "n" = n → loc "lk" = iv → waitLoopA ε c iv.toNat t fuel n l = some r →
      ∃ loc' : Locals, (∀ z, z ≠ "n" → loc' z = loc z) ∧
        Star (aprims ε c) ⟨loopA, k, loc, l⟩ ⟨.skip, k, loc', r⟩ := by
  intro fuel
  induction fuel with
  | zero =>
    intro n loc l r k ht hn hlk hw
    by_cases hnt : n = t
    · simp [waitLoopA, hnt] at hw
      subst hw
      exact ⟨loc, fun _ _ => rfl, Star.single (by simp [step, loopA, Expr.eval, BinOp.eval, ht, hn, hnt])⟩
    · simp [waitLoopA, hnt] at hw
  | succ f ih =>
    intro n loc l r k ht hn hlk hw
    by_cases hnt : n = t
    · simp [waitLoopA, hnt] at hw
      subst hw
      exact ⟨loc, fun _ _ => rfl, Star.single (by simp [step, loopA, Expr.eval, BinOp.eval, ht, hn, hnt])⟩
    · simp only [waitLoopA, hnt, ite_false] at hw
      let l1 := apull ε c l
      let v := BitVec.ofNat 32 (now (projL iv.toNat l1))
      let loc1 := loc.set "n" v
      obtain ⟨loc', hloc', hstar⟩ := ih v loc1 (ev c iv.toNat .getNow :: l1) r k
        (by simp [loc1, ht]) (by simp [loc1]) (by simp [loc1, hlk]) hw
      refine ⟨loc', fun z hz => by rw [hloc' z hz]; simp [loc1, hz], ?_⟩
      refine .step (c' := ⟨.call "n" .getNow [lkE], .loop (.bin .ne (.var "n") (.var "t"))
          (.call "n" .getNow [lkE]) k, loc, l⟩) (by simp [step, loopA, Expr.eval, BinOp.eval, ht, hn, hnt]) ?_
      refine .step (c' := ⟨.skip, .loop (.bin .ne (.var "n") (.var "t"))
          (.call "n" .getNow [lkE]) k, loc1, ev c iv.toNat .getNow :: l1⟩)
          (by simp [step, aprims, lkE, Expr.eval, hlk, loc1, v, l1]) ?_
      exact .step (c' := ⟨loopA, k, loc1, ev c iv.toNat .getNow :: l1⟩) (by simp [step, loopA]) hstar

/-- The C `acquire(i)` reaches the end of the spec; `v` holds the pulled block. -/
theorem acquireA_sim (ε : AEnv) (c : CPU) (fuel : Nat) (σ : Locals) (iv : Val) (l r : ALog)
    (k : Cont APrim) (hlk : σ "lk" = iv) (h : acquireSpecA ε c iv.toNat fuel l = some r) :
    ∃ r0 σ', r = holdPull ε c iv.toNat r0 ∧
      σ' "v" = memOf iv.toNat (apull ε c (ev c iv.toNat .hold :: apull ε c r0)) ∧
      (∀ z, z ≠ "t" → z ≠ "n" → z ≠ "_" → z ≠ "v" → σ' z = σ z) ∧
      Star (aprims ε c) ⟨acquireA, k, σ, l⟩ ⟨.skip, k, σ', r⟩ := by
  simp only [acquireSpecA, Option.map_eq_some_iff] at h
  obtain ⟨r0, hw, rfl⟩ := h
  let i := iv.toNat
  let l1 := apull ε c l
  let t := BitVec.ofNat 32 (ticket (projL i l1))
  let l2 : ALog := ev c i .incTicket :: l1
  let l3 := apull ε c l2
  let n := BitVec.ofNat 32 (now (projL i l3))
  let σ1 := σ.set "t" t
  let σ2 := σ1.set "n" n
  obtain ⟨σ3, hσ3, hloop⟩ := loopA_sim ε c iv t fuel n σ2 (ev c i .getNow :: l3) r0
    (.seq (.seq (.call "_" .hold [lkE]) (.call "v" .pull [lkE])) k)
    (by simp [σ2, σ1]) (by simp [σ2]) (by simp [σ2, σ1, hlk]) hw
  have hlk3 : σ3 "lk" = iv := by rw [hσ3 "lk" (by decide)]; simp [σ2, σ1, hlk]
  let r1 : ALog := ev c i .hold :: apull ε c r0
  let σ4 := σ3.set "_" 0
  refine ⟨r0, σ4.set "v" (memOf i (apull ε c r1)), rfl, by simp [r1, i], fun z h1 h2 h3 h4 => ?_, ?_⟩
  · simp [σ4, Locals.set, h1, h2, h3, h4, hσ3 z h2, σ2, σ1]
  let rest : Stmt APrim := .seq (.call "n" .getNow [lkE])
    (.seq loopA (.seq (.call "_" .hold [lkE]) (.call "v" .pull [lkE])))
  refine .step (c' := ⟨.call "t" .faiTicket [lkE], .seq rest k, σ, l⟩) (by simp [step, acquireA, rest]) ?_
  refine .step (c' := ⟨.skip, .seq rest k, σ1, l2⟩)
    (by simp [step, aprims, lkE, Expr.eval, hlk, σ1, t, l2, l1, i]) ?_
  refine .step (c' := ⟨rest, k, σ1, l2⟩) (by simp [step]) ?_
  refine .step (c' := ⟨.call "n" .getNow [lkE], .seq (.seq loopA (.seq (.call "_" .hold [lkE])
    (.call "v" .pull [lkE]))) k, σ1, l2⟩) (by simp [step, rest]) ?_
  refine .step (c' := ⟨.skip, .seq (.seq loopA (.seq (.call "_" .hold [lkE]) (.call "v" .pull [lkE]))) k,
    σ2, ev c i .getNow :: l3⟩) (by simp [step, aprims, lkE, Expr.eval, σ1, hlk, σ2, n, l3, i]) ?_
  refine .step (c' := ⟨.seq loopA (.seq (.call "_" .hold [lkE]) (.call "v" .pull [lkE])), k,
    σ2, ev c i .getNow :: l3⟩) (by simp [step]) ?_
  refine .step (c' := ⟨loopA, .seq (.seq (.call "_" .hold [lkE]) (.call "v" .pull [lkE])) k,
    σ2, ev c i .getNow :: l3⟩) (by simp [step]) ?_
  refine hloop.trans ?_
  refine .step (c' := ⟨.seq (.call "_" .hold [lkE]) (.call "v" .pull [lkE]), k, σ3, r0⟩) (by simp [step]) ?_
  refine .step (c' := ⟨.call "_" .hold [lkE], .seq (.call "v" .pull [lkE]) k, σ3, r0⟩) (by simp [step]) ?_
  refine .step (c' := ⟨.skip, .seq (.call "v" .pull [lkE]) k, σ4, r1⟩)
    (by simp [step, aprims, lkE, Expr.eval, hlk3, σ4, r1, i]) ?_
  refine .step (c' := ⟨.call "v" .pull [lkE], k, σ4, r1⟩) (by simp [step]) ?_
  exact Star.single (by simp [step, aprims, lkE, Expr.eval, σ4, hlk3, holdPull, r1, i])

theorem releaseA_sim (ε : AEnv) (c : CPU) (σ : Locals) (iv : Val) (l : ALog) (k : Cont APrim)
    (hlk : σ "lk" = iv) :
    Star (aprims ε c) ⟨releaseA, k, σ, l⟩
      ⟨.skip, k, (σ.set "_" 0).set "_" 0, releaseSpecA ε c iv.toNat (σ "v") l⟩ := by
  refine .step (c' := ⟨.call "_" .push [lkE, .var "v"], .seq (.call "_" .incNow [lkE]) k, σ, l⟩)
    (by simp [step, releaseA]) ?_
  refine .step (c' := ⟨.skip, .seq (.call "_" .incNow [lkE]) k, σ.set "_" 0,
    ⟨c, iv.toNat, .push (σ "v")⟩ :: apull ε c l⟩) (by simp [step, aprims, lkE, Expr.eval, hlk]) ?_
  refine .step (c' := ⟨.call "_" .incNow [lkE], k, σ.set "_" 0,
    ⟨c, iv.toNat, .push (σ "v")⟩ :: apull ε c l⟩) (by simp [step]) ?_
  exact Star.single (by simp [step, aprims, lkE, Expr.eval, hlk, releaseSpecA])

end LockArray
