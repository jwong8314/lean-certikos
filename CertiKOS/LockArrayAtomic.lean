import CertiKOS.LockArrayCPU

/-!
# Lock arrays: the atomic interface with data, and the refinement

The layer above: `acq(i)` atomically takes lock `i` and **returns the
contents of block `i`**. `rel(i, v)` atomically stores `v` into block `i` and
releases. The block's contents are a function of the high-level log
(`hmemA`: the value of the last `relA` on `i`). This is CCAL's push/pull
memory model seen from above. Shared data moves only with the lock.

* `hprimsA`: both primitives first pull other CPUs' high-level events. With
  many locks, other CPUs keep using *other* locks while we hold one, so `rel`
  also asks the environment. This is the per-lock reading of CCAL's critical
  state.
* `acquireA_refines`: the C `acquire(i)` (ticket loop, `hold`, `pull`) ⊑ the
  atomic `acq(i)` under a one-entry `ε_H` satisfying `HRelyA`. The C code
  ends with **the value the atomic `acq` returns**, and its high-level log is
  the atomic one plus later events of other CPUs.
* `releaseA_refines`: the C `push(i, v); inc_n(i)` ⊑ the atomic `rel(i, v)`,
  with the same high-level log.
-/

namespace LockArray

open ClightL Ticket

structure HEnvA where
  query : CPU → HLogA → List HEventA
  noSelf : ∀ c h e, e ∈ query c h → e.cpu ≠ c

def hpullA (εH : HEnvA) (c : CPU) (h : HLogA) : HLogA := εH.query c h ++ h

inductive HPrimA
  | acq | rel

def hprimsA (εH : HEnvA) (c : CPU) : Prims HPrimA HLogA
  | .acq, [iv], h =>
      let hp := hpullA εH c h
      if hreplay (projH iv.toNat hp) = some none then
        some (hmemA iv.toNat hp, .acqA c iv.toNat :: hp) else none
  | .rel, [iv, v], h =>
      let hp := hpullA εH c h
      if hreplay (projH iv.toNat hp) = some (some c) then some (0, .relA c iv.toNat v :: hp) else none
  | _, _, _ => none

/-- Other CPUs keep every lock's high-level log well formed. -/
def HRelyA (εH : HEnvA) (c : CPU) : Prop :=
  ∀ h, (∀ j, ∃ o, hreplay (projH j h) = some o) → ∀ j, ∃ o, hreplay (projH j (hpullA εH c h)) = some o

/-- A one-entry environment: at `k` the others did `E`. -/
def HEnvA.one (c : CPU) (k : HLogA) (E : List HEventA) (hE : ∀ e ∈ E, e.cpu ≠ c) : HEnvA where
  query d h := if d = c ∧ h = k then E else []
  noSelf := by
    intro d h e he
    by_cases hd : d = c ∧ h = k
    · rw [if_pos hd] at he; rw [hd.1]; exact hE e he
    · rw [if_neg hd] at he; simp at he

theorem hpullA_one (c : CPU) (k : HLogA) (E : List HEventA) (hE) (h : HLogA) :
    hpullA (HEnvA.one c k E hE) c h = if h = k then E ++ h else h := by
  by_cases e : h = k <;> simp [hpullA, HEnvA.one, e]

/-! ## Facts about high-level logs -/

theorem projH_append (i : Nat) (a b : HLogA) : projH i (a ++ b) = projH i a ++ projH i b := by
  induction a with
  | nil => rfl
  | cons e a ih => cases e <;> simp only [List.cons_append, projH, ih] <;> split <;> rfl

theorem projH_cpu {i : Nat} {c : CPU} : ∀ {E : HLogA}, (∀ e ∈ E, e.cpu ≠ c) → ∀ e ∈ projH i E, e.cpu ≠ c
  | [], _, e, he => by simp [projH] at he
  | x :: E, h, e, he => by
    have ih := projH_cpu (i := i) (E := E) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have hx := h x List.mem_cons_self
    cases x with
    | acqA d j =>
      simp only [projH] at he; split at he
      · rcases List.mem_cons.1 he with rfl | he
        · simpa [HEvent.cpu, HEventA.cpu] using hx
        · exact ih e he
      · exact ih e he
    | relA d j v =>
      simp only [projH] at he; split at he
      · rcases List.mem_cons.1 he with rfl | he
        · simpa [HEvent.cpu, HEventA.cpu] using hx
        · exact ih e he
      · exact ih e he

theorem hreplay_suffix : ∀ (a : List HEvent) {b : List HEvent} {o : Option CPU},
    hreplay (a ++ b) = some o → ∃ o', hreplay b = some o'
  | [], b, o, h => ⟨o, h⟩
  | e :: a, b, o, h => by
    simp only [List.cons_append, hreplay] at h
    split at h
    · simp at h
    · rename_i o1 h1; exact hreplay_suffix a h1

theorem hmemA_skip {i : Nat} : ∀ {E : HLogA}, projH i E = [] → ∀ X, hmemA i (E ++ X) = hmemA i X
  | [], _, X => rfl
  | e :: E, h, X => by
    cases e with
    | acqA d j =>
      simp only [projH] at h; split at h
      · simp at h
      · simp [hmemA, hmemA_skip h X]
    | relA d j v =>
      simp only [projH] at h; split at h
      · simp at h
      · rename_i hj; simp [hmemA, hj, hmemA_skip h X]

/-- A list whose events of `c` are exactly `[x]` splits around `x`. -/
theorem filter_single {c : CPU} {x : HEventA} (hx : x.cpu = c) :
    ∀ {E : HLogA}, cpuFilterA c E = [x] →
      ∃ E2 E1, E = E2 ++ x :: E1 ∧ (∀ e ∈ E2, e.cpu ≠ c) ∧ (∀ e ∈ E1, e.cpu ≠ c)
  | [], h => by simp [cpuFilterA] at h
  | e :: E, h => by
    by_cases he : e.cpu = c
    · have h' : e :: cpuFilterA c E = [x] := by simpa [cpuFilterA, he] using h
      simp only [List.cons.injEq] at h'
      obtain ⟨rfl, hE⟩ := h'
      refine ⟨[], E, rfl, by simp, fun e' he' hc => ?_⟩
      have : e' ∈ cpuFilterA c E := by simp [cpuFilterA, he', hc]
      rw [hE] at this; simp at this
    · have h' : cpuFilterA c E = [x] := by simpa [cpuFilterA, he] using h
      obtain ⟨E2, E1, rfl, h2, h1⟩ := filter_single hx h'
      refine ⟨e :: E2, E1, rfl, fun e' he' => ?_, h1⟩
      rcases List.mem_cons.1 he' with rfl | he'
      · exact he
      · exact h2 e' he'

/-! ## The C acquire extends the log -/

theorem waitLoopA_ext (ε : AEnv) (c : CPU) (i : Nat) (t : Val) :
    ∀ f n l r, waitLoopA ε c i t f n l = some r → ∃ xs, r = xs ++ l := by
  intro f
  induction f with
  | zero => intro n l r h; by_cases hnt : n = t <;> simp_all [waitLoopA]
  | succ f ih =>
    intro n l r h
    by_cases hnt : n = t
    · simp [waitLoopA, hnt] at h; exact ⟨[], by simp [h]⟩
    · simp only [waitLoopA, hnt, ite_false] at h
      obtain ⟨xs, rfl⟩ := ih _ _ _ h
      exact ⟨xs ++ ev c i .getNow :: ε.query c l, by simp [apull]⟩

theorem ext_pull (ε : AEnv) (c : CPU) {r l : ALog} (h : ∃ xs, r = xs ++ l) :
    ∃ xs, apull ε c r = xs ++ l := by
  obtain ⟨xs, rfl⟩ := h; exact ⟨ε.query c (xs ++ l) ++ xs, by simp [apull]⟩

theorem ext_cons (e : AEvent) {r l : ALog} (h : ∃ xs, r = xs ++ l) : ∃ xs, e :: r = xs ++ l := by
  obtain ⟨xs, rfl⟩ := h; exact ⟨e :: xs, rfl⟩

theorem acquireSpecA_ext {ε : AEnv} {c : CPU} {i fuel : Nat} {l r : ALog}
    (h : acquireSpecA ε c i fuel l = some r) : ∃ xs, r = xs ++ l := by
  simp only [acquireSpecA, Option.map_eq_some_iff] at h
  obtain ⟨r0, hw, rfl⟩ := h
  obtain ⟨ys, hys⟩ := waitLoopA_ext ε c i _ _ _ _ _ hw
  obtain ⟨a, ha⟩ := ext_cons (ev c i .getNow) (ext_pull ε c (ext_cons (ev c i .incTicket)
    (ext_pull ε c (r := l) (l := l) ⟨[], rfl⟩)))
  have h0 : ∃ xs, r0 = xs ++ l := ⟨ys ++ a, by rw [hys, ha, List.append_assoc]⟩
  exact ext_cons _ (ext_pull ε c (ext_cons _ (ext_pull ε c h0)))

/-! ## `acquire(i)` ⊑ atomic `acq(i)` -/

theorem acquireA_refines {ε : AEnv} {c : CPU} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) {iv : Val}
    (hidle : (S.lk iv.toNat).phase c = .idle) (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : FairA ε c iv.toNat (ticket (projL iv.toNat (apull ε c l))) bound)
    (σ : Locals) (hlk : σ "lk" = iv) (k : Cont APrim) :
    ∃ (εH : HEnvA) (r : ALog) (σ' : Locals) (E2 : HLogA) (S' : AState),
      HRelyA εH c ∧
      Star (aprims ε c) ⟨acquireA, k, σ, l⟩ ⟨.skip, k, σ', r⟩ ∧
      hprimsA εH c .acq [iv] H = some (σ' "v", .acqA c iv.toNat :: hpullA εH c H) ∧
      areplay r = some (S', E2 ++ .acqA c iv.toNat :: hpullA εH c H) ∧
      (∀ e ∈ E2, e.cpu ≠ c) ∧ Holding S' c iv.toNat := by
  obtain ⟨r, hspec⟩ := acquireA_live_bounded hc hR hl hidle bound K hK hF
  obtain ⟨r0, σ', hr0, hv, -, hstar⟩ := acquireA_sim ε c _ σ iv l r k hlk hspec
  obtain ⟨r0', hr0', S3, H3, hr3, hhold3, hf3, hv3⟩ := acquireA_guarantee hc hR hl hidle hspec
  -- the value the C code pulled
  have hval : σ' "v" = hmemA iv.toNat H3 := by
    have e1 : σ' "v" = memOf iv.toNat r.tail := by rw [hv, hr0]; rfl
    have e2 : memOf iv.toNat (apull ε c (ev c iv.toNat .hold :: apull ε c r0')) = memOf iv.toNat r.tail := by
      rw [hr0']; rfl
    rw [e1, ← e2, hv3]
  -- the high-level log: others' events, our acq, others' events
  obtain ⟨xs, rfl⟩ := acquireSpecA_ext hspec
  obtain ⟨E, hE⟩ := areplay_hext hl xs hr3
  have hfE : cpuFilterA c E = [.acqA c iv.toNat] := by
    rw [hE] at hf3; simp only [cpuFilterA, List.filter_append] at hf3
    exact List.append_cancel_right hf3
  obtain ⟨E2, E1, rfl, hE2, hE1⟩ := filter_single (by rfl) hfE
  have hE' : H3 = E2 ++ (.acqA c iv.toNat :: (E1 ++ H)) := by rw [hE]; simp
  let εH := HEnvA.one c H E1 hE1
  have hpl : hpullA εH c H = E1 ++ H := by simp [εH, hpullA_one]
  have hall : ∀ j, ∃ o, hreplay (projH j H3) = some o := fun j =>
    let ⟨o, ho, _⟩ := replay_hreplay (areplay_proj hr3 j); ⟨o, ho⟩
  have hsplit : ∀ j, projH j H3 = (projH j E2 ++ projH j [.acqA c iv.toNat]) ++ projH j (E1 ++ H) := by
    intro j
    rw [hE', show E2 ++ HEventA.acqA c iv.toNat :: (E1 ++ H) = E2 ++ ([.acqA c iv.toNat] ++ (E1 ++ H))
      from rfl, projH_append, projH_append, List.append_assoc]
  have hsuf : ∀ j, ∃ o, hreplay (projH j (E1 ++ H)) = some o := fun j => by
    obtain ⟨o, ho⟩ := hall j; rw [hsplit j] at ho; exact hreplay_suffix _ ho
  -- lock `iv` is free just before our acq, and nobody touches it after
  have hi3 : projH iv.toNat H3 = projH iv.toNat E2 ++ (.acq c :: projH iv.toNat (E1 ++ H)) := by
    rw [hE', projH_append]; simp [projH]
  obtain ⟨o3, ho3⟩ := hall iv.toNat
  rw [hi3] at ho3
  obtain ⟨o4, ho4⟩ := hreplay_suffix _ ho3
  have hfree : hreplay (projH iv.toNat (E1 ++ H)) = some none := hreplay_acq ho4
  have hheld : hreplay (.acq c :: projH iv.toNat (E1 ++ H)) = some (some c) := by
    simp [hreplay, hfree, hstep]
  have hE2i : projH iv.toNat E2 = [] := held_no_env hheld _ (projH_cpu hE2) ho3
  have hval' : σ' "v" = hmemA iv.toNat (E1 ++ H) := by
    rw [hval, hE', hmemA_skip hE2i]; simp [hmemA]
  refine ⟨εH, _, σ', E2, S3, ?_, hstar, ?_, ?_, hE2, hhold3⟩
  · intro h hh j
    by_cases e : h = H
    · subst e; rw [hpl]; exact hsuf j
    · simp only [εH, hpullA_one, e, ite_false]; exact hh j
  · simp [hprimsA, hpl, hfree, hval']
  · rw [hpl]; rw [hE'] at hr3; exact hr3

/-! ## `release(i)` ⊑ atomic `rel(i, v)` -/

theorem releaseA_refines {ε : AEnv} {c : CPU} (hc : c < NCPU) (hR : RelyA ε c)
    {l : ALog} {S : AState} {H : HLogA} (hl : areplay l = some (S, H)) {iv : Val}
    (hhold : Holding S c iv.toNat) (σ : Locals) (hlk : σ "lk" = iv) (k : Cont APrim) :
    ∃ (εH : HEnvA) (S' : AState),
      HRelyA εH c ∧
      Star (aprims ε c) ⟨releaseA, k, σ, l⟩
        ⟨.skip, k, (σ.set "_" 0).set "_" 0, releaseSpecA ε c iv.toNat (σ "v") l⟩ ∧
      hprimsA εH c .rel [iv, σ "v"] H = some (0, .relA c iv.toNat (σ "v") :: hpullA εH c H) ∧
      areplay (releaseSpecA ε c iv.toNat (σ "v") l) =
        some (S', .relA c iv.toNat (σ "v") :: hpullA εH c H) ∧
      (S'.lk iv.toNat).phase c = .idle ∧ hmemA iv.toNat (.relA c iv.toNat (σ "v") :: hpullA εH c H) = σ "v" := by
  obtain ⟨S', H', hr, hidle, ⟨E, rfl, hE⟩, hm⟩ := releaseA_guarantee hc hR hl hhold (σ "v")
  let εH := HEnvA.one c H E hE
  have hpl : hpullA εH c H = E ++ H := by simp [εH, hpullA_one]
  have hall : ∀ j, ∃ o, hreplay (projH j (.relA c iv.toNat (σ "v") :: (E ++ H))) = some o := fun j =>
    let ⟨o, ho, _⟩ := replay_hreplay (areplay_proj hr j); ⟨o, ho⟩
  have hsuf : ∀ j, ∃ o, hreplay (projH j (E ++ H)) = some o := fun j => by
    obtain ⟨o, ho⟩ := hall j
    rw [show HEventA.relA c iv.toNat (σ "v") :: (E ++ H) = [.relA c iv.toNat (σ "v")] ++ (E ++ H) from rfl,
      projH_append] at ho
    exact hreplay_suffix _ ho
  obtain ⟨o, ho⟩ := hall iv.toNat
  have hheld : hreplay (projH iv.toNat (E ++ H)) = some (some c) := by
    simp only [projH, ite_true] at ho; exact hreplay_rel ho
  refine ⟨εH, S', ?_, releaseA_sim ε c σ iv l k hlk, ?_, by rw [hpl]; exact hr, hidle, by simp [hmemA]⟩
  · intro h hh j
    by_cases e : h = H
    · subst e; rw [hpl]; exact hsuf j
    · simp only [εH, hpullA_one, e, ite_false]; exact hh j
  · simp [hprimsA, hpl, hheld]

end LockArray
