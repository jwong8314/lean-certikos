import CertiKOS.MCSFair
import CertiKOS.Link

/-!
# Multicore linking for the MCS lock

The MCS version of `Link.lean`/`LinkA.lean`. The multicore machine runs every
CPU's `mprims` on one global MCS log, with no environment (`noEnvM`). If every
CPU meets its per-CPU guarantee `GuarM` (under any environment satisfying
`RelyM`, every log it reaches replays), then every multicore run is explained
by the per-CPU layers, under environments built from the run that satisfy
`RelyM` (`composeM`, `transferM`).
-/

namespace LinkM

open ClightL Ticket ClightToPy MCS
open Link (step_cases)

def noEnvM : MEnv := ⟨fun _ _ => [], by intro c l e he; simp at he⟩

@[simp] theorem mpull_noEnvM (c : CPU) (l : MLog) : mpull noEnvM c l = l := rfl

theorem mprims_pull {ε ε' : MEnv} {c : CPU} {l l' : MLog} (h : mpull ε c l = mpull ε' c l')
    (p : MPrim) (args : List Val) : mprims ε c p args l = mprims ε' c p args l' := by
  cases p <;> cases args <;> simp [mprims, h]

theorem mprims_len {ε : MEnv} {c : CPU} {p : MPrim} {args : List Val} {l l' : MLog} {v : Val}
    (h : mprims ε c p args l = some (v, l')) : l.length < l'.length := by
  cases p <;> cases args <;> simp [mprims] at h <;> obtain ⟨-, rfl⟩ := h <;> simp [mpull] <;> omega

theorem step_lenM {ε : MEnv} {c : CPU} {x y : Config MPrim MLog}
    (hs : ClightL.step (mprims ε c) x = some y) : x.abs.length ≤ y.abs.length := by
  rcases step_cases (t := thr x) (a := x.abs) hs with ⟨h, -⟩ | ⟨⟨_, _, _, hv⟩, -⟩
  · simp [h]
  · exact Nat.le_of_lt (mprims_len hv)

theorem star_lenM {ε : MEnv} {c : CPU} {x y : Config MPrim MLog} (h : Star (mprims ε c) x y) :
    x.abs.length ≤ y.abs.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hs _ ih => exact Nat.le_trans (step_lenM hs) ih

/-- A per-CPU run only consulted the environment at logs shorter than where it
ended, so changing the environment elsewhere does not change the run. -/
theorem star_congrM {ε ε' : MEnv} {c : CPU} {x y : Config MPrim MLog} (h : Star (mprims ε c) x y)
    (hag : ∀ l : MLog, l.length < y.abs.length → ε'.query c l = ε.query c l) :
    Star (mprims ε' c) x y := by
  induction h with
  | refl => exact .refl _
  | @step x x' y hs hrest ih =>
    refine .step ?_ (ih hag)
    rcases step_cases (t := thr x) (a := x.abs) hs with ⟨habs, hall⟩ | ⟨⟨p, args, v, hv⟩, hQ⟩
    · have := hall (mprims ε' c) x.abs
      have h2 : (thr x').cfg x.abs = x' := by rw [← habs]; rfl
      rw [h2] at this; exact this
    · have hlt : x.abs.length < y.abs.length :=
        Nat.lt_of_lt_of_le (mprims_len hv) (star_lenM hrest)
      exact hQ (mprims ε' c) x.abs fun p args =>
        mprims_pull (by simp [mpull, hag x.abs hlt]) p args

/-- One step of the global machine adds at most one event, by the CPU that moved. -/
theorem gstep_logM {j : CPU} {t : CThread MPrim} {l : MLog} {c' : Config MPrim MLog}
    (hs : ClightL.step (mprims noEnvM j) (t.cfg l) = some c') :
    ∃ ys, c'.abs = ys ++ l ∧ ∀ e ∈ ys, e.cpu = j := by
  rcases step_cases hs with ⟨h, -⟩ | ⟨⟨p, args, v, hv⟩, -⟩
  · exact ⟨[], by simp [h], by simp⟩
  · cases p <;> cases args <;> simp [mprims] at hv <;>
      obtain ⟨-, h⟩ := hv <;> (rw [← h]; exact ⟨[_], rfl, by simp⟩)

/-! ## Environments built from a run -/

/-- `ε`, except that CPU `c`'s query at log `k` is answered with `xs`. -/
def updM (ε : MEnv) (c : CPU) (k : MLog) (xs : List MEvent) (hx : ∀ e ∈ xs, e.cpu ≠ c) :
    MEnv where
  query d l := if d = c ∧ l = k then xs else ε.query d l
  noSelf := by
    intro d l e he
    by_cases h : d = c ∧ l = k
    · obtain ⟨rfl, rfl⟩ := h; simp at he; exact hx e he
    · simp only [h, ite_false] at he; exact ε.noSelf d l e he

theorem rely_noEnvM (c : CPU) : RelyM noEnvM c := ⟨fun l s h hl => ⟨s, h, by simpa [mpull, noEnvM] using hl⟩⟩

theorem rely_updM {ε : MEnv} {c : CPU} {k : MLog} {xs : List MEvent} {hx : ∀ e ∈ xs, e.cpu ≠ c}
    (hR : RelyM ε c) (hk : ∃ s h, mreplay (xs ++ k) = some (s, h)) : RelyM (updM ε c k xs hx) c where
  conform := by
    intro l s h hl
    by_cases e : l = k
    · subst e; simpa [mpull, updM] using hk
    · simpa [mpull, updM, e] using hR.conform l s h hl

/-! ## Linking -/

abbrev PGM : Nat → Prims MPrim MLog := fun i => mprims noEnvM i

/-- Per-CPU guarantee of thread `t` started at `l0`: under *any* environment
satisfying the rely, every log it reaches replays (it follows the protocol). -/
def GuarM (c : CPU) (t : CThread MPrim) (l0 : MLog) : Prop :=
  ∀ ε, RelyM ε c → ∀ x, Star (mprims ε c) (t.cfg l0) x → ∃ s h, mreplay x.abs = some (s, h)

/-- CPU `c`, started as `t0` at `l0`, is now `t`, and the global log is `l`:
its per-CPU run under `ε` reached `t` at its own view `lc`, and the global log
is `lc` plus events of other CPUs. -/
def ViewM (ε : MEnv) (c : CPU) (t0 : CThread MPrim) (l0 : MLog) (t : CThread MPrim) (l : MLog) :
    Prop :=
  ∃ lc xs, Star (mprims ε c) (t0.cfg l0) (t.cfg lc) ∧ l = xs ++ lc ∧ ∀ e ∈ xs, e.cpu ≠ c

/-- The multicore state `(cs, l)` reached from `(cs0, l0)` is explained by the
per-CPU layers: the log replays and every CPU has a rely-respecting view. -/
def LinkedM (cs0 : List (CThread MPrim)) (l0 : MLog) (cs : List (CThread MPrim)) (l : MLog) : Prop :=
  (∃ s h, mreplay l = some (s, h)) ∧ ∃ hlen : cs.length = cs0.length,
    ∀ c (hc : c < cs0.length), ∃ ε, RelyM ε c ∧ ViewM ε c cs0[c] l0 (cs[c]'(hlen ▸ hc)) l

theorem linkedM_init {cs0 : List (CThread MPrim)} {l0 : MLog} (h0 : ∃ s h, mreplay l0 = some (s, h)) :
    LinkedM cs0 l0 cs0 l0 :=
  ⟨h0, rfl, fun c _ => ⟨noEnvM, rely_noEnvM c, l0, [], .refl _, rfl, by simp⟩⟩

/-- The moving CPU: its view advances by one per-CPU step, under the
environment extended with the events the others appended since its last move. -/
theorem viewM_self {cs0 : List (CThread MPrim)} {l0 : MLog} {j : CPU} (hj0 : j < cs0.length)
    (hG : GuarM j cs0[j] l0) {ε : MEnv} {t : CThread MPrim} {l : MLog} {c' : Config MPrim MLog}
    (hrep : ∃ s h, mreplay l = some (s, h)) (hR : RelyM ε j) (hV : ViewM ε j cs0[j] l0 t l)
    (hst : ClightL.step (mprims noEnvM j) (t.cfg l) = some c') :
    (∃ s h, mreplay c'.abs = some (s, h)) ∧ ∃ ε', RelyM ε' j ∧ ViewM ε' j cs0[j] l0 (thr c') c'.abs := by
  obtain ⟨lj, xs, hstar, rfl, hx⟩ := hV
  have hR' : RelyM (updM ε j lj xs hx) j := rely_updM hR hrep
  have hstar' : Star (mprims (updM ε j lj xs hx) j) (cs0[j].cfg l0) (t.cfg lj) :=
    star_congrM hstar fun k hk => by
      have : k ≠ lj := fun e => by subst e; simp [CThread.cfg] at hk
      simp [updM, this]
  rcases step_cases hst with ⟨habs, hall⟩ | ⟨-, hQ⟩
  · refine ⟨habs ▸ hrep, _, hR', lj, xs, hstar'.trans (.single (hall _ lj)), habs, hx⟩
  · have hs : ClightL.step (mprims (updM ε j lj xs hx) j) (t.cfg lj) = some c' :=
      hQ _ lj fun p args => mprims_pull (by rw [mpull_noEnvM]; simp [mpull, updM]) p args
    have hstar'' := hstar'.trans (.single hs)
    exact ⟨hG _ hR' _ hstar'', _, hR', c'.abs, [], hstar'', by simp, by simp⟩

theorem linkM_step {cs0 : List (CThread MPrim)} {l0 : MLog}
    (hG : ∀ c (hc : c < cs0.length), GuarM c cs0[c] l0) {cs cs' : List (CThread MPrim)} {l l' : MLog}
    (hL : LinkedM cs0 l0 cs l) (hS : CStep PGM cs l cs' l') : LinkedM cs0 l0 cs' l' := by
  obtain ⟨hrep, hlen, hV⟩ := hL
  cases hS with
  | step j hj hst =>
  have hj0 : j < cs0.length := hlen ▸ hj
  obtain ⟨ε, hR, hVj⟩ := hV j hj0
  obtain ⟨hrep', ε', hR', hVj'⟩ := viewM_self hj0 (hG j hj0) hrep hR hVj hst
  obtain ⟨ys, hys, hyj⟩ := gstep_logM hst
  refine ⟨hrep', by simpa using hlen, fun c hc => ?_⟩
  by_cases hcj : c = j
  · subst hcj
    refine ⟨ε', hR', ?_⟩
    simpa only [List.getElem_set_self] using hVj'
  · obtain ⟨εc, hRc, lc, xs, hstar, rfl, hx⟩ := hV c hc
    refine ⟨εc, hRc, lc, ys ++ xs, ?_, by simp [hys], ?_⟩
    · simpa only [List.getElem_set_ne (Ne.symm hcj)] using hstar
    · intro e he
      rcases List.mem_append.1 he with he | he
      · rw [hyj e he]; exact Ne.symm hcj
      · exact hx e he

/-- **Parallel composition.** If every CPU meets its per-CPU guarantee, every
run of the multicore machine is explained by the per-CPU layers. -/
theorem composeM {cs0 : List (CThread MPrim)} {l0 : MLog}
    (hG : ∀ c (hc : c < cs0.length), GuarM c cs0[c] l0) (h0 : ∃ s h, mreplay l0 = some (s, h))
    {cs : List (CThread MPrim)} {l : MLog} (h : CSteps PGM cs0 l0 cs l) : LinkedM cs0 l0 cs l := by
  suffices ∀ {a b : List (CThread MPrim)} {la lb : MLog}, CSteps PGM a la b lb →
      LinkedM cs0 l0 a la → LinkedM cs0 l0 b lb from this h (linkedM_init h0)
  intro a b la lb hab
  induction hab with
  | refl => exact id
  | step h₁ _ ih => exact fun hL => ih (linkM_step hG hL h₁)

/-- **Transfer.** A property proved for the per-CPU layer under every
rely-respecting environment holds of every CPU of every multicore run. -/
theorem transferM {cs0 : List (CThread MPrim)} {l0 : MLog}
    (hG : ∀ c (hc : c < cs0.length), GuarM c cs0[c] l0) (h0 : ∃ s h, mreplay l0 = some (s, h))
    {Q : CPU → Config MPrim MLog → Prop}
    (hQ : ∀ c (hc : c < cs0.length) ε, RelyM ε c → ∀ x, Star (mprims ε c) (cs0[c].cfg l0) x → Q c x)
    {cs : List (CThread MPrim)} {l : MLog} (h : CSteps PGM cs0 l0 cs l) :
    ∀ c (hc : c < cs.length), ∃ lc xs, Q c (cs[c].cfg lc) ∧ l = xs ++ lc ∧ ∀ e ∈ xs, e.cpu ≠ c := by
  obtain ⟨-, hlen, hV⟩ := composeM hG h0 h
  intro c hc
  obtain ⟨ε, hR, lc, xs, hstar, hl, hx⟩ := hV c (hlen ▸ hc)
  exact ⟨lc, xs, hQ c _ ε hR _ hstar, hl, hx⟩

end LinkM
