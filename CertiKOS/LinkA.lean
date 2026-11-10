import CertiKOS.LockArrayFair
import CertiKOS.Link

/-!
# Multicore linking for the lock array

The lock-array version of `Link.lean`. The multicore machine runs every CPU's
`aprims` on one global array log, with no environment (`noEnvA`). Each CPU's
view of a run is a run of its per-CPU layer under an environment built from
the run (`updA`), and that environment satisfies `RelyA`, provided every CPU
meets its per-CPU guarantee `GuarA` (`composeA`, `transferA`).
-/

namespace LinkA

open ClightL Ticket ClightToPy LockArray
open Link (step_cases)

def noEnvA : AEnv := ⟨fun _ _ => [], by intro c l e he; simp at he⟩

@[simp] theorem apull_noEnvA (c : CPU) (l : ALog) : apull noEnvA c l = l := rfl

theorem aprims_pull {ε ε' : AEnv} {c : CPU} {l l' : ALog} (h : apull ε c l = apull ε' c l')
    (p : APrim) (args : List Val) : aprims ε c p args l = aprims ε' c p args l' := by
  cases p <;> rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [aprims, h]

theorem aprims_len {ε : AEnv} {c : CPU} {p : APrim} {args : List Val} {l l' : ALog} {v : Val}
    (h : aprims ε c p args l = some (v, l')) : l.length < l'.length := by
  cases p <;> rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [aprims] at h <;>
    obtain ⟨-, rfl⟩ := h <;> simp [apull] <;> omega

theorem step_lenA {ε : AEnv} {c : CPU} {x y : Config APrim ALog}
    (hs : ClightL.step (aprims ε c) x = some y) : x.abs.length ≤ y.abs.length := by
  rcases step_cases (t := thr x) (a := x.abs) hs with ⟨h, -⟩ | ⟨⟨_, _, _, hv⟩, -⟩
  · simp [h]
  · exact Nat.le_of_lt (aprims_len hv)

theorem star_lenA {ε : AEnv} {c : CPU} {x y : Config APrim ALog} (h : Star (aprims ε c) x y) :
    x.abs.length ≤ y.abs.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hs _ ih => exact Nat.le_trans (step_lenA hs) ih

/-- A per-CPU run only consulted the environment at logs shorter than where it
ended, so changing the environment elsewhere does not change the run. -/
theorem star_congrA {ε ε' : AEnv} {c : CPU} {x y : Config APrim ALog} (h : Star (aprims ε c) x y)
    (hag : ∀ l : ALog, l.length < y.abs.length → ε'.query c l = ε.query c l) :
    Star (aprims ε' c) x y := by
  induction h with
  | refl => exact .refl _
  | @step x x' y hs hrest ih =>
    refine .step ?_ (ih hag)
    rcases step_cases (t := thr x) (a := x.abs) hs with ⟨habs, hall⟩ | ⟨⟨p, args, v, hv⟩, hQ⟩
    · have := hall (aprims ε' c) x.abs
      have h2 : (thr x').cfg x.abs = x' := by rw [← habs]; rfl
      rw [h2] at this; exact this
    · have hlt : x.abs.length < y.abs.length :=
        Nat.lt_of_lt_of_le (aprims_len hv) (star_lenA hrest)
      exact hQ (aprims ε' c) x.abs fun p args =>
        aprims_pull (by simp [apull, hag x.abs hlt]) p args

/-- One step of the global machine adds at most one event, by the CPU that moved. -/
theorem gstep_logA {j : CPU} {t : CThread APrim} {l : ALog} {c' : Config APrim ALog}
    (hs : ClightL.step (aprims noEnvA j) (t.cfg l) = some c') :
    ∃ ys, c'.abs = ys ++ l ∧ ∀ e ∈ ys, e.cpu = j := by
  rcases step_cases hs with ⟨h, -⟩ | ⟨⟨p, args, v, hv⟩, -⟩
  · exact ⟨[], by simp [h], by simp⟩
  · cases p <;> rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [aprims] at hv <;>
      obtain ⟨-, h⟩ := hv <;> (rw [← h]; exact ⟨[_], rfl, by simp [ev]⟩)

/-! ## Environments built from a run -/

/-- `ε`, except that CPU `c`'s query at log `k` is answered with `xs`. -/
def updA (ε : AEnv) (c : CPU) (k : ALog) (xs : List AEvent) (hx : ∀ e ∈ xs, e.cpu ≠ c) :
    AEnv where
  query d l := if d = c ∧ l = k then xs else ε.query d l
  noSelf := by
    intro d l e he
    by_cases h : d = c ∧ l = k
    · obtain ⟨rfl, rfl⟩ := h; simp at he; exact hx e he
    · simp only [h, ite_false] at he; exact ε.noSelf d l e he

theorem rely_noEnvA (c : CPU) : RelyA noEnvA c := ⟨fun l s h hl => ⟨s, h, by simpa [apull, noEnvA] using hl⟩⟩

theorem rely_updA {ε : AEnv} {c : CPU} {k : ALog} {xs : List AEvent} {hx : ∀ e ∈ xs, e.cpu ≠ c}
    (hR : RelyA ε c) (hk : ∃ s h, areplay (xs ++ k) = some (s, h)) : RelyA (updA ε c k xs hx) c where
  conform := by
    intro l s h hl
    by_cases e : l = k
    · subst e; simpa [apull, updA] using hk
    · simpa [apull, updA, e] using hR.conform l s h hl

/-! ## Linking -/

abbrev PGA : Nat → Prims APrim ALog := fun i => aprims noEnvA i

/-- Per-CPU guarantee of thread `t` started at `l0`: under *any* environment
satisfying the rely, every log it reaches replays (it follows the protocol). -/
def GuarA (c : CPU) (t : CThread APrim) (l0 : ALog) : Prop :=
  ∀ ε, RelyA ε c → ∀ x, Star (aprims ε c) (t.cfg l0) x → ∃ s h, areplay x.abs = some (s, h)

/-- CPU `c`, started as `t0` at `l0`, is now `t`, and the global log is `l`:
its per-CPU run under `ε` reached `t` at its own view `lc`, and the global log
is `lc` plus events of other CPUs. -/
def ViewA (ε : AEnv) (c : CPU) (t0 : CThread APrim) (l0 : ALog) (t : CThread APrim) (l : ALog) :
    Prop :=
  ∃ lc xs, Star (aprims ε c) (t0.cfg l0) (t.cfg lc) ∧ l = xs ++ lc ∧ ∀ e ∈ xs, e.cpu ≠ c

/-- The multicore state `(cs, l)` reached from `(cs0, l0)` is explained by the
per-CPU layers: the log replays and every CPU has a rely-respecting view. -/
def LinkedA (cs0 : List (CThread APrim)) (l0 : ALog) (cs : List (CThread APrim)) (l : ALog) : Prop :=
  (∃ s h, areplay l = some (s, h)) ∧ ∃ hlen : cs.length = cs0.length,
    ∀ c (hc : c < cs0.length), ∃ ε, RelyA ε c ∧ ViewA ε c cs0[c] l0 (cs[c]'(hlen ▸ hc)) l

theorem linkedA_init {cs0 : List (CThread APrim)} {l0 : ALog} (h0 : ∃ s h, areplay l0 = some (s, h)) :
    LinkedA cs0 l0 cs0 l0 :=
  ⟨h0, rfl, fun c _ => ⟨noEnvA, rely_noEnvA c, l0, [], .refl _, rfl, by simp⟩⟩

/-- The moving CPU: its view advances by one per-CPU step, under the
environment extended with the events the others appended since its last move. -/
theorem viewA_self {cs0 : List (CThread APrim)} {l0 : ALog} {j : CPU} (hj0 : j < cs0.length)
    (hG : GuarA j cs0[j] l0) {ε : AEnv} {t : CThread APrim} {l : ALog} {c' : Config APrim ALog}
    (hrep : ∃ s h, areplay l = some (s, h)) (hR : RelyA ε j) (hV : ViewA ε j cs0[j] l0 t l)
    (hst : ClightL.step (aprims noEnvA j) (t.cfg l) = some c') :
    (∃ s h, areplay c'.abs = some (s, h)) ∧ ∃ ε', RelyA ε' j ∧ ViewA ε' j cs0[j] l0 (thr c') c'.abs := by
  obtain ⟨lj, xs, hstar, rfl, hx⟩ := hV
  have hR' : RelyA (updA ε j lj xs hx) j := rely_updA hR hrep
  have hstar' : Star (aprims (updA ε j lj xs hx) j) (cs0[j].cfg l0) (t.cfg lj) :=
    star_congrA hstar fun k hk => by
      have : k ≠ lj := fun e => by subst e; simp [CThread.cfg] at hk
      simp [updA, this]
  rcases step_cases hst with ⟨habs, hall⟩ | ⟨-, hQ⟩
  · refine ⟨habs ▸ hrep, _, hR', lj, xs, hstar'.trans (.single (hall _ lj)), habs, hx⟩
  · have hs : ClightL.step (aprims (updA ε j lj xs hx) j) (t.cfg lj) = some c' :=
      hQ _ lj fun p args => aprims_pull (by rw [apull_noEnvA]; simp [apull, updA]) p args
    have hstar'' := hstar'.trans (.single hs)
    exact ⟨hG _ hR' _ hstar'', _, hR', c'.abs, [], hstar'', by simp, by simp⟩

theorem linkA_step {cs0 : List (CThread APrim)} {l0 : ALog}
    (hG : ∀ c (hc : c < cs0.length), GuarA c cs0[c] l0) {cs cs' : List (CThread APrim)} {l l' : ALog}
    (hL : LinkedA cs0 l0 cs l) (hS : CStep PGA cs l cs' l') : LinkedA cs0 l0 cs' l' := by
  obtain ⟨hrep, hlen, hV⟩ := hL
  cases hS with
  | step j hj hst =>
  have hj0 : j < cs0.length := hlen ▸ hj
  obtain ⟨ε, hR, hVj⟩ := hV j hj0
  obtain ⟨hrep', ε', hR', hVj'⟩ := viewA_self hj0 (hG j hj0) hrep hR hVj hst
  obtain ⟨ys, hys, hyj⟩ := gstep_logA hst
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
theorem composeA {cs0 : List (CThread APrim)} {l0 : ALog}
    (hG : ∀ c (hc : c < cs0.length), GuarA c cs0[c] l0) (h0 : ∃ s h, areplay l0 = some (s, h))
    {cs : List (CThread APrim)} {l : ALog} (h : CSteps PGA cs0 l0 cs l) : LinkedA cs0 l0 cs l := by
  suffices ∀ {a b : List (CThread APrim)} {la lb : ALog}, CSteps PGA a la b lb →
      LinkedA cs0 l0 a la → LinkedA cs0 l0 b lb from this h (linkedA_init h0)
  intro a b la lb hab
  induction hab with
  | refl => exact id
  | step h₁ _ ih => exact fun hL => ih (linkA_step hG hL h₁)

/-- **Transfer.** A property proved for the per-CPU layer under every
rely-respecting environment holds of every CPU of every multicore run. -/
theorem transferA {cs0 : List (CThread APrim)} {l0 : ALog}
    (hG : ∀ c (hc : c < cs0.length), GuarA c cs0[c] l0) (h0 : ∃ s h, areplay l0 = some (s, h))
    {Q : CPU → Config APrim ALog → Prop}
    (hQ : ∀ c (hc : c < cs0.length) ε, RelyA ε c → ∀ x, Star (aprims ε c) (cs0[c].cfg l0) x → Q c x)
    {cs : List (CThread APrim)} {l : ALog} (h : CSteps PGA cs0 l0 cs l) :
    ∀ c (hc : c < cs.length), ∃ lc xs, Q c (cs[c].cfg lc) ∧ l = xs ++ lc ∧ ∀ e ∈ xs, e.cpu ≠ c := by
  obtain ⟨-, hlen, hV⟩ := composeA hG h0 h
  intro c hc
  obtain ⟨ε, hR, lc, xs, hstar, hl, hx⟩ := hV c (hlen ▸ hc)
  exact ⟨lc, xs, hQ c _ ε hR _ hstar, hl, hx⟩

end LinkA
