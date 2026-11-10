import CertiKOS.TicketLive

/-!
# Multicore linking: per-CPU layers compose into the shared-log machine

CCAL verifies each CPU `c` against its own layer `L0[c]`. The other CPUs exist
only as an environment context `ε` that answers queries (`pull ε c l`), with
a rely condition (`RelyP ε c`) on its answers. The real machine has no `ε`:
all CPUs append to one global log (`CStep (prims noEnv)`, used by
`TicketPy`/`TicketLive`). Multicore linking connects the two
([PLDI18] §3, parallel layer composition).

* **Projection** (`Linked`, `compose`). Every run of the multicore machine,
  seen from CPU `c`, is a run of the per-CPU machine `Star (prims ε c)` under
  an environment `ε` built from the run itself. `ε` answers each query of `c`
  with exactly the events the other CPUs appended since `c` last moved. CPU
  `c`'s view `lc` is a suffix of the global log, and everything above it was
  appended by the others.
* **Rely/guarantee composition** (`compose`). Suppose each CPU satisfies its
  per-CPU guarantee `Guar`: under *every* rely-respecting `ε`, every log it can
  reach replays. Then every global log replays, and every constructed `ε`
  satisfies `RelyP`. The circularity (rely needs the others' guarantees) is
  broken by induction on the run, as in CCAL.
* **Transfer** (`transfer`). Any property proved per-CPU under an arbitrary
  rely-respecting `ε` holds of every CPU in every multicore run.

Instance: the ticket-lock client.
* `client_guar`: the per-CPU guarantee, proved on `L0[c]` alone (program-point
  invariant `At` from `TicketLive`, but stepped under an arbitrary `ε`).
* `ticket_linked`, `multicore_cs_exclusive`: in every run of T ≤ NCPU CPUs,
  the log replays, each CPU is at a program point consistent with the protocol
  state, and at most one CPU is inside its critical section. All of it comes
  from the per-CPU proofs, with no global invariant.
-/

namespace Link

open ClightL Ticket ClightToPy TicketPy TicketLive

/-! ## Steps either ignore the layer or make exactly one primitive call -/

section Generic
variable {Pn Abs : Type}

theorem step_cases {P : Prims Pn Abs} {t : CThread Pn} {a : Abs} {c' : Config Pn Abs}
    (hs : ClightL.step P (t.cfg a) = some c') :
    (c'.abs = a ∧ ∀ (Q : Prims Pn Abs) b, ClightL.step Q (t.cfg b) = some ((thr c').cfg b)) ∨
    ((∃ p args v, P p args a = some (v, c'.abs)) ∧
      ∀ (Q : Prims Pn Abs) b, (∀ p args, Q p args b = P p args a) →
        ClightL.step Q (t.cfg b) = some ((thr c').cfg c'.abs)) := by
  obtain ⟨s, k, σ⟩ := t
  cases s with
  | call x p args =>
    right
    simp only [ClightL.step, CThread.cfg] at hs ⊢
    split at hs
    · rename_i v a' hv
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨⟨p, _, v, hv⟩, fun Q b hQ => ?_⟩
      rw [hQ, hv]; rfl
    · simp at hs
  | skip =>
    left
    cases k <;> simp only [ClightL.step, CThread.cfg, Option.some.injEq, reduceCtorEq] at hs <;>
      subst hs <;> exact ⟨rfl, fun _ _ => rfl⟩
  | assign x e =>
    left; simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hs; subst hs
    exact ⟨rfl, fun _ _ => rfl⟩
  | seq s₁ s₂ =>
    left; simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hs; subst hs
    exact ⟨rfl, fun _ _ => rfl⟩
  | ite e s₁ s₂ =>
    left; simp only [ClightL.step, CThread.cfg, Option.some.injEq] at hs; subst hs
    exact ⟨rfl, fun _ _ => rfl⟩
  | «while» e b =>
    left
    rw [cstep_while] at hs
    by_cases he : e.eval σ = 0
    · rw [if_pos he, Option.some.injEq] at hs; subst hs
      exact ⟨rfl, fun Q b' => by rw [cstep_while, if_pos he]; rfl⟩
    · rw [if_neg he, Option.some.injEq] at hs; subst hs
      exact ⟨rfl, fun Q b' => by rw [cstep_while, if_neg he]; rfl⟩

end Generic

/-! ## The ticket layer: primitives depend on the environment only through `pull` -/

theorem prims_pull {ε ε' : EnvCtx} {c : CPU} {l l' : Log} (h : pull ε c l = pull ε' c l')
    (p : Prim) (args : List Val) : prims ε c p args l = prims ε' c p args l' := by
  cases p <;> cases args <;> simp [prims, h]

theorem prims_len {ε : EnvCtx} {c : CPU} {p : Prim} {args : List Val} {l l' : Log} {v : Val}
    (h : prims ε c p args l = some (v, l')) : l.length < l'.length := by
  cases p <;> cases args <;> simp [prims] at h <;> obtain ⟨-, rfl⟩ := h <;> simp [pull] <;> omega

theorem step_len {ε : EnvCtx} {c : CPU} {x y : Config Prim Log}
    (hs : ClightL.step (prims ε c) x = some y) : x.abs.length ≤ y.abs.length := by
  rcases step_cases (t := thr x) (a := x.abs) hs with ⟨h, -⟩ | ⟨⟨_, _, _, hv⟩, -⟩
  · simp [h]
  · exact Nat.le_of_lt (prims_len hv)

theorem star_len {ε : EnvCtx} {c : CPU} {x y : Config Prim Log} (h : Star (prims ε c) x y) :
    x.abs.length ≤ y.abs.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hs _ ih => exact Nat.le_trans (step_len hs) ih

/-- A per-CPU run only consulted the environment at logs shorter than where it
ended, so changing the environment elsewhere does not change the run. -/
theorem star_congr {ε ε' : EnvCtx} {c : CPU} {x y : Config Prim Log} (h : Star (prims ε c) x y)
    (hag : ∀ l : Log, l.length < y.abs.length → ε'.query c l = ε.query c l) :
    Star (prims ε' c) x y := by
  induction h with
  | refl => exact .refl _
  | @step x x' y hs hrest ih =>
    refine .step ?_ (ih hag)
    rcases step_cases (t := thr x) (a := x.abs) hs with ⟨habs, hall⟩ | ⟨⟨p, args, v, hv⟩, hQ⟩
    · have := hall (prims ε' c) x.abs
      have h2 : (thr x').cfg x.abs = x' := by rw [← habs]; rfl
      rw [h2] at this; exact this
    · have hlt : x.abs.length < y.abs.length :=
        Nat.lt_of_lt_of_le (prims_len hv) (star_len hrest)
      exact hQ (prims ε' c) x.abs fun p args =>
        prims_pull (by simp [pull, hag x.abs hlt]) p args

/-- One step of the global machine adds at most one event, by the CPU that moved. -/
theorem gstep_log {j : CPU} {t : CThread Prim} {l : Log} {c' : Config Prim Log}
    (hs : ClightL.step (prims noEnv j) (t.cfg l) = some c') :
    ∃ ys, c'.abs = ys ++ l ∧ ∀ e ∈ ys, e.cpu = j := by
  rcases step_cases hs with ⟨h, -⟩ | ⟨⟨p, args, v, hv⟩, -⟩
  · exact ⟨[], by simp [h], by simp⟩
  · cases p <;> cases args <;> simp [prims] at hv <;> obtain ⟨-, h⟩ := hv <;>
      (rw [← h]; exact ⟨[_], rfl, by simp⟩)

/-! ## Environments built from a run -/

/-- `ε`, except that CPU `c`'s query at log `k` is answered with `xs`. -/
def upd (ε : EnvCtx) (c : CPU) (k : Log) (xs : List Event) (hx : ∀ e ∈ xs, e.cpu ≠ c) :
    EnvCtx where
  query d l := if d = c ∧ l = k then xs else ε.query d l
  noSelf := by
    intro d l e he
    by_cases h : d = c ∧ l = k
    · obtain ⟨rfl, rfl⟩ := h; simp at he; exact hx e he
    · simp only [h, ite_false] at he; exact ε.noSelf d l e he

theorem rely_noEnv (c : CPU) : RelyP noEnv c := ⟨fun l s h hl => ⟨s, h, by simpa using hl⟩⟩

theorem rely_upd {ε : EnvCtx} {c : CPU} {k : Log} {xs : List Event} {hx : ∀ e ∈ xs, e.cpu ≠ c}
    (hR : RelyP ε c) (hk : ∃ s h, replay (xs ++ k) = some (s, h)) : RelyP (upd ε c k xs hx) c where
  conform := by
    intro l s h hl
    by_cases e : l = k
    · subst e; simpa [pull, upd] using hk
    · simpa [pull, upd, e] using hR.conform l s h hl

/-! ## Linking -/

abbrev PG : Nat → Prims Prim Log := fun i => prims noEnv i

/-- Per-CPU guarantee of thread `t` started at `l0`: under *any* environment
satisfying the rely, every log it reaches replays (it follows the protocol). -/
def Guar (c : CPU) (t : CThread Prim) (l0 : Log) : Prop :=
  ∀ ε, RelyP ε c → ∀ x, Star (prims ε c) (t.cfg l0) x → ∃ s h, replay x.abs = some (s, h)

/-- CPU `c`, started as `t0` at `l0`, is now `t`, and the global log is `l`:
its per-CPU run under `ε` reached `t` at its own view `lc`, and the global log
is `lc` plus events of other CPUs. -/
def View (ε : EnvCtx) (c : CPU) (t0 : CThread Prim) (l0 : Log) (t : CThread Prim) (l : Log) :
    Prop :=
  ∃ lc xs, Star (prims ε c) (t0.cfg l0) (t.cfg lc) ∧ l = xs ++ lc ∧ ∀ e ∈ xs, e.cpu ≠ c

/-- The multicore state `(cs, l)` reached from `(cs0, l0)` is explained by the
per-CPU layers: the log replays and every CPU has a rely-respecting view. -/
def Linked (cs0 : List (CThread Prim)) (l0 : Log) (cs : List (CThread Prim)) (l : Log) : Prop :=
  (∃ s h, replay l = some (s, h)) ∧ ∃ hlen : cs.length = cs0.length,
    ∀ c (hc : c < cs0.length), ∃ ε, RelyP ε c ∧ View ε c cs0[c] l0 (cs[c]'(hlen ▸ hc)) l

theorem linked_init {cs0 : List (CThread Prim)} {l0 : Log} (h0 : ∃ s h, replay l0 = some (s, h)) :
    Linked cs0 l0 cs0 l0 :=
  ⟨h0, rfl, fun c _ => ⟨noEnv, rely_noEnv c, l0, [], .refl _, rfl, by simp⟩⟩

/-- The moving CPU: its view advances by one per-CPU step, under the
environment extended with the events the others appended since its last move. -/
theorem view_self {cs0 : List (CThread Prim)} {l0 : Log} {j : CPU} (hj0 : j < cs0.length)
    (hG : Guar j cs0[j] l0) {ε : EnvCtx} {t : CThread Prim} {l : Log} {c' : Config Prim Log}
    (hrep : ∃ s h, replay l = some (s, h)) (hR : RelyP ε j) (hV : View ε j cs0[j] l0 t l)
    (hst : ClightL.step (prims noEnv j) (t.cfg l) = some c') :
    (∃ s h, replay c'.abs = some (s, h)) ∧ ∃ ε', RelyP ε' j ∧ View ε' j cs0[j] l0 (thr c') c'.abs := by
  obtain ⟨lj, xs, hstar, rfl, hx⟩ := hV
  have hR' : RelyP (upd ε j lj xs hx) j := rely_upd hR hrep
  have hstar' : Star (prims (upd ε j lj xs hx) j) (cs0[j].cfg l0) (t.cfg lj) :=
    star_congr hstar fun k hk => by
      have : k ≠ lj := fun e => by subst e; simp [CThread.cfg] at hk
      simp [upd, this]
  rcases step_cases hst with ⟨habs, hall⟩ | ⟨-, hQ⟩
  · refine ⟨habs ▸ hrep, _, hR', lj, xs, hstar'.trans (.single (hall _ lj)), habs, hx⟩
  · have hs : ClightL.step (prims (upd ε j lj xs hx) j) (t.cfg lj) = some c' :=
      hQ _ lj fun p args => prims_pull (by rw [pull_noEnv]; simp [pull, upd]) p args
    have hstar'' := hstar'.trans (.single hs)
    exact ⟨hG _ hR' _ hstar'', _, hR', c'.abs, [], hstar'', by simp, by simp⟩

theorem link_step {cs0 : List (CThread Prim)} {l0 : Log}
    (hG : ∀ c (hc : c < cs0.length), Guar c cs0[c] l0) {cs cs' : List (CThread Prim)} {l l' : Log}
    (hL : Linked cs0 l0 cs l) (hS : CStep PG cs l cs' l') : Linked cs0 l0 cs' l' := by
  obtain ⟨hrep, hlen, hV⟩ := hL
  cases hS with
  | step j hj hst =>
  have hj0 : j < cs0.length := hlen ▸ hj
  obtain ⟨ε, hR, hVj⟩ := hV j hj0
  obtain ⟨hrep', ε', hR', hVj'⟩ := view_self hj0 (hG j hj0) hrep hR hVj hst
  obtain ⟨ys, hys, hyj⟩ := gstep_log hst
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
theorem compose {cs0 : List (CThread Prim)} {l0 : Log}
    (hG : ∀ c (hc : c < cs0.length), Guar c cs0[c] l0) (h0 : ∃ s h, replay l0 = some (s, h))
    {cs : List (CThread Prim)} {l : Log} (h : CSteps PG cs0 l0 cs l) : Linked cs0 l0 cs l := by
  suffices ∀ {a b : List (CThread Prim)} {la lb : Log}, CSteps PG a la b lb →
      Linked cs0 l0 a la → Linked cs0 l0 b lb from this h (linked_init h0)
  intro a b la lb hab
  induction hab with
  | refl => exact id
  | step h₁ _ ih => exact fun hL => ih (link_step hG hL h₁)

/-- **Transfer.** A property proved for the per-CPU layer under every
rely-respecting environment holds of every CPU of every multicore run. -/
theorem transfer {cs0 : List (CThread Prim)} {l0 : Log}
    (hG : ∀ c (hc : c < cs0.length), Guar c cs0[c] l0) (h0 : ∃ s h, replay l0 = some (s, h))
    {Q : CPU → Config Prim Log → Prop}
    (hQ : ∀ c (hc : c < cs0.length) ε, RelyP ε c → ∀ x, Star (prims ε c) (cs0[c].cfg l0) x → Q c x)
    {cs : List (CThread Prim)} {l : Log} (h : CSteps PG cs0 l0 cs l) :
    ∀ c (hc : c < cs.length), ∃ lc xs, Q c (cs[c].cfg lc) ∧ l = xs ++ lc ∧ ∀ e ∈ xs, e.cpu ≠ c := by
  obtain ⟨-, hlen, hV⟩ := compose hG h0 h
  intro c hc
  obtain ⟨ε, hR, lc, xs, hstar, hl, hx⟩ := hV c (hlen ▸ hc)
  exact ⟨lc, xs, hQ c _ ε hR _ hstar, hl, hx⟩

/-! ## The ticket-lock client on its per-CPU layer -/

theorem at_others {N : Nat} {c : CPU} {t : CThread Prim} :
    ∀ (xs : Log) {l : Log} {s s' : PState} {h h' : List HEvent} {w : Nat},
      (∀ e ∈ xs, e.cpu ≠ c) → replay l = some (s, h) → replay (xs ++ l) = some (s', h') →
      At N c s t w → ∃ w', At N c s' t w'
  | [], l, s, s', h, h', w, _, hl, hr, hA => by
    simp only [List.nil_append] at hr; rw [hl] at hr; cases hr; exact ⟨w, hA⟩
  | e :: xs, l, s, s', h, h', w, hx, hl, hr, hA => by
    obtain ⟨s2, h2, o, hl2, hp, -⟩ := replay_cons hr
    obtain ⟨w2, hA2⟩ := at_others xs (fun e' he' => hx e' (List.mem_cons_of_mem _ he')) hl hl2 hA
    obtain ⟨w', -, hA'⟩ := at_other (replay_inv hl2) hp (hx e List.mem_cons_self) hA2
    exact ⟨w', hA'⟩

theorem at_pull {N : Nat} {ε : EnvCtx} {c : CPU} (hR : RelyP ε c) {l : Log} {s : PState}
    {h : List HEvent} {t : CThread Prim} {w : Nat} (hl : replay l = some (s, h)) (hA : At N c s t w) :
    ∃ s' h' w', replay (pull ε c l) = some (s', h') ∧ At N c s' t w' := by
  obtain ⟨s', h', hr⟩ := hR.conform l s h hl
  obtain ⟨w', hA'⟩ := at_others (ε.query c l) (ε.noSelf c l) hl hr hA
  exact ⟨s', h', w', hr, hA'⟩

/-- Per-CPU invariant of the client under `ε`: its own view replays, and after
pulling the environment's events it is at a program point that matches. -/
def PInv (N : Nat) (ε : EnvCtx) (c : CPU) (x : Config Prim Log) : Prop :=
  (∃ s h, replay x.abs = some (s, h)) ∧
    ∃ s h w, replay (pull ε c x.abs) = some (s, h) ∧ At N c s (thr x) w

theorem pinv_step {N : Nat} {ε : EnvCtx} {c : CPU} (hc : c < NCPU) (hN : N < 2 ^ 32)
    (hR : RelyP ε c) {x y : Config Prim Log} (hI : PInv N ε c x)
    (hs : ClightL.step (prims ε c) x = some y) : PInv N ε c y := by
  obtain ⟨hx0, s, h, w, hg, hA⟩ := hI
  rcases step_cases (t := thr x) (a := x.abs) hs with ⟨habs, hall⟩ | ⟨-, hQ⟩
  · -- no primitive call: the log is untouched
    obtain ⟨s', hlog, w', hA', -⟩ := own_step hc hN hg hA (hall (prims noEnv c) (pull ε c x.abs))
    rcases hlog with ⟨-, hss⟩ | ⟨k, o, hk, -⟩
    · subst hss; exact ⟨habs ▸ hx0, _, h, w', by rw [habs]; exact hg, by simpa using hA'⟩
    · simp [CThread.cfg] at hk
  · -- a primitive call: it is the global-machine step at the pulled log
    have hs' : ClightL.step (prims noEnv c) ((thr x).cfg (pull ε c x.abs)) = some y :=
      hQ _ _ fun p args => prims_pull (by rw [pull_noEnv]) p args
    obtain ⟨s', hlog, w', hA', -⟩ := own_step hc hN hg hA hs'
    have hy : ∃ h', replay y.abs = some (s', h') := by
      rcases hlog with ⟨he, rfl⟩ | ⟨k, o, hk, hp⟩
      · exact ⟨h, he ▸ hg⟩
      · exact ⟨_, hk ▸ replay_cons_of hg hp⟩
    obtain ⟨h', hy⟩ := hy
    exact ⟨⟨s', h', hy⟩, at_pull hR hy hA'⟩

/-- **Per-CPU guarantee of the client**, proved on `L0[c]` alone: started idle
at any replayable log, under any rely-respecting environment, CPU `c` only
ever produces replayable logs. -/
theorem client_guar {N : Nat} {c : CPU} (hc : c < NCPU) (hN : N < 2 ^ 32) {l0 : Log}
    {s0 : PState} {h0 : List HEvent} (hl0 : replay l0 = some (s0, h0)) (hidle : s0.phase c = .idle) :
    Guar c (cThread N) l0 := by
  intro ε hR x hx
  suffices ∀ {a b}, Star (prims ε c) a b → PInv N ε c a → PInv N ε c b from
    (this hx ⟨⟨s0, h0, hl0⟩, at_pull hR hl0 (At.p0 (σ := fun _ => 0) hidle)⟩).1
  intro a b hab
  induction hab with
  | refl => exact id
  | step hs _ ih => exact fun hI => ih (pinv_step hc hN hR hI hs)

/-- The per-CPU invariant holds along every per-CPU run of the client. -/
theorem client_pinv {N : Nat} {c : CPU} (hc : c < NCPU) (hN : N < 2 ^ 32) {ε : EnvCtx}
    (hR : RelyP ε c) {x : Config Prim Log} (hx : Star (prims ε c) ((cThread N).cfg []) x) :
    PInv N ε c x := by
  suffices ∀ {a b}, Star (prims ε c) a b → PInv N ε c a → PInv N ε c b from
    this hx ⟨⟨_, _, rfl⟩, at_pull hR rfl (At.p0 (σ := fun _ => 0) rfl)⟩
  intro a b hab
  induction hab with
  | refl => exact id
  | step hs _ ih => exact fun hI => ih (pinv_step hc hN hR hI hs)

/-- The client's critical section: after `hold`, before `inc_n` completes. -/
def InCS (N : Nat) (t : CThread Prim) : Prop :=
  (t.stmt = .skip ∧ t.cont = KA N) ∨ (t.stmt = .seq releaseCode incI ∧ t.cont = KO N) ∨
    (t.stmt = releaseCode ∧ t.cont = KR N)

theorem at_cs {N : Nat} {c : CPU} {s : PState} {t : CThread Prim} {w : Nat} (hA : At N c s t w)
    (hcs : InCS N t) : ∃ tn, s.phase c = .holding tn := by
  cases hA <;> simp_all [InCS, KA, KO, KR, KT, KW, KH, KL, loopS, bodyS, clientCode, acquireCode,
    releaseCode, incI, gnC, acquireLoop, holdCall]

/-- **Per-CPU critical-section lemma**, on `L0[c]` alone: under any
rely-respecting environment, whenever the client is inside its critical
section, the protocol state of its view says it holds the lock. -/
theorem client_cs {N : Nat} {c : CPU} (hc : c < NCPU) (hN : N < 2 ^ 32) {ε : EnvCtx}
    (hR : RelyP ε c) {x : Config Prim Log} (hx : Star (prims ε c) ((cThread N).cfg []) x)
    (hcs : InCS N (thr x)) : ∃ s h tn, replay x.abs = some (s, h) ∧ s.phase c = .holding tn := by
  suffices ∀ {a b}, Star (prims ε c) a b → PInv N ε c a → PInv N ε c b by
    obtain ⟨⟨s, h, hr⟩, s', h', w', hr', hA'⟩ :=
      this hx ⟨⟨_, _, rfl⟩, at_pull hR rfl (At.p0 (σ := fun _ => 0) rfl)⟩
    obtain ⟨tn, htn⟩ := at_cs hA' hcs
    have := (replay_others (ε.query c x.abs) (ε.noSelf c x.abs) hr hr').1
    exact ⟨s, h, tn, hr, this ▸ htn⟩
  intro a b hab
  induction hab with
  | refl => exact id
  | step hs _ ih => exact fun hI => ih (pinv_step hc hN hR hI hs)

/-! ## The multicore ticket-lock client, from the per-CPU proofs -/

theorem pool_guar (T N : Nat) (hT : T ≤ NCPU) (hN : N < 2 ^ 32) :
    ∀ c (hc : c < (cPool T N).length), Guar c (cPool T N)[c] [] := by
  intro c hc
  have hcT : c < T := by simpa [cPool] using hc
  simp only [cPool, List.getElem_replicate]
  exact client_guar (Nat.lt_of_lt_of_le hcT hT) hN rfl rfl

/-- **Multicore linking for the ticket lock.** Every run of T ≤ NCPU CPUs
running the client is explained by the per-CPU layers: the global log
replays, and each CPU's view is a run of `L0[c]` under a rely-respecting `ε`
built from the run. -/
theorem ticket_linked (T N : Nat) (hT : T ≤ NCPU) (hN : N < 2 ^ 32)
    {cs : List (CThread Prim)} {l : Log} (h : CSteps PG (cPool T N) [] cs l) :
    Linked (cPool T N) [] cs l :=
  compose (pool_guar T N hT hN) ⟨_, _, rfl⟩ h

/-- **Mutual exclusion on the multicore machine, by linking.** At most one CPU
is inside its critical section, in program-counter terms. The proof uses only
the per-CPU lemma `client_cs`, transferred to every CPU, plus `mutex` on the
global log. -/
theorem multicore_cs_exclusive (T N : Nat) (hT : T ≤ NCPU) (hN : N < 2 ^ 32)
    {cs : List (CThread Prim)} {l : Log} (h : CSteps PG (cPool T N) [] cs l)
    (c d : Nat) (hc : c < cs.length) (hd : d < cs.length)
    (hcc : InCS N cs[c]) (hdc : InCS N cs[d]) : c = d := by
  have hQ := transfer (pool_guar T N hT hN) ⟨_, _, rfl⟩
    (Q := fun c x => InCS N (thr x) → ∃ s h tn, replay x.abs = some (s, h) ∧ s.phase c = .holding tn)
    (fun c hc ε hR x hx hcs => by
      have hcT : c < T := by simpa [cPool] using hc
      simp only [cPool, List.getElem_replicate] at hx
      exact client_cs (Nat.lt_of_lt_of_le hcT hT) hN hR hx hcs) h
  obtain ⟨⟨sg, hg, hl⟩, -⟩ := ticket_linked T N hT hN h
  have glob : ∀ c (hc : c < cs.length), InCS N cs[c] → ∃ tn, sg.phase c = .holding tn := by
    intro c hc hcs
    obtain ⟨lc, xs, hQc, rfl, hx⟩ := hQ c hc
    obtain ⟨s, h', tn, hr, hph⟩ := hQc hcs
    exact ⟨tn, (replay_others xs hx hr hl).1 ▸ hph⟩
  obtain ⟨t, ht⟩ := glob c hc hcc
  obtain ⟨u, hu⟩ := glob d hd hdc
  exact mutex hl ht hu

end Link
