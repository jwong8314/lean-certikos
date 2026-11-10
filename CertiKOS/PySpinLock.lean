import CertiKOS.PyCSL

/-!
# Example: a PyL spin lock that transfers ownership of protected memory

Any number of threads run this Python code:

```python
got = 0
while got == 0:          # acquire: test-and-set under the global lock L
    with L:
        t = lk.held
        if t == 0:
            lk.held = 1
            got = 1
x = d.val                # critical section, OUTSIDE `with L:`
d.val = x + 1
with L:                  # release
    lk.held = 0
```

`lk` is object `0` and `d` is object `1`. The critical section touches
`d.val` without holding `L`. It is still race-free because ownership of
`d.val` travels with the spin lock:

* the lock invariant `J` owns `d.val` while `lk.held == 0`;
* a successful test-and-set takes `d.val` out of `J` into the thread;
* release puts it back.

This is CertiKOS's `pull`/`push` discipline for lock-protected memory
([OSDI16] Fig. 7: `acq_lock` ends with `pull(i)`, `rel_lock` starts with
`push(i)`), stated in separation logic instead of as copies.

The key separation step is in `release_ok`. Inside `with L:` the thread
owns `d.val`, so `J` cannot also own it. Hence `J` must be in its "taken"
state, and the thread may put `d.val` back.

`spinlock_safe` applies `pool_sound`: for any number of threads and any
execution, nothing faults and no two threads ever touch the same attribute
at the same time. In particular, the unlocked `d.val` updates never race.
-/

namespace PyL.SpinLock
open PyL Heap

def lk : Expr := .const 0
def dd : Expr := .const 1
def lHeld : Loc := ⟨0, "held"⟩
def dVal : Loc := ⟨1, "val"⟩

theorem lHeld_ne_dVal : lHeld ≠ dVal := by simp [lHeld, dVal]

def eq0 (x : Var) : Expr := .bin .eq (.var x) (.const 0)

def tryAcquire : Cmd :=
  .seq (.load "t" lk "held")
    (.ite (eq0 "t") (.seq (.store lk "held" (.const 1)) (.assign "got" (.const 1))) .skip)
def acquire : Cmd := .seq (.assign "got" (.const 0)) (.while (eq0 "got") (.atomic tryAcquire))
def critical : Cmd :=
  .seq (.load "x" dd "val") (.store dd "val" (.bin .add (.var "x") (.const 1)))
def release : Cmd := .atomic (.store lk "held" (.const 0))
def client : Cmd := .seq acquire (.seq critical release)

/-- Lock invariant: the spin lock is taken, or it is free and owns `d.val`. -/
def J : Inv := fun h => h = single lHeld 1 ∨ ∃ d, h = single lHeld 0 ⊎ single dVal d

def OwnD : Assn := fun _ h => ∃ d, h = single dVal d
def AcqInv : Assn := fun s h => (s "got" = 0 ∧ h = Heap.emp) ∨ (s "got" ≠ 0 ∧ OwnD s h)

theorem disj_single {l l' : Loc} (v w : Int) (h : l ≠ l') : Disj (single l v) (single l' w) := by
  intro x
  by_cases e : x = l
  · subst e; exact .inr (single_other _ h)
  · exact .inl (single_other _ e)

theorem upd_single (l : Loc) (v w : Int) : (single l v).upd l w = single l w := by
  funext x; by_cases e : x = l <;> simp [upd, single, e]

theorem J_held {h : Heap} (hj : J h) : ∃ v, h lHeld = some v := by
  rcases hj with rfl | ⟨d, rfl⟩
  · exact ⟨1, single_same _ _⟩
  · exact ⟨0, union_some_left (single_same _ _)⟩

theorem eval_eq0 (s : Store) (x : Var) : (eq0 x).eval s = if s x = 0 then 1 else 0 := rfl

/-- The body of `with L:` in acquire, verified with the invariant in hand. -/
theorem tryAcquire_ok :
    Valid empInv (fun s h => s "got" = 0 ∧ J h) tryAcquire (AcqInv ⋆ J.lift) := by
  refine rule_seq (R := fun s h => s "got" = 0 ∧ J h ∧ h lHeld = some (s "t")) rfl ?_ ?_
  · refine rule_conseq rule_load ?_ (fun _ _ x => x)
    rintro s h ⟨hg, hj⟩
    obtain ⟨v, hv⟩ := J_held hj
    exact ⟨v, hv, by simpa using hg, hj, by simpa using hv⟩
  · refine rule_ite rfl rfl ?_ ?_
    · refine rule_seq (R := fun _ h => ∃ d, h = single lHeld 1 ⊎ single dVal d) rfl ?_ ?_
      · refine rule_conseq rule_store ?_ (fun _ _ x => x)
        rintro s h ⟨⟨_, hj, hv⟩, ht⟩
        have ht0 : s "t" = 0 := by
          rw [eval_eq0] at ht; split at ht <;> first | assumption | exact absurd rfl ht
        rcases hj with rfl | ⟨d, rfl⟩
        · simp [ht0] at hv
        · show (single lHeld 0 ⊎ single dVal d) lHeld ≠ none ∧
            ∃ d', (single lHeld 0 ⊎ single dVal d).upd lHeld 1 = single lHeld 1 ⊎ single dVal d'
          refine ⟨union_ne_none_left (by simp), d, ?_⟩
          rw [upd_union_left _ (by simp), upd_single]
      · refine rule_conseq rule_assign ?_ (fun _ _ x => x)
        rintro s _ ⟨d, rfl⟩
        exact ⟨single dVal d, single lHeld 1, (disj_single _ _ lHeld_ne_dVal).symm,
          union_comm (disj_single _ _ lHeld_ne_dVal), .inr ⟨by simp [Expr.eval], d, rfl⟩, .inl rfl⟩
    · refine rule_conseq rule_skip ?_ (fun _ _ x => x)
      rintro s h ⟨⟨hg, hj, _⟩, _⟩
      exact ⟨Heap.emp, h, by simp, by simp, .inl ⟨hg, rfl⟩, hj⟩

/-- `{emp} acquire {d.val ↦ _}`: acquiring hands the thread ownership of `d.val`. -/
theorem acquire_ok : Valid J Assn.emp acquire OwnD := by
  refine rule_seq (R := AcqInv) rfl ?_ ?_
  · refine rule_conseq rule_assign ?_ (fun _ _ x => x)
    intro s h hh; exact .inl ⟨by simp [Expr.eval], hh⟩
  · refine rule_conseq (rule_while rfl ?_) (fun _ _ x => x) ?_
    · refine rule_atomic (rule_conseq tryAcquire_ok ?_ (fun _ _ x => x))
      rintro s _ ⟨h1, h2, _, rfl, ⟨hi, hne⟩, hj⟩
      have hg : s "got" = 0 := by
        rw [eval_eq0] at hne; split at hne <;> first | assumption | exact absurd rfl hne
      rcases hi with ⟨_, rfl⟩ | ⟨hg', _⟩
      · exact ⟨hg, by rw [emp_union]; exact hj⟩
      · exact absurd hg hg'
    · rintro s h ⟨hi, he⟩
      have hg : s "got" ≠ 0 := by
        rw [eval_eq0] at he; split at he <;> first | assumption | exact absurd he (by decide)
      rcases hi with ⟨hg', _⟩ | ⟨_, ho⟩
      · exact absurd hg' hg
      · exact ho

/-- `{d.val ↦ _} x = d.val; d.val = x + 1 {d.val ↦ _}`, outside the lock. -/
theorem critical_ok : Valid J OwnD critical OwnD := by
  refine rule_seq (R := OwnD) rfl ?_ ?_
  · refine rule_conseq rule_load ?_ (fun _ _ x => x)
    rintro s _ ⟨d, rfl⟩
    exact ⟨d, single_same _ _, d, rfl⟩
  · refine rule_conseq rule_store ?_ (fun _ _ x => x)
    rintro s _ ⟨d, rfl⟩
    exact ⟨by simp [dd, dVal, Expr.eval], _, upd_single dVal d _⟩

/-- `{d.val ↦ _} with L: lk.held = 0 {emp}`: release gives `d.val` back. -/
theorem release_ok : Valid J OwnD release Assn.emp := by
  refine rule_atomic (rule_conseq rule_store ?_ (fun _ _ x => x))
  rintro s _ ⟨_, h2, dj, rfl, ⟨d, rfl⟩, hj⟩
  rcases hj with rfl | ⟨d', rfl⟩
  · show (single dVal d ⊎ single lHeld 1) lHeld ≠ none ∧
      ∃ h₁ h₂, Disj h₁ h₂ ∧ (single dVal d ⊎ single lHeld 1).upd lHeld 0 = h₁ ⊎ h₂ ∧
        h₁ = Heap.emp ∧ J h₂
    rw [union_comm dj]
    refine ⟨union_ne_none_left (by simp), Heap.emp, single lHeld 0 ⊎ single dVal d, by simp,
      ?_, rfl, .inr ⟨d, rfl⟩⟩
    rw [upd_union_left _ (by simp), upd_single, emp_union]
  · -- `J` cannot own `d.val` too: the thread already owns it.
    exfalso
    have := dj dVal
    simp [single, union_apply, lHeld, dVal] at this

theorem client_ok : Valid J Assn.emp client Assn.emp :=
  rule_seq rfl acquire_ok (rule_seq rfl critical_ok release_ok)

/-- Initial heap: lock free, `d.val = 0`, both owned by the invariant. -/
def H0 : Heap := single lHeld 0 ⊎ single dVal 0

def pool (N : Nat) (s0 : Store) : Pool := List.replicate N ⟨client, s0⟩

/-- **Any number of threads running `client`, under any interleaving:** no
fault, no two threads touching the same attribute at once (so the unlocked
`d.val` updates never race), and at the end all memory is back in the lock
invariant. -/
theorem spinlock_safe (N : Nat) (s0 : Store) :
    ∀ k ts' H', MSteps k (pool N s0) H0 ts' H' →
      ¬ Faults ts' H' ∧ ¬ Race ts' ∧
      ((∀ i (hi : i < ts'.length), ts'[i].cmd = .skip) →
        ∃ own' : Loc → Option Nat, J (restrict own' H' none) ∧
          ∀ i, i < ts'.length → restrict own' H' (some i) = Heap.emp) := by
  have hJ0 : restrict (fun _ => none) H0 none = H0 := funext fun l => by simp [restrict]
  exact pool_sound (J := J) (P := fun _ => Assn.emp) (Q := fun _ => Assn.emp)
    (fun _ => none)
    (fun i _ => by simp only [pool, List.getElem_replicate]; exact client_ok)
    (fun i _ => by simp only [pool, List.getElem_replicate]; rfl)
    (by rw [hJ0]; exact .inr ⟨0, rfl⟩)
    (fun i _ => funext fun l => by simp [restrict])

/-! ## Sanity checks: the conclusions are not vacuous -/

/-- Without the spin lock, two threads running the critical section race
immediately: `Race` is reachable for unverified code. -/
example (s : Store) : Race [⟨critical, s⟩, ⟨critical, s⟩] :=
  ⟨0, 1, by simp, by simp, by decide, dVal, rfl, rfl⟩

/-- The verified pool really runs: thread 0 can take its first step. -/
example (s0 : Store) : ∃ ts' H', MStep (pool 2 s0) H0 ts' H' :=
  ⟨_, _, MStep.step 0 (by simp [pool]) (Step.seq (Step.seq Step.assign))
    (fun _ h => by simp [Cmd.locked] at h)⟩

end PyL.SpinLock
