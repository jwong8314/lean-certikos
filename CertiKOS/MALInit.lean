import CertiKOS.MALOp

/-!
# mCertiKOS `MALInit`: what `mem_init` computes, ported

`mem_init` reads the memory map that the boot loader left, works out how many
pages there are, and fills the allocation table: pages outside the user range
are the kernel's, pages inside it are normal if a usable region of the map
covers them, and reserved otherwise.

Ported from `layerlib/AuxStateDataType.v`: `MMPerm`, `MMInfo`, `MMTable`,
`MM_range`/`MM_valid`, `MM_kern_valid`, `MM_kern`.

Ported from `clib/RealParams.v`: `maxs_at_i`, `Calculate_nps`, `real_nps`,
`Calculate_AT`, `real_AT`, and the lemmas `real_nps_range`,
`real_at_kern_valid`, `real_at_usr_valid`.

Ported from `objects/ObjPMM.v`: `mem_init_spec`.

* `mem_init_inv`: **`mem_init_spec` establishes the allocation-table
  invariant** `ATInv`. Until now every theorem took it as a hypothesis.

What differs: `ikern`, `ihost` and `pg` are dropped from `mem_init_spec`, and
the fields it sets that this state does not have (`MM`, `MMSize`, `vmxinfo`)
are left out. `MM_kern_valid` is given as a search (`mmKernValidB`) and shown
equal to the existential of the sources.

The C code of `mem_init` and its refinement proof are in `MALInitC.lean`.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace MALInit

open MALOp

/-! ## The memory map (`AuxStateDataType.v`) -/

inductive MMPerm
  | MMUsable | MMResv
  deriving DecidableEq

/-- `MMValid start length perm`: one region of the boot memory map. -/
inductive MMInfo
  | MMValid (s l : Nat) (p : MMPerm)
  | MMUndef

abbrev MMTable := Nat → MMInfo

/-- `MM_valid`: the first `size` entries are regions that fit in 32 bits. -/
def MM_valid (mm : MMTable) (size : Nat) : Prop :=
  ∀ i, i < size → ∃ s l p, mm i = .MMValid s l p ∧ 0 < l ∧ s + l < 2 ^ 32 - 1

/-- `MM_kern_valid`: page `n` lies inside a usable region. -/
def MM_kern_valid (mm : MMTable) (n size : Nat) : Prop :=
  ∃ i s l, i < size ∧ mm i = .MMValid s l .MMUsable ∧ s ≤ n * 4096 ∧ (n + 1) * 4096 ≤ l + s

/-- `MM_kern`: every page below `kern_low` lies inside a usable region. -/
def MM_kern (kern_low : Nat) (mm : MMTable) (size : Nat) : Prop :=
  ∀ i, i < kern_low → MM_kern_valid mm i size

def mmUsableAt (x : MMInfo) (n : Nat) : Bool :=
  match x with
  | .MMValid s l .MMUsable => decide (s ≤ n * 4096) && decide ((n + 1) * 4096 ≤ l + s)
  | _ => false

/-- `MM_kern_valid_dec`, as a search through the map. -/
def mmKernValidB (mm : MMTable) (n : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => mmUsableAt (mm k) n || mmKernValidB mm n k

theorem mmUsableAt_iff (x : MMInfo) (n : Nat) :
    mmUsableAt x n = true ↔ ∃ s l, x = .MMValid s l .MMUsable ∧ s ≤ n * 4096 ∧ (n + 1) * 4096 ≤ l + s := by
  cases x with
  | MMUndef => simp [mmUsableAt]
  | MMValid s l p =>
    cases p with
    | MMResv => simp [mmUsableAt]
    | MMUsable =>
      simp [mmUsableAt]
      constructor
      · rintro ⟨a, b⟩; exact ⟨s, l, ⟨rfl, rfl⟩, a, b⟩
      · rintro ⟨s', l', ⟨rfl, rfl⟩, a, b⟩; exact ⟨a, b⟩

theorem mmKernValidB_iff (mm : MMTable) (n : Nat) : ∀ size, mmKernValidB mm n size = true ↔ MM_kern_valid mm n size
  | 0 => by simp [mmKernValidB, MM_kern_valid]
  | k + 1 => by
    simp only [mmKernValidB, Bool.or_eq_true, mmKernValidB_iff mm n k, mmUsableAt_iff]
    constructor
    · rintro (⟨s, l, h1, h2, h3⟩ | ⟨i, s, l, hi, h1, h2, h3⟩)
      · exact ⟨k, s, l, Nat.lt_succ_self _, h1, h2, h3⟩
      · exact ⟨i, s, l, by omega, h1, h2, h3⟩
    · rintro ⟨i, s, l, hi, h1, h2, h3⟩
      by_cases e : i = k
      · subst e; exact Or.inl ⟨s, l, h1, h2, h3⟩
      · exact Or.inr ⟨i, s, l, by omega, h1, h2, h3⟩

/-! ## The calculated page count and table (`RealParams.v`) -/

/-- The page just past region `i`. -/
def maxs_at_i (i : Nat) (mm : MMTable) : Nat :=
  match mm i with
  | .MMValid s l _ => (s + l) / 4096 + 1
  | .MMUndef => 0

/-- The largest `maxs_at_i` over regions `0..i`. -/
def Calculate_nps : Nat → MMTable → Nat
  | 0, mm => maxs_at_i 0 mm
  | k + 1, mm => if Calculate_nps k mm < maxs_at_i (k + 1) mm then maxs_at_i (k + 1) mm else Calculate_nps k mm

/-- `real_nps`: the number of pages. -/
def real_nps (mm : MMTable) (size : Nat) : Nat := Calculate_nps (size - 1) mm

/-- The entry `mem_init` gives page `i`. -/
def atEntry (kl kh nps : Nat) (mm : MMTable) (size i : Nat) : ATInfo :=
  if kl ≤ i then
    if i < min kh nps then
      if mmKernValidB mm i size then .ATValid false .ATNorm 0 else .ATValid false .ATResv 0
    else .ATValid false .ATKern 0
  else .ATValid false .ATKern 0

/-- `Calculate_AT`: fill entries `0..n`. -/
def Calculate_AT (kl kh nps : Nat) (mm : MMTable) (size : Nat) : Nat → ATable → ATable
  | 0, At => setAt At 0 (.ATValid false .ATKern 0)
  | k + 1, At => setAt (Calculate_AT kl kh nps mm size k At) (k + 1) (atEntry kl kh nps mm size (k + 1))

/-- `real_AT`. -/
def real_AT (kl kh : Nat) (mm : MMTable) (size : Nat) (At : ATable) : ATable :=
  Calculate_AT kl kh (real_nps mm size) mm size (real_nps mm size - 1) At

theorem calnps_ge (mm : MMTable) : ∀ n i, i ≤ n → maxs_at_i i mm ≤ Calculate_nps n mm
  | 0, i, h => by have : i = 0 := by omega
                  subst this; exact Nat.le_refl _
  | n + 1, i, h => by
    simp only [Calculate_nps]
    by_cases e : i = n + 1
    · subst e; split <;> omega
    · have := calnps_ge mm n i (by omega); split <;> omega

theorem calnps_le (mm : MMTable) (B : Nat) : ∀ n, (∀ i, i ≤ n → maxs_at_i i mm ≤ B) → Calculate_nps n mm ≤ B
  | 0, h => h 0 (Nat.le_refl _)
  | n + 1, h => by
    simp only [Calculate_nps]
    have h1 := calnps_le mm B n (fun i hi => h i (by omega))
    have h2 := h (n + 1) (Nat.le_refl _)
    split <;> omega

/-- **`real_nps_range`**: `kern_low ≤ real_nps ≤ maxpage`. -/
theorem real_nps_range {kl : Nat} {mm : MMTable} {size : Nat} (hkl : 0 < kl) (hsz : 0 < size)
    (hv : MM_valid mm size) (hk : MM_kern kl mm size) :
    kl ≤ real_nps mm size ∧ real_nps mm size ≤ 2 ^ 20 := by
  unfold real_nps
  constructor
  · obtain ⟨i, s, l, hi, hm, h1, h2⟩ := hk (kl - 1) (by omega)
    have hge := calnps_ge mm (size - 1) i (by omega)
    have : kl ≤ maxs_at_i i mm := by
      unfold maxs_at_i; rw [hm]
      show kl ≤ (s + l) / 4096 + 1
      have hmul : kl * 4096 ≤ s + l := by
        have e : kl - 1 + 1 = kl := by omega
        rw [e] at h2; omega
      omega
    omega
  · refine calnps_le mm _ _ (fun i hi => ?_)
    obtain ⟨s, l, p, hm, -, hb⟩ := hv i (by omega)
    unfold maxs_at_i; rw [hm]
    show (s + l) / 4096 + 1 ≤ 2 ^ 20
    omega

theorem calAT_get (kl kh nps : Nat) (mm : MMTable) (size : Nat) (At : ATable) (hkl : 0 < kl) :
    ∀ n i, i ≤ n → Calculate_AT kl kh nps mm size n At i = atEntry kl kh nps mm size i
  | 0, i, h => by
    have : i = 0 := by omega
    subst this
    simp only [Calculate_AT, setAt_eq, atEntry]
    rw [if_neg (by omega)]
  | n + 1, i, h => by
    simp only [Calculate_AT]
    by_cases e : i = n + 1
    · subst e; rw [setAt_eq]
    · rw [setAt_ne _ _ e]; exact calAT_get kl kh nps mm size At hkl n i (by omega)

/-- **`real_at_kern_valid`.** -/
theorem real_at_kern_valid {kl kh : Nat} {mm : MMTable} {size : Nat} (At : ATable) (hkl : 0 < kl)
    (hn : 0 < real_nps mm size) (hkn : kl ≤ real_nps mm size) :
    AT_kern kl kh (real_AT kl kh mm size At) (real_nps mm size) := by
  intro i hi
  have hlt : i < real_nps mm size := by omega
  unfold real_AT
  rw [calAT_get kl kh _ mm size At hkl _ i (by omega)]
  unfold atEntry
  rcases hi with h | ⟨h1, h2⟩
  · rw [if_neg (by omega)]
  · by_cases hc : kl ≤ i
    · rw [if_pos hc, if_neg (by simp only [Nat.lt_min]; omega)]
    · rw [if_neg hc]

/-- **`real_at_usr_valid`.** -/
theorem real_at_usr_valid {kl kh : Nat} {mm : MMTable} {size : Nat} (At : ATable) (hkl : 0 < kl) :
    AT_usr kl kh (real_AT kl kh mm size At) (real_nps mm size) := by
  intro i h1 h2
  have hlt : i < real_nps mm size := by simp only [Nat.lt_min] at h2; omega
  unfold real_AT
  rw [calAT_get kl kh _ mm size At hkl _ i (by omega)]
  unfold atEntry
  rw [if_pos h1, if_pos h2]
  refine ⟨false, ?_⟩
  by_cases hv : mmKernValidB mm i size = true
  · rw [if_pos hv]; exact Or.inl ⟨0, rfl⟩
  · rw [if_neg hv]; exact Or.inr rfl

/-- Below `real_nps` every entry of `real_AT` is unallocated. -/
theorem real_AT_unalloc {kl kh : Nat} {mm : MMTable} {size : Nat} (At : ATable) (hkl : 0 < kl) {i : Nat}
    (hi : i < real_nps mm size) : ∃ t n, real_AT kl kh mm size At i = .ATValid false t n := by
  unfold real_AT
  rw [calAT_get kl kh _ mm size At hkl _ i (by omega)]
  unfold atEntry
  split
  · split
    · split <;> exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-! ## `mem_init_spec` (`ObjPMM.v`) -/

/-- **`mem_init_spec`**: set the page count and the allocation table from the
memory map. -/
def mem_init_spec (kl kh : Nat) (mm : MMTable) (size : Nat) (d : PData) : Option PData :=
  if d.init = false then
    some { d with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, init := true }
  else none

/-- **`mem_init_spec` establishes the allocation-table invariant.** The
memory map is valid and covers the pages below `kern_low`
(`real_valid_mm`, `real_valid_mm_kern`), and no page has a permission yet
(`init_pperm`). -/
theorem mem_init_inv {maxpage kl kh : Nat} {mm : MMTable} {size : Nat} {d d' : PData} (hkl : 0 < kl)
    (hsz : 0 < size) (hmax : 2 ^ 20 ≤ maxpage) (hv : MM_valid mm size) (hk : MM_kern kl mm size)
    (hpp : d.pperm = fun _ => .PGUndef) (hs : mem_init_spec kl kh mm size d = some d') :
    ATInv maxpage kl kh d' := by
  unfold mem_init_spec at hs
  by_cases hin : d.init = false
  · rw [if_pos hin] at hs
    simp only [Option.some.injEq] at hs; subst hs
    obtain ⟨h1, h2⟩ := real_nps_range hkl hsz hv hk
    refine ⟨⟨h1, by show real_nps mm size ≤ maxpage; omega⟩,
      real_at_kern_valid d.AT hkl (by omega) h1, real_at_usr_valid d.AT hkl, fun i hi => ⟨fun hne => ?_, fun n hn => ?_⟩⟩
    · exact absurd (by show d.pperm i = .PGUndef; rw [hpp]) hne
    · obtain ⟨t, m, hm⟩ := real_AT_unalloc (kh := kh) d.AT hkl hi
      rw [show ({ d with AT := real_AT kl kh mm size d.AT, nps := real_nps mm size, init := true } : PData).AT i
        = real_AT kl kh mm size d.AT i from rfl, hm] at hn
      cases hn
  · rw [if_neg hin] at hs; cases hs

end MALInit
