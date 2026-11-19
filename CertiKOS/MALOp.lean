import CertiKOS.KernFrame

/-!
# mCertiKOS `MALInit` / `MALOp`: the allocation table, ported

This file follows the mCertiKOS sources (public mirror `npe9/certikos`), not a
design of our own. `KernPAlloc.lean` was a simplified allocator; this one
has mCertiKOS's state, specifications and C code.

Ported from `mcertikos/layerlib/AuxStateDataType.v`:
`ATType`, `ATInfo`, `ATable`, `PPgInfo`, `ZtoATType`, `ZtoBool`, `first_free`,
`AT_kern`, `AT_usr`, `consistent_ppage`.

Ported from `mcertikos/objects/ObjPMM.v`: `is_at_norm_spec`, `get_at_u_spec`,
`get_at_c_spec`, `get_nps_spec`, `set_at_u_spec`, `set_at_norm_spec`,
`set_at_c_spec`, `palloc'_spec`, `pfree'_spec`.

Ported from `mcertikos/mm/MBootCSource.v` and `MALOpCSource.v`: the C code of
`is_norm`, `at_get`, `at_set`, `at_set_c`, `get_nps`, `palloc`, `pfree`.

Ported from `mcertikos/mm/ALInitGenDef.v`: the relation `match_AT` between the
abstract table and memory (`MatchD`). An entry is three words: type,
allocated, count.

What differs from the sources, and why:

* `ikern`/`ihost` (kernel mode, host mode) are dropped from the
  specifications. There is no machine model here.
* Indices and counts are `Nat`, not `Z`. The specifications only accept
  nonnegative ones.
* The table lives in a lock's region (cells `3 * i`, `3 * i + 1`,
  `3 * i + 2`, and the page count at cell `3 * maxpage`), not in CompCert
  memory. The sequential mCertiKOS has no lock. The lock is the mC2 part.
* `palloc`'s loop test `a && b` is written `a * b`. ClightL has no `&&`, and
  both operands are 0 or 1.

The proof has two steps, as in mCertiKOS. The C code computes a function on
the region (`pallocC`, `pfreeC`), for any region. That function refines the
abstract specification whenever the region matches abstract data
(`palloc_ref`, `pfree_ref`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace MALOp

open ClightL Ticket
open LockArray (APrim AEnv ALog acquireA loopA lkE apull upd upd_same upd_other)
open LockRegion (REvent RLog RState HLogR HEventR rreplay rstep REnv rpull rev Region setCell hmemR Holding)
open LockRegionCPU KernFrame
open KernPAlloc (ofNat_ne)

/-! ## Abstract data (`AuxStateDataType.v`) -/

inductive ATType
  | ATKern | ATResv | ATNorm
  deriving DecidableEq

/-- `ATValid allocated type count`. -/
inductive ATInfo
  | ATValid (b : Bool) (t : ATType) (n : Nat)
  | ATUndef
  deriving DecidableEq

abbrev ATable := Nat → ATInfo

/-- Physical page permission. `PGHide n i` is `PGHide (PGPMap n i)`. -/
inductive PPgInfo
  | PGUndef | PGAlloc | PGHide (n i : Nat)
  deriving DecidableEq

/-- The part of `RData` these layers use. -/
structure PData where
  AT : ATable
  nps : Nat
  pperm : Nat → PPgInfo
  init : Bool

/-- `ZMap.set`. -/
def setAt {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α := fun k => if k = i then v else f k

theorem setAt_eq {α : Type} (f : Nat → α) (i : Nat) (v : α) : setAt f i v i = v := by simp [setAt]

theorem setAt_ne {α : Type} (f : Nat → α) {i k : Nat} (v : α) (h : k ≠ i) : setAt f i v k = f k := by
  simp [setAt, h]

def ZtoATType : Nat → Option ATType
  | 0 => some .ATResv
  | 1 => some .ATKern
  | 2 => some .ATNorm
  | _ => none

def ZtoBool : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

/-- An unallocated page of normal type. -/
def isFree : ATInfo → Bool
  | .ATValid false .ATNorm _ => true
  | _ => false

def ffFrom (AT : ATable) : Nat → Nat → Option Nat
  | _, 0 => none
  | m, k + 1 => if isFree (AT m) then some m else ffFrom AT (m + 1) k

/-- `first_free`: the least `n` with `0 < n < size` that is free. -/
def first_free (AT : ATable) (size : Nat) : Option Nat := ffFrom AT 1 (size - 1)

theorem isFree_iff (x : ATInfo) : isFree x = true ↔ ∃ c, x = .ATValid false .ATNorm c := by
  cases x with
  | ATUndef => simp [isFree]
  | ATValid b t n => cases b <;> cases t <;> simp [isFree]

theorem ffFrom_some {AT : ATable} : ∀ {k m n : Nat}, ffFrom AT m k = some n →
    m ≤ n ∧ n < m + k ∧ isFree (AT n) = true ∧ ∀ x, m ≤ x → x < n → isFree (AT x) = false
  | 0, _, _, h => by simp [ffFrom] at h
  | k + 1, m, n, h => by
    simp only [ffFrom] at h
    split at h
    · rename_i hf
      simp only [Option.some.injEq] at h; subst h
      exact ⟨Nat.le_refl _, by omega, hf, fun x h1 h2 => by omega⟩
    · rename_i hf
      obtain ⟨h1, h2, h3, h4⟩ := ffFrom_some h
      refine ⟨by omega, by omega, h3, fun x hx1 hx2 => ?_⟩
      by_cases hxm : x = m
      · subst hxm; simpa using hf
      · exact h4 x (by omega) hx2

theorem ffFrom_none {AT : ATable} : ∀ {k m : Nat}, ffFrom AT m k = none →
    ∀ x, m ≤ x → x < m + k → isFree (AT x) = false
  | 0, _, _, x, h1, h2 => by omega
  | k + 1, m, h, x, h1, h2 => by
    simp only [ffFrom] at h
    split at h
    · simp at h
    · rename_i hf
      by_cases hxm : x = m
      · subst hxm; simpa using hf
      · exact ffFrom_none h x (by omega) (by omega)

/-- The specification of `first_free`, as its Coq type states it. -/
theorem first_free_some {AT : ATable} {size n : Nat} (h : first_free AT size = some n) :
    0 < n ∧ n < size ∧ (∃ c, AT n = .ATValid false .ATNorm c) ∧
      ∀ x, 0 < x → x < n → ¬ ∃ c, AT x = .ATValid false .ATNorm c := by
  obtain ⟨h1, h2, h3, h4⟩ := ffFrom_some h
  refine ⟨by omega, by omega, (isFree_iff _).1 h3, fun x hx1 hx2 hc => ?_⟩
  have := h4 x (by omega) hx2
  rw [(isFree_iff _).2 hc] at this; cases this

theorem first_free_none {AT : ATable} {size : Nat} (h : first_free AT size = none) :
    ∀ x, 0 < x → x < size → ¬ ∃ c, AT x = .ATValid false .ATNorm c := by
  intro x hx1 hx2 hc
  have := ffFrom_none h x (by omega) (by omega)
  rw [(isFree_iff _).2 hc] at this; cases this

/-! ## Specifications (`ObjPMM.v`) -/

section Specs
variable (maxpage : Nat)

/-- Whether page `i` has type "normal". -/
def is_at_norm_spec (i : Nat) (d : PData) : Option Nat :=
  if i < maxpage then
    match d.AT i with
    | .ATValid _ st _ => if st = .ATNorm then some 1 else some 0
    | .ATUndef => none
  else none

/-- Whether page `i` is allocated. -/
def get_at_u_spec (i : Nat) (d : PData) : Option Nat :=
  if i < maxpage then
    match d.AT i with
    | .ATValid true _ _ => some 1
    | .ATValid _ _ _ => some 0
    | .ATUndef => none
  else none

def get_at_c_spec (i : Nat) (d : PData) : Option Nat :=
  if i < maxpage then
    match d.AT i with
    | .ATValid _ _ n => some n
    | .ATUndef => none
  else none

def get_nps_spec (d : PData) : Option Nat := some d.nps

/-- Set the allocated bit of page `i`. -/
def set_at_u_spec (i b : Nat) (d : PData) : Option PData :=
  if i < maxpage then
    match ZtoBool b with
    | some b' =>
      match d.AT i with
      | .ATValid _ .ATNorm n => some { d with AT := setAt d.AT i (.ATValid b' .ATNorm n) }
      | _ => none
    | none => none
  else none

/-- Set the type of page `i`. -/
def set_at_norm_spec (i n : Nat) (d : PData) : Option PData :=
  if i < maxpage then
    match ZtoATType n with
    | some t => some { d with AT := setAt d.AT i (.ATValid false t 0) }
    | none => none
  else none

def set_at_c_spec (i n : Nat) (d : PData) : Option PData :=
  if i < maxpage then
    match d.AT i with
    | .ATValid b .ATNorm _ => some { d with AT := setAt d.AT i (.ATValid b .ATNorm n) }
    | _ => none
  else none

/-- **`palloc'_spec`**: allocate a page and return its index, or 0. -/
def palloc'_spec (d : PData) : Option (PData × Nat) :=
  if d.init then
    match first_free d.AT d.nps with
    | some i =>
      some ({ d with AT := setAt d.AT i (.ATValid true .ATNorm 0), pperm := setAt d.pperm i .PGAlloc }, i)
    | none => some (d, 0)
  else none

/-- **`pfree'_spec`**: free page `i`. Defined only if the page is allocated,
normal, unmapped (count 0), and its permission is `PGAlloc`. -/
def pfree'_spec (i : Nat) (d : PData) : Option PData :=
  if d.init then
    if i < maxpage then
      match d.AT i, d.pperm i with
      | .ATValid true .ATNorm 0, .PGAlloc =>
        some { d with AT := setAt d.AT i (.ATValid false .ATNorm 0), pperm := setAt d.pperm i .PGUndef }
      | _, _ => none
    else none
  else none

end Specs

/-! ## Invariants (`AuxStateDataType.v`, `MALOp.v`, `MContainer.v`) -/

/-- Pages outside `[kern_low, kern_high)` are the kernel's. -/
def AT_kern (kern_low kern_high : Nat) (AT : ATable) (nps : Nat) : Prop :=
  ∀ i, (i < kern_low ∨ (kern_high ≤ i ∧ i < nps)) → AT i = .ATValid false .ATKern 0

/-- Pages inside are normal or reserved. -/
def AT_usr (kern_low kern_high : Nat) (AT : ATable) (nps : Nat) : Prop :=
  ∀ i, kern_low ≤ i → i < min kern_high nps →
    ∃ b, (∃ n, AT i = .ATValid b .ATNorm n) ∨ AT i = .ATValid b .ATResv 0

/-- A page has a permission exactly when it is an allocated normal page. -/
def consistent_ppage (AT : ATable) (ppt : Nat → PPgInfo) (nps : Nat) : Prop :=
  ∀ i, i < nps →
    (ppt i ≠ .PGUndef → ∃ n, AT i = .ATValid true .ATNorm n) ∧
    (∀ n, AT i = .ATValid true .ATNorm n → ppt i ≠ .PGUndef)

/-- The part of `high_level_invariant` about the allocation table. -/
structure ATInv (maxpage kern_low kern_high : Nat) (d : PData) : Prop where
  valid_nps : kern_low ≤ d.nps ∧ d.nps ≤ maxpage
  valid_AT_kern : AT_kern kern_low kern_high d.AT d.nps
  valid_AT_usr : AT_usr kern_low kern_high d.AT d.nps
  valid_pperm : consistent_ppage d.AT d.pperm d.nps

/-- Under the invariant every entry below `nps` is defined. -/
theorem ATInv.valid {maxpage kl kh : Nat} {d : PData} (h : ATInv maxpage kl kh d) {i : Nat} (hi : i < d.nps) :
    ∃ b t n, d.AT i = .ATValid b t n := by
  by_cases h1 : i < kl
  · exact ⟨_, _, _, h.valid_AT_kern i (Or.inl h1)⟩
  · by_cases h2 : kh ≤ i
    · exact ⟨_, _, _, h.valid_AT_kern i (Or.inr ⟨h2, hi⟩)⟩
    · obtain ⟨b, ⟨n, hn⟩ | hr⟩ := h.valid_AT_usr i (by omega) (by simp only [Nat.lt_min]; omega)
      · exact ⟨_, _, _, hn⟩
      · exact ⟨_, _, _, hr⟩

/-! ## The table in a region (`ALInitGenDef.v`) -/

/-- Cell `k` of entry `i`: 0 type, 1 allocated, 2 count. -/
def ix (i k : Val) : Nat := (i * 3 + k).toNat

/-- `match_AT_info`. -/
def MatchInfo : ATInfo → Val → Val → Val → Prop
  | .ATUndef, _, _, _ => True
  | .ATValid b t n, v, u, z => ZtoATType z.toNat = some t ∧ ZtoBool u.toNat = some b ∧ n = v.toNat

/-- `match_AT` and the page count. -/
structure MatchD (maxpage : Nat) (d : PData) (b : Region) : Prop where
  mat : ∀ i, i < maxpage → MatchInfo (d.AT i) (b (3 * i + 2)) (b (3 * i + 1)) (b (3 * i))
  mnps : d.nps = (b (3 * maxpage)).toNat

section Ix
variable {maxpage : Nat} (hmax : 3 * maxpage < 2 ^ 32)
include hmax

theorem ix0 {i : Nat} (hi : i < maxpage) : ix (BitVec.ofNat 32 i) 0 = 3 * i := by
  simp [ix, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem ix1 {i : Nat} (hi : i < maxpage) : ix (BitVec.ofNat 32 i) 1 = 3 * i + 1 := by
  simp [ix, BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem ix2 {i : Nat} (hi : i < maxpage) : ix (BitVec.ofNat 32 i) 2 = 3 * i + 2 := by
  simp [ix, BitVec.toNat_add, BitVec.toNat_mul]; omega

end Ix

theorem ztype_cases {n : Nat} {t : ATType} (h : ZtoATType n = some t) :
    (n = 0 ∧ t = .ATResv) ∨ (n = 1 ∧ t = .ATKern) ∨ (n = 2 ∧ t = .ATNorm) := by
  match n, h with
  | 0, h => simp [ZtoATType] at h; exact Or.inl ⟨rfl, h.symm⟩
  | 1, h => simp [ZtoATType] at h; exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
  | 2, h => simp [ZtoATType] at h; exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
  | n + 3, h => simp [ZtoATType] at h

theorem zbool_cases {n : Nat} {b : Bool} (h : ZtoBool n = some b) :
    (n = 0 ∧ b = false) ∨ (n = 1 ∧ b = true) := by
  match n, h with
  | 0, h => simp [ZtoBool] at h; exact Or.inl ⟨rfl, h⟩
  | 1, h => simp [ZtoBool] at h; exact Or.inr ⟨rfl, h⟩
  | n + 2, h => simp [ZtoBool] at h

theorem val_of_toNat {z : Val} {n : Nat} (h : z.toNat = n) (hn : n < 2 ^ 32) : z = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt hn]; exact h

/-! ## What the C code computes on the region -/

/-- `is_norm`: `t = AT[i].isnorm; if (t != 0) { if (t == 1) t = 0; else t = 1; }` -/
def isNormC (b : Region) (i : Val) : Val :=
  if b (ix i 0) = 0 then 0 else if b (ix i 0) = 1 then 0 else 1

/-- `at_get`: `a = AT[i].allocated; if (a != 0) a = 1;` -/
def atGetC (b : Region) (i : Val) : Val := if b (ix i 1) = 0 then 0 else 1

def freeC (b : Region) (m : Nat) : Bool :=
  decide (isNormC b (BitVec.ofNat 32 m) = 1) && decide (atGetC b (BitVec.ofNat 32 m) = 0)

/-- `palloc`'s loop from page `m`, `k` pages to go: the free page found, or `nps`. -/
def scanC (b : Region) (nps : Nat) : Nat → Nat → Nat
  | _, 0 => nps
  | m, k + 1 => if freeC b m then m else scanC b nps (m + 1) k

/-- What `palloc` does to the region, and what it returns. -/
def pallocC (maxpage : Nat) (b : Region) : Region × Val :=
  let nps := (b (3 * maxpage)).toNat
  let f := scanC b nps 1 (nps - 1)
  if f = nps then (b, 0)
  else (setCell (setCell b (ix (BitVec.ofNat 32 f) 1) 1) (ix (BitVec.ofNat 32 f) 2) 0, BitVec.ofNat 32 f)

/-- What `pfree(i)` does to the region. -/
def pfreeC (b : Region) (i : Val) : Region := setCell b (ix i 1) 0

/-! ## The region functions refine the specifications -/

section Refine
variable {maxpage : Nat} (hmax : 3 * maxpage < 2 ^ 32)
include hmax

/-- `is_norm` refines `is_at_norm_spec`. -/
theorem is_norm_ref {d : PData} {b : Region} (hM : MatchD maxpage d b) {i r : Nat}
    (h : is_at_norm_spec maxpage i d = some r) : isNormC b (BitVec.ofNat 32 i) = BitVec.ofNat 32 r := by
  unfold is_at_norm_spec at h
  by_cases hi : i < maxpage
  · rw [if_pos hi] at h
    have hm := hM.mat i hi
    cases hA : d.AT i with
    | ATUndef => rw [hA] at h; simp at h
    | ATValid b0 t n =>
      rw [hA] at h hm
      obtain ⟨hz, -, -⟩ := hm
      simp only [isNormC, ix0 hmax hi]
      rcases ztype_cases hz with ⟨h0, rfl⟩ | ⟨h0, rfl⟩ | ⟨h0, rfl⟩
      · rw [val_of_toNat h0 (by decide)]; simp at h; subst h; rfl
      · rw [val_of_toNat h0 (by decide)]; simp at h; subst h; rfl
      · rw [val_of_toNat h0 (by decide)]; simp at h; subst h; rfl
  · rw [if_neg hi] at h; cases h

/-- `at_get` refines `get_at_u_spec`. -/
theorem at_get_ref {d : PData} {b : Region} (hM : MatchD maxpage d b) {i r : Nat}
    (h : get_at_u_spec maxpage i d = some r) : atGetC b (BitVec.ofNat 32 i) = BitVec.ofNat 32 r := by
  unfold get_at_u_spec at h
  by_cases hi : i < maxpage
  · rw [if_pos hi] at h
    have hm := hM.mat i hi
    cases hA : d.AT i with
    | ATUndef => rw [hA] at h; simp at h
    | ATValid b0 t n =>
      rw [hA] at h hm
      obtain ⟨-, hu, -⟩ := hm
      simp only [atGetC, ix1 hmax hi]
      rcases zbool_cases hu with ⟨h0, rfl⟩ | ⟨h0, rfl⟩
      · rw [val_of_toNat h0 (by decide)]; simp at h; subst h; rfl
      · rw [val_of_toNat h0 (by decide)]; simp at h; subst h; rfl
  · rw [if_neg hi] at h; cases h

/-- The loop's test agrees with the abstract "free". -/
theorem free_agree {d : PData} {b : Region} (hM : MatchD maxpage d b) {m : Nat} (hm : m < maxpage)
    (hv : ∃ b0 t n, d.AT m = .ATValid b0 t n) : freeC b m = isFree (d.AT m) := by
  obtain ⟨b0, t, n, hA⟩ := hv
  have h1 : is_at_norm_spec maxpage m d = some (if t = .ATNorm then 1 else 0) := by
    simp only [is_at_norm_spec, if_pos hm, hA]; split <;> rfl
  have h2 : get_at_u_spec maxpage m d = some (if b0 then 1 else 0) := by
    simp only [get_at_u_spec, if_pos hm, hA]; cases b0 <;> rfl
  simp only [freeC, is_norm_ref hmax hM h1, at_get_ref hmax hM h2, hA]
  cases b0 <;> cases t <;> simp [isFree] <;> decide

theorem scan_agree {d : PData} {b : Region} (hM : MatchD maxpage d b) (hle : d.nps ≤ maxpage)
    (hv : ∀ i, i < d.nps → ∃ b0 t n, d.AT i = .ATValid b0 t n) :
    ∀ (k m : Nat), m + k = d.nps → scanC b d.nps m k = (ffFrom d.AT m k).getD d.nps
  | 0, _, _ => rfl
  | k + 1, m, h => by
    simp only [scanC, ffFrom, free_agree hmax hM (show m < maxpage by omega) (hv m (by omega))]
    split
    · rfl
    · exact scan_agree hM hle hv k (m + 1) (by omega)

/-- **`palloc` refines `palloc'_spec`.** -/
theorem palloc_ref {kl kh : Nat} {d d' : PData} {b : Region} {r : Nat} (hM : MatchD maxpage d b)
    (hI : ATInv maxpage kl kh d) (h : palloc'_spec d = some (d', r)) :
    MatchD maxpage d' (pallocC maxpage b).1 ∧ (pallocC maxpage b).2 = BitVec.ofNat 32 r := by
  have hsc := scan_agree hmax hM hI.valid_nps.2 (fun i hi => hI.valid hi) (d.nps - 1) 1
  unfold palloc'_spec at h
  by_cases hin : d.init = true
  · rw [if_pos hin] at h
    unfold pallocC
    simp only [← hM.mnps]
    cases hff : first_free d.AT d.nps with
    | none =>
      rw [hff] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      by_cases hn : d.nps = 0
      · simp [hn, scanC]; exact hM
      · have : scanC b d.nps 1 (d.nps - 1) = d.nps := by
          rw [hsc (by omega)]; unfold first_free at hff; rw [hff]; rfl
        rw [if_pos this]; exact ⟨hM, rfl⟩
    | some i =>
      rw [hff] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hi0, hin', ⟨c, hc⟩, -⟩ := first_free_some hff
      have hi : i < maxpage := by have := hI.valid_nps.2; omega
      have : scanC b d.nps 1 (d.nps - 1) = i := by
        rw [hsc (by omega)]; unfold first_free at hff; rw [hff]; rfl
      rw [this, if_neg (by omega), ix1 hmax hi, ix2 hmax hi]
      refine ⟨⟨fun j hj => ?_, ?_⟩, rfl⟩
      · by_cases hji : j = i
        · subst hji
          have hm := hM.mat j hj
          rw [hc] at hm
          simp only [setAt_eq, setCell]
          have e1 : (3 * j + 2 = 3 * j + 2) := rfl
          simp only [show ¬ (3 * j + 1 = 3 * j + 2) by omega, show ¬ (3 * j = 3 * j + 2) by omega,
            show ¬ (3 * j = 3 * j + 1) by omega, if_true, if_false]
          exact ⟨hm.1, rfl, rfl⟩
        · simp only [setAt_ne _ _ hji, setCell]
          simp only [show ¬ (3 * j + 2 = 3 * i + 2) by omega, show ¬ (3 * j + 2 = 3 * i + 1) by omega,
            show ¬ (3 * j + 1 = 3 * i + 2) by omega, show ¬ (3 * j + 1 = 3 * i + 1) by omega,
            show ¬ (3 * j = 3 * i + 2) by omega, show ¬ (3 * j = 3 * i + 1) by omega, if_false]
          exact hM.mat j hj
      · simp only [setCell, show ¬ (3 * maxpage = 3 * i + 2) by omega,
          show ¬ (3 * maxpage = 3 * i + 1) by omega, if_false]
        exact hM.mnps
  · rw [if_neg hin] at h; cases h

/-- **`pfree` refines `pfree'_spec`.** -/
theorem pfree_ref {d d' : PData} {b : Region} {i : Nat} (hM : MatchD maxpage d b)
    (h : pfree'_spec maxpage i d = some d') : MatchD maxpage d' (pfreeC b (BitVec.ofNat 32 i)) := by
  unfold pfree'_spec at h
  by_cases hin : d.init = true
  · rw [if_pos hin] at h
    by_cases hi : i < maxpage
    · rw [if_pos hi] at h
      have hm := hM.mat i hi
      cases hA : d.AT i with
      | ATUndef => rw [hA] at h; simp at h
      | ATValid b0 t n =>
        rw [hA] at h hm
        cases hP : d.pperm i <;> rw [hP] at h <;> cases b0 <;> cases t <;> cases n <;> simp at h
        subst h
        unfold pfreeC
        rw [ix1 hmax hi]
        refine ⟨fun j hj => ?_, ?_⟩
        · by_cases hji : j = i
          · subst hji
            simp only [setAt_eq, setCell, show ¬ (3 * j + 2 = 3 * j + 1) by omega,
              show ¬ (3 * j = 3 * j + 1) by omega, if_true, if_false]
            exact ⟨hm.1, rfl, hm.2.2⟩
          · simp only [setAt_ne _ _ hji, setCell, show ¬ (3 * j + 2 = 3 * i + 1) by omega,
              show ¬ (3 * j + 1 = 3 * i + 1) by omega, show ¬ (3 * j = 3 * i + 1) by omega, if_false]
            exact hM.mat j hj
        · simp only [setCell, show ¬ (3 * maxpage = 3 * i + 1) by omega, if_false]
          exact hM.mnps
    · rw [if_neg hi] at h; cases h
  · rw [if_neg hin] at h; cases h

end Refine

end MALOp
