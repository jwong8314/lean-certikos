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

/-! ## The C code (`MBootCSource.v`, `MALOpCSource.v`) -/

/-- The index of `AT[i].field`. -/
def ixE (ie : Expr) (k : Val) : Expr := .bin .add (.bin .mul ie (.const 3)) (.const k)

/-- `x = is_norm(i)`: `x = AT[i].isnorm; if (x != 0) { if (x == 1) x = 0; else x = 1; }` -/
def isNormS (x : Ident) (ie : Expr) : Stmt APrim :=
  .seq (.call x .pull [lkE, ixE ie 0])
    (.ite (.bin .ne (.var x) (.const 0))
      (.ite (.bin .eq (.var x) (.const 1)) (.assign x (.const 0)) (.assign x (.const 1))) .skip)

/-- `x = at_get(i)`: `x = AT[i].allocated; if (x != 0) x = 1;` -/
def atGetS (x : Ident) (ie : Expr) : Stmt APrim :=
  .seq (.call x .pull [lkE, ixE ie 1]) (.ite (.bin .ne (.var x) (.const 0)) (.assign x (.const 1)) .skip)

/-- `at_set(i, v)`: `AT[i].allocated = v;` -/
def atSetS (ie ve : Expr) : Stmt APrim := .call "_" .push [lkE, ixE ie 1, ve]

/-- `at_set_c(i, v)`: `AT[i].c = v;` -/
def atSetCS (ie ve : Expr) : Stmt APrim := .call "_" .push [lkE, ixE ie 2, ve]

/-- `x = get_nps()` -/
def getNpsS (maxpage : Nat) (x : Ident) : Stmt APrim :=
  .call x .pull [lkE, .const (BitVec.ofNat 32 (3 * maxpage))]

/-- `palloc_index < tnps && palloc_free_index == tnps` -/
def guardE : Expr := .bin .mul (.bin .ltu (.var "pi") (.var "tnps")) (.bin .eq (.var "fi") (.var "tnps"))

/-- The loop body of `palloc`:
`isn = is_norm(pi); if (isn == 1) { cur = at_get(pi); if (cur == 0) fi = pi; } pi++;` -/
def loopBody : Stmt APrim :=
  .seq (isNormS "isn" (.var "pi"))
    (.seq (.ite (.bin .eq (.var "isn") (.const 1))
        (.seq (atGetS "cur" (.var "pi")) (.ite (.bin .eq (.var "cur") (.const 0)) (.assign "fi" (.var "pi")) .skip))
        .skip)
      (.assign "pi" (.bin .add (.var "pi") (.const 1))))

def pallocLoop : Stmt APrim := .while guardE loopBody

/-- The body of `palloc` (`pi` is `palloc_index`, `fi` is `palloc_free_index`):
`tnps = get_nps(); pi = 1; fi = tnps; while (pi < tnps && fi == tnps) { ... }
if (fi == tnps) fi = 0; else { at_set(fi, 1); at_set_c(fi, 0); } return fi;` -/
def pallocCS (maxpage : Nat) : Stmt APrim :=
  .seq (getNpsS maxpage "tnps") (.seq (.assign "pi" (.const 1)) (.seq (.assign "fi" (.var "tnps"))
    (.seq pallocLoop
      (.seq (.ite (.bin .eq (.var "fi") (.var "tnps")) (.assign "fi" (.const 0))
          (.seq (atSetS (.var "fi") (.const 1)) (atSetCS (.var "fi") (.const 0))))
        (.assign "r" (.var "fi"))))))

/-- `palloc()` under the allocation table's lock. The result is in `r`. -/
def palloc (maxpage : Nat) : Stmt APrim := .seq acquireA (.seq (pallocCS maxpage) relA)

/-- `pfree(j)`: `at_set(j, 0);` -/
def pfreeCS : Stmt APrim := atSetS (.var "j") (.const 0)

def pfree : Stmt APrim := .seq acquireA (.seq pfreeCS relA)

/-! ## The C code computes the region functions -/

theorem set_set (σ : Locals) (x : Ident) (a v : Val) : (σ.set x a).set x v = σ.set x v := by
  funext y; by_cases h : y = x <;> simp [Locals.set, h]

theorem set_eq {σ : Locals} {x : Ident} {v w : Val} (h : v = w) : (σ.set x v) x = w :=
  (Locals.set_same _ _ _).trans h

theorem set_neq {σ : Locals} {x : Ident} {v w : Val} (h : ¬ v = w) : (σ.set x v) x ≠ w :=
  fun e => h ((Locals.set_same _ _ _).symm.trans e)

theorem ult_ofNat {m n : Nat} (hm : m < 2 ^ 32) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 m).ult (BitVec.ofNat 32 n) = decide (m < n) := by
  simp [BitVec.ult, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn]

theorem guard_eval (σ : Locals) : guardE.eval σ =
    (if (σ "pi").ult (σ "tnps") then 1 else 0) * (if σ "fi" = σ "tnps" then 1 else 0) := rfl

theorem isNorm_run {εR : REnv} {c : CPU} {i : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (x : Ident) (ie : Expr) :
    Runs (rprimsA εR c) (isNormS x ie) σ l (σ.set x (isNormC b (ie.eval σ))) l := by
  have hrd := cs1_rd (εR := εR) h hlk x (ixE ie 0)
  have e : ((ixE ie 0).eval σ).toNat = ix (ie.eval σ) 0 := rfl
  rw [e] at hrd
  unfold isNormC
  by_cases h0 : b (ix (ie.eval σ) 0) = 0
  · rw [if_pos h0]
    have hs : σ.set x (0 : Val) = σ.set x (b (ix (ie.eval σ) 0)) := by rw [h0]
    rw [hs]
    exact Runs.seq hrd (Runs.ite_false (ne_false (set_eq h0)) Runs.skip)
  · rw [if_neg h0]
    by_cases h1 : b (ix (ie.eval σ) 0) = 1
    · rw [if_pos h1]
      have ha := Runs.assign (P := rprimsA εR c) (σ := σ.set x (b (ix (ie.eval σ) 0))) (l := l) x (.const 0)
      rw [set_set] at ha
      exact Runs.seq hrd (Runs.ite_true (ne_true (set_neq h0)) (Runs.ite_true (eq_true (set_eq h1)) ha))
    · rw [if_neg h1]
      have ha := Runs.assign (P := rprimsA εR c) (σ := σ.set x (b (ix (ie.eval σ) 0))) (l := l) x (.const 1)
      rw [set_set] at ha
      exact Runs.seq hrd (Runs.ite_true (ne_true (set_neq h0)) (Runs.ite_false (eq_false (set_neq h1)) ha))

theorem atGet_run {εR : REnv} {c : CPU} {i : Nat} {l : RLog} {b : Region} (h : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) (x : Ident) (ie : Expr) :
    Runs (rprimsA εR c) (atGetS x ie) σ l (σ.set x (atGetC b (ie.eval σ))) l := by
  have hrd := cs1_rd (εR := εR) h hlk x (ixE ie 1)
  have e : ((ixE ie 1).eval σ).toNat = ix (ie.eval σ) 1 := rfl
  rw [e] at hrd
  unfold atGetC
  by_cases h0 : b (ix (ie.eval σ) 1) = 0
  · rw [if_pos h0]
    have hs : σ.set x (0 : Val) = σ.set x (b (ix (ie.eval σ) 1)) := by rw [h0]
    rw [hs]
    exact Runs.seq hrd (Runs.ite_false (ne_false (set_eq h0)) Runs.skip)
  · rw [if_neg h0]
    have ha := Runs.assign (P := rprimsA εR c) (σ := σ.set x (b (ix (ie.eval σ) 1))) (l := l) x (.const 1)
    rw [set_set] at ha
    exact Runs.seq hrd (Runs.ite_true (ne_true (set_neq h0)) ha)

/-- One iteration of `palloc`'s loop. -/
theorem body_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b : Region} (hcs : CS1 c i l b) {σ : Locals}
    (hlk : (σ "lk").toNat = i) {m nps : Nat} (hpi : σ "pi" = BitVec.ofNat 32 m)
    (hfi : σ "fi" = BitVec.ofNat 32 nps) (htn : σ "tnps" = BitVec.ofNat 32 nps) :
    ∃ σ', Runs (rprimsA εR c) loopBody σ l σ' l ∧ σ' "pi" = BitVec.ofNat 32 (m + 1) ∧
      σ' "fi" = (if freeC b m = true then BitVec.ofNat 32 m else BitVec.ofNat 32 nps) ∧
      σ' "tnps" = BitVec.ofNat 32 nps ∧ σ' "lk" = σ "lk" := by
  let σ1 := σ.set "isn" (isNormC b (BitVec.ofNat 32 m))
  have h1 : Runs (rprimsA εR c) (isNormS "isn" (.var "pi")) σ l σ1 l := by
    have h := isNorm_run (εR := εR) hcs hlk "isn" (.var "pi")
    have e : (Expr.var "pi").eval σ = BitVec.ofNat 32 m := hpi
    rw [e] at h; exact h
  have hinc : ∀ (τ : Locals), τ "pi" = BitVec.ofNat 32 m →
      Runs (rprimsA εR c) (.assign "pi" (.bin .add (.var "pi") (.const 1))) τ l
        (τ.set "pi" (BitVec.ofNat 32 (m + 1))) l := by
    intro τ hτ
    have h := Runs.assign (P := rprimsA εR c) (σ := τ) (l := l) "pi" (.bin .add (.var "pi") (.const 1))
    have e : (Expr.bin .add (.var "pi") (.const 1)).eval τ = BitVec.ofNat 32 (m + 1) := by
      simp [Expr.eval, BinOp.eval, hτ, BitVec.ofNat_add]
    rw [e] at h; exact h
  by_cases hn : isNormC b (BitVec.ofNat 32 m) = 1
  · let σ2 := σ1.set "cur" (atGetC b (BitVec.ofNat 32 m))
    have h2 : Runs (rprimsA εR c) (atGetS "cur" (.var "pi")) σ1 l σ2 l := by
      have h := atGet_run (εR := εR) hcs (σ := σ1) (by simpa [σ1, Locals.set] using hlk) "cur" (.var "pi")
      have e : (Expr.var "pi").eval σ1 = BitVec.ofNat 32 m := by
        show σ1 "pi" = _; simp [σ1, Locals.set, hpi]
      rw [e] at h; exact h
    have hg1 : ¬ (Expr.bin .eq (.var "isn") (.const 1)).eval σ1 = 0 := eq_true (by simp [σ1, hn])
    by_cases hc0 : atGetC b (BitVec.ofNat 32 m) = 0
    · let σ3 := σ2.set "fi" (BitVec.ofNat 32 m)
      have h3 : Runs (rprimsA εR c) (.assign "fi" (.var "pi")) σ2 l σ3 l := by
        have h := Runs.assign (P := rprimsA εR c) (σ := σ2) (l := l) "fi" (.var "pi")
        have e : (Expr.var "pi").eval σ2 = BitVec.ofNat 32 m := by
          show σ2 "pi" = _; simp [σ2, σ1, Locals.set, hpi]
        rw [e] at h; exact h
      have hf : freeC b m = true := by simp [freeC, hn, hc0]
      refine ⟨σ3.set "pi" (BitVec.ofNat 32 (m + 1)), Runs.seq h1 (Runs.seq (Runs.ite_true hg1 (Runs.seq h2
        (Runs.ite_true (eq_true (by simp [σ2, hc0])) h3))) (hinc σ3 (by simp [σ3, σ2, σ1, Locals.set, hpi]))),
        by simp, ?_, ?_, ?_⟩
      · simp [hf, σ3, Locals.set]
      · simp [σ3, σ2, σ1, Locals.set, htn]
      · simp [σ3, σ2, σ1, Locals.set]
    · have hf : ¬ freeC b m = true := by
        intro h; simp only [freeC, Bool.and_eq_true, decide_eq_true_eq] at h; exact hc0 h.2
      refine ⟨σ2.set "pi" (BitVec.ofNat 32 (m + 1)), Runs.seq h1 (Runs.seq (Runs.ite_true hg1 (Runs.seq h2
        (Runs.ite_false (eq_false (set_neq hc0)) Runs.skip))) (hinc σ2 (by simp [σ2, σ1, Locals.set, hpi]))),
        by simp, ?_, ?_, ?_⟩
      · simp [hf, σ2, σ1, Locals.set, hfi]
      · simp [σ2, σ1, Locals.set, htn]
      · simp [σ2, σ1, Locals.set]
  · have hf : ¬ freeC b m = true := by
      intro h; simp only [freeC, Bool.and_eq_true, decide_eq_true_eq] at h; exact hn h.1
    refine ⟨σ1.set "pi" (BitVec.ofNat 32 (m + 1)), Runs.seq h1 (Runs.seq (Runs.ite_false
      (eq_false (set_neq hn)) Runs.skip) (hinc σ1 (by simp [σ1, Locals.set, hpi]))), by simp, ?_, ?_, ?_⟩
    · simp [hf, σ1, Locals.set, hfi]
    · simp [σ1, Locals.set, htn]
    · simp [σ1, Locals.set]

/-- **`palloc`'s loop computes `scanC`.** It only reads. -/
theorem loop_run (εR : REnv) {c : CPU} {i : Nat} {l : RLog} {b : Region} (hcs : CS1 c i l b) (nps : Nat)
    (hnps : nps < 2 ^ 32) :
    ∀ (k m : Nat), nps - m = k → (m ≤ nps ∨ m = 1) → ∀ σ : Locals, (σ "lk").toNat = i →
      σ "pi" = BitVec.ofNat 32 m → σ "fi" = BitVec.ofNat 32 nps → σ "tnps" = BitVec.ofNat 32 nps →
      ∃ σ', Runs (rprimsA εR c) pallocLoop σ l σ' l ∧ σ' "fi" = BitVec.ofNat 32 (scanC b nps m k) ∧
        σ' "tnps" = BitVec.ofNat 32 nps ∧ σ' "lk" = σ "lk"
  | 0, m, hk, hm, σ, _, hpi, hfi, htn => by
    refine ⟨σ, Runs.while_false ?_, by simp [scanC, hfi], htn, rfl⟩
    rw [guard_eval, hpi, htn, ult_ofNat (by omega) hnps]
    simp [show ¬ m < nps by omega]
  | k + 1, m, hk, hm, σ, hlk, hpi, hfi, htn => by
    have hmlt : m < nps := by omega
    obtain ⟨σ1, hb, hpi1, hfi1, htn1, hlk1⟩ := body_run εR hcs hlk hpi hfi htn
    have hg : ¬ guardE.eval σ = 0 := by
      rw [guard_eval, hpi, htn, hfi, ult_ofNat (by omega) hnps]; simp [hmlt]
    by_cases hf : freeC b m = true
    · rw [if_pos hf] at hfi1
      refine ⟨σ1, Runs.while_true hg hb (Runs.while_false ?_), by simp [scanC, hf, hfi1], htn1, hlk1⟩
      rw [guard_eval, hfi1, htn1]
      have hne : (BitVec.ofNat 32 m : Val) ≠ BitVec.ofNat 32 nps := ofNat_ne (by omega) hnps (by omega)
      simp [hne]
    · rw [if_neg hf] at hfi1
      obtain ⟨σ2, hr, hfi2, htn2, hlk2⟩ := loop_run εR hcs nps hnps k (m + 1) (by omega) (Or.inl (by omega))
        σ1 (by rw [hlk1]; exact hlk) hpi1 hfi1 htn1
      exact ⟨σ2, Runs.while_true hg hb hr, by simp [scanC, hf, hfi2], htn2, hlk2.trans hlk1⟩

theorem scanC_bound (b : Region) (nps : Nat) : ∀ (k m : Nat),
    scanC b nps m k = nps ∨ (m ≤ scanC b nps m k ∧ scanC b nps m k < m + k)
  | 0, _ => Or.inl rfl
  | k + 1, m => by
    simp only [scanC]
    split
    · exact Or.inr ⟨Nat.le_refl _, by omega⟩
    · rcases scanC_bound b nps k (m + 1) with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by omega⟩

/-- **The body of `palloc` computes `pallocC`**, on any region. -/
theorem pallocCS_run (εR : REnv) {c : CPU} {i : Nat} {maxpage : Nat} (hmax : 3 * maxpage < 2 ^ 32)
    (σ : Locals) (l : RLog) (b : Region) (hlk : (σ "lk").toNat = i) (hcs : CS1 c i l b) :
    ∃ σ' l', Runs (rprimsA εR c) (pallocCS maxpage) σ l σ' l' ∧
      CS1 c i l' (pallocC maxpage b).1 ∧ σ' "r" = (pallocC maxpage b).2 := by
  let N := (b (3 * maxpage)).toNat
  have hN : N < 2 ^ 32 := (b (3 * maxpage)).isLt
  have hbN : b (3 * maxpage) = BitVec.ofNat 32 N := val_of_toNat rfl hN
  let σ1 := σ.set "tnps" (BitVec.ofNat 32 N)
  have h1 : Runs (rprimsA εR c) (getNpsS maxpage "tnps") σ l σ1 l := by
    have h := cs1_rd (εR := εR) hcs hlk "tnps" (.const (BitVec.ofNat 32 (3 * maxpage)))
    have e : ((Expr.const (BitVec.ofNat 32 (3 * maxpage))).eval σ).toNat = 3 * maxpage := by
      show (BitVec.ofNat 32 (3 * maxpage)).toNat = _
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hmax
    rw [e, hbN] at h; exact h
  let σ2 := σ1.set "pi" 1
  let σ3 := σ2.set "fi" (BitVec.ofNat 32 N)
  have h2 : Runs (rprimsA εR c) (.assign "pi" (.const 1)) σ1 l σ2 l := Runs.assign _ _
  have h3 : Runs (rprimsA εR c) (.assign "fi" (.var "tnps")) σ2 l σ3 l := by
    have h := Runs.assign (P := rprimsA εR c) (σ := σ2) (l := l) "fi" (.var "tnps")
    have e : (Expr.var "tnps").eval σ2 = BitVec.ofNat 32 N := by show σ2 "tnps" = _; simp [σ2, σ1, Locals.set]
    rw [e] at h; exact h
  obtain ⟨σ4, h4, hfi4, htn4, hlk4⟩ := loop_run εR hcs N hN (N - 1) 1 rfl (Or.inr rfl) σ3
    (by simpa [σ3, σ2, σ1, Locals.set] using hlk) (by simp [σ3, σ2, Locals.set]) (by simp [σ3])
    (by simp [σ3, σ2, σ1, Locals.set])
  have hlk4' : (σ4 "lk").toNat = i := by rw [hlk4]; simpa [σ3, σ2, σ1, Locals.set] using hlk
  have hfb : scanC b N 1 (N - 1) ≤ N := by
    rcases scanC_bound b N (N - 1) 1 with h | ⟨h1, h2⟩ <;> omega
  have hpc : pallocC maxpage b = (if scanC b N 1 (N - 1) = N then (b, 0) else
      (setCell (setCell b (ix (BitVec.ofNat 32 (scanC b N 1 (N - 1))) 1) 1)
        (ix (BitVec.ofNat 32 (scanC b N 1 (N - 1))) 2) 0, BitVec.ofNat 32 (scanC b N 1 (N - 1)))) := rfl
  by_cases hf : scanC b N 1 (N - 1) = N
  · rw [hpc, if_pos hf]
    have hg : ¬ (Expr.bin .eq (.var "fi") (.var "tnps")).eval σ4 = 0 := by
      simp [Expr.eval, BinOp.eval, hfi4, htn4, hf]
    let σ5 := σ4.set "fi" 0
    have h5 : Runs (rprimsA εR c) (.assign "fi" (.const 0)) σ4 l σ5 l := Runs.assign _ _
    have h6 : Runs (rprimsA εR c) (.assign "r" (.var "fi")) σ5 l (σ5.set "r" 0) l := by
      have h := Runs.assign (P := rprimsA εR c) (σ := σ5) (l := l) "r" (.var "fi")
      have e : (Expr.var "fi").eval σ5 = 0 := by show σ5 "fi" = _; simp [σ5]
      rw [e] at h; exact h
    exact ⟨σ5.set "r" 0, l, Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq h4
      (Runs.seq (Runs.ite_true hg h5) h6)))), hcs, by simp⟩
  · rw [hpc, if_neg hf]
    have hne : (BitVec.ofNat 32 (scanC b N 1 (N - 1)) : Val) ≠ BitVec.ofNat 32 N :=
      ofNat_ne (by omega) hN hf
    have hg : (Expr.bin .eq (.var "fi") (.var "tnps")).eval σ4 = 0 := by
      simp [Expr.eval, BinOp.eval, hfi4, htn4, hne]
    obtain ⟨l5, h5, hc5⟩ := cs1_wr (εR := εR) hcs hlk4' (ixE (.var "fi") 1) (.const 1)
    have e5 : ((ixE (.var "fi") 1).eval σ4).toNat = ix (BitVec.ofNat 32 (scanC b N 1 (N - 1))) 1 := by
      show ix (σ4 "fi") 1 = _; rw [hfi4]
    have e5' : (Expr.const 1).eval σ4 = 1 := rfl
    rw [e5, e5'] at hc5
    let σ5 := σ4.set "_" 0
    obtain ⟨l6, h6, hc6⟩ := cs1_wr (εR := εR) hc5 (σ := σ5) (by simpa [σ5, Locals.set] using hlk4')
      (ixE (.var "fi") 2) (.const 0)
    have e6 : ((ixE (.var "fi") 2).eval σ5).toNat = ix (BitVec.ofNat 32 (scanC b N 1 (N - 1))) 2 := by
      show ix (σ5 "fi") 2 = _; simp [σ5, Locals.set, hfi4]
    have e6' : (Expr.const 0).eval σ5 = 0 := rfl
    rw [e6, e6'] at hc6
    let σ6 := σ5.set "_" 0
    have h7 : Runs (rprimsA εR c) (.assign "r" (.var "fi")) σ6 l6
        (σ6.set "r" (BitVec.ofNat 32 (scanC b N 1 (N - 1)))) l6 := by
      have h := Runs.assign (P := rprimsA εR c) (σ := σ6) (l := l6) "r" (.var "fi")
      have e : (Expr.var "fi").eval σ6 = BitVec.ofNat 32 (scanC b N 1 (N - 1)) := by
        show σ6 "fi" = _; simp [σ6, σ5, Locals.set, hfi4]
      rw [e] at h; exact h
    exact ⟨_, l6, Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq h4
      (Runs.seq (Runs.ite_false hg (Runs.seq h5 h6)) h7)))), hc6, by simp⟩

theorem pallocCS_fr (maxpage : Nat) : frS "lk" (pallocCS maxpage) = true := by
  simp [frS, pallocCS, getNpsS, pallocLoop, loopBody, isNormS, atGetS, atSetS, atSetCS]

/-! ## `palloc` and `pfree` under the lock -/

/-- **`palloc()` computes `pallocC`** of the table the previous holder released. -/
theorem palloc_guarantee {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) {maxpage : Nat} (hmax : 3 * maxpage < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨palloc maxpage, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = (pallocC maxpage (hmemR iv.toNat H1)).1 ∧
      σ' "r" = (pallocC maxpage (hmemR iv.toNat H1)).2 := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, -, hR1, hR2⟩ :=
    cs_guarantee1 hE hRR hc hRA hl hidle bound K hK hF σ hσ (pallocCS maxpage)
      (fun b _ b' σ' => b' = (pallocC maxpage b).1 ∧ σ' "r" = (pallocC maxpage b).2)
      (fun σ l b hlk hcs => by
        obtain ⟨σ', l', hr, hc', hres⟩ := pallocCS_run εR hmax σ l b (by rw [hlk]) hcs
        exact ⟨σ', l', _, hr, hc', (hr.frame (pallocCS_fr maxpage)).trans hlk, rfl, hres⟩)
  exact ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, hR1, by
    rw [Locals.set_other _ _ (by decide)]; exact hR2⟩

/-- **`palloc()` refines `palloc'_spec`.** If the table the previous holder
released matches abstract data `d` that satisfies the invariant, and the
specification is defined on `d`, then the table `palloc` releases matches the
specification's result, and `r` is the page it returns. -/
theorem palloc_refines {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) {maxpage : Nat} (hmax : 3 * maxpage < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨palloc maxpage, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      ∀ (kl kh : Nat) (d d' : PData) (r : Nat), MatchD maxpage d (hmemR iv.toNat H1) →
        ATInv maxpage kl kh d → palloc'_spec d = some (d', r) →
        MatchD maxpage d' (hmemR iv.toNat H3) ∧ σ' "r" = BitVec.ofNat 32 r := by
  obtain ⟨σ', rb, S3, H1, H3, hrun, hl3, hid, hm, hr⟩ :=
    palloc_guarantee hE hRR hc hRA hl hidle bound K hK hF σ hσ hmax
  refine ⟨σ', rb, S3, H1, H3, hrun, hl3, hid, fun kl kh d d' r hM hI hs => ?_⟩
  obtain ⟨g1, g2⟩ := palloc_ref hmax hM hI hs
  exact ⟨by rw [hm]; exact g1, by rw [hr]; exact g2⟩

/-- **`pfree(j)` refines `pfree'_spec`.** -/
theorem pfree_refines {εR : REnv} {ε : AEnv} {c : CPU} (hE : EnvErases εR ε) (hRR : RelyR εR c)
    (hc : c < NCPU) (hRA : LockArray.RelyA ε c) {l : RLog} {S : RState} {H : HLogR}
    (hl : rreplay l = some (S, H)) {iv : Val} (hidle : (S.lk iv.toNat).phase c = .idle)
    (bound : ALog → Nat) (K : Nat) (hK : ∀ l, bound l ≤ K)
    (hF : LockArray.FairA ε c iv.toNat (ticket (LockArray.projL iv.toNat (apull ε c (erase l)))) bound)
    (σ : Locals) (hσ : σ "lk" = iv) {maxpage : Nat} (hmax : 3 * maxpage < 2 ^ 32) :
    ∃ (σ' : Locals) (rb : RLog) (S3 : RState) (H1 H3 : HLogR),
      Star (rprimsA εR c) ⟨pfree, .stop, σ, l⟩ ⟨.skip, .stop, σ', rb⟩ ∧
      rreplay rb = some (S3, H3) ∧ (S3.lk iv.toNat).phase c = .idle ∧
      hmemR iv.toNat H3 = pfreeC (hmemR iv.toNat H1) (σ "j") ∧
      ∀ (d d' : PData) (i : Nat), σ "j" = BitVec.ofNat 32 i → MatchD maxpage d (hmemR iv.toNat H1) →
        pfree'_spec maxpage i d = some d' → MatchD maxpage d' (hmemR iv.toNat H3) := by
  obtain ⟨σ1, σ2, rb, S3, H1, H3, hrun, hl3, hid, hfr, hR⟩ :=
    cs_guarantee1 hE hRR hc hRA hl hidle bound K hK hF σ hσ pfreeCS
      (fun b σ b' _ => b' = pfreeC b (σ "j"))
      (fun σ l b hlk hcs => by
        obtain ⟨l', hw, hc'⟩ := cs1_wr (εR := εR) hcs (σ := σ) (by rw [hlk]) (ixE (.var "j") 1) (.const 0)
        exact ⟨σ.set "_" 0, l', _, hw, hc', by rw [Locals.set_other _ _ (by decide)]; exact hlk, rfl⟩)
  have hj := hfr "j" (by decide) (by decide) (by decide) (by decide)
  have hm : hmemR iv.toNat H3 = pfreeC (hmemR iv.toNat H1) (σ "j") := by rw [hR, hj]
  refine ⟨σ2.set "_" 0, rb, S3, H1, H3, hrun, hl3, hid, hm, fun d d' i hi hM hs => ?_⟩
  rw [hm, hi]; exact pfree_ref hmax hM hs

end MALOp
