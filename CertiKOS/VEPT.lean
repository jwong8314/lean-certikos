import CertiKOS.MPTIntro
import CertiKOS.MALInitC
import CertiKOS.LayerStep

/-!
# Virtualization: the extended page table (EPT), ported from the Coq version

Transcribed from `coq/EPT.v`, which ports mCertiKOS's `objects/ObjEPT.v` and
proves code written from the C in its comments. Here the code is ClightL and
runs inside a critical section, as every port does.

The EPT maps guest-physical pages to host-physical addresses. It is a flat
table `ept.ptab[pdpt][pdir][ptab]` in the kernel region at `eb`, one word per
guest page, for the 2^20 pages of a 4 GB guest.

* `ept_leaf`, `ept_store`: the four-level tree of mCertiKOS, read and
  written at one guest page. `store_leaf`: a store changes that page only.
* `MatchE`: guest page `g`'s entry is the cell `eb + g`.
* `getPageEntry_step`, `setPageEntry_step`, `addMapping_step`,
  `gpaToHpa_step`, `mmap_step`, `setPermission_step`, `eptInit_step`:
  **each function refines its specification.**

What differs from `coq/EPT.v`: entries are machine words (`Val`), so the range
checks on them are dropped. Otherwise as there: `real_ept` gives every guest
page the entry 0, and the four accessors that build the tree level by level
are not implemented.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace VEPT

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MPTIntro
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)

/-! ## Abstract data -/

inductive EPTE | EPTEValid (hpa : Val) | EPTEUndef
abbrev EPTAB := Nat → EPTE
inductive EPDTE | EPDTEValid (t : EPTAB) | EPDTEUndef
abbrev EPDT := Nat → EPDTE
inductive EPDPTE | EPDPTEValid (t : EPDT) | EPDPTEUndef
abbrev EPDPT := Nat → EPDPTE
inductive EPML4E | EPML4EValid (t : EPDPT) | EPML4EUndef
abbrev EPT := Nat → EPML4E

/-- The part of the abstract state this layer uses. -/
structure VData where
  ikern : Bool
  pg : Bool
  ihost : Bool
  ept : EPT

def PTAB' (i : Nat) : Nat := i % 512
def PDIR' (i : Nat) : Nat := i / 512 % 512
def PDPT' (i : Nat) : Nat := i / 262144 % 512
def PML4' (i : Nat) : Nat := i / 134217728 % 512

def EPT_NO_PERM : Val := 4294967288
def EPT_ADDR_MASK : Val := 4294963200
def NPG : Nat := 1048576

/-- The entry of guest page `gpa`, through the four levels. -/
def ept_leaf (e : EPT) (gpa : Nat) : Option Val :=
  match e (PML4' gpa) with
  | .EPML4EValid a =>
    match a (PDPT' gpa) with
    | .EPDPTEValid b =>
      match b (PDIR' gpa) with
      | .EPDTEValid c =>
        match c (PTAB' gpa) with
        | .EPTEValid h => some h
        | .EPTEUndef => none
      | .EPDTEUndef => none
    | .EPDPTEUndef => none
  | .EPML4EUndef => none

/-- Write the entry of guest page `gpa`, if the three upper levels exist. -/
def ept_store (e : EPT) (gpa : Nat) (v : Val) : Option EPT :=
  match e (PML4' gpa) with
  | .EPML4EValid a =>
    match a (PDPT' gpa) with
    | .EPDPTEValid b =>
      match b (PDIR' gpa) with
      | .EPDTEValid c =>
        some (setAt e (PML4' gpa) (.EPML4EValid (setAt a (PDPT' gpa) (.EPDPTEValid
          (setAt b (PDIR' gpa) (.EPDTEValid (setAt c (PTAB' gpa) (.EPTEValid v))))))))
      | .EPDTEUndef => none
    | .EPDPTEUndef => none
  | .EPML4EUndef => none

/-! ## Specifications (`ObjEPT.v`) -/

section Specs
variable (maxpage : Nat)

def flags (d : VData) : Prop := d.ikern = true ∧ d.pg = true ∧ d.ihost = true

instance (d : VData) : Decidable (flags d) := by unfold flags; exact inferInstance

def ept_get_page_entry_spec (gpa : Nat) (d : VData) : Option Val :=
  if flags d ∧ gpa < maxpage then ept_leaf d.ept gpa else none

def ept_set_page_entry_spec (gpa : Nat) (hpa : Val) (d : VData) : Option VData :=
  if flags d ∧ gpa < maxpage ∧ hpa.toNat < maxpage then
    match ept_store d.ept gpa hpa with
    | some e' => some { d with ept := e' }
    | none => none
  else none

/-- The entry a mapping writes: `(hpa & EPT_ADDR_MASK) | 71 | (mem_type << 3)`. -/
def mapVal (hpa memtype : Nat) : Val :=
  ((BitVec.ofNat 32 hpa &&& EPT_ADDR_MASK) ||| 71) ||| (BitVec.ofNat 32 memtype <<< (3 : Val).toNat)

def ept_add_mapping_spec (gpa hpa memtype : Nat) (d : VData) : Option (VData × Nat) :=
  if flags d ∧ gpa < maxpage ∧ hpa < maxpage ∧ memtype < 4096 then
    match ept_store d.ept gpa (mapVal hpa memtype) with
    | some e' => some ({ d with ept := e' }, 0)
    | none => none
  else none

def ept_invalidate_mappings_spec (d : VData) : Option Nat :=
  if d.ikern = true ∧ d.ihost = true then some 0 else none

def ept_gpa_to_hpa_spec (gpa : Nat) (d : VData) : Option Val :=
  match ept_get_page_entry_spec maxpage gpa d with
  | some e => if e &&& 7 = 0 then some 0 else some ((e &&& EPT_ADDR_MASK) ||| (BitVec.ofNat 32 gpa &&& 4095))
  | none => none

def ept_mmap_spec (gpa hpa memtype : Nat) (d : VData) : Option (VData × Nat) :=
  match ept_get_page_entry_spec maxpage gpa d with
  | some e =>
    if memtype < 4096 then
      if e &&& 7 = 0 then ept_add_mapping_spec maxpage gpa hpa memtype d else some (d, 1)
    else none
  | none => none

def ept_set_permission_spec (gpa perm : Nat) (d : VData) : Option VData :=
  match ept_get_page_entry_spec maxpage gpa d with
  | some e => ept_set_page_entry_spec maxpage gpa ((e &&& EPT_NO_PERM) ||| (BitVec.ofNat 32 perm &&& 7)) d
  | none => none

/-- Every guest page has the entry 0. -/
def real_ept (e : EPT) : EPT :=
  setAt e 0 (.EPML4EValid (fun j => if j < 4 then
    .EPDPTEValid (fun k => if k < 512 then .EPDTEValid (fun _ => .EPTEValid 0) else .EPDTEUndef)
    else .EPDPTEUndef))

def ept_init0_spec (d : VData) : Option VData :=
  if flags d then some { d with ept := real_ept d.ept } else none

end Specs

/-! ## Indices -/

theorem idx_split {g : Nat} (hg : g < NPG) :
    PML4' g = 0 ∧ PDPT' g < 4 ∧ PDIR' g < 512 ∧ PTAB' g < 512 ∧
      g = (PDPT' g * 512 + PDIR' g) * 512 + PTAB' g := by
  unfold PML4' PDPT' PDIR' PTAB'; unfold NPG at hg; omega

theorem idx_inj {g g' : Nat} (hg : g < NPG) (hg' : g' < NPG) (e1 : PDPT' g' = PDPT' g)
    (e2 : PDIR' g' = PDIR' g) (e3 : PTAB' g' = PTAB' g) : g' = g := by
  have a := (idx_split hg).2.2.2.2; have b := (idx_split hg').2.2.2.2
  rw [a, b, e1, e2, e3]

/-- **A store changes the entry of that guest page only.** -/
theorem store_leaf {e e' : EPT} {g : Nat} {v : Val} (hg : g < NPG) (hs : ept_store e g v = some e')
    {g' : Nat} (hg' : g' < NPG) : ept_leaf e' g' = if g' = g then some v else ept_leaf e g' := by
  have p0 := (idx_split hg).1; have p0' := (idx_split hg').1
  unfold ept_store at hs
  cases ea : e (PML4' g) with
  | EPML4EUndef => rw [ea] at hs; cases hs
  | EPML4EValid a =>
    rw [ea] at hs; simp only at hs
    cases eb : a (PDPT' g) with
    | EPDPTEUndef => rw [eb] at hs; cases hs
    | EPDPTEValid b =>
      rw [eb] at hs; simp only at hs
      cases ec : b (PDIR' g) with
      | EPDTEUndef => rw [ec] at hs; cases hs
      | EPDTEValid c =>
        rw [ec] at hs; simp only [Option.some.injEq] at hs
        subst hs
        unfold ept_leaf
        have p : PML4' g' = PML4' g := by rw [p0, p0']
        by_cases h : g' = g
        · subst h; simp [setAt]
        · rw [if_neg h]
          by_cases e1 : PDPT' g' = PDPT' g
          · by_cases e2 : PDIR' g' = PDIR' g
            · have e3 : PTAB' g' ≠ PTAB' g := fun e3 => h (idx_inj hg hg' e1 e2 e3)
              simp [setAt, p, e1, e2, e3, ea, eb, ec]
            · simp [setAt, p, e1, e2, ea, eb]
          · simp [setAt, p, e1, ea]

theorem real_leaf (e : EPT) {g : Nat} (hg : g < NPG) : ept_leaf (real_ept e) g = some 0 := by
  obtain ⟨p0, p1, p2, -, -⟩ := idx_split hg
  unfold ept_leaf real_ept
  rw [p0, setAt_eq]
  simp only [if_pos p1, if_pos p2]

/-! ## The table in the region -/

/-- Guest page `g`'s entry is the cell `eb + g`. -/
def MatchE (eb : Nat) (d : VData) (b : Region) : Prop :=
  ∀ g v, g < NPG → ept_leaf d.ept g = some v → b (eb + g) = v

/-- `&ept.ptab[EPT_PDPT_INDEX(x)][EPT_PDIR_INDEX(x)][EPT_PTAB_INDEX(x)]` -/
def addrE (eb : Nat) (x : Ident) : Expr :=
  .bin .add (.const (BitVec.ofNat 32 eb))
    (.bin .add (.bin .mul (.bin .add (.bin .mul (.bin .mod (.bin .div (.var x) (.const 262144)) (.const 512))
                                       (.const 512))
                                (.bin .mod (.bin .div (.var x) (.const 512)) (.const 512)))
                         (.const 512))
               (.bin .mod (.var x) (.const 512)))

theorem eval_addr {eb : Nat} (heb : eb + NPG ≤ 2 ^ 32) {σ : Locals} {x : Ident} {g : Nat} (hg : g < NPG)
    (hx : σ x = BitVec.ofNat 32 g) : ((addrE eb x).eval σ).toNat = eb + g := by
  unfold NPG at *
  show (BitVec.ofNat 32 eb + ((σ x / 262144 % 512 * 512 + σ x / 512 % 512) * 512 + σ x % 512)).toNat = _
  rw [hx]
  have c1 : (262144 : Val).toNat = 262144 := rfl
  have c2 : (512 : Val).toNat = 512 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod, BitVec.toNat_ofNat, c1, c2]
  omega

theorem match_store {eb : Nat} {d : VData} {b : Region} {g : Nat} {v : Val} {e' : EPT} (hM : MatchE eb d b)
    (hg : g < NPG) (hs : ept_store d.ept g v = some e') : MatchE eb { d with ept := e' } (setCell b (eb + g) v) := by
  intro g' h hg' hl
  have hl' : ept_leaf e' g' = some h := hl
  rw [store_leaf hg hs hg'] at hl'
  by_cases e : g' = g
  · subst e; rw [if_pos rfl] at hl'; cases hl'; exact sc_eq _ _ _
  · rw [if_neg e] at hl'; rw [sc_ne _ _ (by omega)]; exact hM g' h hg' hl'

section Code
variable {eb maxpage : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "ME" => MatchE eb

theorem get_leaf {gpa : Nat} {d : VData} {h : Val} (hmp : maxpage ≤ NPG)
    (hs : ept_get_page_entry_spec maxpage gpa d = some h) : gpa < NPG ∧ ept_leaf d.ept gpa = some h := by
  unfold ept_get_page_entry_spec at hs
  by_cases hc : flags d ∧ gpa < maxpage
  · rw [if_pos hc] at hs; exact ⟨by omega, hs⟩
  · rw [if_neg hc] at hs; cases hs

/-- Reading the entry of a guest page that has one. -/
theorem load_step (heb : eb + NPG ≤ 2 ^ 32) (x : Ident) (hx : x ≠ "lk") {σ : Locals} {d : VData} {g : Nat}
    {h : Val} (hg : g < NPG) (hσ : σ "gpa" = BitVec.ofNat 32 g) (hl : ept_leaf d.ept g = some h) :
    Step εR c i0 ME F (.call x .pull [lkE, addrE eb "gpa"]) σ d (σ.set x h) d := by
  refine ⟨Locals.set_other _ _ (Ne.symm hx), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk x (addrE eb "gpa") (eval_addr heb hg hσ)
  rw [hM g h hg hl] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

/-- Writing the entry of a guest page whose upper levels exist. -/
theorem store_step (heb : eb + NPG ≤ 2 ^ 32) (hF : ∀ k, eb ≤ k → k < eb + NPG → F k) {ve : Expr} {σ : Locals}
    {d : VData} {g : Nat} {v : Val} {e' : EPT} (hg : g < NPG) (hσ : σ "gpa" = BitVec.ofNat 32 g)
    (hv : ve.eval σ = v) (hs : ept_store d.ept g v = some e') :
    Step εR c i0 ME F (.call "_" .push [lkE, addrE eb "gpa", ve]) σ d (σ.set "_" 0) { d with ept := e' } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (addrE eb "gpa") ve (eval_addr heb hg hσ) hv
  exact ⟨l', _, hr, hcs', match_store hM hg hs,
    fun k hk => sc_ne _ _ (fun e => hk (hF k (by omega) (by unfold NPG at *; omega)))⟩

/-! ### The functions -/

/-- `r = ept_get_page_entry(gpa)` -/
def getPageEntryS (eb : Nat) : Stmt APrim := .call "r" .pull [lkE, addrE eb "gpa"]

theorem getPageEntry_step (heb : eb + NPG ≤ 2 ^ 32) (hmp : maxpage ≤ NPG) {σ : Locals} {d : VData} {gpa : Nat}
    {h : Val} (hσ : σ "gpa" = BitVec.ofNat 32 gpa) (hs : ept_get_page_entry_spec maxpage gpa d = some h) :
    Step εR c i0 ME F (getPageEntryS eb) σ d (σ.set "r" h) d := by
  obtain ⟨hg, hl⟩ := get_leaf hmp hs
  exact load_step εR c i0 heb "r" (by decide) hg hσ hl

/-- `ept_set_page_entry(gpa, hpa)` -/
def setPageEntryS (eb : Nat) : Stmt APrim := .call "_" .push [lkE, addrE eb "gpa", .var "hpa"]

theorem set_store {gpa : Nat} {hpa : Val} {d d' : VData} (hmp : maxpage ≤ NPG)
    (hs : ept_set_page_entry_spec maxpage gpa hpa d = some d') :
    gpa < NPG ∧ ∃ e', ept_store d.ept gpa hpa = some e' ∧ d' = { d with ept := e' } := by
  unfold ept_set_page_entry_spec at hs
  by_cases hc : flags d ∧ gpa < maxpage ∧ hpa.toNat < maxpage
  · rw [if_pos hc] at hs
    cases he : ept_store d.ept gpa hpa with
    | none => rw [he] at hs; cases hs
    | some e' =>
      rw [he] at hs; simp only [Option.some.injEq] at hs
      exact ⟨by omega, e', rfl, hs.symm⟩
  · rw [if_neg hc] at hs; cases hs

theorem setPageEntry_step (heb : eb + NPG ≤ 2 ^ 32) (hmp : maxpage ≤ NPG) (hF : ∀ k, eb ≤ k → k < eb + NPG → F k)
    {σ : Locals} {d d' : VData} {gpa : Nat} {hpa : Val} (hσ : σ "gpa" = BitVec.ofNat 32 gpa) (hh : σ "hpa" = hpa)
    (hs : ept_set_page_entry_spec maxpage gpa hpa d = some d') :
    Step εR c i0 ME F (setPageEntryS eb) σ d (σ.set "_" 0) d' := by
  obtain ⟨hg, e', he, rfl⟩ := set_store hmp hs
  exact store_step εR c i0 heb hF hg hσ hh he

/-- `ept_add_mapping(gpa, hpa, mem_type)`:
`ept.ptab[...] = (hpa & EPT_ADDR_MASK) | 71 | (mem_type << 3); r = 0;` -/
def vaE : Expr :=
  .bin .bor (.bin .bor (.bin .band (.var "hpa") (.const EPT_ADDR_MASK)) (.const 71))
    (.bin .shl (.var "memtype") (.const 3))

def addMappingS (eb : Nat) : Stmt APrim :=
  .seq (.call "_" .push [lkE, addrE eb "gpa", vaE]) (.assign "r" (.const 0))

theorem addMapping_step (heb : eb + NPG ≤ 2 ^ 32) (hmp : maxpage ≤ NPG) (hF : ∀ k, eb ≤ k → k < eb + NPG → F k)
    {σ : Locals} {d d' : VData} {gpa hpa memtype r : Nat} (hσ : σ "gpa" = BitVec.ofNat 32 gpa)
    (hh : σ "hpa" = BitVec.ofNat 32 hpa) (hm : σ "memtype" = BitVec.ofNat 32 memtype)
    (hs : ept_add_mapping_spec maxpage gpa hpa memtype d = some (d', r)) :
    Step εR c i0 ME F (addMappingS eb) σ d ((σ.set "_" 0).set "r" 0) d' ∧ r = 0 := by
  unfold ept_add_mapping_spec at hs
  by_cases hc : flags d ∧ gpa < maxpage ∧ hpa < maxpage ∧ memtype < 4096
  · rw [if_pos hc] at hs
    cases he : ept_store d.ept gpa (mapVal hpa memtype) with
    | none => rw [he] at hs; cases hs
    | some e' =>
      rw [he] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨Step.seq (store_step εR c i0 heb hF (by omega) hσ (by simp [vaE, Expr.eval, BinOp.eval, hh, hm, mapVal]) he)
        (Step.assign "r" (by decide) (.const 0)), rfl⟩
  · rw [if_neg hc] at hs; cases hs

/-- `ept_invalidate_mappings()`: `invept` is a hardware TLB flush. -/
def invalidateS : Stmt APrim := .assign "r" (.const 0)

theorem invalidate_step {σ : Locals} {d : VData} {r : Nat} (hs : ept_invalidate_mappings_spec d = some r) :
    Step εR c i0 ME F invalidateS σ d (σ.set "r" 0) d ∧ r = 0 := by
  unfold ept_invalidate_mappings_spec at hs
  split at hs
  · cases hs; exact ⟨Step.assign "r" (by decide) (.const 0), rfl⟩
  · cases hs

/-- `if ((e & 7) == 0)` -/
def permTestE : Expr := .bin .eq (.bin .band (.var "e") (.const 7)) (.const 0)

/-- `ept_gpa_to_hpa(gpa)`: `e = ept_get_page_entry(gpa); if (!(e & 7)) r = 0;
else r = (e & EPT_ADDR_MASK) | (gpa & EPT_ADDR_OFFSET_MASK);` -/
def gpaToHpaS (eb : Nat) : Stmt APrim :=
  .seq (.call "e" .pull [lkE, addrE eb "gpa"])
    (.ite permTestE (.assign "r" (.const 0))
      (.assign "r" (.bin .bor (.bin .band (.var "e") (.const EPT_ADDR_MASK)) (.bin .band (.var "gpa") (.const 4095)))))

theorem gpaToHpa_step (heb : eb + NPG ≤ 2 ^ 32) (hmp : maxpage ≤ NPG) {σ : Locals} {d : VData} {gpa : Nat}
    {r : Val} (hσ : σ "gpa" = BitVec.ofNat 32 gpa) (hs : ept_gpa_to_hpa_spec maxpage gpa d = some r) :
    ∃ σ', Step εR c i0 ME F (gpaToHpaS eb) σ d σ' d ∧ σ' "r" = r := by
  unfold ept_gpa_to_hpa_spec at hs
  cases hg : ept_get_page_entry_spec maxpage gpa d with
  | none => rw [hg] at hs; cases hs
  | some e =>
    rw [hg] at hs; simp only at hs
    obtain ⟨hgn, hl⟩ := get_leaf hmp hg
    have L := load_step (F := F) εR c i0 heb "e" (by decide) hgn hσ hl
    have he : (σ.set "e" e) "e" = e := by simp
    have hgp : (σ.set "e" e) "gpa" = BitVec.ofNat 32 gpa := by simp [Locals.set, hσ]
    by_cases t : e &&& 7 = 0
    · rw [if_pos t] at hs; cases hs
      refine ⟨_, L.seq (Step.ite_true (by simpa [permTestE, Expr.eval, BinOp.eval, he] using t)
        (Step.assign "r" (by decide) (.const 0))), by simp [Expr.eval]⟩
    · rw [if_neg t] at hs; cases hs
      refine ⟨_, L.seq (Step.ite_false (by simpa [permTestE, Expr.eval, BinOp.eval, he] using t)
        (Step.assign "r" (by decide) _)), by simp [Expr.eval, BinOp.eval, he, hgp, hσ]⟩

/-- `ept_mmap(gpa, hpa, mem_type)`: `e = ept_get_page_entry(gpa);
if (e & 7) r = 1; else r = ept_add_mapping(gpa, hpa, mem_type);` -/
def mmapS (eb : Nat) : Stmt APrim :=
  .seq (.call "e" .pull [lkE, addrE eb "gpa"]) (.ite permTestE (addMappingS eb) (.assign "r" (.const 1)))

theorem mmap_step (heb : eb + NPG ≤ 2 ^ 32) (hmp : maxpage ≤ NPG) (hF : ∀ k, eb ≤ k → k < eb + NPG → F k)
    {σ : Locals} {d d' : VData} {gpa hpa memtype r : Nat} (hσ : σ "gpa" = BitVec.ofNat 32 gpa)
    (hh : σ "hpa" = BitVec.ofNat 32 hpa) (hm : σ "memtype" = BitVec.ofNat 32 memtype)
    (hs : ept_mmap_spec maxpage gpa hpa memtype d = some (d', r)) (hr : r < 2 ^ 32) :
    ∃ σ', Step εR c i0 ME F (mmapS eb) σ d σ' d' ∧ σ' "r" = BitVec.ofNat 32 r := by
  unfold ept_mmap_spec at hs
  cases hg : ept_get_page_entry_spec maxpage gpa d with
  | none => rw [hg] at hs; cases hs
  | some e =>
    rw [hg] at hs; simp only at hs
    obtain ⟨hgn, hl⟩ := get_leaf hmp hg
    have L := load_step (F := F) εR c i0 heb "e" (by decide) hgn hσ hl
    have he : (σ.set "e" e) "e" = e := by simp
    by_cases hmt : memtype < 4096
    · rw [if_pos hmt] at hs
      by_cases t : e &&& 7 = 0
      · rw [if_pos t] at hs
        obtain ⟨A, rfl⟩ := addMapping_step εR c i0 heb hmp hF (σ := σ.set "e" e)
          (by simp [Locals.set, hσ]) (by simp [Locals.set, hh]) (by simp [Locals.set, hm]) hs
        exact ⟨_, L.seq (Step.ite_true (by simpa [permTestE, Expr.eval, BinOp.eval, he] using t) A), by simp⟩
      · rw [if_neg t] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, rfl⟩ := hs
        exact ⟨_, L.seq (Step.ite_false (by simpa [permTestE, Expr.eval, BinOp.eval, he] using t)
          (Step.assign "r" (by decide) (.const 1))), by simp [Expr.eval]⟩
    · rw [if_neg hmt] at hs; cases hs

/-- `ept_set_permission(gpa, perm)`: `e = ept_get_page_entry(gpa);
ept_set_page_entry(gpa, (e & ~7) | (perm & 7));` -/
def setPermissionS (eb : Nat) : Stmt APrim :=
  .seq (.call "e" .pull [lkE, addrE eb "gpa"])
    (.call "_" .push [lkE, addrE eb "gpa",
      .bin .bor (.bin .band (.var "e") (.const EPT_NO_PERM)) (.bin .band (.var "perm") (.const 7))])

theorem setPermission_step (heb : eb + NPG ≤ 2 ^ 32) (hmp : maxpage ≤ NPG) (hF : ∀ k, eb ≤ k → k < eb + NPG → F k)
    {σ : Locals} {d d' : VData} {gpa perm : Nat} (hσ : σ "gpa" = BitVec.ofNat 32 gpa)
    (hp : σ "perm" = BitVec.ofNat 32 perm) (hs : ept_set_permission_spec maxpage gpa perm d = some d') :
    ∃ σ', Step εR c i0 ME F (setPermissionS eb) σ d σ' d' := by
  unfold ept_set_permission_spec at hs
  cases hg : ept_get_page_entry_spec maxpage gpa d with
  | none => rw [hg] at hs; cases hs
  | some e =>
    rw [hg] at hs; simp only at hs
    obtain ⟨hgn, hl⟩ := get_leaf hmp hg
    have L := load_step (F := F) εR c i0 heb "e" (by decide) hgn hσ hl
    obtain ⟨-, e', he', rfl⟩ := set_store hmp hs
    exact ⟨_, L.seq (store_step εR c i0 heb hF hgn (by simp [Locals.set, hσ])
      (by simp [Expr.eval, BinOp.eval, Locals.set, hp]) he')⟩

/-! ### `ept_init`: every guest page gets the entry 0 -/

/-- `i = 0; while (i < NPG) { ept.ptab[i] = 0; i++; }` -/
def eptInitS (eb : Nat) : Stmt APrim :=
  .seq (.assign "i" (.const 0))
    (.while (.bin .ltu (.var "i") (.const (BitVec.ofNat 32 NPG)))
      (.seq (.call "_" .push [lkE, .bin .add (.const (BitVec.ofNat 32 eb)) (.var "i"), .const 0])
        (.assign "i" (.bin .add (.var "i") (.const 1)))))

/-- The region during the loop: the first `n` entries are 0. -/
def Zeroed (eb : Nat) (n : Nat) (d : VData) (b : Region) : Prop := ∀ g, g < n → b (eb + g) = 0

theorem eptInit_step (heb : eb + NPG ≤ 2 ^ 32) (hF : ∀ k, eb ≤ k → k < eb + NPG → F k) (σ : Locals) (d : VData)
    (hfl : flags d) :
    ∃ σ', Step εR c i0 (fun (p : Nat × VData) b => Zeroed eb p.1 p.2 b) F (eptInitS eb) σ (0, d) σ' (NPG, d) := by
  have hn : NPG < 2 ^ 32 := by unfold NPG; omega
  let I : Locals → Nat × VData → Prop := fun τ p => p.2 = d ∧ p.1 ≤ NPG ∧ τ "i" = BitVec.ofNat 32 p.1
  have hbody : ∀ τ p, I τ p → ¬ (Expr.bin .ltu (.var "i") (.const (BitVec.ofNat 32 NPG))).eval τ = 0 →
      ∃ τ' p', Step εR c i0 (fun (p : Nat × VData) b => Zeroed eb p.1 p.2 b) F
        (.seq (.call "_" .push [lkE, .bin .add (.const (BitVec.ofNat 32 eb)) (.var "i"), .const 0])
          (.assign "i" (.bin .add (.var "i") (.const 1)))) τ p τ' p' ∧ I τ' p' ∧
        NPG - (τ' "i").toNat < NPG - (τ "i").toNat := by
    rintro τ ⟨m, d0⟩ ⟨rfl, hm, hiτ⟩ hg
    rw [ltu_eval (σ := τ) (ea := .var "i") (eb := .const (BitVec.ofNat 32 NPG)) hiτ rfl (by omega) hn] at hg
    have hmlt : m < NPG := by
      by_cases h : m < NPG
      · exact h
      · rw [if_neg h] at hg; exact absurd rfl hg
    have st : Step εR c i0 (fun (p : Nat × VData) b => Zeroed eb p.1 p.2 b) F
        (.call "_" .push [lkE, .bin .add (.const (BitVec.ofNat 32 eb)) (.var "i"), .const 0]) τ (m, d0)
        (τ.set "_" 0) (m + 1, d0) := by
      refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
      obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (.bin .add (.const (BitVec.ofNat 32 eb)) (.var "i"))
        (.const 0) (n := eb + m) (v := 0) (by
          show (BitVec.ofNat 32 eb + τ "i").toNat = _
          rw [hiτ, BitVec.toNat_add, tn (by omega), tn (by omega)]; omega) rfl
      refine ⟨l', _, hr, hcs', fun g hg' => ?_, fun k hk => sc_ne _ _ (fun e => hk (hF k (by omega) (by omega)))⟩
      by_cases e : g = m
      · subst e; exact sc_eq _ _ _
      · rw [sc_ne _ _ (by omega)]; exact hM g (by omega)
    refine ⟨_, (m + 1, d0), st.seq (Step.assign' "i" (by decide) _ (inc_eval (m := m)
      (by rw [Locals.set_other _ _ (by decide)]; exact hiτ))), ⟨rfl, hmlt, by simp⟩, ?_⟩
    rw [Locals.set_same, hiτ, tn (show m + 1 < 2 ^ 32 by omega), tn (show m < 2 ^ 32 by omega)]; omega
  obtain ⟨σ', ⟨n', d'⟩, hr, ⟨hd, hm, hi'⟩, h0⟩ :=
    Step.while_inv (εR := εR) (c := c) (i := i0) (M := fun (p : Nat × VData) b => Zeroed eb p.1 p.2 b) (F := F) I
      (fun τ => NPG - (τ "i").toNat) hbody NPG (σ.set "i" 0) (0, d) (by omega) ⟨rfl, by omega, by simp⟩
  simp only at hd hm hi'
  rw [ltu_eval (σ := σ') (ea := .var "i") (eb := .const (BitVec.ofNat 32 NPG)) hi' rfl (by omega) hn] at h0
  have hme : n' = NPG := by
    by_cases h : n' < NPG
    · rw [if_pos h] at h0; cases h0
    · omega
  subst hme; subst hd
  exact ⟨σ', (Step.assign "i" (by decide) (.const 0)).seq hr⟩

/-- **The loop of `ept_init` refines `ept_init0_spec`**: afterwards the region
matches the EPT in which every guest page has the entry 0. -/
theorem eptInit_match {d d' : VData} {b : Region} (hz : Zeroed eb NPG d b)
    (hs : ept_init0_spec d = some d') : ME d' b := by
  unfold ept_init0_spec at hs
  split at hs
  · cases hs
    intro g v hg hl
    have hl' : ept_leaf (real_ept d.ept) g = some v := hl
    rw [real_leaf _ hg] at hl'; cases hl'
    exact hz g hg
  · cases hs

end Code

end VEPT
