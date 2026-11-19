import CertiKOS.MPTIntro

/-!
# mCertiKOS `MPTOp`: page-table operations by virtual address, ported

The primitives that mCertiKOS builds on the page-table accessors
(`mcertikos/mm/MPTIntroCSource.v`): they split a virtual address into its
directory index `PDX` and table index `PTX`, and call one accessor.

Ported from `objects/ObjVMMFun.v` and `ObjVMMGetSet.v`: `ptRead_spec`,
`ptReadPDE_spec`, `ptRmvAux_spec`, `ptRmvPDE_spec`, `ptInsertAux_spec`,
`ptInsertPDE_spec`.

Ported from `mm/MPTIntroCSource.v`: `pt_read`, `pt_read_pde`, `pt_rmv_aux`,
`pt_rmv_pde`, `pt_insert_aux`, `pt_insert_pde`.

Each is verified against the triple of the accessor it calls
(`MPTIntro.getPTE_triple` and the others), not against the accessor's code.

Not ported: `idpde_init` (boot, stage 2).
-/

namespace MPTOp

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro

/-- `PDX`: the directory index of a virtual address. -/
def PDX (v : Nat) : Nat := v / (4096 * 1024)

/-- `PTX`: the table index of a virtual address. -/
def PTX (v : Nat) : Nat := (v / 4096) % 1024

/-! ## Specifications -/

section Specs
variable (num_proc : Nat)

def ptRead_spec (n vadr : Nat) (d : PTData) : Option Nat := getPTE_spec num_proc n (PDX vadr) (PTX vadr) d

def ptReadPDE_spec (n vadr : Nat) (d : PTData) : Option Nat := getPDE_spec num_proc n (PDX vadr) d

def ptRmvAux_spec (n vadr : Nat) (d : PTData) : Option PTData := rmvPTE_spec num_proc n (PDX vadr) (PTX vadr) d

def ptRmvPDE_spec (n vadr : Nat) (d : PTData) : Option PTData := rmvPDE_spec num_proc n (PDX vadr) d

def ptInsertAux_spec (n vadr padr perm : Nat) (d : PTData) : Option PTData :=
  setPTE_spec num_proc n (PDX vadr) (PTX vadr) padr perm d

def ptInsertPDE_spec (n vadr pi : Nat) (d : PTData) : Option PTData :=
  setPDEU_spec num_proc n (PDX vadr) pi d

end Specs

/-! ## The C code -/

/-- `vaddr / (4096 * 1024)` -/
def pdxE : Expr := .bin .div (.var "vaddr") (.const 4194304)

/-- `(vaddr / 4096) % 1024` -/
def ptxE : Expr := .bin .mod (.bin .div (.var "vaddr") (.const 4096)) (.const 1024)

/-- `pdx_index = vaddr / (4096 * 1024); s` -/
def withPDX (s : Stmt APrim) : Stmt APrim := .seq (.assign "i" pdxE) s

/-- `pdx_index = vaddr / (4096 * 1024); vaddrl = (vaddr / 4096) % 1024; s` -/
def withPDXPTX (s : Stmt APrim) : Stmt APrim := .seq (.assign "i" pdxE) (.seq (.assign "vadr" ptxE) s)

/-- `pt_read(n, vaddr)` -/
def ptReadS (pb fb : Nat) : Stmt APrim := withPDXPTX (getPTES pb fb)
/-- `pt_read_pde(n, vaddr)` -/
def ptReadPDES (pb : Nat) : Stmt APrim := withPDX (getPDES pb)
/-- `pt_rmv_aux(n, vaddr)` -/
def ptRmvAuxS (pb fb : Nat) : Stmt APrim := withPDXPTX (rmvPTES pb fb)
/-- `pt_rmv_pde(n, vaddr)` -/
def ptRmvPDES (pb : Nat) : Stmt APrim := withPDX (rmvPDES pb)
/-- `pt_insert_aux(n, vaddr, padr, perm)` -/
def ptInsertAuxS (pb fb : Nat) : Stmt APrim := withPDXPTX (setPTES pb fb)
/-- `pt_insert_pde(n, vaddr, pi)` -/
def ptInsertPDES (pb : Nat) : Stmt APrim := withPDX (setPDEUS pb)

theorem pdx_eval {σ : Locals} {v : Nat} (h : σ "vaddr" = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    pdxE.eval σ = BitVec.ofNat 32 (PDX v) := by
  show σ "vaddr" / 4194304 = _
  rw [h]
  refine val_of_toNat ?_ (by unfold PDX; omega)
  rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; rfl

theorem ptx_eval {σ : Locals} {v : Nat} (h : σ "vaddr" = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    ptxE.eval σ = BitVec.ofNat 32 (PTX v) := by
  show σ "vaddr" / 4096 % 1024 = _
  rw [h]
  refine val_of_toNat ?_ (by unfold PTX; omega)
  rw [BitVec.toNat_umod, BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]; rfl

/-- The locals after both index computations. -/
theorem idx2 {σ : Locals} {v : Nat} (h : σ "vaddr" = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    ((σ.set "i" (pdxE.eval σ)).set "vadr" (ptxE.eval (σ.set "i" (pdxE.eval σ)))) "i" = BitVec.ofNat 32 (PDX v) ∧
    ((σ.set "i" (pdxE.eval σ)).set "vadr" (ptxE.eval (σ.set "i" (pdxE.eval σ)))) "vadr" = BitVec.ofNat 32 (PTX v) ∧
    ∀ z, z ≠ "i" → z ≠ "vadr" →
      ((σ.set "i" (pdxE.eval σ)).set "vadr" (ptxE.eval (σ.set "i" (pdxE.eval σ)))) z = σ z := by
  refine ⟨?_, ?_, fun z h1 h2 => ?_⟩
  · rw [Locals.set_other _ _ (by decide), Locals.set_same]; exact pdx_eval h hv
  · rw [Locals.set_same]
    exact ptx_eval (by rw [Locals.set_other _ _ (by decide)]; exact h) hv
  · rw [Locals.set_other _ _ h2, Locals.set_other _ _ h1]

theorem idx1 {σ : Locals} {v : Nat} (h : σ "vaddr" = BitVec.ofNat 32 v) (hv : v < 2 ^ 32) :
    (σ.set "i" (pdxE.eval σ)) "i" = BitVec.ofNat 32 (PDX v) ∧
    ∀ z, z ≠ "i" → (σ.set "i" (pdxE.eval σ)) z = σ z :=
  ⟨by rw [Locals.set_same]; exact pdx_eval h hv, fun z h1 => Locals.set_other _ _ h1⟩

/-! ## Each operation refines its specification -/

section Ops
variable {maxpage num_id cb num_proc pb ib fb ida : Nat}

/-- **`pt_read` refines `ptRead_spec`.** -/
theorem ptRead_triple (εR : REnv) (c : CPU) (i0 : Nat) (hpb : pb + num_proc * 1024 < 2 ^ 32)
    (hfb : fb + 2 ^ 30 ≤ 2 ^ 32) (n vadr : Nat) (hv : vadr < 2 ^ 32) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun _ => False)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        ∃ v, ptRead_spec num_proc n vadr d = some v)
      (ptReadS pb fb)
      (fun _ d σ' d' => d' = d ∧ ∃ v, ptRead_spec num_proc n vadr d = some v ∧ σ' "r" = BitVec.ofNat 32 v) :=
  (((getPTE_triple εR c i0 hpb hfb n (PDX vadr) (PTX vadr)).assign_pre "vadr" (by decide) ptxE).assign_pre
    "i" (by decide) pdxE).conseq
    (fun σ d ⟨hn, hva, v, hs⟩ => by
      obtain ⟨h1, h2, h3⟩ := idx2 hva hv
      exact ⟨by rw [h3 _ (by decide) (by decide)]; exact hn, h1, h2, v, hs⟩)
    (fun _ _ _ _ _ h => h)

/-- **`pt_read_pde` refines `ptReadPDE_spec`.** -/
theorem ptReadPDE_triple (εR : REnv) (c : CPU) (i0 : Nat) (hpb : pb + num_proc * 1024 < 2 ^ 32)
    (n vadr : Nat) (hv : vadr < 2 ^ 32) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun _ => False)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        ∃ v, ptReadPDE_spec num_proc n vadr d = some v)
      (ptReadPDES pb)
      (fun _ d σ' d' => d' = d ∧ ∃ v, ptReadPDE_spec num_proc n vadr d = some v ∧
        σ' "r" = BitVec.ofNat 32 v) :=
  ((getPDE_triple εR c i0 hpb n (PDX vadr)).assign_pre "i" (by decide) pdxE).conseq
    (fun σ d ⟨hn, hva, v, hs⟩ => by
      obtain ⟨h1, h3⟩ := idx1 hva hv
      exact ⟨by rw [h3 _ (by decide)]; exact hn, h1, v, hs⟩)
    (fun _ _ _ _ _ h => h)

/-- **`pt_rmv_aux` refines `ptRmvAux_spec`.** -/
theorem ptRmvAux_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (n vadr : Nat) (hv : vadr < 2 ^ 32) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        ∃ d1, ptRmvAux_spec num_proc n vadr d = some d1)
      (ptRmvAuxS pb fb)
      (fun _ d _ d' => ptRmvAux_spec num_proc n vadr d = some d') :=
  (((rmvPTE_triple εR c i0 hL n (PDX vadr) (PTX vadr)).assign_pre "vadr" (by decide) ptxE).assign_pre
    "i" (by decide) pdxE).conseq
    (fun σ d ⟨hn, hva, d1, hs⟩ => by
      obtain ⟨h1, h2, h3⟩ := idx2 hva hv
      exact ⟨by rw [h3 _ (by decide) (by decide)]; exact hn, h1, h2, d1, hs⟩)
    (fun _ _ _ _ _ h => h)

/-- **`pt_rmv_pde` refines `ptRmvPDE_spec`.** -/
theorem ptRmvPDE_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (n vadr : Nat) (hv : vadr < 2 ^ 32) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        ∃ d1, ptRmvPDE_spec num_proc n vadr d = some d1)
      (ptRmvPDES pb)
      (fun _ d _ d' => ptRmvPDE_spec num_proc n vadr d = some d') :=
  ((rmvPDE_triple εR c i0 hL n (PDX vadr)).assign_pre "i" (by decide) pdxE).conseq
    (fun σ d ⟨hn, hva, d1, hs⟩ => by
      obtain ⟨h1, h3⟩ := idx1 hva hv
      exact ⟨by rw [h3 _ (by decide)]; exact hn, h1, d1, hs⟩)
    (fun _ _ _ _ _ h => h)

/-- **`pt_insert_aux` refines `ptInsertAux_spec`.** -/
theorem ptInsertAux_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (n vadr padr perm : Nat) (hv : vadr < 2 ^ 32) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        σ "padr" = BitVec.ofNat 32 padr ∧ σ "perm" = BitVec.ofNat 32 perm ∧ d.nps ≤ 2 ^ 20 ∧
        ∃ d1, ptInsertAux_spec num_proc n vadr padr perm d = some d1)
      (ptInsertAuxS pb fb)
      (fun _ d _ d' => ptInsertAux_spec num_proc n vadr padr perm d = some d') :=
  (((setPTE_triple εR c i0 hL n (PDX vadr) (PTX vadr) padr perm).assign_pre "vadr" (by decide) ptxE).assign_pre
    "i" (by decide) pdxE).conseq
    (fun σ d ⟨hn, hva, hpa, hpe, hnps, d1, hs⟩ => by
      obtain ⟨h1, h2, h3⟩ := idx2 hva hv
      exact ⟨by rw [h3 _ (by decide) (by decide)]; exact hn, h1, h2,
        by rw [h3 _ (by decide) (by decide)]; exact hpa, by rw [h3 _ (by decide) (by decide)]; exact hpe,
        hnps, d1, hs⟩)
    (fun _ _ _ _ _ h => h)

/-- **`pt_insert_pde` refines `ptInsertPDE_spec`.** -/
theorem ptInsertPDE_triple (εR : REnv) (c : CPU) (i0 : Nat) (hL : Layout maxpage num_id cb num_proc pb ib fb)
    (n vadr pi : Nat) (hv : vadr < 2 ^ 32) :
    Triple εR c i0 (MatchAll maxpage num_id cb num_proc pb ib fb ida) (fun k => pb ≤ k)
      (fun σ d => σ "n" = BitVec.ofNat 32 n ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        σ "pi" = BitVec.ofNat 32 pi ∧ d.nps ≤ 2 ^ 20 ∧
        ∃ d1, ptInsertPDE_spec num_proc n vadr pi d = some d1)
      (ptInsertPDES pb)
      (fun _ d _ d' => ptInsertPDE_spec num_proc n vadr pi d = some d') :=
  ((setPDEU_triple εR c i0 hL n (PDX vadr) pi).assign_pre "i" (by decide) pdxE).conseq
    (fun σ d ⟨hn, hva, hpi, hnps, d1, hs⟩ => by
      obtain ⟨h1, h3⟩ := idx1 hva hv
      exact ⟨by rw [h3 _ (by decide)]; exact hn, h1, by rw [h3 _ (by decide)]; exact hpi, hnps, d1, hs⟩)
    (fun _ _ _ _ _ h => h)

end Ops

end MPTOp
