import CertiKOS.THyp2

/-!
# `SYS_hvm_mmap`: mapping a page of the caller into the guest

Ported from `objects/ObjTrap.v` (`trap_mmap_spec`, with the C quoted there
and in `trap/sys_mmap.c`). The guest page `gpa` is mapped to the host page
behind the caller's address `hva`; if the caller has no page there yet, one
is reserved first (`pt_resv`).

* `trap_mmap_spec`: mCertiKOS's specification on the top state. The address
  arithmetic is on machine words.
* `readU`, `resvU`: `pt_read` and `pt_resv`, verified in the page-table
  layers, carried up to the top state (`liftPC`, `liftPC'`, `liftCI`,
  `liftIU`, `liftUT`).
* `mmap_triple`: **`sys_hvm_mmap` refines `trap_mmap_spec`.**

What differs from the C: ClightL has no `||` or `&&`, so the address checks
are nested tests; `hva % PAGESIZE` is `hva & 4095`. `pt_read` and `pt_resv`
are verified with their locals unspecified except their result, so after
them the handler reads `gpa` and `mem_type` again from the caller's
registers (they are unchanged there).
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace TTop

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MContainer MPTIntro MPTOp MPTCommon MPTKern MPTNew MShare PThread PQueue PAbQueue PCurID PSched PIPC
open KMach PKCtx PUCtxt UMach MCPU PProc FlatMem TTrap
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)
open VVMX (XSt MatchX XF)

def E_INVAL_ADDR : Nat := 4
def ADDR_MASK : Val := 4294963200

/-- The host address: `(hpa & 0xfffff000) + (hva % PAGESIZE)`. -/
def hostAddr (hpa hva : Nat) : Val := (BitVec.ofNat 32 hpa &&& ADDR_MASK) + (BitVec.ofNat 32 hva &&& 4095)

def mmapTail (maxpage gpa hva hpa mt : Nat) (d : HData) : Option HData :=
  hcall (match VVMX.vmx_set_mmap_spec maxpage gpa (hostAddr hpa hva).toNat mt (toX d) with
    | some (x, _) => some (x, [(U_EAX, 0)])
    | none => none) d

/-- **`trap_mmap_spec`.** -/
def trap_mmap_spec (num_proc maxpage : Nat) (d : HData) : Option HData :=
  match uctx_arg2_spec d.toUData, uctx_arg3_spec d.toUData, uctx_arg4_spec d.toUData with
  | some gpa, some hva, some mt =>
    if hva % 4096 = 0 ∧ gpa % 4096 = 0 ∧ 1073741824 ≤ hva ∧ hva + 4096 ≤ 4026531840 then
      match ptRead_spec num_proc d.cid hva d.toPTData with
      | some hpa =>
        if (BitVec.ofNat 32 hpa &&& 1) = 0 then
          match ptResv_spec maxpage num_proc d.cid hva 7 d.toPTData with
          | some (p0, _) =>
            match ptRead_spec num_proc d.cid hva p0 with
            | some hpa' => mmapTail maxpage gpa hva hpa' mt { d with toPTData := p0 }
            | none => none
          | none => none
        else mmapTail maxpage gpa hva hpa mt d
      | none => none
    else hcall (some (toX d, [(U_EAX, E_INVAL_ADDR)])) d
  | _, _, _ => none

/-! ## The code -/

def andE (x : Ident) (m : Nat) : Expr := .bin .band (.var x) (.const (BitVec.ofNat 32 m))

/-- `n = curid; vaddr = hva; pt_read(n, vaddr)` -/
def readS (pb fb : Nat) : Stmt APrim := .seq (.assign "n" (.var "curid")) (.seq (.assign "vaddr" (.var "hva")) (ptReadS pb fb))

/-- `pt_resv(curid, hva, PTE_P | PTE_U | PTE_W); hpa = pt_read(curid, hva);` -/
def resvS (cb maxpage pb fb : Nat) : Stmt APrim :=
  .seq (.assign "n" (.var "curid")) (.seq (.assign "vaddr" (.var "hva")) (.seq (.assign "perm" (.const 7))
    (.seq (ptResvS cb maxpage pb fb) (readS pb fb))))

/-- `hpa = (hpa & 0xfffff000) + (hva % PAGESIZE); vmx_set_mmap(gpa, hpa, mem_type); uctx_set_errno(E_SUCC);` -/
def tailS (cidb ucb eb : Nat) : Stmt APrim :=
  .seq (.assign "hpa" (.bin .add (.bin .band (.var "r") (.const ADDR_MASK)) (andE "hva" 4095)))
    (.seq (uctxArgS cidb ucb "gpa" U_EBX) (.seq (uctxArgS cidb ucb "memtype" U_EDX)
      (.seq (VVMX.setMmapS eb) (errS cidb ucb 0))))

def bodyS (cb maxpage pb fb cidb ucb eb : Nat) : Stmt APrim :=
  .seq (readS pb fb)
    (.seq (.ite (.bin .eq (andE "r" 1) (.const 0)) (resvS cb maxpage pb fb) .skip) (tailS cidb ucb eb))

/-- `sys_hvm_mmap`. -/
def mmapH (cb maxpage pb fb cidb ucb eb : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "gpa" U_EBX) (.seq (uctxArgS cidb ucb "hva" U_ECX) (.seq (uctxArgS cidb ucb "memtype" U_EDX)
    (.ite (.bin .eq (andE "hva" 4095) (.const 0))
      (.ite (.bin .eq (andE "gpa" 4095) (.const 0))
        (.ite (.bin .ltu (.var "hva") (.const 1073741824)) (errS cidb ucb E_INVAL_ADDR)
          (.ite (.bin .ltu (.var "hva") (.const 4026527745)) (bodyS cb maxpage pb fb cidb ucb eb)
            (errS cidb ucb E_INVAL_ADDR)))
        (errS cidb ucb E_INVAL_ADDR))
      (errS cidb ucb E_INVAL_ADDR))))

theorem band4095 (n : Nat) : ((BitVec.ofNat 32 n : Val) &&& BitVec.ofNat 32 4095).toNat = n % 4096 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (BitVec.ofNat 32 4095 : Val).toNat = 2 ^ 12 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_mod_of_dvd n (by decide)

theorem mask_zero {n : Nat} : ((BitVec.ofNat 32 n : Val) &&& BitVec.ofNat 32 4095) = 0 ↔ n % 4096 = 0 := by
  constructor
  · intro h; have := band4095 n; rw [h] at this; simpa using this.symm
  · intro h; apply BitVec.eq_of_toNat_eq; rw [band4095, h]; rfl

section Code
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- `pt_read` on the top state. -/
theorem readU (hL : HL) (nn vadr : Nat) (hv : vadr < 2 ^ 32) :
    Triple εR c i0 MH (fun _ => False)
      (fun σ d => σ "n" = BitVec.ofNat 32 nn ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
        ∃ v, ptRead_spec num_proc nn vadr d.toPTData = some v)
      (ptReadS pb fb)
      (fun _ d σ' d' => d' = d ∧ ∃ v, ptRead_spec num_proc nn vadr d.toPTData = some v ∧ σ' "r" = BitVec.ofNat 32 v) := by
  have hU := hL.ulay
  have hLay := hU.ilay.clay.qlay.tlay.slay.lay
  have T := liftUT (ida := ida) (ob := ob) (xb := xb) (vb := vb) (eb := eb) εR c i0 hL
    (liftIU εR c i0 hU (liftCI εR c i0 hU.ilay (liftPC εR c i0 hU.ilay.clay
      (ptRead_triple εR c i0 (by have := hLay.hib; have := hLay.hfb; have := hLay.hend; omega) hLay.hend
        nn vadr hv (ida := ida)) (fun _ h => h.elim) (fun _ _ _ _ _ hq => by rw [hq.1])) (fun _ h => h.elim))
      (fun _ h => h.elim)) (fun _ h => h.elim)
  refine T.conseq (fun σ d h => h) (fun σ d σ' d' _ hq => ?_)
  obtain ⟨u, rfl, i1, rfl, c1, rfl, p, rfl, rfl, v, hv', hr⟩ := hq
  exact ⟨rfl, v, hv', hr⟩

/-- `pt_resv` on the top state. -/
theorem resvU (hL : HL) (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32) (hmp : maxpage ≤ 2 ^ 20)
    (hnn : num_proc ≤ num_id) {kl kh : Nat} (nn vadr : Nat) (hnid : nn < num_id) :
    Triple εR c i0 MH (fun k => k < cb + 5 * num_id ∨ pb ≤ k)
      (fun σ d => (σ "n" = BitVec.ofNat 32 nn ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧ σ "perm" = BitVec.ofNat 32 7 ∧
        ATInv maxpage kl kh d.toPData ∧ (d.AC nn).cusage ≤ (d.AC nn).cquota ∧
        ∃ d1 r, ptResv_spec maxpage num_proc nn vadr 7 d.toPTData = some (d1, r)) ∧ d.pg = true)
      (ptResvS cb maxpage pb fb)
      (fun _ d σ' d' => ∃ p r, d' = { d with toPTData := p } ∧ ptResv_spec maxpage num_proc nn vadr 7 d.toPTData = some (p, r)) := by
  have hU := hL.ulay
  have hCL := hU.ilay.clay
  have hLay := hCL.qlay.tlay.slay.lay
  have := hU.hub0; have := hU.hue; have := hU.ilay.hib0; have := hCL.hcb; have := hCL.qlay.hqb
  have := hCL.qlay.tlay.htb; have := hCL.qlay.tlay.slay.hsb; have := hCL.qlay.tlay.slay.hse; have := hL.hob
  have T := liftUT (ida := ida) (ob := ob) (xb := xb) (vb := vb) (eb := eb) εR c i0 hL
    (liftIU εR c i0 hU (liftCI εR c i0 hU.ilay (liftPC' εR c i0 hCL
      ((ptResv_triple εR c i0 hLay hmax hnum hmp hnn (kl := kl) (kh := kh) nn vadr 7 hnid (ida := ida)).conseq
        (P' := fun σ (e : PTData) => (σ "n" = BitVec.ofNat 32 nn ∧ σ "vaddr" = BitVec.ofNat 32 vadr ∧
          σ "perm" = BitVec.ofNat 32 7 ∧ ATInv maxpage kl kh e.toPData ∧ (e.AC nn).cusage ≤ (e.AC nn).cquota ∧
          ∃ d1 r, ptResv_spec maxpage num_proc nn vadr 7 e = some (d1, r)) ∧ e.pg = true)
        (fun _ _ h => h.1) (fun _ _ _ _ _ h => h))
      (fun _ h => h) (fun _ _ _ _ hP _ _ => hP.2)) (fun k hk => by omega)) (fun k hk => by omega))
    (fun k hk => by omega)
  refine T.conseq (fun σ d h => h) (fun σ d σ' d' _ hq => ?_)
  obtain ⟨u, rfl, i1, rfl, c1, rfl, p, rfl, r, hr, -⟩ := hq
  exact ⟨p, r, rfl, hr⟩

end Code


theorem ptResv_pg {maxpage num_proc n vadr perm : Nat} {d d' : PTData} {r : Nat}
    (h : ptResv_spec maxpage num_proc n vadr perm d = some (d', r)) : d'.pg = d.pg := by
  unfold ptResv_spec at h
  cases hA : container_alloc_spec n d.toRData with
  | none => rw [hA] at h; cases h
  | some pr =>
    obtain ⟨r1, b⟩ := pr
    rw [hA] at h; simp only at h
    by_cases hb : b = 0
    · rw [if_pos hb] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
    · rw [if_neg hb] at h; exact (MPTNew.ptInsert_flags h).1

theorem arg_pg {reg a : Nat} {u : UData} (h : uctx_arg_spec reg u = some a) : u.pg = true := by
  unfold uctx_arg_spec at h; split at h
  · rename_i hc; exact hc.2.1
  · cases h

/-- An argument does not depend on the page tables. -/
theorem arg_setPT {reg a : Nat} {d : HData} {p : PTData} (hp : p.pg = d.pg)
    (h : uctx_arg_spec reg d.toUData = some a) : uctx_arg_spec reg ({ d with toPTData := p } : HData).toUData = some a := by
  unfold uctx_arg_spec at h ⊢
  show (if d.ikern = true ∧ p.pg = true ∧ d.ihost = true then _ else none) = some a
  rw [hp]; exact h

section Mmap
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- The tail of `sys_hvm_mmap`, from the page found. -/
theorem tail_step (hL : HL) (hmp : maxpage ≤ 2 ^ 20) {σ : Locals} {d d' : HData} {gpa hva hpa mt : Nat}
    (hcp : d.cid < num_proc) (hr : σ "r" = BitVec.ofNat 32 hpa) (hh : σ "hva" = BitVec.ofNat 32 hva)
    (e2 : uctx_arg2_spec d.toUData = some gpa) (e4 : uctx_arg4_spec d.toUData = some mt)
    (hs : mmapTail maxpage gpa hva hpa mt d = some d') :
    ∃ σ', Step εR c i0 MH (HF ucb num_proc xb vb eb) (tailS cidb ucb eb) σ d σ' d' := by
  unfold mmapTail at hs
  obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
  cases hv : VVMX.vmx_set_mmap_spec maxpage gpa (hostAddr hpa hva).toNat mt (toX d) with
  | none => rw [hv] at hb; cases hb
  | some pr =>
    obtain ⟨x1, r1⟩ := pr
    rw [hv] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    let σ1 := σ.set "hpa" (hostAddr hpa hva)
    have S1 : Step εR c i0 MH (HF ucb num_proc xb vb eb) (.assign "hpa" (.bin .add (.bin .band (.var "r")
        (.const ADDR_MASK)) (andE "hva" 4095))) σ d σ1 d :=
      Step.assign' "hpa" (by decide) _ (by simp [Expr.eval, BinOp.eval, andE, hr, hh, hostAddr])
    have S2 := argH (ida := ida) (cidb := cidb) εR c i0 hL "gpa" (by decide) (reg := U_EBX) (by decide) (σ := σ1) hcp e2
    let σ2 := (σ1.set "curid" (BitVec.ofNat 32 d.cid)).set "gpa" (BitVec.ofNat 32 gpa)
    have S3 := argH (ida := ida) (cidb := cidb) εR c i0 hL "memtype" (by decide) (reg := U_EDX) (by decide) (σ := σ2)
      hcp e4
    let σ3 := (σ2.set "curid" (BitVec.ofNat 32 d.cid)).set "memtype" (BitVec.ofNat 32 mt)
    obtain ⟨σ4, B, -⟩ := VVMX.setMmap_step hL.hxv hL.hve (heb_of hL) (by unfold VEPT.NPG; omega) εR c i0 (σ := σ3)
      (by simp [σ3, σ2, Locals.set]) (by simp [σ3, σ2, σ1, Locals.set]) (by simp [σ3]) hv
    obtain ⟨σ5, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ4) (d := putX d x1) hcp hR
    exact ⟨σ5, S1.seq (S2.seq (S3.seq ((xH (ida := ida) εR c i0 hL B).seq R)))⟩

/-- The footprint of `sys_hvm_mmap`: the page tables and containers, and the
hypercall's. -/
def MF (cb num_id pb ucb num_proc xb vb eb : Nat) (k : Nat) : Prop :=
  (k < cb + 5 * num_id ∨ pb ≤ k) ∨ HF ucb num_proc xb vb eb k

/-- **`sys_hvm_mmap` refines `trap_mmap_spec`.** -/
theorem mmap_triple (hL : HL) (hmax : 3 * maxpage < 2 ^ 32) (hnum : cb + 5 * num_id < 2 ^ 32)
    (hmp : maxpage ≤ 2 ^ 20) (hnn : num_proc ≤ num_id) {kl kh : Nat} :
    Triple εR c i0 MH (MF cb num_id pb ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ d.cid < num_id ∧ (d.AC d.cid).cusage ≤ (d.AC d.cid).cquota ∧
        ATInv maxpage kl kh d.toPData ∧ ∃ d1, trap_mmap_spec num_proc maxpage d = some d1)
      (mmapH cb maxpage pb fb cidb ucb eb) (fun _ d _ d' => trap_mmap_spec num_proc maxpage d = some d') := by
  intro σ l b d hlk hcs hM ⟨hcp, hci, hq, hAT, d', hs⟩
  have hs0 := hs
  have hU := hL.ulay
  unfold trap_mmap_spec at hs
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at hs; cases hs
  | some gpa =>
  cases e3 : uctx_arg3_spec d.toUData with
  | none => rw [e2, e3] at hs; cases hs
  | some hva =>
  cases e4 : uctx_arg4_spec d.toUData with
  | none => rw [e2, e3, e4] at hs; cases hs
  | some mt =>
  rw [e2, e3, e4] at hs; simp only at hs
  have hg32 := (arg_val e2).2; have hv32 := (arg_val e3).2
  have hpg : d.pg = true := arg_pg e2
  -- the arguments
  have AR := fun (x : Ident) (hx : x ≠ "lk") (reg : Nat) (hreg : reg < 17) (σ0 : Locals) (a : Nat)
      (ha : uctx_arg_spec reg d.toUData = some a) =>
    stepUH εR c i0 hL (F := fun _ => False) (d := d)
      (uctxArgU (ida := ida) (cidb := cidb) εR c i0 hU x hx hreg (σ := σ0) hcp (arg_val ha).1) (fun _ h => h.elim)
  have run0 : ∀ {s : Stmt APrim} {σ0 σ1 : Locals}, Step εR c i0 MH (fun _ => False) s σ0 d σ1 d →
      (σ0 "lk").toNat = i0 → ∀ l0, CS1 c i0 l0 b → ∃ l1, Runs (rprimsA εR c) s σ0 l0 σ1 l1 ∧ CS1 c i0 l1 b :=
    fun S hl l0 hc => by
      obtain ⟨l1, b1, r1, c1, m1, f1⟩ := S.2 l0 b hl hc hM
      have : b1 = b := funext (fun k => f1 k id)
      subst this; exact ⟨l1, r1, c1⟩
  let cur := BitVec.ofNat 32 d.cid
  let σ1 := (σ.set "curid" cur).set "gpa" (BitVec.ofNat 32 gpa)
  let σ2 := (σ1.set "curid" cur).set "hva" (BitVec.ofNat 32 hva)
  let σ3 := (σ2.set "curid" cur).set "memtype" (BitVec.ofNat 32 mt)
  obtain ⟨l1, r1, c1⟩ := run0 (AR "gpa" (by decide) U_EBX (by decide) σ gpa e2) hlk l hcs
  obtain ⟨l2, r2, c2⟩ := run0 (AR "hva" (by decide) U_ECX (by decide) σ1 hva e3)
    (by simpa [σ1, Locals.set] using hlk) l1 c1
  obtain ⟨l3, r3, c3⟩ := run0 (AR "memtype" (by decide) U_EDX (by decide) σ2 mt e4)
    (by simpa [σ2, σ1, Locals.set] using hlk) l2 c2
  have rA : Runs (rprimsA εR c) (.seq (uctxArgS cidb ucb "gpa" U_EBX) (.seq (uctxArgS cidb ucb "hva" U_ECX)
      (uctxArgS cidb ucb "memtype" U_EDX))) σ l σ3 l3 := Runs.seq r1 (Runs.seq r2 r3)
  have lk3 : (σ3 "lk").toNat = i0 := by simpa [σ3, σ2, σ1, Locals.set] using hlk
  have q_hva : σ3 "hva" = BitVec.ofNat 32 hva := by simp [σ3, σ2, Locals.set]
  have q_gpa : σ3 "gpa" = BitVec.ofNat 32 gpa := by simp [σ3, σ2, σ1, Locals.set]
  have q_cur : σ3 "curid" = cur := by simp [σ3]
  -- the error code
  have ERR : hcall (some (toX d, [(U_EAX, E_INVAL_ADDR)])) d = some d' →
      ∃ σ' l' b', Runs (rprimsA εR c) (errS cidb ucb E_INVAL_ADDR) σ3 l3 σ' l' ∧ CS1 c i0 l' b' ∧ MH d' b' ∧
        σ' "lk" = σ3 "lk" ∧ ∀ k, ¬ MF cb num_id pb ucb num_proc xb vb eb k → b' k = b k := fun h => by
    obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    obtain ⟨σ', R⟩ := errH (ida := ida) εR c i0 hL (σ := σ3) (d := putX d (toX d)) hcp hR
    obtain ⟨l', b', r', c', m', f'⟩ := R.2 l3 b lk3 c3 hM
    exact ⟨σ', l', b', r', c', m', R.1, fun k hk => f' k (fun h => hk (Or.inr h))⟩
  have fin : ∀ {s : Stmt APrim} {σ' : Locals} {l' : RLog} {b' : Region},
      Runs (rprimsA εR c) (.seq (uctxArgS cidb ucb "gpa" U_EBX) (.seq (uctxArgS cidb ucb "hva" U_ECX)
        (.seq (uctxArgS cidb ucb "memtype" U_EDX) s))) σ l σ' l' →
      CS1 c i0 l' b' → MH d' b' → σ' "lk" = σ3 "lk" → (∀ k, ¬ MF cb num_id pb ucb num_proc xb vb eb k → b' k = b k) →
      s = (.ite (.bin .eq (andE "hva" 4095) (.const 0))
        (.ite (.bin .eq (andE "gpa" 4095) (.const 0))
          (.ite (.bin .ltu (.var "hva") (.const 1073741824)) (errS cidb ucb E_INVAL_ADDR)
            (.ite (.bin .ltu (.var "hva") (.const 4026527745)) (bodyS cb maxpage pb fb cidb ucb eb)
              (errS cidb ucb E_INVAL_ADDR)))
          (errS cidb ucb E_INVAL_ADDR))
        (errS cidb ucb E_INVAL_ADDR)) →
      ∃ σ'' l'' b'' d'', Runs (rprimsA εR c) (mmapH cb maxpage pb fb cidb ucb eb) σ l σ'' l'' ∧ CS1 c i0 l'' b'' ∧
        MH d'' b'' ∧ σ'' "lk" = σ "lk" ∧ (∀ k, ¬ MF cb num_id pb ucb num_proc xb vb eb k → b'' k = b k) ∧
        trap_mmap_spec num_proc maxpage d = some d'' := fun r c m k f e => by
    subst e
    exact ⟨_, _, _, d', r, c, m, by rw [k]; simpa [σ3, σ2, σ1, Locals.set], f, hs0⟩
  -- the address checks
  have G1 : ∀ h : Prop, (h ↔ hva % 4096 = 0) → ((Expr.bin .eq (andE "hva" 4095) (.const 0)).eval σ3 = 0 ↔ ¬ h) :=
    fun h hh => by
      show BinOp.eval .eq (σ3 "hva" &&& BitVec.ofNat 32 4095) 0 = 0 ↔ _
      rw [q_hva, hh, ← mask_zero]; simp [BinOp.eval]
  have G2 : ((Expr.bin .eq (andE "gpa" 4095) (.const 0)).eval σ3 = 0 ↔ ¬ gpa % 4096 = 0) := by
    show BinOp.eval .eq (σ3 "gpa" &&& BitVec.ofNat 32 4095) 0 = 0 ↔ _
    rw [q_gpa, ← mask_zero]; simp [BinOp.eval]
  have G3 := ltu_eval (σ := σ3) (ea := .var "hva") (eb := .const 1073741824) (a := hva) (b := 1073741824) q_hva rfl
    hv32 (by decide)
  have G4 := ltu_eval (σ := σ3) (ea := .var "hva") (eb := .const 4026527745) (a := hva) (b := 4026527745) q_hva rfl
    hv32 (by decide)
  by_cases ok : hva % 4096 = 0 ∧ gpa % 4096 = 0 ∧ 1073741824 ≤ hva ∧ hva + 4096 ≤ 4026531840
  · rw [if_pos ok] at hs
    obtain ⟨c1', c2', c3', c4'⟩ := ok
    have g1 : ¬ (Expr.bin .eq (andE "hva" 4095) (.const 0)).eval σ3 = 0 := fun h => ((G1 _ Iff.rfl).1 h) c1'
    have g2 : ¬ (Expr.bin .eq (andE "gpa" 4095) (.const 0)).eval σ3 = 0 := fun h => (G2.1 h) c2'
    rw [if_neg (by omega)] at G3
    rw [if_pos (by omega)] at G4
    -- the body: `n = curid; vaddr = hva; pt_read`
    cases hp : ptRead_spec num_proc d.cid hva d.toPTData with
    | none => rw [hp] at hs; cases hs
    | some hpa =>
    rw [hp] at hs; simp only at hs
    let σ4 := (σ3.set "n" cur).set "vaddr" (BitVec.ofNat 32 hva)
    obtain ⟨σ5, l5, b5, d5, r5, c5, m5, k5, f5, hd5, v5, hv5, hr5⟩ := readU (ida := ida) εR c i0 hL d.cid hva hv32
      σ4 l3 b d (by simpa [σ4, Locals.set] using lk3) c3 hM ⟨by simp [σ4, cur, Locals.set], by simp [σ4], hpa, hp⟩
    subst d5
    rw [hp] at hv5; simp only [Option.some.injEq] at hv5; subst hv5
    have hb5 : b5 = b := funext (fun k => f5 k id)
    subst b5
    have rR : Runs (rprimsA εR c) (readS pb fb) σ3 l3 σ5 l5 :=
      Runs.seq (asg_run "n" (.var "curid") (by simp [Expr.eval, q_cur]))
        (Runs.seq (asg_run "vaddr" (.var "hva") (by simp [Expr.eval, Locals.set, q_hva])) r5)
    have p5 : ∀ z, z = "curid" ∨ z = "hva" ∨ z = "gpa" ∨ z = "memtype" ∨ z = "lk" → σ5 z = σ3 z := by
      rintro z (rfl | rfl | rfl | rfl | rfl) <;> exact rR.frame rfl
    have rG : (Expr.bin .eq (andE "r" 1) (.const 0)).eval σ5 = if (BitVec.ofNat 32 hpa &&& 1) = 0 then 1 else 0 := by
      show BinOp.eval .eq (σ5 "r" &&& BitVec.ofNat 32 1) 0 = _
      rw [hr5]; rfl
    by_cases hz : (BitVec.ofNat 32 hpa &&& 1) = 0
    · rw [if_pos hz] at hs rG
      cases hrv : ptResv_spec maxpage num_proc d.cid hva 7 d.toPTData with
      | none => rw [hrv] at hs; cases hs
      | some pr =>
      obtain ⟨p0, rr⟩ := pr
      rw [hrv] at hs; simp only at hs
      cases hp' : ptRead_spec num_proc d.cid hva p0 with
      | none => rw [hp'] at hs; cases hs
      | some hpa' =>
      rw [hp'] at hs; simp only at hs
      -- `pt_resv(curid, hva, 7)`
      let σ6 := ((σ5.set "n" cur).set "vaddr" (BitVec.ofNat 32 hva)).set "perm" 7
      have lk5 : (σ5 "lk").toNat = i0 := by rw [p5 "lk" (by simp)]; exact lk3
      obtain ⟨σ7, l7, b7, d7, r7, c7, m7, k7, f7, p, r', rfl, hrv'⟩ :=
        resvU (ida := ida) (ob := ob) εR c i0 hL hmax hnum hmp hnn (kl := kl) (kh := kh) d.cid hva hci
          σ6 l5 b d (by simpa [σ6, Locals.set] using lk5) c5 hM
          ⟨⟨by simp [σ6, cur, Locals.set], by simp [σ6, Locals.set], by simp [σ6], hAT, hq, p0, rr, hrv⟩, hpg⟩
      rw [hrv] at hrv'; simp only [Option.some.injEq, Prod.mk.injEq] at hrv'
      obtain ⟨rfl, rfl⟩ := hrv'
      let dR : HData := { d with toPTData := p0 }
      have p7 : ∀ z, z = "curid" ∨ z = "hva" ∨ z = "lk" → σ7 z = σ5 z := by
        rintro z (rfl | rfl | rfl) <;> (rw [r7.frame rfl]; simp [σ6, Locals.set])
      -- `pt_read` again
      let σ8 := (σ7.set "n" cur).set "vaddr" (BitVec.ofNat 32 hva)
      have lk7 : (σ7 "lk").toNat = i0 := by rw [p7 "lk" (by simp)]; exact lk5
      obtain ⟨σ9, l9, b9, d9, r9, c9, m9, k9, f9, hd9, v9, hv9, hr9⟩ := readU (ida := ida) εR c i0 hL d.cid hva hv32
        σ8 l7 b7 dR (by simpa [σ8, Locals.set] using lk7) c7 m7
        ⟨by simp [σ8, cur, Locals.set], by simp [σ8], hpa', hp'⟩
      subst d9
      rw [hp'] at hv9; simp only [Option.some.injEq] at hv9; subst hv9
      have hb9 : b9 = b7 := funext (fun k => f9 k id)
      subst b9
      have rR2 : Runs (rprimsA εR c) (readS pb fb) σ7 l7 σ9 l9 :=
        Runs.seq (asg_run "n" (.var "curid") (by simp [Expr.eval, p7 "curid" (by simp), p5 "curid" (by simp), q_cur]))
          (Runs.seq (asg_run "vaddr" (.var "hva") (by simp [Expr.eval, Locals.set, p7 "hva" (by simp),
            p5 "hva" (by simp), q_hva])) r9)
      have p9 : ∀ z, z = "hva" ∨ z = "lk" → σ9 z = σ7 z := by
        rintro z (rfl | rfl) <;> exact rR2.frame rfl
      have hpgR : p0.pg = d.pg := ptResv_pg hrv
      obtain ⟨σT, T⟩ := tail_step (ida := ida) (ob := ob) (cidb := cidb) εR c i0 hL hmp (σ := σ9) (d := dR)
        (gpa := gpa) (hva := hva) (hpa := hpa') (mt := mt) hcp hr9
        (by rw [p9 "hva" (by simp), p7 "hva" (by simp), p5 "hva" (by simp), q_hva])
        (arg_setPT hpgR e2) (arg_setPT hpgR e4) hs
      obtain ⟨lT, bT, rT, cT, mT, fT⟩ := T.2 l9 b7 (by rw [p9 "lk" (by simp)]; exact lk7) c9 m9
      have rRes : Runs (rprimsA εR c) (resvS cb maxpage pb fb) σ5 l5 σ9 l9 :=
        Runs.seq (asg_run "n" _ (by simp [Expr.eval, p5 "curid" (by simp), q_cur]))
          (Runs.seq (asg_run "vaddr" _ (by simp [Expr.eval, Locals.set, p5 "hva" (by simp), q_hva]))
            (Runs.seq (asg_run "perm" _ rfl) (Runs.seq r7 rR2)))
      have rBody : Runs (rprimsA εR c) (bodyS cb maxpage pb fb cidb ucb eb) σ3 l3 σT lT :=
        Runs.seq rR (Runs.seq (Runs.ite_true (by rw [rG]; decide) rRes) rT)
      exact fin (Runs.seq r1 (Runs.seq r2 (Runs.seq r3 (Runs.ite_true g1 (Runs.ite_true g2
        (Runs.ite_false G3 (Runs.ite_true (by rw [G4]; decide) rBody))))))) cT mT
        (by rw [T.1, p9 "lk" (by simp), p7 "lk" (by simp), p5 "lk" (by simp)])
        (fun k hk => by
          rw [fT k (fun h => hk (Or.inr h)), f7 k (fun h => hk (Or.inl h))]) rfl
    · rw [if_neg hz] at hs rG
      obtain ⟨σT, T⟩ := tail_step (ida := ida) (ob := ob) (cidb := cidb) εR c i0 hL hmp (σ := σ5) (d := d)
        (gpa := gpa) (hva := hva) (hpa := hpa) (mt := mt) hcp hr5 (by rw [p5 "hva" (by simp), q_hva]) e2 e4 hs
      have lk5 : (σ5 "lk").toNat = i0 := by rw [p5 "lk" (by simp)]; exact lk3
      obtain ⟨lT, bT, rT, cT, mT, fT⟩ := T.2 l5 b lk5 c5 hM
      have rBody : Runs (rprimsA εR c) (bodyS cb maxpage pb fb cidb ucb eb) σ3 l3 σT lT :=
        Runs.seq rR (Runs.seq (Runs.ite_false rG Runs.skip) rT)
      exact fin (Runs.seq r1 (Runs.seq r2 (Runs.seq r3 (Runs.ite_true g1 (Runs.ite_true g2
        (Runs.ite_false G3 (Runs.ite_true (by rw [G4]; decide) rBody))))))) cT mT
        (by rw [T.1, p5 "lk" (by simp)])
        (fun k hk => fT k (fun h => hk (Or.inr h))) rfl
  · rw [if_neg ok] at hs
    obtain ⟨σE, lE, bE, rE, cE, mE, kE, fE⟩ := ERR hs
    have W := fun {s : Stmt APrim} (h : Runs (rprimsA εR c) s σ3 l3 σE lE) =>
      fin (s := s) (Runs.seq r1 (Runs.seq r2 (Runs.seq r3 h))) cE mE kE fE
    by_cases c1' : hva % 4096 = 0
    · have g1 : ¬ (Expr.bin .eq (andE "hva" 4095) (.const 0)).eval σ3 = 0 := fun h => ((G1 _ Iff.rfl).1 h) c1'
      by_cases c2' : gpa % 4096 = 0
      · have g2 : ¬ (Expr.bin .eq (andE "gpa" 4095) (.const 0)).eval σ3 = 0 := fun h => (G2.1 h) c2'
        by_cases c3' : hva < 1073741824
        · rw [if_pos c3'] at G3
          exact W (Runs.ite_true g1 (Runs.ite_true g2 (Runs.ite_true (by rw [G3]; decide) rE))) rfl
        · rw [if_neg c3'] at G3
          have c4' : ¬ hva < 4026527745 := fun h => ok ⟨c1', c2', by omega, by omega⟩
          rw [if_neg c4'] at G4
          exact W (Runs.ite_true g1 (Runs.ite_true g2 (Runs.ite_false G3 (Runs.ite_false G4 rE)))) rfl
      · exact W (Runs.ite_true g1 (Runs.ite_false (G2.2 c2') rE)) rfl
    · exact W (Runs.ite_false ((G1 _ Iff.rfl).2 c1') rE) rfl

end Mmap

end TTop
