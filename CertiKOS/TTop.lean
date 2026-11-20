import CertiKOS.TShare
import CertiKOS.VVMX
import CertiKOS.VEPT4

/-!
# The top state: processes, device output and the virtual machine

mCertiKOS's trap layer sees one abstract state with everything in it. The
ports so far stop at `UData` (user contexts on top of the process layers).
The system calls still missing need two more parts:

* **device output** (`devout`): `SYS_print` (number 28) appends its argument
  to the output of the calling process. mCertiKOS's `print_spec` is
  `DeviceOutput_update (devout adt) (cid adt) (cid adt) (OUT content)`.
* **the virtual machine** (`vmx`, `vmcs`, `ept`, and `vinit`, mCertiKOS's
  `init`, which `vm_run` tests): the state of `VVMX`, for the hypercalls.

`HData` adds both to `UData`. In the region:
* each process has a console of 257 words at `ob + i * 257`: the number of
  words written so far, then a ring of 256 words holding the most recent
  ones. `MatchOut`: the count cell holds the length of the output (modulo
  2^32), and every one of the last 256 words is in its slot. So the
  specification keeps mCertiKOS's unbounded list, and the device holds what a
  console shows.
* the three blocks of `VVMX` (`MatchX`) at `xb`, `vb`, `eb`;
* the EPT's three upper tables (`VEPT.MatchUp`, from `VEPT4`) at `upb vb`,
  right after the VMCS page and before the leaf tables at `eb`, as in
  mCertiKOS's `struct eptStruct` (`pml4`, `pdpt`, `pdt`, then `ptab`).
All of it sits between the user contexts and the page-table pool
(`HLayout`), where the layers below do not look.

* `matchU_frame`, `matchOut_frame`, `matchX_frame`: each part depends only on
  its own cells.
* `stepUH`: **a step of the process layers is a step of the top state**, if
  it writes only their cells.
* `stepXH`: **a step of the VMX layer is a step of the top state**, if it
  keeps the EPT's tables (`VEPT.SameShape`): only `vmx_set_mmap` changes the
  EPT, and it writes a leaf (`THyp3.setMmap_shape`).
* `printS`, `print_triple`: **`sys_print` refines `print_spec`.**
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

/-! ## The state -/

structure HData extends UData where
  devout : Nat → List Val
  vinit : Bool
  vmx : Nat → Option Val
  vmcs : VVMCS.VMCS
  ept : VEPT.EPT

/-- The part the VMX layer sees. -/
def toX (d : HData) : XSt := ⟨d.ikern, d.pg, d.ihost, d.vinit, d.vmx, d.vmcs, d.ept⟩

/-- Put back what the VMX layer changed. The flags belong to the process
layers and are not changed here. -/
def putX (d : HData) (x : XSt) : HData := { d with vinit := x.init, vmx := x.vmx, vmcs := x.vmcs, ept := x.ept }

def SYS_print : Nat := 28

/-- **`print_spec`**: argument 2 is appended to the caller's output. -/
def print_spec (d : HData) : Option HData :=
  match uctx_arg2_spec d.toUData with
  | some content =>
    match uctx_set_errno_spec E_SUCC d.toUData with
    | some u => some { d with toUData := u, devout := setAt d.devout d.cid (d.devout d.cid ++ [BitVec.ofNat 32 content]) }
    | none => none
  | none => none

/-! ## The region -/

/-- The consoles: the count, and the last 256 words in their slots. -/
def MatchOut (num_proc ob : Nat) (o : Nat → List Val) (b : Region) : Prop :=
  ∀ i, i < num_proc → b (ob + i * 257) = BitVec.ofNat 32 (o i).length ∧
    ∀ j, j < (o i).length → (o i).length ≤ j + 256 → b (ob + i * 257 + 1 + j % 256) = (o i).getD j 0

/-- The cells of the consoles. -/
def OF (ob num_proc : Nat) (k : Nat) : Prop := ob ≤ k ∧ k < ob + 257 * num_proc

structure HLayout (maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat) : Prop where
  ulay : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb
  hob : ucb + 17 * num_proc ≤ ob
  hxb : ob + 257 * num_proc ≤ xb
  hxv : xb + 36 ≤ vb
  hve : vb + 65540 ≤ eb
  hep : eb + 1048576 ≤ pb
  hup : vb + 65540 + 3072 ≤ eb

/-- Where the EPT's upper tables start: after the VMCS page. -/
def upb (vb : Nat) : Nat := vb + 65540

def MatchH (maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat) (d : HData)
    (b : Region) : Prop :=
  MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb d.toUData b ∧
    (MatchOut num_proc ob d.devout b ∧ (MatchX xb vb eb (toX d) b ∧ VEPT.MatchUp (upb vb) eb d.ept b))

section Region
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}

theorem pb_lt (hL : HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb) :
    pb < 2 ^ 32 := by
  have := hL.ulay.ilay.clay.qlay.tlay.slay.lay.hib; have := hL.ulay.ilay.clay.qlay.tlay.slay.lay.hfb
  have := hL.ulay.ilay.clay.qlay.tlay.slay.lay.hend; omega

theorem matchU_frame (hL : ULayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb) {d : UData}
    {b b' : Region} (hM : MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb d b)
    (hfr : ∀ k, k < ucb + 17 * num_proc ∨ pb ≤ k → b' k = b k) :
    MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb d b' := by
  refine ⟨matchI_frame hL hM.1 (fun k hk => hfr k (by omega)), fun i n hi hn v hv => ?_⟩
  rw [hfr _ (Or.inl (by omega))]
  exact hM.2 i n hi hn v hv

theorem matchOut_frame {o : Nat → List Val} {b b' : Region} (hM : MatchOut num_proc ob o b)
    (hfr : ∀ k, OF ob num_proc k → b' k = b k) : MatchOut num_proc ob o b' := by
  intro i hi
  refine ⟨by rw [hfr _ ⟨by omega, by omega⟩]; exact (hM i hi).1, fun j hj hw => ?_⟩
  have : j % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [hfr _ ⟨by omega, by omega⟩]; exact (hM i hi).2 j hj hw

theorem matchX_of {x y : XSt} {b : Region} (h : MatchX xb vb eb x b) (ev : x.vmx = y.vmx) (ec : x.vmcs = y.vmcs)
    (ee : x.ept = y.ept) : MatchX xb vb eb y b :=
  ⟨fun i v hi hv => h.1 i v hi (by rw [ev]; exact hv), by rw [← ec]; exact h.2.1,
   fun g v hg hl => h.2.2 g v hg (by show VEPT.ept_leaf x.ept g = _; rw [ee]; exact hl)⟩

theorem matchX_frame {x : XSt} {b b' : Region} (h : MatchX xb vb eb x b)
    (hfr : ∀ k, xb ≤ k → k < eb + VEPT.NPG → b' k = b k) (hxv : xb + 36 ≤ vb) (hve : vb + 65540 ≤ eb) :
    MatchX xb vb eb x b' := by
  refine ⟨fun i v hi hv => ?_, VVMX.matchV_frame h.2.1 (fun a h1 h2 => hfr a (by omega) ?_),
    VVMX.matchE_frame h.2.2 (fun a h1 h2 => hfr a (by omega) h2)⟩
  · unfold VVMX.VMX_Size' at hi
    rw [hfr _ (by omega) (by unfold VEPT.NPG; omega)]; exact h.1 i v (by unfold VVMX.VMX_Size'; omega) hv
  · unfold VVMCS.NENC at h2; unfold VEPT.NPG; omega

/-- **The consoles after a word is written**: the word in its slot, the count
one more. -/
theorem matchOut_append {o : Nat → List Val} {b : Region} {i : Nat} (v : Val) (hM : MatchOut num_proc ob o b)
    (hi : i < num_proc) :
    MatchOut num_proc ob (setAt o i (o i ++ [v]))
      (setCell (setCell b (ob + i * 257 + 1 + (o i).length % 256) v) (ob + i * 257)
        (BitVec.ofNat 32 ((o i).length + 1))) := by
  intro k hk
  have hmi : (o i).length % 256 < 256 := Nat.mod_lt _ (by decide)
  by_cases e : k = i
  · subst e
    rw [setAt_eq]
    refine ⟨by rw [sc_eq, List.length_append]; rfl, fun j hj hw => ?_⟩
    rw [List.length_append, List.length_singleton] at hj hw
    have hmj : j % 256 < 256 := Nat.mod_lt _ (by decide)
    rw [sc_ne _ _ (by omega)]
    by_cases ej : j = (o k).length
    · subst ej
      rw [sc_eq]
      simp [List.getD_eq_getElem?_getD]
    · have hj' : j < (o k).length := by omega
      rw [sc_ne _ _ (by omega)]
      rw [(hM k hk).2 j hj' (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
  · rw [setAt_ne _ _ e]
    have h1 : ob + k * 257 ≠ ob + i * 257 := by omega
    refine ⟨by rw [sc_ne _ _ h1, sc_ne _ _ (by omega)]; exact (hM k hk).1, fun j hj hw => ?_⟩
    have hmj : j % 256 < 256 := Nat.mod_lt _ (by decide)
    rw [sc_ne _ _ (by omega), sc_ne _ _ (by omega)]
    exact (hM k hk).2 j hj hw

end Region

/-! ## Steps of the parts are steps of the whole -/

section Lift
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat) {F : Nat → Prop}

local notation "MU" => MatchU maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb
local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb

/-- **A step of the process layers is a step of the top state.** -/
theorem stepUH (hL : HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb)
    {s : Stmt APrim} {σ σ' : Locals} {d : HData} {u : UData} (h : Step εR c i0 MU F s σ d.toUData σ' u)
    (hF : ∀ k, F k → k < ucb + 17 * num_proc ∨ pb ≤ k) : Step εR c i0 MH F s σ d σ' { d with toUData := u } := by
  have := hL.hob; have := hL.hxb; have := hL.hxv; have := hL.hve; have := hL.hep; have := hL.hup
  refine Step.lift (π := HData.toUData) (put := fun (d' : HData) (u' : UData) => ({ d' with toUData := u' } : HData))
    (M2 := fun d' b => MatchOut num_proc ob d'.devout b ∧
      (MatchX xb vb eb (toX d') b ∧ VEPT.MatchUp (upb vb) eb d'.ept b)) h rfl
    (fun b b' h2 _ _ hf => ⟨matchOut_frame h2.1 (fun k hk => hf k (fun h' => by
        have := hF k h'; unfold OF at hk; omega)),
      matchX_of (matchX_frame h2.2.1 (fun k h1 h2' => hf k (fun h' => by
        have := hF k h'; unfold VEPT.NPG at h2'; omega)) hL.hxv hL.hve) rfl rfl rfl,
      VEPT.matchUp_frame h2.2.2 (fun a ha => hf a (fun h' => by
        have := hF a h'; unfold VEPT.InUp upb at ha; omega))⟩)

/-- **A step of the VMX layer is a step of the top state.** -/
theorem stepXH (hL : HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb)
    {s : Stmt APrim} {σ σ' : Locals} {d : HData} {x : XSt}
    (h : Step εR c i0 (MatchX xb vb eb) (XF xb vb eb) s σ (toX d) σ' x) (hsh : VEPT.SameShape d.ept x.ept) :
    Step εR c i0 MH (XF xb vb eb) s σ d σ' (putX d x) := by
  have := hL.hob; have := hL.hxb; have := hL.hxv; have := hL.hve; have := hL.hep; have := hL.hup
  refine ⟨h.1, fun l b hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := h.2 l b hlk hcs hM.2.2.1
  have hx : ∀ k, XF xb vb eb k → xb ≤ k ∧ k < eb + VEPT.NPG := fun k hk => by
    unfold XF VVMX.VMX_Size' VVMCS.NENC VEPT.NPG at hk; unfold VEPT.NPG; omega
  refine ⟨l1, b1, r1, c1, ⟨matchU_frame hL.ulay hM.1 (fun k hk => f1 k (fun h' => by
      have := hx k h'; unfold VEPT.NPG at this; omega)),
    matchOut_frame hM.2.1 (fun k hk => f1 k (fun h' => by have := hx k h'; unfold OF at hk; omega)),
    matchX_of m1 rfl rfl rfl, VEPT.matchUp_shape hM.2.2.2 hsh (fun a ha => f1 a (fun h' => by
      unfold XF VVMX.VMX_Size' VVMCS.NENC VEPT.NPG at h'; unfold VEPT.InUp upb at ha; omega))⟩, f1⟩

/-- **A triple of the process layers holds in the top state**, if it writes
none of the consoles and VMX blocks. -/
theorem liftUT (hL : HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb)
    {F : Nat → Prop} {P : Locals → UData → Prop} {s : Stmt APrim}
    {Q : Locals → UData → Locals → UData → Prop} (h : Triple εR c i0 MU F P s Q)
    (hF : ∀ k, F k → k < ucb + 17 * num_proc ∨ pb ≤ k) :
    Triple εR c i0 MH F (fun σ d => P σ d.toUData) s
      (fun σ d σ' d' => ∃ u, d' = { d with toUData := u } ∧ Q σ d.toUData σ' u) := by
  have := hL.hob; have := hL.hxb; have := hL.hxv; have := hL.hve; have := hL.hep; have := hL.hup
  exact h.lift (π := HData.toUData) (put := fun (d' : HData) (u' : UData) => ({ d' with toUData := u' } : HData))
    (M2 := fun d' b => MatchOut num_proc ob d'.devout b ∧
      (MatchX xb vb eb (toX d') b ∧ VEPT.MatchUp (upb vb) eb d'.ept b)) (fun _ _ => rfl)
    (fun d' b σ σ' d1 b' h2 _ _ _ hf => ⟨matchOut_frame h2.1 (fun k hk => hf k (fun h' => by
        have := hF k h'; unfold OF at hk; omega)),
      matchX_of (matchX_frame h2.2.1 (fun k h1 h2' => hf k (fun h' => by
        have := hF k h'; unfold VEPT.NPG at h2'; omega)) hL.hxv hL.hve) rfl rfl rfl,
      VEPT.matchUp_frame h2.2.2 (fun a ha => hf a (fun h' => by
        have := hF a h'; unfold VEPT.InUp upb at ha; omega))⟩)

end Lift

/-! ## `SYS_print` -/

/-- `&console[curid]`. -/
def oaddrE (ob : Nat) : Expr := .bin .add (.const (BitVec.ofNat 32 ob)) (.bin .mul (.var "curid") (.const 257))

/-- Write `content` to the caller's console:
`console[curid].ring[count & 255] = content; console[curid].count = count + 1;` -/
def outPutS (ob : Nat) : Stmt APrim :=
  .seq (.call "_" .push [lkE, .bin .add (.bin .add (oaddrE ob) (.const 1)) (.bin .band (.var "n") (.const 255)),
      .var "content"])
    (.call "_" .push [lkE, oaddrE ob, .bin .add (.var "n") (.const 1)])

/-- `sys_print`:
```
content = uctx_arg2();
n = console[curid].count;
console[curid].ring[n & 255] = content; console[curid].count = n + 1;
uctx_set_errno(E_SUCC);
``` -/
def printS (cidb ucb ob : Nat) : Stmt APrim :=
  .seq (uctxArgS cidb ucb "content" U_EBX)
    (.seq (.call "n" .pull [lkE, oaddrE ob])
      (.seq (outPutS ob) (uctxSetRegS cidb ucb U_EAX (.const 0))))

section Print
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb

theorem oaddr_eval (hL : HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb)
    {σ : Locals} {i : Nat} (hc : σ "curid" = BitVec.ofNat 32 i) (hi : i < num_proc) :
    (oaddrE ob).eval σ = BitVec.ofNat 32 (ob + i * 257) := by
  show BitVec.ofNat 32 ob + σ "curid" * (257 : Val) = _
  rw [hc, show (257 : Val) = BitVec.ofNat 32 257 from rfl, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]

theorem oaddr_lt (hL : HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb)
    {i : Nat} (hi : i < num_proc) : ob + i * 257 + 257 ≤ 2 ^ 32 := by
  have := pb_lt hL; have := hL.hxb; have := hL.hxv; have := hL.hve; have := hL.hep; omega

theorem band255 (n : Nat) : ((BitVec.ofNat 32 n : Val) &&& (255 : Val)).toNat = n % 256 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (255 : Val).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_mod_of_dvd n (by decide)

/-- `n = console[curid].count;` -/
theorem outCount_step (hL : HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb)
    {F : Nat → Prop} {σ : Locals} {d : HData} {i : Nat} (hc : σ "curid" = BitVec.ofNat 32 i) (hi : i < num_proc) :
    Step εR c i0 MH F (.call "n" .pull [lkE, oaddrE ob]) σ d
      (σ.set "n" (BitVec.ofNat 32 (d.devout i).length)) d := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  have hr := rd_run (εR := εR) hcs hlk "n" (oaddrE ob) (n := ob + i * 257)
    (by rw [oaddr_eval hL hc hi, tn (by have := oaddr_lt hL hi; omega)])
  rw [((hM.2.1) i hi).1] at hr
  exact ⟨l, b, hr, hcs, hM, fun _ _ => rfl⟩

/-- The two writes of `sys_print`, against the abstract append. -/
theorem outPut_step (hL : HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb)
    {σ : Locals} {d : HData} {i : Nat} {v : Val} (hc : σ "curid" = BitVec.ofNat 32 i) (hi : i < num_proc)
    (hn : σ "n" = BitVec.ofNat 32 (d.devout i).length) (hv : σ "content" = v) :
    Step εR c i0 MH (OF ob num_proc) (outPutS ob) σ d ((σ.set "_" 0).set "_" 0)
      { d with devout := setAt d.devout i (d.devout i ++ [v]) } := by
  have := hL.hob; have := hL.hxb; have := hL.hxv; have := hL.hve; have := hL.hep; have := hL.hup
  have hlt := oaddr_lt hL hi
  refine ⟨by simp [Locals.set], fun l b hlk hcs hM => ?_⟩
  have hmi : (d.devout i).length % 256 < 256 := Nat.mod_lt _ (by decide)
  obtain ⟨l1, r1, c1⟩ := wr_run (εR := εR) hcs hlk
    (.bin .add (.bin .add (oaddrE ob) (.const 1)) (.bin .band (.var "n") (.const 255))) (.var "content")
    (n := ob + i * 257 + 1 + (d.devout i).length % 256) (v := v) (by
      show (((oaddrE ob).eval σ + (1 : Val)) + (σ "n" &&& (255 : Val))).toNat = _
      rw [oaddr_eval hL hc hi, hn, BitVec.toNat_add, BitVec.toNat_add, band255, tn (by omega),
        show (1 : Val).toNat = 1 from rfl]
      omega) hv
  obtain ⟨l2, r2, c2⟩ := wr_run (εR := εR) c1 (by simpa [Locals.set] using hlk) (oaddrE ob)
    (.bin .add (.var "n") (.const 1)) (σ := σ.set "_" 0) (n := ob + i * 257)
    (v := BitVec.ofNat 32 ((d.devout i).length + 1))
    (by rw [oaddr_eval hL (by simpa [Locals.set] using hc) hi, tn (by omega)])
    (by show (σ.set "_" 0) "n" + (1 : Val) = _
        rw [Locals.set_other _ _ (by decide), hn, show (1 : Val) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add])
  have hin : ∀ k, ¬ OF ob num_proc k → k ≠ ob + i * 257 ∧ k ≠ ob + i * 257 + 1 + (d.devout i).length % 256 :=
    fun k hk => ⟨fun e => hk ⟨by omega, by omega⟩, fun e => hk ⟨by omega, by omega⟩⟩
  have hfr : ∀ k, ¬ OF ob num_proc k →
      setCell (setCell b (ob + i * 257 + 1 + (d.devout i).length % 256) v) (ob + i * 257)
        (BitVec.ofNat 32 ((d.devout i).length + 1)) k = b k := fun k hk => by
    rw [sc_ne _ _ (hin k hk).1, sc_ne _ _ (hin k hk).2]
  refine ⟨l2, _, Runs.seq r1 r2, c2, ⟨matchU_frame hL.ulay hM.1 (fun k hk => hfr k (fun h' => by
      unfold OF at h'; omega)), matchOut_append v hM.2.1 hi,
    matchX_frame hM.2.2.1 (fun k h1 h2 => hfr k (fun h' => by unfold OF at h'; omega)) hL.hxv hL.hve,
    VEPT.matchUp_frame hM.2.2.2 (fun a ha => hfr a (fun h' => by unfold OF at h'; unfold VEPT.InUp upb at ha; omega))⟩,
    hfr⟩

/-- **`sys_print` refines `print_spec`.** -/
theorem print_triple (hL : HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb) :
    Triple εR c i0 MH (fun k => UCF ucb num_proc k ∨ OF ob num_proc k)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, print_spec d = some d1)
      (printS cidb ucb ob)
      (fun _ d _ d' => print_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hU := hL.ulay
  have := hL.hob
  have hs0 := hs
  unfold print_spec at hs
  cases e2 : uctx_arg2_spec d.toUData with
  | none => rw [e2] at hs; cases hs
  | some content =>
    rw [e2] at hs
    cases e0 : uctx_set_errno_spec E_SUCC d.toUData with
    | none => rw [e0] at hs; cases hs
    | some u =>
      rw [e0] at hs
      simp only [Option.some.injEq] at hs
      subst hs
      obtain ⟨hv, hv32⟩ := arg_val e2
      let σ1 := (σ.set "curid" (BitVec.ofNat 32 d.cid)).set "content" (BitVec.ofNat 32 content)
      have hc1 : σ1 "curid" = BitVec.ofNat 32 d.cid := by simp [σ1, Locals.set]
      have S1 : Step εR c i0 MH (fun k => UCF ucb num_proc k ∨ OF ob num_proc k) (uctxArgS cidb ucb "content" U_EBX)
          σ d σ1 d :=
        (stepUH εR c i0 hL (F := fun _ => False)
          (uctxArgU (ida := ida) (cidb := cidb) εR c i0 hU "content" (by decide) (reg := U_EBX) (by decide)
            (σ := σ) hcp hv) (fun _ h => h.elim)).widen (fun _ h => h.elim)
      have S2 := outCount_step (ida := ida) εR c i0 hL (F := fun k => UCF ucb num_proc k ∨ OF ob num_proc k)
        (σ := σ1) (d := d) hc1 hcp
      let d2 : HData := { d with devout := setAt d.devout d.cid (d.devout d.cid ++ [BitVec.ofNat 32 content]) }
      have S3 := (outPut_step (ida := ida) εR c i0 hL (σ := σ1.set "n" (BitVec.ofNat 32 (d.devout d.cid).length))
        (d := d) (i := d.cid) (v := BitVec.ofNat 32 content) (by simp [σ1, Locals.set]) hcp (by simp)
        (by simp [σ1, Locals.set])).widen (F' := fun k => UCF ucb num_proc k ∨ OF ob num_proc k) (fun _ h => Or.inr h)
      have S4 := (stepUH εR c i0 hL (d := d2) (F := UCF ucb num_proc)
        (setReg_step (ida := ida) (cidb := cidb) εR c i0 hU (F := UCF ucb num_proc) (fun _ h => h) (reg := U_EAX)
          (by decide) (ve := .const 0) (σ := ((σ1.set "n" (BitVec.ofNat 32 (d.devout d.cid).length)).set "_" 0).set "_" 0)
          (d := d2.toUData) (n := E_SUCC) rfl hcp (by exact e0))
        (fun k hk => by unfold UCF at hk; omega)).widen (F' := fun k => UCF ucb num_proc k ∨ OF ob num_proc k)
        (fun _ h => Or.inl h)
      exact ⟨_, _, S1.seq (S2.seq (S3.seq S4)), hs0⟩

end Print

end TTop
