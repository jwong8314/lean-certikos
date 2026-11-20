import CertiKOS.VVMX

/-!
# `vmx_init`, ported from the Coq version

Transcribed from `coq/Init.v`: the virtual machine's part of mCertiKOS's
`vmx_init` (`objects/ObjVMX.v`, `objects/ObjVMCS.v`): `vmcs_set_defaults`,
the VMCS revision identifier, the `vmx` structure's first values, and
`ept_init`.

* `defaults`: the fields `vmcs_set_defaults` writes, in the C's order, each
  with its value as an expression over the arguments (`params`) or a
  constant. A 64-bit field is its two words. What the processor would give
  (`rcr0`, `rcr3`, `rcr4`, `rdmsr`) is 0, mCertiKOS's model of it.
* `vmx_first`: `memset(&vmx, 0, …)`, then `g_rip = 0xfff0`, `vpid = 1`,
  `g_dr6 = 0xffff0ff0`.
* `vmx_init0_spec`: the VMCS gets the defaults and revision identifier 0, the
  `vmx` structure its first values, the EPT the entry 0 for every guest page,
  and `init` is set.
* `vwrites_step`, `xwrites_step`, `revid_step`, `eptInitX_step`: the four
  parts as steps of the VMX state. `vmxInit_step`: **`vmx_init` refines
  `vmx_init0_spec`.**

What differs from mCertiKOS: as in `coq/Init.v`, only the virtual machine's
part; the boot of the process layers is verified there.
-/

set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace VVMX

open ClightL Ticket
open LockArray (APrim lkE)
open LockRegion (RLog REnv Region setCell)
open LockRegionCPU KernFrame Layer
open MALOp MPTIntro
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)
open VVMCS (NENC MatchV vmreadS vmwriteS encE eval_enc)
open VEPT (NPG MatchE)

/-! ## The values -/

def params : List Ident :=
  ["pinbased", "procbased", "procbased2", "exit_ctls", "entry_ctls", "host_rip", "tss", "gdt", "idt",
   "pml4", "vpid", "msr_bitmap", "cr0_ones", "cr0_zeros", "cr4_ones", "cr4_zeros", "io_bitmap_a", "io_bitmap_b"]

def K (n : Nat) : Expr := .const (BitVec.ofNat 32 n)

/-- `vmcs_set_defaults`, field by field (`coq/Init.v`). -/
def defaults : List (Nat × Expr) :=
  [ (16384, .var "pinbased"), (16386, .var "procbased"), (16414, .var "procbased2"),
    (16396, .var "exit_ctls"), (16402, .var "entry_ctls"),
    (27670, .var "host_rip"),
    (27648, K 0), (27650, K 0), (27652, K 0),
    (3072, K 16), (3074, K 8), (3076, K 16), (3078, K 16), (3080, K 16), (3082, K 16), (3084, K 40),
    (27654, K 0), (27656, K 0),
    (27658, .var "tss"), (27660, .var "gdt"), (27662, .var "idt"),
    (19456, K 0), (27664, K 0), (27666, K 0),
    (11268, K 0), (11269, K 0), (11264, K 0), (11265, K 0), (11266, K 0), (11267, K 0),
    (26624, K 1610612784), (26626, K 0), (26628, K 8192),
    (26650, K 1024),
    (10244, K 459782), (10245, K 459782),
    (18474, K 0), (26660, K 0), (26662, K 0),
    (10242, K 0), (10243, K 0),
    (8218, .bin .bor (.var "pml4") (K 30)), (8219, K 0),
    (0, .var "vpid"),
    (8196, .var "msr_bitmap"), (8197, K 0),
    (10240, K 4294967295), (10241, K 4294967295),
    (24576, .bin .bor (.var "cr0_ones") (.var "cr0_zeros")), (24580, .var "cr0_ones"),
    (24578, .bin .bor (.var "cr4_ones") (.var "cr4_zeros")), (24582, .var "cr4_ones"),
    (8192, .var "io_bitmap_a"), (8193, K 0), (8194, .var "io_bitmap_b"), (8195, K 0),
    (18470, K 0), (18468, K 0), (26658, K 0), (16406, K 0) ]

def vmx_first (i : Nat) : Val :=
  if i = VMX_G_RIP' then 65520 else if i = 26 then 1 else if i = 21 then 4294905840 else 0

def vmx_list : List (Nat × Val) := (List.range 36).map fun i => (i, vmx_first i)

def writes : List (Nat × Val) → (Nat → Option Val) → Nat → Option Val
  | [], f => f
  | (k, v) :: t, f => writes t (setAt f k (some v))

/-! ## Specification -/

def vmx_init0_spec (info : Locals) (x : XSt) : Option XSt :=
  if flags x ∧ x.init = false then
    match VEPT.ept_init0_spec (toE x) with
    | some e =>
      some ⟨x.ikern, x.pg, x.ihost, true, writes vmx_list x.vmx,
        ⟨some 0, x.vmcs.abrtid, writes (defaults.map fun p => (p.1, p.2.eval info)) x.vmcs.data⟩, e.ept⟩
    | none => none
  else none

/-! ## The code -/

def vwritesS (vb : Nat) : List (Nat × Expr) → Stmt APrim
  | [] => .skip
  | (k, e) :: t => .seq (vmwriteS vb (K k) e) (vwritesS vb t)

def xwritesS (xb : Nat) : List (Nat × Val) → Stmt APrim
  | [] => .skip
  | (k, v) :: t => .seq (xstoreS xb k (.const v)) (xwritesS xb t)

def revidS (vb : Nat) : Stmt APrim := .call "_" .push [lkE, K vb, K 0]

/-- `vmcs_set_defaults(…); vmcs->identifier = rdmsr(MSR_VMX_BASIC); memset(&vmx, 0, …); vmx.g_rip = 0xfff0;
… ept_init();` -/
def vmxInitS (xb vb eb : Nat) : Stmt APrim :=
  .seq (vwritesS vb defaults) (.seq (revidS vb) (.seq (xwritesS xb vmx_list) (VEPT.eptInitS eb)))

def Expr.vars : Expr → List Ident
  | .const _ => []
  | .var x => [x]
  | .bin _ a b => Expr.vars a ++ Expr.vars b

theorem eval_agree {σ τ : Locals} : ∀ e : Expr, (∀ x ∈ Expr.vars e, σ x = τ x) → e.eval σ = e.eval τ
  | .const _, _ => rfl
  | .var x, h => h x (by simp [Expr.vars])
  | .bin o a b, h => by
    show o.eval (a.eval σ) (b.eval σ) = o.eval (a.eval τ) (b.eval τ)
    rw [eval_agree a (fun x hx => h x (by simp [Expr.vars, hx])),
      eval_agree b (fun x hx => h x (by simp [Expr.vars, hx]))]

theorem defaults_ok : ∀ p ∈ defaults, p.1 < NENC ∧ ∀ x ∈ Expr.vars p.2, x ∈ params := by
  intro p hp
  simp only [defaults, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;> subst h <;> refine ⟨by unfold NENC; omega, ?_⟩ <;>
    simp [Expr.vars, K, params]

section Code
variable {xb vb eb : Nat}
variable (hxv : xb + 36 ≤ vb) (hve : vb + 65540 ≤ eb) (heb : eb + 1048576 ≤ 2 ^ 32)
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MX" => MatchX xb vb eb
local notation "XFP" => XF xb vb eb

include hxv hve heb

theorem vwrites_step (info : Locals) : ∀ (l : List (Nat × Expr)) (σ : Locals) (x : XSt),
    (∀ y ∈ params, σ y = info y) → (∀ p ∈ l, p.1 < NENC ∧ ∀ y ∈ Expr.vars p.2, y ∈ params) →
    ∃ σ', Step εR c i0 MX XFP (vwritesS vb l) σ x σ'
      (setData x (writes (l.map fun p => (p.1, p.2.eval info)) x.vmcs.data)) ∧ ∀ y ∈ params, σ' y = info y
  | [], σ, x, hσ, _ => ⟨σ, Step.skip, hσ⟩
  | (k, e) :: t, σ, x, hσ, hl => by
    obtain ⟨hk, hv⟩ := hl (k, e) (List.mem_cons_self ..)
    have W := vwrite_step hxv hve heb εR c i0 (σ := σ) (d := x) (e := K k) (v := e) (k := k)
      (w := e.eval info) rfl hk (eval_agree e (fun y hy => hσ y (hv y hy)))
    obtain ⟨σ', S, h'⟩ := vwrites_step info t (σ.set "_" 0) (setData x (setAt x.vmcs.data k (some (e.eval info))))
      (fun y hy => by rw [Locals.set_other _ _ (by intro h; subst h; simp [params] at hy)]; exact hσ y hy)
      (fun p hp => hl p (List.mem_cons_of_mem _ hp))
    exact ⟨σ', W.seq S, h'⟩

theorem xwrites_step : ∀ (l : List (Nat × Val)) (σ : Locals) (x : XSt), (∀ p ∈ l, p.1 < VMX_Size') →
    ∃ σ', Step εR c i0 MX XFP (xwritesS xb l) σ x σ' (setVmx x (writes l x.vmx))
  | [], σ, x, _ => ⟨σ, Step.skip⟩
  | (k, v) :: t, σ, x, hl => by
    have W := xstore_step hxv hve heb εR c i0 (σ := σ) (d := x) (i := k) (e := .const v) (w := v)
      (hl (k, v) (List.mem_cons_self ..)) rfl
    obtain ⟨σ', S⟩ := xwrites_step t (σ.set "_" 0) (setVmx x (setAt x.vmx k (some v)))
      (fun p hp => hl p (List.mem_cons_of_mem _ hp))
    exact ⟨σ', W.seq S⟩

omit hxv hve heb in
theorem vmx_list_ok : ∀ p ∈ vmx_list, p.1 < VMX_Size' := by
  intro p hp
  simp only [vmx_list, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  unfold VMX_Size'; exact hi

/-- `vmcs->identifier = 0`. -/
theorem revid_step {σ : Locals} {x : XSt} :
    Step εR c i0 MX XFP (revidS vb) σ x (σ.set "_" 0) { x with vmcs := { x.vmcs with revid := some 0 } } := by
  refine ⟨Locals.set_other _ _ (by decide), fun l b hlk hcs hM => ?_⟩
  obtain ⟨l', hr, hcs'⟩ := wr_run (εR := εR) hcs hlk (K vb) (K 0) (n := vb) (v := 0)
    (tn (by omega)) rfl
  obtain ⟨h1, ⟨v1, v2, v3⟩, h3⟩ := hM
  refine ⟨l', _, hr, hcs', ⟨fun i w hi hw => ?_, ⟨fun r hr => ?_, fun a ha => ?_, fun e w he hw => ?_⟩,
    matchE_frame h3 (fun a h1' h2' => sc_ne _ _ (by omega))⟩,
    fun k hk => sc_ne _ _ (fun e => hk (Or.inr (Or.inl ⟨by omega, by unfold NENC; omega⟩)))⟩
  · unfold VMX_Size' at hi; rw [sc_ne _ _ (by omega)]; exact h1 i w (by unfold VMX_Size'; omega) hw
  · cases hr; exact sc_eq _ _ _
  · rw [sc_ne _ _ (by omega)]; exact v2 a ha
  · rw [sc_ne _ _ (by omega)]; exact v3 e w he hw

/-- `ept_init()` as a step of the VMX state. -/
theorem eptInitX_step {σ : Locals} {x : XSt} {e : VEPT.VData} (hs : VEPT.ept_init0_spec (toE x) = some e) :
    ∃ σ', Step εR c i0 MX XFP (VEPT.eptInitS eb) σ x σ' (setEpt x e.ept) := by
  have hfl : VEPT.flags (toE x) := by
    unfold VEPT.ept_init0_spec at hs; split at hs
    · assumption
    · cases hs
  obtain ⟨σ', S⟩ := VEPT.eptInit_step (eb := eb) (F := VEPT.NPG |> fun n k => eb ≤ k ∧ k < eb + n) εR c i0
    (by unfold NPG; omega) (fun k h1 h2 => ⟨h1, h2⟩) σ (toE x) hfl
  refine ⟨σ', S.1, fun l b hlk hcs hM => ?_⟩
  obtain ⟨l1, b1, r1, c1, m1, f1⟩ := S.2 l b hlk hcs (fun g hg => absurd hg (Nat.not_lt_zero _))
  refine ⟨l1, b1, r1, c1, ⟨fun i w hi hw => ?_, matchV_frame hM.2.1 (fun a h1 h2 => f1 a (fun h => ?_)),
    fun g v hg hl => VEPT.eptInit_match (d := toE x) m1 hs g v hg hl⟩, fun k hk => f1 k (fun h => hk (Or.inr (Or.inr h)))⟩
  · unfold VMX_Size' at hi
    rw [f1 _ (fun h => by unfold NPG at h; omega)]; exact hM.1 i w (by unfold VMX_Size'; omega) hw
  · unfold NENC at h2; unfold NPG at h; omega

/-- **`vmx_init` refines `vmx_init0_spec`.** The arguments of
`vmcs_set_defaults` are in the locals. -/
theorem vmxInit_step (info : Locals) {σ : Locals} {x x' : XSt} (hσ : ∀ y ∈ params, σ y = info y)
    (hs : vmx_init0_spec info x = some x') : ∃ σ', Step εR c i0 MX XFP (vmxInitS xb vb eb) σ x σ' x' := by
  unfold vmx_init0_spec at hs
  by_cases hc : flags x ∧ x.init = false
  · rw [if_pos hc] at hs
    cases he : VEPT.ept_init0_spec (toE x) with
    | none => rw [he] at hs; cases hs
    | some e =>
      rw [he] at hs; simp only [Option.some.injEq] at hs; subst hs
      obtain ⟨σ1, S1, -⟩ := vwrites_step hxv hve heb εR c i0 info defaults σ x hσ defaults_ok
      let x1 := setData x (writes (defaults.map fun p => (p.1, p.2.eval info)) x.vmcs.data)
      let x2 : XSt := { x1 with vmcs := { x1.vmcs with revid := some 0 } }
      have S2 := revid_step hxv hve heb εR c i0 (σ := σ1) (x := x1)
      obtain ⟨σ3, S3⟩ := xwrites_step hxv hve heb εR c i0 vmx_list (σ1.set "_" 0) x2 vmx_list_ok
      have he' : VEPT.ept_init0_spec (toE (setVmx x2 (writes vmx_list x2.vmx))) = some e := he
      obtain ⟨σ4, S4⟩ := eptInitX_step hxv hve heb εR c i0 (σ := σ3) he'
      exact ⟨σ4, Step.post (S1.seq (S2.seq (S3.seq S4))) (fun b h => by
        obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1, h2, h3⟩)⟩
  · rw [if_neg hc] at hs; cases hs

end Code

end VVMX
