import CertiKOS.THyp

/-!
# The hypercalls, second part: exit information, `rdmsr`, `wrmsr`

Transcribed from `coq/Trap.v` (`get_exitinfo_h`, `handle_rdmsr_h`,
`handle_wrmsr_h`).

* `getExitinfo_triple`: **`sys_hvm_get_exitinfo` refines its
  specification**: the exit reason, and for an I/O exit the port, the width
  and the flags (write, rep, string), for an EPT fault the faulting address.
* `rdmsr_triple`, `wrmsr_triple`: **`sys_hvm_handle_rdmsr` and
  `sys_hvm_handle_wrmsr` refine their specifications**: the guest's `eax`
  and `edx` get the value read, and the guest's `eip` moves past the
  instruction.

What differs: the flags are computed before the test on the exit reason (they
are locals; the registers written are the same). `rdmsr` answers 0 and
`wrmsr` changes nothing the model sees, as mCertiKOS's `rdmsr_spec` and
`wrmsr_spec` say.
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
open MALOp MPTIntro PUCtxt TTrap
open MALInit (rd_run wr_run asg_run tn ltu_eval inc_eval)
open VVMX (XSt MatchX XF)

/-! ## Specifications -/

def EXIT_REASON_INOUT : Val := 30
def EXIT_REASON_EPT_FAULT : Val := 48

def get_flags (w r s : Val) : Val :=
  let f0 : Val := if w = 0 then 0 else 0 ||| 1
  let f1 : Val := if r = 0 then f0 else f0 ||| 2
  if s = 0 then f1 else f1 ||| 4

def exit_outs (reason port width write rep str fault : Val) : List (Nat × Nat) :=
  if reason = EXIT_REASON_INOUT then
    [(U_EBX, reason.toNat), (U_ECX, port.toNat), (U_EDX, width.toNat), (U_ESI, (get_flags write rep str).toNat),
     (U_EAX, 0)]
  else if reason = EXIT_REASON_EPT_FAULT then [(U_EBX, reason.toNat), (U_ECX, fault.toNat), (U_EAX, 0)]
  else [(U_EBX, reason.toNat), (U_EAX, 0)]

def get_exitinfo_x (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  match VVMCS.vmx_get_exit_reason_spec (toV x), VVMX.vmx_get_exit_io_port_spec x, VVMX.vmx_get_io_width_spec x,
    VVMX.vmx_get_io_write_spec x, VVMX.vmx_get_exit_io_rep_spec x, VVMX.vmx_get_exit_io_str_spec x,
    VVMCS.vmx_get_exit_fault_addr_spec (toV x) with
  | some reason, some port, some width, some write, some rep, some str, some fault =>
    some (x, exit_outs reason port width write rep str fault)
  | _, _, _, _, _, _, _ => none

def rdmsr_spec (x : XSt) : Option Val := if x.ikern = true ∧ x.ihost = true then some 0 else none
def wrmsr_spec (x : XSt) : Option Val := if x.ikern = true ∧ x.ihost = true then some 0 else none

def rdmsr_x (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  match VVMX.vmx_get_reg_spec 0 x, rdmsr_spec x with
  | some _, some _ =>
    match VVMX.vmx_set_reg_spec 0 0 x with
    | some x0 =>
      match VVMX.vmx_set_reg_spec 3 0 x0 with
      | some x1 =>
        match VVMX.vmx_get_next_eip_spec x1 with
        | some ne =>
          match VVMX.vmx_set_reg_spec 8 ne.toNat x1 with
          | some x2 => some (x2, [(U_EAX, 0)])
          | none => none
        | none => none
      | none => none
    | none => none
  | _, _ => none

def wrmsr_x (x : XSt) : Option (XSt × List (Nat × Nat)) :=
  match VVMX.vmx_get_reg_spec 2 x, VVMX.vmx_get_reg_spec 0 x, VVMX.vmx_get_reg_spec 3 x, wrmsr_spec x with
  | some _, some _, some _, some _ =>
    match VVMX.vmx_get_next_eip_spec x with
    | some ne =>
      match VVMX.vmx_set_reg_spec 8 ne.toNat x with
      | some x2 => some (x2, [(U_EAX, 0)])
      | none => none
    | none => none
  | _, _, _, _ => none

def trap_get_exitinfo_spec (d : HData) : Option HData := hcall (get_exitinfo_x (toX d)) d
def trap_handle_rdmsr_spec (d : HData) : Option HData := hcall (rdmsr_x (toX d)) d
def trap_handle_wrmsr_spec (d : HData) : Option HData := hcall (wrmsr_x (toX d)) d

/-! ## The code -/

def flagS (x : Ident) (bit : Val) : Stmt APrim :=
  .ite (.var x) (.assign "flags" (.bin .bor (.var "flags") (.const bit))) .skip

def readExitS (xb vb : Nat) : Stmt APrim :=
  .seq (VVMCS.exitReasonS vb) (.seq (.assign "reason" (.var "r"))
  (.seq (VVMX.ioPortS xb) (.seq (.assign "port" (.var "r"))
  (.seq (VVMX.ioWidthS xb) (.seq (.assign "width" (.var "r"))
  (.seq (VVMX.ioWriteS xb) (.seq (.assign "write" (.var "r"))
  (.seq (VVMX.ioRepS xb) (.seq (.assign "rep" (.var "r"))
  (.seq (VVMX.ioStrS xb) (.seq (.assign "str" (.var "r"))
  (.seq (VVMCS.exitFaultAddrS vb) (.assign "fault" (.var "r"))))))))))))))

def flagsS : Stmt APrim :=
  .seq (.assign "flags" (.const 0)) (.seq (flagS "write" 1) (.seq (flagS "rep" 2) (flagS "str" 4)))

def postExitS (cidb ucb : Nat) : Stmt APrim :=
  .ite (.bin .eq (.var "reason") (.const EXIT_REASON_INOUT))
    (setsS cidb ucb [(U_EBX, .var "reason"), (U_ECX, .var "port"), (U_EDX, .var "width"), (U_ESI, .var "flags"),
      (U_EAX, .const 0)])
    (.ite (.bin .eq (.var "reason") (.const EXIT_REASON_EPT_FAULT))
      (setsS cidb ucb [(U_EBX, .var "reason"), (U_ECX, .var "fault"), (U_EAX, .const 0)])
      (setsS cidb ucb [(U_EBX, .var "reason"), (U_EAX, .const 0)]))

/-- `sys_hvm_get_exitinfo`. -/
def getExitinfoH (cidb ucb xb vb : Nat) : Stmt APrim := .seq (readExitS xb vb) (.seq flagsS (postExitS cidb ucb))

/-- `sys_hvm_handle_rdmsr`. -/
def rdmsrH (cidb ucb xb vb : Nat) : Stmt APrim :=
  .seq (.assign "reg" (.const 0)) (.seq (VVMX.getRegS xb vb) (.seq (.assign "msr" (.var "r"))
  (.seq (.assign "vlo" (.const 0)) (.seq (.assign "vhi" (.const 0))
  (.seq (.assign "reg" (.const 0)) (.seq (.assign "v" (.var "vlo")) (.seq (VVMX.setRegS xb vb)
  (.seq (.assign "reg" (.const 3)) (.seq (.assign "v" (.var "vhi")) (.seq (VVMX.setRegS xb vb)
  (.seq (VVMX.nextEipS xb vb)
  (.seq (.assign "reg" (.const 8)) (.seq (.assign "v" (.var "r")) (.seq (VVMX.setRegS xb vb)
    (errS cidb ucb 0)))))))))))))))

/-- `sys_hvm_handle_wrmsr`. -/
def wrmsrH (cidb ucb xb vb : Nat) : Stmt APrim :=
  .seq (.assign "reg" (.const 2)) (.seq (VVMX.getRegS xb vb) (.seq (.assign "msr" (.var "r"))
  (.seq (.assign "reg" (.const 0)) (.seq (VVMX.getRegS xb vb) (.seq (.assign "eax" (.var "r"))
  (.seq (.assign "reg" (.const 3)) (.seq (VVMX.getRegS xb vb) (.seq (.assign "edx" (.var "r"))
  (.seq (VVMX.nextEipS xb vb)
  (.seq (.assign "reg" (.const 8)) (.seq (.assign "v" (.var "r")) (.seq (VVMX.setRegS xb vb)
    (errS cidb ucb 0)))))))))))))

section Steps
variable {maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb : Nat}
variable (εR : REnv) (c : CPU) (i0 : Nat)

local notation "MH" => MatchH maxpage num_id cb num_proc pb ib fb ida sb tb num_chan qb cidb ipb ucb ob xb vb eb
local notation "HL" => HLayout maxpage num_id cb num_proc pb ib fb sb tb num_chan qb cidb ipb ucb ob xb vb eb

theorem flag_step {D : Type} {M : D → Region → Prop} {F : Nat → Prop} {σ : Locals} {d : D} (x : Ident) (bit : Val)
    {f v : Val} (hx : σ x = v) (hf : σ "flags" = f) :
    ∃ σ', Step εR c i0 M F (flagS x bit) σ d σ' d ∧ σ' "flags" = (if v = 0 then f else f ||| bit) ∧
      ∀ z, z ≠ "flags" → σ' z = σ z := by
  by_cases e : v = 0
  · refine ⟨σ, Step.ite_false (by show σ x = 0; rw [hx, e]) Step.skip, by rw [if_pos e, hf], fun _ _ => rfl⟩
  · refine ⟨σ.set "flags" (f ||| bit), Step.ite_true (by show ¬ σ x = 0; rw [hx]; exact e)
      (Step.assign' "flags" (by decide) _ (by simp [Expr.eval, BinOp.eval, hf])), by rw [if_neg e]; simp,
      fun z hz => by simp [Locals.set, hz]⟩

theorem val_toNat (v : Val) : BitVec.ofNat 32 v.toNat = v := by simp

/-- **`sys_hvm_get_exitinfo` refines its specification.** -/
theorem getExitinfo_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_get_exitinfo_spec d = some d1)
      (getExitinfoH cidb ucb xb vb) (fun _ d _ d' => trap_get_exitinfo_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_get_exitinfo_spec at hs
  obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
  unfold get_exitinfo_x at hb
  cases er : VVMCS.vmx_get_exit_reason_spec (toV (toX d)) with
  | none => rw [er] at hb; cases hb
  | some reason =>
  cases ep : VVMX.vmx_get_exit_io_port_spec (toX d) with
  | none => rw [er, ep] at hb; cases hb
  | some port =>
  cases ew : VVMX.vmx_get_io_width_spec (toX d) with
  | none => rw [er, ep, ew] at hb; cases hb
  | some width =>
  cases ewr : VVMX.vmx_get_io_write_spec (toX d) with
  | none => rw [er, ep, ew, ewr] at hb; cases hb
  | some write =>
  cases erp : VVMX.vmx_get_exit_io_rep_spec (toX d) with
  | none => rw [er, ep, ew, ewr, erp] at hb; cases hb
  | some rep =>
  cases est : VVMX.vmx_get_exit_io_str_spec (toX d) with
  | none => rw [er, ep, ew, ewr, erp, est] at hb; cases hb
  | some str =>
  cases ef : VVMCS.vmx_get_exit_fault_addr_spec (toV (toX d)) with
  | none => rw [er, ep, ew, ewr, erp, est, ef] at hb; cases hb
  | some fault =>
    rw [er, ep, ew, ewr, erp, est, ef] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hxv := hL.hxv; have hve := hL.hve; have heb := heb_of hL
    obtain ⟨s1, X1, h1, k1⟩ := VVMCS.exitReason_step εR c i0 (hvb_of hL)
      (F := fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC) (σ := σ) er
    let t1 := s1.set "reason" reason
    obtain ⟨s2, X2, h2, k2⟩ := VVMX.ioPort_step hxv hve heb εR c i0 (σ := t1) ep
    let t2 := s2.set "port" port
    obtain ⟨s3, X3, h3, k3⟩ := VVMX.ioWidth_step hxv hve heb εR c i0 (σ := t2) ew
    let t3 := s3.set "width" width
    obtain ⟨s4, X4, h4, k4⟩ := VVMX.ioWrite_step hxv hve heb εR c i0 (σ := t3) ewr
    let t4 := s4.set "write" write
    obtain ⟨s5, X5, h5, k5⟩ := VVMX.ioRep_step hxv hve heb εR c i0 (σ := t4) erp
    let t5 := s5.set "rep" rep
    obtain ⟨s6, X6, h6, k6⟩ := VVMX.ioStr_step hxv hve heb εR c i0 (σ := t5) est
    let t6 := s6.set "str" str
    have X7 := VVMCS.exitFaultAddr_step εR c i0 (hvb_of hL) (F := fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC)
      (σ := t6) ef
    let t7 := (t6.set "r" fault).set "fault" fault
    have RD : Step εR c i0 MH (HF ucb num_proc xb vb eb) (readExitS xb vb) σ d t7 (putX d (toX d)) := by
      have V := fun {s : Stmt APrim} {σa σb : Locals}
          (h : Step εR c i0 (VVMCS.MatchS vb) (fun k => vb + 2 ≤ k ∧ k < vb + 2 + VVMCS.NENC) s σa (toV (toX d)) σb
            (toV (toX d))) => vH (ida := ida) (num_proc := num_proc) (ucb := ucb) (ob := ob) εR c i0 hL (d := d) h
      have Xs := fun {s : Stmt APrim} {σa σb : Locals}
          (h : Step εR c i0 (MatchX xb vb eb) (XF xb vb eb) s σa (toX d) σb (toX d)) =>
        xH (ida := ida) (num_proc := num_proc) (ucb := ucb) (ob := ob) εR c i0 hL (d := d) h (VEPT.SameShape.refl _)
      exact (V X1).seq ((Step.assign' "reason" (by decide) _ (by exact h1)).seq ((Xs X2).seq
        ((Step.assign' "port" (by decide) _ (by exact h2)).seq ((Xs X3).seq
        ((Step.assign' "width" (by decide) _ (by exact h3)).seq ((Xs X4).seq
        ((Step.assign' "write" (by decide) _ (by exact h4)).seq ((Xs X5).seq
        ((Step.assign' "rep" (by decide) _ (by exact h5)).seq ((Xs X6).seq
        ((Step.assign' "str" (by decide) _ (by exact h6)).seq ((V X7).seq
        (Step.assign' "fault" (by decide) _ (by simp [Expr.eval]))))))))))))))
    have q7 : t7 "reason" = reason ∧ t7 "port" = port ∧ t7 "width" = width ∧ t7 "write" = write ∧
        t7 "rep" = rep ∧ t7 "str" = str ∧ t7 "fault" = fault := by
      simp (disch := decide) only [t7, t6, t5, t4, t3, t2, t1, Locals.set_same, Locals.set_other, k6, k5, k4, k3, k2,
        and_self]
    obtain ⟨qr, qp, qw, qwr, qrp, qst, qf⟩ := q7
    obtain ⟨f1, Y1, F1, Z1⟩ := flag_step (M := MH) (F := HF ucb num_proc xb vb eb) (d := putX d (toX d)) εR c i0
      (σ := t7.set "flags" 0) (f := 0) (v := write) "write" 1 (by rw [Locals.set_other _ _ (by decide)]; try exact qwr)
      (Locals.set_same _ _ _)
    obtain ⟨f2, Y2, F2, Z2⟩ := flag_step (M := MH) (F := HF ucb num_proc xb vb eb) (d := putX d (toX d)) εR c i0
      (σ := f1) (v := rep) "rep" 2 (by rw [Z1 _ (by decide), Locals.set_other _ _ (by decide)]; try exact qrp) F1
    obtain ⟨f3, Y3, F3, Z3⟩ := flag_step (M := MH) (F := HF ucb num_proc xb vb eb) (d := putX d (toX d)) εR c i0
      (σ := f2) (v := str) "str" 4 (by rw [Z2 _ (by decide), Z1 _ (by decide), Locals.set_other _ _ (by decide)]; try exact qst) F2
    have FL : Step εR c i0 MH (HF ucb num_proc xb vb eb) flagsS t7 (putX d (toX d)) f3 (putX d (toX d)) :=
      (Step.assign "flags" (by decide) _).seq (Y1.seq (Y2.seq Y3))
    have g : ∀ z, z ≠ "flags" → f3 z = t7 z := fun z hz => by
      rw [Z3 z hz, Z2 z hz, Z1 z hz, Locals.set_other _ _ hz]
    have hfl : f3 "flags" = get_flags write rep str := by rw [F3]; rfl
    have hr3 : f3 "reason" = reason := (g _ (by decide)).trans qr
    have val : ∀ (y : Ident) (w : Val), y ≠ "curid" → y ≠ "_" → f3 y = w →
        ∀ τ : Locals, (∀ z, z ≠ "curid" → z ≠ "_" → τ z = f3 z) → (Expr.var y).eval τ = BitVec.ofNat 32 w.toNat :=
      fun y w h1 h2 hy τ hτ => by show τ y = _; rw [hτ y h1 h2, hy, val_toNat]
    have cst : ∀ τ : Locals, (Expr.const (0 : Val)).eval τ = BitVec.ofNat 32 0 := fun _ => rfl
    unfold exit_outs at hR
    by_cases t1' : reason = EXIT_REASON_INOUT
    · rw [if_pos t1'] at hR
      obtain ⟨σ8, R, -⟩ := setsH (ida := ida) εR c i0 hL
        [(U_EBX, .var "reason", reason.toNat), (U_ECX, .var "port", port.toNat), (U_EDX, .var "width", width.toNat),
         (U_ESI, .var "flags", (get_flags write rep str).toNat), (U_EAX, .const 0, 0)] f3 (putX d (toX d)) u hcp
        (by
          intro p hm
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl
          · exact ⟨by dsimp only; decide, val _ _ (by decide) (by decide) hr3⟩
          · exact ⟨by dsimp only; decide, val _ _ (by decide) (by decide) ((g _ (by decide)).trans qp)⟩
          · exact ⟨by dsimp only; decide, val _ _ (by decide) (by decide) ((g _ (by decide)).trans qw)⟩
          · exact ⟨by dsimp only; decide, val _ _ (by decide) (by decide) hfl⟩
          · exact ⟨by dsimp only; decide, fun τ _ => rfl⟩) hR
      exact ⟨_, _, RD.seq (FL.seq (Step.ite_true (by
        show ¬ BinOp.eval .eq (f3 "reason") EXIT_REASON_INOUT = 0
        rw [hr3, t1']; simp [BinOp.eval]) R)), hs0⟩
    · rw [if_neg t1'] at hR
      have c1 : (Expr.bin .eq (.var "reason") (.const EXIT_REASON_INOUT)).eval f3 = 0 := by
        show BinOp.eval .eq (f3 "reason") EXIT_REASON_INOUT = 0
        rw [hr3]; simp [BinOp.eval, t1']
      by_cases t2' : reason = EXIT_REASON_EPT_FAULT
      · rw [if_pos t2'] at hR
        obtain ⟨σ8, R, -⟩ := setsH (ida := ida) εR c i0 hL
          [(U_EBX, .var "reason", reason.toNat), (U_ECX, .var "fault", fault.toNat), (U_EAX, .const 0, 0)] f3
          (putX d (toX d)) u hcp
          (by
            intro p hm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with rfl | rfl | rfl
            · exact ⟨by dsimp only; decide, val _ _ (by decide) (by decide) hr3⟩
            · exact ⟨by dsimp only; decide, val _ _ (by decide) (by decide) ((g _ (by decide)).trans qf)⟩
            · exact ⟨by dsimp only; decide, fun τ _ => rfl⟩) hR
        exact ⟨_, _, RD.seq (FL.seq (Step.ite_false c1 (Step.ite_true (by
          show ¬ BinOp.eval .eq (f3 "reason") EXIT_REASON_EPT_FAULT = 0
          rw [hr3, t2']; simp [BinOp.eval]) R))), hs0⟩
      · rw [if_neg t2'] at hR
        obtain ⟨σ8, R, -⟩ := setsH (ida := ida) εR c i0 hL
          [(U_EBX, .var "reason", reason.toNat), (U_EAX, .const 0, 0)] f3 (putX d (toX d)) u hcp
          (by
            intro p hm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with rfl | rfl
            · exact ⟨by dsimp only; decide, val _ _ (by decide) (by decide) hr3⟩
            · exact ⟨by dsimp only; decide, fun τ _ => rfl⟩) hR
        exact ⟨_, _, RD.seq (FL.seq (Step.ite_false c1 (Step.ite_false (by
          show BinOp.eval .eq (f3 "reason") EXIT_REASON_EPT_FAULT = 0
          rw [hr3]; simp [BinOp.eval, t2']) R))), hs0⟩

theorem setReg_flags {r v : Nat} {x x' : XSt} (h : VVMX.vmx_set_reg_spec r v x = some x') :
    x'.ikern = x.ikern ∧ x'.pg = x.pg ∧ x'.ihost = x.ihost := by
  unfold VVMX.vmx_set_reg_spec at h
  split at h
  · split at h
    all_goals first | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩) | cases h
  · cases h

theorem toX_putX {d : HData} {x : XSt} (h : x.ikern = d.ikern ∧ x.pg = d.pg ∧ x.ihost = d.ihost) :
    toX (putX d x) = x := by
  obtain ⟨h1, h2, h3⟩ := h
  cases x; simp only at h1 h2 h3; subst h1 h2 h3; rfl

/-- A step of the VMX layer from a state the top state's flags agree with. -/
theorem xH' (hL : HL) {s : Stmt APrim} {σ σ' : Locals} {d : HData} {x x' : XSt}
    (hfl : x.ikern = d.ikern ∧ x.pg = d.pg ∧ x.ihost = d.ihost)
    (h : Step εR c i0 (MatchX xb vb eb) (XF xb vb eb) s σ x σ' x') (hsh : VEPT.SameShape x.ept x'.ept) :
    Step εR c i0 MH (HF ucb num_proc xb vb eb) s σ (putX d x) σ' (putX d x') := by
  have h' : Step εR c i0 (MatchX xb vb eb) (XF xb vb eb) s σ (toX (putX d x)) σ' x' := by
    rw [toX_putX hfl]; exact h
  exact xH (ida := ida) εR c i0 hL h' hsh

/-- **`sys_hvm_handle_rdmsr` refines its specification.** -/
theorem rdmsr_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_handle_rdmsr_spec d = some d1)
      (rdmsrH cidb ucb xb vb) (fun _ d _ d' => trap_handle_rdmsr_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_handle_rdmsr_spec at hs
  obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
  unfold rdmsr_x at hb
  have hxv := hL.hxv; have hve := hL.hve; have heb := heb_of hL
  cases eg : VVMX.vmx_get_reg_spec 0 (toX d) with
  | none => simp only [eg] at hb; cases hb
  | some msr =>
  cases em : rdmsr_spec (toX d) with
  | none => simp only [eg, em] at hb; cases hb
  | some val =>
  cases e0 : VVMX.vmx_set_reg_spec 0 0 (toX d) with
  | none => simp only [eg, em, e0] at hb; cases hb
  | some x0 =>
  cases e1 : VVMX.vmx_set_reg_spec 3 0 x0 with
  | none => simp only [eg, em, e0, e1] at hb; cases hb
  | some x1 =>
  cases en : VVMX.vmx_get_next_eip_spec x1 with
  | none => simp only [eg, em, e0, e1, en] at hb; cases hb
  | some ne =>
  cases e2 : VVMX.vmx_set_reg_spec 8 ne.toNat x1 with
  | none => simp only [eg, em, e0, e1, en, e2] at hb; cases hb
  | some x2 =>
    simp only [eg, em, e0, e1, en, e2, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    -- the VMX state through the handler
    let d0 := putX d x0
    let d1 := putX d x1
    let σ1 := σ.set "reg" 0
    have G := xH (ida := ida) (num_proc := num_proc) (ucb := ucb) (ob := ob) εR c i0 hL (d := d)
      (VVMX.getReg_step hxv hve heb εR c i0 (σ := σ1) (by simp [σ1] <;> rfl) eg) (VEPT.SameShape.refl _)
    let σ6 := (((((σ1.set "r" msr).set "msr" msr).set "vlo" 0).set "vhi" 0).set "reg" 0).set "v" 0
    have S1 := xH (ida := ida) (num_proc := num_proc) (ucb := ucb) (ob := ob) εR c i0 hL (d := putX d (toX d))
      (VVMX.setReg_step hxv hve heb εR c i0 (σ := σ6) (by simp [σ6] <;> rfl) (by simp [σ6] <;> rfl) e0)
      (setReg_ept e0)
    let σ8 := ((σ6.set "_" 0).set "reg" 3).set "v" 0
    have f0 := setReg_flags e0
    have f1 := setReg_flags e1
    have fl0 : x0.ikern = d.ikern ∧ x0.pg = d.pg ∧ x0.ihost = d.ihost := f0
    have fl1 : x1.ikern = d.ikern ∧ x1.pg = d.pg ∧ x1.ihost = d.ihost :=
      ⟨f1.1.trans f0.1, f1.2.1.trans f0.2.1, f1.2.2.trans f0.2.2⟩
    have S2 := xH' (ida := ida) (num_proc := num_proc) (ucb := ucb) (ob := ob) εR c i0 hL (d := d) fl0
      (VVMX.setReg_step hxv hve heb εR c i0 (σ := σ8) (by simp [σ8] <;> rfl) (by simp [σ8] <;> rfl) e1)
      (setReg_ept e1)
    obtain ⟨σ9, N, hn, -⟩ := VVMX.nextEip_step hxv hve heb εR c i0 (σ := σ8.set "_" 0) en
    have N' := xH' (ida := ida) (num_proc := num_proc) (ucb := ucb) (ob := ob) εR c i0 hL (d := d) fl1 N (VEPT.SameShape.refl _)
    let σ11 := (σ9.set "reg" 8).set "v" ne
    have S3 := xH' (ida := ida) (num_proc := num_proc) (ucb := ucb) (ob := ob) εR c i0 hL (d := d) fl1
      (VVMX.setReg_step hxv hve heb εR c i0 (σ := σ11) (by simp [σ11] <;> rfl) (by simp [σ11]) e2) (setReg_ept e2)
    obtain ⟨σ12, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ11.set "_" 0) (d := putX d x2) hcp hR
    exact ⟨_, _, (Step.assign "reg" (by decide) _).seq (G.seq ((Step.assign "msr" (by decide) _).seq
      ((Step.assign "vlo" (by decide) _).seq ((Step.assign "vhi" (by decide) _).seq
      ((Step.assign "reg" (by decide) _).seq ((Step.assign' "v" (by decide) _ (by simp [Expr.eval])).seq (S1.seq
      ((Step.assign "reg" (by decide) _).seq ((Step.assign' "v" (by decide) _ (by simp [Expr.eval, Locals.set, σ6])).seq
      (S2.seq (N'.seq ((Step.assign "reg" (by decide) _).seq
      ((Step.assign' "v" (by decide) _ (by simp [Expr.eval, Locals.set, hn])).seq (S3.seq R)))))))))))))), hs0⟩

/-- **`sys_hvm_handle_wrmsr` refines its specification.** -/
theorem wrmsr_triple (hL : HL) :
    Triple εR c i0 MH (HF ucb num_proc xb vb eb)
      (fun _ d => d.cid < num_proc ∧ ∃ d1, trap_handle_wrmsr_spec d = some d1)
      (wrmsrH cidb ucb xb vb) (fun _ d _ d' => trap_handle_wrmsr_spec d = some d') := by
  refine Step.triple (fun σ d ⟨hcp, d', hs⟩ => ?_)
  have hs0 := hs
  unfold trap_handle_wrmsr_spec at hs
  obtain ⟨x', o, u, hb, hR, rfl⟩ := hcall_some hs
  unfold wrmsr_x at hb
  have hxv := hL.hxv; have hve := hL.hve; have heb := heb_of hL
  cases ec : VVMX.vmx_get_reg_spec 2 (toX d) with
  | none => simp only [ec] at hb; cases hb
  | some msr =>
  cases ea : VVMX.vmx_get_reg_spec 0 (toX d) with
  | none => simp only [ec, ea] at hb; cases hb
  | some eax =>
  cases ed : VVMX.vmx_get_reg_spec 3 (toX d) with
  | none => simp only [ec, ea, ed] at hb; cases hb
  | some edx =>
  cases ew : wrmsr_spec (toX d) with
  | none => simp only [ec, ea, ed, ew] at hb; cases hb
  | some w =>
  cases en : VVMX.vmx_get_next_eip_spec (toX d) with
  | none => simp only [ec, ea, ed, ew, en] at hb; cases hb
  | some ne =>
  cases e2 : VVMX.vmx_set_reg_spec 8 ne.toNat (toX d) with
  | none => simp only [ec, ea, ed, ew, en, e2] at hb; cases hb
  | some x2 =>
    simp only [ec, ea, ed, ew, en, e2, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have X := fun {s : Stmt APrim} {σa σb : Locals} {x : XSt}
        (h : Step εR c i0 (MatchX xb vb eb) (XF xb vb eb) s σa (toX d) σb x) (hsh : VEPT.SameShape d.ept x.ept) =>
      xH (ida := ida) (num_proc := num_proc) (ucb := ucb) (ob := ob) εR c i0 hL (d := d) h hsh
    let σ1 := σ.set "reg" 2
    have G1 := X (VVMX.getReg_step hxv hve heb εR c i0 (σ := σ1) (by simp [σ1] <;> rfl) ec) (VEPT.SameShape.refl _)
    let σ2 := ((σ1.set "r" msr).set "msr" msr).set "reg" 0
    have G2 := X (VVMX.getReg_step hxv hve heb εR c i0 (σ := σ2) (by simp [σ2] <;> rfl) ea) (VEPT.SameShape.refl _)
    let σ3 := ((σ2.set "r" eax).set "eax" eax).set "reg" 3
    have G3 := X (VVMX.getReg_step hxv hve heb εR c i0 (σ := σ3) (by simp [σ3] <;> rfl) ed) (VEPT.SameShape.refl _)
    let σ4 := (σ3.set "r" edx).set "edx" edx
    obtain ⟨σ9, N, hn, -⟩ := VVMX.nextEip_step hxv hve heb εR c i0 (σ := σ4) en
    let σ11 := (σ9.set "reg" 8).set "v" ne
    have S3 := X (VVMX.setReg_step hxv hve heb εR c i0 (σ := σ11) (by simp [σ11] <;> rfl) (by simp [σ11]) e2)
      (setReg_ept e2)
    obtain ⟨σ12, R⟩ := errH (ida := ida) εR c i0 hL (σ := σ11.set "_" 0) (d := putX d x2) hcp hR
    exact ⟨_, _, (Step.assign "reg" (by decide) _).seq (G1.seq ((Step.assign "msr" (by decide) _).seq
      ((Step.assign "reg" (by decide) _).seq (G2.seq ((Step.assign "eax" (by decide) _).seq
      ((Step.assign "reg" (by decide) _).seq (G3.seq ((Step.assign "edx" (by decide) _).seq
      ((X N (VEPT.SameShape.refl _)).seq ((Step.assign "reg" (by decide) _).seq
      ((Step.assign' "v" (by decide) _ (by simp [Expr.eval, Locals.set, hn])).seq (S3.seq R)))))))))))), hs0⟩

end Steps

end TTop
