(** * The hypercalls: the trap-layer handlers of the virtual machine

    Ported from [objects/ObjTrap.v]: [trap_get_reg_spec], [trap_set_reg_spec],
    [trap_set_seg_spec], [trap_get_next_eip_spec], [trap_inject_event_spec],
    [trap_check_pending_event_spec], [trap_check_int_shadow_spec],
    [trap_intercept_int_window_spec], [trap_get_tsc_offset_spec],
    [trap_set_tsc_offset_spec], [trap_get_exitinfo_spec],
    [trap_handle_rdmsr_spec], [trap_handle_wrmsr_spec], [trap_mmap_spec]; and
    from [objects/ObjVMCS.v]: [rdmsr_spec], [wrmsr_spec].

    In the public sources these specifications are inside a comment: the
    verified dispatcher does not reach them. The C code is in [trap/sys_*.c]
    and quoted in [ObjTrap.v]; the code here follows it.

    A handler reads its arguments from the caller's user context and writes
    its results and error code back. Here, as for the processor's registers
    in [VMX.v], the arguments are locals (["reg"], ["v"], ...) and the results
    are the locals ["ret1"] ... ["ret4"] and ["errno"]; the Lean port adds the
    accesses to the user context, which the process layers already verify.
    A specification returns the new state and the list of results it writes.

    What differs:
    - [rdmsr] and [wrmsr] are instructions. mCertiKOS's model of them
      ([rdmsr_spec], [wrmsr_spec]) answers 0; the code here does the same.
    - [sys_hvm_mmap] first finds (or makes) the host page behind the caller's
      address in its page table. That part is the process layers' and is in
      the Lean port; here the handler starts from the host address.
    - [trap_get_tsc_offset_spec] splits the 64-bit offset into its two words;
      the theorem assumes the VMCS holds words ([Words]). *)

From Stdlib Require Import ZArith String Lia Bool List.
From VCoq Require Import Lang.
From VCoq Require EPT VMCS VMX.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope bool_scope.
Open Scope Z_scope.

Definition E_SUCC := 0.
Definition E_INVAL_REG := 6.
Definition E_INVAL_SEG := 7.
Definition EXIT_REASON_INOUT := 30.
Definition EXIT_REASON_EPT_FAULT := 48.
Definition C_GUEST_EAX := 0.
Definition C_GUEST_ECX := 2.
Definition C_GUEST_EDX := 3.
Definition C_GUEST_EIP := 8.
Definition C_GUEST_MAX_REG := 14.
Definition C_GUEST_MAX_SEG_DESC := 10.

(** The results a handler writes, in order. *)
Definition outs := list (string * Z).

(** ** Specifications ([ObjTrap.v], [ObjVMCS.v]) *)

Section Specs.
Variable maxpage : Z.

(** A VMCS function on the combined state. *)
Definition onC (r : option VMCS.VSt) (d : VMX.XSt) : option VMX.XSt :=
  match r with Some v => Some (VMX.set_xvmcs d (VMCS.vmcs v)) | None => None end.

Definition rdmsr_spec (r : Z) (d : VMX.XSt) : option Z :=
  if VMX.xikern d && VMX.xihost d then Some 0 else None.

Definition wrmsr_spec (r v : Z) (d : VMX.XSt) : option Z :=
  if VMX.xikern d && VMX.xihost d then Some 0 else None.

Definition trap_get_reg_spec (reg : Z) (d : VMX.XSt) : option (VMX.XSt * outs) :=
  if (0 <=? reg) && (reg <? C_GUEST_MAX_REG) then
    match VMX.vmx_get_reg_spec reg d with
    | Some v => Some (d, [("ret1", v); ("errno", E_SUCC)])
    | None => None
    end
  else Some (d, [("errno", E_INVAL_REG)]).

Definition trap_set_reg_spec (reg v : Z) (d : VMX.XSt) : option (VMX.XSt * outs) :=
  if (0 <=? reg) && (reg <? C_GUEST_MAX_REG) then
    match VMX.vmx_set_reg_spec reg v d with
    | Some d' => Some (d', [("errno", E_SUCC)])
    | None => None
    end
  else Some (d, [("errno", E_INVAL_REG)]).

Definition trap_set_seg_spec (seg sel base lim ar : Z) (d : VMX.XSt) : option (VMX.XSt * outs) :=
  if (0 <=? seg) && (seg <? C_GUEST_MAX_SEG_DESC) then
    match onC (VMCS.vmx_set_desc_spec seg sel base lim ar (VMX.toC d)) d with
    | Some d' => Some (d', [("errno", E_SUCC)])
    | None => None
    end
  else Some (d, [("errno", E_INVAL_SEG)]).

Definition trap_get_next_eip_spec (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match VMX.vmx_get_next_eip_spec d with
  | Some neip =>
    if (0 <=? neip) && (neip <=? EPT.max_unsigned) then Some (d, [("ret1", neip); ("errno", E_SUCC)])
    else None
  | None => None
  end.

Definition trap_inject_event_spec (type vector errcode ev : Z) (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match onC (VMCS.vmx_inject_event_spec type vector errcode ev (VMX.toC d)) d with
  | Some d' => Some (d', [("errno", E_SUCC)])
  | None => None
  end.

Definition trap_check_pending_event_spec (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match VMCS.vmx_check_pending_event_spec (VMX.toC d) with
  | Some ev => Some (d, [("ret1", ev); ("errno", E_SUCC)])
  | None => None
  end.

Definition trap_check_int_shadow_spec (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match VMCS.vmx_check_int_shadow_spec (VMX.toC d) with
  | Some sh => Some (d, [("ret1", sh); ("errno", E_SUCC)])
  | None => None
  end.

Definition trap_intercept_int_window_spec (enable : Z) (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match onC (VMCS.vmx_set_intercept_intwin_spec enable (VMX.toC d)) d with
  | Some d' => Some (d', [("errno", E_SUCC)])
  | None => None
  end.

Definition trap_get_tsc_offset_spec (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match VMCS.vmx_get_tsc_offset_spec (VMX.toC d) with
  | Some ofs => Some (d, [("ret1", ofs / W); ("ret2", ofs mod W); ("errno", E_SUCC)])
  | None => None
  end.

Definition trap_set_tsc_offset_spec (hi lo : Z) (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match onC (VMCS.vmx_set_tsc_offset_spec (hi * W + lo) (VMX.toC d)) d with
  | Some d' => Some (d', [("errno", E_SUCC)])
  | None => None
  end.

Definition get_flags (write rep str : Z) : Z :=
  let f0 := if write =? 0 then 0 else wor 0 1 in
  let f1 := if rep =? 0 then f0 else wor f0 2 in
  if str =? 0 then f1 else wor f1 4.

Definition exitinfo_outs (reason port width write rep str fault : Z) : outs :=
  if reason =? EXIT_REASON_INOUT then
    [("ret1", reason); ("ret2", port); ("ret3", width); ("ret4", get_flags write rep str); ("errno", E_SUCC)]
  else if reason =? EXIT_REASON_EPT_FAULT then [("ret1", reason); ("ret2", fault); ("errno", E_SUCC)]
  else [("ret1", reason); ("errno", E_SUCC)].

Definition trap_get_exitinfo_spec (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match VMCS.vmx_get_exit_reason_spec (VMX.toC d), VMX.vmx_get_exit_io_port_spec d,
        VMX.vmx_get_io_width_spec d, VMX.vmx_get_io_write_spec d,
        VMX.vmx_get_exit_io_rep_spec d, VMX.vmx_get_exit_io_str_spec d,
        VMCS.vmx_get_exit_fault_addr_spec (VMX.toC d) with
  | Some reason, Some port, Some width, Some write, Some rep, Some str, Some fault =>
    Some (d, exitinfo_outs reason port width write rep str fault)
  | _, _, _, _, _, _, _ => None
  end.

Definition trap_handle_rdmsr_spec (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match VMX.vmx_get_reg_spec C_GUEST_EAX d with
  | Some msr =>
    match rdmsr_spec msr d with
    | Some val =>
      match VMX.vmx_set_reg_spec C_GUEST_EAX (val mod W) d with
      | Some d0 =>
        match VMX.vmx_set_reg_spec C_GUEST_EDX (val / W) d0 with
        | Some d1 =>
          match VMX.vmx_get_next_eip_spec d1 with
          | Some neip =>
            if (0 <=? neip) && (neip <=? EPT.max_unsigned) then
              match VMX.vmx_set_reg_spec C_GUEST_EIP neip d1 with
              | Some d2 => Some (d2, [("errno", E_SUCC)])
              | None => None
              end
            else None
          | None => None
          end
        | None => None
        end
      | None => None
      end
    | None => None
    end
  | None => None
  end.

Definition trap_handle_wrmsr_spec (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match VMX.vmx_get_reg_spec C_GUEST_ECX d, VMX.vmx_get_reg_spec C_GUEST_EAX d,
        VMX.vmx_get_reg_spec C_GUEST_EDX d with
  | Some msr, Some eax, Some edx =>
    match wrmsr_spec msr (edx * W + eax) d with
    | Some _ =>
      match VMX.vmx_get_next_eip_spec d with
      | Some neip =>
        if (0 <=? neip) && (neip <=? EPT.max_unsigned) then
          match VMX.vmx_set_reg_spec C_GUEST_EIP neip d with
          | Some d0 => Some (d0, [("errno", E_SUCC)])
          | None => None
          end
        else None
      | None => None
      end
    | None => None
    end
  | _, _, _ => None
  end.

(** [sys_hvm_mmap] from the host address on. *)
Definition trap_mmap_spec (gpa hpa memtype : Z) (d : VMX.XSt) : option (VMX.XSt * outs) :=
  match VMX.vmx_set_mmap_spec maxpage gpa hpa memtype d with
  | Some (d', _) => Some (d', [("errno", E_SUCC)])
  | None => None
  end.

End Specs.

(** ** The code *)

Section Code.
Variables xb vb eb : Z.
Hypothesis hxb : 0 <= xb.
Hypothesis hxv : xb + VMX.VMX_Size' <= vb.
Hypothesis hve : vb + 65540 <= eb.
Hypothesis heb2 : eb + EPT.NPG <= W.
Variable maxpage : Z.
Hypothesis hmp : maxpage <= EPT.NPG.

Notation MatchX := (VMX.MatchX xb vb eb).

Lemma hvb : 0 <= vb.
Proof. unfold VMX.VMX_Size' in *; lia. Qed.
Lemma hvb2 : vb + 65540 <= W.
Proof. unfold EPT.NPG in *; lia. Qed.

(** The results are in the locals. *)
Definition Outs (s : locals) (o : outs) : Prop := forall x v, In (x, v) o -> s x = v.

(** A reader of the VMCS reads the VMCS block of the combined state. *)
Lemma matchC : forall d m, MatchX d m -> VMCS.MatchS vb (VMX.toC d) m.
Proof. intros d m (_ & H2 & _); exact H2. Qed.

(** A writer of the VMCS leaves the other two blocks alone. *)
Lemma liftC : forall d m m' v', MatchX d m -> VMCS.MatchS vb v' m' -> VMCS.FrameV vb m m' ->
  MatchX (VMX.set_xvmcs d (VMCS.vmcs v')) m'.
Proof.
  intros d m m' v' (H1 & H2 & H3) HM F; split; [|split].
  - intros i v Hi Hv; simpl in Hv; rewrite F by (unfold VMX.VMX_Size' in *; lia); apply H1; auto.
  - exact HM.
  - intros g h Hg Hl; rewrite F by (unfold EPT.NPG, VMCS.NENC in *; lia); apply H3; auto.
Qed.

Lemma onC_some : forall r d d', onC r d = Some d' -> exists v, r = Some v /\ d' = VMX.set_xvmcs d (VMCS.vmcs v).
Proof. intros [v|] d d' H; simpl in H; [inversion H; eauto | discriminate]. Qed.

(** The tail of every handler: [ret1 = r; errno = E_SUCC;] and the like. *)
Lemma outs2 : forall s x1 v1, Outs (lset (lset s x1 v1) "errno" E_SUCC) [(x1, v1); ("errno", E_SUCC)] \/ x1 = "errno".
Proof.
  intros s x1 v1; destruct (string_dec x1 "errno") as [->|N]; [right; reflexivity|left].
  intros x v [H|[H|[]]]; inversion H; subst.
  - rewrite lset_other by auto; apply lset_same.
  - apply lset_same.
Qed.

Lemma outs_errno : forall s e, Outs (lset s "errno" e) [("errno", e)].
Proof. intros s e x v [H|[]]; inversion H; subst; apply lset_same. Qed.

Lemma outs_ret1 : forall s v, Outs (lset (lset s "ret1" v) "errno" E_SUCC) [("ret1", v); ("errno", E_SUCC)].
Proof. intros s v; destruct (outs2 s "ret1" v) as [H|H]; [exact H | discriminate]. Qed.

Definition errnoS (e : Z) : stmt := Assign "errno" (Const e).
Definition ret1S (x : string) : stmt := Seq (Assign "ret1" (Var x)) (errnoS E_SUCC).

Lemma ltu_eval : forall s x a b, s x = a -> eval s (Bin Ltu (Var x) (Const b)) = if a <? b then 1 else 0.
Proof. intros s x a b H; simpl; rewrite H; reflexivity. Qed.

(** *** [sys_hvm_get_reg]:
    [if (reg < GUEST_MAX_REG) { reg = vmx_get_reg(reg); uctx_set_retval1(reg); uctx_set_errno(E_SUCC); }
     else uctx_set_errno(E_INVAL_REG);] *)
Definition getRegH : stmt :=
  Ite (Bin Ltu (Var "reg") (Const C_GUEST_MAX_REG)) (Seq (VMX.getRegS xb vb) (ret1S "r")) (errnoS E_INVAL_REG).

Theorem get_reg_h : forall d d' o m s reg, MatchX d m -> s "reg" = reg -> 0 <= reg < W ->
  trap_get_reg_spec reg d = Some (d', o) ->
  exists s', exec getRegH s m s' m /\ d' = d /\ Outs s' o.
Proof.
  intros d d' o m s reg HM Hs Hr H; unfold trap_get_reg_spec in H.
  destruct ((0 <=? reg) && (reg <? C_GUEST_MAX_REG)) eqn:T.
  - apply andb_true_iff in T; destruct T as [_ T].
    destruct (VMX.vmx_get_reg_spec reg d) as [v|] eqn:Eg; [|discriminate].
    inversion H; subst d' o; clear H.
    pose proof (VMX.get_reg_ref xb vb eb hxb hxv hve heb2 d m s reg v HM Hs Eg) as G.
    exists (lset (lset (lset s "r" v) "ret1" v) "errno" E_SUCC); split; [|split; [reflexivity | apply outs_ret1]].
    apply EIteT; [rewrite (ltu_eval _ _ _ _ Hs), T; discriminate|].
    apply ESeq with (s1 := lset s "r" v) (m1 := m); [exact G|].
    apply ESeq with (s1 := lset (lset s "r" v) "ret1" v) (m1 := m); apply exec_assign; [apply lset_same | reflexivity].
  - inversion H; subst d' o; clear H.
    exists (lset s "errno" E_INVAL_REG); split; [|split; [reflexivity | apply outs_errno]].
    apply EIteF; [rewrite (ltu_eval _ _ _ _ Hs); destruct (reg <? C_GUEST_MAX_REG) eqn:L; [|reflexivity]|].
    + assert (L0 : 0 <=? reg = true) by (apply Z.leb_le; lia).
      rewrite L0 in T; try rewrite L in T; simpl in T; discriminate.
    + apply exec_assign; reflexivity.
Qed.

(** *** [sys_hvm_set_reg]:
    [if (reg < GUEST_MAX_REG) { vmx_set_reg(reg, val); uctx_set_errno(E_SUCC); }
     else uctx_set_errno(E_INVAL_REG);] *)
Definition setRegH : stmt :=
  Ite (Bin Ltu (Var "reg") (Const C_GUEST_MAX_REG)) (Seq (VMX.setRegS xb vb) (errnoS E_SUCC)) (errnoS E_INVAL_REG).

Theorem set_reg_h : forall d d' o m s reg v, MatchX d m -> s "reg" = reg -> s "v" = norm v -> 0 <= reg < W ->
  trap_set_reg_spec reg v d = Some (d', o) ->
  exists s' m', exec setRegH s m s' m' /\ MatchX d' m' /\ Outs s' o.
Proof.
  intros d d' o m s reg v HM Hs Hv Hr H; unfold trap_set_reg_spec in H.
  destruct ((0 <=? reg) && (reg <? C_GUEST_MAX_REG)) eqn:T.
  - apply andb_true_iff in T; destruct T as [_ T].
    destruct (VMX.vmx_set_reg_spec reg v d) as [d1|] eqn:Es; [|discriminate].
    inversion H; subst d' o; clear H.
    destruct (VMX.set_reg_ref xb vb eb hxb hxv hve heb2 d d1 m s reg v HM Hs Hv Es) as [m' [Ex HM']].
    exists (lset s "errno" E_SUCC), m'; split; [|split; [exact HM' | apply outs_errno]].
    apply EIteT; [rewrite (ltu_eval _ _ _ _ Hs), T; discriminate|].
    apply ESeq with (s1 := s) (m1 := m'); [exact Ex | apply exec_assign; reflexivity].
  - inversion H; subst d' o; clear H.
    exists (lset s "errno" E_INVAL_REG), m; split; [|split; [exact HM | apply outs_errno]].
    apply EIteF; [rewrite (ltu_eval _ _ _ _ Hs); destruct (reg <? C_GUEST_MAX_REG) eqn:L; [|reflexivity]|].
    + assert (L0 : 0 <=? reg = true) by (apply Z.leb_le; lia).
      rewrite L0 in T; try rewrite L in T; simpl in T; discriminate.
    + apply exec_assign; reflexivity.
Qed.

(** *** [sys_hvm_set_seg]:
    [if (seg < GUEST_MAX_SEG_DESC) { vmx_set_desc(seg, sel, base, lim, ar); uctx_set_errno(E_SUCC); }
     else uctx_set_errno(E_INVAL_SEG);] *)
Definition setSegH : stmt :=
  Ite (Bin Ltu (Var "seg") (Const C_GUEST_MAX_SEG_DESC)) (Seq (VMCS.setDescS vb) (errnoS E_SUCC))
    (errnoS E_INVAL_SEG).

Theorem set_seg_h : forall d d' o m s seg sel base lim ar, MatchX d m ->
  s "seg" = seg -> s "sel" = norm sel -> s "base" = norm base -> s "lim" = norm lim -> s "ar" = norm ar ->
  0 <= seg < W -> trap_set_seg_spec seg sel base lim ar d = Some (d', o) ->
  exists s' m', exec setSegH s m s' m' /\ MatchX d' m' /\ Outs s' o.
Proof.
  intros d d' o m s seg sel base lim ar HM Hseg Hsel Hb Hl Ha Hr H; unfold trap_set_seg_spec in H.
  destruct ((0 <=? seg) && (seg <? C_GUEST_MAX_SEG_DESC)) eqn:T.
  - apply andb_true_iff in T; destruct T as [_ T].
    destruct (onC (VMCS.vmx_set_desc_spec seg sel base lim ar (VMX.toC d)) d) as [d1|] eqn:Es; [|discriminate].
    inversion H; subst d' o; clear H.
    destruct (onC_some _ _ _ Es) as [v [Ev ->]].
    destruct (VMCS.set_desc_ref vb hvb hvb2 (VMX.toC d) v m s seg sel base lim ar (matchC d m HM)
      Hseg Hsel Hb Hl Ha Ev) as [s1 [m' [Ex [HM' F]]]].
    exists (lset s1 "errno" E_SUCC), m'; split; [|split; [exact (liftC d m m' v HM HM' F) | apply outs_errno]].
    apply EIteT; [rewrite (ltu_eval _ _ _ _ Hseg), T; discriminate|].
    apply ESeq with (s1 := s1) (m1 := m'); [exact Ex | apply exec_assign; reflexivity].
  - inversion H; subst d' o; clear H.
    exists (lset s "errno" E_INVAL_SEG), m; split; [|split; [exact HM | apply outs_errno]].
    apply EIteF; [rewrite (ltu_eval _ _ _ _ Hseg); destruct (seg <? C_GUEST_MAX_SEG_DESC) eqn:L; [|reflexivity]|].
    + assert (L0 : 0 <=? seg = true) by (apply Z.leb_le; lia).
      rewrite L0 in T; try rewrite L in T; simpl in T; discriminate.
    + apply exec_assign; reflexivity.
Qed.

(** *** [sys_hvm_get_next_eip]: [neip = vmx_get_next_eip(); uctx_set_retval1(neip); uctx_set_errno(E_SUCC);] *)
Definition getNextEipH : stmt := Seq (VMX.nextEipS xb vb) (ret1S "r").

Theorem get_next_eip_h : forall d d' o m s, MatchX d m -> trap_get_next_eip_spec d = Some (d', o) ->
  exists s', exec getNextEipH s m s' m /\ d' = d /\ Outs s' o.
Proof.
  intros d d' o m s HM H; unfold trap_get_next_eip_spec in H.
  destruct (VMX.vmx_get_next_eip_spec d) as [r|] eqn:E; [|discriminate].
  destruct ((0 <=? r) && (r <=? EPT.max_unsigned)); [|discriminate].
  inversion H; subst d' o; clear H.
  destruct (VMX.next_eip_ref xb vb eb hxb hxv hve heb2 d m s r HM E) as [s1 [Ex Hr]].
  exists (lset (lset s1 "ret1" r) "errno" E_SUCC); split; [|split; [reflexivity | apply outs_ret1]].
  apply ESeq with (s1 := s1) (m1 := m); [exact Ex|].
  apply ESeq with (s1 := lset s1 "ret1" r) (m1 := m); apply exec_assign; [exact Hr | reflexivity].
Qed.

(** *** [sys_hvm_inject_event]: [vmx_inject_event(ev_type, vector, errcode, ev); uctx_set_errno(E_SUCC);] *)
Definition injectEventH : stmt := Seq (VMCS.injectEventS vb) (errnoS E_SUCC).

Theorem inject_event_h : forall d d' o m s type vector errcode ev, MatchX d m ->
  s "type" = type -> s "vector" = vector -> s "errcode" = norm errcode -> s "ev" = ev ->
  trap_inject_event_spec type vector errcode ev d = Some (d', o) ->
  exists s' m', exec injectEventH s m s' m' /\ MatchX d' m' /\ Outs s' o.
Proof.
  intros d d' o m s type vector errcode ev HM Ht Hv He Hev H; unfold trap_inject_event_spec in H.
  destruct (onC (VMCS.vmx_inject_event_spec type vector errcode ev (VMX.toC d)) d) as [d1|] eqn:Es; [|discriminate].
  inversion H; subst d' o; clear H.
  destruct (onC_some _ _ _ Es) as [v [Ev ->]].
  destruct (VMCS.inject_event_ref vb hvb hvb2 (VMX.toC d) v m s type vector errcode ev (matchC d m HM)
    Ht Hv He Hev Ev) as [s1 [m' [Ex [HM' F]]]].
  exists (lset s1 "errno" E_SUCC), m'; split; [|split; [exact (liftC d m m' v HM HM' F) | apply outs_errno]].
  apply ESeq with (s1 := s1) (m1 := m'); [exact Ex | apply exec_assign; reflexivity].
Qed.

(** *** [sys_hvm_check_pending_event], [sys_hvm_check_int_shadow]:
    [r = vmx_check_...(); uctx_set_retval1(r); uctx_set_errno(E_SUCC);] *)
Definition checkPendingH : stmt := Seq (VMCS.checkPendingS vb) (ret1S "r").
Definition checkIntShadowH : stmt := Seq (VMCS.checkIntShadowS vb) (ret1S "r").

Theorem check_pending_h : forall d d' o m s, MatchX d m -> trap_check_pending_event_spec d = Some (d', o) ->
  exists s', exec checkPendingH s m s' m /\ d' = d /\ Outs s' o.
Proof.
  intros d d' o m s HM H; unfold trap_check_pending_event_spec in H.
  destruct (VMCS.vmx_check_pending_event_spec (VMX.toC d)) as [r|] eqn:E; [|discriminate].
  inversion H; subst d' o; clear H.
  destruct (VMCS.check_pending_ref vb hvb hvb2 (VMX.toC d) m s r (matchC d m HM) E) as [s1 [Ex Hr]].
  exists (lset (lset s1 "ret1" r) "errno" E_SUCC); split; [|split; [reflexivity | apply outs_ret1]].
  apply ESeq with (s1 := s1) (m1 := m); [exact Ex|].
  apply ESeq with (s1 := lset s1 "ret1" r) (m1 := m); apply exec_assign; [exact Hr | reflexivity].
Qed.

Theorem check_int_shadow_h : forall d d' o m s, MatchX d m -> trap_check_int_shadow_spec d = Some (d', o) ->
  exists s', exec checkIntShadowH s m s' m /\ d' = d /\ Outs s' o.
Proof.
  intros d d' o m s HM H; unfold trap_check_int_shadow_spec in H.
  destruct (VMCS.vmx_check_int_shadow_spec (VMX.toC d)) as [r|] eqn:E; [|discriminate].
  inversion H; subst d' o; clear H.
  destruct (VMCS.check_int_shadow_ref vb hvb hvb2 (VMX.toC d) m s r (matchC d m HM) E) as [s1 [Ex Hr]].
  exists (lset (lset s1 "ret1" r) "errno" E_SUCC); split; [|split; [reflexivity | apply outs_ret1]].
  apply ESeq with (s1 := s1) (m1 := m); [exact Ex|].
  apply ESeq with (s1 := lset s1 "ret1" r) (m1 := m); apply exec_assign; [exact Hr | reflexivity].
Qed.

(** *** [sys_hvm_intercept_int_window]: [vmx_set_intercept_intwin(enable); uctx_set_errno(E_SUCC);] *)
Definition interceptIntWindowH : stmt := Seq (VMCS.setIntwinS vb) (errnoS E_SUCC).

Theorem intercept_int_window_h : forall d d' o m s enable, MatchX d m -> s "enable" = enable ->
  trap_intercept_int_window_spec enable d = Some (d', o) ->
  exists s' m', exec interceptIntWindowH s m s' m' /\ MatchX d' m' /\ Outs s' o.
Proof.
  intros d d' o m s enable HM Hs H; unfold trap_intercept_int_window_spec in H.
  destruct (onC (VMCS.vmx_set_intercept_intwin_spec enable (VMX.toC d)) d) as [d1|] eqn:Es; [|discriminate].
  inversion H; subst d' o; clear H.
  destruct (onC_some _ _ _ Es) as [v [Ev ->]].
  destruct (VMCS.set_intwin_ref vb hvb hvb2 (VMX.toC d) v m s enable (matchC d m HM) Hs Ev)
    as [s1 [m' [Ex [HM' F]]]].
  exists (lset s1 "errno" E_SUCC), m'; split; [|split; [exact (liftC d m m' v HM HM' F) | apply outs_errno]].
  apply ESeq with (s1 := s1) (m1 := m'); [exact Ex | apply exec_assign; reflexivity].
Qed.

(** *** The TSC offset *)

(** The VMCS holds words, as it does in mCertiKOS ([Vint]). *)
Definition Words (d : VMX.XSt) : Prop :=
  forall e x, VMCS.data (VMX.xvmcs d) e = Some x -> 0 <= x < W.

Lemma z64_split : forall hi lo, 0 <= hi -> 0 <= lo < W ->
  VMCS.Z64ofwords hi lo / W = hi /\ VMCS.Z64ofwords hi lo mod W = lo.
Proof.
  intros hi lo Hh Hl.
  assert (E : VMCS.Z64ofwords hi lo = hi * W + lo).
  { unfold VMCS.Z64ofwords; rewrite Z.shiftl_mul_pow2 by lia.
    change (2 ^ 32) with W.
    assert (L : Z.land (hi * W) lo = 0).
    { rewrite <- (Z.mod_small lo (2 ^ 32)) by (unfold W in Hl; lia).
      rewrite <- Z.land_ones by lia.
      rewrite (Z.land_comm lo), Z.land_assoc, Z.land_ones by lia.
      change (2 ^ 32) with W; rewrite Z.mod_mul by (unfold W; lia).
      apply Z.land_0_l. }
    pose proof (Z.add_lor_land (hi * W) lo) as A; rewrite L in A; lia. }
  rewrite E; split.
  - rewrite Z.div_add_l by (unfold W; lia); rewrite Z.div_small by lia; lia.
  - rewrite Z.add_comm, Z.mod_add by (unfold W; lia); apply Z.mod_small; lia.
Qed.

(** [sys_hvm_get_tsc_offset]: [ofs = vmx_get_tsc_offset(); uctx_set_retval1(ofs >> 32);
    uctx_set_retval2(ofs & 0xffffffff); uctx_set_errno(E_SUCC);] *)
Definition getTscH : stmt :=
  Seq (VMCS.getTscS vb) (Seq (Assign "ret1" (Var "hi")) (Seq (Assign "ret2" (Var "lo")) (errnoS E_SUCC))).

Theorem get_tsc_h : forall d d' o m s, MatchX d m -> Words d -> trap_get_tsc_offset_spec d = Some (d', o) ->
  exists s', exec getTscH s m s' m /\ d' = d /\ Outs s' o.
Proof.
  intros d d' o m s HM HW H; unfold trap_get_tsc_offset_spec in H.
  destruct (VMCS.vmx_get_tsc_offset_spec (VMX.toC d)) as [ofs|] eqn:E; [|discriminate].
  inversion H; subst d' o; clear H.
  unfold VMCS.vmx_get_tsc_offset_spec in E.
  destruct (VMCS.flags (VMX.toC d)); [|discriminate].
  destruct (VMCS.data (VMCS.vmcs (VMX.toC d)) VMCS.C_VMCS_TSC_OFFSET) as [lo|] eqn:E1; [|discriminate].
  destruct (VMCS.data (VMCS.vmcs (VMX.toC d)) (VMCS.C_VMCS_TSC_OFFSET + 1)) as [hi|] eqn:E2; [|discriminate].
  inversion E; subst ofs; clear E.
  pose proof (HW _ _ E1) as Wl; pose proof (HW _ _ E2) as Wh.
  destruct (z64_split hi lo ltac:(lia) Wl) as [D M].
  pose proof (matchC d m HM) as HC.
  set (s1 := lset s "enc" VMCS.C_VMCS_TSC_OFFSET).
  set (s2 := lset s1 "lo" lo).
  set (s3 := lset s2 "hi" hi).
  exists (lset (lset (lset s3 "ret1" hi) "ret2" lo) "errno" E_SUCC); split; [|split; [reflexivity|]].
  - apply ESeq with (s1 := s3) (m1 := m).
    + apply ESeq with (s1 := s1) (m1 := m); [apply exec_assign; reflexivity|].
      apply ESeq with (s1 := s2) (m1 := m).
      * apply (VMCS.vmread_run vb hvb hvb2 (VMCS.vmcs (VMX.toC d)) m s1 "lo" (Var "enc") VMCS.C_VMCS_TSC_OFFSET lo HC);
          [apply lset_same | unfold VMCS.C_VMCS_TSC_OFFSET, VMCS.NENC; lia | exact E1].
      * apply (VMCS.vmread_run vb hvb hvb2 (VMCS.vmcs (VMX.toC d)) m s2 "hi" _ (VMCS.C_VMCS_TSC_OFFSET + 1) hi HC);
          [unfold s2, s1; reflexivity
          | unfold VMCS.C_VMCS_TSC_OFFSET, VMCS.NENC; lia | exact E2].
    + apply ESeq with (s1 := lset s3 "ret1" hi) (m1 := m); [apply exec_assign; unfold s3, s2, s1; reflexivity|].
      apply ESeq with (s1 := lset (lset s3 "ret1" hi) "ret2" lo) (m1 := m);
        [apply exec_assign; unfold s3, s2, s1; reflexivity | apply exec_assign; reflexivity].
  - rewrite D, M; intros x v [Hx|[Hx|[Hx|[]]]]; inversion Hx; subst; unfold s3, s2, s1; reflexivity.
Qed.

(** [sys_hvm_set_tsc_offset]: [ofs = (uint64_t) hi << 32 | lo; vmx_set_tsc_offset(ofs); uctx_set_errno(E_SUCC);] *)
Definition setTscH : stmt := Seq (VMCS.setTscS vb) (errnoS E_SUCC).

Theorem set_tsc_h : forall d d' o m s hi lo, MatchX d m -> s "hi" = hi -> s "lo" = lo ->
  0 <= hi < W -> 0 <= lo < W -> trap_set_tsc_offset_spec hi lo d = Some (d', o) ->
  exists s' m', exec setTscH s m s' m' /\ MatchX d' m' /\ Outs s' o.
Proof.
  intros d d' o m s hi lo HM Hh Hl Rh Rl H; unfold trap_set_tsc_offset_spec in H.
  destruct (onC (VMCS.vmx_set_tsc_offset_spec (hi * W + lo) (VMX.toC d)) d) as [d1|] eqn:Es; [|discriminate].
  inversion H; subst d' o; clear H.
  destruct (onC_some _ _ _ Es) as [v [Ev ->]].
  assert (L1 : s "lo" = (hi * W + lo) mod W).
  { rewrite Hl, Z.add_comm, Z.mod_add by (unfold W; lia); symmetry; apply Z.mod_small; lia. }
  assert (L2 : s "hi" = ((hi * W + lo) / W) mod W).
  { rewrite Hh, Z.div_add_l by (unfold W; lia); rewrite (Z.div_small lo) by lia; rewrite Z.add_0_r.
    symmetry; apply Z.mod_small; lia. }
  destruct (VMCS.set_tsc_ref vb hvb hvb2 (VMX.toC d) v m s (hi * W + lo) (matchC d m HM) L1 L2 Ev)
    as [s1 [m' [Ex [HM' F]]]].
  exists (lset s1 "errno" E_SUCC), m'; split; [|split; [exact (liftC d m m' v HM HM' F) | apply outs_errno]].
  apply ESeq with (s1 := s1) (m1 := m'); [exact Ex | apply exec_assign; reflexivity].
Qed.

(** *** [sys_hvm_mmap], from the host address on: [vmx_set_mmap(gpa, hpa, mem_type); uctx_set_errno(E_SUCC);] *)
Definition mmapH : stmt := Seq (VMX.setMmapS eb) (errnoS E_SUCC).

Theorem mmap_h : forall d d' o m s gpa hpa memtype, MatchX d m ->
  s "gpa" = gpa -> s "hpa" = hpa -> s "memtype" = memtype ->
  trap_mmap_spec maxpage gpa hpa memtype d = Some (d', o) ->
  exists s' m', exec mmapH s m s' m' /\ MatchX d' m' /\ Outs s' o.
Proof.
  intros d d' o m s gpa hpa memtype HM Hg Hh Hm H; unfold trap_mmap_spec in H.
  destruct (VMX.vmx_set_mmap_spec maxpage gpa hpa memtype d) as [[d1 r]|] eqn:E; [|discriminate].
  inversion H; subst d' o; clear H.
  destruct (VMX.set_mmap_ref xb vb eb hxb hxv hve heb2 maxpage hmp d d1 m s gpa hpa memtype r HM Hg Hh Hm E)
    as [s1 [m' [Ex [HM' _]]]].
  exists (lset s1 "errno" E_SUCC), m'; split; [|split; [exact HM' | apply outs_errno]].
  apply ESeq with (s1 := s1) (m1 := m'); [exact Ex | apply exec_assign; reflexivity].
Qed.

(** *** [sys_hvm_get_exitinfo] *)

Ltac chase :=
  repeat (first [ rewrite lset_same | rewrite lset_other by discriminate
    | match goal with H : forall z, ~ In z _ -> ?a z = _ |- context [?a ?y] =>
        rewrite (H y) by (apply not_assigned; reflexivity) end
    | match goal with H : forall z, z <> "flags" -> ?a z = _ |- context [?a ?y] =>
        rewrite (H y) by discriminate end ]).

Definition flagS (x : string) (bit : Z) : stmt :=
  Ite (Var x) (Assign "flags" (Bin Or (Var "flags") (Const bit))) Skip.

Lemma flag_step : forall m s0 x bit f v, s0 x = v -> s0 "flags" = f ->
  exists s', exec (flagS x bit) s0 m s' m /\ s' "flags" = (if v =? 0 then f else wor f bit) /\
    (forall z, z <> "flags" -> s' z = s0 z).
Proof.
  intros m s0 x bit f v Hx Hf; unfold flagS; destruct (v =? 0) eqn:E.
  - apply Z.eqb_eq in E; exists s0; split; [apply EIteF; [simpl; congruence | constructor] | auto].
  - apply Z.eqb_neq in E; exists (lset s0 "flags" (wor f bit)); split; [|split; [apply lset_same|]].
    + apply EIteT; [simpl; congruence | apply exec_assign; simpl; rewrite Hf; reflexivity].
    + intros z Hz; apply lset_other; auto.
Qed.

(** [reason = vmx_get_exit_reason(); port = vmx_get_exit_io_port(); ... fault_addr = vmx_get_exit_fault_addr();] *)
Definition readExitS : stmt :=
  Seq (VMCS.exitReasonS vb) (Seq (Assign "reason" (Var "r"))
  (Seq (VMX.ioPortS xb) (Seq (Assign "port" (Var "r"))
  (Seq (VMX.ioWidthS xb) (Seq (Assign "width" (Var "r"))
  (Seq (VMX.ioWriteS xb) (Seq (Assign "write" (Var "r"))
  (Seq (VMX.ioRepS xb) (Seq (Assign "rep" (Var "r"))
  (Seq (VMX.ioStrS xb) (Seq (Assign "str" (Var "r"))
  (Seq (VMCS.exitFaultAddrS vb) (Assign "fault" (Var "r")))))))))))))).

(** [uctx_set_retval1(reason); if (reason == EXIT_REASON_INOUT) { ... flags ... }
     else if (reason == EXIT_REASON_EPT_FAULT) uctx_set_retval2(fault_addr); uctx_set_errno(E_SUCC);] *)
Definition postExitS : stmt :=
  Seq (Assign "ret1" (Var "reason"))
  (Seq (Ite (Bin Eq (Var "reason") (Const EXIT_REASON_INOUT))
         (Seq (Assign "ret2" (Var "port")) (Seq (Assign "ret3" (Var "width")) (Seq (Assign "flags" (Const 0))
         (Seq (flagS "write" 1) (Seq (flagS "rep" 2) (Seq (flagS "str" 4) (Assign "ret4" (Var "flags"))))))))
         (Ite (Bin Eq (Var "reason") (Const EXIT_REASON_EPT_FAULT)) (Assign "ret2" (Var "fault")) Skip))
       (errnoS E_SUCC)).

Definition getExitinfoH : stmt := Seq readExitS postExitS.

Lemma post_exit_run : forall m s0 reason port width write rep str fault,
  s0 "reason" = reason -> s0 "port" = port -> s0 "width" = width -> s0 "write" = write -> s0 "rep" = rep ->
  s0 "str" = str -> s0 "fault" = fault ->
  exists s', exec postExitS s0 m s' m /\ Outs s' (exitinfo_outs reason port width write rep str fault).
Proof.
  intros m s0 reason port width write rep str fault Hr Hp Hw Hwr Hrp Hst Hf.
  unfold postExitS, exitinfo_outs.
  set (s1 := lset s0 "ret1" reason).
  assert (A1 : exec (Assign "ret1" (Var "reason")) s0 m s1 m) by (apply exec_assign; exact Hr).
  assert (R1 : s1 "reason" = reason) by (unfold s1; rewrite lset_other by discriminate; exact Hr).
  destruct (reason =? EXIT_REASON_INOUT) eqn:T1.
  - set (s4 := lset (lset (lset s1 "ret2" port) "ret3" width) "flags" 0).
    assert (Q1 : s4 "write" = write) by (unfold s4, s1; chase; exact Hwr).
    assert (Q0 : s4 "flags" = 0) by (unfold s4; chase; reflexivity).
    destruct (flag_step m s4 "write" 1 0 write Q1 Q0) as [f1 [Y1 [F1 Z1]]].
    assert (Q2 : f1 "rep" = rep) by (rewrite Z1 by discriminate; unfold s4, s1; chase; exact Hrp).
    destruct (flag_step m f1 "rep" 2 _ rep Q2 F1) as [f2 [Y2 [F2 Z2]]].
    assert (Q3 : f2 "str" = str) by (rewrite Z2, Z1 by discriminate; unfold s4, s1; chase; exact Hst).
    destruct (flag_step m f2 "str" 4 _ str Q3 F2) as [f3 [Y3 [F3 Z3]]].
    exists (lset (lset f3 "ret4" (get_flags write rep str)) "errno" E_SUCC); split.
    + apply ESeq with (s1 := s1) (m1 := m); [exact A1|].
      apply ESeq with (s1 := lset f3 "ret4" (get_flags write rep str)) (m1 := m);
        [|apply exec_assign; reflexivity].
      apply EIteT; [cbn [eval binop_eval]; rewrite R1, T1; discriminate|].
      apply ESeq with (s1 := lset s1 "ret2" port) (m1 := m);
        [apply exec_assign; unfold s1; simpl; rewrite lset_other by discriminate; exact Hp|].
      apply ESeq with (s1 := lset (lset s1 "ret2" port) "ret3" width) (m1 := m);
        [apply exec_assign; unfold s1; simpl; rewrite !lset_other by discriminate; exact Hw|].
      apply ESeq with (s1 := s4) (m1 := m); [apply exec_assign; reflexivity|].
      apply ESeq with (s1 := f1) (m1 := m); [exact Y1|].
      apply ESeq with (s1 := f2) (m1 := m); [exact Y2|].
      apply ESeq with (s1 := f3) (m1 := m); [exact Y3|].
      apply exec_assign; simpl; rewrite F3; unfold get_flags; reflexivity.
    + intros x v Hin; simpl in Hin.
      destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; inversion H; subst; unfold s4, s1; chase; auto.
  - destruct (reason =? EXIT_REASON_EPT_FAULT) eqn:T2.
    + exists (lset (lset s1 "ret2" fault) "errno" E_SUCC); split.
      * apply ESeq with (s1 := s1) (m1 := m); [exact A1|].
        apply ESeq with (s1 := lset s1 "ret2" fault) (m1 := m); [|apply exec_assign; reflexivity].
        apply EIteF; [cbn [eval binop_eval]; rewrite R1, T1; reflexivity|].
        apply EIteT; [cbn [eval binop_eval]; rewrite R1, T2; discriminate|].
        apply exec_assign; unfold s1; simpl; rewrite lset_other by discriminate; exact Hf.
      * intros x v Hin; simpl in Hin.
        destruct Hin as [H|[H|[H|[]]]]; inversion H; subst; unfold s1; chase; auto.
    + exists (lset s1 "errno" E_SUCC); split.
      * apply ESeq with (s1 := s1) (m1 := m); [exact A1|].
        apply ESeq with (s1 := s1) (m1 := m); [|apply exec_assign; reflexivity].
        apply EIteF; [cbn [eval binop_eval]; rewrite R1, T1; reflexivity|].
        apply EIteF; [cbn [eval binop_eval]; rewrite R1, T2; reflexivity | constructor].
      * intros x v Hin; simpl in Hin.
        destruct Hin as [H|[H|[]]]; inversion H; subst; unfold s1; chase; auto.
Qed.

Theorem get_exitinfo_h : forall d d' o m s, MatchX d m -> trap_get_exitinfo_spec d = Some (d', o) ->
  exists s', exec getExitinfoH s m s' m /\ d' = d /\ Outs s' o.
Proof.
  intros d d' o m s HM H; unfold trap_get_exitinfo_spec in H.
  destruct (VMCS.vmx_get_exit_reason_spec (VMX.toC d)) as [reason|] eqn:Er; [|discriminate].
  destruct (VMX.vmx_get_exit_io_port_spec d) as [port|] eqn:Ep; [|discriminate].
  destruct (VMX.vmx_get_io_width_spec d) as [width|] eqn:Ew; [|discriminate].
  destruct (VMX.vmx_get_io_write_spec d) as [write|] eqn:Ewr; [|discriminate].
  destruct (VMX.vmx_get_exit_io_rep_spec d) as [rep|] eqn:Erp; [|discriminate].
  destruct (VMX.vmx_get_exit_io_str_spec d) as [str|] eqn:Est; [|discriminate].
  destruct (VMCS.vmx_get_exit_fault_addr_spec (VMX.toC d)) as [fault|] eqn:Ef; [|discriminate].
  inversion H; subst d' o; clear H.
  pose proof (matchC d m HM) as HC.
  destruct (VMCS.exit_reason_ref vb hvb hvb2 (VMX.toC d) m s reason HC Er) as [s1 [X1 H1]].
  destruct (VMX.io_port_ref xb vb eb d m (lset s1 "reason" reason) port HM Ep) as [s2 [X2 H2]].
  pose proof (exec_assigns _ _ _ _ _ X2) as K2.
  destruct (VMX.io_width_ref xb vb eb d m (lset s2 "port" port) width HM Ew) as [s3 [X3 H3]].
  pose proof (exec_assigns _ _ _ _ _ X3) as K3.
  destruct (VMX.io_write_ref xb vb eb d m (lset s3 "width" width) write HM Ewr) as [s4 [X4 H4]].
  pose proof (exec_assigns _ _ _ _ _ X4) as K4.
  destruct (VMX.io_rep_ref xb vb eb d m (lset s4 "write" write) rep HM Erp) as [s5 [X5 H5]].
  pose proof (exec_assigns _ _ _ _ _ X5) as K5.
  destruct (VMX.io_str_ref xb vb eb d m (lset s5 "rep" rep) str HM Est) as [s6 [X6 H6]].
  pose proof (exec_assigns _ _ _ _ _ X6) as K6.
  pose proof (VMCS.exit_fault_addr_ref vb hvb hvb2 (VMX.toC d) m (lset s6 "str" str) fault HC Ef) as X7.
  set (sF := lset (lset (lset s6 "str" str) "r" fault) "fault" fault).
  assert (XR : exec readExitS s m sF m).
  { unfold readExitS.
    apply ESeq with (s1 := s1) (m1 := m); [exact X1|].
    apply ESeq with (s1 := lset s1 "reason" reason) (m1 := m); [apply exec_assign; exact H1|].
    apply ESeq with (s1 := s2) (m1 := m); [exact X2|].
    apply ESeq with (s1 := lset s2 "port" port) (m1 := m); [apply exec_assign; exact H2|].
    apply ESeq with (s1 := s3) (m1 := m); [exact X3|].
    apply ESeq with (s1 := lset s3 "width" width) (m1 := m); [apply exec_assign; exact H3|].
    apply ESeq with (s1 := s4) (m1 := m); [exact X4|].
    apply ESeq with (s1 := lset s4 "write" write) (m1 := m); [apply exec_assign; exact H4|].
    apply ESeq with (s1 := s5) (m1 := m); [exact X5|].
    apply ESeq with (s1 := lset s5 "rep" rep) (m1 := m); [apply exec_assign; exact H5|].
    apply ESeq with (s1 := s6) (m1 := m); [exact X6|].
    apply ESeq with (s1 := lset s6 "str" str) (m1 := m); [apply exec_assign; exact H6|].
    apply ESeq with (s1 := lset (lset s6 "str" str) "r" fault) (m1 := m); [exact X7|].
    apply exec_assign; apply lset_same. }
  destruct (post_exit_run m sF reason port width write rep str fault) as [s' [XP O]];
    try (unfold sF; chase; reflexivity).
  exists s'; split; [|split; [reflexivity | exact O]].
  apply ESeq with (s1 := sF) (m1 := m); [exact XR | exact XP].
Qed.

(** *** [sys_hvm_handle_rdmsr]:
    [msr = vmx_get_reg(GUEST_EAX); val = rdmsr(msr); vmx_set_reg(GUEST_EAX, val & 0xffffffff);
     vmx_set_reg(GUEST_EDX, (val >> 32) & 0xffffffff); next_eip = vmx_get_next_eip();
     vmx_set_reg(GUEST_EIP, next_eip); uctx_set_errno(E_SUCC);]
    [rdmsr] answers 0, as [rdmsr_spec] does. *)
Definition handleRdmsrH : stmt :=
  Seq (Assign "reg" (Const C_GUEST_EAX)) (Seq (VMX.getRegS xb vb) (Seq (Assign "msr" (Var "r"))
  (Seq (Assign "vlo" (Const 0)) (Seq (Assign "vhi" (Const 0))
  (Seq (Assign "reg" (Const C_GUEST_EAX)) (Seq (Assign "v" (Var "vlo")) (Seq (VMX.setRegS xb vb)
  (Seq (Assign "reg" (Const C_GUEST_EDX)) (Seq (Assign "v" (Var "vhi")) (Seq (VMX.setRegS xb vb)
  (Seq (VMX.nextEipS xb vb)
  (Seq (Assign "reg" (Const C_GUEST_EIP)) (Seq (Assign "v" (Var "r")) (Seq (VMX.setRegS xb vb)
    (errnoS E_SUCC))))))))))))))).

Theorem handle_rdmsr_h : forall d d' o m s, MatchX d m -> trap_handle_rdmsr_spec d = Some (d', o) ->
  exists s' m', exec handleRdmsrH s m s' m' /\ MatchX d' m' /\ Outs s' o.
Proof.
  intros d d' o m s HM H; unfold trap_handle_rdmsr_spec in H.
  destruct (VMX.vmx_get_reg_spec C_GUEST_EAX d) as [msr|] eqn:Eg; [|discriminate].
  unfold rdmsr_spec in H; destruct (VMX.xikern d && VMX.xihost d); [|discriminate].
  destruct (VMX.vmx_set_reg_spec C_GUEST_EAX (0 mod W) d) as [d0|] eqn:E0; [|discriminate].
  destruct (VMX.vmx_set_reg_spec C_GUEST_EDX (0 / W) d0) as [d1|] eqn:E1; [|discriminate].
  destruct (VMX.vmx_get_next_eip_spec d1) as [ne|] eqn:En; [|discriminate].
  destruct ((0 <=? ne) && (ne <=? EPT.max_unsigned)) eqn:R; [|discriminate].
  destruct (VMX.vmx_set_reg_spec C_GUEST_EIP ne d1) as [d2|] eqn:E2; [|discriminate].
  inversion H; subst d' o; clear H.
  apply andb_true_iff in R; destruct R as [R1 R2]; apply Z.leb_le in R1; apply Z.leb_le in R2.
  pose proof (VMX.get_reg_ref xb vb eb hxb hxv hve heb2 d m (lset s "reg" C_GUEST_EAX) C_GUEST_EAX msr HM
    eq_refl Eg) as G.
  set (s6 := lset (lset (lset (lset (lset (lset (lset s "reg" C_GUEST_EAX) "r" msr) "msr" msr) "vlo" 0) "vhi" 0)
    "reg" C_GUEST_EAX) "v" 0).
  destruct (VMX.set_reg_ref xb vb eb hxb hxv hve heb2 d d0 m s6 C_GUEST_EAX (0 mod W) HM eq_refl eq_refl E0)
    as [m1 [X1 M1]].
  set (s8 := lset (lset s6 "reg" C_GUEST_EDX) "v" 0).
  destruct (VMX.set_reg_ref xb vb eb hxb hxv hve heb2 d0 d1 m1 s8 C_GUEST_EDX (0 / W) M1 eq_refl eq_refl E1)
    as [m2 [X2 M2]].
  destruct (VMX.next_eip_ref xb vb eb hxb hxv hve heb2 d1 m2 s8 ne M2 En) as [s9 [X3 Hr]].
  set (s11 := lset (lset s9 "reg" C_GUEST_EIP) "v" ne).
  assert (Hv : s11 "v" = norm ne)
    by (unfold s11; rewrite lset_same; symmetry; apply norm_small; unfold EPT.max_unsigned, W in *; lia).
  destruct (VMX.set_reg_ref xb vb eb hxb hxv hve heb2 d1 d2 m2 s11 C_GUEST_EIP ne M2 eq_refl Hv E2)
    as [m3 [X4 M3]].
  exists (lset s11 "errno" E_SUCC), m3; split; [|split; [exact M3 | apply outs_errno]].
  unfold handleRdmsrH.
  apply ESeq with (s1 := lset s "reg" C_GUEST_EAX) (m1 := m); [apply exec_assign; reflexivity|].
  apply ESeq with (s1 := lset (lset s "reg" C_GUEST_EAX) "r" msr) (m1 := m); [exact G|].
  apply ESeq with (s1 := lset (lset (lset s "reg" C_GUEST_EAX) "r" msr) "msr" msr) (m1 := m);
    [apply exec_assign; apply lset_same|].
  do 4 (eapply ESeq; [apply exec_assign; reflexivity|]).
  apply ESeq with (s1 := s6) (m1 := m1); [exact X1|].
  apply ESeq with (s1 := lset s6 "reg" C_GUEST_EDX) (m1 := m1); [apply exec_assign; reflexivity|].
  apply ESeq with (s1 := s8) (m1 := m1); [apply exec_assign; reflexivity|].
  apply ESeq with (s1 := s8) (m1 := m2); [exact X2|].
  apply ESeq with (s1 := s9) (m1 := m2); [exact X3|].
  apply ESeq with (s1 := lset s9 "reg" C_GUEST_EIP) (m1 := m2); [apply exec_assign; reflexivity|].
  apply ESeq with (s1 := s11) (m1 := m2); [apply exec_assign; exact Hr|].
  apply ESeq with (s1 := s11) (m1 := m3); [exact X4 | apply exec_assign; reflexivity].
Qed.

(** *** [sys_hvm_handle_wrmsr]:
    [msr = vmx_get_reg(GUEST_ECX); eax = vmx_get_reg(GUEST_EAX); edx = vmx_get_reg(GUEST_EDX);
     wrmsr(msr, (uint64_t) edx << 32 | eax); next_eip = vmx_get_next_eip();
     vmx_set_reg(GUEST_EIP, next_eip); uctx_set_errno(E_SUCC);]
    [wrmsr] changes nothing the model sees, as [wrmsr_spec] says. *)
Definition handleWrmsrH : stmt :=
  Seq (Assign "reg" (Const C_GUEST_ECX)) (Seq (VMX.getRegS xb vb) (Seq (Assign "msr" (Var "r"))
  (Seq (Assign "reg" (Const C_GUEST_EAX)) (Seq (VMX.getRegS xb vb) (Seq (Assign "eax" (Var "r"))
  (Seq (Assign "reg" (Const C_GUEST_EDX)) (Seq (VMX.getRegS xb vb) (Seq (Assign "edx" (Var "r"))
  (Seq (VMX.nextEipS xb vb)
  (Seq (Assign "reg" (Const C_GUEST_EIP)) (Seq (Assign "v" (Var "r")) (Seq (VMX.setRegS xb vb)
    (errnoS E_SUCC))))))))))))).

Theorem handle_wrmsr_h : forall d d' o m s, MatchX d m -> trap_handle_wrmsr_spec d = Some (d', o) ->
  exists s' m', exec handleWrmsrH s m s' m' /\ MatchX d' m' /\ Outs s' o.
Proof.
  intros d d' o m s HM H; unfold trap_handle_wrmsr_spec in H.
  destruct (VMX.vmx_get_reg_spec C_GUEST_ECX d) as [msr|] eqn:Ec; [|discriminate].
  destruct (VMX.vmx_get_reg_spec C_GUEST_EAX d) as [eax|] eqn:Ea; [|discriminate].
  destruct (VMX.vmx_get_reg_spec C_GUEST_EDX d) as [edx|] eqn:Ed; [|discriminate].
  unfold wrmsr_spec in H; destruct (VMX.xikern d && VMX.xihost d); [|discriminate].
  destruct (VMX.vmx_get_next_eip_spec d) as [ne|] eqn:En; [|discriminate].
  destruct ((0 <=? ne) && (ne <=? EPT.max_unsigned)) eqn:R; [|discriminate].
  destruct (VMX.vmx_set_reg_spec C_GUEST_EIP ne d) as [d2|] eqn:E2; [|discriminate].
  inversion H; subst d' o; clear H.
  apply andb_true_iff in R; destruct R as [R1 R2]; apply Z.leb_le in R1; apply Z.leb_le in R2.
  set (t1 := lset s "reg" C_GUEST_ECX).
  pose proof (VMX.get_reg_ref xb vb eb hxb hxv hve heb2 d m t1 C_GUEST_ECX msr HM eq_refl Ec) as G1.
  set (t2 := lset (lset (lset t1 "r" msr) "msr" msr) "reg" C_GUEST_EAX).
  pose proof (VMX.get_reg_ref xb vb eb hxb hxv hve heb2 d m t2 C_GUEST_EAX eax HM eq_refl Ea) as G2.
  set (t3 := lset (lset (lset t2 "r" eax) "eax" eax) "reg" C_GUEST_EDX).
  pose proof (VMX.get_reg_ref xb vb eb hxb hxv hve heb2 d m t3 C_GUEST_EDX edx HM eq_refl Ed) as G3.
  set (t4 := lset (lset t3 "r" edx) "edx" edx).
  destruct (VMX.next_eip_ref xb vb eb hxb hxv hve heb2 d m t4 ne HM En) as [s9 [X3 Hr]].
  set (s11 := lset (lset s9 "reg" C_GUEST_EIP) "v" ne).
  assert (Hv : s11 "v" = norm ne)
    by (unfold s11; rewrite lset_same; symmetry; apply norm_small; unfold EPT.max_unsigned, W in *; lia).
  destruct (VMX.set_reg_ref xb vb eb hxb hxv hve heb2 d d2 m s11 C_GUEST_EIP ne HM eq_refl Hv E2)
    as [m3 [X4 M3]].
  exists (lset s11 "errno" E_SUCC), m3; split; [|split; [exact M3 | apply outs_errno]].
  unfold handleWrmsrH.
  apply ESeq with (s1 := t1) (m1 := m); [apply exec_assign; reflexivity|].
  apply ESeq with (s1 := lset t1 "r" msr) (m1 := m); [exact G1|].
  apply ESeq with (s1 := lset (lset t1 "r" msr) "msr" msr) (m1 := m); [apply exec_assign; apply lset_same|].
  apply ESeq with (s1 := t2) (m1 := m); [apply exec_assign; reflexivity|].
  apply ESeq with (s1 := lset t2 "r" eax) (m1 := m); [exact G2|].
  apply ESeq with (s1 := lset (lset t2 "r" eax) "eax" eax) (m1 := m); [apply exec_assign; apply lset_same|].
  apply ESeq with (s1 := t3) (m1 := m); [apply exec_assign; reflexivity|].
  apply ESeq with (s1 := lset t3 "r" edx) (m1 := m); [exact G3|].
  apply ESeq with (s1 := t4) (m1 := m); [apply exec_assign; apply lset_same|].
  apply ESeq with (s1 := s9) (m1 := m); [exact X3|].
  apply ESeq with (s1 := lset s9 "reg" C_GUEST_EIP) (m1 := m); [apply exec_assign; reflexivity|].
  apply ESeq with (s1 := s11) (m1 := m); [apply exec_assign; exact Hr|].
  apply ESeq with (s1 := s11) (m1 := m3); [exact X4 | apply exec_assign; reflexivity].
Qed.

End Code.
