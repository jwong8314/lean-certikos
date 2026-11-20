(** * The virtual-machine control structure (VMCS), ported and implemented

    Ported from [objects/ObjVMCS.v] and [layerlib/AuxStateDataType.v]: the
    VMCS ([VMCSValid revid abrtid data]), its field encodings, and the
    specifications [vmcs_get_revid_spec], [vmcs_set_revid_spec],
    [vmcs_get_abrtid_spec], [vmcs_set_abrtid_spec], [vmcs_readz_spec],
    [vmcs_writez_spec], [vmcs_readz64_spec], [vmcs_writez64_spec],
    [vmx_set_intercept_intwin_spec], [vmx_set_desc_spec],
    [vmx_inject_event_spec], [vmx_check_pending_event_spec],
    [vmx_check_int_shadow_spec], [vmx_get_exit_reason_spec],
    [vmx_set_tsc_offset_spec], [vmx_get_tsc_offset_spec],
    [vmx_get_exit_fault_addr_spec].

    The VMCS is the processor's record of one virtual machine: guest state,
    host state and controls, one field per encoding. On real hardware it is
    read and written with [vmread] and [vmwrite]. Here it is a block of the
    kernel region at [vb]: the revision id at [vb], the abort indicator at
    [vb+1], and field [enc] at [vb + 2 + enc]. [vmread] and [vmwrite] are a
    load and a store there; this is the model of the hardware, as [cswitch]
    is for kernel contexts. The C code of the functions above is quoted in
    [ObjVMCS.v]; the code here follows it.

    What differs:
    - A field holds a word or nothing ([None] for [Vundef]). mCertiKOS also
      stores pointers there ([vmcs_write_ident_spec]); here an address is a
      word, so that is [vmcs_writez_spec].
    - [write64_aux] is not in the public sources; it is defined here as
      [vmcs_write64] in the C does it: the low word at [enc], the high word at
      [enc + 1]. A 64-bit argument or result is two locals, ["lo"] and ["hi"],
      as in the 32-bit calling convention.
    - The C operations on words are [wand], [wor] (32-bit), as in [EPT.v].
    - [vmcs_set_defaults_spec] and the hardware accessors [rdmsr], [wrmsr],
      [rcr0], [rcr3], [rcr4], [vmptrld] are not here. *)

From Stdlib Require Import ZArith String Lia Bool List.
From VCoq Require Import Lang.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope bool_scope.
Open Scope Z_scope.

(** ** Abstract data *)

Record VMCS := VMCSValid { revid : option Z; abrtid : option Z; data : Z -> option Z }.

Record VSt := mkS { ikern : bool; pg : bool; ihost : bool; vmcs : VMCS }.

Definition set_vmcs (d : VSt) (v : VMCS) : VSt := mkS (ikern d) (pg d) (ihost d) v.

Definition zset {A} (f : Z -> A) (k : Z) (v : A) : Z -> A :=
  fun x => if Z.eq_dec x k then v else f x.

(** The field encodings ([vmcs_ZtoEncoding] is defined exactly on these). *)
Definition encodings : list Z := [0; 2048; 2050; 2052; 2054; 2056; 2058; 2060; 2062; 3072; 3074; 3076; 3078; 3080; 3082; 3084; 8192; 8193; 8194; 8195; 8196; 8197; 8198; 8200; 8202; 8204; 8208; 8210; 8212; 8218; 8219; 9216; 10240; 10242; 10244; 10246; 10248; 10250; 10252; 10254; 10256; 11264; 11266; 11268; 16384; 16386; 16388; 16390; 16392; 16394; 16396; 16398; 16400; 16402; 16404; 16406; 16408; 16410; 16412; 16414; 16416; 16418; 17408; 17410; 17412; 17414; 17416; 17418; 17420; 17422; 18432; 18434; 18436; 18438; 18440; 18442; 18444; 18446; 18448; 18450; 18452; 18454; 18456; 18458; 18460; 18462; 18464; 18466; 18468; 18470; 18472; 18474; 18478; 19456; 24576; 24578; 24580; 24582; 24584; 24586; 24588; 24590; 25600; 25602; 25604; 25606; 25608; 25610; 26624; 26626; 26628; 26630; 26632; 26634; 26636; 26638; 26640; 26642; 26644; 26646; 26648; 26650; 26652; 26654; 26656; 26658; 26660; 26662; 27648; 27650; 27652; 27654; 27656; 27658; 27660; 27662; 27664; 27666; 27668; 27670].

Definition valid_enc (z : Z) : bool := existsb (Z.eqb z) encodings.

Lemma valid_enc_range : forall z, valid_enc z = true -> 0 <= z <= 27670.
Proof.
  intros z H; unfold valid_enc in H; apply existsb_exists in H.
  destruct H as [x [Hin Hx]]; apply Z.eqb_eq in Hx; subst x.
  assert (F : Forall (fun x => 0 <= x <= 27670) encodings) by (repeat constructor; lia).
  rewrite Forall_forall in F; apply F; exact Hin.
Qed.

Definition C_VMCS_PRI_PROC_BASED_CTLS := 16386.
Definition C_VMCS_ENTRY_INTR_INFO := 16406.
Definition C_VMCS_ENTRY_EXCEPTION_ERROR := 16408.
Definition C_VMCS_EXIT_REASON := 17410.
Definition C_VMCS_GUEST_INTERRUPTIBILITY := 18468.
Definition C_VMCS_TSC_OFFSET := 8208.
Definition C_VMCS_GUEST_PHYSICAL_ADDRESS := 9216.
Definition PROCBASED_INT_WINDOW_EXITING := 4.
Definition NOT_PROCBASED_INT_WINDOW_EXITING := 4294967291.
Definition VMCS_INTERRUPTION_INFO_VALID := 2147483648.
Definition VMCS_INTERRUPTION_INFO_EV := 2048.
Definition VMCS_INTERRUPTIBILITY_STI_or_MOVSS_BLOCKING := 3.
Definition EXIT_REASON_MASK := 65535.

(** [seg_encode]: base, limit, access rights and selector of each segment.
    GDTR and IDTR (8 and 9) have only a base and a limit. *)
Definition seg_table : list (Z * (Z * Z * Z * Z)) :=
  [(0, (26632, 18434, 18454, 2050));   (* CS *)
   (1, (26636, 18438, 18458, 2054));   (* DS *)
   (2, (26630, 18432, 18452, 2048));   (* ES *)
   (3, (26638, 18440, 18460, 2056));   (* FS *)
   (4, (26640, 18442, 18462, 2058));   (* GS *)
   (5, (26634, 18436, 18456, 2052));   (* SS *)
   (6, (26642, 18444, 18464, 2060));   (* LDTR *)
   (7, (26644, 18446, 18466, 2062));   (* TR *)
   (8, (26646, 18448, 0, 0));          (* GDTR *)
   (9, (26648, 18450, 0, 0))].         (* IDTR *)

Fixpoint lookup (t : list (Z * (Z * Z * Z * Z))) (k : Z) : option (Z * Z * Z * Z) :=
  match t with
  | [] => None
  | (k', p) :: t' => if Z.eqb k k' then Some p else lookup t' k
  end.

(** ** Specifications ([ObjVMCS.v]) *)

Definition flags (d : VSt) : bool := ikern d && pg d && ihost d.

Definition Z64ofwords (hi lo : Z) : Z := Z.lor (Z.shiftl hi 32) lo.

Definition write64_aux (enc v : Z) (dt : Z -> option Z) : Z -> option Z :=
  zset (zset dt enc (Some (v mod W))) (enc + 1) (Some ((v / W) mod W)).

Definition vmcs_get_revid_spec (d : VSt) : option Z :=
  if flags d then revid (vmcs d) else None.

Definition vmcs_set_revid_spec (r : Z) (d : VSt) : option VSt :=
  if flags d then Some (set_vmcs d (VMCSValid (Some (norm r)) (abrtid (vmcs d)) (data (vmcs d)))) else None.

Definition vmcs_get_abrtid_spec (d : VSt) : option Z :=
  if flags d then abrtid (vmcs d) else None.

Definition vmcs_set_abrtid_spec (a : Z) (d : VSt) : option VSt :=
  if flags d then Some (set_vmcs d (VMCSValid (revid (vmcs d)) (Some (norm a)) (data (vmcs d)))) else None.

Definition set_data (d : VSt) (dt : Z -> option Z) : VSt :=
  set_vmcs d (VMCSValid (revid (vmcs d)) (abrtid (vmcs d)) dt).

Definition vmcs_readz_spec (enc : Z) (d : VSt) : option Z :=
  if flags d then if valid_enc enc then data (vmcs d) enc else None else None.

Definition vmcs_writez_spec (enc value : Z) (d : VSt) : option VSt :=
  if flags d then
    if valid_enc enc then Some (set_data d (zset (data (vmcs d)) enc (Some (norm value)))) else None
  else None.

Definition vmcs_readz64_spec (enc : Z) (d : VSt) : option Z :=
  if flags d then
    if valid_enc enc then
      match data (vmcs d) enc, data (vmcs d) (enc + 1) with
      | Some lo, Some hi => Some (Z64ofwords hi lo)
      | _, _ => None
      end
    else None
  else None.

Definition vmcs_writez64_spec (enc value : Z) (d : VSt) : option VSt :=
  if flags d then
    if valid_enc enc then Some (set_data d (write64_aux enc value (data (vmcs d)))) else None
  else None.

Definition vmx_set_intercept_intwin_spec (enable : Z) (d : VSt) : option VSt :=
  if flags d then
    match data (vmcs d) C_VMCS_PRI_PROC_BASED_CTLS with
    | Some ctrls =>
      if enable =? 1 then
        Some (set_data d (zset (data (vmcs d)) C_VMCS_PRI_PROC_BASED_CTLS
                (Some (wor ctrls PROCBASED_INT_WINDOW_EXITING))))
      else
        Some (set_data d (zset (data (vmcs d)) C_VMCS_PRI_PROC_BASED_CTLS
                (Some (wand ctrls NOT_PROCBASED_INT_WINDOW_EXITING))))
    | None => None
    end
  else None.

Definition vmx_set_desc_aux (seg sel base lim ar : Z) (dt : Z -> option Z) : option (Z -> option Z) :=
  match lookup seg_table seg with
  | Some (eb, el, ea, es) =>
    if seg <? 8 then
      Some (zset (zset (zset (zset dt eb (Some (norm base))) el (Some (norm lim))) ea (Some (norm ar)))
              es (Some (norm sel)))
    else Some (zset (zset dt eb (Some (norm base))) el (Some (norm lim)))
  | None => None
  end.

Definition vmx_set_desc_spec (seg sel base lim ar : Z) (d : VSt) : option VSt :=
  if flags d then
    match vmx_set_desc_aux seg sel base lim ar (data (vmcs d)) with
    | Some dt => Some (set_data d dt)
    | None => None
    end
  else None.

Definition vmx_inject_event_spec (type vector errcode ev : Z) (d : VSt) : option VSt :=
  if flags d then
    match data (vmcs d) C_VMCS_ENTRY_INTR_INFO with
    | Some i =>
      if wand i VMCS_INTERRUPTION_INFO_VALID =? 0 then
        let i2 := wor (wor VMCS_INTERRUPTION_INFO_VALID type) vector in
        if ev =? 1 then
          let dt1 := zset (data (vmcs d)) C_VMCS_ENTRY_INTR_INFO (Some (wor i2 VMCS_INTERRUPTION_INFO_EV)) in
          Some (set_data d (zset dt1 C_VMCS_ENTRY_EXCEPTION_ERROR (Some (norm errcode))))
        else Some (set_data d (zset (data (vmcs d)) C_VMCS_ENTRY_INTR_INFO (Some i2)))
      else Some d
    | None => None
    end
  else None.

Definition vmx_check_pending_event_spec (d : VSt) : option Z :=
  if flags d then
    match data (vmcs d) C_VMCS_ENTRY_INTR_INFO with
    | Some c => if wand c VMCS_INTERRUPTION_INFO_VALID =? 0 then Some 0 else Some 1
    | None => None
    end
  else None.

Definition vmx_check_int_shadow_spec (d : VSt) : option Z :=
  if flags d then
    match data (vmcs d) C_VMCS_GUEST_INTERRUPTIBILITY with
    | Some c => if wand c VMCS_INTERRUPTIBILITY_STI_or_MOVSS_BLOCKING =? 0 then Some 0 else Some 1
    | None => None
    end
  else None.

Definition vmx_get_exit_reason_spec (d : VSt) : option Z :=
  if flags d then
    match data (vmcs d) C_VMCS_EXIT_REASON with
    | Some r => Some (wand r EXIT_REASON_MASK)
    | None => None
    end
  else None.

Definition vmx_set_tsc_offset_spec (v : Z) (d : VSt) : option VSt :=
  if flags d then Some (set_data d (write64_aux C_VMCS_TSC_OFFSET v (data (vmcs d)))) else None.

Definition vmx_get_tsc_offset_spec (d : VSt) : option Z :=
  if flags d then
    match data (vmcs d) C_VMCS_TSC_OFFSET, data (vmcs d) (C_VMCS_TSC_OFFSET + 1) with
    | Some lo, Some hi => Some (Z64ofwords hi lo)
    | _, _ => None
    end
  else None.

Definition vmx_get_exit_fault_addr_spec (d : VSt) : option Z :=
  if flags d then data (vmcs d) C_VMCS_GUEST_PHYSICAL_ADDRESS else None.

(** ** The VMCS in the region *)

Section Code.
Variable vb : Z.
Hypothesis hvb : 0 <= vb.
Hypothesis hvb2 : vb + 65540 <= W.

Definition NENC := 65537.

Definition MatchV (v : VMCS) (m : mem) : Prop :=
  (forall r, revid v = Some r -> m vb = r) /\
  (forall a, abrtid v = Some a -> m (vb + 1) = a) /\
  (forall e x, 0 <= e < NENC -> data v e = Some x -> m (vb + 2 + e) = x).

Definition MatchS (d : VSt) (m : mem) : Prop := MatchV (vmcs d) m.

(** The cells outside the VMCS block are left alone. *)
Definition FrameV (m m' : mem) : Prop := forall a, (a < vb \/ vb + 2 + NENC <= a) -> m' a = m a.

Lemma frame_upd : forall m k w, vb + 2 <= k < vb + 2 + NENC -> FrameV m (upd m k w).
Proof. intros m k w Hk a Ha; apply upd_other; lia. Qed.

Lemma frame_trans : forall m1 m2 m3, FrameV m1 m2 -> FrameV m2 m3 -> FrameV m1 m3.
Proof. intros m1 m2 m3 F1 F2 a Ha; rewrite F2 by auto; auto. Qed.

Lemma frame_refl : forall m, FrameV m m.
Proof. intros m a _; reflexivity. Qed.

(** [vmread(e)] and [vmwrite(e, v)]: the cell of field [e]. *)
Definition encE (e : expr) : expr := Bin Add (Const (vb + 2)) e.
Definition vmreadS (x : string) (e : expr) : stmt := Load x (encE e).
Definition vmwriteS (e v : expr) : stmt := Store (encE e) v.

Lemma eval_enc : forall s e k, eval s e = k -> 0 <= k < NENC -> eval s (encE e) = vb + 2 + k.
Proof.
  intros s e k Hk Hr; simpl; rewrite Hk; apply norm_small; unfold NENC, W in *; lia.
Qed.

Lemma vmread_run : forall v m s x e k w, MatchV v m -> eval s e = k -> 0 <= k < NENC ->
  data v k = Some w -> exec (vmreadS x e) s m (lset s x w) m.
Proof.
  intros v m s x e k w HM Hk Hr Hd.
  destruct HM as (_ & _ & H3).
  rewrite <- (H3 k w Hr Hd); apply exec_load, eval_enc; auto.
Qed.

Lemma vmwrite_run : forall m s e v k w, eval s e = k -> 0 <= k < NENC -> eval s v = w ->
  exec (vmwriteS e v) s m s (upd m (vb + 2 + k) w).
Proof. intros; apply exec_store; auto; apply eval_enc; auto. Qed.

Lemma match_write : forall v m k w, MatchV v m -> 0 <= k < NENC ->
  MatchV (VMCSValid (revid v) (abrtid v) (zset (data v) k (Some w))) (upd m (vb + 2 + k) w).
Proof.
  intros v m k w (H1 & H2 & H3) Hk; split; [|split].
  - intros r Hr; simpl in Hr; rewrite upd_other by lia; auto.
  - intros a Ha; simpl in Ha; rewrite upd_other by lia; auto.
  - intros e x He Hx; simpl in Hx; unfold zset in Hx.
    destruct (Z.eq_dec e k) as [->|Ne].
    + inversion Hx; apply upd_same.
    + rewrite upd_other by lia; auto.
Qed.

Lemma valid_enc_lt : forall z, valid_enc z = true -> 0 <= z < NENC /\ 0 <= z + 1 < NENC.
Proof. intros z H; apply valid_enc_range in H; unfold NENC; lia. Qed.

Lemma flags_true : forall (d : VSt) (A : Type) (x : option A) (y : A),
  (if flags d then x else None) = Some y -> flags d = true /\ x = Some y.
Proof. intros d A x y H; destruct (flags d); [auto | discriminate]. Qed.

Lemma valid_true : forall z (A : Type) (x : option A) (y : A),
  (if valid_enc z then x else None) = Some y -> valid_enc z = true /\ x = Some y.
Proof. intros z A x y H; destruct (valid_enc z); [auto | discriminate]. Qed.

(** *** [vmcs_readz]: [r = vmread(enc);] *)
Definition readzS : stmt := vmreadS "r" (Var "enc").

Theorem readz_ref : forall d m s enc r, MatchS d m -> s "enc" = enc ->
  vmcs_readz_spec enc d = Some r -> exec readzS s m (lset s "r" r) m.
Proof.
  intros d m s enc r HM Hs H; unfold vmcs_readz_spec in H.
  apply flags_true in H; destruct H as [_ H]; apply valid_true in H; destruct H as [Hv H].
  destruct (valid_enc_lt _ Hv) as [Hr _].
  eapply vmread_run; eauto.
Qed.

(** *** [vmcs_writez]: [vmwrite(enc, value);] *)
Definition writezS : stmt := vmwriteS (Var "enc") (Var "value").

Theorem writez_ref : forall d d' m s enc value, MatchS d m -> s "enc" = enc -> s "value" = norm value ->
  vmcs_writez_spec enc value d = Some d' -> exists m', exec writezS s m s m' /\ MatchS d' m'.
Proof.
  intros d d' m s enc value HM Hs Hv H; unfold vmcs_writez_spec in H.
  apply flags_true in H; destruct H as [_ H]; apply valid_true in H; destruct H as [Hve H].
  inversion H; subst d'; clear H.
  destruct (valid_enc_lt _ Hve) as [Hr _].
  exists (upd m (vb + 2 + enc) (norm value)); split.
  - apply vmwrite_run; auto.
  - apply match_write; auto.
Qed.

(** *** [vmcs_read64]: [lo = vmread(enc); hi = vmread(enc + 1);] *)
Definition readz64S : stmt :=
  Seq (vmreadS "lo" (Var "enc")) (vmreadS "hi" (Bin Add (Var "enc") (Const 1))).

Theorem readz64_ref : forall d m s enc r, MatchS d m -> s "enc" = enc ->
  vmcs_readz64_spec enc d = Some r ->
  exists s' lo hi, exec readz64S s m s' m /\ r = Z64ofwords hi lo /\ s' "lo" = lo /\ s' "hi" = hi.
Proof.
  intros d m s enc r HM Hs H; unfold vmcs_readz64_spec in H.
  apply flags_true in H; destruct H as [_ H]; apply valid_true in H; destruct H as [Hve H].
  destruct (valid_enc_lt _ Hve) as [Hr1 Hr2].
  destruct (data (vmcs d) enc) as [lo|] eqn:E1; [|discriminate].
  destruct (data (vmcs d) (enc + 1)) as [hi|] eqn:E2; [|discriminate].
  inversion H; subst r.
  exists (lset (lset s "lo" lo) "hi" hi), lo, hi; split; [|split; [reflexivity|split]].
  - apply ESeq with (s1 := lset s "lo" lo) (m1 := m).
    + apply (vmread_run (vmcs d) m s "lo" (Var "enc") enc lo HM Hs Hr1 E1).
    + apply (vmread_run (vmcs d) m (lset s "lo" lo) "hi" _ (enc + 1) hi HM); auto.
      simpl; rewrite lset_other by discriminate; rewrite Hs; apply norm_small; unfold NENC, W in *; lia.
  - rewrite lset_other by discriminate; apply lset_same.
  - apply lset_same.
Qed.

(** *** [vmcs_write64]: [vmwrite(enc, lo); vmwrite(enc + 1, hi);] *)
Definition writez64S : stmt :=
  Seq (vmwriteS (Var "enc") (Var "lo")) (vmwriteS (Bin Add (Var "enc") (Const 1)) (Var "hi")).

Lemma match_write64 : forall v m enc value, MatchV v m -> 0 <= enc < NENC -> 0 <= enc + 1 < NENC ->
  MatchV (VMCSValid (revid v) (abrtid v) (write64_aux enc value (data v)))
    (upd (upd m (vb + 2 + enc) (value mod W)) (vb + 2 + (enc + 1)) ((value / W) mod W)).
Proof.
  intros v m enc value HM H1 H2.
  pose proof (match_write v m enc (value mod W) HM H1) as M1.
  exact (match_write _ _ (enc + 1) ((value / W) mod W) M1 H2).
Qed.

Theorem writez64_ref : forall d d' m s enc value, MatchS d m -> s "enc" = enc ->
  s "lo" = value mod W -> s "hi" = (value / W) mod W ->
  vmcs_writez64_spec enc value d = Some d' -> exists m', exec writez64S s m s m' /\ MatchS d' m' /\ FrameV m m'.
Proof.
  intros d d' m s enc value HM Hs Hlo Hhi H; unfold vmcs_writez64_spec in H.
  apply flags_true in H; destruct H as [_ H]; apply valid_true in H; destruct H as [Hve H].
  inversion H; subst d'; clear H.
  destruct (valid_enc_lt _ Hve) as [Hr1 Hr2].
  eexists; split.
  - apply ESeq with (s1 := s) (m1 := upd m (vb + 2 + enc) (value mod W)).
    + apply vmwrite_run; auto.
    + apply (vmwrite_run _ s _ _ (enc + 1) ((value / W) mod W)); auto.
      simpl; rewrite Hs; apply norm_small; unfold NENC, W in *; lia.
  - split; [apply match_write64; auto|].
    repeat (eapply frame_trans; [|apply frame_upd; lia]); apply frame_refl.
Qed.

(** *** [vmx_set_intercept_intwin] *)
(** [c = vmcs_read32(VMCS_PRI_PROC_BASED_CTLS);
     if (enable == 1) c |= PROCBASED_INT_WINDOW_EXITING; else c &= ~PROCBASED_INT_WINDOW_EXITING;
     vmcs_write32(VMCS_PRI_PROC_BASED_CTLS, c);] *)
Definition setIntwinS : stmt :=
  Seq (vmreadS "c" (Const C_VMCS_PRI_PROC_BASED_CTLS))
  (Seq (Ite (Bin Eq (Var "enable") (Const 1))
            (Assign "c" (Bin Or (Var "c") (Const PROCBASED_INT_WINDOW_EXITING)))
            (Assign "c" (Bin And (Var "c") (Const NOT_PROCBASED_INT_WINDOW_EXITING))))
       (vmwriteS (Const C_VMCS_PRI_PROC_BASED_CTLS) (Var "c"))).

Theorem set_intwin_ref : forall d d' m s enable, MatchS d m -> s "enable" = enable ->
  vmx_set_intercept_intwin_spec enable d = Some d' ->
  exists s' m', exec setIntwinS s m s' m' /\ MatchS d' m' /\ FrameV m m'.
Proof.
  intros d d' m s enable HM Hs H; unfold vmx_set_intercept_intwin_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct (data (vmcs d) C_VMCS_PRI_PROC_BASED_CTLS) as [c|] eqn:Ec; [|discriminate].
  assert (R : 0 <= C_VMCS_PRI_PROC_BASED_CTLS < NENC) by (unfold C_VMCS_PRI_PROC_BASED_CTLS, NENC; lia).
  assert (L : exec (vmreadS "c" (Const C_VMCS_PRI_PROC_BASED_CTLS)) s m (lset s "c" c) m)
    by (eapply vmread_run; eauto; reflexivity).
  assert (Ee : lset s "c" c "enable" = enable) by (rewrite lset_other by discriminate; auto).
  destruct (enable =? 1) eqn:T.
  - inversion H; subst d'; clear H.
    set (c' := wor c PROCBASED_INT_WINDOW_EXITING).
    exists (lset (lset s "c" c) "c" c'), (upd m (vb + 2 + C_VMCS_PRI_PROC_BASED_CTLS) c'); split.
    + apply ESeq with (s1 := lset s "c" c) (m1 := m); [exact L|].
      apply ESeq with (s1 := lset (lset s "c" c) "c" c') (m1 := m).
      * apply EIteT; [simpl; rewrite Ee, T; discriminate | apply exec_assign; simpl; rewrite lset_same; reflexivity].
      * apply vmwrite_run; auto; apply lset_same.
    + split; [apply match_write; auto | apply frame_upd; lia].
  - inversion H; subst d'; clear H.
    set (c' := wand c NOT_PROCBASED_INT_WINDOW_EXITING).
    exists (lset (lset s "c" c) "c" c'), (upd m (vb + 2 + C_VMCS_PRI_PROC_BASED_CTLS) c'); split.
    + apply ESeq with (s1 := lset s "c" c) (m1 := m); [exact L|].
      apply ESeq with (s1 := lset (lset s "c" c) "c" c') (m1 := m).
      * apply EIteF; [simpl; rewrite Ee, T; reflexivity | apply exec_assign; simpl; rewrite lset_same; reflexivity].
      * apply vmwrite_run; auto; apply lset_same.
    + split; [apply match_write; auto | apply frame_upd; lia].
Qed.

(** *** [vmx_set_desc] *)

(** The selection of the four encodings of a segment from [seg_encode]. *)
Fixpoint selS (t : list (Z * (Z * Z * Z * Z))) : stmt :=
  match t with
  | [] => Skip
  | (k, (b, l, a, sl)) :: t' =>
    Ite (Bin Eq (Var "seg") (Const k))
        (Seq (Assign "eb" (Const b)) (Seq (Assign "el" (Const l))
          (Seq (Assign "ea" (Const a)) (Assign "es" (Const sl)))))
        (selS t')
  end.

Lemma sel_run : forall t s m seg b l a sl, s "seg" = seg -> lookup t seg = Some (b, l, a, sl) ->
  exists s', exec (selS t) s m s' m /\ s' "eb" = b /\ s' "el" = l /\ s' "ea" = a /\ s' "es" = sl /\
    (forall z, z <> "eb" -> z <> "el" -> z <> "ea" -> z <> "es" -> s' z = s z).
Proof.
  induction t as [|[k [[[b0 l0] a0] s0]] t IH]; intros s m seg b l a sl Hs Hl; simpl in Hl; [discriminate|].
  destruct (seg =? k) eqn:E.
  - inversion Hl; subst b0 l0 a0 s0.
    exists (lset (lset (lset (lset s "eb" b) "el" l) "ea" a) "es" sl); split.
    + apply EIteT; [simpl; rewrite Hs, E; discriminate|].
      repeat (eapply ESeq; [apply exec_assign; reflexivity|]); apply exec_assign; reflexivity.
    + split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|].
      intros z H1 H2 H3 H4; unfold lset.
      destruct (string_dec z "es"); [congruence|].
      destruct (string_dec z "ea"); [congruence|].
      destruct (string_dec z "el"); [congruence|].
      destruct (string_dec z "eb"); [congruence|].
      reflexivity.
  - destruct (IH s m seg b l a sl Hs Hl) as [s' [Ex R]].
    exists s'; split; [|exact R].
    apply EIteF; [simpl; rewrite Hs, E; reflexivity | exact Ex].
Qed.

(** [vmcs_write32(seg_encode[seg].base, base); vmcs_write32(seg_encode[seg].limit, lim);
     if (seg != GUEST_GDTR && seg != GUEST_IDTR) {
       vmcs_write32(seg_encode[seg].access, ar); vmcs_write32(seg_encode[seg].selector, sel); }] *)
Definition setDescS : stmt :=
  Seq (selS seg_table)
  (Seq (vmwriteS (Var "eb") (Var "base"))
  (Seq (vmwriteS (Var "el") (Var "lim"))
       (Ite (Bin Eq (Var "seg") (Const 8)) Skip
         (Ite (Bin Eq (Var "seg") (Const 9)) Skip
           (Seq (vmwriteS (Var "ea") (Var "ar")) (vmwriteS (Var "es") (Var "sel"))))))).

Lemma seg_entries : forall seg b l a sl, lookup seg_table seg = Some (b, l, a, sl) ->
  0 <= seg < 10 /\ 0 <= b < NENC /\ 0 <= l < NENC /\ (seg < 8 -> 0 <= a < NENC /\ 0 <= sl < NENC).
Proof.
  intros seg b l a sl H; unfold seg_table in H; simpl in H.
  repeat match type of H with
  | (if (seg =? ?k) then _ else _) = _ => destruct (Z.eqb_spec seg k) as [->|?]
  end; try discriminate.
  all: inversion H; subst; unfold NENC; intuition lia.
Qed.

Theorem set_desc_ref : forall d d' m s seg sel base lim ar, MatchS d m ->
  s "seg" = seg -> s "sel" = norm sel -> s "base" = norm base -> s "lim" = norm lim -> s "ar" = norm ar ->
  vmx_set_desc_spec seg sel base lim ar d = Some d' ->
  exists s' m', exec setDescS s m s' m' /\ MatchS d' m' /\ FrameV m m'.
Proof.
  intros d d' m s seg sel base lim ar HM Hseg Hsel Hb Hl Ha H; unfold vmx_set_desc_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct (vmx_set_desc_aux seg sel base lim ar (data (vmcs d))) as [dt|] eqn:Ed; [|discriminate].
  inversion H; subst d'; clear H.
  unfold vmx_set_desc_aux in Ed.
  destruct (lookup seg_table seg) as [[[[eb el] ea] es]|] eqn:Lk; [|discriminate].
  destruct (seg_entries _ _ _ _ _ Lk) as (Rs & Rb & Rl & Ras).
  destruct (sel_run seg_table s m seg eb el ea es Hseg Lk) as [s1 [Ex1 (E1 & E2 & E3 & E4 & Fr)]].
  assert (G : forall z, z = "seg" \/ z = "sel" \/ z = "base" \/ z = "lim" \/ z = "ar" -> s1 z = s z)
    by (intros z [ -> | [ -> | [ -> | [ -> | -> ]]]]; apply Fr; discriminate).
  set (m1 := upd m (vb + 2 + eb) (norm base)).
  set (m2 := upd m1 (vb + 2 + el) (norm lim)).
  assert (X2 : exec (Seq (vmwriteS (Var "eb") (Var "base")) (vmwriteS (Var "el") (Var "lim"))) s1 m s1 m2).
  { apply ESeq with (s1 := s1) (m1 := m1); apply vmwrite_run; simpl; auto;
      [rewrite G by auto; auto | rewrite G by auto; auto]. }
  assert (M2 : MatchV (VMCSValid (revid (vmcs d)) (abrtid (vmcs d))
                 (zset (zset (data (vmcs d)) eb (Some (norm base))) el (Some (norm lim)))) m2).
  { exact (match_write _ _ el (norm lim) (match_write _ _ eb (norm base) HM Rb) Rl). }
  destruct (seg <? 8) eqn:S8.
  - apply Z.ltb_lt in S8; destruct (Ras S8) as [Ra Rsl].
    inversion Ed; subst dt; clear Ed.
    set (m3 := upd m2 (vb + 2 + ea) (norm ar)).
    exists s1, (upd m3 (vb + 2 + es) (norm sel)); split.
    + apply ESeq with (s1 := s1) (m1 := m); [exact Ex1|].
      apply ESeq with (s1 := s1) (m1 := m1); [apply vmwrite_run; simpl; auto; rewrite G by auto; auto|].
      apply ESeq with (s1 := s1) (m1 := m2); [apply vmwrite_run; simpl; auto; rewrite G by auto; auto|].
      apply EIteF; [simpl; rewrite G by auto; rewrite Hseg; replace (seg =? 8) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
      apply EIteF; [simpl; rewrite G by auto; rewrite Hseg; replace (seg =? 9) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
      apply ESeq with (s1 := s1) (m1 := m3); apply vmwrite_run; simpl; auto; rewrite G by auto; auto.
    + split; [exact (match_write _ _ es (norm sel) (match_write _ _ ea (norm ar) M2 Ra) Rsl)|].
      unfold m3, m2, m1; repeat (eapply frame_trans; [|apply frame_upd; lia]); apply frame_refl.
  - apply Z.ltb_ge in S8.
    inversion Ed; subst dt; clear Ed.
    exists s1, m2; split; [|split; [exact M2|]].
    2: unfold m2, m1; repeat (eapply frame_trans; [|apply frame_upd; lia]); apply frame_refl.
    apply ESeq with (s1 := s1) (m1 := m); [exact Ex1|].
    apply ESeq with (s1 := s1) (m1 := m1); [apply vmwrite_run; simpl; auto; rewrite G by auto; auto|].
    apply ESeq with (s1 := s1) (m1 := m2); [apply vmwrite_run; simpl; auto; rewrite G by auto; auto|].
    destruct (Z.eq_dec seg 8) as [->|N8].
    + apply EIteT; [simpl; rewrite G by auto; rewrite Hseg; discriminate | constructor].
    + assert (E9 : seg = 9) by lia; rewrite E9 in Hseg.
      apply EIteF; [simpl; rewrite G by auto; rewrite Hseg; reflexivity|].
      apply EIteT; [simpl; rewrite G by auto; rewrite Hseg; discriminate | constructor].
Qed.

(** *** [vmx_inject_event] *)
(** [i = vmcs_read32(VMCS_ENTRY_INTR_INFO);
     if (!(i & VMCS_INTERRUPTION_INFO_VALID)) {
       i = VMCS_INTERRUPTION_INFO_VALID | type | vector;
       if (ev == 1) { vmcs_write32(VMCS_ENTRY_INTR_INFO, i | VMCS_INTERRUPTION_INFO_EV);
                      vmcs_write32(VMCS_ENTRY_EXCEPTION_ERROR, errcode); }
       else vmcs_write32(VMCS_ENTRY_INTR_INFO, i); }] *)
Definition injectEventS : stmt :=
  Seq (vmreadS "i" (Const C_VMCS_ENTRY_INTR_INFO))
      (Ite (Bin Eq (Bin And (Var "i") (Const VMCS_INTERRUPTION_INFO_VALID)) (Const 0))
           (Seq (Assign "i" (Bin Or (Bin Or (Const VMCS_INTERRUPTION_INFO_VALID) (Var "type")) (Var "vector")))
                (Ite (Bin Eq (Var "ev") (Const 1))
                     (Seq (vmwriteS (Const C_VMCS_ENTRY_INTR_INFO) (Bin Or (Var "i") (Const VMCS_INTERRUPTION_INFO_EV)))
                          (vmwriteS (Const C_VMCS_ENTRY_EXCEPTION_ERROR) (Var "errcode")))
                     (vmwriteS (Const C_VMCS_ENTRY_INTR_INFO) (Var "i"))))
           Skip).

Theorem inject_event_ref : forall d d' m s type vector errcode ev, MatchS d m ->
  s "type" = type -> s "vector" = vector -> s "errcode" = norm errcode -> s "ev" = ev ->
  vmx_inject_event_spec type vector errcode ev d = Some d' ->
  exists s' m', exec injectEventS s m s' m' /\ MatchS d' m' /\ FrameV m m'.
Proof.
  intros d d' m s type vector errcode ev HM Ht Hv He Hev H; unfold vmx_inject_event_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct (data (vmcs d) C_VMCS_ENTRY_INTR_INFO) as [i|] eqn:Ei; [|discriminate].
  assert (R1 : 0 <= C_VMCS_ENTRY_INTR_INFO < NENC) by (unfold C_VMCS_ENTRY_INTR_INFO, NENC; lia).
  assert (R2 : 0 <= C_VMCS_ENTRY_EXCEPTION_ERROR < NENC) by (unfold C_VMCS_ENTRY_EXCEPTION_ERROR, NENC; lia).
  set (s1 := lset s "i" i).
  assert (L : exec (vmreadS "i" (Const C_VMCS_ENTRY_INTR_INFO)) s m s1 m) by (eapply vmread_run; eauto; reflexivity).
  assert (Q : forall z, z <> "i" -> s1 z = s z) by (intros; unfold s1; apply lset_other; auto).
  destruct (wand i VMCS_INTERRUPTION_INFO_VALID =? 0) eqn:T.
  - set (i2 := wor (wor VMCS_INTERRUPTION_INFO_VALID type) vector) in *.
    set (s2 := lset s1 "i" i2).
    assert (Q2 : forall z, z <> "i" -> s2 z = s z) by (intros; unfold s2; rewrite lset_other by auto; auto).
    assert (A : exec (Assign "i" (Bin Or (Bin Or (Const VMCS_INTERRUPTION_INFO_VALID) (Var "type")) (Var "vector"))) s1 m s2 m).
    { apply exec_assign; simpl; rewrite !Q by discriminate; rewrite Ht, Hv; reflexivity. }
    destruct (ev =? 1) eqn:Tev.
    + inversion H; subst d'; clear H.
      set (m1 := upd m (vb + 2 + C_VMCS_ENTRY_INTR_INFO) (wor i2 VMCS_INTERRUPTION_INFO_EV)).
      exists s2, (upd m1 (vb + 2 + C_VMCS_ENTRY_EXCEPTION_ERROR) (norm errcode)); split.
      * apply ESeq with (s1 := s1) (m1 := m); [exact L|].
        apply EIteT; [simpl; unfold s1; rewrite lset_same, T; discriminate|].
        apply ESeq with (s1 := s2) (m1 := m); [exact A|].
        apply EIteT; [simpl; rewrite Q2 by discriminate; rewrite Hev, Tev; discriminate|].
        apply ESeq with (s1 := s2) (m1 := m1).
        -- apply vmwrite_run; auto; simpl; unfold s2; rewrite lset_same; reflexivity.
        -- apply vmwrite_run; auto; simpl; rewrite Q2 by discriminate; auto.
      * split; [exact (match_write _ _ _ _ (match_write _ _ _ _ HM R1) R2)|].
        unfold m1; repeat (eapply frame_trans; [|apply frame_upd; unfold C_VMCS_ENTRY_EXCEPTION_ERROR, C_VMCS_ENTRY_INTR_INFO in *; lia]); apply frame_refl.
    + inversion H; subst d'; clear H.
      exists s2, (upd m (vb + 2 + C_VMCS_ENTRY_INTR_INFO) i2); split.
      * apply ESeq with (s1 := s1) (m1 := m); [exact L|].
        apply EIteT; [simpl; unfold s1; rewrite lset_same, T; discriminate|].
        apply ESeq with (s1 := s2) (m1 := m); [exact A|].
        apply EIteF; [simpl; rewrite Q2 by discriminate; rewrite Hev, Tev; reflexivity|].
        apply vmwrite_run; auto; simpl; unfold s2; apply lset_same.
      * split; [exact (match_write _ _ _ _ HM R1) | apply frame_upd; lia].
  - inversion H; subst d'; clear H.
    exists s1, m; split; [|split; [exact HM | apply frame_refl]].
    apply ESeq with (s1 := s1) (m1 := m); [exact L|].
    apply EIteF; [simpl; unfold s1; rewrite lset_same, T; reflexivity | constructor].
Qed.

(** *** The readers *)

(** [r = (vmcs_read32(VMCS_ENTRY_INTR_INFO) & VMCS_INTERRUPTION_INFO_VALID) ? 1 : 0;] *)
Definition testBitS (enc mask : Z) : stmt :=
  Seq (vmreadS "c" (Const enc))
      (Ite (Bin Eq (Bin And (Var "c") (Const mask)) (Const 0)) (Assign "r" (Const 0)) (Assign "r" (Const 1))).

Lemma test_bit_run : forall d m s enc mask c, MatchS d m -> 0 <= enc < NENC -> data (vmcs d) enc = Some c ->
  exists s', exec (testBitS enc mask) s m s' m /\ s' "r" = (if wand c mask =? 0 then 0 else 1).
Proof.
  intros d m s enc mask c HM Hr Hc.
  assert (L : exec (vmreadS "c" (Const enc)) s m (lset s "c" c) m) by (eapply vmread_run; eauto; reflexivity).
  destruct (wand c mask =? 0) eqn:T.
  - exists (lset (lset s "c" c) "r" 0); split; [|apply lset_same].
    apply ESeq with (s1 := lset s "c" c) (m1 := m); [exact L|].
    apply EIteT; [simpl; rewrite lset_same, T; discriminate | apply exec_assign; reflexivity].
  - exists (lset (lset s "c" c) "r" 1); split; [|apply lset_same].
    apply ESeq with (s1 := lset s "c" c) (m1 := m); [exact L|].
    apply EIteF; [simpl; rewrite lset_same, T; reflexivity | apply exec_assign; reflexivity].
Qed.

Definition checkPendingS : stmt := testBitS C_VMCS_ENTRY_INTR_INFO VMCS_INTERRUPTION_INFO_VALID.
Definition checkIntShadowS : stmt :=
  testBitS C_VMCS_GUEST_INTERRUPTIBILITY VMCS_INTERRUPTIBILITY_STI_or_MOVSS_BLOCKING.

Theorem check_pending_ref : forall d m s r, MatchS d m -> vmx_check_pending_event_spec d = Some r ->
  exists s', exec checkPendingS s m s' m /\ s' "r" = r.
Proof.
  intros d m s r HM H; unfold vmx_check_pending_event_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct (data (vmcs d) C_VMCS_ENTRY_INTR_INFO) as [c|] eqn:Ec; [|discriminate].
  destruct (test_bit_run d m s C_VMCS_ENTRY_INTR_INFO VMCS_INTERRUPTION_INFO_VALID c HM ltac:(unfold C_VMCS_ENTRY_INTR_INFO, NENC; lia) Ec)
    as [s' [Ex Hr]].
  exists s'; split; [exact Ex|]; rewrite Hr.
  destruct (wand c VMCS_INTERRUPTION_INFO_VALID =? 0); inversion H; reflexivity.
Qed.

Theorem check_int_shadow_ref : forall d m s r, MatchS d m -> vmx_check_int_shadow_spec d = Some r ->
  exists s', exec checkIntShadowS s m s' m /\ s' "r" = r.
Proof.
  intros d m s r HM H; unfold vmx_check_int_shadow_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct (data (vmcs d) C_VMCS_GUEST_INTERRUPTIBILITY) as [c|] eqn:Ec; [|discriminate].
  destruct (test_bit_run d m s C_VMCS_GUEST_INTERRUPTIBILITY VMCS_INTERRUPTIBILITY_STI_or_MOVSS_BLOCKING c HM
    ltac:(unfold C_VMCS_GUEST_INTERRUPTIBILITY, NENC; lia) Ec) as [s' [Ex Hr]].
  exists s'; split; [exact Ex|]; rewrite Hr.
  destruct (wand c VMCS_INTERRUPTIBILITY_STI_or_MOVSS_BLOCKING =? 0); inversion H; reflexivity.
Qed.

(** [r = vmcs_read32(VMCS_EXIT_REASON) & EXIT_REASON_MASK;] *)
Definition exitReasonS : stmt :=
  Seq (vmreadS "c" (Const C_VMCS_EXIT_REASON)) (Assign "r" (Bin And (Var "c") (Const EXIT_REASON_MASK))).

Theorem exit_reason_ref : forall d m s r, MatchS d m -> vmx_get_exit_reason_spec d = Some r ->
  exists s', exec exitReasonS s m s' m /\ s' "r" = r.
Proof.
  intros d m s r HM H; unfold vmx_get_exit_reason_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct (data (vmcs d) C_VMCS_EXIT_REASON) as [c|] eqn:Ec; [|discriminate].
  inversion H; subst r.
  exists (lset (lset s "c" c) "r" (wand c EXIT_REASON_MASK)); split; [|apply lset_same].
  apply ESeq with (s1 := lset s "c" c) (m1 := m).
  - apply (vmread_run (vmcs d) m s "c" (Const C_VMCS_EXIT_REASON) C_VMCS_EXIT_REASON c HM);
      [reflexivity | unfold C_VMCS_EXIT_REASON, NENC; lia | exact Ec].
  - apply exec_assign; simpl; rewrite lset_same; reflexivity.
Qed.

(** [r = vmcs_read32(VMCS_GUEST_PHYSICAL_ADDRESS);] *)
Definition exitFaultAddrS : stmt := vmreadS "r" (Const C_VMCS_GUEST_PHYSICAL_ADDRESS).

Theorem exit_fault_addr_ref : forall d m s r, MatchS d m -> vmx_get_exit_fault_addr_spec d = Some r ->
  exec exitFaultAddrS s m (lset s "r" r) m.
Proof.
  intros d m s r HM H; unfold vmx_get_exit_fault_addr_spec in H.
  apply flags_true in H; destruct H as [_ H].
  apply (vmread_run (vmcs d) m s "r" (Const C_VMCS_GUEST_PHYSICAL_ADDRESS) C_VMCS_GUEST_PHYSICAL_ADDRESS r HM);
    [reflexivity | unfold C_VMCS_GUEST_PHYSICAL_ADDRESS, NENC; lia | exact H].
Qed.

(** [vmx_set_tsc_offset] and [vmx_get_tsc_offset]: [vmcs_write64] and [vmcs_read64] at
    [VMCS_TSC_OFFSET]. *)
Definition setTscS : stmt := Seq (Assign "enc" (Const C_VMCS_TSC_OFFSET)) writez64S.
Definition getTscS : stmt := Seq (Assign "enc" (Const C_VMCS_TSC_OFFSET)) readz64S.

Lemma tsc_valid : valid_enc C_VMCS_TSC_OFFSET = true.
Proof. reflexivity. Qed.

Theorem set_tsc_ref : forall d d' m s v, MatchS d m -> s "lo" = v mod W -> s "hi" = (v / W) mod W ->
  vmx_set_tsc_offset_spec v d = Some d' -> exists s' m', exec setTscS s m s' m' /\ MatchS d' m' /\ FrameV m m'.
Proof.
  intros d d' m s v HM Hlo Hhi H; unfold vmx_set_tsc_offset_spec in H.
  apply flags_true in H; destruct H as [Hf H].
  assert (H' : vmcs_writez64_spec C_VMCS_TSC_OFFSET v d = Some d')
    by (unfold vmcs_writez64_spec; rewrite Hf, tsc_valid; exact H).
  destruct (writez64_ref d d' m (lset s "enc" C_VMCS_TSC_OFFSET) C_VMCS_TSC_OFFSET v HM (lset_same _ _ _)
    ltac:(rewrite lset_other by discriminate; auto) ltac:(rewrite lset_other by discriminate; auto) H')
    as [m' [Ex [HM' Fr]]].
  exists (lset s "enc" C_VMCS_TSC_OFFSET), m'; split; [|split; [exact HM' | exact Fr]].
  apply ESeq with (s1 := lset s "enc" C_VMCS_TSC_OFFSET) (m1 := m); [apply exec_assign; reflexivity | exact Ex].
Qed.

Theorem get_tsc_ref : forall d m s r, MatchS d m -> vmx_get_tsc_offset_spec d = Some r ->
  exists s' lo hi, exec getTscS s m s' m /\ r = Z64ofwords hi lo /\ s' "lo" = lo /\ s' "hi" = hi.
Proof.
  intros d m s r HM H; unfold vmx_get_tsc_offset_spec in H.
  apply flags_true in H; destruct H as [Hf H].
  assert (H' : vmcs_readz64_spec C_VMCS_TSC_OFFSET d = Some r)
    by (unfold vmcs_readz64_spec; rewrite Hf, tsc_valid; exact H).
  destruct (readz64_ref d m (lset s "enc" C_VMCS_TSC_OFFSET) C_VMCS_TSC_OFFSET r HM (lset_same _ _ _) H')
    as [s' [lo [hi [Ex R]]]].
  exists s', lo, hi; split; [|exact R].
  apply ESeq with (s1 := lset s "enc" C_VMCS_TSC_OFFSET) (m1 := m); [apply exec_assign; reflexivity | exact Ex].
Qed.

(** *** The revision id and the abort indicator *)
Definition getRevidS : stmt := Load "r" (Const vb).
Definition setRevidS : stmt := Store (Const vb) (Var "revid").
Definition getAbrtidS : stmt := Load "r" (Const (vb + 1)).
Definition setAbrtidS : stmt := Store (Const (vb + 1)) (Var "abrtid").

Theorem get_revid_ref : forall d m s r, MatchS d m -> vmcs_get_revid_spec d = Some r ->
  exec getRevidS s m (lset s "r" r) m.
Proof.
  intros d m s r (H1 & _ & _) H; unfold vmcs_get_revid_spec in H.
  apply flags_true in H; destruct H as [_ H].
  rewrite <- (H1 r H); apply exec_load; reflexivity.
Qed.

Theorem set_revid_ref : forall d d' m s r, MatchS d m -> s "revid" = norm r ->
  vmcs_set_revid_spec r d = Some d' -> exec setRevidS s m s (upd m vb (norm r)) /\ MatchS d' (upd m vb (norm r)).
Proof.
  intros d d' m s r (H1 & H2 & H3) Hs H; unfold vmcs_set_revid_spec in H.
  apply flags_true in H; destruct H as [_ H]; inversion H; subst d'; clear H.
  split; [apply exec_store; simpl; auto|].
  split; [|split].
  - intros x Hx; simpl in Hx; inversion Hx; apply upd_same.
  - intros a Ha; simpl in Ha; rewrite upd_other by lia; auto.
  - intros e x He Hx; simpl in Hx; rewrite upd_other by (unfold NENC in *; lia); auto.
Qed.

Theorem get_abrtid_ref : forall d m s a, MatchS d m -> vmcs_get_abrtid_spec d = Some a ->
  exec getAbrtidS s m (lset s "r" a) m.
Proof.
  intros d m s a (_ & H2 & _) H; unfold vmcs_get_abrtid_spec in H.
  apply flags_true in H; destruct H as [_ H].
  rewrite <- (H2 a H); apply exec_load; reflexivity.
Qed.

Theorem set_abrtid_ref : forall d d' m s a, MatchS d m -> s "abrtid" = norm a ->
  vmcs_set_abrtid_spec a d = Some d' ->
  exec setAbrtidS s m s (upd m (vb + 1) (norm a)) /\ MatchS d' (upd m (vb + 1) (norm a)).
Proof.
  intros d d' m s a (H1 & H2 & H3) Hs H; unfold vmcs_set_abrtid_spec in H.
  apply flags_true in H; destruct H as [_ H]; inversion H; subst d'; clear H.
  split; [apply exec_store; simpl; auto|].
  split; [|split].
  - intros x Hx; simpl in Hx; rewrite upd_other by lia; auto.
  - intros x Hx; simpl in Hx; inversion Hx; apply upd_same.
  - intros e x He Hx; simpl in Hx; rewrite upd_other by (unfold NENC in *; lia); auto.
Qed.

End Code.
