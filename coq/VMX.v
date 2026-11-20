(** * The VMX layer: guest registers, VM entry and VM exit, ported and implemented

    Ported from [objects/ObjVMX.v]: the [vmx] structure (guest registers,
    exit information, saved host registers; 36 words), and the
    specifications [vmx_readz_spec], [vmx_writez_spec], [vmx_get_reg_spec],
    [vmx_set_reg_spec], [vmx_get_next_eip_spec], [vmx_get_io_width_spec],
    [vmx_get_io_write_spec], [vmx_get_exit_io_rep_spec],
    [vmx_get_exit_io_str_spec], [vmx_get_exit_io_port_spec],
    [vmx_set_mmap_spec], [vmx_enter_pre_spec], [vm_run_spec],
    [vmx_exit_post_spec], [vmx_return_from_guest_spec].

    The state combines the three parts: the [vmx] structure at [xb], the VMCS
    at [vb] ([VMCS.v]) and the EPT at [eb] ([EPT.v]), in disjoint blocks of
    the kernel region.

    Entering and leaving the guest:
    - [vm_run] is [vmx_enter_pre] (copy the guest [eip] into the VMCS) and
      [vmx_enter] (assembly in mCertiKOS: save the host [ebp] and [edi], load
      the guest registers), then [vmlaunch]/[vmresume].
    - [vmx_return_from_guest] is the reverse: [vmx_exit] (assembly: save the
      guest registers, load the host [ebp] and [edi]) and [vmx_exit_post]
      (copy [eip], the exit reason and the exit qualification out of the
      VMCS).
    Here the processor's registers are the locals ["EAX"], ["EBX"], ["EDX"],
    ["ESI"], ["EDI"], ["EBP"], ["RA"]. The code is what runs between the
    hardware transitions; the transitions themselves ([vmlaunch] and the VM
    exit) are the machine's, and change only the flag [ihost], as [trap_in]
    changes [ikern] in the Lean development.

    What differs:
    - The C operations on words are [wand], [norm] (32-bit). Right shifts of
      the exit qualification are divisions ([q >> 3] is [q / 8]); on 32-bit
      unsigned words they agree.
    - [vmx_get_next_eip_spec] wraps the sum to 32 bits, as the C [unsigned]
      addition does; mCertiKOS's specification adds in [Z] and the result is
      cast to a word when returned.
    - A register holds a word or nothing ([None] for [Vundef]).
    - [vmx_init_spec] is not here. *)

From Stdlib Require Import ZArith String Lia Bool List.
From VCoq Require Import Lang.
From VCoq Require EPT VMCS.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope bool_scope.
Open Scope Z_scope.

(** ** Abstract data *)

Record XSt := mkX {
  xikern : bool; xpg : bool; xihost : bool; xinit : bool;
  vmx : Z -> option Z;            (* the vmx structure, 36 words *)
  xvmcs : VMCS.VMCS;
  xept : EPT.EPT }.

Definition zset {A} (f : Z -> A) (k : Z) (v : A) : Z -> A :=
  fun x => if Z.eq_dec x k then v else f x.

Definition set_vmx (d : XSt) (x : Z -> option Z) : XSt :=
  mkX (xikern d) (xpg d) (xihost d) (xinit d) x (xvmcs d) (xept d).
Definition set_xvmcs (d : XSt) (v : VMCS.VMCS) : XSt :=
  mkX (xikern d) (xpg d) (xihost d) (xinit d) (vmx d) v (xept d).
Definition set_xept (d : XSt) (e : EPT.EPT) : XSt :=
  mkX (xikern d) (xpg d) (xihost d) (xinit d) (vmx d) (xvmcs d) e.
Definition set_ihost (d : XSt) (b : bool) : XSt :=
  mkX (xikern d) (xpg d) b (xinit d) (vmx d) (xvmcs d) (xept d).

(** The views the two lower layers work on. *)
Definition toE (d : XSt) : EPT.VData := EPT.mkV (xikern d) (xpg d) (xihost d) (xept d).
Definition toC (d : XSt) : VMCS.VSt := VMCS.mkS (xikern d) (xpg d) (xihost d) (xvmcs d).

Definition VMX_G_RAX' := 0.
Definition VMX_G_RBX' := 2.
Definition VMX_G_RDX' := 6.
Definition VMX_G_RSI' := 8.
Definition VMX_G_RDI' := 10.
Definition VMX_G_RBP' := 12.
Definition VMX_G_RIP' := 14.
Definition VMX_G_CR2' := 16.
Definition VMX_EXIT_REASON' := 27.
Definition VMX_EXIT_QUALIFICATION' := 28.
Definition VMX_LAUNCHED' := 31.
Definition VMX_HOST_EBP' := 33.
Definition VMX_HOST_EDI' := 34.
Definition VMX_Size' := 36.

Definition C_VMCS_GUEST_RIP := 26654.
Definition C_VMCS_GUEST_RSP := 26652.
Definition C_VMCS_GUEST_RFLAGS := 26656.
Definition C_VMCS_GUEST_CR0 := 26624.
Definition C_VMCS_GUEST_CR3 := 26626.
Definition C_VMCS_GUEST_CR4 := 26628.
Definition C_VMCS_EXIT_INSTRUCTION_LENGTH := 17420.
Definition C_VMCS_EXIT_QUALIFICATION := 25600.
Definition C_VMCS_EXIT_REASON := 17410.

(** Where each guest register lives: a word of [vmx], or a VMCS field. *)
Inductive reg_type := TVMCS (z : Z) | TVMX (z : Z).

Definition reg_table : list (Z * reg_type) :=
  [(0, TVMX VMX_G_RAX'); (1, TVMX VMX_G_RBX'); (2, TVMX 4); (3, TVMX VMX_G_RDX');
   (4, TVMX VMX_G_RSI'); (5, TVMX VMX_G_RDI'); (11, TVMX VMX_G_CR2'); (6, TVMX VMX_G_RBP');
   (8, TVMX VMX_G_RIP');
   (7, TVMCS C_VMCS_GUEST_RSP); (9, TVMCS C_VMCS_GUEST_RFLAGS); (10, TVMCS C_VMCS_GUEST_CR0);
   (12, TVMCS C_VMCS_GUEST_CR3); (13, TVMCS C_VMCS_GUEST_CR4)].

Fixpoint lookup (t : list (Z * reg_type)) (k : Z) : option reg_type :=
  match t with
  | [] => None
  | (k', r) :: t' => if Z.eqb k k' then Some r else lookup t' k
  end.

(** [Z2reg_type] *)
Definition Z2reg_type (reg : Z) : option reg_type := lookup reg_table reg.

(** ** Specifications ([ObjVMX.v]) *)

Section Specs.
Variable maxpage : Z.

Definition flags (d : XSt) : bool := xikern d && xpg d && xihost d.

Definition vmx_readz_spec (i : Z) (d : XSt) : option Z :=
  if flags d then if (0 <=? i) && (i <? VMX_Size') then vmx d i else None else None.

Definition vmx_writez_spec (i value : Z) (d : XSt) : option XSt :=
  if flags d then
    if (0 <=? i) && (i <? VMX_Size') then Some (set_vmx d (zset (vmx d) i (Some (norm value)))) else None
  else None.

Definition vmx_get_reg_spec (reg : Z) (d : XSt) : option Z :=
  if flags d then
    match Z2reg_type reg with
    | Some (TVMX z) => vmx d z
    | Some (TVMCS z) => VMCS.data (xvmcs d) z
    | None => None
    end
  else None.

Definition vmx_set_reg_spec (reg v : Z) (d : XSt) : option XSt :=
  if flags d then
    match Z2reg_type reg with
    | Some (TVMX z) => Some (set_vmx d (zset (vmx d) z (Some (norm v))))
    | Some (TVMCS z) =>
      Some (set_xvmcs d (VMCS.VMCSValid (VMCS.revid (xvmcs d)) (VMCS.abrtid (xvmcs d))
              (zset (VMCS.data (xvmcs d)) z (Some (norm v)))))
    | None => None
    end
  else None.

Definition vmx_get_next_eip_spec (d : XSt) : option Z :=
  if flags d then
    match vmx d VMX_G_RIP', VMCS.data (xvmcs d) C_VMCS_EXIT_INSTRUCTION_LENGTH with
    | Some v1, Some v2 => Some (norm (v1 + v2))
    | _, _ => None
    end
  else None.

Definition qual (d : XSt) : option Z :=
  if flags d then vmx d VMX_EXIT_QUALIFICATION' else None.

Definition vmx_get_io_width_spec (d : XSt) : option Z :=
  match qual d with
  | Some q =>
    let sz := wand q 7 in
    if sz =? 0 then Some 0 else if sz =? 1 then Some 1 else Some 2
  | None => None
  end.

Definition vmx_get_io_write_spec (d : XSt) : option Z :=
  match qual d with
  | Some q => if wand (q / 8) 1 =? 1 then Some 0 else Some 1
  | None => None
  end.

Definition vmx_get_exit_io_rep_spec (d : XSt) : option Z :=
  match qual d with Some q => Some (wand (q / 32) 1) | None => None end.

Definition vmx_get_exit_io_str_spec (d : XSt) : option Z :=
  match qual d with Some q => Some (wand (q / 16) 1) | None => None end.

Definition vmx_get_exit_io_port_spec (d : XSt) : option Z :=
  match qual d with Some q => Some (q / 65536) | None => None end.

(** [vmx_set_mmap]: add the mapping, then invalidate the EPT TLB. *)
Definition vmx_set_mmap_spec (gpa hpa memtype : Z) (d : XSt) : option (XSt * Z) :=
  match EPT.ept_add_mapping_spec maxpage gpa hpa memtype (toE d) with
  | Some (e', res) =>
    if (0 <=? res) && (res <=? EPT.max_unsigned) then
      if (0 <=? memtype) && (memtype <? 4096) then
        if res =? 0 then
          match EPT.ept_invalidate_mappings_spec e' with
          | Some z => Some (set_xept d (EPT.ept e'), z)
          | None => None
          end
        else Some (set_xept d (EPT.ept e'), res)
      else None
    else None
  | None => None
  end.

(** [vm_run_spec]: the guest's [eip] goes to the VMCS, the host's [ebp] and
    [edi] are saved, the guest registers are loaded, and the processor is in
    guest mode. [rebp], [redi]: the host registers at the call. *)
Definition vm_run_spec (rebp redi : Z) (d : XSt) : option XSt :=
  if xikern d && xpg d && xihost d && xinit d then
    match vmx d VMX_G_RIP' with
    | Some v =>
      let dt' := zset (VMCS.data (xvmcs d)) C_VMCS_GUEST_RIP (Some v) in
      let x2 := zset (zset (vmx d) VMX_HOST_EBP' (Some rebp)) VMX_HOST_EDI' (Some redi) in
      Some (set_ihost (set_xvmcs (set_vmx d x2)
              (VMCS.VMCSValid (VMCS.revid (xvmcs d)) (VMCS.abrtid (xvmcs d)) dt')) false)
    | None => None
    end
  else None.

(** [vmx_return_from_guest_spec]: the guest registers at the exit are saved,
    [eip], the exit reason and the exit qualification come out of the VMCS,
    and the processor is in host mode. *)
Definition vmx_return_from_guest_spec (redi reax rebx redx resi rebp : Z) (d : XSt) : option XSt :=
  if xikern d && xpg d && negb (xihost d) && xinit d then
    let x7 := zset (zset (zset (zset (zset (zset (vmx d) VMX_G_RDI' (Some redi)) VMX_G_RAX' (Some reax))
                VMX_G_RBX' (Some rebx)) VMX_G_RDX' (Some redx)) VMX_G_RSI' (Some resi)) VMX_G_RBP' (Some rebp) in
    match VMCS.data (xvmcs d) C_VMCS_GUEST_RIP, VMCS.data (xvmcs d) C_VMCS_EXIT_REASON,
          VMCS.data (xvmcs d) C_VMCS_EXIT_QUALIFICATION with
    | Some v1, Some v2, Some v3 =>
      let x11 := zset (zset (zset (zset x7 VMX_G_RIP' (Some v1)) VMX_EXIT_REASON' (Some v2))
                   VMX_EXIT_QUALIFICATION' (Some v3)) VMX_LAUNCHED' (Some 1) in
      Some (set_ihost (set_vmx d x11) true)
    | _, _, _ => None
    end
  else None.

End Specs.

(** ** The three blocks in the region *)

Section Code.
Variables xb vb eb : Z.
Hypothesis hxb : 0 <= xb.
Hypothesis hxv : xb + VMX_Size' <= vb.
Hypothesis hve : vb + 65540 <= eb.
Hypothesis heb2 : eb + EPT.NPG <= W.
Variable maxpage : Z.
Hypothesis hmp : maxpage <= EPT.NPG.

Definition MatchX (d : XSt) (m : mem) : Prop :=
  (forall i v, 0 <= i < VMX_Size' -> vmx d i = Some v -> m (xb + i) = v) /\
  VMCS.MatchV vb (xvmcs d) m /\ EPT.MatchE eb (toE d) m.

Lemma heb : 0 <= eb.
Proof. unfold VMX_Size' in *; lia. Qed.
Lemma hvb : 0 <= vb.
Proof. unfold VMX_Size' in *; lia. Qed.
Lemma hvb2 : vb + 65540 <= W.
Proof. unfold EPT.NPG in *; lia. Qed.

Lemma matchV_frame : forall v m m', VMCS.MatchV vb v m ->
  (forall a, vb <= a < vb + 2 + VMCS.NENC -> m' a = m a) -> VMCS.MatchV vb v m'.
Proof.
  intros v m m' (H1 & H2 & H3) F; unfold VMCS.NENC in *; split; [|split].
  - intros r Hr; rewrite F by lia; auto.
  - intros a Ha; rewrite F by lia; auto.
  - intros e x He Hx; rewrite F by (unfold VMCS.NENC in *; lia); auto.
Qed.

Lemma matchE_frame : forall e m m', EPT.MatchE eb e m ->
  (forall a, eb <= a < eb + EPT.NPG -> m' a = m a) -> EPT.MatchE eb e m'.
Proof. intros e m m' H F g h Hg Hl; rewrite F by lia; auto. Qed.

(** A write to a word of [vmx]. *)
Lemma match_vmx_write : forall d m i w, MatchX d m -> 0 <= i < VMX_Size' ->
  MatchX (set_vmx d (zset (vmx d) i (Some w))) (upd m (xb + i) w).
Proof.
  intros d m i w (H1 & H2 & H3) Hi; unfold VMX_Size' in *; split; [|split].
  - intros j v Hj Hv; simpl in Hv; unfold zset in Hv.
    destruct (Z.eq_dec j i) as [->|Ne]; [inversion Hv; apply upd_same | rewrite upd_other by lia; auto].
  - apply (matchV_frame _ m); auto; intros a Ha; apply upd_other; unfold VMCS.NENC in *; lia.
  - apply (matchE_frame _ m); auto; intros a Ha; apply upd_other; unfold EPT.NPG in *; lia.
Qed.

(** A write to a field of the VMCS. *)
Lemma match_vmcs_write : forall d m k w, MatchX d m -> 0 <= k < VMCS.NENC ->
  MatchX (set_xvmcs d (VMCS.VMCSValid (VMCS.revid (xvmcs d)) (VMCS.abrtid (xvmcs d))
            (zset (VMCS.data (xvmcs d)) k (Some w)))) (upd m (vb + 2 + k) w).
Proof.
  intros d m k w (H1 & H2 & H3) Hk; unfold VMX_Size', VMCS.NENC in *; split; [|split].
  - intros j v Hj Hv; unfold VMX_Size' in Hj; simpl in Hv; rewrite upd_other by lia; auto.
  - exact (VMCS.match_write vb (xvmcs d) m k w H2 Hk).
  - apply (matchE_frame _ m); auto; intros a Ha; apply upd_other; unfold EPT.NPG in *; lia.
Qed.

Lemma match_ihost : forall d m b, MatchX d m -> MatchX (set_ihost d b) m.
Proof. intros d m b (H1 & H2 & H3); split; [|split]; auto. Qed.

(** [&vmx.field]: the cell [xb + i]. *)
Definition xE (i : Z) : expr := Const (xb + i).

Lemma vmx_load : forall d m s x i v, MatchX d m -> 0 <= i < VMX_Size' -> vmx d i = Some v ->
  exec (Load x (xE i)) s m (lset s x v) m.
Proof.
  intros d m s x i v (H1 & _ & _) Hi Hv; rewrite <- (H1 i v Hi Hv); apply exec_load; reflexivity.
Qed.

Lemma vmcs_load : forall d m s x k v, MatchX d m -> 0 <= k < VMCS.NENC -> VMCS.data (xvmcs d) k = Some v ->
  exec (VMCS.vmreadS vb x (Const k)) s m (lset s x v) m.
Proof.
  intros d m s x k v (_ & H2 & _) Hk Hv.
  exact (VMCS.vmread_run vb hvb hvb2 (xvmcs d) m s x (Const k) k v H2 eq_refl Hk Hv).
Qed.

Lemma vmcs_store : forall m s k e w, 0 <= k < VMCS.NENC -> eval s e = w ->
  exec (VMCS.vmwriteS vb (Const k) e) s m s (upd m (vb + 2 + k) w).
Proof. intros m s k e w Hk He; exact (VMCS.vmwrite_run vb hvb hvb2 m s (Const k) e k w eq_refl Hk He). Qed.

Lemma flags_true : forall (d : XSt) (A : Type) (x : option A) (y : A),
  (if flags d then x else None) = Some y -> flags d = true /\ x = Some y.
Proof. intros d A x y H; destruct (flags d); [auto | discriminate]. Qed.

(** *** [vmx_readz], [vmx_writez]: word [i] of [vmx]. *)
Definition readzS : stmt := Load "r" (Bin Add (Const xb) (Var "i")).
Definition writezS : stmt := Store (Bin Add (Const xb) (Var "i")) (Var "value").

Lemma eval_xi : forall s i, s "i" = i -> 0 <= i < VMX_Size' -> eval s (Bin Add (Const xb) (Var "i")) = xb + i.
Proof.
  intros s i Hs Hi; simpl; rewrite Hs; apply norm_small; unfold VMX_Size', EPT.NPG in *; lia.
Qed.

Theorem readz_ref : forall d m s i r, MatchX d m -> s "i" = i -> vmx_readz_spec i d = Some r ->
  exec readzS s m (lset s "r" r) m.
Proof.
  intros d m s i r HM Hs H; unfold vmx_readz_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct ((0 <=? i) && (i <? VMX_Size')) eqn:R; [|discriminate].
  apply andb_true_iff in R; destruct R as [R1 R2]; apply Z.leb_le in R1; apply Z.ltb_lt in R2.
  destruct HM as (H1 & _ & _).
  rewrite <- (H1 i r ltac:(lia) H); apply exec_load, eval_xi; auto; lia.
Qed.

Theorem writez_ref : forall d d' m s i value, MatchX d m -> s "i" = i -> s "value" = norm value ->
  vmx_writez_spec i value d = Some d' -> exists m', exec writezS s m s m' /\ MatchX d' m'.
Proof.
  intros d d' m s i value HM Hs Hv H; unfold vmx_writez_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct ((0 <=? i) && (i <? VMX_Size')) eqn:R; [|discriminate].
  apply andb_true_iff in R; destruct R as [R1 R2]; apply Z.leb_le in R1; apply Z.ltb_lt in R2.
  inversion H; subst d'; clear H.
  exists (upd m (xb + i) (norm value)); split.
  - apply exec_store; [apply eval_xi; auto; lia | simpl; auto].
  - apply match_vmx_write; auto; lia.
Qed.

(** *** [vmx_get_reg] and [vmx_set_reg]: a [switch] on the register. *)

Definition regGetBody (t : reg_type) : stmt :=
  match t with
  | TVMX z => Load "r" (xE z)
  | TVMCS z => VMCS.vmreadS vb "r" (Const z)
  end.

Definition regSetBody (t : reg_type) : stmt :=
  match t with
  | TVMX z => Store (xE z) (Var "v")
  | TVMCS z => VMCS.vmwriteS vb (Const z) (Var "v")
  end.

Fixpoint switchS (body : reg_type -> stmt) (t : list (Z * reg_type)) : stmt :=
  match t with
  | [] => Skip
  | (k, r) :: t' => Ite (Bin Eq (Var "reg") (Const k)) (body r) (switchS body t')
  end.

Lemma switch_run : forall body t s m s' m' reg r, s "reg" = reg -> lookup t reg = Some r ->
  exec (body r) s m s' m' -> exec (switchS body t) s m s' m'.
Proof.
  induction t as [|[k r0] t IH]; intros s m s' m' reg r Hs Hl Hb; simpl in Hl; [discriminate|].
  simpl; destruct (reg =? k) eqn:E.
  - inversion Hl; subst r0; apply EIteT; [simpl; rewrite Hs, E; discriminate | exact Hb].
  - apply EIteF; [simpl; rewrite Hs, E; reflexivity | eapply IH; eauto].
Qed.

Lemma reg_bounds : forall reg t, Z2reg_type reg = Some t ->
  match t with TVMX z => 0 <= z < VMX_Size' | TVMCS z => 0 <= z < VMCS.NENC end.
Proof.
  intros reg t H; unfold Z2reg_type, reg_table in H; simpl in H.
  repeat match type of H with
  | (if (reg =? ?k) then _ else _) = _ => destruct (Z.eqb_spec reg k) as [->|?]
  end; try discriminate; inversion H; subst;
  unfold VMX_Size', VMCS.NENC, VMX_G_RAX', VMX_G_RBX', VMX_G_RDX', VMX_G_RSI', VMX_G_RDI', VMX_G_RBP',
    VMX_G_RIP', VMX_G_CR2', C_VMCS_GUEST_RSP, C_VMCS_GUEST_RFLAGS, C_VMCS_GUEST_CR0, C_VMCS_GUEST_CR3,
    C_VMCS_GUEST_CR4; simpl; lia.
Qed.

Definition getRegS : stmt := switchS regGetBody reg_table.
Definition setRegS : stmt := switchS regSetBody reg_table.

Theorem get_reg_ref : forall d m s reg r, MatchX d m -> s "reg" = reg -> vmx_get_reg_spec reg d = Some r ->
  exec getRegS s m (lset s "r" r) m.
Proof.
  intros d m s reg r HM Hs H; unfold vmx_get_reg_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct (Z2reg_type reg) as [t|] eqn:Et; [|discriminate].
  pose proof (reg_bounds _ _ Et) as B.
  apply (switch_run regGetBody reg_table s m _ _ reg t Hs Et).
  destruct t as [z|z]; simpl.
  - eapply vmcs_load; eauto.
  - eapply vmx_load; eauto.
Qed.

Theorem set_reg_ref : forall d d' m s reg v, MatchX d m -> s "reg" = reg -> s "v" = norm v ->
  vmx_set_reg_spec reg v d = Some d' -> exists m', exec setRegS s m s m' /\ MatchX d' m'.
Proof.
  intros d d' m s reg v HM Hs Hv H; unfold vmx_set_reg_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct (Z2reg_type reg) as [t|] eqn:Et; [|discriminate].
  pose proof (reg_bounds _ _ Et) as B.
  destruct t as [z|z]; inversion H; subst d'; clear H.
  - exists (upd m (vb + 2 + z) (norm v)); split.
    + apply (switch_run regSetBody reg_table s m _ _ reg (TVMCS z) Hs Et).
      apply vmcs_store; auto.
    + apply match_vmcs_write; auto.
  - exists (upd m (xb + z) (norm v)); split.
    + apply (switch_run regSetBody reg_table s m _ _ reg (TVMX z) Hs Et).
      apply exec_store; [reflexivity | simpl; auto].
    + apply match_vmx_write; auto.
Qed.

(** *** [vmx_get_next_eip]: [r = vmx.g_rip + vmcs_read32(VMCS_EXIT_INSTRUCTION_LENGTH);] *)
Definition nextEipS : stmt :=
  Seq (Load "t" (xE VMX_G_RIP'))
  (Seq (VMCS.vmreadS vb "u" (Const C_VMCS_EXIT_INSTRUCTION_LENGTH))
       (Assign "r" (Bin Add (Var "t") (Var "u")))).

Theorem next_eip_ref : forall d m s r, MatchX d m -> vmx_get_next_eip_spec d = Some r ->
  exists s', exec nextEipS s m s' m /\ s' "r" = r.
Proof.
  intros d m s r HM H; unfold vmx_get_next_eip_spec in H.
  apply flags_true in H; destruct H as [_ H].
  destruct (vmx d VMX_G_RIP') as [v1|] eqn:E1; [|discriminate].
  destruct (VMCS.data (xvmcs d) C_VMCS_EXIT_INSTRUCTION_LENGTH) as [v2|] eqn:E2; [|discriminate].
  inversion H; subst r.
  exists (lset (lset (lset s "t" v1) "u" v2) "r" (norm (v1 + v2))); split; [|apply lset_same].
  apply ESeq with (s1 := lset s "t" v1) (m1 := m).
  - eapply vmx_load; eauto; unfold VMX_G_RIP', VMX_Size'; lia.
  - apply ESeq with (s1 := lset (lset s "t" v1) "u" v2) (m1 := m).
    + eapply vmcs_load; eauto; unfold C_VMCS_EXIT_INSTRUCTION_LENGTH, VMCS.NENC; lia.
    + apply exec_assign; simpl; rewrite lset_same, lset_other, lset_same by discriminate; reflexivity.
Qed.

(** *** The exit qualification *)
Definition loadQualS : stmt := Load "q" (xE VMX_EXIT_QUALIFICATION').

Lemma qual_load : forall d m s q, MatchX d m -> qual d = Some q -> exec loadQualS s m (lset s "q" q) m.
Proof.
  intros d m s q HM H; unfold qual in H; apply flags_true in H; destruct H as [_ H].
  eapply vmx_load; eauto; unfold VMX_EXIT_QUALIFICATION', VMX_Size'; lia.
Qed.

(** [sz = q & 7; r = sz == 0 ? SZ8 : sz == 1 ? SZ16 : SZ32;] *)
Definition ioWidthS : stmt :=
  Seq loadQualS
  (Seq (Assign "sz" (Bin And (Var "q") (Const 7)))
       (Ite (Bin Eq (Var "sz") (Const 0)) (Assign "r" (Const 0))
            (Ite (Bin Eq (Var "sz") (Const 1)) (Assign "r" (Const 1)) (Assign "r" (Const 2))))).

Theorem io_width_ref : forall d m s r, MatchX d m -> vmx_get_io_width_spec d = Some r ->
  exists s', exec ioWidthS s m s' m /\ s' "r" = r.
Proof.
  intros d m s r HM H; unfold vmx_get_io_width_spec in H.
  destruct (qual d) as [q|] eqn:Eq; [|discriminate].
  set (s1 := lset s "q" q); set (s2 := lset s1 "sz" (wand q 7)).
  assert (LQ : exec loadQualS s m s1 m) by (eapply qual_load; eauto).
  assert (LA : exec (Assign "sz" (Bin And (Var "q") (Const 7))) s1 m s2 m)
    by (apply exec_assign; simpl; unfold s1; rewrite lset_same; reflexivity).
  assert (Esz : s2 "sz" = wand q 7) by apply lset_same.
  destruct (wand q 7 =? 0) eqn:T0; [|destruct (wand q 7 =? 1) eqn:T1].
  - inversion H; subst r.
    exists (lset s2 "r" 0); split; [|apply lset_same].
    apply ESeq with (s1 := s1) (m1 := m); [exact LQ|].
    apply ESeq with (s1 := s2) (m1 := m); [exact LA|].
    apply EIteT; [simpl; rewrite Esz, T0; discriminate | apply exec_assign; reflexivity].
  - inversion H; subst r.
    exists (lset s2 "r" 1); split; [|apply lset_same].
    apply ESeq with (s1 := s1) (m1 := m); [exact LQ|].
    apply ESeq with (s1 := s2) (m1 := m); [exact LA|].
    apply EIteF; [simpl; rewrite Esz, T0; reflexivity|].
    apply EIteT; [simpl; rewrite Esz, T1; discriminate | apply exec_assign; reflexivity].
  - inversion H; subst r.
    exists (lset s2 "r" 2); split; [|apply lset_same].
    apply ESeq with (s1 := s1) (m1 := m); [exact LQ|].
    apply ESeq with (s1 := s2) (m1 := m); [exact LA|].
    apply EIteF; [simpl; rewrite Esz, T0; reflexivity|].
    apply EIteF; [simpl; rewrite Esz, T1; reflexivity | apply exec_assign; reflexivity].
Qed.

(** [r = ((q >> 3) & 1) == EXIT_QUAL_IO_IN ? 0 : 1;] *)
Definition ioWriteS : stmt :=
  Seq loadQualS
      (Ite (Bin Eq (Bin And (Bin Div (Var "q") (Const 8)) (Const 1)) (Const 1))
           (Assign "r" (Const 0)) (Assign "r" (Const 1))).

Theorem io_write_ref : forall d m s r, MatchX d m -> vmx_get_io_write_spec d = Some r ->
  exists s', exec ioWriteS s m s' m /\ s' "r" = r.
Proof.
  intros d m s r HM H; unfold vmx_get_io_write_spec in H.
  destruct (qual d) as [q|] eqn:Eq; [|discriminate].
  pose proof (qual_load d m s q HM Eq) as L.
  assert (Eqv : lset s "q" q "q" = q) by apply lset_same.
  destruct (wand (q / 8) 1 =? 1) eqn:T; inversion H; subst r.
  - exists (lset (lset s "q" q) "r" 0); split; [|apply lset_same].
    apply ESeq with (s1 := lset s "q" q) (m1 := m); [exact L|].
    apply EIteT; [simpl; rewrite Eqv, T; discriminate | apply exec_assign; reflexivity].
  - exists (lset (lset s "q" q) "r" 1); split; [|apply lset_same].
    apply ESeq with (s1 := lset s "q" q) (m1 := m); [exact L|].
    apply EIteF; [simpl; rewrite Eqv, T; reflexivity | apply exec_assign; reflexivity].
Qed.

(** [r = (q >> k) & 1;] and [r = (q >> 16) & 0xffff;] *)
Definition qualFieldS (e : expr) : stmt := Seq loadQualS (Assign "r" e).

Definition ioRepS : stmt := qualFieldS (Bin And (Bin Div (Var "q") (Const 32)) (Const 1)).
Definition ioStrS : stmt := qualFieldS (Bin And (Bin Div (Var "q") (Const 16)) (Const 1)).
Definition ioPortS : stmt := qualFieldS (Bin Div (Var "q") (Const 65536)).

Lemma qual_field_run : forall d m s q e, MatchX d m -> qual d = Some q ->
  exec (qualFieldS e) s m (lset (lset s "q" q) "r" (eval (lset s "q" q) e)) m.
Proof.
  intros d m s q e HM Hq; apply ESeq with (s1 := lset s "q" q) (m1 := m);
    [eapply qual_load; eauto | apply exec_assign; reflexivity].
Qed.

Theorem io_rep_ref : forall d m s r, MatchX d m -> vmx_get_exit_io_rep_spec d = Some r ->
  exists s', exec ioRepS s m s' m /\ s' "r" = r.
Proof.
  intros d m s r HM H; unfold vmx_get_exit_io_rep_spec in H.
  destruct (qual d) as [q|] eqn:Eq; [|discriminate]; inversion H; subst r.
  eexists; split; [apply (qual_field_run d m s q _ HM Eq) | rewrite lset_same; simpl; rewrite lset_same; reflexivity].
Qed.

Theorem io_str_ref : forall d m s r, MatchX d m -> vmx_get_exit_io_str_spec d = Some r ->
  exists s', exec ioStrS s m s' m /\ s' "r" = r.
Proof.
  intros d m s r HM H; unfold vmx_get_exit_io_str_spec in H.
  destruct (qual d) as [q|] eqn:Eq; [|discriminate]; inversion H; subst r.
  eexists; split; [apply (qual_field_run d m s q _ HM Eq) | rewrite lset_same; simpl; rewrite lset_same; reflexivity].
Qed.

Theorem io_port_ref : forall d m s r, MatchX d m -> vmx_get_exit_io_port_spec d = Some r ->
  exists s', exec ioPortS s m s' m /\ s' "r" = r.
Proof.
  intros d m s r HM H; unfold vmx_get_exit_io_port_spec in H.
  destruct (qual d) as [q|] eqn:Eq; [|discriminate]; inversion H; subst r.
  eexists; split; [apply (qual_field_run d m s q _ HM Eq) | rewrite lset_same; simpl; rewrite lset_same; reflexivity].
Qed.

(** *** [vmx_set_mmap]: [r = ept_add_mapping(gpa, hpa, mem_type); if (r == 0) r = ept_invalidate_mappings();] *)
Definition setMmapS : stmt :=
  Seq (EPT.addMappingS eb) (Ite (Bin Eq (Var "r") (Const 0)) EPT.invalidateS Skip).

Theorem set_mmap_ref : forall d d' m s gpa hpa memtype r, MatchX d m ->
  s "gpa" = gpa -> s "hpa" = hpa -> s "memtype" = memtype ->
  vmx_set_mmap_spec maxpage gpa hpa memtype d = Some (d', r) ->
  exists s' m', exec setMmapS s m s' m' /\ MatchX d' m' /\ s' "r" = r.
Proof.
  intros d d' m s gpa hpa memtype r HM Hg Hh Hm H; unfold vmx_set_mmap_spec in H.
  destruct (EPT.ept_add_mapping_spec maxpage gpa hpa memtype (toE d)) as [[e' res]|] eqn:Ea; [|discriminate].
  destruct HM as (H1 & H2 & H3).
  destruct (EPT.add_mapping_ref eb heb heb2 maxpage hmp (toE d) e' m s gpa hpa memtype res H3 Hg Hh Hm Ea)
    as [s1 [m1 [Ex [HE [Hr [_ Fr]]]]]].
  assert (HE' : forall e2, EPT.ept e' = e2 -> EPT.MatchE eb (toE (set_xept d e2)) m1).
  { intros e2 <-; intros g h Hgg Hl; apply HE; auto. }
  assert (M1 : MatchX (set_xept d (EPT.ept e')) m1).
  { split; [|split].
    - intros i v Hi Hv; rewrite Fr by (unfold VMX_Size', EPT.NPG in *; lia); apply H1; auto.
    - apply (matchV_frame _ m); auto; intros a Ha; apply Fr; unfold VMCS.NENC in *; lia.
    - apply HE'; reflexivity. }
  destruct ((0 <=? res) && (res <=? EPT.max_unsigned)); [|discriminate].
  destruct ((0 <=? memtype) && (memtype <? 4096)); [|discriminate].
  destruct (res =? 0) eqn:T.
  - destruct (EPT.ept_invalidate_mappings_spec e') as [z|] eqn:Ei; [|discriminate].
    inversion H; subst d' r.
    exists (lset s1 "r" z), m1; split; [|split; [exact M1 | apply lset_same]].
    apply ESeq with (s1 := s1) (m1 := m1); [exact Ex|].
    apply EIteT; [simpl; rewrite Hr, T; discriminate | apply EPT.invalidate_ref with (d := e'); exact Ei].
  - inversion H; subst d' r.
    exists s1, m1; split; [|split; [exact M1 | exact Hr]].
    apply ESeq with (s1 := s1) (m1 := m1); [exact Ex|].
    apply EIteF; [simpl; rewrite Hr, T; reflexivity | constructor].
Qed.

(** *** [vm_run]: [vmx_enter_pre] and [vmx_enter] *)

(** [vmcs_write32(VMCS_GUEST_RIP, vmx.g_rip);] *)
Definition enterPreS : stmt :=
  Seq (Load "t" (xE VMX_G_RIP')) (VMCS.vmwriteS vb (Const C_VMCS_GUEST_RIP) (Var "t")).

(** [vmx_enter]: save the host [ebp] and [edi], load the guest registers. *)
Definition enterS : stmt :=
  Seq (Store (xE VMX_HOST_EBP') (Var "EBP"))
  (Seq (Store (xE VMX_HOST_EDI') (Var "EDI"))
  (Seq (Load "EAX" (xE VMX_G_RAX'))
  (Seq (Load "EBX" (xE VMX_G_RBX'))
  (Seq (Load "EDX" (xE VMX_G_RDX'))
  (Seq (Load "ESI" (xE VMX_G_RSI'))
  (Seq (Load "EDI" (xE VMX_G_RDI'))
  (Seq (Load "EBP" (xE VMX_G_RBP'))
       (Load "RA" (xE VMX_G_RIP'))))))))).

Definition vmRunS : stmt := Seq enterPreS enterS.

(** The guest registers in the processor's registers, where they are known. *)
Definition GuestRegs (x : Z -> option Z) (s : locals) : Prop :=
  (forall v, x VMX_G_RAX' = Some v -> s "EAX" = v) /\ (forall v, x VMX_G_RBX' = Some v -> s "EBX" = v) /\
  (forall v, x VMX_G_RDX' = Some v -> s "EDX" = v) /\ (forall v, x VMX_G_RSI' = Some v -> s "ESI" = v) /\
  (forall v, x VMX_G_RDI' = Some v -> s "EDI" = v) /\ (forall v, x VMX_G_RBP' = Some v -> s "EBP" = v) /\
  (forall v, x VMX_G_RIP' = Some v -> s "RA" = v).

Lemma xstore : forall m s i e w, eval s e = w -> exec (Store (xE i) e) s m s (upd m (xb + i) w).
Proof. intros; apply exec_store; [reflexivity | auto]. Qed.

Lemma xload : forall m s x i, exec (Load x (xE i)) s m (lset s x (m (xb + i))) m.
Proof. intros; apply exec_load; reflexivity. Qed.

Ltac slot := unfold VMX_G_RAX', VMX_G_RBX', VMX_G_RDX', VMX_G_RSI', VMX_G_RDI', VMX_G_RBP', VMX_G_RIP',
  VMX_HOST_EBP', VMX_HOST_EDI', VMX_EXIT_REASON', VMX_EXIT_QUALIFICATION', VMX_LAUNCHED', VMX_Size',
  C_VMCS_GUEST_RIP, C_VMCS_EXIT_REASON, C_VMCS_EXIT_QUALIFICATION, VMCS.NENC, EPT.NPG in *.

(** **[vm_run] refines [vm_run_spec].** The host [ebp] and [edi] are in
    ["EBP"] and ["EDI"]; afterwards the guest registers are in the
    processor's registers. *)
Theorem vm_run_ref : forall d d' m s rebp redi, MatchX d m -> s "EBP" = rebp -> s "EDI" = redi ->
  vm_run_spec rebp redi d = Some d' ->
  exists s' m', exec vmRunS s m s' m' /\ MatchX d' m' /\ GuestRegs (vmx d) s'.
Proof.
  intros d d' m s rebp redi HM Hb Hdi H; unfold vm_run_spec in H.
  destruct (xikern d && xpg d && xihost d && xinit d); [|discriminate].
  destruct (vmx d VMX_G_RIP') as [v|] eqn:Ev; [|discriminate].
  inversion H; subst d'; clear H.
  destruct HM as (H1 & H2 & H3).
  set (st := lset s "t" v).
  set (m1 := upd m (vb + 2 + C_VMCS_GUEST_RIP) v).
  set (m2 := upd m1 (xb + VMX_HOST_EBP') rebp).
  set (m3 := upd m2 (xb + VMX_HOST_EDI') redi).
  assert (Hst : forall z, z <> "t" -> st z = s z) by (intros; unfold st; apply lset_other; auto).
  (* the cells of the guest registers are not written *)
  assert (G : forall i, 0 <= i < VMX_Size' -> i <> VMX_HOST_EBP' -> i <> VMX_HOST_EDI' -> m3 (xb + i) = m (xb + i)).
  { intros i Hi N1 N2; unfold m3, m2, m1; slot; rewrite !upd_other by lia; reflexivity. }
  set (s1 := lset st "EAX" (m3 (xb + VMX_G_RAX'))).
  set (s2 := lset s1 "EBX" (m3 (xb + VMX_G_RBX'))).
  set (s3 := lset s2 "EDX" (m3 (xb + VMX_G_RDX'))).
  set (s4 := lset s3 "ESI" (m3 (xb + VMX_G_RSI'))).
  set (s5 := lset s4 "EDI" (m3 (xb + VMX_G_RDI'))).
  set (s6 := lset s5 "EBP" (m3 (xb + VMX_G_RBP'))).
  set (s7 := lset s6 "RA" (m3 (xb + VMX_G_RIP'))).
  exists s7, m3; split; [|split].
  - apply ESeq with (s1 := st) (m1 := m1).
    + apply ESeq with (s1 := st) (m1 := m).
      * unfold st; eapply vmx_load; [exact (conj H1 (conj H2 H3)) | slot; lia | exact Ev].
      * apply vmcs_store; [slot; lia | simpl; unfold st; apply lset_same].
    + apply ESeq with (s1 := st) (m1 := m2); [apply xstore; simpl; rewrite Hst by discriminate; auto|].
      apply ESeq with (s1 := st) (m1 := m3); [apply xstore; simpl; rewrite Hst by discriminate; exact Hdi|].
      apply ESeq with (s1 := s1) (m1 := m3); [apply xload|].
      apply ESeq with (s1 := s2) (m1 := m3); [apply xload|].
      apply ESeq with (s1 := s3) (m1 := m3); [apply xload|].
      apply ESeq with (s1 := s4) (m1 := m3); [apply xload|].
      apply ESeq with (s1 := s5) (m1 := m3); [apply xload|].
      apply ESeq with (s1 := s6) (m1 := m3); [apply xload | apply xload].
  - assert (M1 : MatchX (set_xvmcs d (VMCS.VMCSValid (VMCS.revid (xvmcs d)) (VMCS.abrtid (xvmcs d))
                   (zset (VMCS.data (xvmcs d)) C_VMCS_GUEST_RIP (Some v)))) m1)
      by (apply match_vmcs_write; [exact (conj H1 (conj H2 H3)) | slot; lia]).
    pose proof (match_vmx_write _ _ VMX_HOST_EBP' rebp M1 ltac:(slot; lia)) as M2.
    pose proof (match_vmx_write _ _ VMX_HOST_EDI' redi M2 ltac:(slot; lia)) as M3.
    apply match_ihost; exact M3.
  - assert (R : forall i v', 0 <= i < VMX_Size' -> i <> VMX_HOST_EBP' -> i <> VMX_HOST_EDI' ->
                  vmx d i = Some v' -> m3 (xb + i) = v')
      by (intros i v' Hi N1 N2 Hv'; rewrite G by auto; apply H1; auto).
    unfold s7, s6, s5, s4, s3, s2, s1.
    repeat split; intros v' Hv'; unfold lset; simpl; apply R; auto; slot; lia.
Qed.

(** *** [vmx_return_from_guest]: [vmx_exit] and [vmx_exit_post] *)

(** [vmx_exit]: save the guest registers, load the host [edi] and [ebp]. *)
Definition exitS : stmt :=
  Seq (Store (xE VMX_G_RDI') (Var "EDI"))
  (Seq (Store (xE VMX_G_RAX') (Var "EAX"))
  (Seq (Store (xE VMX_G_RBX') (Var "EBX"))
  (Seq (Store (xE VMX_G_RDX') (Var "EDX"))
  (Seq (Store (xE VMX_G_RSI') (Var "ESI"))
  (Seq (Store (xE VMX_G_RBP') (Var "EBP"))
  (Seq (Load "EDI" (xE VMX_HOST_EDI'))
       (Load "EBP" (xE VMX_HOST_EBP')))))))).

(** [vmx.g_rip = vmcs_read32(VMCS_GUEST_RIP); vmx.exit_reason = vmcs_read32(VMCS_EXIT_REASON);
     vmx.exit_qualification = vmcs_read32(VMCS_EXIT_QUALIFICATION); vmx.launched = 1;] *)
Definition exitPostS : stmt :=
  Seq (VMCS.vmreadS vb "t" (Const C_VMCS_GUEST_RIP))
  (Seq (Store (xE VMX_G_RIP') (Var "t"))
  (Seq (VMCS.vmreadS vb "t" (Const C_VMCS_EXIT_REASON))
  (Seq (Store (xE VMX_EXIT_REASON') (Var "t"))
  (Seq (VMCS.vmreadS vb "t" (Const C_VMCS_EXIT_QUALIFICATION))
  (Seq (Store (xE VMX_EXIT_QUALIFICATION') (Var "t"))
       (Store (xE VMX_LAUNCHED') (Const 1))))))).

Definition returnS : stmt := Seq exitS exitPostS.

(** **[vmx_return_from_guest] refines [vmx_return_from_guest_spec].** The
    guest registers at the exit are in the processor's registers; afterwards
    the host [edi] and [ebp] are back. *)
Theorem return_ref : forall d d' m s redi reax rebx redx resi rebp, MatchX d m ->
  s "EDI" = redi -> s "EAX" = reax -> s "EBX" = rebx -> s "EDX" = redx -> s "ESI" = resi -> s "EBP" = rebp ->
  vmx_return_from_guest_spec redi reax rebx redx resi rebp d = Some d' ->
  exists s' m', exec returnS s m s' m' /\ MatchX d' m' /\
    (forall v, vmx d VMX_HOST_EDI' = Some v -> s' "EDI" = v) /\
    (forall v, vmx d VMX_HOST_EBP' = Some v -> s' "EBP" = v).
Proof.
  intros d d' m s redi reax rebx redx resi rebp HM E1 E2 E3 E4 E5 E6 H.
  unfold vmx_return_from_guest_spec in H.
  destruct (xikern d && xpg d && negb (xihost d) && xinit d); [|discriminate].
  destruct (VMCS.data (xvmcs d) C_VMCS_GUEST_RIP) as [v1|] eqn:V1; [|discriminate].
  destruct (VMCS.data (xvmcs d) C_VMCS_EXIT_REASON) as [v2|] eqn:V2; [|discriminate].
  destruct (VMCS.data (xvmcs d) C_VMCS_EXIT_QUALIFICATION) as [v3|] eqn:V3; [|discriminate].
  inversion H; subst d'; clear H.
  (* the stores, as matches *)
  pose proof (match_vmx_write _ _ VMX_G_RDI' redi HM ltac:(slot; lia)) as M1.
  pose proof (match_vmx_write _ _ VMX_G_RAX' reax M1 ltac:(slot; lia)) as M2.
  pose proof (match_vmx_write _ _ VMX_G_RBX' rebx M2 ltac:(slot; lia)) as M3.
  pose proof (match_vmx_write _ _ VMX_G_RDX' redx M3 ltac:(slot; lia)) as M4.
  pose proof (match_vmx_write _ _ VMX_G_RSI' resi M4 ltac:(slot; lia)) as M5.
  pose proof (match_vmx_write _ _ VMX_G_RBP' rebp M5 ltac:(slot; lia)) as M6.
  pose proof (match_vmx_write _ _ VMX_G_RIP' v1 M6 ltac:(slot; lia)) as M7.
  pose proof (match_vmx_write _ _ VMX_EXIT_REASON' v2 M7 ltac:(slot; lia)) as M8.
  pose proof (match_vmx_write _ _ VMX_EXIT_QUALIFICATION' v3 M8 ltac:(slot; lia)) as M9.
  pose proof (match_vmx_write _ _ VMX_LAUNCHED' 1 M9 ltac:(slot; lia)) as M10.
  set (m1 := upd m (xb + VMX_G_RDI') redi) in *.
  set (m2 := upd m1 (xb + VMX_G_RAX') reax) in *.
  set (m3 := upd m2 (xb + VMX_G_RBX') rebx) in *.
  set (m4 := upd m3 (xb + VMX_G_RDX') redx) in *.
  set (m5 := upd m4 (xb + VMX_G_RSI') resi) in *.
  set (m6 := upd m5 (xb + VMX_G_RBP') rebp) in *.
  set (m7 := upd m6 (xb + VMX_G_RIP') v1) in *.
  set (m8 := upd m7 (xb + VMX_EXIT_REASON') v2) in *.
  set (m9 := upd m8 (xb + VMX_EXIT_QUALIFICATION') v3) in *.
  set (m10 := upd m9 (xb + VMX_LAUNCHED') 1) in *.
  destruct HM as (H1 & H2 & H3).
  (* the VMCS cells read by exit_post are not written by the stores *)
  assert (VC : forall k, 0 <= k < VMCS.NENC -> m6 (vb + 2 + k) = m (vb + 2 + k)).
  { intros k Hk; unfold m6, m5, m4, m3, m2, m1; slot; rewrite !upd_other by lia; reflexivity. }
  assert (R1 : m6 (vb + 2 + C_VMCS_GUEST_RIP) = v1).
  { rewrite VC by (slot; lia); destruct H2 as (_ & _ & H2c); apply H2c; auto; slot; lia. }
  assert (R2 : m6 (vb + 2 + C_VMCS_EXIT_REASON) = v2).
  { rewrite VC by (slot; lia); destruct H2 as (_ & _ & H2c); apply H2c; auto; slot; lia. }
  assert (R3 : m6 (vb + 2 + C_VMCS_EXIT_QUALIFICATION) = v3).
  { rewrite VC by (slot; lia); destruct H2 as (_ & _ & H2c); apply H2c; auto; slot; lia. }
  set (sa := lset s "EDI" (m6 (xb + VMX_HOST_EDI'))).
  set (sb := lset sa "EBP" (m6 (xb + VMX_HOST_EBP'))).
  set (sc := lset sb "t" v1).
  set (sd := lset sc "t" v2).
  set (se := lset sd "t" v3).
  exists se, m10; split; [|split; [|split]].
  - apply ESeq with (s1 := sb) (m1 := m6).
    + apply ESeq with (s1 := s) (m1 := m1); [apply xstore; simpl; auto|].
      apply ESeq with (s1 := s) (m1 := m2); [apply xstore; simpl; auto|].
      apply ESeq with (s1 := s) (m1 := m3); [apply xstore; simpl; auto|].
      apply ESeq with (s1 := s) (m1 := m4); [apply xstore; simpl; auto|].
      apply ESeq with (s1 := s) (m1 := m5); [apply xstore; simpl; auto|].
      apply ESeq with (s1 := s) (m1 := m6); [apply xstore; simpl; auto|].
      apply ESeq with (s1 := sa) (m1 := m6); [apply xload | apply xload].
    + apply ESeq with (s1 := sc) (m1 := m6).
      { unfold sc; rewrite <- R1; apply exec_load; simpl; apply norm_small; slot; lia. }
      apply ESeq with (s1 := sc) (m1 := m7); [apply xstore; simpl; unfold sc; apply lset_same|].
      apply ESeq with (s1 := sd) (m1 := m7).
      { unfold sd; replace v2 with (m7 (vb + 2 + C_VMCS_EXIT_REASON))
          by (unfold m7; rewrite upd_other by (slot; lia); exact R2).
        apply exec_load; simpl; apply norm_small; slot; lia. }
      apply ESeq with (s1 := sd) (m1 := m8); [apply xstore; simpl; unfold sd; apply lset_same|].
      apply ESeq with (s1 := se) (m1 := m8).
      { unfold se; replace v3 with (m8 (vb + 2 + C_VMCS_EXIT_QUALIFICATION))
          by (unfold m8, m7; rewrite !upd_other by (slot; lia); exact R3).
        apply exec_load; simpl; apply norm_small; slot; lia. }
      apply ESeq with (s1 := se) (m1 := m9); [apply xstore; simpl; unfold se; apply lset_same|].
      apply xstore; reflexivity.
  - apply match_ihost; exact M10.
  - intros v Hv; unfold se, sd, sc, sb, sa; unfold lset; simpl.
    unfold m6, m5, m4, m3, m2, m1; slot; rewrite !upd_other by lia; apply H1; auto; lia.
  - intros v Hv; unfold se, sd, sc, sb; unfold lset; simpl.
    unfold m6, m5, m4, m3, m2, m1; slot; rewrite !upd_other by lia; apply H1; auto; lia.
Qed.

End Code.
