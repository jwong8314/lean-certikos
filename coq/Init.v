(** * [vmx_init]: the virtual machine before its first entry

    Ported from [objects/ObjVMX.v] ([vmx_init_spec], with the C quoted there)
    and [objects/ObjVMCS.v] ([vmcs_set_defaults_spec], with the C quoted
    there), and [objects/ObjEPT.v] ([ept_init_spec]).

    In mCertiKOS, [vmx_init] is the whole boot (memory, containers, page
    tables, shared memory, threads, channels) and then three things for the
    virtual machine: [vmcs_set_defaults] (the VMCS's controls, host state and
    guest state), the VMCS revision identifier, and the [vmx] structure's
    first values; the EPT is set up by [ept_init]. The boot is verified in the
    process layers; this file is the virtual machine's part, [vmx_init0].

    The definitions of [real_vmcs], [real_vmx] and [real_ept] are not in the
    public sources. Here they are what the C does:
    - [vmcs_set_defaults] writes the fields listed in [defaults], in the C's
      order. A 64-bit field is two words (low at [enc], high at [enc + 1]),
      as [vmcs_write64] does. The values that come from the processor
      ([rcr0], [rcr3], [rcr4], [rdmsr]) are 0, mCertiKOS's model of them
      ([rcr0_spec] and the like). The values that come from the boot (the
      controls in [vmx_info], the addresses of [tss], [gdt], [idt], the
      bitmaps, the EPT, the host entry point, the VPID) are the arguments:
      the locals [params].
    - The revision identifier is [rdmsr(MSR_VMX_BASIC) & 0xffffffff], which
      is 0 in the model.
    - The [vmx] structure is cleared ([memset] in [vmx_hw_init]) and then
      [g_rip = 0xfff0], [vpid = 1], [g_cr2 = 0], [g_dr0 ... g_dr3 = 0],
      [g_dr6 = 0xffff0ff0].
    - The EPT gives every guest page the entry 0 ([EPT.ept_init0_spec]).

    What differs: [vmx_init] here asks that the virtual machine is not yet
    set up ([xinit = false]) and that the kernel is in its normal mode
    ([flags]); it leaves the process layers' boot to them. *)

From Stdlib Require Import ZArith String Lia Bool List.
From VCoq Require Import Lang.
From VCoq Require EPT VMCS VMX.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope bool_scope.
Open Scope Z_scope.

(** ** The values *)

(** The arguments of [vmcs_set_defaults] and the addresses it uses. *)
Definition params : list string :=
  ["pinbased"; "procbased"; "procbased2"; "exit_ctls"; "entry_ctls"; "host_rip"; "tss"; "gdt"; "idt";
   "pml4"; "vpid"; "msr_bitmap"; "cr0_ones"; "cr0_zeros"; "cr4_ones"; "cr4_zeros"; "io_bitmap_a";
   "io_bitmap_b"].

Definition CPU_GDT_KCODE := 8.
Definition CPU_GDT_KDATA := 16.
Definition CPU_GDT_TSS := 40.

(** [vmcs_set_defaults], field by field. *)
Definition defaults : list (Z * expr) :=
  [ (16384, Var "pinbased"); (16386, Var "procbased"); (16414, Var "procbased2");
    (16396, Var "exit_ctls"); (16402, Var "entry_ctls");
    (27670, Var "host_rip");                                            (* host rip *)
    (27648, Const 0); (27650, Const 0); (27652, Const 0);               (* host cr0, cr3, cr4: rcr0() ... *)
    (3072, Const CPU_GDT_KDATA); (3074, Const CPU_GDT_KCODE); (3076, Const CPU_GDT_KDATA);
    (3078, Const CPU_GDT_KDATA); (3080, Const CPU_GDT_KDATA); (3082, Const CPU_GDT_KDATA);
    (3084, Const CPU_GDT_TSS);                                          (* host selectors *)
    (27654, Const 0); (27656, Const 0);                                 (* host fs, gs base *)
    (27658, Var "tss"); (27660, Var "gdt"); (27662, Var "idt");
    (19456, Const 0); (27664, Const 0); (27666, Const 0);               (* host sysenter: rdmsr() *)
    (11268, Const 0); (11269, Const 0); (11264, Const 0); (11265, Const 0);
    (11266, Const 0); (11267, Const 0);                                 (* host perf, pat, efer: rdmsr() *)
    (26624, Const 1610612784); (26626, Const 0); (26628, Const 8192);  (* guest cr0, cr3, cr4 *)
    (26650, Const 1024);                                                (* guest dr7 *)
    (10244, Const 459782); (10245, Const 459782);                       (* guest pat *)
    (18474, Const 0); (26660, Const 0); (26662, Const 0);               (* guest sysenter *)
    (10242, Const 0); (10243, Const 0);                                 (* guest debugctl *)
    (8218, Bin Or (Var "pml4") (Const 30)); (8219, Const 0);            (* EPTP *)
    (0, Var "vpid");
    (8196, Var "msr_bitmap"); (8197, Const 0);
    (10240, Const 4294967295); (10241, Const 4294967295);               (* link pointer *)
    (24576, Bin Or (Var "cr0_ones") (Var "cr0_zeros")); (24580, Var "cr0_ones");
    (24578, Bin Or (Var "cr4_ones") (Var "cr4_zeros")); (24582, Var "cr4_ones");
    (8192, Var "io_bitmap_a"); (8193, Const 0); (8194, Var "io_bitmap_b"); (8195, Const 0);
    (18470, Const 0); (18468, Const 0); (26658, Const 0); (16406, Const 0) ].

(** The [vmx] structure after [memset] and [vmx_init]. *)
Definition vmx_first (i : Z) : Z :=
  if i =? VMX.VMX_G_RIP' then 65520
  else if i =? 26 then 1
  else if i =? 21 then 4294905840
  else 0.

Definition vmx_list : list (Z * Z) := map (fun i => (i, vmx_first i)) (map Z.of_nat (seq 0 36)).

Fixpoint writes {A} (l : list (Z * A)) (f : Z -> option A) : Z -> option A :=
  match l with
  | [] => f
  | (k, v) :: t => writes t (VMX.zset f k (Some v))
  end.

(** ** Specification *)

Definition vmx_init0_spec (info : locals) (d : VMX.XSt) : option VMX.XSt :=
  if VMX.flags d && negb (VMX.xinit d) then
    match EPT.ept_init0_spec (VMX.toE d) with
    | Some e =>
      Some (VMX.mkX (VMX.xikern d) (VMX.xpg d) (VMX.xihost d) true (writes vmx_list (VMX.vmx d))
        (VMCS.VMCSValid (Some 0) (VMCS.abrtid (VMX.xvmcs d))
          (writes (map (fun p => (fst p, eval info (snd p))) defaults) (VMCS.data (VMX.xvmcs d))))
        (EPT.ept e))
    | None => None
    end
  else None.

(** ** The code *)

Fixpoint vwritesS (vb : Z) (l : list (Z * expr)) : stmt :=
  match l with
  | [] => Skip
  | (k, e) :: t => Seq (VMCS.vmwriteS vb (Const k) e) (vwritesS vb t)
  end.

Fixpoint xwritesS (xb : Z) (l : list (Z * Z)) : stmt :=
  match l with
  | [] => Skip
  | (k, v) :: t => Seq (Store (Const (xb + k)) (Const v)) (xwritesS xb t)
  end.

(** [vmcs_set_defaults(...); vmcs->identifier = rdmsr(MSR_VMX_BASIC) & 0xffffffff;
     memset(&vmx, 0, sizeof vmx); vmx.g_rip = 0xfff0; ...; ept_init();] *)
Definition vmxInitS (xb vb eb : Z) : stmt :=
  Seq (vwritesS vb defaults) (Seq (Store (Const vb) (Const 0)) (Seq (xwritesS xb vmx_list) (EPT.eptInitS eb))).

(** The locals an expression reads. *)
Fixpoint vars (e : expr) : list string :=
  match e with
  | Const _ => []
  | Var x => [x]
  | Bin _ a b => vars a ++ vars b
  end.

Lemma eval_agree : forall s t e, (forall x, In x (vars e) -> s x = t x) -> eval s e = eval t e.
Proof.
  intros s t e; induction e as [v|x|o a IHa b IHb]; intros H; simpl; auto.
  - apply H; left; reflexivity.
  - rewrite IHa, IHb; auto; intros x Hx; apply H; apply in_or_app; auto.
Qed.

Lemma defaults_vars : forall p, In p defaults -> forall x, In x (vars (snd p)) -> In x params.
Proof.
  intros p Hp x Hx; unfold defaults in Hp.
  repeat (destruct Hp as [<-|Hp]; [simpl in Hx; repeat (destruct Hx as [<-|Hx]; [simpl; tauto|]);
    try contradiction; try (simpl in Hx; contradiction)|]).
  contradiction.
Qed.

Lemma defaults_enc : forall p, In p defaults -> 0 <= fst p < VMCS.NENC.
Proof.
  intros p Hp; unfold defaults in Hp.
  repeat (destruct Hp as [<-|Hp]; [simpl; unfold VMCS.NENC; lia|]); contradiction.
Qed.

Lemma vmx_list_range : forall p, In p vmx_list -> 0 <= fst p < VMX.VMX_Size'.
Proof.
  intros p Hp; unfold vmx_list in Hp; apply in_map_iff in Hp; destruct Hp as [i [<- Hi]].
  apply in_map_iff in Hi; destruct Hi as [n [<- Hn]]; apply in_seq in Hn.
  simpl; unfold VMX.VMX_Size'; lia.
Qed.

Section Code.
Variables xb vb eb : Z.
Hypothesis hxb : 0 <= xb.
Hypothesis hxv : xb + VMX.VMX_Size' <= vb.
Hypothesis hve : vb + 65540 <= eb.
Hypothesis heb2 : eb + EPT.NPG <= W.

Notation MatchX := (VMX.MatchX xb vb eb).

Lemma hvb0 : 0 <= vb.
Proof. unfold VMX.VMX_Size' in *; lia. Qed.
Lemma hvb2' : vb + 65540 <= W.
Proof. unfold EPT.NPG in *; lia. Qed.
Lemma heb0 : 0 <= eb.
Proof. unfold VMX.VMX_Size' in *; lia. Qed.

(** The defaults, one [vmwrite] after another. *)
Lemma vwrites_run : forall (l : list (Z * expr)) d m s info,
  MatchX d m -> (forall p, In p l -> 0 <= fst p < VMCS.NENC /\ eval s (snd p) = eval info (snd p)) ->
  exists m', exec (vwritesS vb l) s m s m' /\
    MatchX (VMX.set_xvmcs d (VMCS.VMCSValid (VMCS.revid (VMX.xvmcs d)) (VMCS.abrtid (VMX.xvmcs d))
      (writes (map (fun p => (fst p, eval info (snd p))) l) (VMCS.data (VMX.xvmcs d))))) m'.
Proof.
  induction l as [|[k e] t IH]; intros d m s info HM Hl; simpl.
  - exists m; split; [constructor|].
    destruct d as [a b c i v [r ab dt] ep]; exact HM.
  - destruct (Hl (k, e) (or_introl eq_refl)) as [Hk He]; simpl in Hk, He.
    pose proof (VMX.match_vmcs_write xb vb eb hxv hve d m k (eval info e) HM Hk) as M1.
    destruct (IH _ _ s info M1 (fun p hp => Hl p (or_intror hp))) as [m' [Ex M']].
    exists m'; split.
    + apply ESeq with (s1 := s) (m1 := upd m (vb + 2 + k) (eval info e)); [|exact Ex].
      apply (VMCS.vmwrite_run vb hvb0 hvb2' m s (Const k) e k (eval info e)); auto.
    + exact M'.
Qed.

(** The [vmx] structure, one store after another. *)
Lemma xwrites_run : forall (l : list (Z * Z)) d m s,
  MatchX d m -> (forall p, In p l -> 0 <= fst p < VMX.VMX_Size') ->
  exists m', exec (xwritesS xb l) s m s m' /\ MatchX (VMX.set_vmx d (writes l (VMX.vmx d))) m'.
Proof.
  induction l as [|[k v] t IH]; intros d m s HM Hl; simpl.
  - exists m; split; [constructor|]; destruct d; exact HM.
  - pose proof (Hl (k, v) (or_introl eq_refl)) as Hk; simpl in Hk.
    pose proof (VMX.match_vmx_write xb vb eb hxv hve d m k v HM Hk) as M1.
    destruct (IH _ _ s M1 (fun p hp => Hl p (or_intror hp))) as [m' [Ex M']].
    exists m'; split.
    + apply ESeq with (s1 := s) (m1 := upd m (xb + k) v); [apply exec_store; reflexivity|exact Ex].
    + exact M'.
Qed.

(** **[vmx_init] refines [vmx_init0_spec].** The arguments are in the locals. *)
Theorem vmx_init_ref : forall info d d' m s, MatchX d m -> (forall x, In x params -> s x = info x) ->
  vmx_init0_spec info d = Some d' -> exists s' m', exec (vmxInitS xb vb eb) s m s' m' /\ MatchX d' m'.
Proof.
  intros info d d' m s HM Hs H; unfold vmx_init0_spec in H.
  destruct (VMX.flags d && negb (VMX.xinit d)); [|discriminate].
  destruct (EPT.ept_init0_spec (VMX.toE d)) as [e|] eqn:Ee; [|discriminate].
  inversion H; subst d'; clear H.
  (* the VMCS defaults *)
  destruct (vwrites_run defaults d m s info HM (fun p hp => conj (defaults_enc p hp)
    (eval_agree s info (snd p) (fun x hx => Hs x (defaults_vars p hp x hx))))) as [m1 [X1 M1]].
  set (d1 := VMX.set_xvmcs d (VMCS.VMCSValid (VMCS.revid (VMX.xvmcs d)) (VMCS.abrtid (VMX.xvmcs d))
      (writes (map (fun p => (fst p, eval info (snd p))) defaults) (VMCS.data (VMX.xvmcs d))))) in M1.
  (* the revision identifier *)
  set (d2 := VMX.set_xvmcs d1 (VMCS.VMCSValid (Some 0) (VMCS.abrtid (VMX.xvmcs d1)) (VMCS.data (VMX.xvmcs d1)))).
  assert (M2 : MatchX d2 (upd m1 vb 0)).
  { destruct M1 as (H1 & (V1 & V2 & V3) & H3); split; [|split; [split; [|split]|]].
    - intros i v Hi Hv; rewrite upd_other by (unfold VMX.VMX_Size' in *; lia); apply H1; auto.
    - intros r Hr; simpl in Hr; inversion Hr; apply upd_same.
    - intros a Ha; simpl in Ha; rewrite upd_other by lia; apply V2; auto.
    - intros k x Hk Hx; simpl in Hx; rewrite upd_other by lia; apply V3; auto.
    - intros g h Hg Hl; rewrite upd_other by (unfold EPT.NPG in *; lia); apply H3; auto. }
  (* the vmx structure *)
  destruct (xwrites_run vmx_list d2 (upd m1 vb 0) s M2 vmx_list_range) as [m3 [X3 M3]].
  (* the EPT *)
  destruct (EPT.ept_init_ref eb heb0 heb2 (VMX.toE (VMX.set_vmx d2 (writes vmx_list (VMX.vmx d2))))
    (EPT.set_ept (VMX.toE d) (EPT.ept e)) m3 s) as [s4 [m4 [X4 [HE Fr]]]].
  { unfold EPT.ept_init0_spec in *; simpl.
    destruct (EPT.flags (VMX.toE d)) eqn:F; [|discriminate].
    inversion Ee; subst e; simpl; unfold EPT.flags in *; simpl in *; rewrite F; reflexivity. }
  exists s4, m4; split.
  - unfold vmxInitS.
    apply ESeq with (s1 := s) (m1 := m1); [exact X1|].
    apply ESeq with (s1 := s) (m1 := upd m1 vb 0); [apply exec_store; reflexivity|].
    apply ESeq with (s1 := s) (m1 := m3); [exact X3 | exact X4].
  - destruct M3 as (H1 & H2 & H3); split; [|split].
    + intros i v Hi Hv; rewrite Fr by (unfold VMX.VMX_Size' in *; lia); apply H1; auto.
    + apply (VMX.matchV_frame vb _ m3); [exact H2|].
      intros a Ha; apply Fr; unfold VMCS.NENC in *; lia.
    + exact HE.
Qed.

End Code.
