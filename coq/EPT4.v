(** * The EPT's upper tables in memory

    [EPT.v] keeps the four-level tree of mCertiKOS's EPT ([AuxStateDataType.v])
    in the abstract state and the leaf entries in memory (a flat array, one
    word per guest page). This file adds the three upper tables of
    [struct eptStruct] ([kernel/sys/preinit/lib/ept.h]):
    [pml4[512]], [pdpt[512]] and [pdt[4][512]], in the region at [ub]:
    - [pml4] at [ub], [pdpt] at [ub + 512], [pdt[j]] at [ub + 1024 + 512 j];
    - the leaf table [ptab[j][k]] is the slice of the flat array at
      [eb + 512 (512 j + k)].
    An entry that points to a table holds that table's address with the
    permission bits ([ent]); an entry with no table holds 0.

    - [MatchUp]: the upper tables hold what the abstract tree says, for the
      part a 4 GB guest uses ([pml4] index 0, [pdpt] indices 0 to 3).
    - [setEPML4_spec], [setEPDPTE_spec], [setEPDTE_spec] ([ObjEPT.v]): each
      adds a level, with nothing below it; the code writes the entry and
      clears the new table (a [pdt] has to be cleared; a leaf table does not,
      since entries under no table are not looked at).
    - [ept_init4]: the tree [real_ept] builds, written out: every upper entry
      points to its table, every leaf is 0.
    - [up_store]: a write of a leaf (what [ept_set_page_entry],
      [ept_add_mapping] and the others do) keeps [MatchUp].

    What differs: a table's address is a word index here; [ent a] is
    [4 a + 7] (the byte address with read, write and execute), which is
    [4 a | 7] for an aligned table. [setEPML4] clears the four [pdpt] entries
    a 4 GB guest uses, not all 512. *)

From Stdlib Require Import ZArith String Lia Bool.
From VCoq Require Import Lang.
From VCoq Require EPT.
Local Open Scope string_scope.
Local Open Scope bool_scope.
Open Scope Z_scope.

Import EPT.

Definition ent (a : Z) : Z := norm (4 * a + 7).

Lemma ent_nz : forall a, ent a <> 0.
Proof.
  intros a H; unfold ent, norm, W in H.
  assert (E : (4 * a + 7) mod 4294967296 mod 4 = 3).
  { rewrite <- Znumtheory.Zmod_div_mod; [| lia | lia | exists 1073741824; lia].
    replace (4 * a + 7) with (3 + (a + 1) * 4) by lia; rewrite Z.mod_add by lia; reflexivity. }
  rewrite H in E; discriminate.
Qed.

(** ** The shape of the tree *)

Definition v4 (e : EPT) : bool := match e 0 with EPML4EValid _ => true | _ => false end.
Definition vP (e : EPT) (j : Z) : bool :=
  match e 0 with EPML4EValid a => match a j with EPDPTEValid _ => true | _ => false end | _ => false end.
Definition vD (e : EPT) (j k : Z) : bool :=
  match e 0 with
  | EPML4EValid a => match a j with
    | EPDPTEValid b => match b k with EPDTEValid _ => true | _ => false end
    | _ => false end
  | _ => false
  end.

Lemma shape_store : forall e g v e', ept_store e g v = Some e' ->
  v4 e' = v4 e /\ (forall j, vP e' j = vP e j) /\ (forall j k, vD e' j k = vD e j k).
Proof.
  intros e g v e' H; unfold ept_store in H.
  destruct (e (PML4' g)) as [a|] eqn:Ea; [|discriminate].
  destruct (a (PDPT' g)) as [b|] eqn:Eb; [|discriminate].
  destruct (b (PDIR' g)) as [c|] eqn:Ec; [|discriminate].
  inversion H; subst e'; clear H.
  unfold v4, vP, vD, zset.
  destruct (Z.eq_dec 0 (PML4' g)) as [E0|E0].
  - rewrite <- E0 in Ea; rewrite Ea; split; [reflexivity|split].
    + intros j; destruct (Z.eq_dec j (PDPT' g)) as [ -> | _]; [rewrite Eb|]; reflexivity.
    + intros j k; destruct (Z.eq_dec j (PDPT' g)) as [ -> | _]; [rewrite Eb|reflexivity].
      destruct (Z.eq_dec k (PDIR' g)) as [ -> | _]; [rewrite Ec|]; reflexivity.
  - repeat split.
Qed.

(** ** Specifications ([ObjEPT.v]) *)

Definition empty3 : EPDPT := fun _ => EPDPTEUndef.
Definition empty2 : EPDT := fun _ => EPDTEUndef.
Definition empty1 : EPTAB := fun _ => EPTEUndef.

(** [EPT_PML4_INDEX(0xffffffff) = 0], [EPT_PDPT_INDEX(0xffffffff) = 3],
    [EPT_PDIR_INDEX(0xffffffff) = 511]: the bounds of the specifications. *)
Definition setEPML4_spec (pml4 : Z) (d : VData) : option VData :=
  if flags d && (pml4 =? 0) then Some (set_ept d (zset (ept d) 0 (EPML4EValid empty3))) else None.

Definition setEPDPTE_spec (pml4 pdpt : Z) (d : VData) : option VData :=
  if flags d && (pml4 =? 0) && (0 <=? pdpt) && (pdpt <? 4) then
    match ept d 0 with
    | EPML4EValid a => Some (set_ept d (zset (ept d) 0 (EPML4EValid (zset a pdpt (EPDPTEValid empty2)))))
    | EPML4EUndef => None
    end
  else None.

Definition setEPDTE_spec (pml4 pdpt pdir : Z) (d : VData) : option VData :=
  if flags d && (pml4 =? 0) && (0 <=? pdpt) && (pdpt <? 4) && (0 <=? pdir) && (pdir <? 512) then
    match ept d 0 with
    | EPML4EValid a =>
      match a pdpt with
      | EPDPTEValid b =>
        Some (set_ept d (zset (ept d) 0 (EPML4EValid (zset a pdpt (EPDPTEValid (zset b pdir (EPDTEValid empty1)))))))
      | EPDPTEUndef => None
      end
    | EPML4EUndef => None
    end
  else None.

(** ** The tables in the region *)

Section Code.
Variables ub eb : Z.
Hypothesis hub : 0 <= ub.
Hypothesis hue : ub + 3072 <= eb.
Hypothesis heb2 : eb + NPG <= W.

Definition P2 (j : Z) := ub + 1024 + 512 * j.
Definition leafT (j k : Z) := eb + 512 * (512 * j + k).

Definition MatchUp (e : EPT) (m : mem) : Prop :=
  m ub = (if v4 e then ent (ub + 512) else 0) /\
  (v4 e = true -> forall j, 0 <= j < 4 -> m (ub + 512 + j) = (if vP e j then ent (P2 j) else 0)) /\
  (forall j k, 0 <= j < 4 -> 0 <= k < 512 -> vP e j = true ->
     m (P2 j + k) = (if vD e j k then ent (leafT j k) else 0)).

(** The upper tables are below the leaves. *)
Definition InUp (a : Z) : Prop := ub <= a < ub + 3072.

Lemma matchUp_frame : forall e m m', MatchUp e m -> (forall a, InUp a -> m' a = m a) -> MatchUp e m'.
Proof.
  intros e m m' (H1 & H2 & H3) F; unfold InUp in *; split; [|split].
  - rewrite (F ub) by lia; exact H1.
  - intros h j Hj; rewrite (F (ub + 512 + j)) by lia; apply H2; auto.
  - intros j k Hj Hk hv; rewrite (F (P2 j + k)) by (unfold P2; lia); apply H3; auto.
Qed.

(** **A write of a leaf keeps the upper tables.** *)
Theorem up_store : forall e g v e' m m', ept_store e g v = Some e' -> MatchUp e m ->
  (forall a, InUp a -> m' a = m a) -> MatchUp e' m'.
Proof.
  intros e g v e' m m' Hs HM F.
  destruct (shape_store e g v e' Hs) as (S4 & SP & SD).
  destruct (matchUp_frame e m m' HM F) as (H1 & H2 & H3).
  split; [|split].
  - rewrite S4; exact H1.
  - intros h j Hj; rewrite SP; apply H2; [rewrite <- S4|]; auto.
  - intros j k Hj Hk hv; rewrite SD; apply H3; auto; rewrite <- SP; auto.
Qed.

(** The leaves under a new, empty level are not there. *)
Lemma leaf_empty3 : forall e g, 0 <= g < NPG -> ept_leaf (zset e 0 (EPML4EValid empty3)) g = None.
Proof.
  intros e g Hg; destruct (idx_split g Hg) as (P0 & _).
  unfold ept_leaf, zset; rewrite P0; destruct (Z.eq_dec 0 0); [reflexivity|congruence].
Qed.

(** *** [setEPML4]: [pml4[0] = &pdpt | 7; pdpt[0..3] = 0;] *)
Definition setEPML4S : stmt :=
  Seq (Store (Const ub) (Const (ent (ub + 512))))
  (Seq (Store (Const (ub + 512)) (Const 0)) (Seq (Store (Const (ub + 513)) (Const 0))
  (Seq (Store (Const (ub + 514)) (Const 0)) (Store (Const (ub + 515)) (Const 0))))).

Theorem setEPML4_ref : forall d d' m s pml4, EPT.MatchE eb d m -> MatchUp (ept d) m ->
  setEPML4_spec pml4 d = Some d' -> exists m', exec setEPML4S s m s m' /\ EPT.MatchE eb d' m' /\
    MatchUp (ept d') m' /\ (forall a, ~ InUp a -> m' a = m a).
Proof.
  intros d d' m s pml4 HE HU H; unfold setEPML4_spec in H.
  destruct (flags d && (pml4 =? 0)); [|discriminate].
  inversion H; subst d'; clear H.
  set (m' := upd (upd (upd (upd (upd m ub (ent (ub + 512))) (ub + 512) 0) (ub + 513) 0) (ub + 514) 0) (ub + 515) 0).
  exists m'; split; [|split; [|split]].
  - repeat (eapply ESeq; [apply exec_store; reflexivity|]); apply exec_store; reflexivity.
  - intros g h Hg Hl; simpl in Hl; rewrite leaf_empty3 in Hl by auto; discriminate.
  - unfold MatchUp, v4, vP, vD, zset; simpl.
    destruct (Z.eq_dec 0 0) as [_|N]; [|congruence].
    split; [|split].
    + unfold m'; rewrite !upd_other by lia; apply upd_same.
    + intros _ j Hj; unfold empty3; cbv beta iota; unfold m'.
      assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
      destruct Hj' as [ -> | [ -> | [ -> | -> ]]]; unfold upd;
        repeat (destruct (Z.eq_dec _ _); [first [lia | reflexivity] |]); lia.
    + intros j k _ _ hv; unfold empty3 in hv; discriminate.
  - intros a Ha; unfold InUp in Ha; unfold m'; rewrite !upd_other by lia; reflexivity.
Qed.

(** A loop that writes [f i] at [base + i] for [i] from [i0] to [n]. *)
Definition fillS (base : Z) (n : Z) (v : expr) : stmt :=
  While (Bin Ltu (Var "i") (Const n))
        (Seq (Store (Bin Add (Const base) (Var "i")) v) (Assign "i" (Bin Add (Var "i") (Const 1)))).

Lemma fill_run : forall base n v f, 0 <= base -> base + n <= W -> 0 <= n -> n < W ->
  (forall s i, s "i" = i -> 0 <= i < n -> eval s v = f i) ->
  forall k s m i, s "i" = i -> 0 <= i -> i + Z.of_nat k = n ->
  exists s' m', exec (fillS base n v) s m s' m' /\ (forall j, i <= j < n -> m' (base + j) = f j) /\
    (forall a, (a < base + i \/ base + n <= a) -> m' a = m a).
Proof.
  intros base n v f Hb Hn Hn0 HnW Hv; induction k as [|k IH]; intros s m i Hs Hi Hk.
  - exists s, m; split; [|split].
    + apply EWhileF; simpl; rewrite Hs; replace i with n by lia; rewrite Z.ltb_irrefl; reflexivity.
    + intros j Hj; lia.
    + auto.
  - set (s1 := lset s "i" (i + 1)).
    set (m1 := upd m (base + i) (f i)).
    destruct (IH s1 m1 (i + 1)) as [s' [m' [Ex [Hz Hf]]]]; [unfold s1; apply lset_same | lia | lia |].
    exists s', m'; split; [|split].
    + apply EWhileT with (s1 := s1) (m1 := m1).
      * simpl; rewrite Hs; replace (i <? n) with true by (symmetry; apply Z.ltb_lt; lia); discriminate.
      * apply ESeq with (s1 := s) (m1 := m1).
        -- unfold m1; apply exec_store; [simpl; rewrite Hs; apply norm_small; unfold W in *; lia | apply Hv; auto; lia].
        -- unfold s1; apply exec_assign; simpl; rewrite Hs; apply norm_small; unfold W in *; lia.
      * exact Ex.
    + intros j Hj; destruct (Z.eq_dec j i) as [->|Ne].
      * rewrite Hf by lia; unfold m1; apply upd_same.
      * apply Hz; lia.
    + intros a Ha; rewrite Hf by lia; unfold m1; apply upd_other; lia.
Qed.

(** *** [setEPDPTE]: [pdpt[pdpt] = &pdt[pdpt] | 7; pdt[pdpt][0..511] = 0;] *)
Definition setEPDPTES (pdpt : Z) : stmt :=
  Seq (Store (Const (ub + 512 + pdpt)) (Const (ent (P2 pdpt))))
      (Seq (Assign "i" (Const 0)) (fillS (P2 pdpt) 512 (Const 0))).

Theorem setEPDPTE_ref : forall d d' m s pml4 pdpt, EPT.MatchE eb d m -> MatchUp (ept d) m ->
  setEPDPTE_spec pml4 pdpt d = Some d' -> exists s' m', exec (setEPDPTES pdpt) s m s' m' /\
    EPT.MatchE eb d' m' /\ MatchUp (ept d') m' /\ (forall a, ~ InUp a -> m' a = m a).
Proof.
  intros d d' m s pml4 pdpt HE HU H; unfold setEPDPTE_spec in H.
  destruct (flags d && (pml4 =? 0) && (0 <=? pdpt) && (pdpt <? 4)) eqn:C; [|discriminate].
  repeat rewrite andb_true_iff in C; destruct C as [[[_ _] C1] C2].
  apply Z.leb_le in C1; apply Z.ltb_lt in C2.
  destruct (ept d 0) as [a|] eqn:E0; [|discriminate].
  inversion H; subst d'; clear H.
  set (m1 := upd m (ub + 512 + pdpt) (ent (P2 pdpt))).
  destruct (fill_run (P2 pdpt) 512 (Const 0) (fun _ => 0) ltac:(unfold P2; lia) ltac:(unfold P2, NPG in *; lia)
    ltac:(lia) ltac:(unfold W; lia) (fun _ _ _ _ => eq_refl) 512 (lset s "i" 0) m1 0 (lset_same _ _ _) ltac:(lia) ltac:(reflexivity))
    as [s' [m' [Ex [Hz Hf]]]].
  destruct HU as (U1 & U2 & U3).
  assert (V4 : v4 (ept d) = true) by (unfold v4; rewrite E0; reflexivity).
  exists s', m'; split; [|split; [|split]].
  - apply ESeq with (s1 := s) (m1 := m1); [apply exec_store; reflexivity|].
    apply ESeq with (s1 := lset s "i" 0) (m1 := m1); [apply exec_assign; reflexivity | exact Ex].
  - intros g h Hg Hl; simpl in Hl.
    destruct (idx_split g Hg) as (P0 & PJ & PK & PT & Eg).
    unfold ept_leaf, zset in Hl; rewrite P0 in Hl.
    destruct (Z.eq_dec 0 0) as [_|N]; [|congruence].
    destruct (Z.eq_dec (PDPT' g) pdpt) as [Ej|Ej]; [unfold empty2 in Hl; discriminate|].
    rewrite Hf by (unfold P2; lia); unfold m1; rewrite upd_other by lia.
    apply HE; auto; unfold ept_leaf; rewrite P0, E0; exact Hl.
  - unfold MatchUp, v4, vP, vD, zset; simpl.
    destruct (Z.eq_dec 0 0) as [_|N]; [|congruence].
    split; [|split].
    + rewrite Hf by (unfold P2; lia); unfold m1; rewrite upd_other by lia.
      rewrite U1, V4; reflexivity.
    + intros _ j Hj.
      rewrite Hf by (unfold P2; lia); unfold m1.
      destruct (Z.eq_dec j pdpt) as [ -> | Nj]; [apply upd_same|].
      rewrite upd_other by lia; rewrite (U2 V4 j Hj); unfold vP; rewrite E0; reflexivity.
    + intros j k Hj Hk hv.
      destruct (Z.eq_dec j pdpt) as [ -> | Nj].
      * rewrite Hz by lia; unfold empty2; reflexivity.
      * rewrite Hf by (unfold P2; lia); unfold m1; rewrite upd_other by (unfold P2; lia).
        assert (hv' : vP (ept d) j = true) by (unfold vP; rewrite E0; exact hv).
        rewrite (U3 j k Hj Hk hv'); unfold vD; rewrite E0; reflexivity.
  - intros a' Ha; unfold InUp in Ha; rewrite Hf by (unfold P2; lia); unfold m1; rewrite upd_other by lia; reflexivity.
Qed.

(** *** [setEPDTE]: [pdt[pdpt][pdir] = &ptab[pdpt][pdir] | 7;] *)
Definition setEPDTES (pdpt pdir : Z) : stmt :=
  Store (Const (P2 pdpt + pdir)) (Const (ent (leafT pdpt pdir))).

Theorem setEPDTE_ref : forall d d' m s pml4 pdpt pdir, EPT.MatchE eb d m -> MatchUp (ept d) m ->
  setEPDTE_spec pml4 pdpt pdir d = Some d' ->
  exec (setEPDTES pdpt pdir) s m s (upd m (P2 pdpt + pdir) (ent (leafT pdpt pdir))) /\
  EPT.MatchE eb d' (upd m (P2 pdpt + pdir) (ent (leafT pdpt pdir))) /\
  MatchUp (ept d') (upd m (P2 pdpt + pdir) (ent (leafT pdpt pdir))).
Proof.
  intros d d' m s pml4 pdpt pdir HE HU H; unfold setEPDTE_spec in H.
  destruct (flags d && (pml4 =? 0) && (0 <=? pdpt) && (pdpt <? 4) && (0 <=? pdir) && (pdir <? 512)) eqn:C;
    [|discriminate].
  repeat rewrite andb_true_iff in C; destruct C as [[[[[_ _] C1] C2] C3] C4].
  apply Z.leb_le in C1; apply Z.ltb_lt in C2; apply Z.leb_le in C3; apply Z.ltb_lt in C4.
  destruct (ept d 0) as [a|] eqn:E0; [|discriminate].
  destruct (a pdpt) as [b|] eqn:Eb; [|discriminate].
  inversion H; subst d'; clear H.
  destruct HU as (U1 & U2 & U3).
  assert (V4 : v4 (ept d) = true) by (unfold v4; rewrite E0; reflexivity).
  split; [apply exec_store; reflexivity|split].
  - intros g h Hg Hl; simpl in Hl.
    destruct (idx_split g Hg) as (P0 & PJ & PK & PT & Eg).
    unfold ept_leaf, zset in Hl; rewrite P0 in Hl.
    destruct (Z.eq_dec 0 0) as [_|N]; [|congruence].
    rewrite upd_other by (unfold P2; lia).
    apply HE; auto; unfold ept_leaf; rewrite P0, E0.
    destruct (Z.eq_dec (PDPT' g) pdpt) as [Ej|Ej]; simpl in Hl.
    + rewrite Ej, Eb.
      destruct (Z.eq_dec (PDIR' g) pdir) as [Ek|Ek]; simpl in Hl; [unfold empty1 in Hl; discriminate | exact Hl].
    + exact Hl.
  - unfold MatchUp, v4, vP, vD, zset; simpl.
    destruct (Z.eq_dec 0 0) as [_|N]; [|congruence].
    split; [|split].
    + rewrite upd_other by (unfold P2; lia); rewrite U1, V4; reflexivity.
    + intros _ j Hj; rewrite upd_other by (unfold P2; lia).
      rewrite (U2 V4 j Hj); unfold vP; rewrite E0.
      destruct (Z.eq_dec j pdpt) as [ -> | Nj]; [rewrite Eb|]; reflexivity.
    + intros j k Hj Hk hv.
      destruct (Z.eq_dec j pdpt) as [ -> | Nj].
      * destruct (Z.eq_dec k pdir) as [ -> | Nk]; [apply upd_same|].
        rewrite upd_other by (unfold P2; lia).
        assert (hv' : vP (ept d) pdpt = true) by (unfold vP; rewrite E0, Eb; reflexivity).
        rewrite (U3 pdpt k Hj Hk hv'); unfold vD; rewrite E0, Eb; reflexivity.
      * rewrite upd_other by (unfold P2; lia).
        assert (hv' : vP (ept d) j = true) by (unfold vP; rewrite E0; exact hv).
        rewrite (U3 j k Hj Hk hv'); unfold vD; rewrite E0; reflexivity.
Qed.

(** *** [ept_init]'s upper tables: [pml4[0]], [pdpt[0..3]], and the 2048 [pdt] entries. *)
Definition initUpS : stmt :=
  Seq (Store (Const ub) (Const (ent (ub + 512))))
  (Seq (Store (Const (ub + 512)) (Const (ent (P2 0)))) (Seq (Store (Const (ub + 513)) (Const (ent (P2 1))))
  (Seq (Store (Const (ub + 514)) (Const (ent (P2 2)))) (Seq (Store (Const (ub + 515)) (Const (ent (P2 3))))
  (Seq (Assign "i" (Const 0))
       (fillS (ub + 1024) 2048 (Bin Add (Const (ent eb)) (Bin Mul (Var "i") (Const 2048))))))))).

Lemma ent_step : forall i, 0 <= i < 2048 ->
  norm (ent eb + norm (i * 2048)) = ent (eb + 512 * i).
Proof.
  intros i Hi; unfold ent, norm.
  rewrite Z.add_mod_idemp_r by (unfold W; lia); rewrite Z.add_mod_idemp_l by (unfold W; lia).
  f_equal; lia.
Qed.

Lemma fill_val : forall s0 i, s0 "i" = i -> 0 <= i < 2048 ->
  eval s0 (Bin Add (Const (ent eb)) (Bin Mul (Var "i") (Const 2048))) = ent (eb + 512 * i).
Proof. intros s0 i Hs Hi; simpl; rewrite Hs; apply ent_step; auto. Qed.

Theorem init_up_ref : forall e m s, exists s' m', exec initUpS s m s' m' /\ MatchUp (real_ept e) m' /\
  (forall a, ~ InUp a -> m' a = m a).
Proof.
  intros e m s.
  set (m1 := upd (upd (upd (upd (upd m ub (ent (ub + 512))) (ub + 512) (ent (P2 0))) (ub + 513) (ent (P2 1)))
    (ub + 514) (ent (P2 2))) (ub + 515) (ent (P2 3))).
  destruct (fill_run (ub + 1024) 2048 (Bin Add (Const (ent eb)) (Bin Mul (Var "i") (Const 2048)))
    (fun i => ent (eb + 512 * i)) ltac:(lia) ltac:(unfold NPG in *; lia) ltac:(lia) ltac:(unfold W; lia)
    fill_val 2048 (lset s "i" 0) m1 0 (lset_same _ _ _) ltac:(lia) ltac:(reflexivity))
    as [s' [m' [Ex [Hz Hf]]]].
  exists s', m'; split; [|split; [unfold MatchUp; split; [|split]|]].
  - unfold initUpS.
    repeat (eapply ESeq; [apply exec_store; reflexivity|]).
    eapply ESeq; [apply exec_assign; reflexivity | exact Ex].
  - unfold v4, real_ept, zset; simpl.
    destruct (Z.eq_dec 0 0) as [_|N]; [|congruence].
    rewrite Hf by lia; unfold m1; rewrite !upd_other by lia; apply upd_same.
  - intros _ j Hj.
    unfold vP, real_ept, zset; simpl.
    destruct (Z.eq_dec 0 0) as [_|N]; [|congruence].
    replace ((0 <=? j) && (j <? 4)) with true by (symmetry; apply andb_true_intro; split; lia).
    rewrite Hf by lia; unfold m1.
    assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
    destruct Hj' as [ -> | [ -> | [ -> | -> ]]]; unfold upd;
        repeat (destruct (Z.eq_dec _ _); [first [lia | reflexivity] |]); lia.
  - intros j k Hj Hk _.
    unfold vD, real_ept, zset; simpl.
    destruct (Z.eq_dec 0 0) as [_|N]; [|congruence].
    replace ((0 <=? j) && (j <? 4)) with true by (symmetry; apply andb_true_intro; split; lia).
    replace ((0 <=? k) && (k <? 512)) with true by (symmetry; apply andb_true_intro; split; lia).
    unfold P2, leafT.
    replace (ub + 1024 + 512 * j + k) with (ub + 1024 + (512 * j + k)) by lia.
    rewrite Hz by lia; f_equal; lia.
  - intros a Ha; unfold InUp in Ha; rewrite Hf by lia; unfold m1; rewrite !upd_other by lia; reflexivity.
Qed.

End Code.
