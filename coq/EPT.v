(** * The extended page table (EPT), ported from mCertiKOS and implemented

    Ported from [objects/ObjEPT.v] and [layerlib/AuxStateDataType.v]: the
    four-level EPT, the specifications [ept_get_page_entry_spec],
    [ept_set_page_entry_spec], [ept_add_mapping_spec],
    [ept_invalidate_mappings_spec], [ept_gpa_to_hpa_spec], [ept_mmap_spec],
    [ept_set_permission_spec]. The EPT maps guest-physical pages to
    host-physical addresses.

    The public mCertiKOS sources have no code for this layer. The code here is
    written from the C quoted in comments in [ObjEPT.v]: the table is a flat
    array [ept.ptab[pdpt][pdir][ptab]] in the kernel region at [eb], one word
    per guest page, covering the 4 GB guest-physical space (2^20 pages).

    Each function is proved to refine its specification: if the region
    matches the abstract EPT and the specification is defined, the code runs
    and leaves a region matching the result.

    What differs:
    - The C operations on words ([&], [|], [<<]) are [wand], [wor], [wshl]
      (32-bit wrap-around). mCertiKOS writes [Z.land] and the like; on 32-bit
      inputs they agree.
    - [ept_init] in mCertiKOS is the whole boot plus [real_ept]. Here
      [ept_init0_spec] is the EPT part only: every guest page gets an entry 0
      (not mapped, no permissions). The definition of [real_ept] is not in the
      public sources; this is the one that makes [ept_mmap] defined on every
      guest page afterwards.
    - The four accessors that build the tree level by level ([setEPML4_spec]
      and the like) are not implemented: with a fixed flat array the tree
      always exists. *)

From Stdlib Require Import ZArith String Lia Bool.
From VCoq Require Import Lang.
Local Open Scope string_scope.
Local Open Scope bool_scope.
Open Scope Z_scope.

(** ** Abstract data ([AuxStateDataType.v]) *)

Inductive EPTE := EPTEValid (hpa : Z) | EPTEUndef.
Definition EPTAB := Z -> EPTE.
Inductive EPDTE := EPDTEValid (t : EPTAB) | EPDTEUndef.
Definition EPDT := Z -> EPDTE.
Inductive EPDPTE := EPDPTEValid (t : EPDT) | EPDPTEUndef.
Definition EPDPT := Z -> EPDPTE.
Inductive EPML4E := EPML4EValid (t : EPDPT) | EPML4EUndef.
Definition EPT := Z -> EPML4E.

Definition zset {A} (f : Z -> A) (k : Z) (v : A) : Z -> A :=
  fun x => if Z.eq_dec x k then v else f x.

(** The part of the abstract state this layer uses. *)
Record VData := mkV { ikern : bool; pg : bool; ihost : bool; ept : EPT }.

Definition set_ept (d : VData) (e : EPT) : VData := mkV (ikern d) (pg d) (ihost d) e.

Definition PTAB' (i : Z) := i mod 512.
Definition PDIR' (i : Z) := (i / 512) mod 512.
Definition PDPT' (i : Z) := (i / 262144) mod 512.
Definition PML4' (i : Z) := (i / 134217728) mod 512.

Definition EPTEPERM := 7.
Definition EPT_NO_PERM := 4294967288.
Definition EPT_ADDR_OFFSET_MASK := 4095.
Definition EPT_PG_IGNORE_PAT_or_PERM := 71.
Definition EPT_ADDR_MASK := 4294963200.
Definition EPT_PG_MEMORY_TYPE := 3.
Definition max_unsigned := 4294967295.

(** The entry of guest page [gpa], through the four levels. *)
Definition ept_leaf (e : EPT) (gpa : Z) : option Z :=
  match e (PML4' gpa) with
  | EPML4EValid epdpt =>
    match epdpt (PDPT' gpa) with
    | EPDPTEValid epdt =>
      match epdt (PDIR' gpa) with
      | EPDTEValid eptab =>
        match eptab (PTAB' gpa) with
        | EPTEValid hpa => Some hpa
        | EPTEUndef => None
        end
      | EPDTEUndef => None
      end
    | EPDPTEUndef => None
    end
  | EPML4EUndef => None
  end.

(** Write the entry of guest page [gpa], if the three upper levels exist. *)
Definition ept_store (e : EPT) (gpa v : Z) : option EPT :=
  match e (PML4' gpa) with
  | EPML4EValid epdpt =>
    match epdpt (PDPT' gpa) with
    | EPDPTEValid epdt =>
      match epdt (PDIR' gpa) with
      | EPDTEValid eptab =>
        let eptab' := zset eptab (PTAB' gpa) (EPTEValid v) in
        let epdt' := zset epdt (PDIR' gpa) (EPDTEValid eptab') in
        let epdpt' := zset epdpt (PDPT' gpa) (EPDPTEValid epdt') in
        Some (zset e (PML4' gpa) (EPML4EValid epdpt'))
      | EPDTEUndef => None
      end
    | EPDPTEUndef => None
    end
  | EPML4EUndef => None
  end.

(** ** Specifications ([ObjEPT.v]) *)

Section Specs.
Variable maxpage : Z.

Definition flags (d : VData) : bool := ikern d && pg d && ihost d.

Definition ept_get_page_entry_spec (gpa : Z) (d : VData) : option Z :=
  if flags d then
    if (0 <=? gpa) && (gpa <? maxpage) then ept_leaf (ept d) gpa else None
  else None.

Definition ept_set_page_entry_spec (gpa hpa : Z) (d : VData) : option VData :=
  if flags d then
    if (0 <=? gpa) && (gpa <? maxpage) && (0 <=? hpa) && (hpa <? maxpage) then
      match ept_store (ept d) gpa hpa with
      | Some e' => Some (set_ept d e')
      | None => None
      end
    else None
  else None.

Definition ept_add_mapping_spec (gpa hpa memtype : Z) (d : VData) : option (VData * Z) :=
  if flags d then
    if (0 <=? gpa) && (gpa <? maxpage) && (0 <=? hpa) && (hpa <? maxpage) &&
       (0 <=? memtype) && (memtype <? 4096) then
      let va := wor (wor (wand hpa EPT_ADDR_MASK) EPT_PG_IGNORE_PAT_or_PERM)
                    (wshl memtype EPT_PG_MEMORY_TYPE) in
      match ept_store (ept d) gpa va with
      | Some e' => Some (set_ept d e', 0)
      | None => None
      end
    else None
  else None.

(** [invept] only flushes the TLB, which the abstract state does not have. *)
Definition ept_invalidate_mappings_spec (d : VData) : option Z :=
  if ikern d && ihost d then Some 0 else None.

Definition ept_gpa_to_hpa_spec (gpa : Z) (d : VData) : option Z :=
  match ept_get_page_entry_spec gpa d with
  | Some hpa =>
    if (0 <=? hpa) && (hpa <=? max_unsigned) then
      if wand hpa EPTEPERM =? 0 then Some 0
      else Some (wor (wand hpa EPT_ADDR_MASK) (wand gpa EPT_ADDR_OFFSET_MASK))
    else None
  | None => None
  end.

Definition ept_mmap_spec (gpa hpa memtype : Z) (d : VData) : option (VData * Z) :=
  match ept_get_page_entry_spec gpa d with
  | Some hpa' =>
    if (0 <=? hpa') && (hpa' <=? max_unsigned) then
      if (0 <=? memtype) && (memtype <? 4096) then
        if wand hpa' EPTEPERM =? 0 then ept_add_mapping_spec gpa hpa memtype d
        else Some (d, 1)
      else None
    else None
  | None => None
  end.

Definition ept_set_permission_spec (gpa perm : Z) (d : VData) : option VData :=
  match ept_get_page_entry_spec gpa d with
  | Some hpa' =>
    if (0 <=? hpa') && (hpa' <=? max_unsigned) then
      ept_set_page_entry_spec gpa (wor (wand hpa' EPT_NO_PERM) (wand perm EPTEPERM)) d
    else None
  | None => None
  end.

(** Every guest page has an entry, 0. *)
Definition real_ept (e : EPT) : EPT :=
  zset e 0 (EPML4EValid (fun j =>
    if (0 <=? j) && (j <? 4) then
      EPDPTEValid (fun k => if (0 <=? k) && (k <? 512) then EPDTEValid (fun _ => EPTEValid 0) else EPDTEUndef)
    else EPDPTEUndef)).

Definition ept_init0_spec (d : VData) : option VData :=
  if flags d then Some (set_ept d (real_ept (ept d))) else None.

End Specs.

(** ** Indices *)

Definition NPG := 1048576.

Lemma idx_split : forall g, 0 <= g < NPG ->
  PML4' g = 0 /\ 0 <= PDPT' g < 4 /\ 0 <= PDIR' g < 512 /\ 0 <= PTAB' g < 512 /\
  g = (PDPT' g * 512 + PDIR' g) * 512 + PTAB' g.
Proof.
  intros g Hg; unfold NPG in Hg; unfold PML4', PDPT', PDIR', PTAB'.
  assert (H1 : g = 512 * (g / 512) + g mod 512) by (apply Z.div_mod; lia).
  assert (H2 : g / 512 = 512 * (g / 512 / 512) + (g / 512) mod 512) by (apply Z.div_mod; lia).
  assert (H3 : g / 512 / 512 = g / 262144) by (rewrite Z.div_div by lia; reflexivity).
  assert (H4 : 0 <= g / 262144 < 4) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (H5 : g / 134217728 = 0) by (apply Z.div_small; lia).
  rewrite H5, (Z.mod_small (g / 262144)) by lia.
  pose proof (Z.mod_pos_bound g 512) as B1; pose proof (Z.mod_pos_bound (g / 512) 512) as B2.
  rewrite H3 in H2.
  repeat split; try lia.
Qed.

Lemma idx_inj : forall g g', 0 <= g < NPG -> 0 <= g' < NPG ->
  PDPT' g' = PDPT' g -> PDIR' g' = PDIR' g -> PTAB' g' = PTAB' g -> g' = g.
Proof.
  intros g g' Hg Hg' E1 E2 E3.
  destruct (idx_split g Hg) as (_ & _ & _ & _ & Eg).
  destruct (idx_split g' Hg') as (_ & _ & _ & _ & Eg').
  rewrite Eg, Eg', E1, E2, E3; reflexivity.
Qed.

(** ** What a store does to the leaves *)

Lemma store_leaf : forall e g v e', 0 <= g < NPG -> ept_store e g v = Some e' ->
  forall g', 0 <= g' < NPG -> ept_leaf e' g' = if Z.eq_dec g' g then Some v else ept_leaf e g'.
Proof.
  intros e g v e' Hg Hs g' Hg'.
  destruct (idx_split g Hg) as (P0 & _ & _ & _ & _).
  destruct (idx_split g' Hg') as (P0' & _ & _ & _ & _).
  unfold ept_store in Hs.
  destruct (e (PML4' g)) as [a|] eqn:Ea; [|discriminate].
  destruct (a (PDPT' g)) as [b|] eqn:Eb; [|discriminate].
  destruct (b (PDIR' g)) as [c|] eqn:Ec; [|discriminate].
  inversion Hs; subst e'; clear Hs.
  unfold ept_leaf, zset.
  rewrite P0', P0 in *.
  destruct (Z.eq_dec 0 0) as [_|N]; [|congruence].
  destruct (Z.eq_dec g' g) as [->|Ne].
  - destruct (Z.eq_dec (PDPT' g) (PDPT' g)); [|congruence].
    destruct (Z.eq_dec (PDIR' g) (PDIR' g)); [|congruence].
    destruct (Z.eq_dec (PTAB' g) (PTAB' g)); [|congruence].
    reflexivity.
  - rewrite Ea.
    destruct (Z.eq_dec (PDPT' g') (PDPT' g)) as [E1|E1].
    + rewrite E1, Eb.
      destruct (Z.eq_dec (PDIR' g') (PDIR' g)) as [E2|E2].
      * rewrite E2, Ec.
        destruct (Z.eq_dec (PTAB' g') (PTAB' g)) as [E3|E3].
        -- exfalso; apply Ne; apply idx_inj; auto.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
Qed.

Lemma real_leaf : forall e g, 0 <= g < NPG -> ept_leaf (real_ept e) g = Some 0.
Proof.
  intros e g Hg.
  destruct (idx_split g Hg) as (P0 & P1 & P2 & _ & _).
  unfold ept_leaf, real_ept, zset; rewrite P0.
  destruct (Z.eq_dec 0 0); [|congruence].
  replace ((0 <=? PDPT' g) && (PDPT' g <? 4)) with true by (symmetry; apply andb_true_intro; split; lia).
  replace ((0 <=? PDIR' g) && (PDIR' g <? 512)) with true by (symmetry; apply andb_true_intro; split; lia).
  reflexivity.
Qed.

(** ** The table in the region *)

Section Code.
Variable eb : Z.
Hypothesis heb : 0 <= eb.
Hypothesis heb2 : eb + NPG <= W.
Variable maxpage : Z.
Hypothesis hmp : maxpage <= NPG.

(** Guest page [g]'s entry is the cell [eb + g]. *)
Definition MatchE (d : VData) (m : mem) : Prop :=
  forall g h, 0 <= g < NPG -> ept_leaf (ept d) g = Some h -> m (eb + g) = h.

Ltac norm_in :=
  repeat match goal with
  | |- context[norm ?z] =>
    lazymatch z with
    | context[norm _] => fail
    | _ => rewrite (norm_small z) by (unfold W, NPG in *; lia)
    end
  end.

(** [&ept.ptab[EPT_PDPT_INDEX(x)][EPT_PDIR_INDEX(x)][EPT_PTAB_INDEX(x)]] *)
Definition addrE (x : string) : expr :=
  Bin Add (Const eb)
    (Bin Add (Bin Mul (Bin Add (Bin Mul (Bin Mod (Bin Div (Var x) (Const 262144)) (Const 512)) (Const 512))
                                (Bin Mod (Bin Div (Var x) (Const 512)) (Const 512)))
                      (Const 512))
             (Bin Mod (Var x) (Const 512))).

Lemma eval_addr : forall s x g, 0 <= g < NPG -> s x = g -> eval s (addrE x) = eb + g.
Proof.
  intros s x g Hg Hs.
  pose proof (idx_split g Hg) as (_ & P1 & P2 & P3 & Eg).
  unfold PDPT', PDIR', PTAB' in *.
  unfold NPG, W in *.
  simpl; rewrite Hs; norm_in; lia.
Qed.

Lemma match_store : forall d m g v e', MatchE d m -> 0 <= g < NPG -> ept_store (ept d) g v = Some e' ->
  MatchE (set_ept d e') (upd m (eb + g) v).
Proof.
  intros d m g v e' HM Hg Hs g' h Hg' Hl.
  simpl in Hl; rewrite (store_leaf _ _ _ _ Hg Hs g' Hg') in Hl.
  destruct (Z.eq_dec g' g) as [->|Ne].
  - inversion Hl; apply upd_same.
  - rewrite upd_other by lia; apply HM; auto.
Qed.

Lemma get_leaf : forall gpa d h, ept_get_page_entry_spec maxpage gpa d = Some h ->
  0 <= gpa < NPG /\ ept_leaf (ept d) gpa = Some h.
Proof.
  intros gpa d h H; unfold ept_get_page_entry_spec in H.
  destruct (flags d); [|discriminate].
  destruct ((0 <=? gpa) && (gpa <? maxpage)) eqn:R; [|discriminate].
  apply andb_true_iff in R; destruct R as [R1 R2]; apply Z.leb_le in R1; apply Z.ltb_lt in R2.
  split; [lia | exact H].
Qed.

Lemma set_store : forall gpa hpa d d', ept_set_page_entry_spec maxpage gpa hpa d = Some d' ->
  0 <= gpa < NPG /\ exists e', ept_store (ept d) gpa hpa = Some e' /\ d' = set_ept d e'.
Proof.
  intros gpa hpa d d' H; unfold ept_set_page_entry_spec in H.
  destruct (flags d); [|discriminate].
  destruct ((0 <=? gpa) && (gpa <? maxpage) && (0 <=? hpa) && (hpa <? maxpage)) eqn:R; [|discriminate].
  repeat rewrite andb_true_iff in R; destruct R as [[[R1 R2] _] _].
  apply Z.leb_le in R1; apply Z.ltb_lt in R2.
  destruct (ept_store (ept d) gpa hpa) as [e'|]; [|discriminate].
  inversion H; split; [lia | eauto].
Qed.

(** *** [ept_get_page_entry]: [r = ept.ptab[...][...][...];] *)
Definition getPageEntryS : stmt := Load "r" (addrE "gpa").

Theorem get_page_entry_ref : forall d m s gpa h, MatchE d m -> s "gpa" = gpa ->
  ept_get_page_entry_spec maxpage gpa d = Some h -> exec getPageEntryS s m (lset s "r" h) m.
Proof.
  intros d m s gpa h HM Hs H.
  destruct (get_leaf _ _ _ H) as [Hg Hl].
  rewrite <- (HM gpa h Hg Hl).
  apply exec_load, eval_addr; auto.
Qed.

(** *** [ept_set_page_entry]: [ept.ptab[...][...][...] = hpa;] *)
Definition setPageEntryS : stmt := Store (addrE "gpa") (Var "hpa").

Theorem set_page_entry_ref : forall d d' m s gpa hpa, MatchE d m -> s "gpa" = gpa -> s "hpa" = hpa ->
  ept_set_page_entry_spec maxpage gpa hpa d = Some d' ->
  exists m', exec setPageEntryS s m s m' /\ MatchE d' m'.
Proof.
  intros d d' m s gpa hpa HM Hs Hh H.
  destruct (set_store _ _ _ _ H) as [Hg [e' [He ->]]].
  exists (upd m (eb + gpa) hpa); split.
  - apply exec_store; [apply eval_addr; auto | simpl; auto].
  - eapply match_store; eauto.
Qed.

(** *** [ept_add_mapping] *)
Definition vaE : expr :=
  Bin Or (Bin Or (Bin And (Var "hpa") (Const EPT_ADDR_MASK)) (Const EPT_PG_IGNORE_PAT_or_PERM))
         (Bin Shl (Var "memtype") (Const EPT_PG_MEMORY_TYPE)).

(** [ept.ptab[...] = (hpa & EPT_ADDR_MASK) | EPT_PG_IGNORE_PAT | EPT_PG_EX | EPT_PG_WR | EPT_PG_RD
    | EPT_PG_MEMORY_TYPE(mem_type); r = 0;] *)
Definition addMappingS : stmt := Seq (Store (addrE "gpa") vaE) (Assign "r" (Const 0)).

Theorem add_mapping_ref : forall d d' m s gpa hpa memtype r, MatchE d m ->
  s "gpa" = gpa -> s "hpa" = hpa -> s "memtype" = memtype ->
  ept_add_mapping_spec maxpage gpa hpa memtype d = Some (d', r) ->
  exists s' m', exec addMappingS s m s' m' /\ MatchE d' m' /\ s' "r" = r /\
    (forall z, z <> "r" -> s' z = s z) /\ (forall a, (a < eb \/ eb + NPG <= a) -> m' a = m a).
Proof.
  intros d d' m s gpa hpa memtype r HM Hs Hh Hm H; unfold ept_add_mapping_spec in H.
  destruct (flags d); [|discriminate].
  match type of H with context[if ?b then _ else _] => destruct b eqn:R end; [|discriminate].
  repeat rewrite andb_true_iff in R; destruct R as [[[[[R1 R2] _] _] _] _].
  apply Z.leb_le in R1; apply Z.ltb_lt in R2.
  match type of H with context[ept_store ?e ?g ?v] => destruct (ept_store e g v) as [e'|] eqn:He end;
    [|discriminate].
  inversion H; subst d' r; clear H.
  set (va := wor (wor (wand hpa EPT_ADDR_MASK) EPT_PG_IGNORE_PAT_or_PERM) (wshl memtype EPT_PG_MEMORY_TYPE)).
  exists (lset s "r" 0), (upd m (eb + gpa) va); split; [|split; [|split; [|split]]].
  - apply ESeq with (s1 := s) (m1 := upd m (eb + gpa) va).
    + apply exec_store; [apply eval_addr; [lia | auto] | simpl; rewrite Hh, Hm; reflexivity].
    + apply exec_assign; reflexivity.
  - eapply match_store; eauto; lia.
  - apply lset_same.
  - intros z Hz; apply lset_other; auto.
  - intros a Ha; apply upd_other; unfold NPG in *; lia.
Qed.

(** *** [ept_invalidate_mappings]: [invept] is a hardware TLB flush. *)
Definition invalidateS : stmt := Assign "r" (Const 0).

Theorem invalidate_ref : forall d m s r, ept_invalidate_mappings_spec d = Some r ->
  exec invalidateS s m (lset s "r" r) m.
Proof.
  intros d m s r H; unfold ept_invalidate_mappings_spec in H.
  destruct (ikern d && ihost d); [|discriminate].
  inversion H; apply exec_assign; reflexivity.
Qed.

(** *** [ept_gpa_to_hpa] *)
Definition permTestE : expr := Bin Eq (Bin And (Var "e") (Const EPTEPERM)) (Const 0).

(** [e = ept_get_page_entry(gpa); if (!(e & 7)) r = 0;
     else r = (e & EPT_ADDR_MASK) | (gpa & EPT_ADDR_OFFSET_MASK);] *)
Definition gpaToHpaS : stmt :=
  Seq (Load "e" (addrE "gpa"))
      (Ite permTestE (Assign "r" (Const 0))
           (Assign "r" (Bin Or (Bin And (Var "e") (Const EPT_ADDR_MASK))
                               (Bin And (Var "gpa") (Const EPT_ADDR_OFFSET_MASK))))).

Theorem gpa_to_hpa_ref : forall d m s gpa r, MatchE d m -> s "gpa" = gpa ->
  ept_gpa_to_hpa_spec maxpage gpa d = Some r ->
  exists s', exec gpaToHpaS s m s' m /\ s' "r" = r.
Proof.
  intros d m s gpa r HM Hs H; unfold ept_gpa_to_hpa_spec in H.
  destruct (ept_get_page_entry_spec maxpage gpa d) as [hpa|] eqn:Hg; [|discriminate].
  destruct (get_leaf _ _ _ Hg) as [Hr Hl].
  destruct ((0 <=? hpa) && (hpa <=? max_unsigned)); [|discriminate].
  pose proof (HM gpa hpa Hr Hl) as Hc.
  assert (L : exec (Load "e" (addrE "gpa")) s m (lset s "e" hpa) m).
  { rewrite <- Hc; apply exec_load, eval_addr; auto. }
  assert (Ee : lset s "e" hpa "e" = hpa) by apply lset_same.
  assert (Eg : lset s "e" hpa "gpa" = gpa) by (rewrite lset_other by discriminate; auto).
  destruct (wand hpa EPTEPERM =? 0) eqn:T.
  - inversion H; subst r.
    exists (lset (lset s "e" hpa) "r" 0); split; [|apply lset_same].
    econstructor; [exact L|].
    apply EIteT; [simpl; rewrite Ee, T; discriminate | apply exec_assign; reflexivity].
  - inversion H; subst r.
    eexists; split; [|apply lset_same].
    econstructor; [exact L|].
    apply EIteF; [simpl; rewrite Ee, T; reflexivity |].
    apply exec_assign; simpl; rewrite Ee, Eg; reflexivity.
Qed.

(** *** [ept_mmap] *)
(** [e = ept_get_page_entry(gpa); if (e & 7) r = 1; else r = ept_add_mapping(gpa, hpa, mem_type);] *)
Definition mmapS : stmt :=
  Seq (Load "e" (addrE "gpa")) (Ite permTestE addMappingS (Assign "r" (Const 1))).

Theorem mmap_ref : forall d d' m s gpa hpa memtype r, MatchE d m ->
  s "gpa" = gpa -> s "hpa" = hpa -> s "memtype" = memtype ->
  ept_mmap_spec maxpage gpa hpa memtype d = Some (d', r) ->
  exists s' m', exec mmapS s m s' m' /\ MatchE d' m' /\ s' "r" = r.
Proof.
  intros d d' m s gpa hpa memtype r HM Hs Hh Hm H; unfold ept_mmap_spec in H.
  destruct (ept_get_page_entry_spec maxpage gpa d) as [hpa'|] eqn:Hg; [|discriminate].
  destruct (get_leaf _ _ _ Hg) as [Hr Hl].
  destruct ((0 <=? hpa') && (hpa' <=? max_unsigned)); [|discriminate].
  destruct ((0 <=? memtype) && (memtype <? 4096)); [|discriminate].
  pose proof (HM gpa hpa' Hr Hl) as Hc.
  assert (L : exec (Load "e" (addrE "gpa")) s m (lset s "e" hpa') m).
  { rewrite <- Hc; apply exec_load, eval_addr; auto. }
  assert (Ee : lset s "e" hpa' "e" = hpa') by apply lset_same.
  destruct (wand hpa' EPTEPERM =? 0) eqn:T.
  - destruct (add_mapping_ref d d' m (lset s "e" hpa') gpa hpa memtype r HM
      ltac:(rewrite lset_other by discriminate; auto) ltac:(rewrite lset_other by discriminate; auto)
      ltac:(rewrite lset_other by discriminate; auto) H) as [s' [m' [Ex [HM' [Hr' _]]]]].
    exists s', m'; split; [|auto].
    econstructor; [exact L|].
    apply EIteT; [simpl; rewrite Ee, T; discriminate | exact Ex].
  - inversion H; subst d' r.
    eexists; exists m; split; [|split; [exact HM | apply lset_same]].
    econstructor; [exact L|].
    apply EIteF; [simpl; rewrite Ee, T; reflexivity | apply exec_assign; reflexivity].
Qed.

(** *** [ept_set_permission] *)
(** [e = ept_get_page_entry(gpa); ept_set_page_entry(gpa, (e & ~7) | (perm & 7));] *)
Definition setPermissionS : stmt :=
  Seq (Load "e" (addrE "gpa"))
      (Store (addrE "gpa") (Bin Or (Bin And (Var "e") (Const EPT_NO_PERM)) (Bin And (Var "perm") (Const EPTEPERM)))).

Theorem set_permission_ref : forall d d' m s gpa perm, MatchE d m -> s "gpa" = gpa -> s "perm" = perm ->
  ept_set_permission_spec maxpage gpa perm d = Some d' ->
  exists s' m', exec setPermissionS s m s' m' /\ MatchE d' m'.
Proof.
  intros d d' m s gpa perm HM Hs Hp H; unfold ept_set_permission_spec in H.
  destruct (ept_get_page_entry_spec maxpage gpa d) as [hpa'|] eqn:Hg; [|discriminate].
  destruct (get_leaf _ _ _ Hg) as [Hr Hl].
  destruct ((0 <=? hpa') && (hpa' <=? max_unsigned)); [|discriminate].
  pose proof (HM gpa hpa' Hr Hl) as Hc.
  destruct (set_store _ _ _ _ H) as [_ [e' [He ->]]].
  set (v := wor (wand hpa' EPT_NO_PERM) (wand perm EPTEPERM)) in *.
  assert (L : exec (Load "e" (addrE "gpa")) s m (lset s "e" hpa') m).
  { rewrite <- Hc; apply exec_load, eval_addr; auto. }
  exists (lset s "e" hpa'), (upd m (eb + gpa) v); split.
  - apply ESeq with (s1 := lset s "e" hpa') (m1 := m).
    + exact L.
    + apply exec_store.
      * apply eval_addr; auto; rewrite lset_other by discriminate; auto.
      * simpl; rewrite lset_same, lset_other by discriminate; rewrite Hp; reflexivity.
  - eapply match_store; eauto.
Qed.

(** *** [ept_init]: every guest page gets the entry 0. *)
Definition initLoopS : stmt :=
  While (Bin Ltu (Var "i") (Const NPG))
        (Seq (Store (Bin Add (Const eb) (Var "i")) (Const 0)) (Assign "i" (Bin Add (Var "i") (Const 1)))).

Definition eptInitS : stmt := Seq (Assign "i" (Const 0)) initLoopS.

Lemma init_loop : forall n s m i, s "i" = i -> 0 <= i -> i + Z.of_nat n = NPG ->
  exists s' m', exec initLoopS s m s' m' /\ (forall g, i <= g < NPG -> m' (eb + g) = 0) /\
    (forall a, (a < eb + i \/ eb + NPG <= a) -> m' a = m a).
Proof.
  induction n as [|n IH]; intros s m i Hs Hi Hn.
  - exists s, m; split; [|split].
    + apply EWhileF; simpl; rewrite Hs; replace i with NPG by lia; rewrite Z.ltb_irrefl; reflexivity.
    + intros g Hg; lia.
    + auto.
  - set (s1 := lset s "i" (i + 1)).
    set (m1 := upd m (eb + i) 0).
    destruct (IH s1 m1 (i + 1)) as [s' [m' [Ex [Hz Hf]]]].
    { unfold s1; apply lset_same. }
    { lia. }
    { lia. }
    exists s', m'; split; [|split].
    + eapply EWhileT.
      * simpl; rewrite Hs; replace (i <? NPG) with true by (symmetry; apply Z.ltb_lt; lia); discriminate.
      * econstructor.
        -- apply exec_store; [simpl; rewrite Hs; unfold NPG in *; norm_in; reflexivity | reflexivity].
        -- apply exec_assign; simpl; rewrite Hs; unfold NPG, W in *; norm_in; reflexivity.
      * exact Ex.
    + intros g Hg.
      destruct (Z.eq_dec g i) as [->|Ne].
      * rewrite Hf by lia; unfold m1; apply upd_same.
      * apply Hz; lia.
    + intros a Ha; rewrite Hf by lia; unfold m1; apply upd_other; lia.
Qed.

Theorem ept_init_ref : forall d d' m s, ept_init0_spec d = Some d' ->
  exists s' m', exec eptInitS s m s' m' /\ MatchE d' m' /\
    (forall a, (a < eb \/ eb + NPG <= a) -> m' a = m a).
Proof.
  intros d d' m s H; unfold ept_init0_spec in H.
  destruct (flags d); [|discriminate].
  inversion H; subst d'; clear H.
  destruct (init_loop (Z.to_nat NPG) (lset s "i" 0) m 0 (lset_same _ _ _)) as [s' [m' [Ex [Hz Hf]]]];
    [lia | unfold NPG; lia |].
  exists s', m'; split; [|split].
  - econstructor; [apply exec_assign; reflexivity | exact Ex].
  - intros g h Hg Hl; simpl in Hl; rewrite real_leaf in Hl by auto; inversion Hl; apply Hz; lia.
  - intros a Ha; apply Hf; lia.
Qed.

End Code.
