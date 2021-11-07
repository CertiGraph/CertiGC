From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From compcert Require Import common.Values.
From compcert Require Import lib.Integers.

From VST Require Import floyd.functional_base.
From VST Require Import floyd.sublist.
From VST Require Import msl.shares.
From VST Require Import veric.base.
From VST Require Import veric.shares.
From VST Require Import veric.val_lemmas.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Export graph.graph_gen.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.util.

Import ListNotations.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.


Record Addr: Type := {
    addr_gen: nat;
    addr_block: nat;
}.
Instance Addr_EqDec: EqDec Addr eq.
Proof.
    intros [gen_x block_x] [gen_y block_y].
    destruct (equiv_dec gen_x gen_y) as [ H1 | H1 ] ;
    destruct (equiv_dec block_x block_y) as [ H2 | H2 ].
    all:
      cbv in * ; subst ; try firstorder ;
      right ; intro F ; congruence.
Defined.


Record Field: Type := {
    field_addr: Addr;
    field_index: nat;
}.
Instance Field_EqDec: EqDec Field eq.
Proof.
    intros [addr_x index_x] [addr_y index_y].
    destruct (equiv_dec addr_x addr_y) as [ H1 | H1 ] ;
    destruct (equiv_dec index_x index_y) as [ H2 | H2 ].
    all:
      cbv in * ; subst ; try firstorder ;
      right ; intro F ; congruence.
Defined.


Inductive GC_Pointer := | GCPtr: block -> ptrofs -> GC_Pointer.

Definition FieldValue: Type := option (Z + GC_Pointer).

Instance FieldValue_Inhabitant: Inhabitant FieldValue := None.


Record Block : Type := {
    block_mark: bool;
    block_copied_vertex: Addr;
    block_fields: list FieldValue;
    block_color: Z;
    block_tag: Z;
    block_tag__range: (0 <= block_tag < 256)%Z;
    block_color__range: (0 <= block_color < 4)%Z;
    block_fields__range: (0 < Zlength block_fields < two_p (WORD_SIZE * 8 - 10))%Z;
    tag_no_scan: (NO_SCAN_TAG <= block_tag -> ~ In None block_fields)%Z;
    (* TODO: what's up with this? why can raw_f be None at all? *)
}.

Lemma block_fields__range2: forall r,
    Zlength (block_fields r) <= if Archi.ptr64 then Int64.max_signed else Int.max_signed.
Proof.
  intros. pose proof (block_fields__range r). remember (Zlength (block_fields r)).
  clear Heqz. cbv delta[Archi.ptr64]. simpl. rewrite <- Z.lt_succ_r. destruct H.
  transitivity (two_p (WORD_SIZE * 8 - 10)); auto. now vm_compute.
Qed.

Lemma block_fields__not_nil (rvb: Block):
    block_fields rvb <> nil.
Proof.
    pose proof (block_fields__range rvb) as H.
    remember (block_fields rvb) as ff eqn:E.
    clear E rvb.
    now destruct ff.
Qed.

Definition block_fields_head (rvb: Block): FieldValue
 := match block_fields rvb as l return (block_fields rvb = l -> FieldValue) with
    | nil => fun E => False_rect _ (block_fields__not_nil _ E)
    | f :: _ => fun _ => f
    end eq_refl.

Lemma block_fields_head__cons (rvb: Block):
    exists f ff, block_fields rvb = f :: ff /\ block_fields_head rvb = f.
Proof.
    refine (
        match block_fields rvb as l return (block_fields rvb = l -> _) with
        | nil => fun E => False_rect _ (block_fields__not_nil _ E)
        | f :: ff => fun E => _
        end eq_refl
    ).
    exists f, ff. destruct rvb. simpl in E. now subst.
Qed.


Record Generation: Type := {
    generation_base: val;
    generation_block_count: nat;
    generation_sh: share;
    generation_base__isptr: isptr generation_base;
    generation_sh__writable: writable_share generation_sh;
}.

Definition null_generation: Generation := {|
    generation_base := Vptr xH Ptrofs.zero;
    generation_block_count := O;
    generation_sh := Tsh;
    generation_base__isptr := I;
    generation_sh__writable := writable_share_top;
|}.

Instance Generation_Inhabitant: Inhabitant Generation := null_generation.


Record Generations : Type := {
    generations: list Generation;
    generations__not_nil: generations <> nil;
}.

Definition HeapGraph := LabeledGraph Addr Field Block unit Generations.


Definition vertex_size (g: HeapGraph) (v: Addr): Z
 := Zlength (vlabel g v).(block_fields) + 1.

Lemma vertex_size__one (g: HeapGraph) (v: Addr):
    1 < vertex_size g v.
Proof.
    unfold vertex_size.
    pose proof (block_fields__range (vlabel g v)).
    lia.
Qed.


Definition vertex_size_accum g gen (s: Z) (n: nat): Z
 := s + vertex_size g {| addr_gen := gen; addr_block := n |}.

Lemma vertex_size_accum__mono (g: HeapGraph) (gen: nat) (s: Z) (n: nat):
    s < vertex_size_accum g gen s n.
Proof.
    unfold vertex_size_accum.
    pose proof (vertex_size__one g {| addr_gen := gen; addr_block := n |}) as H.
    lia.
Qed.

Lemma vertex_size_accum__comm (g: HeapGraph) (gen: nat) (s: Z) (n1 n2: nat):
    vertex_size_accum g gen (vertex_size_accum g gen s n1) n2 =
    vertex_size_accum g gen (vertex_size_accum g gen s n2) n1.
Proof.
    unfold vertex_size_accum.
    lia.
Qed.

Lemma vertex_size_accum__fold_lt (g: HeapGraph) (gen: nat) (s: Z) (l: list nat) (Hl: l <> nil):
    s < fold_left (vertex_size_accum g gen) l s.
Proof.
    apply (fold_left_Z_mono_strict (vertex_size_accum g gen) nil l l) ; try assumption.
    + apply vertex_size_accum__mono.
    + apply vertex_size_accum__comm.
    + apply Permutation_refl.
Qed.

Lemma vertex_size_accum__fold_le (g: HeapGraph) (gen: nat) (s: Z) (l: list nat):
    s <= fold_left (vertex_size_accum g gen) l s.
Proof.
    destruct l as [|n l] ; try easy.
    rewrite Z.le_lteq.
    left.
    now apply vertex_size_accum__fold_lt.
Qed.

Lemma vsa_fold_left:
  forall (g : HeapGraph) (gen : nat) (l : list nat) (z1 z2 : Z),
    fold_left (vertex_size_accum g gen) l (z2 + z1) =
    fold_left (vertex_size_accum g gen) l z2 + z1.
Proof.
  intros. revert z1 z2. induction l; intros; simpl. 1: reflexivity.
  rewrite <- IHl. f_equal. unfold vertex_size_accum. lia.
Qed.


Definition previous_vertices_size (g: HeapGraph) (gen i: nat): Z
 := fold_left (vertex_size_accum g gen) (nat_inc_list i) 0.

 Lemma previous_vertices_size__S (g: HeapGraph) (gen i: nat):
    previous_vertices_size g gen (S i) =
    previous_vertices_size g gen i + vertex_size g {| addr_gen := gen; addr_block := i |}.
Proof.
    unfold previous_vertices_size at 1.
    now rewrite nat_inc_list_S, fold_left_app.
Qed.

Lemma previous_vertices_size__nonneg (g: HeapGraph) (gen i: nat):
    0 <= previous_vertices_size g gen i.
Proof.
    unfold previous_vertices_size.
    apply vertex_size_accum__fold_le.
Qed.

Lemma pvs_mono_strict: forall g gen i j,
    (i < j)%nat -> (previous_vertices_size g gen i < previous_vertices_size g gen j)%Z.
Proof.
  intros. assert (j = i + (j - i))%nat by lia. rewrite H0. remember (j - i)%nat. subst j.
  unfold previous_vertices_size. rewrite nat_inc_list_app, fold_left_app.
  apply vertex_size_accum__fold_lt. pose proof (nat_seq_length i n). destruct (nat_seq i n).
  - simpl in H0. lia.
  - intro S; inversion S.
Qed.

Lemma pvs_mono: forall g gen i j,
    (i <= j)%nat -> (previous_vertices_size g gen i <= previous_vertices_size g gen j)%Z.
Proof.
  intros. rewrite Nat.le_lteq in H. destruct H. 2: subst; lia.
  rewrite Z.le_lteq. left. apply pvs_mono_strict. assumption.
Qed.

Lemma pvs_lt_rev: forall g gen i j,
    (previous_vertices_size g gen i < previous_vertices_size g gen j)%Z -> (i < j)%nat.
Proof.
  intros. destruct (le_lt_dec j i).
  - apply (pvs_mono g gen) in l. exfalso. lia.
  - assumption.
Qed.



Definition vertex_offset (g: HeapGraph) (v: Addr): Z
 := previous_vertices_size g (addr_gen v) (addr_block v) + 1.


Definition nth_gen (g: HeapGraph) (gen: nat): Generation
 := nth gen g.(glabel).(generations) null_generation.

Definition graph_gen_clear (g: HeapGraph) (gen: nat) :=
  generation_block_count (nth_gen g gen) = O.


Definition nth_sh g gen := generation_sh (nth_gen g gen).


Definition graph_gen_size g gen
 := previous_vertices_size g gen (generation_block_count (nth_gen g gen)).


Definition graph_has_gen (g: HeapGraph) (n: nat): Prop
 := (n < length g.(glabel).(generations))%nat.

Lemma graph_has_gen_O (g: HeapGraph):
    graph_has_gen g O.
Proof.
    hnf.
    destruct (generations (glabel g)) as [|x xx] eqn:E ; simpl; try lia.
    now pose proof (generations__not_nil (glabel g)).
Qed.


Definition gen_has_index (g: HeapGraph) (gen index: nat): Prop
 := (index < generation_block_count (nth_gen g gen))%nat.


Lemma vo_lt_gs: forall g v,
    gen_has_index g (addr_gen v) (addr_block v) ->
    vertex_offset g v < graph_gen_size g (addr_gen v).
Proof.
  intros. unfold vertex_offset, graph_gen_size. red in H.
  remember (generation_block_count (nth_gen g (addr_gen v))). remember (addr_gen v).
  assert (S (addr_block v) <= n)%nat by lia.
  apply Z.lt_le_trans with (previous_vertices_size g n0 (S (addr_block v))).
  - rewrite previous_vertices_size__S. apply Zplus_lt_compat_l, vertex_size__one.
  - apply pvs_mono; assumption.
Qed.


Definition graph_has_gen_dec g n: {graph_has_gen g n} + {~ graph_has_gen g n}
 := lt_dec n (length (generations (glabel g))).


Definition gen_start (g: HeapGraph) (gen: nat): val
 := if graph_has_gen_dec g gen
    then generation_base (nth_gen g gen)
    else Vundef.

Lemma graph_has_gen_start_isptr (g: HeapGraph) (n: nat) (Hgn: graph_has_gen g n):
    isptr (gen_start g n).
Proof.
    unfold gen_start.
    if_tac ; try easy.
    apply generation_base__isptr.
Qed.


Definition vertex_address (g: HeapGraph) (v: Addr): val
 := offset_val (WORD_SIZE * vertex_offset g v) (gen_start g (addr_gen v)).

Lemma vertex_address_the_same: forall (g1 g2: HeapGraph) v,
    (forall v, g1.(vlabel) v = g2.(vlabel) v) ->
    map generation_base g1.(glabel).(generations) = map generation_base g2.(glabel).(generations) ->
    vertex_address g1 v = vertex_address g2 v.
Proof.
  intros. unfold vertex_address. f_equal.
  - f_equal. unfold vertex_offset. f_equal. remember (addr_block v). clear Heqn.
    induction n; simpl; auto. rewrite !previous_vertices_size__S, IHn. f_equal. unfold vertex_size.
    rewrite H. reflexivity.
  - assert (forall gen, graph_has_gen g1 gen <-> graph_has_gen g2 gen). {
      intros. unfold graph_has_gen.
      cut (length (generations (glabel g1)) = length (generations (glabel g2))).
      - intros. rewrite H1. reflexivity.
      - do 2 rewrite <- (map_length generation_base). rewrite H0. reflexivity.
    } unfold gen_start. do 2 if_tac; [|rewrite H1 in H2; contradiction.. |reflexivity].
    unfold nth_gen. rewrite <- !(map_nth generation_base), H0. reflexivity.
Qed.


Definition make_header (g: HeapGraph) (v: Addr): Z:=
  let vb := vlabel g v in if vb.(block_mark)
                          then 0 else
                            vb.(block_tag) + (Z.shiftl vb.(block_color) 8) +
                            (Z.shiftl (Zlength vb.(block_fields)) 10).

Lemma make_header_mark_iff: forall g v,
    make_header g v = 0 <-> block_mark (vlabel g v) = true.
Proof.
  intros. unfold make_header. destruct (block_mark (vlabel g v)). 1: intuition.
  split; intros. 2: inversion H. exfalso.
  destruct (block_tag__range (vlabel g v)) as [? _].
  assert (0 <= Z.shiftl (block_color (vlabel g v)) 8). {
    rewrite Z.shiftl_nonneg. apply (proj1 (block_color__range (vlabel g v))).
  } assert (Z.shiftl (Zlength (block_fields (vlabel g v))) 10 <= 0) by lia.
  clear -H2. assert (0 <= Z.shiftl (Zlength (block_fields (vlabel g v))) 10) by
      (rewrite Z.shiftl_nonneg; apply Zlength_nonneg).
  assert (Z.shiftl (Zlength (block_fields (vlabel g v))) 10 = 0) by lia. clear -H0.
  rewrite Z.shiftl_eq_0_iff in H0 by lia.
  pose proof (proj1 (block_fields__range (vlabel g v))). lia.
Qed.

Lemma make_header_range: forall g v, 0 <= make_header g v < two_p (WORD_SIZE * 8).
Proof.
  intros. unfold make_header. destruct (block_mark (vlabel g v)).
  - pose proof (two_p_gt_ZERO (WORD_SIZE * 8)). unfold WORD_SIZE in *; lia.
  - pose proof (block_tag__range (vlabel g v)). pose proof (block_color__range (vlabel g v)).
    pose proof (block_fields__range (vlabel g v)). remember (block_tag (vlabel g v)) as z1.
    clear Heqz1. remember (block_color (vlabel g v)) as z2. clear Heqz2.
    remember (Zlength (block_fields (vlabel g v))) as z3. clear Heqz3.
    assert (0 <= 8) by lia. apply (Zbits.Zshiftl_mul_two_p z2) in H2. rewrite H2.
    clear H2. assert (0 <= 10) by lia. apply (Zbits.Zshiftl_mul_two_p z3) in H2.
    rewrite H2. clear H2. assert (two_p 10 > 0) by (apply two_p_gt_ZERO; lia).
    assert (two_p 8 > 0) by (apply two_p_gt_ZERO; lia). split.
    + assert (0 <= z2 * two_p 8) by (apply Z.mul_nonneg_nonneg; lia).
      assert (0 <= z3 * two_p 10) by (apply Z.mul_nonneg_nonneg; lia). lia.
    + destruct H as [_ ?]. destruct H0 as [_ ?]. destruct H1 as [_ ?].
      change 256 with (two_p 8) in H. change 4 with (two_p 2) in H0.
      assert (z1 <= two_p 8 - 1) by lia. clear H.
      assert (z2 <= two_p 2 - 1) by lia. clear H0.
      assert (z3 <= two_p (WORD_SIZE * 8 - 10) - 1) by lia. clear H1.
      apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in H. 2: lia.
      apply Z.mul_le_mono_nonneg_r with (p := two_p 10) in H0. 2: lia.
      rewrite Z.mul_sub_distr_r in H, H0. rewrite Z.mul_1_l in H, H0.
      assert (0 <= WORD_SIZE * 8 - 10) by (unfold WORD_SIZE; lia).
      rewrite <- two_p_is_exp in H, H0 by lia. simpl Z.add in H, H0. clear H1.
      Opaque two_p. simpl. Transparent two_p. lia.
Qed.

Lemma make_header_int_rep_mark_iff: forall g v,
    (if Archi.ptr64 then Int64.repr (make_header g v) = Int64.repr 0
     else Int.repr (make_header g v) = Int.repr 0) <->
    block_mark (vlabel g v) = true.
Proof.
  intros. rewrite <- make_header_mark_iff. split; intros; [|rewrite H; reflexivity].
  cbv delta [Archi.ptr64] in H. simpl in H. Transparent Int.repr Int64.repr.
  inversion H. Opaque Int64.repr Int.repr. clear H. rewrite H1.
  match goal with
  | H : Int64.Z_mod_modulus _ = _ |- _ => rewrite Int64.Z_mod_modulus_eq in H
  | H : Int.Z_mod_modulus _ = _ |- _ => rewrite Int.Z_mod_modulus_eq in H
  end.
  rewrite Z.mod_small in H1; auto. apply make_header_range.
Qed.

Lemma make_header_Wosize: forall g v,
    block_mark (vlabel g v) = false ->
    if Archi.ptr64 then
      Int64.shru (Int64.repr (make_header g v)) (Int64.repr 10) =
      Int64.repr (Zlength (block_fields (vlabel g v)))
    else
      Int.shru (Int.repr (make_header g v)) (Int.repr 10) =
      Int.repr (Zlength (block_fields (vlabel g v))).
Proof.
  intros. cbv delta [Archi.ptr64]. simpl.
  match goal with
  | |- Int64.shru _ _ = Int64.repr _ =>
    rewrite Int64.shru_div_two_p, !Int64.unsigned_repr
  | |- Int.shru _ _ = Int.repr _ => rewrite Int.shru_div_two_p, !Int.unsigned_repr
  end.
  - f_equal. unfold make_header.
    remember (vlabel g v) as r eqn:E. clear E.
    rewrite H, !Zbits.Zshiftl_mul_two_p by lia. rewrite Z.div_add. 2: compute; lia.
    pose proof (block_tag__range r). pose proof (block_color__range r).
    cut ((block_tag r + block_color r * two_p 8) / two_p 10 = 0). 1: intros; lia.
    apply Z.div_small. change 256 with (two_p 8) in H0. change 4 with (two_p 2) in H1.
    assert (0 <= block_tag r <= two_p 8 - 1) by lia. clear H0. destruct H2.
    assert (0 <= block_color r <= two_p 2 - 1) by lia. clear H1. destruct H3.
    assert (two_p 8 > 0) by (apply two_p_gt_ZERO; lia). split.
    + assert (0 <= block_color r * two_p 8) by (apply Z.mul_nonneg_nonneg; lia). lia.
    + apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in H3. 2: lia.
      rewrite Z.mul_sub_distr_r, <- two_p_is_exp in H3 by lia. simpl Z.add in H3. lia.
  - rep_lia.
  - pose proof (make_header_range g v). unfold WORD_SIZE in *.
    match goal with
    | |- context [Int64.max_unsigned] =>
      unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize
    | |- context [Int.max_unsigned] =>
      unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize
    end. simpl Z.mul in H0. rewrite two_power_nat_two_p. simpl Z.of_nat. lia.
Qed.


Definition field_t: Type := Z + GC_Pointer + Field.

Instance field_t_inhabitant: Inhabitant field_t := inl (inl Z.zero).

Definition GC_Pointer2val (x: GC_Pointer) : val :=
  match x with | GCPtr b z => Vptr b z end.

Definition field2val (g: HeapGraph) (fd: field_t) : val :=
  match fd with
  | inl (inl z) => odd_Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr e => vertex_address g (dst g e)
  end.


Fixpoint make_fields' (l_raw: list FieldValue) (v: Addr) (n: nat): list field_t :=
  match l_raw with
  | nil => nil
  | Some (inl z) :: l => inl (inl z) :: make_fields' l v (n + 1)
  | Some (inr ptr) :: l => inl (inr ptr) :: make_fields' l v (n + 1)
  | None :: l => inr {| field_addr := v; field_index := n |} :: make_fields' l v (n + 1)
  end.

Lemma e_in_make_fields': forall l v n e,
    In (inr e) (make_fields' l v n) -> exists s, e = {| field_addr := v; field_index := s |}.
Proof.
  induction l; intros; simpl in *. 1: exfalso; assumption. destruct a; [destruct s|].
  - simpl in H. destruct H. 1: inversion H. apply IHl with (n + 1)%nat. assumption.
  - simpl in H. destruct H. 1: inversion H. apply IHl with (n + 1)%nat. assumption.
  - simpl in H. destruct H.
    + inversion H. exists n. reflexivity.
    + apply IHl with (n + 1)%nat. assumption.
Qed.

Lemma make_fields'_eq_length: forall l v n, length (make_fields' l v n) = length l.
Proof.
  intros. revert n. induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|]; simpl; rewrite IHl; reflexivity.
Qed.

Lemma make_fields'_eq_Zlength: forall l v n, Zlength (make_fields' l v n) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct. rewrite make_fields'_eq_length. reflexivity.
Qed.

Lemma make_fields'_edge_depends_on_index:
  forall n l_raw i v e,
    0 <= Z.of_nat n < Zlength l_raw ->
    nth n (make_fields' l_raw v i) field_t_inhabitant = inr e ->
    e = {| field_addr := v; field_index := n+i |}.
Proof.
  induction n as [|n' IHn'].
  - intros. destruct l_raw as [| r l_raw]; try inversion H0.
    destruct r; [destruct s|]; simpl in H0; inversion H0;
      reflexivity.
  - intro. destruct l_raw as [| r l_raw]; try inversion 2.
    replace (S n' + i)%nat with (n' + S i)%nat by lia.
    specialize (IHn' l_raw (S i) v e).
    assert (0 <= Z.of_nat n' < Zlength l_raw) by
          (rewrite Zlength_cons, Nat2Z.inj_succ in H; lia).
      assert (nth n' (make_fields' l_raw v (S i)) field_t_inhabitant = inr e) by
        (destruct r; [destruct s|]; simpl in H2;
        replace (i + 1)%nat with (S i) in H2 by lia; assumption).
      destruct r; [destruct s|]; simpl; apply IHn'; assumption.
Qed.

Lemma make_fields'_n_doesnt_matter: forall i l v n m gcptr,
    nth i (make_fields' l v n) field_t_inhabitant = inl (inr gcptr) ->
    nth i (make_fields' l v m) field_t_inhabitant = inl (inr gcptr).
Proof.
  intros.
  unfold make_fields' in *.
  generalize dependent i.
  generalize dependent n.
  generalize dependent m.
  induction l.
  + intros; assumption.
  + induction i.
    - destruct a; [destruct s|]; simpl; intros; try assumption; try inversion H.
    - destruct a; [destruct s|]; simpl; intro;
        apply IHl with (m:=(m+1)%nat) in H; assumption.
Qed.

Lemma make_fields'_item_was_in_list: forall l v n gcptr,
    0 <= n < Zlength l ->
    Znth n (make_fields' l v 0) = inl (inr gcptr) ->
    Znth n l = Some (inr gcptr).
Proof.
  intros.
  rewrite <- nth_Znth; rewrite <- nth_Znth in H0; [| rewrite Zlength_correct in *..];
    try rewrite make_fields'_eq_length; [|assumption..].
  generalize dependent n.
  induction l.
  - intros. rewrite nth_Znth in H0; try assumption.
    unfold make_fields' in H0; rewrite Znth_nil in H0; inversion H0.
  - intro n. induction (Z.to_nat n) eqn:?.
    + intros. destruct a; [destruct s|]; simpl in *; try inversion H0; try reflexivity.
    + intros. simpl in *. clear IHn0.
      replace n0 with (Z.to_nat (Z.of_nat n0)) by apply Nat2Z.id.
      assert (0 <= Z.of_nat n0 < Zlength l). {
        split; try lia.
        destruct H; rewrite Zlength_cons in H1.
        apply Zsucc_lt_reg; rewrite <- Nat2Z.inj_succ.
        rewrite <- Heqn0; rewrite Z2Nat.id; assumption.
      }
      destruct a; [destruct s|]; simpl in H0; apply IHl;
        try assumption; apply make_fields'_n_doesnt_matter with (n:=1%nat);
        rewrite Nat2Z.id; assumption.
Qed.


Definition make_fields (g: HeapGraph) (v: Addr): list field_t :=
  make_fields' (vlabel g v).(block_fields) v O.

Definition get_edges (g: HeapGraph) (v: Addr): list Field :=
  filter_sum_right (make_fields g v).

Definition graph_has_v (g: HeapGraph) (v: Addr): Prop
 := graph_has_gen g (addr_gen v) /\ gen_has_index g (addr_gen v) (addr_block v).

Definition no_dangling_dst (g: HeapGraph): Prop :=
  forall v, graph_has_v g v ->
            forall e, In e (get_edges g v) -> graph_has_v g (dst g e).

Lemma get_edges_In: forall g v s,
    In {| field_addr := v; field_index := s|} (get_edges g v) <-> In s (map field_index (get_edges g v)).
Proof.
  intros. unfold get_edges, make_fields. remember (block_fields (vlabel g v)).
  remember O as n. clear Heqn Heql. revert n. induction l; intros; simpl ; try easy.
  destruct a as [a|] ; try destruct a as [a|a] ; simpl.
  all: rewrite IHl ; try easy.
  intuition. inversion H0. left; reflexivity.
Qed.

Lemma get_edges_fst: forall g v e, In e (get_edges g v) -> field_addr e = v.
Proof.
  intros g v e. unfold get_edges, make_fields. remember (block_fields (vlabel g v)).
  remember O as n. clear Heqn Heql. revert n. induction l; intros; simpl in *.
  - exfalso; assumption.
  - destruct a; [destruct s|]; simpl in *;
      [| | destruct H; [subst e; simpl; reflexivity|]]; apply IHl in H; assumption.
Qed.


Definition v_in_range (v: val) (start: val) (n: Z): Prop :=
  exists i, 0 <= i < n /\ v = offset_val i start.


Lemma make_fields_eq_length: forall g v,
    Zlength (make_fields g v) = Zlength (block_fields (vlabel g v)).
Proof.
  unfold make_fields. intros.
  rewrite !Zlength_correct, make_fields'_eq_length. reflexivity.
Qed.

Lemma make_fields_Znth_edge: forall g v n e,
    0 <= n < Zlength (block_fields (vlabel g v)) ->
    Znth n (make_fields g v) = inr e -> e = {| field_addr := v; field_index := Z.to_nat n |}.
Proof.
  intros. rewrite <- nth_Znth in H0. 2: rewrite make_fields_eq_length; assumption.
  apply make_fields'_edge_depends_on_index in H0.
  - now rewrite Nat.add_0_r in H0.
  - now rewrite Z2Nat.id.
Qed.

Lemma make_fields_edge_unique: forall g e v1 v2 n m,
    0 <= n < Zlength (make_fields g v1) ->
    0 <= m < Zlength (make_fields g v2) ->
    Znth n (make_fields g v1) = inr e ->
    Znth m (make_fields g v2) = inr e ->
    n = m /\ v1 = v2.
Proof.
  intros. unfold make_fields in *.
  rewrite make_fields'_eq_Zlength in *.
  assert (0 <= Z.of_nat (Z.to_nat n) < Zlength (block_fields (vlabel g v1))) by
      (destruct H; split; rewrite Z2Nat.id; assumption).
  rewrite <- nth_Znth in H1 by
      (rewrite make_fields'_eq_Zlength; assumption).
  assert (0 <= Z.of_nat (Z.to_nat m) < Zlength (block_fields (vlabel g v2))) by
       (destruct H0; split; rewrite Z2Nat.id; assumption).
  rewrite <- nth_Znth in H2 by
      (rewrite make_fields'_eq_Zlength; assumption).
  pose proof (make_fields'_edge_depends_on_index
                (Z.to_nat n) (block_fields (vlabel g v1)) 0 v1 e H3 H1).
  pose proof (make_fields'_edge_depends_on_index
                (Z.to_nat m) (block_fields (vlabel g v2)) 0 v2 e H4 H2).
  rewrite H5 in H6. inversion H6.
  rewrite Nat.add_cancel_r, Z2Nat.inj_iff in H9 by lia.
  split; [assumption | reflexivity].
Qed.


Definition make_fields_vals (g: HeapGraph) (v: Addr): list val :=
  let vb := vlabel g v in
  let original_fields_val := map (field2val g) (make_fields g v) in
  if vb.(block_mark)
  then vertex_address g vb.(block_copied_vertex) :: tl original_fields_val
  else original_fields_val.

Lemma fields_eq_length: forall g v,
    Zlength (make_fields_vals g v) = Zlength (block_fields (vlabel g v)).
Proof.
  intros. rewrite !Zlength_correct. f_equal. unfold make_fields_vals, make_fields.
  destruct (block_mark (vlabel g v)).
  - destruct (block_fields_head__cons (vlabel g v)) as [r [l [? ?]]].
    rewrite H; simpl; destruct r; [destruct s|]; simpl;
      rewrite map_length, make_fields'_eq_length; reflexivity.
  - rewrite map_length, make_fields'_eq_length. reflexivity.
Qed.

Lemma mfv_unmarked_all_is_ptr_or_int: forall (g : HeapGraph) (v : Addr),
    no_dangling_dst g -> graph_has_v g v ->
    Forall is_pointer_or_integer (map (field2val g) (make_fields g v)).
Proof.
  intros. rewrite Forall_forall. intros f ?. apply list_in_map_inv in H1.
  destruct H1 as [x [? ?]]. destruct x as [[? | ?] | ?]; simpl in H1; subst.
  - unfold odd_Z2val. exact I.
  - destruct g0. exact I.
  - apply isptr_is_pointer_or_integer. unfold vertex_address.
    rewrite isptr_offset_val. apply graph_has_gen_start_isptr.
    apply filter_sum_right_In_iff, H in H2; [destruct H2|]; assumption.
Qed.

Definition copy_compatible (g: HeapGraph): Prop :=
  forall v, graph_has_v g v -> (vlabel g v).(block_mark) = true ->
            graph_has_v g (vlabel g v).(block_copied_vertex) /\
            addr_gen v <> addr_gen (vlabel g v).(block_copied_vertex).

Lemma mfv_all_is_ptr_or_int: forall g v,
    copy_compatible g -> no_dangling_dst g -> graph_has_v g v ->
    Forall is_pointer_or_integer (make_fields_vals g v).
Proof.
  intros. rewrite Forall_forall. intros f ?. unfold make_fields_vals in H2.
  pose proof (mfv_unmarked_all_is_ptr_or_int _ _ H0 H1). rewrite Forall_forall in H3.
  specialize (H3 f). destruct (block_mark (vlabel g v)) eqn:? . 2: apply H3; assumption.
  simpl in H2. destruct H2. 2: apply H3, In_tail; assumption.
  subst f. unfold vertex_address. apply isptr_is_pointer_or_integer.
  rewrite isptr_offset_val. apply graph_has_gen_start_isptr, (proj1 (H _ H1 Heqb)).
Qed.



Lemma make_fields_the_same: forall (g1 g2: HeapGraph) v,
    (forall e, dst g1 e = dst g2 e) ->
    (forall v, g1.(vlabel) v = g2.(vlabel) v) ->
    map generation_base g1.(glabel).(generations) = map generation_base g2.(glabel).(generations) ->
    make_fields_vals g1 v = make_fields_vals g2 v.
Proof.
  intros. unfold make_fields_vals, make_fields. remember O. clear Heqn. rewrite H0.
  remember (block_fields (vlabel g2 v)) as l. clear Heql.
  cut (forall fl, map (field2val g1) fl = map (field2val g2) fl).
  - intros. rewrite H2. rewrite (vertex_address_the_same g1 g2) by assumption.
    reflexivity.
  - apply map_ext. intros. unfold field2val. destruct a. 1: reflexivity.
    rewrite H. apply vertex_address_the_same; assumption.
Qed.


Definition unmarked_gen_size (g: HeapGraph) (gen: nat) :=
  fold_left (vertex_size_accum g gen)
            (filter (fun i => negb (vlabel g {| addr_gen := gen; addr_block := i |}).(block_mark))
                    (nat_inc_list (generation_block_count (nth_gen g gen)))) 0.

Lemma unmarked_gen_size_le: forall g n, unmarked_gen_size g n <= graph_gen_size g n.
Proof.
  intros g gen. unfold unmarked_gen_size, graph_gen_size, previous_vertices_size.
  apply fold_left_mono_filter;
    [intros; rewrite Z.le_lteq; left; apply vertex_size_accum__mono | apply vertex_size_accum__comm].
Qed.

Lemma single_unmarked_le: forall g v,
    graph_has_v g v -> block_mark (vlabel g v) = false ->
    vertex_size g v <= unmarked_gen_size g (addr_gen v).
Proof.
  intros. unfold unmarked_gen_size.
  remember (filter (fun i : nat => negb (block_mark (vlabel g {| addr_gen := addr_gen v; addr_block := i |})))
                   (nat_inc_list (generation_block_count (nth_gen g (addr_gen v))))).
  assert (In (addr_block v) l). {
    subst l. rewrite filter_In. split.
    - rewrite nat_inc_list_In_iff. apply (proj2 H).
    - destruct v; simpl. rewrite negb_true_iff. apply H0. }
  apply In_Permutation_cons in H1. destruct H1 as [l1 ?]. symmetry in H1.
  change (addr_block v :: l1) with ([addr_block v] ++ l1) in H1.
  transitivity (fold_left (vertex_size_accum g (addr_gen v)) [addr_block v] 0).
  - simpl. destruct v; simpl. apply Z.le_refl.
  - apply (fold_left_Z_mono (vertex_size_accum g (addr_gen v)) [addr_block v] l1 l 0);
      [intros; apply Z.le_lteq; left; apply vertex_size_accum__mono | apply vertex_size_accum__comm | apply H1].
Qed.


Lemma lgd_graph_has_v: forall g e v v',
    graph_has_v g v <-> graph_has_v (labeledgraph_gen_dst g e v') v.
Proof. reflexivity. Qed.

Lemma lgd_graph_has_gen: forall g e v x,
    graph_has_gen (labeledgraph_gen_dst g e v) x <-> graph_has_gen g x.
Proof. intros; unfold graph_has_gen; intuition. Qed.

Lemma lgd_raw_fld_length_eq: forall (g: HeapGraph) v e v',
    Zlength (block_fields (vlabel g v)) =
    Zlength (block_fields (vlabel (labeledgraph_gen_dst g e v') v)).
Proof. reflexivity. Qed.

Lemma lgd_vertex_address_eq: forall g e v' x,
    vertex_address (labeledgraph_gen_dst g e v') x = vertex_address g x.
Proof. reflexivity. Qed.

Lemma lgd_make_fields_eq: forall (g : HeapGraph) (v v': Addr) e,
    make_fields (labeledgraph_gen_dst g e v') v = make_fields g v.
Proof. reflexivity. Qed.

Lemma lgd_make_header_eq: forall g e v' x,
    make_header g x = make_header (labeledgraph_gen_dst g e v') x.
Proof. reflexivity. Qed.

Lemma lgd_block_mark_eq: forall (g: HeapGraph) e (v v' : Addr),
    block_mark (vlabel g v) = block_mark (vlabel (labeledgraph_gen_dst g e v') v).
Proof. reflexivity. Qed.

Lemma lgd_dst_old: forall (g: HeapGraph) e v e',
    e <> e' -> dst (labeledgraph_gen_dst g e v) e' = dst g e'.
Proof.
  intros. simpl. unfold updateEdgeFunc. rewrite if_false. 1: reflexivity. auto.
Qed.

Lemma lgd_dst_new: forall (g: HeapGraph) e v,
    dst (labeledgraph_gen_dst g e v) e = v.
Proof. intros. simpl. unfold updateEdgeFunc. rewrite if_true; reflexivity. Qed.

Definition closure_has_index (g: HeapGraph) (gen index: nat) :=
  (index <= generation_block_count (nth_gen g gen))%nat.

Definition closure_has_v (g: HeapGraph) (v: Addr): Prop :=
  graph_has_gen g (addr_gen v) /\ closure_has_index g (addr_gen v) (addr_block v).

Lemma graph_has_v_in_closure: forall g v, graph_has_v g v -> closure_has_v g v.
Proof.
  intros g v. destruct v as [gen index].
  unfold graph_has_v, closure_has_v, closure_has_index, gen_has_index.
  simpl. intros. intuition.
Qed.


Definition root_t: Type := Z + GC_Pointer + Addr.

Instance root_t_inhabitant: Inhabitant root_t := inl (inl Z.zero).

Definition roots_t: Type := list root_t.

Definition root2val (g: HeapGraph) (fd: root_t) : val :=
  match fd with
  | inl (inl z) => odd_Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr v => vertex_address g v
  end.


Definition outlier_t: Type := list GC_Pointer.
