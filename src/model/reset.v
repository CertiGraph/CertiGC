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

From CertiGraph Require Export graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.heap.
From CertiGC Require Import model.thread_info.
From CertiGC Require Import model.util.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.


Definition reset_gen_info (gi: Generation) : Generation := {|
    generation_base := generation_base gi;
    generation_block_count := O;
    generation_sh := generation_sh gi;
    generation_base__isptr := generation_base__isptr gi;
    generation_sh__writable := generation_sh__writable gi;
|}.

Fixpoint reset_nth_gen_info
         (n: nat) (gi: list Generation) : list Generation :=
  match n with
  | O => match gi with
         | nil => nil
         | g :: l => reset_gen_info g :: l
         end
  | S m => match gi with
           | nil => nil
           | g :: l => g :: reset_nth_gen_info m l
           end
  end.

  Lemma reset_nth_gen_info_length: forall n gl,
  length (reset_nth_gen_info n gl) = length gl.
Proof.
intros. revert n. induction gl; simpl; intros; destruct n; simpl;
                    [| | | rewrite IHgl]; reflexivity.
Qed.

Lemma reset_nth_gen_info_not_nil: forall n g, reset_nth_gen_info n (generations g) <> nil.
Proof.
intros. pose proof (generations__not_nil g). destruct (generations g).
- contradiction.
- destruct n; simpl; discriminate.
Qed.

Lemma reset_nth_gen_info_diff: forall gl i j a,
  i <> j -> nth i (reset_nth_gen_info j gl) a = nth i gl a.
Proof.
intros ? ? ?. revert gl i. induction j; intros; simpl; destruct gl; try reflexivity.
- destruct i. 1: contradiction. simpl. reflexivity.
- destruct i. 1: reflexivity. simpl. apply IHj. lia.
Qed.

Lemma reset_nth_gen_info_same: forall gl i,
  nth i (reset_nth_gen_info i gl) null_generation = reset_gen_info (nth i gl null_generation).
Proof.
intros. revert gl. induction i; intros; destruct gl; simpl in *; try reflexivity.
apply IHi.
Qed.

Lemma reset_nth_gen_info_overflow: forall gl i,
  (length gl <= i)%nat -> reset_nth_gen_info i gl = gl.
Proof.
intros ? ?. revert gl. induction i; intros; destruct gl; simpl in *; try reflexivity.
1: lia. rewrite IHi; [reflexivity | lia].
Qed.

Definition reset_nth_graph_info (n: nat) (g: Generations) : Generations := {|
    generations := reset_nth_gen_info n g.(generations);
    generations__not_nil := reset_nth_gen_info_not_nil n g;
|}.


Lemma generation_base__reset: forall n l,
   map generation_base (reset_nth_gen_info n l) = map generation_base l.
Proof.
  intros. revert n.
  induction l; intros; simpl; destruct n; simpl; [| | | rewrite IHl]; reflexivity.
Qed.


Definition reset_nth_glabel (n: nat) (g: HeapGraph) : HeapGraph :=
  Build_LabeledGraph _ _ _ (pg_lg g) (vlabel g) (elabel g)
                     (reset_nth_graph_info n (glabel g)).

Definition pregraph_remove_vertex_and_edges
        (g: HeapGraph) (v: Addr): PreGraph Addr Field :=
fold_left pregraph_remove_edge (get_edges g v) (pregraph_remove_vertex g v).

Definition lgraph_remove_vertex_and_edges (g: HeapGraph) (v: Addr): HeapGraph :=
  Build_LabeledGraph _ _ _ (pregraph_remove_vertex_and_edges g v)
                     (vlabel g) (elabel g) (glabel g).

Definition remove_nth_gen_ve (g: HeapGraph) (gen: nat): HeapGraph :=
  let all_nv := map (fun idx => {| addr_gen := gen; addr_block := idx |})
                    (nat_inc_list (generation_block_count (nth_gen g gen))) in
  fold_left lgraph_remove_vertex_and_edges all_nv g.

Lemma remove_ve_glabel_unchanged: forall g gen,
    glabel (remove_nth_gen_ve g gen) = glabel g.
Proof.
  intros. unfold remove_nth_gen_ve.
  remember (map (fun idx : nat => {| addr_gen := gen; addr_block := idx |})
                (nat_inc_list (generation_block_count (nth_gen g gen)))). clear Heql.
  revert g. induction l; intros; simpl. 1: reflexivity. rewrite IHl. reflexivity.
Qed.

Lemma remove_ve_vlabel_unchanged: forall g gen v,
    vlabel (remove_nth_gen_ve g gen) v = vlabel g v.
Proof.
  intros. unfold remove_nth_gen_ve.
  remember (map (fun idx : nat => {| addr_gen := gen; addr_block := idx |})
                (nat_inc_list (generation_block_count (nth_gen g gen)))). clear Heql.
  revert g v. induction l; intros; simpl. 1: reflexivity. rewrite IHl. reflexivity.
Qed.

Lemma remove_ve_dst_unchanged: forall g gen e,
    dst (remove_nth_gen_ve g gen) e = dst g e.
Proof.
  intros. unfold remove_nth_gen_ve.
  remember (map (fun idx : nat => {| addr_gen := gen; addr_block := idx |})
                (nat_inc_list (generation_block_count (nth_gen g gen)))). clear Heql.
  revert g e. induction l; intros; simpl. 1: reflexivity. rewrite IHl.
  clear. simpl. unfold pregraph_remove_vertex_and_edges.
  transitivity (dst (pregraph_remove_vertex g a) e). 2: reflexivity.
  remember (pregraph_remove_vertex g a) as g'. remember (get_edges g a) as l.
  clear a g Heqg' Heql. rename g' into g. revert g e. induction l; intros; simpl.
  1: reflexivity. rewrite IHl. reflexivity.
Qed.

Definition reset_graph (n: nat) (g: HeapGraph) : HeapGraph :=
  reset_nth_glabel n (remove_nth_gen_ve g n).

Lemma graph_has_gen_reset: forall (g: HeapGraph) gen1 gen2,
    graph_has_gen (reset_graph gen1 g) gen2 <-> graph_has_gen g gen2.
Proof.
  intros. unfold graph_has_gen. simpl. rewrite reset_nth_gen_info_length.
  rewrite remove_ve_glabel_unchanged. reflexivity.
Qed.

Lemma reset_nth_gen_diff: forall g i j,
    i <> j -> nth_gen (reset_graph j g) i = nth_gen g i.
Proof.
  intros. unfold nth_gen, reset_graph. simpl.
  rewrite remove_ve_glabel_unchanged.
  apply reset_nth_gen_info_diff. assumption.
Qed.

Lemma vertex_address_reset: forall (g: HeapGraph) v n,
    vertex_address (reset_graph n g) v = vertex_address g v.
Proof.
  intros. apply vertex_address_the_same; unfold reset_graph; simpl.
  - intros. rewrite remove_ve_vlabel_unchanged. reflexivity.
  - rewrite remove_ve_glabel_unchanged, generation_base__reset. reflexivity.
Qed.

Lemma make_fields_reset: forall (g: HeapGraph) v n,
    make_fields_vals (reset_graph n g) v = make_fields_vals g v.
Proof.
  intros. apply make_fields_the_same; unfold reset_graph; simpl; intros.
  - apply remove_ve_dst_unchanged.
  - apply remove_ve_vlabel_unchanged.
  - rewrite remove_ve_glabel_unchanged. apply generation_base__reset.
Qed.

Lemma make_header_reset: forall (g: HeapGraph) v n,
    make_header (reset_graph n g) v = make_header g v.
Proof.
  intros. unfold make_header. simpl vlabel. rewrite remove_ve_vlabel_unchanged.
  reflexivity.
Qed.


Lemma reset_space__order: forall sp, (0 <= 0 <= space_capacity sp)%Z.
Proof. intros. pose proof (space__order sp). lia. Qed.

Definition reset_space (sp: Space) : Space := {|
    space_base := space_base sp;
    space_allocated := 0;
    space_capacity := space_capacity sp;
    space_sh := space_sh sp;
    space__order := reset_space__order sp;
    space__upper_bound := space__upper_bound sp;
|}.

Fixpoint reset_nth_space (n: nat) (s: list Space): list Space :=
  match n with
  | O => match s with
         | nil => nil
         | sp :: l => reset_space sp :: l
         end
  | S m => match s with
           | nil => nil
           | sp :: l => sp :: reset_nth_space m l
           end
  end.

Lemma reset_nth_space_length: forall n s, length (reset_nth_space n s) = length s.
Proof.
  induction n; intros; simpl.
  - destruct s; simpl; reflexivity.
  - destruct s; [|simpl; rewrite (IHn s0)]; reflexivity.
Qed.

Lemma reset_nth_space_Zlength: forall n s, Zlength s = Zlength (reset_nth_space n s).
Proof. intros. rewrite !Zlength_correct, reset_nth_space_length. reflexivity. Qed.

Lemma reset_nth_heap_Zlength: forall n h,
    Zlength (reset_nth_space n (heap_spaces h)) = MAX_SPACES.
Proof. intros. rewrite <- reset_nth_space_Zlength. apply heap_spaces__size. Qed.

Lemma reset_nth_space_Permutation: forall n s,
    (n < length s)%nat -> exists l, Permutation (reset_nth_space n s)
                                          (reset_space (nth n s null_space) :: l) /\
                              Permutation s (nth n s null_space :: l).
Proof.
  induction n; intros; destruct s; simpl in *; try lia.
  - exists s0. split; constructor; reflexivity.
  - assert (n < length s0)%nat by lia. destruct (IHn _ H0) as [ll [? ?]].
    exists (s :: ll). split.
    + transitivity (s :: reset_space (nth n s0 null_space) :: ll).
      1: constructor; assumption. apply perm_swap.
    + transitivity (s :: nth n s0 null_space :: ll).
      1: constructor; assumption. apply perm_swap.
Qed.

Lemma reset_nth_space_Znth: forall s i,
    (i < length s)%nat ->
    reset_nth_space i s = upd_Znth (Z.of_nat i) s (reset_space (Znth (Z.of_nat i) s)).
Proof.
  intros ? ?. revert s. induction i; intros; destruct s; simpl in H; try lia.
  - simpl.
    rewrite upd_Znth0_old, Znth_0_cons, sublist_1_cons, sublist_same;
      try reflexivity; rewrite Zlength_cons. lia.
    pose proof (Zlength_nonneg s0). lia.
  - replace (Z.of_nat (S i)) with (Z.of_nat i + 1)%Z by (zify; lia).
    rewrite Znth_pos_cons by lia.
    replace (Z.of_nat i + 1 - 1)%Z with (Z.of_nat i) by lia. simpl.
    rewrite upd_Znth_pos_cons.
    + replace (Z.of_nat i + 1 - 1)%Z with (Z.of_nat i) by lia.
      rewrite <- IHi; [reflexivity | lia].
    + rewrite Zlength_correct. lia.
Qed.

Lemma reset_nth_space_overflow: forall s i, (length s <= i)%nat -> reset_nth_space i s = s.
Proof.
  intros ? ?. revert s.
  induction i; intros; destruct s; simpl in *; try lia; try reflexivity.
  rewrite IHi; [reflexivity | lia].
Qed.

Lemma reset_nth_space_diff: forall gl i j a,
    i <> j -> nth i (reset_nth_space j gl) a = nth i gl a.
Proof.
  intros ? ? ?. revert gl i. induction j; intros; simpl; destruct gl; try reflexivity.
  - destruct i. 1: contradiction. simpl. reflexivity.
  - destruct i. 1: reflexivity. simpl. apply IHj. lia.
Qed.

Lemma reset_nth_space_same: forall gl i a,
    (i < length gl)%nat -> nth i (reset_nth_space i gl) a = reset_space (nth i gl a).
Proof.
  intros. revert gl H. induction i; intros; destruct gl; simpl in *; try lia.
  - reflexivity.
  - apply IHi. lia.
Qed.

Definition reset_nth_heap (n: nat) (h: Heap) : Heap := {|
  heap_spaces := reset_nth_space n (heap_spaces h);
  heap_spaces__size := reset_nth_heap_Zlength n h;
|}.

Definition reset_nth_heap_thread_info (n: nat) (ti: thread_info) :=
  Build_thread_info (ti_heap_p ti) (reset_nth_heap n (ti_heap ti))
                    (ti_args ti) (arg_size ti).

Lemma reset_thread_info_overflow: forall n ti,
    (length (heap_spaces (ti_heap ti)) <= n)%nat -> reset_nth_heap_thread_info n ti = ti.
Proof.
  intros. unfold reset_nth_heap_thread_info. destruct ti. f_equal.
  simpl. unfold reset_nth_heap. destruct ti_heap. simpl in *.
  assert (heap_spaces = reset_nth_space n heap_spaces) by
      (rewrite reset_nth_space_overflow; [reflexivity | assumption]).
  apply EqdepFacts.f_eq_dep_non_dep, EqdepFacts.eq_dep1_dep.
  apply (EqdepFacts.eq_dep1_intro _ _ _ _ _ _ H0). apply proof_irr.
Qed.
