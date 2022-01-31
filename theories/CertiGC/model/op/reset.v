From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.compatible.compatible.
From CertiGC Require Import model.constants.
From CertiGC Require Import model.heap.heap.
From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.block.ptr.
From CertiGC Require Import model.heapgraph.block.cell.
From CertiGC Require Import model.heapgraph.block.field.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.has_block.
From CertiGC Require Import model.heapgraph.has_field.
From CertiGC Require Import model.heapgraph.mark.
From CertiGC Require Import model.heapgraph.predicates.
From CertiGC Require Import model.heapgraph.remset.remset.
From CertiGC Require Import model.heapgraph.roots.
From CertiGC Require Import model.thread_info.thread_info.
From CertiGC Require Import model.util.


Definition reset_gen_info (gi: Generation) : Generation := {|
    generation_base := generation_base gi;
    generation_block_count := O;
    generation_remember_count := O;
    generation_sh := generation_sh gi;
    generation_base__isptr := generation_base__isptr gi;
    generation_sh__writable := generation_sh__writable gi;
|}.

Fixpoint reset_heapgraph_generation_info
         (n: nat) (gi: list Generation) : list Generation :=
  match n with
  | O => match gi with
         | nil => nil
         | g :: l => reset_gen_info g :: l
         end
  | S m => match gi with
           | nil => nil
           | g :: l => g :: reset_heapgraph_generation_info m l
           end
  end.

  Lemma reset_heapgraph_generation_info_length: forall n gl,
  length (reset_heapgraph_generation_info n gl) = length gl.
Proof.
intros. revert n. induction gl; simpl; intros; destruct n; simpl;
                    [| | | rewrite IHgl]; reflexivity.
Qed.

Lemma reset_heapgraph_generation_info_not_nil: forall n g, reset_heapgraph_generation_info n (generations g) <> nil.
Proof.
intros. pose proof (generations__not_nil g). destruct (generations g).
- contradiction.
- destruct n; simpl; discriminate.
Qed.

Lemma reset_heapgraph_generation_info_diff: forall gl i j a,
  i <> j -> nth i (reset_heapgraph_generation_info j gl) a = nth i gl a.
Proof.
intros ? ? ?. revert gl i. induction j; intros; simpl; destruct gl; try reflexivity.
- destruct i. 1: contradiction. simpl. reflexivity.
- destruct i. 1: reflexivity. simpl. apply IHj. lia.
Qed.

Lemma reset_heapgraph_generation_info_same: forall gl i,
  nth i (reset_heapgraph_generation_info i gl) null_generation = reset_gen_info (nth i gl null_generation).
Proof.
intros. revert gl. induction i; intros; destruct gl; simpl in *; try reflexivity.
apply IHi.
Qed.

Lemma reset_heapgraph_generation_info_overflow: forall gl i,
  (length gl <= i)%nat -> reset_heapgraph_generation_info i gl = gl.
Proof.
intros ? ?. revert gl. induction i; intros; destruct gl; simpl in *; try reflexivity.
1: lia. rewrite IHi; [reflexivity | lia].
Qed.

Definition reset_nth_graph_info (n: nat) (g: Generations) : Generations := {|
    generations := reset_heapgraph_generation_info n g.(generations);
    generations__not_nil := reset_heapgraph_generation_info_not_nil n g;
|}.


Lemma generation_base__reset: forall n l,
   map generation_base (reset_heapgraph_generation_info n l) = map generation_base l.
Proof.
  intros. revert n.
  induction l; intros; simpl; destruct n; simpl; [| | | rewrite IHl]; reflexivity.
Qed.


Definition reset_nth_glabel (n: nat) (g: HeapGraph) : HeapGraph :=
  Build_LabeledGraph _ _ _ (pg_lg g) (heapgraph_block g) (elabel g)
                     (reset_nth_graph_info n (heapgraph_generations g)).

Definition pregraph_remove_vertex_and_edges
        (g: HeapGraph) (v: Addr): PreGraph Addr Field :=
fold_left pregraph_remove_edge (heapgraph_block_fields g v) (pregraph_remove_vertex g v).

Definition lgraph_remove_vertex_and_edges (g: HeapGraph) (v: Addr): HeapGraph :=
  Build_LabeledGraph _ _ _ (pregraph_remove_vertex_and_edges g v)
                     (heapgraph_block g) (elabel g) (heapgraph_generations g).

Definition remove_heapgraph_generation_ve (g: HeapGraph) (gen: nat): HeapGraph :=
  let all_nv := map (fun idx => {| addr_gen := gen; addr_block := idx |})
                    (nat_inc_list (generation_block_count (heapgraph_generation g gen))) in
  fold_left lgraph_remove_vertex_and_edges all_nv g.

Lemma remove_ve_glabel_unchanged: forall g gen,
    heapgraph_generations (remove_heapgraph_generation_ve g gen) = heapgraph_generations g.
Proof.
  intros. unfold remove_heapgraph_generation_ve.
  remember (map (fun idx : nat => {| addr_gen := gen; addr_block := idx |})
                (nat_inc_list (generation_block_count (heapgraph_generation g gen)))). clear Heql.
  revert g. induction l; intros; simpl. 1: reflexivity. rewrite IHl. reflexivity.
Qed.

Lemma remove_ve_vlabel_unchanged: forall g gen v,
    heapgraph_block (remove_heapgraph_generation_ve g gen) v = heapgraph_block g v.
Proof.
  intros. unfold remove_heapgraph_generation_ve.
  remember (map (fun idx : nat => {| addr_gen := gen; addr_block := idx |})
                (nat_inc_list (generation_block_count (heapgraph_generation g gen)))). clear Heql.
  revert g v. induction l; intros; simpl. 1: reflexivity. rewrite IHl. reflexivity.
Qed.

Lemma remove_ve_dst_unchanged: forall g gen e,
    dst (remove_heapgraph_generation_ve g gen) e = dst g e.
Proof.
  intros. unfold remove_heapgraph_generation_ve.
  remember (map (fun idx : nat => {| addr_gen := gen; addr_block := idx |})
                (nat_inc_list (generation_block_count (heapgraph_generation g gen)))). clear Heql.
  revert g e. induction l; intros; simpl. 1: reflexivity. rewrite IHl.
  clear. simpl. unfold pregraph_remove_vertex_and_edges.
  transitivity (dst (pregraph_remove_vertex g a) e). 2: reflexivity.
  remember (pregraph_remove_vertex g a) as g'. remember (heapgraph_block_fields g a) as l.
  clear a g Heqg' Heql. rename g' into g. revert g e. induction l; intros; simpl.
  1: reflexivity. rewrite IHl. reflexivity.
Qed.

Definition reset_graph (n: nat) (g: HeapGraph) : HeapGraph :=
  reset_nth_glabel n (remove_heapgraph_generation_ve g n).

Lemma graph_has_gen_reset: forall (g: HeapGraph) gen1 gen2,
    heapgraph_has_gen (reset_graph gen1 g) gen2 <-> heapgraph_has_gen g gen2.
Proof.
  intros. unfold heapgraph_has_gen. simpl. rewrite reset_heapgraph_generation_info_length.
  rewrite remove_ve_glabel_unchanged. reflexivity.
Qed.

Lemma reset_heapgraph_generation_diff: forall g i j,
    i <> j -> heapgraph_generation (reset_graph j g) i = heapgraph_generation g i.
Proof.
  intros. unfold heapgraph_generation, reset_graph. simpl.
  rewrite remove_ve_glabel_unchanged.
  apply reset_heapgraph_generation_info_diff. assumption.
Qed.

Lemma heapgraph_block_ptr_reset: forall (g: HeapGraph) v n,
    heapgraph_block_ptr (reset_graph n g) v = heapgraph_block_ptr g v.
Proof.
  intros. apply heapgraph_block_ptr__eq; unfold reset_graph; simpl.
  - intros. rewrite remove_ve_vlabel_unchanged. reflexivity.
  - rewrite remove_ve_glabel_unchanged, generation_base__reset. reflexivity.
Qed.

Lemma heapgraph_block_cells_reset: forall (g: HeapGraph) v n,
    heapgraph_block_cells_vals (reset_graph n g) v = heapgraph_block_cells_vals g v.
Proof.
  intros. apply heapgraph_block_cells_the_same; unfold reset_graph; simpl; intros.
  - apply remove_ve_dst_unchanged.
  - apply remove_ve_vlabel_unchanged.
  - rewrite remove_ve_glabel_unchanged. apply generation_base__reset.
Qed.

Lemma heapgraph_block_header__reset: forall (g: HeapGraph) v n,
    heapgraph_block_header (reset_graph n g) v = heapgraph_block_header g v.
Proof.
  intros. unfold heapgraph_block_header. simpl heapgraph_block. rewrite remove_ve_vlabel_unchanged.
  reflexivity.
Qed.


Lemma reset_space__order: forall sp, (0 <= 0 <= space_capacity sp)%Z.
Proof. intros. pose proof (space__order sp). lia. Qed.

Definition reset_space (sp: Space) : Space := {|
    space_base := space_base sp;
    space_allocated := 0;
    space_remembered := 0;
    space_capacity := space_capacity sp;
    space_sh := space_sh sp;
    space_allocated__lower_bound := ltac:(easy);
    space_remembered__lower_bound := ltac:(easy);
    space__order := reset_space__order sp;
    space__upper_bound := space__upper_bound sp;
|}.

Lemma space_base__reset_space (sp: Space):
  space_base (reset_space sp) = space_base sp.
Proof.
  easy.
Qed.

Lemma space_allocated__reset_space (sp: Space):
  space_allocated (reset_space sp) = 0.
Proof.
  easy.
Qed.

Lemma space_remembered__reset_space (sp: Space):
  space_remembered (reset_space sp) = 0.
Proof.
  easy.
Qed.

Lemma space_capacity__reset_space (sp: Space):
  space_capacity (reset_space sp) = space_capacity sp.
Proof.
  easy.
Qed.

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


Lemma reset_nth_sh_diff: forall g i j,
    i <> j -> heapgraph_generation_sh (reset_graph j g) i = heapgraph_generation_sh g i.
Proof. intros. unfold heapgraph_generation_sh. rewrite reset_heapgraph_generation_diff; auto. Qed.

Lemma reset_nth_sh: forall g i j,
    heapgraph_generation_sh (reset_graph j g) i = heapgraph_generation_sh g i.
Proof.
  intros. destruct (Nat.eq_dec i j).
  - subst. unfold reset_graph, heapgraph_generation_sh, heapgraph_generation. simpl.
    rewrite reset_heapgraph_generation_info_same, remove_ve_glabel_unchanged. reflexivity.
  - apply reset_nth_sh_diff. assumption.
Qed.

Lemma pvs_reset_unchanged: forall g gen n l,
    heapgraph_block_size_prev (reset_graph gen g) n l =
    heapgraph_block_size_prev g n l.
Proof.
  intros. unfold heapgraph_block_size_prev. apply fold_left_ext. intros.
  unfold heapgraph_block_size_accum. f_equal. unfold heapgraph_block_size. simpl.
  rewrite remove_ve_vlabel_unchanged. reflexivity.
Qed.

Lemma reset_graph_gen_size_eq: forall g i j,
    i <> j -> heapgraph_generation_size (reset_graph i g) j = heapgraph_generation_size g j.
Proof.
  intros. unfold heapgraph_generation_size.
  rewrite pvs_reset_unchanged, reset_heapgraph_generation_diff; auto.
Qed.

Lemma reset_graph_remember_size_eq: forall g i j,
    i <> j -> heapgraph_remember_size (reset_graph i g) j = heapgraph_remember_size g j.
Proof.
  intros.
  unfold heapgraph_remember_size.
  unfold heapgraph_generation at 1.
  unfold reset_graph.
  simpl.
  rewrite reset_heapgraph_generation_info_diff by congruence.
  now rewrite remove_ve_glabel_unchanged.
Qed.

Lemma reset_graph_remember_size_zero: forall g i,
    heapgraph_remember_size (reset_graph i g) i = 0.
Proof.
  intros.
  unfold heapgraph_remember_size.
  unfold heapgraph_generation at 1.
  unfold reset_graph.
  simpl.
  now rewrite reset_heapgraph_generation_info_same.
Qed.


Lemma graph_thread_info_compatible_reset: forall g t_info gen,
    graph_thread_info_compatible g t_info ->
    graph_thread_info_compatible (reset_graph gen g)
                                 (reset_nth_heap_thread_info gen t_info).
Proof.
  intros. destruct H as [? [? ?]].
  split; [|split]; [|simpl; rewrite reset_heapgraph_generation_info_length..].
  - rewrite gsc_iff by
        (simpl; rewrite remove_ve_glabel_unchanged, reset_nth_space_length,
                reset_heapgraph_generation_info_length; assumption).
    intros n ?. rewrite gsc_iff in H by assumption. rewrite graph_has_gen_reset in H2.
    specialize (H _ H2). red in H. simpl. unfold heapgraph_generation, nth_space in *. simpl.
    rewrite remove_ve_glabel_unchanged. destruct (Nat.eq_dec n gen).
    + subst gen. red in H2.
      unfold generation_space_compatible in * ; simpl in *.
      rewrite reset_heapgraph_generation_info_same.
      rewrite reset_nth_space_same by lia.
      dintuition idtac.
    + rewrite reset_heapgraph_generation_info_diff, reset_nth_space_diff by assumption.
      unfold generation_space_compatible in * ; simpl in *.
      dintuition idtac.
      now rewrite pvs_reset_unchanged.
  - rewrite remove_ve_glabel_unchanged.
    destruct (le_lt_dec (length (heap_spaces (ti_heap t_info))) gen).
    + rewrite reset_nth_space_overflow; assumption.
    + rewrite reset_nth_space_Znth by assumption. rewrite <- upd_Znth_map. simpl.
      remember (heap_spaces (ti_heap t_info)).
      assert (0 <= Z.of_nat gen < Zlength l0) by (rewrite Zlength_correct; lia).
      replace (space_base (Znth (Z.of_nat gen) l0))
        with (Znth (Z.of_nat gen) (map space_base l0)) by (rewrite Znth_map; auto).
      rewrite upd_Znth_unchanged; [|rewrite Zlength_map]; assumption.
  - rewrite remove_ve_glabel_unchanged, reset_nth_space_length. assumption.
Qed.


Lemma fta_compatible_reset: forall g t_info fi r gen,
    fun_thread_arg_compatible g t_info fi r ->
    fun_thread_arg_compatible (reset_graph gen g)
                              (reset_nth_heap_thread_info gen t_info) fi r.
Proof.
  intros. unfold fun_thread_arg_compatible in *. rewrite Znth_list_eq in *.
  destruct H. rewrite !Zlength_map in *. split. 1: assumption. intros.
  specialize (H0 _ H1). rewrite Znth_map in * by assumption. simpl. rewrite <- H0.
  destruct (Znth j r) eqn: ?; simpl. 1: reflexivity.
  apply heapgraph_block_ptr_reset.
Qed.

Lemma heapgraph_generation_has_index_reset: forall (g: HeapGraph) gen1 gen2 idx,
    heapgraph_generation_has_index (reset_graph gen1 g) gen2 idx <->
    heapgraph_generation_has_index g gen2 idx /\ gen1 <> gen2.
Proof.
  intros. unfold heapgraph_generation_has_index. unfold heapgraph_generation. simpl.
  rewrite remove_ve_glabel_unchanged. destruct (Nat.eq_dec gen1 gen2).
  - subst. rewrite reset_heapgraph_generation_info_same. simpl. intuition.
  - rewrite reset_heapgraph_generation_info_diff by auto. intuition.
Qed.

Lemma reset_graph__heapgraph_has_block (g: HeapGraph) (gen : nat) (v : Addr):
    heapgraph_has_block (reset_graph gen g) v <->
    heapgraph_has_block g v /\ gen <> addr_gen v.
Proof.
    split; intros; destruct v; simpl in *.
    + destruct H as [Hg1 Hg2]. simpl in *.
      rewrite graph_has_gen_reset in Hg1.
      rewrite heapgraph_generation_has_index_reset in Hg2.
      intuition.
      refine {|
        heapgraph_has_block__has_gen := _;
        heapgraph_has_block__has_index := _;
      |} ; intuition.
    + destruct H as [Hg Hgen] ; destruct Hg ; simpl in *.
      refine {|
        heapgraph_has_block__has_gen := _;
        heapgraph_has_block__has_index := _;
      |} ; simpl.
      - now rewrite graph_has_gen_reset.
      - now rewrite heapgraph_generation_has_index_reset.
Qed.

Lemma rgc_reset: forall g gen roots,
    roots_graph_compatible roots g ->
    roots_have_no_gen roots gen ->
    roots_graph_compatible roots (reset_graph gen g).
Proof.
  intros. red in H |-*. rewrite Forall_forall in *. intros.
  specialize (H _ H1). destruct H. split.
  - rewrite graph_has_gen_reset. assumption.
  - rewrite heapgraph_generation_has_index_reset. split. 1: assumption.
    rewrite <- filter_sum_right_In_iff in H1. apply H0 in H1. auto.
Qed.

Lemma roots_compatible_reset: forall g gen outlier roots,
    roots_compatible g outlier roots ->
    roots_have_no_gen roots gen ->
    roots_compatible (reset_graph gen g) outlier roots.
Proof. intros. destruct H. split; [|apply rgc_reset]; assumption. Qed.

Lemma outlier_compatible_reset: forall g outlier gen,
    outlier_compatible g outlier ->
    outlier_compatible (reset_graph gen g) outlier.
Proof.
  intros. unfold outlier_compatible in *. intros. simpl.
  rewrite remove_ve_vlabel_unchanged. apply H.
  rewrite reset_graph__heapgraph_has_block in H0. destruct H0. assumption.
Qed.

Lemma super_compatible_reset: forall g t_info roots f_info outlier gen,
    roots_have_no_gen roots gen ->
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible (reset_graph gen g,
                      reset_nth_heap_thread_info gen t_info, roots) f_info outlier.
Proof.
  intros. destruct H0 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply graph_thread_info_compatible_reset; assumption.
  - apply fta_compatible_reset; assumption.
  - apply roots_compatible_reset; assumption.
  - apply outlier_compatible_reset; assumption.
Qed.

Lemma tir_reset: forall t_info gen,
    thread_info_relation t_info (reset_nth_heap_thread_info gen t_info).
Proof.
  intros.
  refine {|
    thread_info_relation__ti_heap := _;
    thread_info_relation__gen_size n := _;
    thread_info_relation__space_base n := _;
  |}.
  - easy.
  - unfold gen_size, nth_space.
    unfold heap_spaces at 2.
    simpl.
    destruct (le_lt_dec (length (heap_spaces (ti_heap t_info))) gen) as [Hgen|Hgen].
    + now rewrite reset_nth_space_overflow.
    + destruct (Nat.eq_dec n gen) as [Hngen|Hngen].
      * subst.
        now rewrite reset_nth_space_same.
      * now rewrite reset_nth_space_diff.
  - unfold reset_nth_heap_thread_info, nth_space ; simpl.
    destruct (le_lt_dec (length (heap_spaces (ti_heap t_info))) gen) as [Hgen|Hgen].
    + now rewrite reset_nth_space_overflow.
    + destruct (Nat.eq_dec n gen) as [Hngen|Hngen].
      * subst.
        now rewrite reset_nth_space_same.
      * now rewrite reset_nth_space_diff.
Qed.


Lemma heapgraph_generation_is_unmarked_reset_same: forall g gen,
    heapgraph_generation_is_unmarked (reset_graph gen g) gen.
Proof.
  intros. red. intros. rewrite graph_has_gen_reset in H.
  rewrite heapgraph_generation_has_index_reset in H0. destruct H0. contradiction.
Qed.

Lemma heapgraph_generation_is_unmarked_reset_diff: forall g gen1 gen2,
    heapgraph_generation_is_unmarked g gen2 -> heapgraph_generation_is_unmarked (reset_graph gen1 g) gen2.
Proof.
  intros. unfold heapgraph_generation_is_unmarked in *. intros. rewrite graph_has_gen_reset in H0.
  rewrite heapgraph_generation_has_index_reset in H1. destruct H1. specialize (H H0 _ H1). simpl.
  rewrite remove_ve_vlabel_unchanged. assumption.
Qed.


Lemma heapgraph_block_fields_reset: forall g gen v,
    heapgraph_block_fields (reset_graph gen g) v = heapgraph_block_fields g v.
Proof.
  intros. unfold heapgraph_block_fields, heapgraph_block_cells. simpl. rewrite remove_ve_vlabel_unchanged.
  reflexivity.
Qed.

Lemma reset_graph__heapgraph_has_field (g: HeapGraph) (gen: nat) (e: Field):
    heapgraph_has_field (reset_graph gen g) e <-> heapgraph_has_field g e /\ gen <> addr_gen (field_addr e).
Proof.
    destruct e as [v idx].
    simpl.
    split ; intro H.
    + destruct H as [Hblock Hin].
      simpl in *.
      rewrite reset_graph__heapgraph_has_block in Hblock.
      rewrite heapgraph_block_fields_reset in Hin.
      split ; now try constructor.
    + destruct H as [[Hblock Hin] Hgen].
      refine {|
        heapgraph_has_field__has_block := _;
        heapgraph_has_field__in := _;
      |}.
      - now rewrite reset_graph__heapgraph_has_block.
      - now rewrite heapgraph_block_fields_reset.
Qed.

Lemma gen2gen_no_edge_reset_inv: forall g gen1 gen2 gen3,
    gen1 <> gen2 -> gen2gen_no_edge (reset_graph gen1 g) gen2 gen3 ->
    gen2gen_no_edge g gen2 gen3.
Proof.
  intros. unfold gen2gen_no_edge. intros. red in H0. simpl in H0.
  specialize (H0 vidx eidx). rewrite remove_ve_dst_unchanged in H0. apply H0.
  rewrite reset_graph__heapgraph_has_field. simpl. split; assumption.
Qed.

Lemma gen2gen_no_edge_reset: forall g gen1 gen2 gen3,
    gen2gen_no_edge g gen2 gen3 ->
    gen2gen_no_edge (reset_graph gen1 g) gen2 gen3.
Proof.
  intros. unfold gen2gen_no_edge. intros. simpl. rewrite remove_ve_dst_unchanged.
  apply H. rewrite reset_graph__heapgraph_has_field in H0. destruct H0. assumption.
Qed.

Lemma firstn_gen_clear_reset: forall g i,
    firstn_gen_clear g i -> firstn_gen_clear (reset_graph i g) (S i).
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  assert (i0 < i \/ i0 = i)%nat by lia. destruct H1.
  - rewrite reset_heapgraph_generation_diff by lia. apply H; assumption.
  - subst i0. unfold heapgraph_generation. simpl. rewrite reset_heapgraph_generation_info_same.
    simpl. reflexivity.
Qed.

Lemma reset_stct: forall g i gen1 gen2,
    i <> gen2 -> heapgraph_generation_can_copy g gen1 gen2 ->
    heapgraph_generation_can_copy (reset_graph i g) gen1 gen2.
Proof.
  intros.
  unfold heapgraph_generation_can_copy in *.
  rewrite reset_graph_gen_size_eq; auto.
  now rewrite reset_graph_remember_size_eq.
Qed.

Lemma no_dangling_dst_reset: forall g gen,
    no_dangling_dst g -> no_edge2gen g gen ->
    no_dangling_dst (reset_graph gen g).
Proof.
  intros. unfold no_dangling_dst in *. red in H0. simpl. intros.
  rewrite reset_graph__heapgraph_has_block in *. destruct H1. rewrite heapgraph_block_fields_reset in H2.
  rewrite remove_ve_dst_unchanged. split.
  - apply (H v); assumption.
  - cut (addr_gen (dst g e) <> gen). 1: intuition. unfold gen2gen_no_edge in H0.
    destruct e as [[vgen vidx] eidx]. pose proof H2. apply heapgraph_block_fields_fst in H2.
    simpl in H2. subst v. simpl in *. apply H0; intuition. split; simpl; assumption.
Qed.
