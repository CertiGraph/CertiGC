From Coq Require Import Logic.FinFun.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.compatible.
From CertiGC Require Import model.constants.
From CertiGC Require Import model.do_generation.
From CertiGC Require Import model.forward.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.heap.
From CertiGC Require Import model.reset.
From CertiGC Require Import model.scan.
From CertiGC Require Import model.thread_info.
From CertiGC Require Import model.util.


Inductive garbage_collect_loop (f_info : fun_info)
  : list nat -> roots_t -> HeapGraph -> roots_t -> HeapGraph -> Prop :=
  gcl_nil: forall g roots, garbage_collect_loop f_info nil roots g roots g
| gcl_cons: forall (g1 g2 g3 g4: HeapGraph) (i: nat) (il: list nat)
                   (roots1 roots2 roots3: roots_t),
    new_gen_relation (S i) g1 g2 ->
    do_generation_relation i (S i) f_info roots1 roots2 g2 g3 ->
    garbage_collect_loop f_info il roots2 g3 roots3 g4 ->
    garbage_collect_loop f_info (i :: il) roots1 g1 roots3 g4.

Definition garbage_collect_relation (f_info: fun_info)
           (roots1 roots2: roots_t) (g1 g2: HeapGraph): Prop :=
  exists n, garbage_collect_loop f_info (nat_inc_list (S n)) roots1 g1 roots2 g2 /\
            safe_to_copy_gen g2 n (S n).

Definition garbage_collect_condition (g: HeapGraph) (t_info : thread_info)
           (roots : roots_t) (f_info : fun_info) : Prop :=
  graph_unmarked g /\ no_backward_edge g /\ no_dangling_dst g /\
  roots_fi_compatible roots f_info /\ ti_size_spec t_info.

Local Open Scope Z_scope.

Lemma gcc_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES) roots fi,
    generation_block_count gi = O -> space_capacity sp = nth_gen_size (Z.to_nat i) ->
    garbage_collect_condition g ti roots fi ->
    garbage_collect_condition (lgraph_add_new_gen g gi)
                              (ti_add_new_space ti sp i Hs) roots fi.
Proof.
  intros. destruct H1 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply graph_unmarked_add; assumption.
  - apply no_backward_edge_add; assumption.
  - apply no_dangling_dst_add; assumption.
  - assumption.
  - apply ti_size_spec_add; assumption.
Qed.


Lemma gc_cond_implies_do_gen_cons: forall g t_info roots f_info i,
    safe_to_copy_to_except g i ->
    graph_has_gen g (S i) ->
    graph_thread_info_compatible g t_info ->
    garbage_collect_condition g t_info roots f_info ->
    do_generation_condition g t_info roots f_info i (S i).
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]].
  assert (graph_has_gen g i) by (unfold graph_has_gen in H0 |-*; lia).
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; auto.
  - unfold safe_to_copy_to_except, safe_to_copy_gen in H. red.
    unfold rest_gen_size. specialize (H (S i)). simpl in H.
    destruct (gt_gs_compatible _ _ H1 _ H0) as [_ [_ ?]].
    destruct (gt_gs_compatible _ _ H1 _ H7) as [_ [_ ?]].
    fold (graph_gen_size g (S i)) in H8. fold (graph_gen_size g i) in H9.
    rewrite <- H8. fold (gen_size t_info (S i)).
    destruct (space__order (nth_space t_info i)) as [_ ?].
    fold (gen_size t_info i) in H10. rewrite <- H9 in H10.
    transitivity (gen_size t_info i). 1: assumption.
    rewrite (ti_size_gen _ _ _ H1 H7 H6), (ti_size_gen _ _ _ H1 H0 H6).
    apply H; [lia.. | assumption].
  - apply graph_unmarked_copy_compatible; assumption.
  - rewrite (ti_size_gen _ _ _ H1 H0 H6). apply ngs_0_lt.
  - rewrite graph_gen_unmarked_iff in H2. apply H2.
Qed.

Lemma do_gen_gcc: forall g1 t_info1 roots1 g2 t_info2 roots2 f_info i out,
    super_compatible (g1, t_info1, roots1) f_info out ->
    firstn_gen_clear g1 i -> graph_has_gen g1 (S i) ->
    thread_info_relation t_info1 t_info2 ->
    garbage_collect_condition g1 t_info1 roots1 f_info ->
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    garbage_collect_condition g2 t_info2 roots2 f_info.
Proof.
  intros. destruct H3 as [? [? [? [? ?]]]].
  assert (gen_unmarked g1 (S i)) by (rewrite graph_gen_unmarked_iff in H3; apply H3).
  assert (no_dangling_dst g2). {
    eapply do_gen_no_dangling_dst; eauto.
    - apply graph_unmarked_copy_compatible; assumption.
    - apply (proj1 H7).
    - destruct H as [_ [_ [[_ ?] _]]]. assumption. }
  split; [|split; [|split; [|split]]]; auto.
  - eapply do_gen_graph_unmarked; eauto.
  - eapply do_gen_no_backward_edge; eauto.
  - destruct H4 as [g3 [g4 [? _]]]. eapply frr_roots_fi_compatible; eauto.
  - eapply ti_relation_size_spec; eauto.
Qed.

Lemma do_gen_stcte: forall g1 roots1 g2 roots2 f_info i,
    safe_to_copy_to_except g1 i -> graph_has_gen g1 (S i) ->
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    safe_to_copy_to_except g2 (S i).
Proof.
  intros. unfold safe_to_copy_to_except in *. intros.
  destruct H1 as [g3 [g4 [? [? ?]]]]. destruct (Nat.eq_dec n i).
  - subst. red. unfold graph_gen_size, nth_gen. simpl.
    rewrite reset_nth_gen_info_same. simpl. unfold previous_vertices_size.
    simpl. destruct i. 1: contradiction. simpl. rewrite Z.sub_0_r.
    apply nth_gen_size_le_S.
  - subst g2. apply reset_stct; auto. destruct H5 as [m [? ?]].
    rewrite graph_has_gen_reset in H4.
    assert (graph_has_gen g3 (S i)) by (erewrite <- frr_graph_has_gen; eauto).
    assert (graph_has_gen g3 n) by (erewrite svwl_graph_has_gen; eauto).
    eapply (svwl_stcg i (S i) _ g3); eauto.
    assert (graph_has_gen g1 n) by (erewrite frr_graph_has_gen; eauto).
    eapply (frr_stcg i (S i) _ _ g1); eauto.
Qed.

Lemma gcl_add_tail: forall l g1 roots1 g2 roots2 g3 roots3 g4 f_info i,
    garbage_collect_loop f_info l roots1 g1 roots2 g2 ->
    new_gen_relation (S i) g2 g3 ->
    do_generation_relation i (S i) f_info roots2 roots3 g3 g4 ->
    garbage_collect_loop f_info (l +:: i) roots1 g1 roots3 g4.
Proof.
  induction l; intros.
  - simpl. inversion H. subst. eapply gcl_cons; eauto. constructor.
  - inversion H. subst. clear H. simpl app. eapply gcl_cons; eauto.
Qed.