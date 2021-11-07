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
From CertiGC Require Import model.forward.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.reset.
From CertiGC Require Import model.scan.
From CertiGC Require Import model.thread_info.


Definition do_generation_condition g t_info roots f_info from to: Prop :=
  enough_space_to_have_g g t_info from to /\ graph_has_gen g from /\
  graph_has_gen g to /\ copy_compatible g /\ no_dangling_dst g /\
  0 < gen_size t_info to /\ gen_unmarked g to /\ roots_fi_compatible roots f_info.

Lemma dgc_imply_fc: forall g t_info roots f_info from to,
    do_generation_condition g t_info roots f_info from to ->
    forward_condition g t_info from to /\ 0 < gen_size t_info to /\
    gen_unmarked g to /\ roots_fi_compatible roots f_info.
Proof.
  intros. destruct H. do 2 (split; [|intuition]). clear H0. red in H |-* .
  transitivity (graph_gen_size g from); [apply unmarked_gen_size_le | assumption].
Qed.

Definition do_generation_relation (from to: nat) (f_info: fun_info)
           (roots roots': roots_t) (g g': HeapGraph): Prop := exists g1 g2,
    forward_roots_relation from to f_info roots g roots' g1 /\
    do_scan_relation from to (generation_block_count (nth_gen g to)) g1 g2 /\
    g' = reset_graph from g2.

Lemma do_gen_graph_has_gen: forall from to f_info roots roots' g g',
    graph_has_gen g to ->
    do_generation_relation from to f_info roots roots' g g' ->
    forall gen, graph_has_gen g gen <-> graph_has_gen g' gen.
Proof.
  intros. destruct H0 as [g1 [g2 [? [? ?]]]]. transitivity (graph_has_gen g1 gen).
  - eapply frr_graph_has_gen; eauto.
  - transitivity (graph_has_gen g2 gen).
    + destruct H1 as [n [? ?]]. eapply svwl_graph_has_gen; eauto.
      rewrite <- frr_graph_has_gen; eauto.
    + subst g'. rewrite graph_has_gen_reset. reflexivity.
Qed.

Lemma do_gen_graph_unmarked: forall from to f_info roots roots' g g',
    graph_has_gen g to ->
    do_generation_relation from to f_info roots roots' g g' ->
    graph_unmarked g -> graph_unmarked g'.
Proof.
  intros. destruct H0 as [g1 [g2 [? [? ?]]]]. rewrite graph_gen_unmarked_iff in H1.
  assert (forall gen, from <> gen -> gen_unmarked g1 gen) by
      (intros; eapply frr_gen_unmarked; eauto).
  assert (forall gen, from <> gen -> gen_unmarked g2 gen). {
    intros. destruct H2 as [n [? ?]]. eapply (svwl_gen_unmarked _ _ _ g1 g2); eauto.
    rewrite <- frr_graph_has_gen; eauto. } subst g'.
  rewrite graph_gen_unmarked_iff. intros. destruct (Nat.eq_dec from gen).
  - subst. apply gen_unmarked_reset_same.
  - apply gen_unmarked_reset_diff. apply H5. assumption.
Qed.

Lemma do_gen_no_dangling_dst: forall g1 g2 roots1 roots2 f_info from to,
  graph_has_gen g1 to -> copy_compatible g1 -> gen_unmarked g1 to ->
  Zlength roots1 = Zlength (live_roots_indices f_info) -> from <> to ->
  roots_graph_compatible roots1 g1 -> firstn_gen_clear g1 from ->
  no_backward_edge g1 ->
  do_generation_relation from to f_info roots1 roots2 g1 g2 ->
  no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  intros. destruct H7 as [g3 [g4 [? [? ?]]]].
  assert (no_dangling_dst g3) by (eapply (frr_no_dangling_dst from); eauto).
  assert (no_dangling_dst g4). {
    destruct H9 as [n [? ?]]. eapply (svwl_no_dangling_dst _ _ _ g3); eauto.
    - rewrite <- frr_graph_has_gen; eauto.
    - eapply frr_gen_unmarked; eauto.
    - eapply frr_copy_compatible; eauto. }
  subst g2. apply no_dangling_dst_reset; auto.
  eapply frr_dsr_no_edge2gen; eauto. apply fgc_nbe_no_edge2gen; auto.
Qed.

Lemma do_gen_firstn_gen_clear: forall g1 g2 roots1 roots2 f_info i,
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    graph_has_gen g1 (S i) -> firstn_gen_clear g1 i -> firstn_gen_clear g2 (S i).
Proof.
  intros. destruct H as [g3 [g4 [? [? ?]]]].
  eapply frr_firstn_gen_clear in H1; eauto. destruct H2 as [n [? ?]].
  eapply svwl_firstn_gen_clear in H1; eauto. 2: erewrite <- frr_graph_has_gen; eauto.
  subst g2. apply firstn_gen_clear_reset. assumption.
Qed.

Lemma do_gen_no_backward_edge: forall g1 g2 roots1 roots2 f_info i,
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    no_dangling_dst g2 -> graph_has_gen g1 (S i) -> gen_unmarked g1 (S i) ->
    firstn_gen_clear g1 i -> no_backward_edge g1 -> no_backward_edge g2.
Proof.
  intros. unfold no_backward_edge in *. intros. destruct (Nat.eq_dec gen1 (S i)).
  - red. intros. destruct H6. simpl in *. eapply do_gen_firstn_gen_clear in H3; eauto.
    subst. specialize (H0 _ H6 _ H7). destruct H0. red in H8. intro. rewrite H9 in H8.
    red in H3. assert (gen2 < S i)%nat by lia. specialize (H3 _ H10). red in H3.
    rewrite H3 in H8. lia.
  - destruct H as [g3 [g4 [? [? ?]]]]. subst g2. apply gen2gen_no_edge_reset.
    assert (gen2gen_no_edge g3 gen1 gen2) by (eapply frr_gen2gen_no_edge; eauto).
    destruct H6 as [m [? ?]]. eapply (svwl_gen2gen_no_edge i _ _ g3); eauto.
    + rewrite <- frr_graph_has_gen; eauto.
    + eapply frr_gen_unmarked; eauto.
Qed.