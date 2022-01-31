From Coq Require Import Logic.FinFun.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.compatible.compatible.
From CertiGC Require Import model.heap.heap.
From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.block.block_rep.
From CertiGC Require Import model.heapgraph.block.cell.
From CertiGC Require Import model.heapgraph.block.field.
From CertiGC Require Import model.heapgraph.can_copy.
From CertiGC Require Import model.heapgraph.field_pairs.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.has_block.
From CertiGC Require Import model.heapgraph.has_field.
From CertiGC Require Import model.heapgraph.mark.
From CertiGC Require Import model.heapgraph.predicates.
From CertiGC Require Import model.heapgraph.remset.remset.
From CertiGC Require Import model.heapgraph.roots.
From CertiGC Require Import model.op.forward.
From CertiGC Require Import model.op.reset.
From CertiGC Require Import model.op.scan.
From CertiGC Require Import model.thread_info.thread_info.


Definition do_generation_condition g t_info roots f_info from to: Prop :=
  enough_space_to_have_g g t_info from to /\ heapgraph_has_gen g from /\
  heapgraph_has_gen g to /\ copy_compatible g /\ no_dangling_dst g /\
  0 < gen_size t_info to - space_remembered (nth_space t_info to) /\
  heapgraph_generation_is_unmarked g to /\ roots_fi_compatible roots f_info.

Lemma dgc_imply_fc: forall g t_info roots f_info from to,
    do_generation_condition g t_info roots f_info from to ->
    forward_condition g t_info from to /\ 0 < gen_size t_info to - space_remembered (nth_space t_info to) /\
    heapgraph_generation_is_unmarked g to /\ roots_fi_compatible roots f_info.
Proof.
  intros.
  destruct H.
  refine (conj (conj _ (conj _ (conj _ (conj _ _)))) (conj _ (conj _ _))) ; intuition idtac.
  red in H |-* .
  pose proof (unmarked_gen_size_le g from).
  lia.
Qed.

Definition do_generation_relation (from to: nat) (f_info: fun_info)
           (roots roots': roots_t) (g g': HeapGraph): Prop := exists g1 g2,
    forward_roots_relation from to f_info roots g roots' g1 /\
    do_scan_relation from to (generation_block_count (heapgraph_generation g to)) g1 g2 /\
    g' = reset_graph from g2.

Lemma do_gen_graph_has_gen: forall from to f_info roots roots' g g',
    heapgraph_has_gen g to ->
    do_generation_relation from to f_info roots roots' g g' ->
    forall gen, heapgraph_has_gen g gen <-> heapgraph_has_gen g' gen.
Proof.
  intros. destruct H0 as [g1 [g2 [? [? ?]]]]. transitivity (heapgraph_has_gen g1 gen).
  - eapply frr_graph_has_gen; eauto.
  - transitivity (heapgraph_has_gen g2 gen).
    + destruct H1 as [n [? ?]]. eapply svwl_graph_has_gen; eauto.
      rewrite <- frr_graph_has_gen; eauto.
    + subst g'. rewrite graph_has_gen_reset. reflexivity.
Qed.

Lemma do_gen_graph_unmarked: forall from to f_info roots roots' g g',
    heapgraph_has_gen g to ->
    do_generation_relation from to f_info roots roots' g g' ->
    graph_unmarked g -> graph_unmarked g'.
Proof.
  intros. destruct H0 as [g1 [g2 [? [? ?]]]]. rewrite graph_heapgraph_generation_is_unmarked_iff in H1.
  assert (forall gen, from <> gen -> heapgraph_generation_is_unmarked g1 gen) by
      (intros; eapply frr_heapgraph_generation_is_unmarked; eauto).
  assert (forall gen, from <> gen -> heapgraph_generation_is_unmarked g2 gen). {
    intros. destruct H2 as [n [? ?]]. eapply (svwl_heapgraph_generation_is_unmarked _ _ _ g1 g2); eauto.
    rewrite <- frr_graph_has_gen; eauto. } subst g'.
  rewrite graph_heapgraph_generation_is_unmarked_iff. intros. destruct (Nat.eq_dec from gen).
  - subst. apply heapgraph_generation_is_unmarked_reset_same.
  - apply heapgraph_generation_is_unmarked_reset_diff. apply H5. assumption.
Qed.

Lemma do_gen_no_dangling_dst: forall g1 g2 roots1 roots2 f_info from to,
  heapgraph_has_gen g1 to -> copy_compatible g1 -> heapgraph_generation_is_unmarked g1 to ->
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
    - eapply frr_heapgraph_generation_is_unmarked; eauto.
    - eapply frr_copy_compatible; eauto. }
  subst g2. apply no_dangling_dst_reset; auto.
  eapply frr_dsr_no_edge2gen; eauto. apply fgc_nbe_no_edge2gen; auto.
Qed.

Lemma do_gen_firstn_gen_clear: forall g1 g2 roots1 roots2 f_info i,
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    heapgraph_has_gen g1 (S i) -> firstn_gen_clear g1 i -> firstn_gen_clear g2 (S i).
Proof.
  intros. destruct H as [g3 [g4 [? [? ?]]]].
  eapply frr_firstn_gen_clear in H1; eauto. destruct H2 as [n [? ?]].
  eapply svwl_firstn_gen_clear in H1; eauto. 2: erewrite <- frr_graph_has_gen; eauto.
  subst g2. apply firstn_gen_clear_reset. assumption.
Qed.

Lemma do_gen_no_backward_edge: forall g1 g2 roots1 roots2 f_info i,
    do_generation_relation i (S i) f_info roots1 roots2 g1 g2 ->
    no_dangling_dst g2 -> heapgraph_has_gen g1 (S i) -> heapgraph_generation_is_unmarked g1 (S i) ->
    firstn_gen_clear g1 i -> no_backward_edge g1 -> no_backward_edge g2.
Proof.
  intros. unfold no_backward_edge in *. intros. destruct (Nat.eq_dec gen1 (S i)).
  - red. intros.
    eapply do_gen_firstn_gen_clear in H3; eauto.
    subst.
    specialize (H0 _ (heapgraph_has_field__has_block H6) _ (heapgraph_has_field__in H6)).
    pose proof (heapgraph_has_block__has_index H0) as Hindex.
    red in Hindex. intro Egen2. rewrite Egen2 in Hindex.
    red in H3. assert (gen2 < S i)%nat as Hgen2 by lia. specialize (H3 _ Hgen2). red in H3.
    rewrite H3 in Hindex. lia.
  - destruct H as [g3 [g4 [? [? ?]]]]. subst g2. apply gen2gen_no_edge_reset.
    assert (gen2gen_no_edge g3 gen1 gen2) by (eapply frr_gen2gen_no_edge; eauto).
    destruct H6 as [m [? ?]]. eapply (svwl_gen2gen_no_edge i _ _ g3); eauto.
    + rewrite <- frr_graph_has_gen; eauto.
    + eapply frr_heapgraph_generation_is_unmarked; eauto.
Qed.