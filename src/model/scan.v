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
(* From CertiGC Require Import model.constants. *)
From CertiGC Require Import model.copy.
(* From CertiGC Require Import model.cut. *)
From CertiGC Require Import model.forward.
From CertiGC Require Import model.graph.
(* From CertiGC Require Import model.heap. *)
(* From CertiGC Require Import model.reset. *)
From CertiGC Require Import model.thread_info.
From CertiGC Require Import model.util.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.


Inductive scan_vertex_for_loop (from to: nat) (v: Addr):
  list nat -> HeapGraph -> HeapGraph -> Prop :=
| svfl_nil: forall g, scan_vertex_for_loop from to v nil g g
| svfl_cons: forall g1 g2 g3 i il,
  forward_relation
    from to O (forward_p2forward_t (inr (v, (Z.of_nat i))) nil g1) g1 g2 ->
  scan_vertex_for_loop from to v il g2 g3 ->
  scan_vertex_for_loop from to v (i :: il) g1 g3.


Inductive scan_vertex_while_loop (from to: nat):
  list nat -> HeapGraph -> HeapGraph -> Prop :=
| svwl_nil: forall g, scan_vertex_while_loop from to nil g g
| svwl_no_scan: forall g1 g2 i il,
    heapgraph_generation_has_index g1 to i -> heapgraph_block_is_no_scan g1 {| addr_gen := to; addr_block := i |} ->
    scan_vertex_while_loop from to il g1 g2 ->
    scan_vertex_while_loop from to (i :: il) g1 g2
| svwl_scan: forall g1 g2 g3 i il,
    heapgraph_generation_has_index g1 to i -> ~ heapgraph_block_is_no_scan g1 {| addr_gen := to; addr_block := i|} ->
    scan_vertex_for_loop
      from to {| addr_gen := to; addr_block := i|}
      (nat_inc_list (length (heapgraph_block g1 {| addr_gen := to; addr_block := i|}).(block_fields))) g1 g2 ->
    scan_vertex_while_loop from to il g2 g3 ->
    scan_vertex_while_loop from to (i :: il) g1 g3.

Definition do_scan_relation (from to to_index: nat) (g1 g2: HeapGraph) : Prop :=
  exists n, scan_vertex_while_loop from to (nat_seq to_index n) g1 g2 /\
            ~ heapgraph_generation_has_index g2 to (to_index + n).


Lemma svfl_graph_has_gen: forall from to v l g g',
    heapgraph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, heapgraph_has_gen g x <-> heapgraph_has_gen g' x.
Proof.
  intros from to v l. revert from to v. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (heapgraph_has_gen g2 x).
  - eapply fr_graph_has_gen; eauto.
  - apply (IHl from to v). 2: assumption. rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma svfl_heapgraph_generation_is_unmarked: forall from to v l g g',
    heapgraph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall gen, from <> gen -> heapgraph_generation_is_unmarked g gen -> heapgraph_generation_is_unmarked g' gen.
Proof.
  intros from to v l. revert from to v.
  induction l; intros; inversion H0; subst; try assumption.
  eapply (IHl from to _ g2); eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_heapgraph_generation_is_unmarked; eauto.
Qed.

Lemma svwl_heapgraph_generation_is_unmarked: forall from to l g g',
    heapgraph_has_gen g to -> scan_vertex_while_loop from to l g g' ->
    forall gen, from <> gen -> heapgraph_generation_is_unmarked g gen -> heapgraph_generation_is_unmarked g' gen.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst;
                [| apply (IHl g) | apply (IHl g2)]; try assumption.
  - rewrite <- svfl_graph_has_gen; eauto.
  - eapply svfl_heapgraph_generation_is_unmarked; eauto.
Qed.

Lemma svfl_heapgraph_block_ptr: forall from to v l g g',
    heapgraph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, closure_has_v g x -> heapgraph_block_ptr g x = heapgraph_block_ptr g' x.
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (heapgraph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H4; [rewrite <- H4 |]; assumption).
  assert (closure_has_v g2 x) by (eapply fr_closure_has_v in H4; eauto).
  eapply (IHl from to _ g2) in H7; eauto. rewrite <- H7.
  eapply fr_heapgraph_block_ptr; eauto.
Qed.

Lemma svfl_heapgraph_has_block: forall from to v l g g',
    heapgraph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, heapgraph_has_block g x -> heapgraph_has_block g' x.
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: assumption. assert (heapgraph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H4; [rewrite <- H4 |]; assumption).
  assert (heapgraph_has_block g2 x) by (eapply fr_heapgraph_has_block in H4; eauto).
  eapply (IHl from to _ g2) in H7; eauto.
Qed.

Lemma svfl_block_fields: forall from to v l g g',
    heapgraph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, heapgraph_has_block g x -> block_fields (heapgraph_block g x) = block_fields (heapgraph_block g' x).
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (heapgraph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H4; [rewrite <- H4 |]; assumption).
  assert (heapgraph_has_block g2 x) by (eapply fr_heapgraph_has_block in H4; eauto).
  eapply (IHl from to _ g2) in H7; eauto. rewrite <- H7.
  eapply fr_block_fields; eauto.
Qed.

Lemma svfl_block_mark: forall from to v l g g',
    heapgraph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, heapgraph_has_block g x -> addr_gen x <> from ->
              block_mark (heapgraph_block g x) = block_mark (heapgraph_block g' x).
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (heapgraph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H5; [rewrite <- H5 |]; assumption).
  assert (heapgraph_has_block g2 x) by (eapply fr_heapgraph_has_block in H5; eauto).
  eapply (IHl from to _ g2) in H8; eauto. rewrite <- H8.
  eapply fr_block_mark; eauto.
Qed.

Lemma svfl_add_tail: forall from to v l roots i g1 g2 g3,
    scan_vertex_for_loop from to v l g1 g2 ->
    forward_relation from to 0
                     (forward_p2forward_t (inr (v, Z.of_nat i)) roots g2) g2 g3 ->
    scan_vertex_for_loop from to v (l +:: i) g1 g3.
Proof.
  do 4 intro. revert from to v. induction l; intros; inversion H; subst.
  - simpl. rewrite forward_p2t_inr_roots in H0.
    apply svfl_cons with g3. 1: assumption. constructor.
  - simpl app. apply svfl_cons with g4. 1: assumption.
    apply IHl with roots g2; assumption.
Qed.

Lemma svwl_add_tail_no_scan: forall from to l g1 g2 i,
    scan_vertex_while_loop from to l g1 g2 -> heapgraph_generation_has_index g2 to i ->
    heapgraph_block_is_no_scan g2 {| addr_gen := to; addr_block := i |} -> scan_vertex_while_loop from to (l +:: i) g1 g2.
Proof.
  do 3 intro. revert from to. induction l; intros; inversion H; subst.
  - simpl. apply svwl_no_scan; assumption.
  - simpl app. apply svwl_no_scan; try assumption. apply IHl; assumption.
  - simpl app. apply svwl_scan with g3; try assumption. apply IHl; assumption.
Qed.

Lemma svwl_add_tail_scan: forall from to l g1 g2 g3 i,
    scan_vertex_while_loop from to l g1 g2 -> heapgraph_generation_has_index g2 to i ->
    ~ heapgraph_block_is_no_scan g2 {| addr_gen := to; addr_block := i |} ->
    scan_vertex_for_loop
      from to {| addr_gen := to; addr_block := i |}
      (nat_inc_list (length (block_fields (heapgraph_block g2 {| addr_gen := to; addr_block := i |}))))
      g2 g3 ->
    scan_vertex_while_loop from to (l +:: i) g1 g3.
Proof.
  do 3 intro. revert from to. induction l; intros; inversion H; subst.
  - simpl. apply svwl_scan with g3; try assumption. constructor.
  - simpl app. apply svwl_no_scan; try assumption. apply IHl with g2; assumption.
  - simpl app. apply svwl_scan with g4; try assumption. apply IHl with g2; assumption.
Qed.


Lemma svwl_graph_has_gen: forall from to l g1 g2,
    heapgraph_has_gen g1 to ->
    scan_vertex_while_loop from to l g1 g2 ->
    forall gen, heapgraph_has_gen g1 gen <-> heapgraph_has_gen g2 gen.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: reflexivity.
  - apply IHl; assumption.
  - transitivity (heapgraph_has_gen g3 gen).
    + eapply svfl_graph_has_gen; eauto.
    + apply IHl. 2: assumption. rewrite <- svfl_graph_has_gen; eauto.
Qed.


Lemma svfl_dst_unchanged: forall from to v l g1 g2,
    heapgraph_has_block g1 v -> block_mark (heapgraph_block g1 v) = false -> addr_gen v <> from ->
    (forall i,  In i l -> i < length (block_fields (heapgraph_block g1 v)))%nat ->
    heapgraph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall e, heapgraph_has_block g1 (field_addr e) -> (forall i, In i l -> e <> {| field_addr := v; field_index := i |}) ->
              dst g1 e = dst g2 e.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H4; subst. 1: reflexivity.
  transitivity (dst g3 e).
  - eapply fr_O_dst_unchanged_field; eauto.
    + simpl. intuition. rewrite Zlength_correct. apply inj_lt. apply H2.
      left; reflexivity.
    + apply H6. left; reflexivity.
  - apply IHl; auto.
    + eapply fr_heapgraph_has_block; eauto.
    + erewrite <- fr_block_mark; eauto.
    + intros. erewrite <- fr_block_fields; eauto. apply H2. right; assumption.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_heapgraph_has_block; eauto.
    + intros. apply H6. right; assumption.
Qed.

Lemma svwl_dst_unchanged: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    from <> to -> heapgraph_generation_is_unmarked g1 to ->
    forall e, heapgraph_has_block g1 (field_addr e) ->
              (addr_gen (field_addr e) = to -> ~ In (addr_block (field_addr e)) l) ->
              dst g1 e = dst g2 e.
Proof.
  intros. induction H0. 1: reflexivity.
  - apply IHscan_vertex_while_loop; try assumption. intros. specialize (H4 H7).
    intro. apply H4. right. assumption.
  - transitivity (dst g2 e).
    + eapply (svfl_dst_unchanged from to {| addr_gen := to; addr_block := i |}); eauto.
      * split; assumption.
      * intros. rewrite nat_inc_list_In_iff in H8. assumption.
      * intros. destruct (Nat.eq_dec (addr_gen (field_addr e)) to).
        -- specialize (H4 e0). intro. subst e. simpl in H4. apply H4. left; auto.
        -- intro. subst e. simpl in n. apply n; reflexivity.
    + apply IHscan_vertex_while_loop.
      * erewrite <- svfl_graph_has_gen; eauto.
      * eapply svfl_heapgraph_generation_is_unmarked; eauto.
      * eapply svfl_heapgraph_has_block; eauto.
      * intros. specialize (H4 H8). intro. apply H4. right; assumption.
Qed.

Lemma svfl_gen_v_num_to: forall from to v l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    (heapgraph_generation_block_count g1 to <= heapgraph_generation_block_count g2 to)%nat.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H0; subst. 1: lia.
  assert (heapgraph_has_gen g3 to) by (rewrite <- fr_graph_has_gen; eauto).
  specialize (IHl _ _ H1 H6). transitivity (heapgraph_generation_block_count g3 to); auto.
  eapply fr_O_gen_v_num_to; eauto.
Qed.

Lemma svfl_heapgraph_has_block_inv: forall from to v l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall v2,
      heapgraph_has_block g2 v2 ->
      heapgraph_has_block g1 v2 \/
      (addr_gen v2 = to /\ heapgraph_generation_block_count g1 to <= addr_block v2 < heapgraph_generation_block_count g2 to)%nat.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H0; subst. 1: left; assumption.
  assert (heapgraph_has_gen g3 to) by (rewrite <- fr_graph_has_gen; eauto).
  specialize (IHl _ _ H2 H7 _ H1). destruct IHl.
  - eapply (fr_O_heapgraph_has_block_inv from to _ g1 g3) in H4; eauto. destruct H4.
    1: left; assumption. right. clear -H1 H4. unfold new_copied_v in H4. subst.
    destruct H1. unfold heapgraph_generation_block_count. simpl in *. red in H0. lia.
  - right. destruct H3. split. 1: assumption. destruct H5. split; auto.
    eapply fr_O_gen_v_num_to in H4; [lia | assumption].
Qed.

Lemma svwl_heapgraph_has_block: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall v, heapgraph_has_block g1 v -> heapgraph_has_block g2 v.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: assumption.
  1: eapply IHl; eauto. assert (heapgraph_has_gen g3 to) by
      (rewrite <- svfl_graph_has_gen; eauto). eapply IHl; eauto.
  eapply (svfl_heapgraph_has_block _ _ _ _ g1 g3); eauto.
Qed.

Lemma svwl_gen_v_num_to: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    (heapgraph_generation_block_count g1 to <= heapgraph_generation_block_count g2 to)%nat.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: lia.
  1: apply IHl; auto. transitivity (heapgraph_generation_block_count g3 to).
  - eapply svfl_gen_v_num_to; eauto.
  - apply IHl; auto. rewrite <- svfl_graph_has_gen; eauto.
Qed.

Lemma svwl_heapgraph_has_block_inv: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall v,
      heapgraph_has_block g2 v ->
      heapgraph_has_block g1 v \/
      (addr_gen v = to /\ heapgraph_generation_block_count g1 to <= addr_block v < heapgraph_generation_block_count g2 to)%nat.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: left; assumption.
  1: eapply IHl; eauto. assert (heapgraph_has_gen g3 to) by
      (rewrite <- svfl_graph_has_gen; eauto).
  specialize (IHl _ _ H2 H9 _ H1). destruct IHl.
  - eapply svfl_heapgraph_has_block_inv in H6; eauto. destruct H6; [left|right]. 1: assumption.
    destruct H6 as [? [? ?]]. split; [|split]; [assumption..|].
    apply svwl_gen_v_num_to in H9; [lia | assumption].
  - right. destruct H3 as [? [? ?]]. split; [|split]; try assumption.
    apply svfl_gen_v_num_to in H6; [lia | assumption].
Qed.

Lemma svwl_block_fields: forall from to l g g',
    heapgraph_has_gen g to -> scan_vertex_while_loop from to l g g' ->
    forall v, heapgraph_has_block g v -> block_fields (heapgraph_block g v) = block_fields (heapgraph_block g' v).
Proof.
  do 3 intro. induction l; intros; inversion H0; subst. 1: reflexivity.
  1: eapply IHl; eauto. erewrite <- (IHl g2 g'); eauto.
  - eapply svfl_block_fields; eauto.
  - rewrite <- svfl_graph_has_gen; eauto.
  - eapply svfl_heapgraph_has_block; eauto.
Qed.

Lemma svwl_gen2gen_no_edge: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> from <> to -> heapgraph_generation_is_unmarked g1 to ->
    scan_vertex_while_loop from to l g1 g2 ->
    forall gen1 gen2, gen1 <> to -> gen2gen_no_edge g1 gen1 gen2 ->
                      gen2gen_no_edge g2 gen1 gen2.
Proof.
  intros. unfold gen2gen_no_edge in *. intros. destruct H5. simpl in H5.
  eapply svwl_heapgraph_has_block_inv in H5; eauto. simpl in H5. destruct H5 as [? | [? ?]].
  2: contradiction. erewrite <- svwl_dst_unchanged; eauto.
  apply H4. split; simpl in *. 1: assumption.
  cut (heapgraph_block_fields g1 {| addr_gen := gen1 ; addr_block := vidx |} = heapgraph_block_fields g2 {| addr_gen := gen1 ; addr_block := vidx |}).
  + intros; rewrite H7; assumption.
  + unfold heapgraph_block_fields. unfold heapgraph_block_cells. erewrite svwl_block_fields; eauto.
Qed.


Lemma svfl_dst_changed: forall from to v l g1 g2,
    heapgraph_has_block g1 v -> block_mark (heapgraph_block g1 v) = false -> addr_gen v <> from ->
    copy_compatible g1 -> no_dangling_dst g1 -> from <> to ->
    (forall i,  In i l -> i < length (block_fields (heapgraph_block g1 v)))%nat -> NoDup l ->
    heapgraph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall e i, In i l -> Znth (Z.of_nat i) (heapgraph_block_cells g2 v) = inr e ->
                addr_gen (dst g2 e) <> from.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H8; subst. 1: inversion H9.
  assert (e = {| field_addr := v ; field_index := i |}). {
    apply heapgraph_block_cells_Znth_edge in H10. 1: rewrite Nat2Z.id in H10; assumption.
    split. 1: lia. rewrite Zlength_correct. apply inj_lt.
    erewrite <- svfl_block_fields; eauto. }
  assert (heapgraph_has_block g3 v) by (eapply fr_heapgraph_has_block; eauto).
  assert (block_mark (heapgraph_block g3 v) = false) by (erewrite <- fr_block_mark; eauto).
  assert (heapgraph_has_gen g3 to) by (erewrite <- fr_graph_has_gen; eauto).
  assert (forall j : nat, In j l -> j < Datatypes.length (block_fields (heapgraph_block g3 v)))%nat. {
    intros. erewrite <- (fr_block_fields _ _ _ _ g1); eauto. apply H5.
    right; assumption. } simpl in H9. destruct H9.
  - subst a. cut (addr_gen (dst g3 e) <> from).
    + intros. cut (dst g2 e = dst g3 e). 1: intro HS; rewrite HS; assumption.
      symmetry. apply (svfl_dst_unchanged from to v l); auto.
      * subst e; simpl; assumption.
      * intros. subst e. intro. inversion H11. subst. apply NoDup_cons_2 in H6.
        contradiction.
    + eapply (fr_O_dst_changed_field from to); eauto.
      * simpl. intuition. rewrite Zlength_correct. apply inj_lt. apply H5.
        left; reflexivity.
      * unfold heapgraph_block_cells in H8 |-*. erewrite svfl_block_fields; eauto.
  - eapply (IHl g3); eauto.
    + eapply (fr_copy_compatible _ _ _ _ g1); eauto.
    + eapply (fr_O_no_dangling_dst _ _ _ g1); eauto.
      * simpl. intuition. rewrite Zlength_correct. apply inj_lt. apply H5.
        left; reflexivity.
      * simpl. constructor.
    + apply NoDup_cons_1 in H6; assumption.
Qed.

Lemma svfl_no_edge2from: forall from to v g1 g2,
    heapgraph_has_block g1 v -> block_mark (heapgraph_block g1 v) = false -> addr_gen v <> from ->
    copy_compatible g1 -> no_dangling_dst g1 -> from <> to -> heapgraph_has_gen g1 to ->
    scan_vertex_for_loop
      from to v (nat_inc_list (length (block_fields (heapgraph_block g1 v)))) g1 g2 ->
    forall e, In e (heapgraph_block_fields g2 v) -> addr_gen (dst g2 e) <> from.
Proof.
  intros. unfold heapgraph_block_fields in H7. rewrite <- filter_sum_right_In_iff in H7.
  apply In_Znth in H7. destruct H7 as [i [? ?]].
  rewrite <- (Z2Nat.id i) in H8 by lia. eapply svfl_dst_changed; eauto.
  - intros. rewrite nat_inc_list_In_iff in H9. assumption.
  - apply nat_inc_list_NoDup.
  - rewrite nat_inc_list_In_iff. rewrite heapgraph_block_cells_eq_length in H7.
    erewrite svfl_block_fields; eauto. rewrite <- ZtoNat_Zlength.
    apply Z2Nat.inj_lt; lia.
Qed.

Lemma svfl_heapgraph_generation_unchanged: forall from to v l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall gen, gen <> to -> heapgraph_generation g1 gen = heapgraph_generation g2 gen.
Proof.
  intros. induction H0; subst; try reflexivity. transitivity (heapgraph_generation g2 gen).
  - eapply fr_O_heapgraph_generation_unchanged; eauto.
  - apply IHscan_vertex_for_loop. rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma svwl_heapgraph_generation_unchanged: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen, gen <> to -> heapgraph_generation g1 gen = heapgraph_generation g2 gen.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst; try reflexivity.
  1: apply IHl; auto. transitivity (heapgraph_generation g3 gen).
  - eapply svfl_heapgraph_generation_unchanged; eauto.
  - apply IHl; auto. rewrite <- svfl_graph_has_gen; eauto.
Qed.

Lemma svwl_firstn_gen_clear: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen, (gen <= to)%nat ->
                firstn_gen_clear g1 gen -> firstn_gen_clear g2 gen.
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  erewrite <- (svwl_heapgraph_generation_unchanged from); eauto. lia.
Qed.


Lemma svfl_stcg: forall from to v l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall gen1 gen2, heapgraph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  intros. induction H0; subst; try assumption. apply IHscan_vertex_for_loop.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - eapply (fr_O_stcg from to); eauto.
Qed.

Lemma svwl_stcg: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen1 gen2, heapgraph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst; try assumption.
  1: apply (IHl g1); auto. apply (IHl g3); auto.
  - erewrite <- (svfl_graph_has_gen from to); eauto.
  - erewrite <- (svfl_graph_has_gen from to); eauto.
  - eapply (svfl_stcg from to); eauto.
Qed.


Lemma svfl_copy_compatible: forall from to v l g1 g2,
    from <> to -> heapgraph_has_gen g1 to ->
    scan_vertex_for_loop from to v l g1 g2 ->
    copy_compatible g1 -> copy_compatible g2.
Proof.
  do 4 intro. induction l; intros; inversion H1; subst. 1: assumption.
  cut (copy_compatible g3).
  - intros. apply (IHl g3); auto. erewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
Qed.

Lemma svfl_no_dangling_dst: forall from to v l g1 g2,
    heapgraph_has_block g1 v -> block_mark (heapgraph_block g1 v) = false -> addr_gen v <> from ->
    copy_compatible g1 -> heapgraph_has_gen g1 to -> from <> to ->
    scan_vertex_for_loop from to v l g1 g2 ->
    (forall i,  In i l -> i < length (block_fields (heapgraph_block g1 v)))%nat ->
    no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  do 4 intro. induction l; intros; inversion H5; subst. 1: assumption.
  cut (no_dangling_dst g3).
  - intros. apply (IHl g3); auto.
    + eapply fr_heapgraph_has_block; eauto.
    + erewrite <- fr_block_mark; eauto.
    + eapply (fr_copy_compatible O from to); eauto.
    + erewrite <- fr_graph_has_gen; eauto.
    + intros. erewrite <- fr_block_fields; eauto. apply H6. right; assumption.
  - eapply fr_O_no_dangling_dst; eauto.
    + simpl. intuition. rewrite Zlength_correct. apply inj_lt.
      apply H6. left; reflexivity.
    + simpl. constructor.
Qed.

Lemma svwl_no_edge2from: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    heapgraph_generation_is_unmarked g1 to -> copy_compatible g1 -> no_dangling_dst g1 ->
    from <> to -> NoDup l ->
    forall e i, In i l -> In e (heapgraph_block_fields g2 {| addr_gen := to; addr_block := i |}) ->
                addr_gen (dst g2 e) <> from.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst. 1: inversion H6.
  - simpl in H6. destruct H6. 2: apply NoDup_cons_1 in H5; eapply IHl; eauto. subst a.
    assert (In e (heapgraph_block_fields g1 {| addr_gen := to; addr_block := i |})). {
      unfold heapgraph_block_fields, heapgraph_block_cells in H7 |-*.
      erewrite svwl_block_fields; eauto. split; simpl; assumption. }
    rewrite heapgraph_block_is_no_scan__no_fields in H6. 2: assumption. inversion H6.
  - simpl in H6.
    assert (heapgraph_has_gen g3 to) by (erewrite <- svfl_graph_has_gen; eauto).
    assert (heapgraph_generation_is_unmarked g3 to) by (eapply (svfl_heapgraph_generation_is_unmarked _ _ _ _ g1); eauto).
    destruct H6.
    + subst a. cut (addr_gen (dst g3 e) <> from).
      * intros. cut (dst g3 e = dst g2 e). 1: intros HS; rewrite <- HS; assumption.
        eapply svwl_dst_unchanged; eauto.
        -- erewrite heapgraph_block_fields_fst; eauto. eapply (svfl_heapgraph_has_block _ _ _ _ g1); eauto.
           split; simpl; assumption.
        -- intros. erewrite heapgraph_block_fields_fst; eauto. simpl.
           apply NoDup_cons_2 in H5. assumption.
      * assert (heapgraph_has_block g1 {| addr_gen := to; addr_block := i |}) by (split; simpl; assumption).
        eapply svfl_no_edge2from; eauto. unfold heapgraph_block_fields, heapgraph_block_cells in H7 |-*.
        erewrite svwl_block_fields; eauto. eapply (svfl_heapgraph_has_block _ _ _ _ g1); eauto.
    + eapply (IHl g3); eauto.
      * eapply (svfl_copy_compatible _ _ _ _ g1); eauto.
      * eapply (svfl_no_dangling_dst from to); eauto.
        -- split; simpl; assumption.
        -- intros. rewrite nat_inc_list_In_iff in H13. assumption.
      * apply NoDup_cons_1 in H5. assumption.
Qed.

Lemma svwl_no_dangling_dst: forall from to l g1 g2,
    heapgraph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    heapgraph_generation_is_unmarked g1 to -> copy_compatible g1 -> from <> to ->
    no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst;
                [assumption | eapply IHl; eauto|]. cut (no_dangling_dst g3).
  - intros. apply (IHl g3); auto.
    + erewrite <- svfl_graph_has_gen; eauto.
    + eapply svfl_heapgraph_generation_is_unmarked; eauto.
    + eapply svfl_copy_compatible; eauto.
  - eapply (svfl_no_dangling_dst from to _ _ g1); eauto.
    + split; simpl; assumption.
    + intros. rewrite nat_inc_list_In_iff in H5. assumption.
Qed.

Lemma frr_dsr_no_edge2gen: forall from to f_info roots roots' g g1 g2,
    heapgraph_has_gen g to -> from <> to -> heapgraph_generation_is_unmarked g to ->
    copy_compatible g -> no_dangling_dst g ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    roots_graph_compatible roots g ->
    forward_roots_relation from to f_info roots g roots' g1 ->
    do_scan_relation from to (generation_block_count (heapgraph_generation g to)) g1 g2 ->
    no_edge2gen g from -> no_edge2gen g2 from.
Proof.
  intros. unfold no_edge2gen in *. intros. specialize (H8 _ H9).
  destruct (Nat.eq_dec another to).
  - subst. unfold gen2gen_no_edge in *. intros.
    destruct H10. simpl fst in *. destruct H7 as [m [? ?]].
    assert (heapgraph_has_gen g1 to) by (erewrite <- frr_graph_has_gen; eauto).
    assert (heapgraph_has_block g {| addr_gen := to ; addr_block := vidx |} \/ heapgraph_generation_block_count g to <= vidx < heapgraph_generation_block_count g2 to)%nat. {
      eapply (svwl_heapgraph_has_block_inv from to _ g1 g2) in H10; eauto. simpl in H10.
      destruct H10.
      - eapply (frr_heapgraph_has_block_inv from _ _ _ g) in H10; eauto.
        simpl in H10. destruct H10. 1: left; assumption.
        right. destruct H10 as [_ [? ?]]. split; auto.
        apply svwl_gen_v_num_to in H7; [lia | assumption].
      - right. destruct H10 as [_ [? ?]]. split; auto.
        apply frr_gen_v_num_to in H6; [lia | assumption]. } destruct H14.
    + assert (heapgraph_has_block g1 {| addr_gen := to ; addr_block := vidx |}) by
          (eapply (frr_heapgraph_has_block from to _ _ g); eauto).
      assert (heapgraph_block_fields g {| addr_gen := to ; addr_block := vidx |} = heapgraph_block_fields g2 {| addr_gen := to ; addr_block := vidx |}). {
        transitivity (heapgraph_block_fields g1 {| addr_gen := to ; addr_block := vidx |}); unfold heapgraph_block_fields, heapgraph_block_cells.
        - erewrite frr_block_fields; eauto.
        - erewrite svwl_block_fields; eauto. } simpl in H11. rewrite <- H16 in H11.
      assert (graph_has_e g {| field_addr := {| addr_gen := to ; addr_block := vidx |} ; field_index := eidx |}) by (split; simpl; assumption).
      specialize (H8 _ _ H17).
      erewrite (frr_dst_unchanged _ _ _ _ _ _ g1) in H8; eauto.
      erewrite (svwl_dst_unchanged) in H8; eauto; simpl.
      * eapply (frr_heapgraph_generation_is_unmarked _ _ _ _ g); eauto.
      * repeat intro. rewrite nat_seq_In_iff in H19. destruct H19 as [? _].
        destruct H14. simpl in H20. red in H20. lia.
    + eapply svwl_no_edge2from; eauto.
      * eapply (frr_heapgraph_generation_is_unmarked _ _ _ _ g); eauto.
      * eapply (frr_copy_compatible from to _ _ g); eauto.
      * eapply (frr_no_dangling_dst _ _ _ _ g); eauto.
      * apply nat_seq_NoDup.
      * rewrite nat_seq_In_iff. unfold heapgraph_generation_has_index in H12.
        unfold heapgraph_generation_block_count in H14. lia.
  - eapply (frr_gen2gen_no_edge _ _ _ _ g _ g1) in H8; eauto.
    destruct H7 as [m [? ?]]. eapply (svwl_gen2gen_no_edge from to _ g1 g2); eauto.
    + erewrite <- frr_graph_has_gen; eauto.
    + eapply frr_heapgraph_generation_is_unmarked; eauto.
Qed.
