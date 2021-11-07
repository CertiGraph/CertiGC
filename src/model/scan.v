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
    gen_has_index g1 to i -> no_scan g1 {| addr_gen := to; addr_block := i |} ->
    scan_vertex_while_loop from to il g1 g2 ->
    scan_vertex_while_loop from to (i :: il) g1 g2
| svwl_scan: forall g1 g2 g3 i il,
    gen_has_index g1 to i -> ~ no_scan g1 {| addr_gen := to; addr_block := i|} ->
    scan_vertex_for_loop
      from to {| addr_gen := to; addr_block := i|}
      (nat_inc_list (length (vlabel g1 {| addr_gen := to; addr_block := i|}).(block_fields))) g1 g2 ->
    scan_vertex_while_loop from to il g2 g3 ->
    scan_vertex_while_loop from to (i :: il) g1 g3.

Definition do_scan_relation (from to to_index: nat) (g1 g2: HeapGraph) : Prop :=
  exists n, scan_vertex_while_loop from to (nat_seq to_index n) g1 g2 /\
            ~ gen_has_index g2 to (to_index + n).


Lemma svfl_graph_has_gen: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, graph_has_gen g x <-> graph_has_gen g' x.
Proof.
  intros from to v l. revert from to v. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (graph_has_gen g2 x).
  - eapply fr_graph_has_gen; eauto.
  - apply (IHl from to v). 2: assumption. rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma svfl_gen_unmarked: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall gen, from <> gen -> gen_unmarked g gen -> gen_unmarked g' gen.
Proof.
  intros from to v l. revert from to v.
  induction l; intros; inversion H0; subst; try assumption.
  eapply (IHl from to _ g2); eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_gen_unmarked; eauto.
Qed.

Lemma svwl_gen_unmarked: forall from to l g g',
    graph_has_gen g to -> scan_vertex_while_loop from to l g g' ->
    forall gen, from <> gen -> gen_unmarked g gen -> gen_unmarked g' gen.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst;
                [| apply (IHl g) | apply (IHl g2)]; try assumption.
  - rewrite <- svfl_graph_has_gen; eauto.
  - eapply svfl_gen_unmarked; eauto.
Qed.

Lemma svfl_vertex_address: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, closure_has_v g x -> vertex_address g x = vertex_address g' x.
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (graph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H4; [rewrite <- H4 |]; assumption).
  assert (closure_has_v g2 x) by (eapply fr_closure_has_v in H4; eauto).
  eapply (IHl from to _ g2) in H7; eauto. rewrite <- H7.
  eapply fr_vertex_address; eauto.
Qed.

Lemma svfl_graph_has_v: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, graph_has_v g x -> graph_has_v g' x.
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: assumption. assert (graph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H4; [rewrite <- H4 |]; assumption).
  assert (graph_has_v g2 x) by (eapply fr_graph_has_v in H4; eauto).
  eapply (IHl from to _ g2) in H7; eauto.
Qed.

Lemma svfl_block_fields: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, graph_has_v g x -> block_fields (vlabel g x) = block_fields (vlabel g' x).
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (graph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H4; [rewrite <- H4 |]; assumption).
  assert (graph_has_v g2 x) by (eapply fr_graph_has_v in H4; eauto).
  eapply (IHl from to _ g2) in H7; eauto. rewrite <- H7.
  eapply fr_block_fields; eauto.
Qed.

Lemma svfl_block_mark: forall from to v l g g',
    graph_has_gen g to -> scan_vertex_for_loop from to v l g g' ->
    forall x, graph_has_v g x -> addr_gen x <> from ->
              block_mark (vlabel g x) = block_mark (vlabel g' x).
Proof.
  do 4 intro. revert from to v. induction l; intros; simpl; inversion H0; subst.
  1: reflexivity. assert (graph_has_gen g2 to) by
      (eapply fr_graph_has_gen in H5; [rewrite <- H5 |]; assumption).
  assert (graph_has_v g2 x) by (eapply fr_graph_has_v in H5; eauto).
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
    scan_vertex_while_loop from to l g1 g2 -> gen_has_index g2 to i ->
    no_scan g2 {| addr_gen := to; addr_block := i |} -> scan_vertex_while_loop from to (l +:: i) g1 g2.
Proof.
  do 3 intro. revert from to. induction l; intros; inversion H; subst.
  - simpl. apply svwl_no_scan; assumption.
  - simpl app. apply svwl_no_scan; try assumption. apply IHl; assumption.
  - simpl app. apply svwl_scan with g3; try assumption. apply IHl; assumption.
Qed.

Lemma svwl_add_tail_scan: forall from to l g1 g2 g3 i,
    scan_vertex_while_loop from to l g1 g2 -> gen_has_index g2 to i ->
    ~ no_scan g2 {| addr_gen := to; addr_block := i |} ->
    scan_vertex_for_loop
      from to {| addr_gen := to; addr_block := i |}
      (nat_inc_list (length (block_fields (vlabel g2 {| addr_gen := to; addr_block := i |}))))
      g2 g3 ->
    scan_vertex_while_loop from to (l +:: i) g1 g3.
Proof.
  do 3 intro. revert from to. induction l; intros; inversion H; subst.
  - simpl. apply svwl_scan with g3; try assumption. constructor.
  - simpl app. apply svwl_no_scan; try assumption. apply IHl with g2; assumption.
  - simpl app. apply svwl_scan with g4; try assumption. apply IHl with g2; assumption.
Qed.


Lemma svwl_graph_has_gen: forall from to l g1 g2,
    graph_has_gen g1 to ->
    scan_vertex_while_loop from to l g1 g2 ->
    forall gen, graph_has_gen g1 gen <-> graph_has_gen g2 gen.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: reflexivity.
  - apply IHl; assumption.
  - transitivity (graph_has_gen g3 gen).
    + eapply svfl_graph_has_gen; eauto.
    + apply IHl. 2: assumption. rewrite <- svfl_graph_has_gen; eauto.
Qed.


Lemma svfl_dst_unchanged: forall from to v l g1 g2,
    graph_has_v g1 v -> block_mark (vlabel g1 v) = false -> addr_gen v <> from ->
    (forall i,  In i l -> i < length (block_fields (vlabel g1 v)))%nat ->
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall e, graph_has_v g1 (field_addr e) -> (forall i, In i l -> e <> {| field_addr := v; field_index := i |}) ->
              dst g1 e = dst g2 e.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H4; subst. 1: reflexivity.
  transitivity (dst g3 e).
  - eapply fr_O_dst_unchanged_field; eauto.
    + simpl. intuition. rewrite Zlength_correct. apply inj_lt. apply H2.
      left; reflexivity.
    + apply H6. left; reflexivity.
  - apply IHl; auto.
    + eapply fr_graph_has_v; eauto.
    + erewrite <- fr_block_mark; eauto.
    + intros. erewrite <- fr_block_fields; eauto. apply H2. right; assumption.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
    + intros. apply H6. right; assumption.
Qed.

Lemma svwl_dst_unchanged: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    from <> to -> gen_unmarked g1 to ->
    forall e, graph_has_v g1 (field_addr e) ->
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
      * eapply svfl_gen_unmarked; eauto.
      * eapply svfl_graph_has_v; eauto.
      * intros. specialize (H4 H8). intro. apply H4. right; assumption.
Qed.

Lemma svfl_gen_v_num_to: forall from to v l g1 g2,
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    (gen_v_num g1 to <= gen_v_num g2 to)%nat.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H0; subst. 1: lia.
  assert (graph_has_gen g3 to) by (rewrite <- fr_graph_has_gen; eauto).
  specialize (IHl _ _ H1 H6). transitivity (gen_v_num g3 to); auto.
  eapply fr_O_gen_v_num_to; eauto.
Qed.

Lemma svfl_graph_has_v_inv: forall from to v l g1 g2,
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall v2,
      graph_has_v g2 v2 ->
      graph_has_v g1 v2 \/
      (addr_gen v2 = to /\ gen_v_num g1 to <= addr_block v2 < gen_v_num g2 to)%nat.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H0; subst. 1: left; assumption.
  assert (graph_has_gen g3 to) by (rewrite <- fr_graph_has_gen; eauto).
  specialize (IHl _ _ H2 H7 _ H1). destruct IHl.
  - eapply (fr_O_graph_has_v_inv from to _ g1 g3) in H4; eauto. destruct H4.
    1: left; assumption. right. clear -H1 H4. unfold new_copied_v in H4. subst.
    destruct H1. unfold gen_v_num. simpl in *. red in H0. lia.
  - right. destruct H3. split. 1: assumption. destruct H5. split; auto.
    eapply fr_O_gen_v_num_to in H4; [lia | assumption].
Qed.

Lemma svwl_graph_has_v: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall v, graph_has_v g1 v -> graph_has_v g2 v.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: assumption.
  1: eapply IHl; eauto. assert (graph_has_gen g3 to) by
      (rewrite <- svfl_graph_has_gen; eauto). eapply IHl; eauto.
  eapply (svfl_graph_has_v _ _ _ _ g1 g3); eauto.
Qed.

Lemma svwl_gen_v_num_to: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    (gen_v_num g1 to <= gen_v_num g2 to)%nat.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: lia.
  1: apply IHl; auto. transitivity (gen_v_num g3 to).
  - eapply svfl_gen_v_num_to; eauto.
  - apply IHl; auto. rewrite <- svfl_graph_has_gen; eauto.
Qed.

Lemma svwl_graph_has_v_inv: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall v,
      graph_has_v g2 v ->
      graph_has_v g1 v \/
      (addr_gen v = to /\ gen_v_num g1 to <= addr_block v < gen_v_num g2 to)%nat.
Proof.
  intros ? ? ?. induction l; intros; inversion H0; subst. 1: left; assumption.
  1: eapply IHl; eauto. assert (graph_has_gen g3 to) by
      (rewrite <- svfl_graph_has_gen; eauto).
  specialize (IHl _ _ H2 H9 _ H1). destruct IHl.
  - eapply svfl_graph_has_v_inv in H6; eauto. destruct H6; [left|right]. 1: assumption.
    destruct H6 as [? [? ?]]. split; [|split]; [assumption..|].
    apply svwl_gen_v_num_to in H9; [lia | assumption].
  - right. destruct H3 as [? [? ?]]. split; [|split]; try assumption.
    apply svfl_gen_v_num_to in H6; [lia | assumption].
Qed.

Lemma svwl_block_fields: forall from to l g g',
    graph_has_gen g to -> scan_vertex_while_loop from to l g g' ->
    forall v, graph_has_v g v -> block_fields (vlabel g v) = block_fields (vlabel g' v).
Proof.
  do 3 intro. induction l; intros; inversion H0; subst. 1: reflexivity.
  1: eapply IHl; eauto. erewrite <- (IHl g2 g'); eauto.
  - eapply svfl_block_fields; eauto.
  - rewrite <- svfl_graph_has_gen; eauto.
  - eapply svfl_graph_has_v; eauto.
Qed.

Lemma svwl_gen2gen_no_edge: forall from to l g1 g2,
    graph_has_gen g1 to -> from <> to -> gen_unmarked g1 to ->
    scan_vertex_while_loop from to l g1 g2 ->
    forall gen1 gen2, gen1 <> to -> gen2gen_no_edge g1 gen1 gen2 ->
                      gen2gen_no_edge g2 gen1 gen2.
Proof.
  intros. unfold gen2gen_no_edge in *. intros. destruct H5. simpl in H5.
  eapply svwl_graph_has_v_inv in H5; eauto. simpl in H5. destruct H5 as [? | [? ?]].
  2: contradiction. erewrite <- svwl_dst_unchanged; eauto.
  apply H4. split; simpl in *. 1: assumption.
  cut (get_edges g1 {| addr_gen := gen1 ; addr_block := vidx |} = get_edges g2 {| addr_gen := gen1 ; addr_block := vidx |}).
  + intros; rewrite H7; assumption.
  + unfold get_edges. unfold make_fields. erewrite svwl_block_fields; eauto.
Qed.


Lemma svfl_dst_changed: forall from to v l g1 g2,
    graph_has_v g1 v -> block_mark (vlabel g1 v) = false -> addr_gen v <> from ->
    copy_compatible g1 -> no_dangling_dst g1 -> from <> to ->
    (forall i,  In i l -> i < length (block_fields (vlabel g1 v)))%nat -> NoDup l ->
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall e i, In i l -> Znth (Z.of_nat i) (make_fields g2 v) = inr e ->
                addr_gen (dst g2 e) <> from.
Proof.
  intros ? ? ? ?. induction l; intros; inversion H8; subst. 1: inversion H9.
  assert (e = {| field_addr := v ; field_index := i |}). {
    apply make_fields_Znth_edge in H10. 1: rewrite Nat2Z.id in H10; assumption.
    split. 1: lia. rewrite Zlength_correct. apply inj_lt.
    erewrite <- svfl_block_fields; eauto. }
  assert (graph_has_v g3 v) by (eapply fr_graph_has_v; eauto).
  assert (block_mark (vlabel g3 v) = false) by (erewrite <- fr_block_mark; eauto).
  assert (graph_has_gen g3 to) by (erewrite <- fr_graph_has_gen; eauto).
  assert (forall j : nat, In j l -> j < Datatypes.length (block_fields (vlabel g3 v)))%nat. {
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
      * unfold make_fields in H8 |-*. erewrite svfl_block_fields; eauto.
  - eapply (IHl g3); eauto.
    + eapply (fr_copy_compatible _ _ _ _ g1); eauto.
    + eapply (fr_O_no_dangling_dst _ _ _ g1); eauto.
      * simpl. intuition. rewrite Zlength_correct. apply inj_lt. apply H5.
        left; reflexivity.
      * simpl. constructor.
    + apply NoDup_cons_1 in H6; assumption.
Qed.

Lemma svfl_no_edge2from: forall from to v g1 g2,
    graph_has_v g1 v -> block_mark (vlabel g1 v) = false -> addr_gen v <> from ->
    copy_compatible g1 -> no_dangling_dst g1 -> from <> to -> graph_has_gen g1 to ->
    scan_vertex_for_loop
      from to v (nat_inc_list (length (block_fields (vlabel g1 v)))) g1 g2 ->
    forall e, In e (get_edges g2 v) -> addr_gen (dst g2 e) <> from.
Proof.
  intros. unfold get_edges in H7. rewrite <- filter_sum_right_In_iff in H7.
  apply In_Znth in H7. destruct H7 as [i [? ?]].
  rewrite <- (Z2Nat.id i) in H8 by lia. eapply svfl_dst_changed; eauto.
  - intros. rewrite nat_inc_list_In_iff in H9. assumption.
  - apply nat_inc_list_NoDup.
  - rewrite nat_inc_list_In_iff. rewrite make_fields_eq_length in H7.
    erewrite svfl_block_fields; eauto. rewrite <- ZtoNat_Zlength.
    apply Z2Nat.inj_lt; lia.
Qed.

Lemma svfl_nth_gen_unchanged: forall from to v l g1 g2,
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall gen, gen <> to -> nth_gen g1 gen = nth_gen g2 gen.
Proof.
  intros. induction H0; subst; try reflexivity. transitivity (nth_gen g2 gen).
  - eapply fr_O_nth_gen_unchanged; eauto.
  - apply IHscan_vertex_for_loop. rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma svwl_nth_gen_unchanged: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen, gen <> to -> nth_gen g1 gen = nth_gen g2 gen.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst; try reflexivity.
  1: apply IHl; auto. transitivity (nth_gen g3 gen).
  - eapply svfl_nth_gen_unchanged; eauto.
  - apply IHl; auto. rewrite <- svfl_graph_has_gen; eauto.
Qed.

Lemma svwl_firstn_gen_clear: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen, (gen <= to)%nat ->
                firstn_gen_clear g1 gen -> firstn_gen_clear g2 gen.
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  erewrite <- (svwl_nth_gen_unchanged from); eauto. lia.
Qed.


Lemma svfl_stcg: forall from to v l g1 g2,
    graph_has_gen g1 to -> scan_vertex_for_loop from to v l g1 g2 ->
    forall gen1 gen2, graph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  intros. induction H0; subst; try assumption. apply IHscan_vertex_for_loop.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - eapply (fr_O_stcg from to); eauto.
Qed.

Lemma svwl_stcg: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen1 gen2, graph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst; try assumption.
  1: apply (IHl g1); auto. apply (IHl g3); auto.
  - erewrite <- (svfl_graph_has_gen from to); eauto.
  - erewrite <- (svfl_graph_has_gen from to); eauto.
  - eapply (svfl_stcg from to); eauto.
Qed.


Lemma svfl_copy_compatible: forall from to v l g1 g2,
    from <> to -> graph_has_gen g1 to ->
    scan_vertex_for_loop from to v l g1 g2 ->
    copy_compatible g1 -> copy_compatible g2.
Proof.
  do 4 intro. induction l; intros; inversion H1; subst. 1: assumption.
  cut (copy_compatible g3).
  - intros. apply (IHl g3); auto. erewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
Qed.

Lemma svfl_no_dangling_dst: forall from to v l g1 g2,
    graph_has_v g1 v -> block_mark (vlabel g1 v) = false -> addr_gen v <> from ->
    copy_compatible g1 -> graph_has_gen g1 to -> from <> to ->
    scan_vertex_for_loop from to v l g1 g2 ->
    (forall i,  In i l -> i < length (block_fields (vlabel g1 v)))%nat ->
    no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  do 4 intro. induction l; intros; inversion H5; subst. 1: assumption.
  cut (no_dangling_dst g3).
  - intros. apply (IHl g3); auto.
    + eapply fr_graph_has_v; eauto.
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
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    gen_unmarked g1 to -> copy_compatible g1 -> no_dangling_dst g1 ->
    from <> to -> NoDup l ->
    forall e i, In i l -> In e (get_edges g2 {| addr_gen := to; addr_block := i |}) ->
                addr_gen (dst g2 e) <> from.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst. 1: inversion H6.
  - simpl in H6. destruct H6. 2: apply NoDup_cons_1 in H5; eapply IHl; eauto. subst a.
    assert (In e (get_edges g1 {| addr_gen := to; addr_block := i |})). {
      unfold get_edges, make_fields in H7 |-*.
      erewrite svwl_block_fields; eauto. split; simpl; assumption. }
    rewrite no_scan_no_edge in H6. 2: assumption. inversion H6.
  - simpl in H6.
    assert (graph_has_gen g3 to) by (erewrite <- svfl_graph_has_gen; eauto).
    assert (gen_unmarked g3 to) by (eapply (svfl_gen_unmarked _ _ _ _ g1); eauto).
    destruct H6.
    + subst a. cut (addr_gen (dst g3 e) <> from).
      * intros. cut (dst g3 e = dst g2 e). 1: intros HS; rewrite <- HS; assumption.
        eapply svwl_dst_unchanged; eauto.
        -- erewrite get_edges_fst; eauto. eapply (svfl_graph_has_v _ _ _ _ g1); eauto.
           split; simpl; assumption.
        -- intros. erewrite get_edges_fst; eauto. simpl.
           apply NoDup_cons_2 in H5. assumption.
      * assert (graph_has_v g1 {| addr_gen := to; addr_block := i |}) by (split; simpl; assumption).
        eapply svfl_no_edge2from; eauto. unfold get_edges, make_fields in H7 |-*.
        erewrite svwl_block_fields; eauto. eapply (svfl_graph_has_v _ _ _ _ g1); eauto.
    + eapply (IHl g3); eauto.
      * eapply (svfl_copy_compatible _ _ _ _ g1); eauto.
      * eapply (svfl_no_dangling_dst from to); eauto.
        -- split; simpl; assumption.
        -- intros. rewrite nat_inc_list_In_iff in H13. assumption.
      * apply NoDup_cons_1 in H5. assumption.
Qed.

Lemma svwl_no_dangling_dst: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    gen_unmarked g1 to -> copy_compatible g1 -> from <> to ->
    no_dangling_dst g1 -> no_dangling_dst g2.
Proof.
  do 3 intro. induction l; intros; inversion H0; subst;
                [assumption | eapply IHl; eauto|]. cut (no_dangling_dst g3).
  - intros. apply (IHl g3); auto.
    + erewrite <- svfl_graph_has_gen; eauto.
    + eapply svfl_gen_unmarked; eauto.
    + eapply svfl_copy_compatible; eauto.
  - eapply (svfl_no_dangling_dst from to _ _ g1); eauto.
    + split; simpl; assumption.
    + intros. rewrite nat_inc_list_In_iff in H5. assumption.
Qed.

Lemma frr_dsr_no_edge2gen: forall from to f_info roots roots' g g1 g2,
    graph_has_gen g to -> from <> to -> gen_unmarked g to ->
    copy_compatible g -> no_dangling_dst g ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    roots_graph_compatible roots g ->
    forward_roots_relation from to f_info roots g roots' g1 ->
    do_scan_relation from to (generation_block_count (nth_gen g to)) g1 g2 ->
    no_edge2gen g from -> no_edge2gen g2 from.
Proof.
  intros. unfold no_edge2gen in *. intros. specialize (H8 _ H9).
  destruct (Nat.eq_dec another to).
  - subst. unfold gen2gen_no_edge in *. intros.
    destruct H10. simpl fst in *. destruct H7 as [m [? ?]].
    assert (graph_has_gen g1 to) by (erewrite <- frr_graph_has_gen; eauto).
    assert (graph_has_v g {| addr_gen := to ; addr_block := vidx |} \/ gen_v_num g to <= vidx < gen_v_num g2 to)%nat. {
      eapply (svwl_graph_has_v_inv from to _ g1 g2) in H10; eauto. simpl in H10.
      destruct H10.
      - eapply (frr_graph_has_v_inv from _ _ _ g) in H10; eauto.
        simpl in H10. destruct H10. 1: left; assumption.
        right. destruct H10 as [_ [? ?]]. split; auto.
        apply svwl_gen_v_num_to in H7; [lia | assumption].
      - right. destruct H10 as [_ [? ?]]. split; auto.
        apply frr_gen_v_num_to in H6; [lia | assumption]. } destruct H14.
    + assert (graph_has_v g1 {| addr_gen := to ; addr_block := vidx |}) by
          (eapply (frr_graph_has_v from to _ _ g); eauto).
      assert (get_edges g {| addr_gen := to ; addr_block := vidx |} = get_edges g2 {| addr_gen := to ; addr_block := vidx |}). {
        transitivity (get_edges g1 {| addr_gen := to ; addr_block := vidx |}); unfold get_edges, make_fields.
        - erewrite frr_block_fields; eauto.
        - erewrite svwl_block_fields; eauto. } simpl in H11. rewrite <- H16 in H11.
      assert (graph_has_e g {| field_addr := {| addr_gen := to ; addr_block := vidx |} ; field_index := eidx |}) by (split; simpl; assumption).
      specialize (H8 _ _ H17).
      erewrite (frr_dst_unchanged _ _ _ _ _ _ g1) in H8; eauto.
      erewrite (svwl_dst_unchanged) in H8; eauto; simpl.
      * eapply (frr_gen_unmarked _ _ _ _ g); eauto.
      * repeat intro. rewrite nat_seq_In_iff in H19. destruct H19 as [? _].
        destruct H14. simpl in H20. red in H20. lia.
    + eapply svwl_no_edge2from; eauto.
      * eapply (frr_gen_unmarked _ _ _ _ g); eauto.
      * eapply (frr_copy_compatible from to _ _ g); eauto.
      * eapply (frr_no_dangling_dst _ _ _ _ g); eauto.
      * apply nat_seq_NoDup.
      * rewrite nat_seq_In_iff. unfold gen_has_index in H12.
        unfold gen_v_num in H14. lia.
  - eapply (frr_gen2gen_no_edge _ _ _ _ g _ g1) in H8; eauto.
    destruct H7 as [m [? ?]]. eapply (svwl_gen2gen_no_edge from to _ g1 g2); eauto.
    + erewrite <- frr_graph_has_gen; eauto.
    + eapply frr_gen_unmarked; eauto.
Qed.