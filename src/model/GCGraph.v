Require Import Coq.Logic.FinFun.
Require Export Coq.Program.Basics.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

From compcert Require Import lib.Integers.
From compcert Require Import common.Values.

From VST Require Import floyd.sublist.
From VST Require Import floyd.coqlib3.
From VST Require Import floyd.functional_base.
From VST Require Import floyd.data_at_rec_lemmas.
From VST Require Import floyd.list_solver.
From VST Require Import msl.seplog.
From VST Require Import msl.shares.
From VST Require Import veric.base.
From VST Require Import veric.Clight_lemmas.
From VST Require Import veric.val_lemmas.
From VST Require Import veric.shares.

From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Export graph.graph_gen.

From CertiGC Require Import model.constants.

From CertiGC Require Export model.compatible.
From CertiGC Require Export model.copy.
From CertiGC Require Export model.cut.
From CertiGC Require Export model.forward.
From CertiGC Require Export model.graph.
From CertiGC Require Export model.heap.
From CertiGC Require Export model.reset.
From CertiGC Require Export model.update.
From CertiGC Require Export model.util.
From CertiGC Require Export model.scan.
From CertiGC Require Export model.thread_info.

Import ListNotations.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Local Close Scope Z_scope.

Local Open Scope Z_scope.

Instance share_inhabitant: Inhabitant share := emptyshare.


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


Local Close Scope Z_scope.



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
    (forall i,  In i l -> i < length (block_fields (vlabel g1 v))) ->
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

Lemma no_dangling_dst_reset: forall g gen,
    no_dangling_dst g -> no_edge2gen g gen ->
    no_dangling_dst (reset_graph gen g).
Proof.
  intros. unfold no_dangling_dst in *. red in H0. simpl. intros.
  rewrite graph_has_v_reset in *. destruct H1. rewrite get_edges_reset in H2.
  rewrite remove_ve_dst_unchanged. split.
  - apply (H v); assumption.
  - cut (addr_gen (dst g e) <> gen). 1: intuition. unfold gen2gen_no_edge in H0.
    destruct e as [[vgen vidx] eidx]. pose proof H2. apply get_edges_fst in H2.
    simpl in H2. subst v. simpl in *. apply H0; intuition. split; simpl; assumption.
Qed.

Lemma frr_copy_compatible: forall from to f_info roots g roots' g',
    from <> to -> graph_has_gen g to ->
    forward_roots_relation from to f_info roots g roots' g' ->
    copy_compatible g -> copy_compatible g'.
Proof.
  intros. induction H1. 1: assumption. apply IHforward_roots_loop.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
Qed.

Lemma frl_no_dangling_dst: forall from to f_info l roots g roots' g',
    graph_has_gen g to -> copy_compatible g -> from <> to ->
    (forall i, In i l -> i < length roots) ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    roots_graph_compatible roots g ->
    forward_roots_loop from to f_info l roots g roots' g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  do 4 intro. induction l; intros; inversion H5; subst. 1: assumption.
  assert (forward_p_compatible (inl (Z.of_nat a)) roots g from). {
    simpl. split. 1: lia. rewrite Zlength_correct. apply inj_lt.
    apply H2; left; reflexivity. } cut (no_dangling_dst g2).
  - intros. eapply (IHl (upd_roots from to (inl (Z.of_nat a)) g roots f_info)
                        g2 roots'); eauto.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply (fr_copy_compatible O from to _ g); eauto.
    + intros. rewrite <- ZtoNat_Zlength, upd_roots_Zlength, ZtoNat_Zlength; auto.
      apply H2. right; assumption.
    + rewrite upd_roots_Zlength; assumption.
    + eapply fr_roots_graph_compatible; eauto.
  - fold (forward_p2forward_t (inl (Z.of_nat a)) roots g) in H9.
    eapply fr_O_no_dangling_dst; eauto.
Qed.

Lemma frr_no_dangling_dst: forall from to f_info roots g roots' g',
    graph_has_gen g to -> copy_compatible g -> from <> to ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    roots_graph_compatible roots g ->
    forward_roots_relation from to f_info roots g roots' g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros. eapply frl_no_dangling_dst; eauto. intros.
  rewrite nat_inc_list_In_iff in H6. assumption.
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
    assert (graph_has_v g {| addr_gen := to ; addr_block := vidx |} \/ gen_v_num g to <= vidx < gen_v_num g2 to). {
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

Lemma frr_roots_fi_compatible: forall from to f_info roots1 g1 roots2 g2,
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    roots_fi_compatible roots1 f_info -> roots_fi_compatible roots2 f_info.
Proof.
  intros. induction H; subst. 1: assumption. apply IHforward_roots_loop.
  apply upd_roots_rf_compatible; assumption.
Qed.



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

Lemma ngs_0_lt: forall i, 0 < nth_gen_size i.
Proof.
  intros. unfold nth_gen_size.
  rewrite NURSERY_SIZE_eq, Zbits.Zshiftl_mul_two_p, Z.mul_1_l,
  <- two_p_is_exp by lia.
  cut (two_p (16 + Z.of_nat i) > 0); [|apply two_p_gt_ZERO]; lia.
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

Lemma safe_to_copy_complete: forall g i,
    safe_to_copy_to_except g (S i) -> safe_to_copy_gen g i (S i) -> safe_to_copy g.
Proof.
  intros. unfold safe_to_copy_to_except in H. unfold safe_to_copy. intros.
  destruct (Nat.eq_dec n i).
  - subst. assumption.
  - specialize (H (S n)). simpl in H. apply H; auto.
Qed.
