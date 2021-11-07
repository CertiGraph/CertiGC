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

Definition no_backward_edge (g: HeapGraph): Prop :=
  forall gen1 gen2, gen1 > gen2 -> gen2gen_no_edge g gen1 gen2.

Definition firstn_gen_clear (g: HeapGraph) (n: nat): Prop :=
  forall i, i < n -> graph_gen_clear g i.

Definition safe_to_copy_to_except (g: HeapGraph) (gen: nat): Prop :=
  forall n, n <> O -> n <> gen -> graph_has_gen g n -> safe_to_copy_gen g (pred n) n .

Definition safe_to_copy (g: HeapGraph): Prop :=
  forall n, graph_has_gen g (S n) -> safe_to_copy_gen g n (S n).

Lemma stc_stcte_O_iff: forall g, safe_to_copy g <-> safe_to_copy_to_except g O.
Proof.
  intros. unfold safe_to_copy, safe_to_copy_to_except. split; intros.
  - destruct n. 1: contradiction. simpl. apply H; assumption.
  - specialize (H (S n)). simpl in H. apply H; auto.
Qed.

Lemma fgc_nbe_no_edge2gen: forall g n,
    firstn_gen_clear g n -> no_backward_edge g -> no_edge2gen g n.
Proof.
  intros. red in H, H0 |-* . intros. red. intros. destruct H2. simpl in *.
  destruct (lt_eq_lt_dec another n) as [[?|?]|?]. 2: contradiction.
  - specialize (H _ l). red in H. destruct H2. simpl in *.
    red in H4. rewrite H in H4. lia.
  - assert (another > n) by lia. specialize (H0 _ _ H4). apply H0.
    split; simpl; assumption.
Qed.

Definition add_new_gen (gi: Generations) (gen_i: Generation): Generations := {|
  generations := generations gi +:: gen_i;
  generations__not_nil := app_not_nil (generations gi) gen_i;
|}.

Definition lgraph_add_new_gen (g: HeapGraph) (gen_i: Generation): HeapGraph :=
  Build_LabeledGraph _ _ _
                     (pg_lg g) (vlabel g) (elabel g) (add_new_gen (glabel g) gen_i).

Definition new_gen_relation (gen: nat) (g1 g2: HeapGraph): Prop :=
  if graph_has_gen_dec g1 gen then g1 = g2
  else exists gen_i: Generation, generation_block_count gen_i = O /\
                                      g2 = lgraph_add_new_gen g1 gen_i.

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

Lemma upd_heap_Zlength: forall (hp : Heap) (sp : Space) (i : Z),
    0 <= i < MAX_SPACES -> Zlength (upd_Znth i (heap_spaces hp) sp) = MAX_SPACES.
Proof.
  intros. rewrite upd_Znth_Zlength; rewrite heap_spaces__size; [reflexivity | assumption].
Qed.

Definition add_new_space (hp: Heap) (sp: Space) i (Hs: 0 <= i < MAX_SPACES): Heap := {|
  heap_spaces := upd_Znth i (heap_spaces hp) sp;
  heap_spaces__size := upd_heap_Zlength hp sp i Hs
|}.

Definition ti_add_new_space (ti: thread_info) (sp: Space) i
           (Hs: 0 <= i < MAX_SPACES): thread_info :=
  Build_thread_info (ti_heap_p ti) (add_new_space (ti_heap ti) sp i Hs)
                    (ti_args ti) (arg_size ti).

Lemma ang_nth_old: forall g gi gen,
    graph_has_gen g gen -> nth_gen (lgraph_add_new_gen g gi) gen = nth_gen g gen.
Proof. intros. unfold nth_gen. simpl. rewrite app_nth1; [reflexivity|assumption]. Qed.

Lemma ang_nth_new: forall g gi,
    nth_gen (lgraph_add_new_gen g gi) (length (generations (glabel g))) = gi.
Proof.
  intros. unfold nth_gen. simpl. rewrite app_nth2 by lia. rewrite Nat.sub_diag.
  simpl. reflexivity.
Qed.

Lemma ans_nth_old: forall ti sp i (Hs: 0 <= i < MAX_SPACES) gen,
    gen <> Z.to_nat i -> nth_space (ti_add_new_space ti sp i Hs) gen =
                         nth_space ti gen.
Proof.
  intros. rewrite !nth_space_Znth. simpl. rewrite upd_Znth_diff_strong.
  - reflexivity.
  - rewrite heap_spaces__size. assumption.
  - intro. apply H. subst. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma ans_nth_new: forall ti sp i (Hs: 0 <= i < MAX_SPACES),
    nth_space (ti_add_new_space ti sp i Hs) (Z.to_nat i) = sp.
Proof.
  intros. rewrite nth_space_Znth. simpl. rewrite Z2Nat.id by lia.
  rewrite upd_Znth_same; [reflexivity | rewrite heap_spaces__size; assumption].
Qed.

Lemma ang_graph_has_gen: forall g gi gen,
    graph_has_gen (lgraph_add_new_gen g gi) gen <->
    graph_has_gen g gen \/ gen = length (generations (glabel g)).
Proof.
  intros. unfold graph_has_gen. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma gti_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES),
    graph_thread_info_compatible g ti ->
    ~ graph_has_gen g (Z.to_nat i) -> graph_has_gen g (Z.to_nat (i - 1)) ->
    (forall (gr: HeapGraph), generation_space_compatible gr (Z.to_nat i, gi, sp)) ->
    graph_thread_info_compatible (lgraph_add_new_gen g gi)
                                 (ti_add_new_space ti sp i Hs).
Proof.
  intros. unfold graph_thread_info_compatible in *. destruct H as [? [? ?]].
  assert (length (generations (glabel g)) = Z.to_nat i). {
    clear -H0 H1. unfold graph_has_gen in *.
    rewrite Z2Nat.inj_sub in H1 by lia. simpl in H1. lia. }
  pose proof (heap_spaces__size (ti_heap ti)).
  assert (length (generations (glabel (lgraph_add_new_gen g gi))) <=
          length (heap_spaces (ti_heap (ti_add_new_space ti sp i Hs))))%nat. {
    simpl. rewrite <- !ZtoNat_Zlength, upd_Znth_Zlength by lia.
    rewrite H6, ZtoNat_Zlength, app_length, H5. simpl. change (S O) with (Z.to_nat 1).
    rewrite <- Z2Nat.inj_add, <- Z2Nat.inj_le by lia. lia. }
  split; [|split]; auto.
  - rewrite gsc_iff in H |- * by assumption. intros.
    apply ang_graph_has_gen in H8. destruct H8.
    + rewrite ang_nth_old by assumption. rewrite ans_nth_old.
      1: apply H; assumption. red in H8. rewrite H5 in H8. lia.
    + subst gen. rewrite ang_nth_new, H5, ans_nth_new. apply H2.
  - simpl. rewrite <- upd_Znth_map. rewrite app_length. rewrite H5 in *. simpl.
    change (S O) with (Z.to_nat 1).
    rewrite <- Z2Nat.inj_add, <- sublist_skip in * by lia.
    rewrite upd_Znth_Zlength; rewrite Zlength_map, heap_spaces__size in *. 2: assumption.
    rewrite sublist_upd_Znth_r. 2: lia. 2: rewrite Zlength_map, heap_spaces__size; lia.
    apply Forall_incl with (VST.floyd.sublist.sublist i MAX_SPACES (map space_base (heap_spaces (ti_heap ti)))) ; try assumption.
    rewrite Z.add_comm. replace MAX_SPACES with (MAX_SPACES - i + i) at 1 by lia.
    rewrite <- sublist_sublist with (j := MAX_SPACES) by lia.
    unfold incl. intro a. apply VST.floyd.sublist.sublist_In.
Qed.

Lemma ang_graph_has_v: forall g gi v,
    graph_has_v g v -> graph_has_v (lgraph_add_new_gen g gi) v.
Proof.
  intros. destruct v as [gen idx]. destruct H; split; simpl in *.
  - unfold graph_has_gen in *. simpl. rewrite app_length. simpl. lia.
  - unfold gen_has_index in *. rewrite ang_nth_old; assumption.
Qed.

Lemma ang_roots_graph_compatible: forall roots g gi,
    roots_graph_compatible roots g ->
    roots_graph_compatible roots (lgraph_add_new_gen g gi).
Proof.
  intros. unfold roots_graph_compatible in *. rewrite Forall_forall in *. intros.
  apply ang_graph_has_v. apply H. assumption.
Qed.

Lemma ang_roots_compatible: forall roots out g gi,
    roots_compatible g out roots ->
    roots_compatible (lgraph_add_new_gen g gi) out roots.
Proof. intros. destruct H. split; auto. apply ang_roots_graph_compatible. auto. Qed.

Lemma ang_graph_has_v_inv: forall g gi v,
    generation_block_count gi = O -> graph_has_v (lgraph_add_new_gen g gi) v ->
    graph_has_v g v.
Proof.
  intros. destruct v as [gen idx]. destruct H0; split; simpl in *.
  - apply ang_graph_has_gen in H0. destruct H0; auto. red in H1. exfalso. subst.
    rewrite ang_nth_new, H in H1. lia.
  - apply ang_graph_has_gen in H0. red in H1. destruct H0.
    + rewrite ang_nth_old in H1; assumption.
    + exfalso. subst. rewrite ang_nth_new, H in H1. lia.
Qed.

Lemma ang_outlier_compatible: forall g gi out,
    generation_block_count gi = O -> outlier_compatible g out ->
    outlier_compatible (lgraph_add_new_gen g gi) out.
Proof.
  intros. unfold outlier_compatible in *. intros.
  apply ang_graph_has_v_inv in H1; auto. simpl. apply H0. assumption.
Qed.

Lemma ang_vertex_address_old: forall (g : HeapGraph) (gi : Generation) (v : Addr),
    graph_has_v g v ->
    vertex_address (lgraph_add_new_gen g gi) v = vertex_address g v.
Proof.
  intros. unfold vertex_address. f_equal. unfold gen_start. destruct H.
  rewrite if_true by (rewrite ang_graph_has_gen; left; assumption).
  rewrite if_true by assumption. rewrite ang_nth_old by assumption. reflexivity.
Qed.

Lemma fta_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES) fi roots,
    fun_thread_arg_compatible g ti fi roots -> roots_graph_compatible roots g ->
    fun_thread_arg_compatible (lgraph_add_new_gen g gi)
                              (ti_add_new_space ti sp i Hs) fi roots.
Proof.
  intros. unfold fun_thread_arg_compatible in *. simpl. rewrite <- H.
  apply map_ext_in. intros. destruct a; [destruct s|]; simpl; try reflexivity.
  apply ang_vertex_address_old. red in H0. rewrite Forall_forall in H0. apply H0.
  rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Lemma super_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES) fi roots out,
    ~ graph_has_gen g (Z.to_nat i) -> graph_has_gen g (Z.to_nat (i - 1)) ->
    (forall (gr: HeapGraph), generation_space_compatible gr (Z.to_nat i, gi, sp)) ->
    generation_block_count gi = O -> super_compatible (g, ti, roots) fi out ->
    super_compatible (lgraph_add_new_gen g gi, ti_add_new_space ti sp i Hs, roots)
                     fi out.
Proof.
  intros. destruct H3 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply gti_compatible_add; assumption.
  - apply fta_compatible_add; [|destruct H5]; assumption.
  - apply ang_roots_compatible; assumption.
  - apply ang_outlier_compatible; assumption.
Qed.

Lemma ti_size_spec_add: forall ti sp i (Hs: 0 <= i < MAX_SPACES),
    space_capacity sp = nth_gen_size (Z.to_nat i) -> ti_size_spec ti ->
    ti_size_spec (ti_add_new_space ti sp i Hs).
Proof.
  intros. unfold ti_size_spec in *. rewrite Forall_forall in *. intros.
  specialize (H0 _ H1). unfold nth_gen_size_spec in *.
  destruct (Nat.eq_dec x (Z.to_nat i)); unfold gen_size.
  - subst x. rewrite !ans_nth_new. if_tac; auto.
  - rewrite !ans_nth_old; assumption.
Qed.

Lemma firstn_gen_clear_add: forall g gi i,
    graph_has_gen g (Z.to_nat i) -> firstn_gen_clear g (Z.to_nat i) ->
    firstn_gen_clear (lgraph_add_new_gen g gi) (Z.to_nat i).
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros. specialize (H0 _ H1).
  rewrite ang_nth_old; auto. unfold graph_has_gen in *. lia.
Qed.

Lemma ans_space_address: forall ti sp i (Hs: 0 <= i < MAX_SPACES) j,
    space_address (ti_add_new_space ti sp i Hs) (Z.to_nat j) =
    space_address ti (Z.to_nat j).
Proof. intros. unfold space_address. simpl. reflexivity. Qed.

Lemma ang_make_header: forall g gi v,
    make_header g v = make_header (lgraph_add_new_gen g gi) v.
Proof. intros. unfold make_header. reflexivity. Qed.

Lemma ang_make_fields_vals_old: forall g gi v,
    graph_has_v g v -> copy_compatible g -> no_dangling_dst g ->
    make_fields_vals g v = make_fields_vals (lgraph_add_new_gen g gi) v.
Proof.
  intros. unfold make_fields_vals. simpl.
  assert (map (field2val g) (make_fields g v) =
          map (field2val (lgraph_add_new_gen g gi))
              (make_fields (lgraph_add_new_gen g gi) v)). {
    unfold make_fields. simpl. apply map_ext_in. intros.
    destruct a; [destruct s|]; simpl; auto. rewrite ang_vertex_address_old; auto.
    red in H1. apply (H1 v); auto. unfold get_edges.
    rewrite <- filter_sum_right_In_iff. assumption. } rewrite <- H2.
  destruct (block_mark (vlabel g v)) eqn:?; auto. f_equal.
  rewrite ang_vertex_address_old; auto. destruct (H0 _ H Heqb). assumption.
Qed.

Lemma ang_graph_gen_size_old: forall g gi gen,
    graph_has_gen g gen -> graph_gen_size g gen =
                           graph_gen_size (lgraph_add_new_gen g gi) gen.
Proof.
  intros. unfold graph_gen_size. rewrite ang_nth_old by assumption.
  apply fold_left_ext. intros. unfold vertex_size_accum. reflexivity.
Qed.

Lemma nth_gen_size_le_S: forall n : nat, nth_gen_size n <= nth_gen_size (S n).
Proof.
  intros n. unfold nth_gen_size. rewrite Nat2Z.inj_succ, two_p_S by lia.
  assert (two_p (Z.of_nat n) > 0) by (apply two_p_gt_ZERO; lia).
  assert (0 < NURSERY_SIZE) by (vm_compute; reflexivity).
  rewrite Z.mul_assoc, (Z.mul_comm NURSERY_SIZE 2).
  assert (0 < NURSERY_SIZE * two_p (Z.of_nat n)). apply Z.mul_pos_pos; lia.
  rewrite <- Z.add_diag, Z.mul_add_distr_r. lia.
Qed.

Lemma stcte_add: forall g gi i,
    generation_block_count gi = O -> safe_to_copy_to_except g i ->
    safe_to_copy_to_except (lgraph_add_new_gen g gi) i.
Proof.
  intros. unfold safe_to_copy_to_except in *. intros. rewrite ang_graph_has_gen in H3.
  destruct H3.
  - specialize (H0 _ H1 H2 H3). unfold safe_to_copy_gen in *.
    rewrite <- ang_graph_gen_size_old; assumption.
  - unfold safe_to_copy_gen. simpl. unfold graph_gen_size.
    rewrite H3 at 4. rewrite ang_nth_new, H. unfold previous_vertices_size.
    simpl. destruct n. 1: contradiction. simpl. rewrite Z.sub_0_r.
    apply nth_gen_size_le_S.
Qed.

Lemma graph_unmarked_add: forall g gi,
    generation_block_count gi = O -> graph_unmarked g ->
    graph_unmarked (lgraph_add_new_gen g gi).
Proof.
  intros. unfold graph_unmarked in *. intros. apply ang_graph_has_v_inv in H1; auto.
  simpl. apply H0. assumption.
Qed.

Lemma ang_get_edges: forall g gi v,
    get_edges g v = get_edges (lgraph_add_new_gen g gi) v.
Proof. intros. unfold get_edges, make_fields. simpl. reflexivity. Qed.

Lemma no_backward_edge_add: forall g gi,
    generation_block_count gi = O -> no_backward_edge g ->
    no_backward_edge (lgraph_add_new_gen g gi).
Proof.
  intros. unfold no_backward_edge, gen2gen_no_edge in *. intros. simpl.
  destruct H2. simpl in *. rewrite <- ang_get_edges in H3.
  apply ang_graph_has_v_inv in H2; auto. apply H0; auto. split; simpl; auto.
Qed.

Lemma no_dangling_dst_add: forall g gi,
    generation_block_count gi = O -> no_dangling_dst g ->
    no_dangling_dst (lgraph_add_new_gen g gi).
Proof.
  intros. unfold no_dangling_dst in *. intros. simpl.
  apply ang_graph_has_v_inv in H1; auto. rewrite <- ang_get_edges in H2.
  apply ang_graph_has_v, (H0 v); auto.
Qed.

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

Lemma frr_nth_gen_unchanged: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, gen <> to -> nth_gen g1 gen = nth_gen g2 gen.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_O_nth_gen_unchanged; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
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

Lemma frr_firstn_gen_clear: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, (gen <= to)%nat ->
                firstn_gen_clear g1 gen -> firstn_gen_clear g2 gen.
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  erewrite <- frr_nth_gen_unchanged; eauto. lia.
Qed.

Lemma svwl_firstn_gen_clear: forall from to l g1 g2,
    graph_has_gen g1 to -> scan_vertex_while_loop from to l g1 g2 ->
    forall gen, (gen <= to)%nat ->
                firstn_gen_clear g1 gen -> firstn_gen_clear g2 gen.
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  erewrite <- (svwl_nth_gen_unchanged from); eauto. lia.
Qed.

Lemma firstn_gen_clear_reset: forall g i,
    firstn_gen_clear g i -> firstn_gen_clear (reset_graph i g) (S i).
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  assert (i0 < i \/ i0 = i)%nat by lia. destruct H1.
  - rewrite reset_nth_gen_diff by lia. apply H; assumption.
  - subst i0. unfold nth_gen. simpl. rewrite reset_nth_gen_info_same.
    simpl. reflexivity.
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

Lemma ti_relation_size_spec: forall t_info1 t_info2 : thread_info,
    thread_info_relation t_info1 t_info2 ->
    ti_size_spec t_info1 -> ti_size_spec t_info2.
Proof.
  intros. unfold ti_size_spec in *. rewrite Forall_forall in *. intros.
  specialize (H0 _ H1). unfold nth_gen_size_spec in *. destruct H as [? [? ?]].
  rewrite <- H2, <- H3. assumption.
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



Lemma fr_O_stcg: forall from to p g1 g2,
    graph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen1 gen2, graph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  intros. unfold safe_to_copy_gen in *.
  erewrite <- (fr_O_graph_gen_size_unchanged from to); eauto.
Qed.

Lemma frr_stcg: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen1 gen2, graph_has_gen g1 gen2 -> gen2 <> to ->
                      safe_to_copy_gen g1 gen1 gen2 -> safe_to_copy_gen g2 gen1 gen2.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_loop.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - eapply (fr_O_stcg from to); eauto.
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

Lemma reset_stct: forall g i gen1 gen2,
    i <> gen2 -> safe_to_copy_gen g gen1 gen2 ->
    safe_to_copy_gen (reset_graph i g) gen1 gen2.
Proof.
  intros. unfold safe_to_copy_gen in *. rewrite reset_graph_gen_size_eq; auto.
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
