Require Import Coq.Logic.FinFun.
Require Export Coq.Program.Basics.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

From compcert Require Import lib.Integers.
From compcert Require Import common.Values.

From VST Require Import veric.base.
From VST Require Import veric.Clight_lemmas.
From VST Require Import veric.val_lemmas.
From VST Require Import veric.shares.
From VST Require Import msl.seplog.
From VST Require Import msl.shares.
From VST Require Import floyd.sublist.
From VST Require Import floyd.coqlib3.
From VST Require Import floyd.functional_base.
From VST Require Import floyd.data_at_rec_lemmas.
From VST Require Import floyd.list_solver.

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
From CertiGC Require Export model.thread_info.

Import ListNotations.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Local Close Scope Z_scope.

Local Open Scope Z_scope.

Instance share_inhabitant: Inhabitant share := emptyshare.



Lemma lcv_super_compatible_unchanged: forall
    g t_info roots f_info outlier to v
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (vertex_size g v)),
    graph_has_gen g to -> graph_has_v g v ->
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible
      (lgraph_copy_v g v to,
       (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh),
       roots) f_info outlier.
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lcv_graph_thread_info_compatible; assumption.
  - destruct H3. apply lcv_fun_thread_arg_compatible_unchanged; assumption.
  - apply lcv_roots_compatible_unchanged; assumption.
  - apply lcv_outlier_compatible; assumption.
Qed.

Lemma lcv_super_compatible: forall
    g t_info roots f_info outlier to v z
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (vertex_size g v))
    (Hm : 0 <= Znth z (live_roots_indices f_info) < MAX_ARGS),
    graph_has_gen g to -> graph_has_v g v ->
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible
      (lgraph_copy_v g v to,
       update_thread_info_arg
         (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh)
         (Znth z (live_roots_indices f_info))
         (vertex_address g (new_copied_v g to)) Hm,
       upd_bunch z f_info roots (inr (new_copied_v g to))) f_info outlier.
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lcv_graph_thread_info_compatible; assumption.
  - destruct H3. apply lcv_fun_thread_arg_compatible; assumption.
  - apply lcv_roots_compatible; assumption.
  - apply lcv_outlier_compatible; assumption.
Qed.




Lemma utia_ti_heap: forall t_info i ad (Hm : 0 <= i < MAX_ARGS),
    ti_heap (update_thread_info_arg t_info i ad Hm) = ti_heap t_info.
Proof. intros. simpl. reflexivity. Qed.

Lemma cti_space_not_eq: forall t_info i s n
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s),
    (Z.of_nat n) <> i ->
    nth_space (cut_thread_info t_info i s Hi Hh) n = nth_space t_info n.
Proof.
  intros. rewrite !nth_space_Znth. simpl.
  pose proof (Nat2Z.is_nonneg n). remember (Z.of_nat n). clear Heqz.
  remember (heap_spaces (ti_heap t_info)). destruct (Z_lt_le_dec z (Zlength l)).
  - assert (0 <= z < Zlength l) by lia.
    rewrite upd_Znth_diff; [reflexivity |assumption..].
  - rewrite !Znth_overflow;
      [reflexivity | | rewrite upd_Znth_Zlength by assumption]; lia.
Qed.

Lemma cti_space_eq: forall t_info i s
    (Hi : 0 <= Z.of_nat i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat i) (heap_spaces (ti_heap t_info))) s),
    nth_space (cut_thread_info t_info (Z.of_nat i) s Hi Hh) i =
    cut_space (Znth (Z.of_nat i) (heap_spaces (ti_heap t_info))) s Hh.
Proof.
  intros. rewrite nth_space_Znth. simpl. rewrite upd_Znth_same by assumption.
  reflexivity.
Qed.

Lemma cti_gen_size: forall t_info i s n
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s),
    gen_size (cut_thread_info t_info i s Hi Hh) n =
    gen_size t_info n.
Proof.
  intros. unfold gen_size. destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i. rewrite cti_space_eq. simpl. rewrite nth_space_Znth. reflexivity.
  - rewrite cti_space_not_eq; [reflexivity | assumption].
Qed.

Lemma cti_space_base: forall t_info i s  n
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s),
    space_base (nth_space (cut_thread_info t_info i s Hi Hh) n) =
    space_base (nth_space t_info n).
Proof.
  intros. destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i. rewrite cti_space_eq. simpl. rewrite nth_space_Znth. reflexivity.
  - rewrite cti_space_not_eq; [reflexivity | assumption].
Qed.

Lemma utiacti_gen_size: forall t_info i1 i2 s ad n
    (Hi : 0 <= i1 < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i1 (heap_spaces (ti_heap t_info))) s)
    (Hm : 0 <= i2 < MAX_ARGS),
    gen_size (update_thread_info_arg (cut_thread_info t_info i1 s Hi Hh) i2 ad Hm) n =
    gen_size t_info n.
Proof.
  intros. unfold gen_size, nth_space. rewrite utia_ti_heap. apply cti_gen_size.
Qed.

Lemma utiacti_space_base: forall t_info i1 i2 s ad n
    (Hi : 0 <= i1 < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i1 (heap_spaces (ti_heap t_info))) s)
    (Hm : 0 <= i2 < MAX_ARGS),
    space_base
      (nth_space (update_thread_info_arg (cut_thread_info t_info i1 s Hi Hh) i2 ad Hm)
                 n) = space_base (nth_space t_info n).
Proof. intros. unfold nth_space. rewrite utia_ti_heap. apply cti_space_base. Qed.

Definition thread_info_relation t t':=
  ti_heap_p t = ti_heap_p t' /\ (forall n, gen_size t n = gen_size t' n) /\
  forall n, space_base (nth_space t n) = space_base (nth_space t' n).

Lemma tir_id: forall t, thread_info_relation t t.
Proof. intros. red. split; [|split]; reflexivity. Qed.

Lemma upd_Znth_diff_strong : forall {A}{d: Inhabitant A} i j l (u : A),
    0 <= j < Zlength l -> i <> j ->
  Znth i (upd_Znth j l u) = Znth i l.
Proof.
  intros.
  destruct (zlt i 0).
  { rewrite !Znth_underflow; auto. }
  destruct (zlt i (Zlength l)).
  apply upd_Znth_diff; auto; lia.
  { rewrite !Znth_overflow; auto.
    rewrite upd_Znth_Zlength; auto. }
Qed.


Lemma lgd_f2v_eq_except_one: forall g fd e v',
    fd <> (inr e) ->
    field2val g fd = field2val (labeledgraph_gen_dst g e v') fd.
Proof.
  intros; unfold field2val; simpl.
  destruct fd; [destruct s|]; try reflexivity.
  unfold updateEdgeFunc; if_tac; [exfalso; apply H; rewrite H0|]; reflexivity.
Qed.

Lemma lgd_map_f2v_diff_vert_eq: forall g v v' v1 e n,
    0 <= n < Zlength (make_fields g v) ->
    Znth n (make_fields g v) = inr e ->
    v1 <> v ->
    map (field2val g) (make_fields g v1) =
    map (field2val (labeledgraph_gen_dst g e v'))
        (make_fields (labeledgraph_gen_dst g e v') v1).
Proof.
    intros.
    rewrite lgd_make_fields_eq.
    apply Znth_list_eq. split.
    1: repeat rewrite Zlength_map; reflexivity.
    intros. rewrite Zlength_map in H2.
    repeat rewrite Znth_map by assumption.
    apply lgd_f2v_eq_except_one. intro.
    pose proof (make_fields_edge_unique g e v
                                        v1 n j H H2 H0 H3).
    destruct H4. unfold not in H1. symmetry in H5.
    apply (H1 H5).
Qed.

Lemma lgd_f2v_eq_after_update: forall g v v' e n j,
  0 <= n < Zlength (make_fields g v) ->
  0 <= j < Zlength (make_fields g v) ->
  Znth n (make_fields g v) = inr e ->
  Znth j (upd_Znth n (map (field2val g)
                          (make_fields g v)) (vertex_address g v')) =
  Znth j
    (map (field2val (labeledgraph_gen_dst g e v'))
         (make_fields (labeledgraph_gen_dst g e v') v)).
Proof.
  intros.
  rewrite Znth_map.
  2: rewrite lgd_make_fields_eq; assumption.
  assert (j = n \/ j <> n) by lia; destruct H2.
  + subst j; rewrite upd_Znth_same.
    2: rewrite Zlength_map; assumption.
    replace (make_fields (labeledgraph_gen_dst g e v') v)
      with (make_fields g v) by reflexivity.
    rewrite H1; simpl field2val.
    unfold updateEdgeFunc; if_tac; try reflexivity.
    unfold complement in H2; assert (e = e) by reflexivity.
    apply H2 in H3; exfalso; assumption.
  + rewrite upd_Znth_diff_strong; [|rewrite Zlength_map|]; try assumption.
    rewrite Znth_map by assumption.
    apply (lgd_f2v_eq_except_one g (Znth j (make_fields g v))).
    intro. pose proof (make_fields_edge_unique g e v v n j H H0 H1 H3).
    lia.
Qed.

Lemma lgd_mfv_change_in_one_spot: forall g v e v' n,
    0 <= n < Zlength (make_fields g v) ->
    block_mark (vlabel g v) = false ->
    Znth n (make_fields g v) = inr e ->
    upd_Znth n (make_fields_vals g v) (vertex_address g v') =
    (make_fields_vals (labeledgraph_gen_dst g e v') v).
Proof.
  intros.
  rewrite (Znth_list_eq (upd_Znth n (make_fields_vals g v)
               (vertex_address g v')) (make_fields_vals
                     (labeledgraph_gen_dst g e v') v)).
  rewrite upd_Znth_Zlength, fields_eq_length.
  2: rewrite fields_eq_length; rewrite make_fields_eq_length in H; assumption.
  split. 1: rewrite fields_eq_length; reflexivity.
  intros.
  unfold make_fields_vals.
  replace (block_mark (vlabel (labeledgraph_gen_dst g e v') v))
    with (block_mark (vlabel g v)) by reflexivity.
  rewrite H0; rewrite <- make_fields_eq_length in H2.
  apply lgd_f2v_eq_after_update; assumption.
Qed.

Lemma lgd_no_dangling_dst: forall g e v',
    graph_has_v g v' ->
    no_dangling_dst g ->
     no_dangling_dst (labeledgraph_gen_dst g e v').
Proof.
  intros. unfold no_dangling_dst in *.
  intros. rewrite <- lgd_graph_has_v.
  simpl. unfold updateEdgeFunc; if_tac; [assumption | apply (H0 v)]; assumption.
Qed.

Lemma lgd_no_dangling_dst_copied_vert: forall g e v,
    copy_compatible g ->
    graph_has_v g v ->
    block_mark (vlabel g v) = true ->
    no_dangling_dst g ->
    no_dangling_dst (labeledgraph_gen_dst g e (block_copied_vertex (vlabel g v))).
Proof.
  intros.
  assert (graph_has_v g (block_copied_vertex (vlabel g v))) by apply (H v H0 H1).
  apply lgd_no_dangling_dst; assumption.
Qed.

Lemma lgd_enough_space_to_copy: forall g e v' t_info gen sp,
    enough_space_to_copy g t_info gen sp ->
    enough_space_to_copy (labeledgraph_gen_dst g e v') t_info gen sp.
Proof.
  intros. unfold enough_space_to_copy in *. intuition. Qed.

Lemma lgd_copy_compatible: forall g v' e,
    copy_compatible g ->
    copy_compatible (labeledgraph_gen_dst g e v').
Proof.
  intros. unfold copy_compatible in *. intuition. Qed.

Lemma lgd_forward_condition: forall g t_info v to v' e,
    addr_gen v <> to ->
    graph_has_v g v ->
    graph_has_v g v' ->
    forward_condition g t_info (addr_gen v) to ->
    forward_condition (labeledgraph_gen_dst g e v') t_info (addr_gen v) to.
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply lgd_enough_space_to_copy; assumption.
  - apply lgd_graph_has_gen; assumption.
  - apply lgd_graph_has_gen; assumption.
  - apply lgd_copy_compatible; assumption.
  - apply lgd_no_dangling_dst; assumption.
Qed.

Lemma lgd_rgc: forall g roots e v,
    roots_graph_compatible roots g ->
    roots_graph_compatible roots (labeledgraph_gen_dst g e v).
Proof.
  intros. red in H |-*. rewrite Forall_forall in *. intros.
  rewrite <- lgd_graph_has_v. apply H. assumption.
Qed.

Lemma lgd_roots_compatible: forall g outlier roots e v,
    roots_compatible g outlier roots ->
    roots_compatible (labeledgraph_gen_dst g e v) outlier roots.
Proof. intros. destruct H. split; [|apply lgd_rgc]; assumption. Qed.

Lemma lgd_graph_thread_info_compatible:
  forall (g : HeapGraph) (t_info : thread_info) e (v' : Addr),
  graph_thread_info_compatible g t_info ->
  graph_thread_info_compatible (labeledgraph_gen_dst g e v') t_info.
Proof.
  intros; destruct H; split; assumption. Qed.

Lemma lgd_fun_thread_arg_compatible:
  forall (g : HeapGraph) (t_info : thread_info) e (v' : Addr) f_info roots,
    fun_thread_arg_compatible g t_info f_info roots ->
    fun_thread_arg_compatible (labeledgraph_gen_dst g e v') t_info f_info roots.
Proof.
  intros. unfold fun_thread_arg_compatible in *.
  rewrite <- H. apply map_ext_in. intros. destruct a; [destruct s|]; reflexivity.
Qed.

Lemma lgd_outlier_compatible:
  forall (g : HeapGraph) (t_info : thread_info) e (v' : Addr) outlier,
    outlier_compatible g outlier ->
    outlier_compatible (labeledgraph_gen_dst g e v') outlier.
Proof.
  intros. intro v. intros.
  rewrite <- lgd_graph_has_v in H0.
  unfold labeledgraph_gen_dst, pregraph_gen_dst, updateEdgeFunc; simpl.
  apply (H v H0).
Qed.

Lemma lgd_super_compatible: forall g t_info roots f_info outlier v' e,
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible ((labeledgraph_gen_dst g e v'), t_info, roots) f_info outlier.
Proof.
  intros. destruct H as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lgd_graph_thread_info_compatible; assumption.
  - destruct H1. apply lgd_fun_thread_arg_compatible; assumption.
  - apply lgd_roots_compatible; assumption.
  - apply lgd_outlier_compatible; assumption.
Qed.



Lemma lcv_closure_has_v: forall g v to x,
    graph_has_gen g to -> closure_has_v g x -> closure_has_v (lgraph_copy_v g v to) x.
Proof.
  intros. unfold closure_has_v in *. destruct x as [gen index]. simpl in *.
  destruct H0. split. 1: rewrite <- lcv_graph_has_gen; assumption.
  destruct (Nat.eq_dec gen to).
  - subst gen. red. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption.
    simpl. red in H1. unfold nth_gen in H1. lia.
  - red. rewrite lcv_nth_gen; assumption.
Qed.

Lemma fr_closure_has_v: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, closure_has_v g v -> closure_has_v g' v.
Proof.
  intros. remember (fun (g: HeapGraph) (v: Addr) (x: nat) => True) as Q.
  remember (fun g1 g2 v => closure_has_v g1 v -> closure_has_v g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - apply H3, H2. assumption.
  - apply lcv_closure_has_v; assumption.
Qed.


Lemma fl_graph_has_v: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, graph_has_v g v -> graph_has_v g' v.
Proof.
  intros. revert g g' H H0 v H1. induction l; intros; inversion H0; subst.
  1: assumption. cut (graph_has_v g2 v).
  - intros. assert (graph_has_gen g2 to) by
        (apply (fr_graph_has_gen _ _ _ _ _ _ H H5); assumption).
    apply (IHl _ _ H3 H8 _ H2).
  - apply (fr_graph_has_v _ _ _ _ _ _ H H5 _ H1).
Qed.

Lemma fr_vertex_address: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, closure_has_v g v -> vertex_address g v = vertex_address g' v.
Proof.
  intros. remember (fun g v (x: nat) => closure_has_v g v) as Q.
  remember (fun g1 g2 v => vertex_address g1 v = vertex_address g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - rewrite H2. assumption.
  - rewrite lcv_vertex_address; [reflexivity | assumption..].
  - apply (fr_closure_has_v _ _ _ _ _ _ H2 H3 _ H4).
  - apply lcv_closure_has_v; assumption.
Qed.

Lemma fl_vertex_address: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, closure_has_v g v -> vertex_address g v = vertex_address g' v.
Proof.
  intros. revert g g' H H0 v H1. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (vertex_address g2 v).
  - apply (fr_vertex_address _ _ _ _ _ _ H H5 _ H1).
  - apply IHl; [|assumption|].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_closure_has_v; eauto.
Qed.

Lemma lmc_block_fields: forall g old new x,
    block_fields (vlabel g x) = block_fields (vlabel (lgraph_mark_copied g old new) x).
Proof.
  intros. destruct (Addr_EqDec old x).
  - unfold equiv in e. subst. simpl. unfold update_copied_old_vlabel, update_vlabel.
    rewrite if_true by reflexivity. simpl. reflexivity.
  - assert (x <> old) by intuition.
    rewrite lmc_vlabel_not_eq; [reflexivity | assumption].
Qed.

Lemma lcv_block_fields: forall g v to x,
    graph_has_gen g to -> graph_has_v g x ->
    block_fields (vlabel g x) = block_fields (vlabel (lgraph_copy_v g v to) x).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_block_fields, lacv_vlabel_old.
  1: reflexivity. apply graph_has_v_not_eq; assumption.
Qed.

Lemma lcv_mfv_Zlen_eq: forall g v v' to,
    graph_has_gen g to ->
    graph_has_v g v ->
    Zlength (make_fields_vals g v) =
    Zlength (make_fields_vals (lgraph_copy_v g v' to) v).
Proof.
  intros. repeat rewrite fields_eq_length.
  rewrite <- lcv_block_fields by assumption; reflexivity.
Qed.

Lemma fr_block_fields: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v -> block_fields (vlabel g v) = block_fields (vlabel g' v).
Proof.
  intros. remember (fun (g: HeapGraph) (v: Addr) (x: nat) => graph_has_v g v) as Q.
  remember (fun (g1 g2: HeapGraph) v =>
              block_fields (vlabel g1 v) = block_fields (vlabel g2 v)) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - rewrite H2. apply H3.
  - rewrite <- lcv_block_fields; [reflexivity | assumption..].
  - apply (fr_graph_has_v _ _ _ _ _ _ H2 H3 _ H4).
  - apply lcv_graph_has_v_old; assumption.
Qed.

Lemma fl_block_fields: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, graph_has_v g v -> block_fields (vlabel g v) = block_fields (vlabel g' v).
Proof.
  intros. revert g g' H H0 v H1. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (block_fields (vlabel g2 v)).
  - apply (fr_block_fields _ _ _ _ _ _ H H5 _ H1).
  - apply IHl; [|assumption|].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
Qed.

Lemma lmc_block_mark: forall g old new x,
    x <> old -> block_mark (vlabel g x) =
                block_mark (vlabel (lgraph_mark_copied g old new) x).
Proof.
  intros. destruct (Addr_EqDec x old).
  - unfold equiv in e. contradiction.
  - rewrite lmc_vlabel_not_eq; [reflexivity | assumption].
Qed.

Lemma lcv_block_mark: forall g v to x,
    x <> v -> graph_has_gen g to -> graph_has_v g x ->
    block_mark (vlabel g x) = block_mark (vlabel (lgraph_copy_v g v to) x).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_block_mark by assumption.
  rewrite lacv_vlabel_old. 1: reflexivity. apply graph_has_v_not_eq; assumption.
Qed.

Lemma fr_block_mark: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v -> addr_gen v <> from ->
              block_mark (vlabel g v) = block_mark (vlabel g' v).
Proof.
  intros. remember (fun (g: HeapGraph) (v: Addr) (x: nat) =>
                      graph_has_v g v /\ addr_gen v <> x) as Q.
  remember (fun (g1 g2: HeapGraph) v =>
              block_mark (vlabel g1 v) = block_mark (vlabel g2 v)) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H3; clear H3; intros; try assumption; try reflexivity.
  - rewrite H3. apply H4.
  - destruct H4. rewrite <- lcv_block_mark; [reflexivity | try assumption..].
    destruct x, v0. simpl in *. intro. inversion H9. subst. contradiction.
  - destruct H5. split. 2: assumption.
    apply (fr_graph_has_v _ _ _ _ _ _ H3 H4 _ H5).
  - destruct H4. split. 2: assumption. apply lcv_graph_has_v_old; assumption.
  - split; assumption.
Qed.

Lemma fl_block_mark: forall depth from to l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, graph_has_v g v -> addr_gen v <> from ->
              block_mark (vlabel g v) = block_mark (vlabel g' v).
Proof.
  intros. revert g g' H H0 v H1 H2. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (block_mark (vlabel g2 v)).
  - apply (fr_block_mark _ _ _ _ _ _ H H6 _ H1 H2).
  - apply IHl; [|assumption| |assumption].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
Qed.

Lemma tir_trans: forall t1 t2 t3,
    thread_info_relation t1 t2 -> thread_info_relation t2 t3 ->
    thread_info_relation t1 t3.
Proof.
  intros. destruct H as [? [? ?]], H0 as [? [? ?]].
  split; [|split]; [rewrite H; assumption | intros; rewrite H1; apply H3|
                   intros; rewrite H2; apply H4].
Qed.

Lemma forward_loop_add_tail: forall from to depth l x g1 g2 g3 roots,
    forward_loop from to depth l g1 g2 ->
    forward_relation from to depth (forward_p2forward_t (inr x) roots g2) g2 g3 ->
    forward_loop from to depth (l +:: (inr x)) g1 g3.
Proof.
  intros. revert x g1 g2 g3 H H0. induction l; intros.
  - simpl. inversion H. subst. apply fl_cons with g3. 2: constructor. apply H0.
  - inversion H. subst. clear H. simpl app. apply fl_cons with g4. 1: assumption.
    apply IHl with g2; assumption.
Qed.

Lemma vpp_Zlength: forall g x,
    Zlength (vertex_pos_pairs g x) = Zlength (block_fields (vlabel g x)).
Proof.
  intros. unfold vertex_pos_pairs.
  rewrite Zlength_map, !Zlength_correct, nat_inc_list_length. reflexivity.
Qed.

Instance forward_p_type_Inhabitant: Inhabitant forward_p_type := inl 0.

Lemma vpp_Znth: forall (x : Addr) (g : HeapGraph) (i : Z),
    0 <= i < Zlength (block_fields (vlabel g x)) ->
    Znth i (vertex_pos_pairs g x) = inr (x, i).
Proof.
  intros. unfold vertex_pos_pairs.
  assert (0 <= i < Zlength (nat_inc_list (length (block_fields (vlabel g x))))) by
      (rewrite Zlength_correct, nat_inc_list_length, <- Zlength_correct; assumption).
  rewrite Znth_map by assumption. do 2 f_equal. rewrite <- nth_Znth by assumption.
  rewrite nat_inc_list_nth. 1: rewrite Z2Nat.id; lia.
  rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_lt; lia.
Qed.

Lemma forward_loop_add_tail_vpp: forall from to depth x g g1 g2 g3 roots i,
    0 <= i < Zlength (block_fields (vlabel g x)) ->
    forward_loop from to depth (sublist 0 i (vertex_pos_pairs g x)) g1 g2 ->
    forward_relation from to depth (forward_p2forward_t (inr (x, i)) roots g2) g2 g3 ->
    forward_loop from to depth (sublist 0 (i + 1) (vertex_pos_pairs g x)) g1 g3.
Proof.
  intros. rewrite <- vpp_Zlength in H. rewrite sublist_last_1; [|lia..].
  rewrite vpp_Zlength in H. rewrite vpp_Znth by assumption.
  apply forward_loop_add_tail with (g2 := g2) (roots := roots); assumption.
Qed.

Lemma lcv_vlabel_new: forall g v to,
    addr_gen v <> to ->
    vlabel (lgraph_copy_v g v to) (new_copied_v g to) = vlabel g v.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_vlabel_not_eq, lacv_vlabel_new;
    [| unfold new_copied_v; intro; apply H; inversion H0; simpl]; reflexivity.
Qed.

Inductive scan_vertex_for_loop (from to: nat) (v: Addr):
  list nat -> HeapGraph -> HeapGraph -> Prop :=
| svfl_nil: forall g, scan_vertex_for_loop from to v nil g g
| svfl_cons: forall g1 g2 g3 i il,
  forward_relation
    from to O (forward_p2forward_t (inr (v, (Z.of_nat i))) nil g1) g1 g2 ->
  scan_vertex_for_loop from to v il g2 g3 ->
  scan_vertex_for_loop from to v (i :: il) g1 g3.

Definition no_scan (g: HeapGraph) (v: Addr): Prop :=
  NO_SCAN_TAG <= (vlabel g v).(block_tag).

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

Definition gen_unmarked (g: HeapGraph) (gen: nat): Prop :=
  graph_has_gen g gen ->
  forall idx, gen_has_index g gen idx -> (vlabel g {| addr_gen := gen; addr_block := idx |}).(block_mark) = false.

Lemma lcv_graph_has_v_inv: forall (g : HeapGraph) (v : Addr) (to : nat) (x : Addr),
    graph_has_gen g to -> graph_has_v (lgraph_copy_v g v to) x ->
    graph_has_v g x \/ x = new_copied_v g to.
Proof.
  intros. unfold lgraph_copy_v in H0. rewrite <- lmc_graph_has_v in H0.
  apply (lacv_graph_has_v_inv g v); assumption.
Qed.

Lemma lcv_gen_unmarked: forall (to : nat) (g : HeapGraph) (v : Addr),
    graph_has_gen g to -> block_mark (vlabel g v) = false ->
    forall gen, addr_gen v <> gen ->
                gen_unmarked g gen -> gen_unmarked (lgraph_copy_v g v to) gen.
Proof.
  intros. unfold gen_unmarked in *. intros.
  assert (graph_has_v (lgraph_copy_v g v to) {| addr_gen := gen; addr_block := idx |}) by (split; assumption).
  apply lcv_graph_has_v_inv in H5. 2: assumption. destruct H5.
  - pose proof H5. destruct H6. simpl in * |- . specialize (H2 H6 _ H7).
    rewrite <- lcv_block_mark; try assumption. destruct v. simpl in *. intro. apply H1.
    inversion H8. reflexivity.
  - rewrite H5. rewrite lcv_vlabel_new; try assumption. unfold new_copied_v in H5.
    inversion H5. subst. assumption.
Qed.

Lemma fr_gen_unmarked: forall from to depth p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall gen, from  <> gen -> gen_unmarked g gen -> gen_unmarked g' gen.
Proof.
  intros. remember (fun (g: HeapGraph) (gen: nat) (x: nat) => x <> gen) as Q.
  remember (fun (g1 g2: HeapGraph) gen =>
              gen_unmarked g1 gen -> gen_unmarked g2 gen) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H3; clear H3; intros; try assumption; try reflexivity.
  - apply H4, H3. assumption.
  - rewrite <- H7 in H4. apply lcv_gen_unmarked; assumption.
Qed.

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

Lemma make_header_tag_prep64: forall z,
    0 <= z < two_p (8 * 8) ->
    Int64.and (Int64.repr z) (Int64.repr 255) =
    Int64.sub (Int64.repr z)
              (Int64.mul (Int64.repr (z / two_p 8)) (Int64.repr (two_p 8))).
Proof.
  intros. replace (Int64.repr 255) with (Int64.sub (Int64.repr 256) Int64.one) by
      now vm_compute.
  rewrite <- (Int64.modu_and _ _ (Int64.repr 8)) by now vm_compute.
  rewrite Int64.modu_divu by (vm_compute; intro S; inversion S).
  rewrite (Int64.divu_pow2 _ _ (Int64.repr 8)) by now vm_compute.
  rewrite (Int64.mul_pow2 _ _ (Int64.repr 8)) by now vm_compute.
  rewrite Int64.shru_div_two_p, !Int64.unsigned_repr; [| rep_lia | ].
  - rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia. easy.
  - simpl Z.mul in H. unfold Int64.max_unsigned, Int64.modulus.
    unfold Int64.wordsize, Wordsize_64.wordsize. rewrite two_power_nat_two_p.
    simpl Z.of_nat. lia.
Qed.

Lemma make_header_tag_prep32: forall z,
    0 <= z < two_p (4 * 8) ->
    Int.and (Int.repr z) (Int.repr 255) =
    Int.sub (Int.repr z)
              (Int.mul (Int.repr (z / two_p 8)) (Int.repr (two_p 8))).
Proof.
  intros. replace (Int.repr 255) with (Int.sub (Int.repr 256) Int.one) by
      now vm_compute.
  rewrite <- (Int.modu_and _ _ (Int.repr 8)) by now vm_compute.
  rewrite Int.modu_divu by (vm_compute; intro S; inversion S).
  rewrite (Int.divu_pow2 _ _ (Int.repr 8)) by now vm_compute.
  rewrite (Int.mul_pow2 _ _ (Int.repr 8)) by now vm_compute.
  rewrite Int.shru_div_two_p, !Int.unsigned_repr; [| rep_lia | ].
  - rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia. easy.
  - simpl Z.mul in H. unfold Int.max_unsigned, Int.modulus.
    unfold Int.wordsize, Wordsize_32.wordsize. rewrite two_power_nat_two_p.
    simpl Z.of_nat. lia.
Qed.

Lemma make_header_tag: forall g v,
    block_mark (vlabel g v) = false ->
    if Archi.ptr64 then
        Int64.and (Int64.repr (make_header g v)) (Int64.repr 255) =
        Int64.repr (block_tag (vlabel g v))
    else Int.and (Int.repr (make_header g v)) (Int.repr 255) =
         Int.repr (block_tag (vlabel g v)).
Proof.
  intros. cbv delta [Archi.ptr64]. simpl.
  first [rewrite make_header_tag_prep32 | rewrite make_header_tag_prep64].
  2: apply make_header_range.
  unfold make_header in *. remember (vlabel g v) as r eqn:E. clear E.
  rewrite H, !Zbits.Zshiftl_mul_two_p in * by lia. rewrite <- Z.add_assoc.
  replace (block_color r * two_p 8 + Zlength (block_fields r) * two_p 10)
    with ((block_color r + Zlength (block_fields r) * two_p 2) * two_p 8) by
      (rewrite Z.mul_add_distr_r, <- Z.mul_assoc, <- two_p_is_exp by lia;
       reflexivity). rewrite Z.div_add by (vm_compute; intros S; inversion S).
  assert (block_tag r / two_p 8 = 0) by (apply Z.div_small, block_tag__range).
  rewrite H0, Z.add_0_l.
  first [rewrite mul_repr, sub_repr | rewrite mul64_repr, sub64_repr].
  now rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
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

Lemma forward_p2t_inr_roots: forall v n roots g,
    forward_p2forward_t (inr (v, n)) roots g = forward_p2forward_t (inr (v, n)) nil g.
Proof. intros. simpl. reflexivity. Qed.

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

Lemma root_in_outlier: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier -> In p outlier.
Proof.
  intros. apply H0. rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff.
  assumption.
Qed.

Definition do_generation_relation (from to: nat) (f_info: fun_info)
           (roots roots': roots_t) (g g': HeapGraph): Prop := exists g1 g2,
    forward_roots_relation from to f_info roots g roots' g1 /\
    do_scan_relation from to (generation_block_count (nth_gen g to)) g1 g2 /\
    g' = reset_graph from g2.

Definition space_address (t_info: thread_info) (gen: nat) :=
  offset_val (SPACE_STRUCT_SIZE * Z.of_nat gen) (ti_heap_p t_info).

Definition enough_space_to_have_g g t_info from to: Prop :=
  graph_gen_size g from <= rest_gen_size t_info to.

Definition roots_fi_compatible (roots: roots_t) f_info: Prop :=
  Zlength roots = Zlength (live_roots_indices f_info) /\
  forall i j,
    0 <= i < Zlength roots -> 0 <= j < Zlength roots ->
    Znth i (live_roots_indices f_info) = Znth j (live_roots_indices f_info) ->
    Znth i roots = Znth j roots.

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


Lemma frl_roots_Zlength: forall from to f_info l roots g roots' g',
    Zlength roots = Zlength (live_roots_indices f_info) ->
    forward_roots_loop from to f_info l roots g roots' g' ->
    Zlength roots' = Zlength roots.
Proof.
  intros. induction H0. 1: reflexivity. rewrite IHforward_roots_loop.
  - apply upd_roots_Zlength; assumption.
  - rewrite upd_roots_Zlength; assumption.
Qed.

Opaque upd_roots.

Lemma frl_add_tail: forall from to f_info l i g1 g2 g3 roots1 roots2,
    forward_roots_loop from to f_info l roots1 g1 roots2 g2 ->
    forward_relation from to O (root2forward (Znth (Z.of_nat i) roots2)) g2 g3 ->
    forward_roots_loop
      from to f_info (l +:: i) roots1 g1
      (upd_roots from to (inl (Z.of_nat i)) g2 roots2 f_info) g3.
Proof.
  intros ? ? ? ?. induction l; intros.
  - simpl. inversion H. subst. apply frl_cons with g3. 2: constructor. apply H0.
  - inversion H. subst. clear H. simpl app. apply frl_cons with g4. 1: assumption.
    apply IHl; assumption.
Qed.

Transparent upd_roots.

Lemma frr_vertex_address: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, closure_has_v g1 v -> vertex_address g1 v = vertex_address g2 v.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_vertex_address; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_closure_has_v; eauto.
Qed.

Lemma frr_closure_has_v: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, closure_has_v g1 v -> closure_has_v g2 v.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_loop.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_closure_has_v; eauto.
Qed.

Lemma frr_gen_unmarked: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, gen <> from -> gen_unmarked g1 gen -> gen_unmarked g2 gen.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_loop.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_gen_unmarked; eauto.
Qed.


Lemma graph_thread_info_compatible_reset: forall g t_info gen,
    graph_thread_info_compatible g t_info ->
    graph_thread_info_compatible (reset_graph gen g)
                                 (reset_nth_heap_thread_info gen t_info).
Proof.
  intros. destruct H as [? [? ?]].
  split; [|split]; [|simpl; rewrite reset_nth_gen_info_length..].
  - rewrite gsc_iff by
        (simpl; rewrite remove_ve_glabel_unchanged, reset_nth_space_length,
                reset_nth_gen_info_length; assumption).
    intros n ?. rewrite gsc_iff in H by assumption. rewrite graph_has_gen_reset in H2.
    specialize (H _ H2). red in H. simpl. unfold nth_gen, nth_space in *. simpl.
    rewrite remove_ve_glabel_unchanged. destruct (Nat.eq_dec n gen).
    + subst gen. red in H2. rewrite reset_nth_gen_info_same.
      rewrite reset_nth_space_same by lia. intuition.
    + rewrite reset_nth_gen_info_diff, reset_nth_space_diff by assumption.
      destruct H as [? [? ?]]. split. 1: assumption. split. 1: assumption.
      rewrite pvs_reset_unchanged. assumption.
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

Lemma upd_bunch_rf_compatible: forall f_info roots z r,
    roots_fi_compatible roots f_info ->
    roots_fi_compatible (upd_bunch z f_info roots r) f_info.
Proof.
  intros. unfold roots_fi_compatible in *. destruct H.
  assert (Zlength (upd_bunch z f_info roots r) = Zlength (live_roots_indices f_info))
    by (rewrite upd_bunch_Zlength; assumption). split; intros. 1: assumption.
  rewrite H1 in *. rewrite <- H in *.
  destruct (Z.eq_dec (Znth i (live_roots_indices f_info))
                     (Znth z (live_roots_indices f_info))).
  - rewrite !upd_bunch_same; try assumption; try reflexivity.
    rewrite H4 in e; assumption.
  - rewrite !upd_bunch_diff; try assumption; [apply H0 | rewrite <- H4]; assumption.
Qed.

Lemma upd_roots_rf_compatible: forall from to f_info roots p g,
    roots_fi_compatible roots f_info ->
    roots_fi_compatible (upd_roots from to p g roots f_info) f_info.
Proof.
  intros. unfold upd_roots. destruct p; [|assumption]. destruct (Znth z roots).
  1: destruct s; assumption. if_tac. 2: assumption.
  destruct (block_mark (vlabel g a)); apply upd_bunch_rf_compatible; assumption.
Qed.

Definition np_roots_rel from f_info (roots roots': roots_t) (l: list Z) : Prop :=
  let lri := live_roots_indices f_info in
  let maped_lri := (map (flip Znth lri) l) in
  forall v j, Znth j roots' = inr v ->
              (In (Znth j lri) maped_lri -> addr_gen v <> from) /\
              (~ In (Znth j lri) maped_lri -> Znth j roots = inr v).

Lemma upd_roots_not_pointing: forall from to i g roots f_info roots',
    copy_compatible g -> roots_graph_compatible roots g -> from <> to ->
    0 <= i < Zlength roots -> roots_fi_compatible roots f_info ->
    roots' = upd_roots from to (inl i) g roots f_info ->
    np_roots_rel from f_info roots roots' [i].
Proof.
  intros. unfold np_roots_rel. intros. simpl. unfold flip.
  assert (Zlength roots' = Zlength roots) by
      (rewrite H4; apply upd_roots_Zlength, (proj1 H3)).
  assert (0 <= j < Zlength roots). {
    rewrite <- H6. destruct (Z_lt_le_dec j (Zlength roots')).
    2: rewrite Znth_outofbounds in H5 by lia; inversion H5. split; auto.
    destruct (Z_lt_le_dec j 0); auto. rewrite Znth_outofbounds in H5 by lia.
    inversion H5. } simpl in H4. destruct H3. destruct (Znth i roots) eqn:? .
  - assert (roots' = roots) by (destruct s; assumption). clear H4. subst roots'.
    split; intros; auto. destruct H4; auto.
    destruct H3. apply H8 in H4; try assumption. rewrite Heqr, H5 in H4. inversion H4.
  - if_tac in H4.
    + destruct (block_mark (vlabel g a)) eqn: ?; subst; split; intros.
      * destruct H4; auto. symmetry in H4. rewrite upd_bunch_same in H5 by assumption.
        inversion H5. red in H0. rewrite Forall_forall in H0.
        assert (graph_has_v g a). {
          apply H0. rewrite <- filter_sum_right_In_iff, <- Heqr.
          apply Znth_In; assumption. } destruct (H _ H9 Heqb) as [_ ?]. auto.
      * assert (Znth j (live_roots_indices f_info) <>
                Znth i (live_roots_indices f_info)) by intuition. clear H4.
        rewrite upd_bunch_diff in H5; assumption.
      * destruct H4; auto. symmetry in H4. rewrite upd_bunch_same in H5 by assumption.
        inversion H5. unfold new_copied_v. simpl. auto.
      * assert (Znth j (live_roots_indices f_info) <>
                Znth i (live_roots_indices f_info)) by intuition. clear H4.
        rewrite upd_bunch_diff in H5; assumption.
    + split; intros; subst roots'; auto. destruct H10; auto.
      apply H8 in H4; try assumption. rewrite Heqr, H5 in H4. inversion H4.
      subst a. assumption.
Qed.

Lemma np_roots_rel_cons: forall roots1 roots2 roots3 from f_info i l,
    np_roots_rel from f_info roots1 roots2 [i] ->
    np_roots_rel from f_info roots2 roots3 l ->
    np_roots_rel from f_info roots1 roots3 (i :: l).
Proof.
  intros. unfold np_roots_rel in *. intros. simpl. specialize (H0 _ _ H1).
  destruct H0. split; intros; unfold flip in H2 at 1.
  - destruct (in_dec Z.eq_dec (Znth j (live_roots_indices f_info))
                     (map (flip Znth (live_roots_indices f_info)) l)).
    1: apply H0; assumption. destruct H3. 2: contradiction. unfold flip in H3.
    specialize (H2 n). specialize (H _ _ H2). destruct H. apply H. simpl. unfold flip.
    left; assumption.
  - unfold flip in H3 at 1. apply Decidable.not_or in H3. destruct H3.
    specialize (H2 H4). specialize (H _ _ H2). destruct H. apply H5. simpl. tauto.
Qed.

Lemma fr_copy_compatible: forall depth from to p g g',
    from <> to -> graph_has_gen g to -> forward_relation from to depth p g g' ->
    copy_compatible g -> copy_compatible g'.
Proof.
  intros. remember (fun (g: HeapGraph) (v: Addr) (x: nat) => True) as Q.
  remember (fun g1 g2 (v: Addr) => copy_compatible g1 -> copy_compatible g2) as P.
  remember (fun (x y: nat) => x <> y) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H3; clear H3; intros; try assumption; try reflexivity.
  - apply H4, H3. assumption.
  - subst from0. apply lcv_copy_compatible; auto.
  - exact {| addr_gen := O; addr_block := O |}.
Qed.

Lemma fr_right_roots_graph_compatible: forall depth from to e g g' roots,
    graph_has_gen g to -> forward_p_compatible (inr e) roots g from ->
    forward_relation from to depth (forward_p2forward_t (inr e) [] g) g g' ->
    roots_graph_compatible roots g -> roots_graph_compatible roots g'.
Proof.
  intros. simpl in H1, H0. destruct e. destruct H0 as [_ [_ [? _]]]. rewrite H0 in H1.
  simpl in H1. remember (fun (g: HeapGraph) (v: nat) (x: nat) => True) as Q.
  remember (fun g1 g2 (x: nat) => roots_graph_compatible roots g1->
                                  roots_graph_compatible roots g2) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop
                depth from to (field2forward (Znth z (make_fields g a))) g g' _ Q P R).
  subst Q P R. apply H3; clear H3; intros; try assumption; try reflexivity.
  - apply H4, H3. assumption.
  - apply lcv_rgc_unchanged; assumption.
Qed.

Lemma fl_edge_roots_graph_compatible: forall depth from to l g g' v roots,
    addr_gen v <> from ->
    graph_has_gen g to -> graph_has_v g v -> block_mark (vlabel g v) = false ->
    forward_loop from to depth (map (fun x : nat => inr (v, Z.of_nat x)) l) g g' ->
    (forall i, In i l -> i < length (block_fields (vlabel g v)))%nat ->
    roots_graph_compatible roots g -> roots_graph_compatible roots g'.
Proof.
  do 4 intro. induction l; intros; simpl in H3; inversion H3; subst. 1: assumption.
  cut (roots_graph_compatible roots g2).
  - intros. apply (IHl g2 _ v); try assumption.
    + rewrite <- fr_graph_has_gen; eauto.
    + eapply fr_graph_has_v; eauto.
    + rewrite <- H2. symmetry. eapply fr_block_mark; eauto.
    + assert (block_fields (vlabel g v) = block_fields (vlabel g2 v)) by
          (eapply fr_block_fields; eauto). rewrite <- H7.
      intros; apply H4; right; assumption.
  - specialize (H4 _ (in_eq a l)). eapply fr_right_roots_graph_compatible; eauto.
    simpl. intuition. rewrite Zlength_correct. apply inj_lt; assumption.
Qed.

Lemma fr_roots_outlier_compatible: forall from to p g roots f_info outlier,
    roots_outlier_compatible roots outlier ->
    roots_outlier_compatible (upd_roots from to p g roots f_info) outlier.
Proof.
  intros. destruct p; simpl in *. 2: assumption. destruct (Znth z roots) eqn: ?.
  + destruct s; assumption.
  + if_tac. 2: assumption.
    destruct (block_mark (vlabel g a)); apply upd_roots_outlier_compatible; assumption.
Qed.

Lemma fr_roots_graph_compatible (depth from to: nat) (p : forward_p_type) (g g' : HeapGraph) (roots : roots_t) (f_info : fun_info)
    (Hto: graph_has_gen g to)
    (Hp: forward_p_compatible p roots g from)
    (Hg: copy_compatible g)
    (Hfwd: forward_relation from to depth (forward_p2forward_t p roots g) g g')
    (Hfrom_to: from <> to)
    (Hroots: roots_graph_compatible roots g):
    roots_graph_compatible (upd_roots from to p g roots f_info) g'.
Proof.
  destruct p.
  - simpl in *. destruct (Znth z roots) eqn: ?; simpl in *.
    + destruct s; inversion Hfwd; subst; assumption.
    + assert (graph_has_v g a). {
        red in Hroots. rewrite Forall_forall in Hroots. apply Hroots.
        rewrite <- filter_sum_right_In_iff. rewrite <- Heqr. apply Znth_In.
        assumption. }
      inversion Hfwd ; destruct (Nat.eq_dec (addr_gen v) from) eqn:HE_v_from ; subst ; rewrite HE_v_from ; try easy.
      * rename H3 into Eblock_mark ; rewrite Eblock_mark.
        apply upd_bunch_graph_compatible ; try assumption.
        now apply Hg.
      * rename H3 into Eblock_mark ; rewrite Eblock_mark.
        now apply lcv_roots_graph_compatible.
      * rename H2 into Eblock_mark ; rewrite Eblock_mark.
        assert (graph_has_v new_g (new_copied_v g to)) by
          (subst new_g; apply lcv_graph_has_v_new; assumption).
        remember (nat_inc_list (length (block_fields (vlabel new_g (new_copied_v g to))))) as new_fields.
        assert (graph_has_v new_g (new_copied_v g to)) by (subst new_g; apply lcv_graph_has_v_new; assumption).
        remember (upd_bunch z f_info roots (inr (new_copied_v g to))) as roots'.
        assert (roots_graph_compatible roots' new_g) by (subst; subst new_g; apply lcv_roots_graph_compatible; assumption).
        assert (block_mark (vlabel new_g (new_copied_v g to)) = false). {
          subst new_g. unfold lgraph_copy_v. rewrite <- lmc_block_mark.
          - now rewrite lacv_vlabel_new.
          - unfold new_copied_v. destruct a. destruct Heqroots'. simpl in *.
            red in H1. intro HS. inversion HS. lia. }
        eapply (fl_edge_roots_graph_compatible depth0 (addr_gen a) to new_fields new_g _ (new_copied_v g to)) ; eauto.
        -- subst new_g. now rewrite <- lcv_graph_has_gen.
        -- now subst new_fields.
        -- intros idx Hidx. subst new_fields. now rewrite nat_inc_list_In_iff in Hidx.
  - simpl. eapply fr_right_roots_graph_compatible; eauto.
Qed.

Lemma fr_roots_compatible: forall depth from to p g g' roots f_info outlier,
    graph_has_gen g to -> forward_p_compatible p roots g from -> copy_compatible g ->
    forward_relation from to depth (forward_p2forward_t p roots g) g g' ->
    roots_compatible g outlier roots -> from <> to ->
    roots_compatible g' outlier (upd_roots from to p g roots f_info).
Proof.
  intros. destruct H3. split.
  - apply fr_roots_outlier_compatible; assumption.
  - eapply fr_roots_graph_compatible; eauto.
Qed.

Lemma frl_not_pointing: forall from to f_info l roots1 g1 roots2 g2,
    copy_compatible g1 -> roots_graph_compatible roots1 g1 -> from <> to ->
    (forall i, In i l -> i < length roots1)%nat -> roots_fi_compatible roots1 f_info ->
    forward_roots_loop from to f_info l roots1 g1 roots2 g2 -> graph_has_gen g1 to ->
    np_roots_rel from f_info roots1 roots2 (map Z.of_nat l).
Proof.
  do 4 intro. induction l; intros; inversion H4; subst.
  1: red; simpl; intros; intuition.
  remember (upd_roots from to (inl (Z.of_nat a)) g1 roots1 f_info) as roots3.
  simpl. apply np_roots_rel_cons with roots3.
  - apply (upd_roots_not_pointing from to _ g1); try assumption.
    split. 1: lia. rewrite Zlength_correct. apply inj_lt. apply H2. left; auto.
  - assert (Zlength roots3 = Zlength roots1) by
        (subst roots3; apply upd_roots_Zlength; apply (proj1 H3)).
    apply (IHl _ g3 _ g2); auto.
    + apply fr_copy_compatible in H8; assumption.
    + subst roots3. eapply fr_roots_graph_compatible; eauto. simpl. split. 1: lia.
      specialize (H2 _ (in_eq a l)). rewrite Zlength_correct. apply inj_lt; assumption.
    + intros. subst roots3. rewrite <- ZtoNat_Zlength, H6, ZtoNat_Zlength.
      apply H2; right; assumption.
    + subst roots3; apply upd_roots_rf_compatible; assumption.
    + rewrite <- (fr_graph_has_gen _ _ _ _ _ _ H5 H8); assumption.
Qed.

Definition roots_have_no_gen (roots: roots_t) (gen: nat): Prop :=
  forall v, In (inr v) roots -> addr_gen v <> gen.

Lemma frr_not_pointing: forall from to f_info roots1 g1 roots2 g2,
    copy_compatible g1 -> roots_graph_compatible roots1 g1 -> from <> to ->
    graph_has_gen g1 to -> roots_fi_compatible roots1 f_info ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    roots_have_no_gen roots2 from.
Proof.
  intros. unfold forward_roots_relation in H0. eapply frl_not_pointing in H0; eauto.
  red; intros. 2: intros; rewrite nat_inc_list_In_iff in H5; assumption. red in H0.
  apply In_Znth in H5. destruct H5 as [i [? ?]]. specialize (H0 _ _ H6). destruct H0.
  apply H0. destruct H3 as [? _].
  replace (length roots1) with (length (live_roots_indices f_info)) by
      (rewrite <- !ZtoNat_Zlength, H3; reflexivity).
  remember (live_roots_indices f_info). rewrite map_map. unfold flip.
  assert (map (fun x : nat => Znth (Z.of_nat x) l) (nat_inc_list (length l)) = l). {
    clear. rewrite Znth_list_eq. split.
    - rewrite Zlength_map, !Zlength_correct, nat_inc_list_length. reflexivity.
    - intros. rewrite Zlength_map in H. rewrite Znth_map by assumption. f_equal.
      rewrite <- nth_Znth by assumption. rewrite nat_inc_list_nth.
      1: apply Z2Nat.id; lia. rewrite Zlength_correct, nat_inc_list_length in H.
      rep_lia. } rewrite H8. clear H8. apply Znth_In. apply frl_roots_Zlength in H4.
  2: subst; assumption. rewrite <- H3, <- H4. assumption.
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
  apply vertex_address_reset.
Qed.

Lemma gen_has_index_reset: forall (g: HeapGraph) gen1 gen2 idx,
    gen_has_index (reset_graph gen1 g) gen2 idx <->
    gen_has_index g gen2 idx /\ gen1 <> gen2.
Proof.
  intros. unfold gen_has_index. unfold nth_gen. simpl.
  rewrite remove_ve_glabel_unchanged. destruct (Nat.eq_dec gen1 gen2).
  - subst. rewrite reset_nth_gen_info_same. simpl. intuition.
  - rewrite reset_nth_gen_info_diff by auto. intuition.
Qed.

Lemma graph_has_v_reset: forall (g: HeapGraph) gen v,
    graph_has_v (reset_graph gen g) v <->
    graph_has_v g v /\ gen <> addr_gen v.
Proof.
  intros. split; intros; destruct v; unfold graph_has_v in *; simpl in *.
  - rewrite graph_has_gen_reset, gen_has_index_reset in H. intuition.
  - rewrite graph_has_gen_reset, gen_has_index_reset. intuition.
Qed.

Lemma rgc_reset: forall g gen roots,
    roots_graph_compatible roots g ->
    roots_have_no_gen roots gen ->
    roots_graph_compatible roots (reset_graph gen g).
Proof.
  intros. red in H |-*. rewrite Forall_forall in *. intros.
  specialize (H _ H1). destruct H. split.
  - rewrite graph_has_gen_reset. assumption.
  - rewrite gen_has_index_reset. split. 1: assumption.
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
  rewrite graph_has_v_reset in H0. destruct H0. assumption.
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
  intros. split; simpl. 1: reflexivity.
  unfold gen_size, nth_space. simpl.
  destruct (le_lt_dec (length (heap_spaces (ti_heap t_info))) gen).
  - rewrite reset_nth_space_overflow by assumption. split; intros; reflexivity.
  - split; intros; destruct (Nat.eq_dec n gen).
    + subst. rewrite reset_nth_space_same; simpl; [reflexivity | assumption].
    + rewrite reset_nth_space_diff; [reflexivity | assumption].
    + subst. rewrite reset_nth_space_same; simpl; [reflexivity | assumption].
    + rewrite reset_nth_space_diff; [reflexivity | assumption].
Qed.

Lemma frr_graph_has_gen: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, graph_has_gen g1 gen <-> graph_has_gen g2 gen.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_graph_has_gen; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
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

Definition graph_unmarked (g: HeapGraph): Prop := forall v,
    graph_has_v g v -> block_mark (vlabel g v) = false.

Lemma graph_gen_unmarked_iff: forall g,
    graph_unmarked g <-> forall gen, gen_unmarked g gen.
Proof.
  intros. unfold graph_unmarked, gen_unmarked. split; intros.
  - apply H. unfold graph_has_v. simpl. split; assumption.
  - destruct v as [gen idx]. destruct H0. simpl in *. apply H; assumption.
Qed.

Lemma graph_unmarked_copy_compatible: forall g,
    graph_unmarked g -> copy_compatible g.
Proof.
  intros. red in H |-* . intros. apply H in H0. rewrite H0 in H1. inversion H1.
Qed.

Lemma gen_unmarked_reset_same: forall g gen,
    gen_unmarked (reset_graph gen g) gen.
Proof.
  intros. red. intros. rewrite graph_has_gen_reset in H.
  rewrite gen_has_index_reset in H0. destruct H0. contradiction.
Qed.

Lemma gen_unmarked_reset_diff: forall g gen1 gen2,
    gen_unmarked g gen2 -> gen_unmarked (reset_graph gen1 g) gen2.
Proof.
  intros. unfold gen_unmarked in *. intros. rewrite graph_has_gen_reset in H0.
  rewrite gen_has_index_reset in H1. destruct H1. specialize (H H0 _ H1). simpl.
  rewrite remove_ve_vlabel_unchanged. assumption.
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

Definition graph_has_e (g: HeapGraph) (e: Field): Prop :=
  let v := field_addr e in graph_has_v g v /\ In e (get_edges g v).

Definition gen2gen_no_edge (g: HeapGraph) (gen1 gen2: nat): Prop :=
  forall vidx eidx, let e := {| field_addr := {| addr_gen := gen1; addr_block := vidx |}; field_index := eidx |} in
                    graph_has_e g e -> addr_gen (dst g e) <> gen2.

Definition no_edge2gen (g: HeapGraph) (gen: nat): Prop :=
  forall another, another <> gen -> gen2gen_no_edge g another gen.

Definition egeneration (e: Field): nat := addr_gen (field_addr e).

Lemma get_edges_reset: forall g gen v,
    get_edges (reset_graph gen g) v = get_edges g v.
Proof.
  intros. unfold get_edges, make_fields. simpl. rewrite remove_ve_vlabel_unchanged.
  reflexivity.
Qed.

Lemma graph_has_e_reset: forall g gen e,
    graph_has_e (reset_graph gen g) e <->
    graph_has_e g e /\ gen <> egeneration e.
Proof.
  intros. unfold graph_has_e, egeneration. destruct e as [v idx]. simpl.
  rewrite graph_has_v_reset, get_edges_reset. intuition.
Qed.

Lemma gen2gen_no_edge_reset_inv: forall g gen1 gen2 gen3,
    gen1 <> gen2 -> gen2gen_no_edge (reset_graph gen1 g) gen2 gen3 ->
    gen2gen_no_edge g gen2 gen3.
Proof.
  intros. unfold gen2gen_no_edge. intros. red in H0. simpl in H0.
  specialize (H0 vidx eidx). rewrite remove_ve_dst_unchanged in H0. apply H0.
  rewrite graph_has_e_reset. unfold egeneration. simpl. split; assumption.
Qed.

Lemma gen2gen_no_edge_reset: forall g gen1 gen2 gen3,
    gen2gen_no_edge g gen2 gen3 ->
    gen2gen_no_edge (reset_graph gen1 g) gen2 gen3.
Proof.
  intros. unfold gen2gen_no_edge. intros. simpl. rewrite remove_ve_dst_unchanged.
  apply H. rewrite graph_has_e_reset in H0. destruct H0. assumption.
Qed.

Lemma fr_O_dst_unchanged_root: forall from to r g g',
    forward_relation from to O (root2forward r) g g' ->
    forall e, graph_has_v g (field_addr e) -> dst g e = dst g' e.
Proof.
  intros. destruct r; [destruct s|]; simpl in H; inversion H; subst; try reflexivity.
  simpl. rewrite pcv_dst_old. 1: reflexivity. destruct e as [[gen vidx] eidx].
  unfold graph_has_v in H0. unfold new_copied_v. simpl in *. destruct H0. intro.
  inversion H2. subst. red in H1. lia.
Qed.

Lemma frr_dst_unchanged: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall e, graph_has_v g1 (field_addr e) -> dst g1 e = dst g2 e.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_O_dst_unchanged_root; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
Qed.

Lemma fr_O_graph_has_v_inv: forall from to p g g',
    graph_has_gen g to -> forward_relation from to O p g g' ->
    forall v, graph_has_v g' v -> graph_has_v g v \/ v = new_copied_v g to.
Proof.
  intros. inversion H0; subst; try (left; assumption);
            [|subst new_g; rewrite <- lgd_graph_has_v in H1];
            apply lcv_graph_has_v_inv in H1; assumption.
Qed.

Definition gen_v_num (g: HeapGraph) (gen: nat): nat := generation_block_count (nth_gen g gen).

Definition nth_gen_size (n: nat) := NURSERY_SIZE * two_p (Z.of_nat n).

Definition nth_gen_size_spec (tinfo: thread_info) (n: nat): Prop :=
  if Val.eq (nth_space tinfo n).(space_base) nullval
  then True
  else gen_size tinfo n = nth_gen_size n.

Definition ti_size_spec (tinfo: thread_info): Prop :=
  Forall (nth_gen_size_spec tinfo) (nat_inc_list (Z.to_nat MAX_SPACES)).

Definition safe_to_copy_gen g from to: Prop :=
  nth_gen_size from <= nth_gen_size to - graph_gen_size g to.

Lemma ngs_range: forall i,
    0 <= i < MAX_SPACES -> 0 <= nth_gen_size (Z.to_nat i) < MAX_SPACE_SIZE.
Proof.
  intros. unfold nth_gen_size. rewrite MAX_SPACES_eq in H.
  rewrite Z2Nat.id, NURSERY_SIZE_eq, Zbits.Zshiftl_mul_two_p,
  Z.mul_1_l, <- two_p_is_exp by lia. split.
  - cut (two_p (16 + i) > 0). 1: intros; lia. apply two_p_gt_ZERO. lia.
  - transitivity (two_p 28). 1: apply two_p_monotone_strict; lia.
    vm_compute. reflexivity.
Qed.

Lemma ngs_int_singed_range: forall i,
    0 <= i < MAX_SPACES ->
    (if Archi.ptr64 then Int64.min_signed else Int.min_signed) <=
    nth_gen_size (Z.to_nat i) <=
    (if Archi.ptr64 then Int64.max_signed else Int.max_signed).
Proof.
  intros. apply ngs_range in H. destruct H. split.
  - transitivity 0. 2: assumption. vm_compute. intro HS; inversion HS.
  - apply Z.lt_le_incl. transitivity MAX_SPACE_SIZE. 1: assumption.
    unfold MAX_SPACE_SIZE. vm_compute. reflexivity.
Qed.

Lemma ngs_S: forall i,
    0 <= i -> 2 * nth_gen_size (Z.to_nat i) = nth_gen_size (Z.to_nat (i + 1)).
Proof.
  intros. unfold nth_gen_size. rewrite !Z2Nat.id by lia.
  rewrite Z.mul_comm, <- Z.mul_assoc, (Z.mul_comm (two_p i)), <- two_p_S by assumption.
  reflexivity.
Qed.

Lemma space_base_isptr: forall (g: HeapGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (heap_spaces (ti_heap t_info)) ->
    graph_has_gen g (Z.to_nat i) ->
    isptr (space_base (Znth i (heap_spaces (ti_heap t_info)))).
Proof.
  intros. destruct (gt_gs_compatible _ _ H _ H1) as [? _].
  rewrite nth_space_Znth in H2. rewrite Z2Nat.id in H2 by lia. rewrite <- H2.
  apply generation_base__isptr.
Qed.

Lemma space_base_isnull: forall (g: HeapGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (heap_spaces (ti_heap t_info)) ->
    ~ graph_has_gen g (Z.to_nat i) ->
    space_base (Znth i (heap_spaces (ti_heap t_info))) = nullval.
Proof.
  intros. unfold graph_has_gen in H1. destruct H as [_ [? ?]].
  rewrite Forall_forall in H. symmetry. apply H. rewrite <- map_skipn.
  apply List.in_map. remember (generations (glabel g)).
  replace i with (i - Zlength l + Zlength l) by lia.
  assert (length l <= Z.to_nat i)%nat by lia. clear H1.
  assert (0 <= i - Zlength l) by
      (rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_le in H3; rep_lia).
  rewrite <- Znth_skipn by rep_lia. rewrite ZtoNat_Zlength.
  apply Znth_In. split. 1: assumption. rewrite <- ZtoNat_Zlength, Zlength_skipn.
  rewrite (Z.max_r 0 (Zlength l)) by rep_lia. rewrite Z.max_r; rep_lia.
Qed.

Lemma space_base_is_pointer_or_null: forall (g: HeapGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (heap_spaces (ti_heap t_info)) ->
    is_pointer_or_null (space_base (Znth i (heap_spaces (ti_heap t_info)))).
Proof.
  intros. destruct (graph_has_gen_dec g (Z.to_nat i)).
  - apply val_lemmas.isptr_is_pointer_or_null. eapply space_base_isptr; eauto.
  - cut (space_base (Znth i (heap_spaces (ti_heap t_info))) = nullval).
    + intros. rewrite H1. apply mapsto_memory_block.is_pointer_or_null_nullval.
    + eapply space_base_isnull; eauto.
Qed.

Lemma space_base_isptr_iff: forall (g: HeapGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (heap_spaces (ti_heap t_info)) ->
    graph_has_gen g (Z.to_nat i) <->
    isptr (space_base (Znth i (heap_spaces (ti_heap t_info)))).
Proof.
  intros. split; intros.
  - eapply space_base_isptr; eauto.
  - destruct (graph_has_gen_dec g (Z.to_nat i)). 1: assumption. exfalso.
    eapply space_base_isnull in n; eauto. rewrite n in H1. inversion H1.
Qed.

Lemma space_base_isnull_iff: forall (g: HeapGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (heap_spaces (ti_heap t_info)) ->
    ~ graph_has_gen g (Z.to_nat i) <->
    space_base (Znth i (heap_spaces (ti_heap t_info))) = nullval.
Proof.
  intros. split; intros. 1: eapply space_base_isnull; eauto.
  destruct (graph_has_gen_dec g (Z.to_nat i)). 2: assumption. exfalso.
  eapply space_base_isptr in g0; eauto. rewrite H1 in g0. inversion g0.
Qed.

Lemma ti_size_gen: forall (g : HeapGraph) (t_info : thread_info) (gen : nat),
    graph_thread_info_compatible g t_info ->
    graph_has_gen g gen -> ti_size_spec t_info ->
    gen_size t_info gen = nth_gen_size gen.
Proof.
  intros. red in H1. rewrite Forall_forall in H1.
  assert (0 <= (Z.of_nat gen) < Zlength (heap_spaces (ti_heap t_info))). {
    split. 1: rep_lia. rewrite Zlength_correct. apply inj_lt.
    destruct H as [_ [_ ?]]. red in H0. lia. }
  assert (nth_gen_size_spec t_info gen). {
    apply H1. rewrite nat_inc_list_In_iff. destruct H as [_ [_ ?]]. red in H0.
    rewrite <- (heap_spaces__size (ti_heap t_info)), ZtoNat_Zlength. lia. } red in H3.
  destruct (Val.eq (space_base (nth_space t_info gen)) nullval). 2: assumption.
  rewrite nth_space_Znth in e. erewrite <- space_base_isnull_iff in e; eauto.
  unfold graph_has_gen in e. exfalso; apply e. rewrite Nat2Z.id. assumption.
Qed.

Lemma ti_size_gt_0: forall (g : HeapGraph) (t_info : thread_info) (gen : nat),
    graph_thread_info_compatible g t_info ->
    graph_has_gen g gen -> ti_size_spec t_info -> 0 < gen_size t_info gen.
Proof.
  intros. erewrite ti_size_gen; eauto. unfold nth_gen_size. apply Z.mul_pos_pos.
  - rewrite NURSERY_SIZE_eq. vm_compute. reflexivity.
  - cut (two_p (Z.of_nat gen) > 0). 1: lia. apply two_p_gt_ZERO. lia.
Qed.

Local Close Scope Z_scope.

Lemma lcv_gen_v_num_to: forall g v to,
    graph_has_gen g to -> gen_v_num g to <= gen_v_num (lgraph_copy_v g v to) to.
Proof.
  intros. unfold gen_v_num, nth_gen; simpl. rewrite cvmgil_eq by assumption.
  simpl. lia.
Qed.

Lemma lgd_gen_v_num_to: forall g e v to,
    gen_v_num (labeledgraph_gen_dst g e v) to = gen_v_num g to.
Proof. intros. reflexivity. Qed.

Lemma fr_O_gen_v_num_to: forall from to p g g',
    graph_has_gen g to -> forward_relation from to O p g g' ->
    gen_v_num g to <= gen_v_num g' to.
Proof.
  intros. inversion H0; subst; try lia; [|subst new_g..].
  - apply lcv_gen_v_num_to; auto.
  - rewrite lgd_gen_v_num_to. lia.
  - rewrite lgd_gen_v_num_to. apply lcv_gen_v_num_to. assumption.
Qed.

Lemma frr_gen_v_num_to: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    gen_v_num g1 to <= gen_v_num g2 to.
Proof.
  intros. induction H0. 1: lia. transitivity (gen_v_num g2 to).
  - eapply fr_O_gen_v_num_to; eauto.
  - apply IHforward_roots_loop; rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma frr_graph_has_v_inv: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, graph_has_v g2 v -> graph_has_v g1 v \/
                                  (addr_gen v = to /\
                                   gen_v_num g1 to <= addr_block v < gen_v_num g2 to).
Proof.
  intros. induction H0. 1: left; assumption.
  assert (graph_has_gen g2 to) by (rewrite <- fr_graph_has_gen; eauto).
  specialize (IHforward_roots_loop H3 H1). destruct IHforward_roots_loop.
  - eapply (fr_O_graph_has_v_inv from to _ g1 g2) in H0; eauto. destruct H0.
    1: left; assumption. right. unfold new_copied_v in H0. subst v.
    clear H2. destruct H1. red in H1. simpl in *. unfold gen_v_num. lia.
  - right. destruct H4. split. 1: assumption. destruct H5. split. 2: assumption.
    apply fr_O_gen_v_num_to in H0; [lia | assumption].
Qed.

Lemma frr_block_fields: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, graph_has_v g1 v -> block_fields (vlabel g1 v) = block_fields (vlabel g2 v).
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_block_fields; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
Qed.

Lemma frr_gen2gen_no_edge: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen1 gen2, gen1 <> to -> gen2gen_no_edge g1 gen1 gen2 ->
                      gen2gen_no_edge g2 gen1 gen2.
Proof.
  intros. unfold gen2gen_no_edge in *. intros.
  cut (graph_has_e g1 {| field_addr := {| addr_gen := gen1; addr_block := vidx |} ; field_index := eidx |}).
  - intros. erewrite <- frr_dst_unchanged; eauto. destruct H4. assumption.
  - destruct H3. eapply frr_graph_has_v_inv in H3; eauto. destruct H3 as [? | [? ?]].
    2: simpl in H3; contradiction. split. 1: simpl; assumption. simpl in *.
    cut (get_edges g1 {| addr_gen := gen1 ; addr_block := vidx |} = get_edges g2 {| addr_gen := gen1 ; addr_block := vidx |}).
    + intros; rewrite H5; assumption.
    + unfold get_edges. unfold make_fields. erewrite frr_block_fields; eauto.
Qed.

Lemma fr_O_dst_unchanged_field: forall from to v n g g',
    forward_p_compatible (inr (v, Z.of_nat n)) [] g from ->
    forward_relation from to O (forward_p2forward_t (inr (v, Z.of_nat n)) [] g) g g' ->
    forall e, graph_has_v g (field_addr e) -> e <> {| field_addr := v; field_index := n |} -> dst g e = dst g' e.
Proof.
  intros. simpl in *. destruct H as [? [? [? ?]]]. rewrite H4 in H0. simpl in H0.
  remember (Znth (Z.of_nat n) (make_fields g v)).
  assert (forall e0, inr e0 = Znth (Z.of_nat n) (make_fields g v) -> e0 <> e). {
    intros. symmetry in H6. apply make_fields_Znth_edge in H6. 2: assumption.
    rewrite Nat2Z.id in H6. rewrite <- H6 in H2. auto. }
  destruct f; [destruct s |]; simpl in H0; inversion H0; subst; try reflexivity.
  - subst new_g. rewrite lgd_dst_old. 1: reflexivity. apply H6; assumption.
  - subst new_g. rewrite lgd_dst_old. 2: apply H6; assumption. simpl.
    rewrite pcv_dst_old. 1: reflexivity. intro. rewrite H7 in H1. destruct H1.
    unfold new_copied_v in H8. simpl in H8. red in H8. lia.
Qed.

Lemma svfl_dst_unchanged: forall from to v l g1 g2,
    graph_has_v g1 v -> block_mark (vlabel g1 v) = false -> addr_gen v <> from ->
    (forall i,  In i l -> i < length (block_fields (vlabel g1 v))) ->
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
    gen_v_num g1 to <= gen_v_num g2 to.
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
      (addr_gen v2 = to /\ gen_v_num g1 to <= addr_block v2 < gen_v_num g2 to).
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
    gen_v_num g1 to <= gen_v_num g2 to.
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
      (addr_gen v = to /\ gen_v_num g1 to <= addr_block v < gen_v_num g2 to).
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

Lemma frr_graph_has_v: forall from to f_info roots1 g1 roots2 g2,
    graph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, graph_has_v g1 v -> graph_has_v g2 v.
Proof.
  intros. induction H0; subst. 1: assumption. cut (graph_has_v g2 v).
  - intros. apply IHforward_roots_loop; auto. erewrite <- fr_graph_has_gen; eauto.
  - eapply fr_graph_has_v; eauto.
Qed.

Lemma fr_O_dst_changed_field: forall from to v n g g',
    copy_compatible g -> no_dangling_dst g -> from <> to -> graph_has_gen g to ->
    forward_p_compatible (inr (v, Z.of_nat n)) [] g from ->
    forward_relation from to O (forward_p2forward_t (inr (v, Z.of_nat n)) [] g) g g' ->
    forall e, Znth (Z.of_nat n) (make_fields g' v) = inr e ->
              addr_gen (dst g' e) <> from.
Proof.
  intros. simpl in *. destruct H3 as [? [? [? ?]]]. rewrite H7 in H4. simpl in H4.
  assert (make_fields g v = make_fields g' v) by
      (unfold make_fields; erewrite fr_block_fields; eauto). rewrite <- H9 in *.
  clear H9. remember (Znth (Z.of_nat n) (make_fields g v)). destruct f; inversion H5.
  subst. clear H5. symmetry in Heqf. pose proof Heqf.
  apply make_fields_Znth_edge in Heqf. 2: assumption. simpl in H4. subst.
  rewrite Nat2Z.id in *.
  inversion H4; subst; try assumption; subst new_g; rewrite lgd_dst_new.
  - apply H in H12. 1: destruct H12; auto. specialize (H0 _ H3). apply H0.
    unfold get_edges. rewrite <- filter_sum_right_In_iff, <- H5. apply Znth_In.
    rewrite make_fields_eq_length. assumption.
  - unfold new_copied_v. simpl. auto.
Qed.

Lemma fr_O_no_dangling_dst: forall from to p g g' roots,
    forward_p_compatible p roots g from -> graph_has_gen g to ->
    roots_graph_compatible roots g -> copy_compatible g ->
    forward_relation from to O (forward_p2forward_t p roots g) g g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros. inversion H3; subst; try assumption.
  - destruct p; simpl in H5.
    + destruct (Znth z roots) eqn:? ; [destruct s|]; simpl in H5; inversion H5.
      subst. clear H5. apply lcv_no_dangling_dst; auto. red in H1.
      rewrite Forall_forall in H1. apply H1. rewrite <- filter_sum_right_In_iff.
      rewrite <- Heqr. apply Znth_In. assumption.
    + destruct p. simpl in H. destruct H as [? [? [? ?]]]. rewrite H8 in H5.
      simpl in H5. destruct (Znth z (make_fields g a)); [destruct s|];
                     simpl in H5; inversion H5.
  - subst new_g. apply lgd_no_dangling_dst_copied_vert; auto.
    destruct p; simpl in H5.
    + destruct (Znth z roots); [destruct s|]; simpl in H5; inversion H5.
    + destruct p. simpl in H. destruct H as [? [? [? ?]]]. rewrite H7 in H5.
      simpl in H5. destruct (Znth z (make_fields g a)) eqn:? ; [destruct s|];
                     simpl in H5; inversion H5. subst. clear H5.
      specialize (H4 _ H). apply H4. unfold get_edges.
      rewrite <- filter_sum_right_In_iff, <- Heqf. apply Znth_In.
      rewrite make_fields_eq_length. assumption.
  - subst new_g. apply lgd_no_dangling_dst. 1: apply lcv_graph_has_v_new; auto.
    apply lcv_no_dangling_dst; auto. destruct p; simpl in H5.
    + destruct (Znth z roots); [destruct s|]; simpl in H5; inversion H5.
    + destruct p. simpl in H. destruct H as [? [? [? ?]]]. rewrite H8 in H5.
      simpl in H5. destruct (Znth z (make_fields g a)) eqn:? ; [destruct s|];
                     simpl in H5; inversion H5. subst. clear H5.
      specialize (H4 _ H). apply H4. unfold get_edges.
      rewrite <- filter_sum_right_In_iff, <- Heqf. apply Znth_In.
      rewrite make_fields_eq_length. assumption.
Qed.

Lemma svfl_dst_changed: forall from to v l g1 g2,
    graph_has_v g1 v -> block_mark (vlabel g1 v) = false -> addr_gen v <> from ->
    copy_compatible g1 -> no_dangling_dst g1 -> from <> to ->
    (forall i,  In i l -> i < length (block_fields (vlabel g1 v))) -> NoDup l ->
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
  assert (forall j : nat, In j l -> j < Datatypes.length (block_fields (vlabel g3 v))). {
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

Lemma no_scan_no_edge: forall g v, no_scan g v -> get_edges g v = nil.
Proof.
  intros. unfold no_scan in H. apply tag_no_scan in H. unfold get_edges.
  destruct (filter_sum_right (make_fields g v)) eqn:? . 1: reflexivity. exfalso.
  assert (In f (filter_sum_right (make_fields g v))) by (rewrite Heql; left; auto).
  rewrite <- filter_sum_right_In_iff in H0. clear l Heql. apply H. clear H.
  unfold make_fields in H0. remember (block_fields (vlabel g v)). clear Heql.
  remember O. clear Heqn. revert n H0. induction l; simpl; intros; auto.
  destruct a; [destruct s|]; simpl in H0;
    [right; destruct H0; [inversion H | eapply IHl; eauto]..|left]; auto.
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
    apply Forall_incl with
        (sublist i MAX_SPACES (map space_base (heap_spaces (ti_heap ti)))). 2: assumption.
    rewrite Z.add_comm. replace MAX_SPACES with (MAX_SPACES - i + i) at 1 by lia.
    rewrite <- sublist_sublist with (j := MAX_SPACES) by lia.
    unfold incl. intro a. apply sublist_In.
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
