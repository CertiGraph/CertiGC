From Coq Require Import Lists.List.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.compatible.
From CertiGC Require Import model.constants.
From CertiGC Require Import model.copy.
From CertiGC Require Import model.cut.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.heap.
From CertiGC Require Import model.thread_info.
From CertiGC Require Import model.util.


Definition upd_bunch (index: Z) (f_info: fun_info)
           (roots: roots_t) (v: root_t): roots_t :=
  fold_right (fun i rs => upd_Znth i rs v) roots
             (get_indices index (live_roots_indices f_info)).

Lemma upd_bunch_graph_compatible: forall g f_info roots z,
    roots_graph_compatible roots g ->
    forall v : Addr,
      graph_has_v g v ->
      roots_graph_compatible (upd_bunch z f_info roots (inr v)) g.
Proof.
  intros. red in H |-* . rewrite Forall_forall in H |-* . intros.
  rewrite <- filter_sum_right_In_iff in H1. unfold upd_bunch in H1.
  apply fold_right_upd_Znth_In in H1. destruct H1. 2: inversion H1; assumption.
  apply H. rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Lemma upd_bunch_Zlength: forall (f_info : fun_info) (roots : roots_t) (z : Z),
    Zlength roots = Zlength (live_roots_indices f_info) ->
    forall r : root_t, Zlength (upd_bunch z f_info roots r) = Zlength roots.
Proof.
  intros. unfold upd_bunch. apply fold_right_upd_Znth_Zlength.
  intros. rewrite H. rewrite get_indices_spec in H0. destruct H0; assumption.
Qed.

Lemma upd_bunch_same: forall f_info roots z j r,
    0 <= j < Zlength roots ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Znth j (live_roots_indices f_info) = Znth z (live_roots_indices f_info) ->
    Znth j (upd_bunch z f_info roots r) = r.
Proof.
  intros. unfold upd_bunch. apply fold_right_upd_Znth_same.
  - intros. rewrite get_indices_spec in H2. destruct H2. rewrite H0; assumption.
  - rewrite get_indices_spec. split; [rewrite <- H0|]; assumption.
Qed.

Lemma upd_bunch_diff: forall f_info roots z j r,
    0 <= j < Zlength roots ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Znth j (live_roots_indices f_info) <> Znth z (live_roots_indices f_info) ->
    Znth j (upd_bunch z f_info roots r) = Znth j roots.
Proof.
  intros. unfold upd_bunch. apply fold_right_upd_Znth_diff. 3: assumption.
  - intros. rewrite get_indices_spec in H2. destruct H2. rewrite H0; assumption.
  - rewrite get_indices_spec. intro. destruct H2. apply H1. assumption.
Qed.


Lemma upd_thread_info_Zlength: forall (t: thread_info) (i: Z) (v: val),
    0 <= i < MAX_ARGS -> Zlength (upd_Znth i (ti_args t) v) = MAX_ARGS.
Proof.
  intros. rewrite upd_Znth_Zlength; [apply arg_size | rewrite arg_size; assumption].
Qed.

Definition upd_thread_info_arg
           (t: thread_info) (i: Z) (v: val) (H: 0 <= i < MAX_ARGS) : thread_info :=
  Build_thread_info (ti_heap_p t) (ti_heap t) (upd_Znth i (ti_args t) v)
                    (upd_thread_info_Zlength t i v H).

Lemma upd_fun_thread_arg_compatible: forall g t_info f_info roots z,
    fun_thread_arg_compatible g t_info f_info roots ->
    forall (v : Addr) (HB : 0 <= Znth z (live_roots_indices f_info) < MAX_ARGS),
      fun_thread_arg_compatible
        g (upd_thread_info_arg t_info (Znth z (live_roots_indices f_info))
                               (heapgraph_block_ptr g v) HB) f_info
        (upd_bunch z f_info roots (inr v)).
Proof.
  intros. red in H |-* . unfold upd_thread_info_arg. simpl. rewrite Znth_list_eq in H.
  destruct H. rewrite !Zlength_map in H. rewrite Zlength_map in H0.
  assert (Zlength (upd_bunch z f_info roots (inr v)) = Zlength roots) by
      (rewrite upd_bunch_Zlength; [reflexivity | assumption]).
  rewrite Znth_list_eq. split. 1: rewrite !Zlength_map, H1; assumption. intros.
  rewrite Zlength_map, H1 in H2.
  rewrite !Znth_map; [|rewrite <- H | rewrite H1]; [|assumption..].
  specialize (H0 _ H2). rewrite !Znth_map in H0; [|rewrite <- H| ]; [|assumption..].
  destruct (Z.eq_dec (Znth j (live_roots_indices f_info))
                     (Znth z (live_roots_indices f_info))).
  - rewrite e, upd_Znth_same. 2: now rewrite arg_size.
    rewrite upd_bunch_same; [|assumption..]. reflexivity.
  - rewrite upd_Znth_diff. 4: assumption. 3: now rewrite arg_size.
    + rewrite <- H0. rewrite upd_bunch_diff; [|assumption..]. reflexivity.
    + rewrite arg_size. apply (fi_index_range f_info), Znth_In.
      rewrite <- H. assumption.
Qed.


Lemma upd_roots_outlier_compatible: forall f_info roots outlier z v,
    roots_outlier_compatible roots outlier ->
    (* forall v : Addr, *)
    (*   graph_has_v g v -> *)
    roots_outlier_compatible (upd_bunch z f_info roots (inr v)) outlier.
Proof.
  intros. do 2 red in H |-* . intros.
  rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff in H0.
  unfold upd_bunch in H0. apply fold_right_upd_Znth_In in H0. destruct H0.
  2: inversion H0. apply H.
  rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff. assumption.
Qed.

Lemma upd_roots_compatible: forall g f_info roots outlier z,
    roots_compatible g outlier roots ->
    forall v : Addr, graph_has_v g v ->
                      roots_compatible g outlier (upd_bunch z f_info roots (inr v)).
Proof.
  intros. destruct H. split.
  - apply upd_roots_outlier_compatible; assumption.
  - apply upd_bunch_graph_compatible; assumption.
Qed.

Lemma upd_tf_arg_Zlength: forall (t: thread_info) (index: Z) (v: val),
    0 <= index < MAX_ARGS -> Zlength (upd_Znth index (ti_args t) v) = MAX_ARGS.
Proof.
  intros. rewrite upd_Znth_Zlength; [apply arg_size | rewrite arg_size; assumption].
Qed.

Definition update_thread_info_arg (t: thread_info) (index: Z)
           (v: val) (H: 0 <= index < MAX_ARGS): thread_info :=
  Build_thread_info (ti_heap_p t) (ti_heap t) (upd_Znth index (ti_args t) v)
                    (upd_tf_arg_Zlength t index v H).

Lemma utia_estc: forall g t_info from to index v (H : 0 <= index < MAX_ARGS),
    enough_space_to_copy g t_info from to ->
    enough_space_to_copy g (update_thread_info_arg t_info index v H) from to.
Proof.
  unfold enough_space_to_copy. intros. unfold rest_gen_size, nth_space in *. apply H0.
Qed.

Lemma utia_ti_heap: forall t_info i ad (Hm : 0 <= i < MAX_ARGS),
    ti_heap (update_thread_info_arg t_info i ad Hm) = ti_heap t_info.
Proof. intros. simpl. reflexivity. Qed.

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


Lemma forward_estc: forall
    g t_info v to index uv
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (heapgraph_block_size g v))
    (Hm : 0 <= index < MAX_ARGS),
    addr_gen v <> to -> heapgraph_has_gen g to ->
    graph_has_v g v -> block_mark (heapgraph_block g v) = false ->
    enough_space_to_copy g t_info (addr_gen v) to ->
    enough_space_to_copy
      (lgraph_copy_v g v to)
      (update_thread_info_arg
         (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g v) Hi Hh) index uv Hm)
      (addr_gen v) to.
Proof.
  intros. apply utia_estc. clear index uv Hm.
  apply forward_estc_unchanged; assumption.
Qed.

Lemma lcv_roots_graph_compatible: forall g roots v to f_info z,
    heapgraph_has_gen g to ->
    roots_graph_compatible roots g ->
    roots_graph_compatible (upd_bunch z f_info roots (inr (new_copied_v g to)))
                           (lgraph_copy_v g v to).
Proof.
  intros. apply upd_bunch_graph_compatible.
  - apply lcv_rgc_unchanged; assumption.
  - unfold lgraph_copy_v; rewrite <- lmc_graph_has_v;
      apply lacv_graph_has_v_new; assumption.
Qed.

Lemma lcv_roots_compatible: forall g roots outlier v to f_info z,
    heapgraph_has_gen g to ->
    roots_compatible g outlier roots ->
    roots_compatible (lgraph_copy_v g v to) outlier
                     (upd_bunch z f_info roots (inr (new_copied_v g to))).
Proof.
  intros. destruct H0. split.
  - apply upd_roots_outlier_compatible; assumption.
  - apply lcv_roots_graph_compatible; assumption.
Qed.

Lemma lcv_fun_thread_arg_compatible: forall
    g t_info f_info roots z v to i s
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s)
    (Hm : 0 <= Znth z (live_roots_indices f_info) < MAX_ARGS),
    heapgraph_has_gen g to -> roots_graph_compatible roots g ->
    fun_thread_arg_compatible g t_info f_info roots ->
    fun_thread_arg_compatible
      (lgraph_copy_v g v to)
      (update_thread_info_arg
         (cut_thread_info t_info i s Hi Hh) (Znth z (live_roots_indices f_info))
         (heapgraph_block_ptr g (new_copied_v g to)) Hm)
      f_info (upd_bunch z f_info roots (inr (new_copied_v g to))).
Proof.
  intros. rewrite <- (lcv_heapgraph_block_ptr_new g v to H).
  apply upd_fun_thread_arg_compatible with (HB := Hm).
    apply lcv_fun_thread_arg_compatible_unchanged; assumption.
Qed.

Lemma lcv_super_compatible: forall
    g t_info roots f_info outlier to v z
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (heapgraph_block_size g v))
    (Hm : 0 <= Znth z (live_roots_indices f_info) < MAX_ARGS),
    heapgraph_has_gen g to -> graph_has_v g v ->
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible
      (lgraph_copy_v g v to,
       update_thread_info_arg
         (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g v) Hi Hh)
         (Znth z (live_roots_indices f_info))
         (heapgraph_block_ptr g (new_copied_v g to)) Hm,
       upd_bunch z f_info roots (inr (new_copied_v g to))) f_info outlier.
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lcv_graph_thread_info_compatible; assumption.
  - destruct H3. apply lcv_fun_thread_arg_compatible; assumption.
  - apply lcv_roots_compatible; assumption.
  - apply lcv_outlier_compatible; assumption.
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
