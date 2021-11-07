From Coq Require Import Lists.List.

From VST Require Import floyd.sublist.
From VST Require Import veric.base.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.compatible.
From CertiGC Require Import model.constants.
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
                               (vertex_address g v) HB) f_info
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
