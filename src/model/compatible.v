From Coq Require Import Lists.List.

From VST Require Import floyd.sublist.
From VST Require Import veric.base.
From VST Require Import veric.val_lemmas.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.heap.
From CertiGC Require Import model.thread_info.
From CertiGC Require Import model.util.


Definition roots_outlier_compatible (roots: roots_t) (outlier: outlier_t): Prop :=
  incl (filter_sum_right (filter_sum_left roots)) outlier.

Definition roots_graph_compatible (roots: roots_t) (g: HeapGraph): Prop :=
  Forall (graph_has_v g) (filter_sum_right roots).

Definition roots_compatible (g: HeapGraph) (outlier: outlier_t) (roots: roots_t): Prop :=
  roots_outlier_compatible roots outlier /\ roots_graph_compatible roots g.


Definition outlier_compatible (g: HeapGraph) (outlier: outlier_t): Prop :=
  forall v,
    graph_has_v g v ->
    incl (filter_sum_right (filter_option (vlabel g v).(block_fields))) outlier.

Lemma in_gcptr_outlier: forall g gcptr outlier n v,
    graph_has_v g v ->
    outlier_compatible g outlier ->
    0 <= n < Zlength (block_fields (vlabel g v)) ->
    Znth n (make_fields g v) = inl (inr gcptr) ->
    In gcptr outlier.
Proof.
  intros.
  apply H0 in H; apply H; clear H; clear H0.
  unfold make_fields in H2.
  apply make_fields'_item_was_in_list in H2; try assumption.
  rewrite <- filter_sum_right_In_iff, <- filter_option_In_iff.
  rewrite <- H2; apply Znth_In; assumption.
Qed.


Definition generation_space_compatible (g: HeapGraph)
           (tri: nat * Generation * Space) : Prop :=
  match tri with
  | (gen, gi, sp) =>
    generation_base gi = sp.(space_base) /\
    generation_sh gi = sp.(space_sh) /\
    previous_vertices_size g gen gi.(generation_block_count) = sp.(space_allocated)
  end.

Definition graph_thread_info_compatible (g: HeapGraph) (ti: thread_info): Prop :=
  Forall (generation_space_compatible g)
         (combine (combine (nat_inc_list (length g.(glabel).(generations)))
                           g.(glabel).(generations)) ti.(ti_heap).(heap_spaces)) /\
  Forall (eq nullval)
         (skipn (length g.(glabel).(generations)) (map space_base ti.(ti_heap).(heap_spaces))) /\
  (length g.(glabel).(generations) <= length ti.(ti_heap).(heap_spaces))%nat.

Definition fun_thread_arg_compatible
           (g: HeapGraph) (ti: thread_info) (fi: fun_info) (roots: roots_t) : Prop :=
  map (root2val g) roots = map ((fun x y => Znth y x) ti.(ti_args)) fi.(live_roots_indices).


Definition super_compatible (g_ti_r: HeapGraph * thread_info * roots_t) (fi: fun_info) (out: outlier_t) : Prop
 := let (g_ti, r) := g_ti_r
 in let (g, ti) := g_ti
 in graph_thread_info_compatible g ti /\
    fun_thread_arg_compatible g ti fi r /\
    roots_compatible g out r /\
    outlier_compatible g out.


Lemma gsc_iff: forall (g: HeapGraph) t_info,
    (length (generations (glabel g)) <= length (heap_spaces (ti_heap t_info)))%nat ->
    Forall (generation_space_compatible g)
           (combine (combine (nat_inc_list (length (generations (glabel g))))
                             (generations (glabel g))) (heap_spaces (ti_heap t_info))) <->
    forall gen,
      graph_has_gen g gen ->
      generation_space_compatible g (gen, nth_gen g gen, nth_space t_info gen).
Proof.
  intros. rewrite Forall_forall. remember (generations (glabel g)).
  remember (nat_inc_list (length l)). remember (heap_spaces (ti_heap t_info)).
  assert (length (combine l0 l) = length l) by
      (subst; rewrite combine_length, nat_inc_list_length, Nat.min_id; reflexivity).
  assert (length (combine (combine l0 l) l1) = length l) by
      (rewrite combine_length, H0, min_l by assumption; reflexivity).
  cut (forall x, In x (combine (combine l0 l) l1) <->
                    exists gen, graph_has_gen g gen /\
                                x = (gen, nth_gen g gen, nth_space t_info gen)).
  - intros. split; intros.
    + apply H3. rewrite H2. exists gen. intuition.
    + rewrite H2 in H4. destruct H4 as [gen [? ?]]. subst x. apply H3. assumption.
  - intros.
    assert (forall gen,
               graph_has_gen g gen ->
               nth gen (combine (combine l0 l) l1) (O, null_generation, null_space) =
               (gen, nth_gen g gen, nth_space t_info gen)). {
      intros. red in H2. rewrite <- Heql in H2.
      rewrite combine_nth_lt; [|rewrite H0; lia | lia].
      rewrite combine_nth by (subst l0; rewrite nat_inc_list_length; reflexivity).
      rewrite Heql0. rewrite nat_inc_list_nth by assumption.
      rewrite Heql. unfold nth_gen, nth_space. rewrite Heql1. reflexivity. }
    split; intros.
    + apply (In_nth (combine (combine l0 l) l1) x (O, null_generation, null_space)) in H3.
      destruct H3 as [gen [? ?]]. exists gen. rewrite H1 in H3.
      assert (graph_has_gen g gen) by (subst l; assumption). split. 1: assumption.
      rewrite H2 in H4 by assumption. subst x. reflexivity.
    + destruct H3 as [gen [? ?]]. rewrite <- H2 in H4 by assumption. subst x.
      apply nth_In. rewrite H1. subst l. assumption.
Qed.

Lemma gt_gs_compatible:
  forall (g: HeapGraph) (t_info: thread_info),
    graph_thread_info_compatible g t_info ->
    forall gen,
      graph_has_gen g gen ->
      generation_space_compatible g (gen, nth_gen g gen, nth_space t_info gen).
Proof.
  intros. destruct H as [? [_ ?]]. rewrite gsc_iff in H by assumption.
  apply H. assumption.
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
  pose proof (Zlength_nonneg l).
  assert (0 <= i - Zlength l). { rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_le in H3 ; lia. }
  rewrite <- Znth_skipn by lia. rewrite ZtoNat_Zlength.
  apply Znth_In. split. 1: assumption. rewrite <- ZtoNat_Zlength, Zlength_skipn.
  rewrite (Z.max_r 0 (Zlength l)) by lia. rewrite Z.max_r; lia.
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
    split. 1: lia. rewrite Zlength_correct. apply inj_lt.
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


Definition forward_roots_compatible
           (from to: nat) (g: HeapGraph) (ti : thread_info): Prop :=
  (nth_space ti from).(space_allocated) <= (nth_space ti to).(space_capacity) -
                                      (nth_space ti to).(space_allocated).

Definition roots_fi_compatible (roots: roots_t) f_info: Prop :=
  Zlength roots = Zlength (live_roots_indices f_info) /\
  forall i j,
    0 <= i < Zlength roots -> 0 <= j < Zlength roots ->
    Znth i (live_roots_indices f_info) = Znth j (live_roots_indices f_info) ->
    Znth i roots = Znth j roots.


Lemma graph_thread_v_in_range (g: HeapGraph) (t_info: thread_info) (v: Addr)
    (Hcompat: graph_thread_info_compatible g t_info)
    (Hv: graph_has_v g v):
    v_in_range
        (vertex_address g v)
        (gen_start g (addr_gen v))
        (WORD_SIZE * gen_size t_info (addr_gen v)).
Proof.
    exists (WORD_SIZE * vertex_offset g v).
    pose proof WORD_SIZE_pos as HH.
    repeat split.
    {
        pose proof (previous_vertices_size__nonneg g (addr_gen v) (addr_block v)) as HH'.
        unfold vertex_offset.
        lia.
    }
    {
        apply Zmult_lt_compat_l ; try assumption.
        pose proof (proj2 (space__order (nth_space t_info (addr_gen v)))) as HH'.
        apply Z.lt_le_trans with (space_allocated (nth_space t_info (addr_gen v))) ; try assumption.
        destruct Hv as [Hv_gen Hv_index].
        destruct (gt_gs_compatible _ _ Hcompat _ Hv_gen) as [Estart [Esh Eused]].
        rewrite <- Eused.
        now apply vo_lt_gs.
    }
Qed.
