From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
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
  Forall (heapgraph_has_block g) (filter_sum_right roots).

Definition roots_compatible (g: HeapGraph) (outlier: outlier_t) (roots: roots_t): Prop :=
  roots_outlier_compatible roots outlier /\ roots_graph_compatible roots g.


Definition outlier_compatible (g: HeapGraph) (outlier: outlier_t): Prop :=
  forall v,
    heapgraph_has_block g v ->
    incl (filter_sum_right (filter_option (heapgraph_block g v).(block_fields))) outlier.

Lemma in_gcptr_outlier: forall g gcptr outlier n v,
    heapgraph_has_block g v ->
    outlier_compatible g outlier ->
    (0 <= n < Zlength (block_fields (heapgraph_block g v)))%Z ->
    Znth n (heapgraph_block_cells g v) = inl (inr gcptr) ->
    In gcptr outlier.
Proof.
  intros.
  apply H0 in H; apply H; clear H; clear H0.
  unfold heapgraph_block_cells in H2.
  apply fields_to_cells__id in H2; try assumption.
  rewrite <- filter_sum_right_In_iff, <- filter_option_In_iff.
  rewrite <- H2; apply Znth_In; assumption.
Qed.


Definition generation_space_compatible (g: HeapGraph)
           (tri: nat * Generation * Space) : Prop :=
  match tri with
  | (gen, gi, sp) =>
    generation_base gi = sp.(space_base) /\
    generation_sh gi = sp.(space_sh) /\
    heapgraph_block_size_prev g gen gi.(generation_block_count) = sp.(space_allocated)
  end.

Definition graph_thread_info_compatible (g: HeapGraph) (ti: thread_info): Prop :=
  Forall (generation_space_compatible g)
         (combine (combine (nat_inc_list (length (heapgraph_generations g).(generations)))
                           (heapgraph_generations g).(generations)) ti.(ti_heap).(heap_spaces)) /\
  Forall (eq nullval)
         (skipn (length (heapgraph_generations g).(generations)) (map space_base ti.(ti_heap).(heap_spaces))) /\
  (length (heapgraph_generations g).(generations) <= length ti.(ti_heap).(heap_spaces))%nat.

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
    (length (generations (heapgraph_generations g)) <= length (heap_spaces (ti_heap t_info)))%nat ->
    Forall (generation_space_compatible g)
           (combine (combine (nat_inc_list (length (generations (heapgraph_generations g))))
                             (generations (heapgraph_generations g))) (heap_spaces (ti_heap t_info))) <->
    forall gen,
      heapgraph_has_gen g gen ->
      generation_space_compatible g (gen, heapgraph_generation g gen, nth_space t_info gen).
Proof.
  intros. rewrite Forall_forall. remember (generations (heapgraph_generations g)).
  remember (nat_inc_list (length l)). remember (heap_spaces (ti_heap t_info)).
  assert (length (combine l0 l) = length l) by
      (subst; rewrite combine_length, nat_inc_list_length, Nat.min_id; reflexivity).
  assert (length (combine (combine l0 l) l1) = length l) by
      (rewrite combine_length, H0, min_l by assumption; reflexivity).
  cut (forall x, In x (combine (combine l0 l) l1) <->
                    exists gen, heapgraph_has_gen g gen /\
                                x = (gen, heapgraph_generation g gen, nth_space t_info gen)).
  - intros. split; intros.
    + apply H3. rewrite H2. exists gen. intuition.
    + rewrite H2 in H4. destruct H4 as [gen [? ?]]. subst x. apply H3. assumption.
  - intros.
    assert (forall gen,
               heapgraph_has_gen g gen ->
               nth gen (combine (combine l0 l) l1) (O, null_generation, null_space) =
               (gen, heapgraph_generation g gen, nth_space t_info gen)). {
      intros. red in H2. rewrite <- Heql in H2.
      rewrite combine_nth_lt; [|rewrite H0; lia | lia].
      rewrite combine_nth by (subst l0; rewrite nat_inc_list_length; reflexivity).
      rewrite Heql0. rewrite nat_inc_list_nth by assumption.
      rewrite Heql. unfold heapgraph_generation, nth_space. rewrite Heql1. reflexivity. }
    split; intros.
    + apply (In_nth (combine (combine l0 l) l1) x (O, null_generation, null_space)) in H3.
      destruct H3 as [gen [? ?]]. exists gen. rewrite H1 in H3.
      assert (heapgraph_has_gen g gen) by (subst l; assumption). split. 1: assumption.
      rewrite H2 in H4 by assumption. subst x. reflexivity.
    + destruct H3 as [gen [? ?]]. rewrite <- H2 in H4 by assumption. subst x.
      apply nth_In. rewrite H1. subst l. assumption.
Qed.

Lemma gt_gs_compatible:
  forall (g: HeapGraph) (t_info: thread_info),
    graph_thread_info_compatible g t_info ->
    forall gen,
      heapgraph_has_gen g gen ->
      generation_space_compatible g (gen, heapgraph_generation g gen, nth_space t_info gen).
Proof.
  intros. destruct H as [? [_ ?]]. rewrite gsc_iff in H by assumption.
  apply H. assumption.
Qed.

Lemma space_base_isptr: forall (g: HeapGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (heap_spaces (ti_heap t_info)) ->
    heapgraph_has_gen g (Z.to_nat i) ->
    isptr (space_base (Znth i (heap_spaces (ti_heap t_info)))).
Proof.
  intros. destruct (gt_gs_compatible _ _ H _ H1) as [? _].
  rewrite nth_space_Znth in H2. rewrite Z2Nat.id in H2 by lia. rewrite <- H2.
  apply generation_base__isptr.
Qed.

Lemma space_base_isnull: forall (g: HeapGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (heap_spaces (ti_heap t_info)) ->
    ~ heapgraph_has_gen g (Z.to_nat i) ->
    space_base (Znth i (heap_spaces (ti_heap t_info))) = nullval.
Proof.
  intros. unfold heapgraph_has_gen in H1. destruct H as [_ [? ?]].
  rewrite Forall_forall in H. symmetry. apply H. rewrite <- map_skipn.
  apply List.in_map. remember (generations (heapgraph_generations g)).
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
  intros. destruct (heapgraph_has_gen_dec g (Z.to_nat i)).
  - apply val_lemmas.isptr_is_pointer_or_null. eapply space_base_isptr; eauto.
  - cut (space_base (Znth i (heap_spaces (ti_heap t_info))) = nullval).
    + intros. rewrite H1. apply mapsto_memory_block.is_pointer_or_null_nullval.
    + eapply space_base_isnull; eauto.
Qed.

Lemma space_base_isptr_iff: forall (g: HeapGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (heap_spaces (ti_heap t_info)) ->
    heapgraph_has_gen g (Z.to_nat i) <->
    isptr (space_base (Znth i (heap_spaces (ti_heap t_info)))).
Proof.
  intros. split; intros.
  - eapply space_base_isptr; eauto.
  - destruct (heapgraph_has_gen_dec g (Z.to_nat i)). 1: assumption. exfalso.
    eapply space_base_isnull in n; eauto. rewrite n in H1. inversion H1.
Qed.

Lemma space_base_isnull_iff: forall (g: HeapGraph) (t_info: thread_info) i,
    graph_thread_info_compatible g t_info ->
    0 <= i < Zlength (heap_spaces (ti_heap t_info)) ->
    ~ heapgraph_has_gen g (Z.to_nat i) <->
    space_base (Znth i (heap_spaces (ti_heap t_info))) = nullval.
Proof.
  intros. split; intros. 1: eapply space_base_isnull; eauto.
  destruct (heapgraph_has_gen_dec g (Z.to_nat i)). 2: assumption. exfalso.
  eapply space_base_isptr in h; eauto. rewrite H1 in h. inversion h.
Qed.


Lemma ti_size_gen: forall (g : HeapGraph) (t_info : thread_info) (gen : nat),
    graph_thread_info_compatible g t_info ->
    heapgraph_has_gen g gen -> ti_size_spec t_info ->
    gen_size t_info gen = generation_size gen.
Proof.
  intros. red in H1. rewrite Forall_forall in H1.
  assert (0 <= (Z.of_nat gen) < Zlength (heap_spaces (ti_heap t_info))). {
    split. 1: lia. rewrite Zlength_correct. apply inj_lt.
    destruct H as [_ [_ ?]]. red in H0. lia. }
  assert (generation_size_spec t_info gen). {
    apply H1. rewrite nat_inc_list_In_iff. destruct H as [_ [_ ?]]. red in H0.
    rewrite <- (heap_spaces__size (ti_heap t_info)), ZtoNat_Zlength. lia. } red in H3.
  destruct (Val.eq (space_base (nth_space t_info gen)) nullval). 2: assumption.
  rewrite nth_space_Znth in e. erewrite <- space_base_isnull_iff in e; eauto.
  unfold heapgraph_has_gen in e. exfalso; apply e. rewrite Nat2Z.id. assumption.
Qed.

Lemma ti_size_gt_0: forall (g : HeapGraph) (t_info : thread_info) (gen : nat),
    graph_thread_info_compatible g t_info ->
    heapgraph_has_gen g gen -> ti_size_spec t_info -> 0 < gen_size t_info gen.
Proof.
  intros. erewrite ti_size_gen; eauto. unfold generation_size. apply Z.mul_pos_pos.
  - rewrite NURSERY_SIZE_eq. vm_compute. reflexivity.
  - cut (two_p (Z.of_nat gen) > 0). 1: lia. apply two_p_gt_ZERO. lia.
Qed.


Lemma lgd_rgc: forall g roots e v,
    roots_graph_compatible roots g ->
    roots_graph_compatible roots (labeledgraph_gen_dst g e v).
Proof.
  intros. red in H |-*. rewrite Forall_forall in *. intros.
  rewrite <- lgd_heapgraph_has_block. apply H. assumption.
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
  rewrite <- lgd_heapgraph_has_block in H0.
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
    (Hv: heapgraph_has_block g v):
    v_in_range
        (heapgraph_block_ptr g v)
        (heapgraph_generation_base g (addr_gen v))
        (WORD_SIZE * gen_size t_info (addr_gen v)).
Proof.
    exists (WORD_SIZE * heapgraph_block_offset g v).
    pose proof WORD_SIZE_pos as HH.
    repeat split.
    {
        pose proof (heapgraph_block_size_prev__nonneg g (addr_gen v) (addr_block v)) as HH'.
        unfold heapgraph_block_offset.
        lia.
    }
    {
        apply Zmult_lt_compat_l ; try assumption.
        pose proof (proj2 (space__order (nth_space t_info (addr_gen v)))) as HH'.
        apply Z.lt_le_trans with (space_allocated (nth_space t_info (addr_gen v)) + space_remembered (nth_space t_info (addr_gen v))) ; try assumption.
        destruct Hv as [Hv_gen Hv_index].
        destruct (gt_gs_compatible _ _ Hcompat _ Hv_gen) as [Estart [Esh Eused]].
        rewrite <- Eused.
        pose proof (space_remembered__lower_bound (nth_space t_info (addr_gen v))) as Hnth_lower_bound.
        pose proof (heapgraph_block_offset__heapgraph_generation_size g v Hv_index) as Hgen_size.
        change
          (heapgraph_block_size_prev g (addr_gen v) (generation_block_count (heapgraph_generation g (addr_gen v))))
          with (heapgraph_generation_size g (addr_gen v)).
        lia.
    }
Qed.


Lemma gti_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES),
    graph_thread_info_compatible g ti ->
    ~ heapgraph_has_gen g (Z.to_nat i) -> heapgraph_has_gen g (Z.to_nat (i - 1)) ->
    (forall (gr: HeapGraph), generation_space_compatible gr (Z.to_nat i, gi, sp)) ->
    graph_thread_info_compatible (heapgraph_generations_append g gi)
                                 (ti_add_new_space ti sp i Hs).
Proof.
  intros. unfold graph_thread_info_compatible in *. destruct H as [? [? ?]].
  assert (length (generations (heapgraph_generations g)) = Z.to_nat i). {
    clear -H0 H1. unfold heapgraph_has_gen in *.
    rewrite Z2Nat.inj_sub in H1 by lia. simpl in H1. lia. }
  pose proof (heap_spaces__size (ti_heap ti)).
  assert (length (generations (heapgraph_generations (heapgraph_generations_append g gi))) <=
          length (heap_spaces (ti_heap (ti_add_new_space ti sp i Hs))))%nat. {
    simpl. rewrite <- !ZtoNat_Zlength, upd_Znth_Zlength by lia.
    rewrite H6, ZtoNat_Zlength, app_length, H5. simpl. change (S O) with (Z.to_nat 1).
    rewrite <- Z2Nat.inj_add, <- Z2Nat.inj_le by lia. lia. }
  split; [|split]; auto.
  - rewrite gsc_iff in H |- * by assumption. intros.
    apply heapgraph_has_gen__heapgraph_generations_append in H8. destruct H8.
    + rewrite heapgraph_generation__heapgraph_generations_append__old by assumption. rewrite ans_nth_old.
      1: apply H; assumption. red in H8. rewrite H5 in H8. lia.
    + subst gen. rewrite heapgraph_generation__heapgraph_generations_append__new, H5, ans_nth_new. apply H2.
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


Lemma ang_roots_graph_compatible: forall roots g gi,
    roots_graph_compatible roots g ->
    roots_graph_compatible roots (heapgraph_generations_append g gi).
Proof.
  intros. unfold roots_graph_compatible in *. rewrite Forall_forall in *. intros.
  apply heapgraph_generations_append__heapgraph_has_block. apply H. assumption.
Qed.

Lemma ang_roots_compatible: forall roots out g gi,
    roots_compatible g out roots ->
    roots_compatible (heapgraph_generations_append g gi) out roots.
Proof. intros. destruct H. split; auto. apply ang_roots_graph_compatible. auto. Qed.

Lemma ang_outlier_compatible: forall g gi out,
    generation_block_count gi = O -> outlier_compatible g out ->
    outlier_compatible (heapgraph_generations_append g gi) out.
Proof.
  intros. unfold outlier_compatible in *. intros.
  apply heapgraph_generations_append__heapgraph_has_block_inv in H1; auto. simpl. apply H0. assumption.
Qed.

Lemma fta_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES) fi roots,
    fun_thread_arg_compatible g ti fi roots -> roots_graph_compatible roots g ->
    fun_thread_arg_compatible (heapgraph_generations_append g gi)
                              (ti_add_new_space ti sp i Hs) fi roots.
Proof.
  intros. unfold fun_thread_arg_compatible in *. simpl. rewrite <- H.
  apply map_ext_in. intros. destruct a; [destruct s|]; simpl; try reflexivity.
  apply heapgraph_generations_append__heapgraph_block_ptr. red in H0. rewrite Forall_forall in H0. apply H0.
  rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Lemma super_compatible_add: forall g ti gi sp i (Hs: 0 <= i < MAX_SPACES) fi roots out,
    ~ heapgraph_has_gen g (Z.to_nat i) -> heapgraph_has_gen g (Z.to_nat (i - 1)) ->
    (forall (gr: HeapGraph), generation_space_compatible gr (Z.to_nat i, gi, sp)) ->
    generation_block_count gi = O -> super_compatible (g, ti, roots) fi out ->
    super_compatible (heapgraph_generations_append g gi, ti_add_new_space ti sp i Hs, roots)
                     fi out.
Proof.
  intros. destruct H3 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply gti_compatible_add; assumption.
  - apply fta_compatible_add; [|destruct H5]; assumption.
  - apply ang_roots_compatible; assumption.
  - apply ang_outlier_compatible; assumption.
Qed.