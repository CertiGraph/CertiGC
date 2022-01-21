From CertiGraph Require Import msl_ext.ramification_lemmas.
From CertiGraph Require Import graph.graph_gen.

From CertiGC Require Import CertiGC.vst.spec.gc_spec.

Local Open Scope logic.

Lemma root_valid_int_or_ptr: forall g (roots: roots_t) root outlier,
    In root roots ->
    roots_compatible g outlier roots ->
    graph_rep g * outlier_rep outlier |-- !! (valid_int_or_ptr (root2val g root)).
Proof.
  intros. destruct H0. destruct root as [[? | ?] | ?].
  - simpl root2val. unfold odd_Z2val. replace (2 * z + 1) with (z + z + 1) by lia.
    apply prop_right, valid_int_or_ptr_ii1.
  - sep_apply (roots_outlier_rep_single_rep _ _ _ H H0).
    sep_apply (single_outlier_rep_valid_int_or_ptr g0). entailer!.
  - red in H1. rewrite Forall_forall in H1.
    rewrite (filter_sum_right_In_iff a roots) in H.
    apply H1 in H. simpl. sep_apply (graph_rep_valid_int_or_ptr _ _ H). entailer!.
Qed.

Lemma weak_derives_strong: forall (P Q: mpred),
    P |-- Q -> P |-- (weak_derives P Q && emp) * P.
Proof.
  intros. cancel. apply andp_right. 2: cancel.
  assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
  apply derives_weak. assumption.
Qed.

Lemma sapi_ptr_val: forall p m n,
    isptr p -> Int.min_signed <= n <= Int.max_signed ->
    (force_val
       (sem_add_ptr_int int_or_ptr_type Signed (offset_val (WORD_SIZE * m) p)
                        (vint n))) = offset_val (WORD_SIZE * (m + n)) p.
Proof.
  intros. rewrite sem_add_pi_ptr_special; [| easy | | easy].
  - simpl. rewrite offset_offset_val. f_equal. fold WORD_SIZE; rep_lia.
  - rewrite isptr_offset_val. assumption.
Qed.

Lemma sapil_ptr_val: forall p m n,
    isptr p ->
    if Archi.ptr64 then
      force_val
        (sem_add_ptr_long int_or_ptr_type (offset_val (WORD_SIZE * m) p)
                          (Vlong (Int64.repr n))) = offset_val (WORD_SIZE * (m + n)) p
    else
      force_val
        (sem_add_ptr_int int_or_ptr_type Signed (offset_val (WORD_SIZE * m) p)
                         (vint n)) = offset_val (WORD_SIZE * (m + n)) p.
Proof.
  intros. simpl.
  first [rewrite sem_add_pi_ptr_special' | rewrite sem_add_pl_ptr_special']; auto.
  simpl. fold WORD_SIZE. rewrite offset_offset_val. f_equal. lia.
Qed.

Lemma data_at_mfs_eq: forall g v i sh nv,
    field_compatible int_or_ptr_type [] (offset_val (WORD_SIZE * i) nv) ->
    0 <= i < Zlength (block_fields (heapgraph_block g v)) ->
    data_at sh (tarray int_or_ptr_type i) (sublist 0 i (heapgraph_block_cells_vals g v)) nv *
    field_at sh int_or_ptr_type [] (Znth i (heapgraph_block_cells_vals g v))
             (offset_val (WORD_SIZE * i) nv) =
    data_at sh (tarray int_or_ptr_type (i + 1))
            (sublist 0 (i + 1) (heapgraph_block_cells_vals g v)) nv.
Proof.
  intros. rewrite field_at_data_at. unfold field_address.
  rewrite if_true by assumption. simpl nested_field_type.
  simpl nested_field_offset. rewrite offset_offset_val.
  replace (WORD_SIZE * i + 0) with (WORD_SIZE * i)%Z by lia.
  rewrite <- (data_at_singleton_array_eq
                sh int_or_ptr_type _ [Znth i (heapgraph_block_cells_vals g v)]) by reflexivity.
  rewrite <- fields_eq_length in H0.
  rewrite (data_at_tarray_value
             sh (i + 1) i nv (sublist 0 (i + 1) (heapgraph_block_cells_vals g v))
             (heapgraph_block_cells_vals g v) (sublist 0 i (heapgraph_block_cells_vals g v))
             [Znth i (heapgraph_block_cells_vals g v)]).
  - replace (i + 1 - i) with 1 by lia. reflexivity.
  - lia.
  - lia.
  - autorewrite with sublist. reflexivity.
  - reflexivity.
  - rewrite sublist_one; [reflexivity | lia..].
Qed.

Lemma data_at__value_0_size: forall sh p,
    data_at_ sh (tarray int_or_ptr_type 0) p |-- emp.
Proof. intros. rewrite data_at__eq. apply data_at_zero_array_inv; reflexivity. Qed.

Lemma data_at_minus1_address: forall sh v p,
    data_at sh (if Archi.ptr64 then tulong else tuint)
            v (offset_val (- WORD_SIZE) p) |--
            !! (force_val (sem_add_ptr_int (if Archi.ptr64 then tulong else tuint)
                                           Signed p (eval_unop Oneg tint (vint 1))) =
                field_address (if Archi.ptr64 then tulong else tuint) []
                              (offset_val (- WORD_SIZE) p)).
Proof.
  intros. unfold eval_unop. simpl. entailer!.
  unfold field_address. rewrite if_true by assumption. rewrite offset_offset_val.
  simpl. reflexivity.
Qed.

Lemma body_forward: semax_body Vprog Gprog f_forward forward_spec.
Proof.
  start_function.
  destruct H as [? [? [? ?]]]. destruct H1 as [? [? [? [? ?]]]].
  unfold limit_address, next_address, forward_p_address. destruct forward_p.
  - unfold thread_info_rep. Intros.
    assert (Zlength roots = Zlength (live_roots_indices f_info)) by
        (rewrite <- (Zlength_map _ _ ((fun x y => Znth y x) (ti_args t_info))), <- H4, Zlength_map; trivial).
    pose proof (Znth_map _ (root2val g) _ H0). hnf in H0. rewrite H11 in H0.
    rewrite H4, Znth_map in H12 by assumption.
    remember (Znth z roots) as root. rewrite <- H11 in H0.
    pose proof (Znth_In _ _ H0).
    rewrite <- Heqroot in H13. rewrite H11 in H0. unfold Inhabitant_val in H12.
    assert (forall v, In (inr v) roots -> isptr (heapgraph_block_ptr g v)). { (**)
      intros. destruct H5. unfold heapgraph_block_ptr. red in H15.
      rewrite Forall_forall in H15.
      rewrite (filter_sum_right_In_iff v roots) in H14. apply H15 in H14.
      pose proof (heapgraph_has_block__has_gen H14) as Hgen.
      apply heapgraph_generation_base__isptr in Hgen.
      remember (heapgraph_generation_base g (addr_gen v)) as vv.
      destruct vv; try contradiction.
      simpl. exact I.
    }
    assert (is_pointer_or_integer (root2val g root)). {
      destruct root as [[? | ?] | ?]; simpl; auto.
      - destruct g0. simpl. exact I.
      - specialize (H14 _ H13). apply isptr_is_pointer_or_integer. assumption. }
    assert (0 <= Znth z (live_roots_indices f_info) < MAX_ARGS) by
        (apply (fi_index_range f_info), Znth_In; assumption).
    forward; rewrite H12. 1: entailer!.
    assert_PROP (valid_int_or_ptr (root2val g root)). {
      gather_SEP (graph_rep _) (outlier_rep _).
      sep_apply (root_valid_int_or_ptr _ _ _ _ H13 H5). entailer!. }
    forward_call (root2val g root).
    remember (graph_rep g * heap_rest_rep (ti_heap t_info) * outlier_rep outlier)
      as P. pose proof (graph_and_heap_rest_data_at_ _ _ _ H7 H).
    unfold generation_data_at_ in H18. remember (heapgraph_generation_base g from) as fp.
    remember (heapgraph_generation_sh g from) as fsh. remember (gen_size t_info from) as gn.
    remember (WORD_SIZE * gn)%Z as fn.
    assert (P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
      apply weak_derives_strong. subst. sep_apply H18.
      rewrite data_at__memory_block.
      rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold gen_size].
      destruct (space_capacity__tight_range (nth_space t_info from)). assumption. }
    destruct root as [[? | ?] | ?]; simpl root2val.
    + unfold odd_Z2val. forward_if.
      1: exfalso; apply H20'; reflexivity.
      forward. Exists g t_info roots.
      entailer!.
      * simpl; split3; try rewrite <- Heqroot; [easy..|].
        split3; [constructor | easy | apply tir_id].
      * unfold thread_info_rep. entailer!.
    + unfold GC_Pointer2val. destruct g0. forward_if.
      2: exfalso; apply Int.one_not_zero in H20; assumption.
      forward_call (Vptr b i).
      gather_SEP (graph_rep _) (heap_rest_rep _) (outlier_rep _).
      rewrite <- HeqP. destruct H5.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H19. Intros. simpl root2val in *.
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        subst. cancel. apply andp_right. 2: cancel.
        assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
        apply derives_weak.
        sep_apply (roots_outlier_rep_valid_pointer _ _ _ H13 H5).
        simpl GC_Pointer2val. cancel. }
      replace_SEP 1 ((weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) by
          (entailer; assumption). Intros. clear H19.
      forward_call (fsh, fp, fn, (Vptr b i), P). Intros v. destruct v.
      * rewrite HeqP. Intros.
        gather_SEP (graph_rep g) (heap_rest_rep _).
        sep_apply H18. rewrite Heqfn in v.
        sep_apply (roots_outlier_rep_single_rep _ _ _ H13 H5). Intros.
        gather_SEP (single_outlier_rep _) (data_at_ _ _ _).
        change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in v.
        pose proof (generation_sh__writable (heapgraph_generation g from)).
        change (generation_sh (heapgraph_generation g from)) with (heapgraph_generation_sh g from) in H19.
        rewrite <- Heqfsh in H19. unfold generation_data_at_.
        sep_apply (single_outlier_rep_memory_block_FF (GCPtr b i) fp gn fsh H19 v).
        assert_PROP False by entailer!. contradiction.
      * forward_if. 1: exfalso; apply H19'; reflexivity.
        forward. Exists g t_info roots.
        entailer!.
        -- split3; [| |split3]; simpl; try rewrite <- Heqroot;
             [easy.. | constructor | hnf; intuition | apply tir_id].
        -- unfold thread_info_rep. entailer!.
    + specialize (H14 _ H13). destruct (heapgraph_block_ptr g a) eqn:Ea ; try contradiction.
      forward_if. 2: exfalso; apply Int.one_not_zero in H20; assumption.
      clear H20 H20'. simpl in H15, H17. forward_call (Vptr b i).
      rewrite <- Ea in *.
      gather_SEP (graph_rep _) (heap_rest_rep _) (outlier_rep _).
      rewrite <- HeqP.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H19. Intros. assert (heapgraph_has_block g a). {
        destruct H5. red in H19. rewrite Forall_forall in H19. apply H19.
        rewrite <- filter_sum_right_In_iff. assumption. }
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        apply weak_derives_strong. subst. sep_apply (graph_rep_vertex_rep g a H19).
        Intros shh. unfold vertex_rep, vertex_at. remember (heapgraph_block_cells_vals g a).
        sep_apply (data_at_valid_ptr shh (tarray int_or_ptr_type (Zlength l)) l (heapgraph_block_ptr g a)).
        - apply readable_nonidentity, writable_readable_share. assumption.
        - subst l. simpl. rewrite fields_eq_length.
          rewrite Z.max_r; pose proof (block_fields__range (heapgraph_block g a)); lia.
        - rewrite Ea. cancel.
      }
      replace_SEP 1 (weak_derives P (valid_pointer (Vptr b i) * TT) && emp * P)
        by (entailer; assumption). clear H20. Intros. rewrite <- Ea in *.
      forward_call (fsh, fp, fn, (heapgraph_block_ptr g a), P). Intros vv. rewrite HeqP.
      sep_apply (graph_and_heap_rest_v_in_range_iff _ _ _ _ H H7 H19). Intros.
      rewrite <- Heqfp, <- Heqgn, <- Heqfn in H20. destruct vv.
      * Intros. rewrite H20 in v. clear H20. forward_if.
        2: exfalso; inversion H20. freeze [1; 2; 3; 4; 5; 6] FR.
        clear H20 H20'. localize [vertex_rep (heapgraph_generation_sh g (addr_gen a)) g a].
        unfold vertex_rep, vertex_at. Intros. rewrite v.
        assert (readable_share (heapgraph_generation_sh g from)) by
            (unfold heapgraph_generation_sh; apply writable_readable, generation_sh__writable).
        sep_apply (data_at_minus1_address (heapgraph_generation_sh g from) (Z2val (heapgraph_block_header g a))
                                          (heapgraph_block_ptr g a)).
        Intros. forward. clear H21.
        gather_SEP (data_at _ (if Archi.ptr64 then tulong else tuint) _ _)
                   (data_at _ _ _ _).
        replace_SEP 0 (vertex_rep (heapgraph_generation_sh g (addr_gen a)) g a) by
            (unfold vertex_rep, vertex_at; entailer!).
        unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
        forward_if.
        -- try apply Int64.same_if_eq in H21.
           pose proof (heapgraph_block_header__repr_iff g a). simpl in H22.
           rewrite H22 in H21. clear H22.
           localize [vertex_rep (heapgraph_generation_sh g (addr_gen a)) g a].
           rewrite v. unfold vertex_rep, vertex_at. Intros.
           unfold heapgraph_block_cells_vals at 2. rewrite H21.
           assert (0 <= 0 < Zlength (heapgraph_block_cells_vals g a)). {
             split. 1: lia. rewrite fields_eq_length.
             apply (proj1 (block_fields__range (heapgraph_block g a))). }
           assert (is_pointer_or_integer
                     (heapgraph_block_ptr g (block_copied_vertex (heapgraph_block g a)))). {
             apply isptr_is_pointer_or_integer. unfold heapgraph_block_ptr.
             rewrite isptr_offset_val.
             apply heapgraph_generation_base__isptr, H9; assumption. }
           forward.
           rewrite Znth_0_cons.
           gather_SEP (data_at _ _ _ _)
                      (data_at _ _ _ _).
           replace_SEP 0 (vertex_rep (heapgraph_generation_sh g (addr_gen a)) g a). {
             unfold vertex_rep, vertex_at. unfold heapgraph_block_cells_vals at 3.
             rewrite H21. entailer!. }
           unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
           thaw FR. forward.
           Exists g (upd_thread_info_arg
                       t_info
                       (Znth z (live_roots_indices f_info))
                       (heapgraph_block_ptr g (block_copied_vertex (heapgraph_block g a))) H16)
                  (upd_bunch z f_info roots (inr (block_copied_vertex (heapgraph_block g a)))).
           unfold thread_info_rep. entailer!. 2: simpl; entailer!. simpl.
           split; split; [|split; [|split] | |split]; auto.
           ++ now apply upd_fun_thread_arg_compatible.
           ++ specialize (H9 _ H19 H21). destruct H9 as [? _].
              now apply upd_roots_compatible.
           ++ rewrite <- Heqroot, H21.
              now rewrite if_true by reflexivity.
           ++ rewrite <- Heqroot. apply fr_v_in_forwarded; [reflexivity | assumption].
           ++ easy.
        -- forward. thaw FR. freeze [0; 1; 2; 3; 4; 5] FR.
           try apply Int64_eq_false in H21.
           pose proof (heapgraph_block_header__repr_iff g a). simpl in H22.
           rewrite H22 in H21. clear H22. apply not_true_is_false in H21.
           rewrite heapgraph_block_header__Wosize by assumption.
           assert (0 <= Z.of_nat to < 12). {
             clear -H H8. destruct H as [_ [_ ?]]. red in H8.
             pose proof (heap_spaces__size (ti_heap t_info)).
             rewrite Zlength_correct in H0. rep_lia. } unfold heap_struct_rep.
           destruct (gt_gs_compatible _ _ H _ H8) as [? [? ?]].
           rewrite nth_space_Znth in *.
           remember (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) as sp_to.
           assert (isptr (space_base sp_to)) by (rewrite <- H23; apply generation_base__isptr).
           remember (map space_tri (heap_spaces (ti_heap t_info))) as l.
           assert (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef))
                         (Z.of_nat to) l = space_tri sp_to). {
             subst l sp_to. rewrite Znth_map by (rewrite heap_spaces__size; rep_lia).
             reflexivity. }
           forward; rewrite H27; unfold space_tri. 1: entailer!.
           forward. simpl sem_binary_operation'.
           rewrite sapi_ptr_val; [|assumption | rep_lia].
           Opaque Znth. forward. Transparent Znth.
           rewrite sapil_ptr_val by assumption. rewrite H27. unfold space_tri.
           rewrite <- Z.add_assoc.
           replace (1 + Zlength (block_fields (heapgraph_block g a))) with (heapgraph_block_size g a) by
               (unfold heapgraph_block_size; lia). thaw FR. freeze [0; 2; 3; 4; 5; 6] FR.
           assert (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info))) by
               (rewrite heap_spaces__size; rep_lia).
           assert (Hh: has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info)))
                                 (heapgraph_block_size g a)). {
             red. split. 1: pose proof (heapgraph_block_size__one g a); lia.
             transitivity (unmarked_gen_size g (addr_gen a)).
             - apply single_unmarked_le; assumption.
             - red in H1. unfold rest_gen_size in H1. subst from.
               rewrite nth_space_Znth in H1. assumption. }
           assert (Hn: space_base (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) <>
                       nullval). {
             rewrite <- Heqsp_to. destruct (space_base sp_to); try contradiction.
             intro Hn. inversion Hn. }
           rewrite (heap_rest_rep_cut
                      (ti_heap t_info) (Z.of_nat to) (heapgraph_block_size g a) Hi Hh Hn).
           rewrite <- Heqsp_to. thaw FR.
           gather_SEP (data_at _ thread_info_type _ _)
                      (data_at _ heap_type _ _)
                      (heap_rest_rep _).
           replace_SEP 0 (thread_info_rep
                            sh (cut_thread_info t_info _ _ Hi Hh) ti). {
             entailer. unfold thread_info_rep. simpl ti_heap. simpl ti_heap_p. cancel.
             simpl heap_spaces. rewrite <- upd_Znth_map. unfold cut_space.
             unfold space_tri at 3. simpl. unfold heap_struct_rep. cancel. }
           sep_apply (graph_vertex_ramif_stable _ _ H19). Intros.
           freeze [1; 2; 3; 4; 5] FR. rewrite v.
           remember (heapgraph_generation_sh g from) as shv.
           assert (writable_share (space_sh sp_to)) by
               (rewrite <- H24; apply generation_sh__writable).
           remember (space_sh sp_to) as sht.
           rewrite (data_at__tarray_value _ _ 1). 2: unfold heapgraph_block_size; rep_lia.
           Intros.
           remember (offset_val (WORD_SIZE * space_allocated sp_to) (space_base sp_to)).
           rewrite (data_at__int_or_ptr_integer sht v0).
           assert_PROP
             (force_val (sem_add_ptr_int
                           (if Archi.ptr64 then tulong else tuint) Signed
                           (offset_val (WORD_SIZE * (space_allocated sp_to + 1))
                                       (space_base sp_to))
                           (eval_unop Oneg tint (vint 1))) =
              field_address (if Archi.ptr64 then tulong else tuint) [] v0). {
             subst v0. entailer!. simpl. rewrite neg_repr.
             rewrite sem_add_pi_ptr_special; auto. 2: rep_lia. simpl in *.
             unfold field_address. rewrite if_true by assumption.
             simpl. rewrite !offset_offset_val. f_equal. unfold WORD_SIZE. lia. }
           forward. sep_apply (field_at_data_at_cancel
                                 sht (if Archi.ptr64 then tulong else tuint)
                                 (Z2val (heapgraph_block_header g a)) v0). clear H29.
           subst v0. rewrite offset_offset_val.
           replace (heapgraph_block_size g a - 1) with (Zlength (block_fields (heapgraph_block g a)))
             by (unfold heapgraph_block_size; lia).
           replace (WORD_SIZE * space_allocated sp_to + WORD_SIZE * 1) with
               (WORD_SIZE * (space_allocated sp_to + 1))%Z by rep_lia.
           remember (offset_val (WORD_SIZE * (space_allocated sp_to + 1))
                                (space_base sp_to)) as nv.
           thaw FR. freeze [0; 1; 2; 3; 4; 5] FR. rename i into j.
           remember (Zlength (block_fields (heapgraph_block g a))) as n.
           assert (isptr nv) by (subst nv; rewrite isptr_offset_val; assumption).
           remember (field_address thread_info_type
                                   [ArraySubsc (Znth z (live_roots_indices f_info));
                                    StructField _args] ti) as p_addr.
           remember (field_address heap_type
                                   [StructField _next; ArraySubsc (Z.of_nat to);
                                    StructField _spaces] (ti_heap_p t_info)) as n_addr.
           forward_for_simple_bound
             n
             (EX i: Z,
              PROP ( )
              LOCAL (temp _new nv;
                     temp _sz (if Archi.ptr64 then Vlong (Int64.repr n) else vint n);
                     temp _v (heapgraph_block_ptr g a);
                     temp _from_start fp;
                     temp _from_limit (offset_val fn fp);
                     temp _next n_addr;
                     temp _p p_addr;
                     temp _depth (vint depth))
              SEP (vertex_rep shv g a;
                   data_at sht (tarray int_or_ptr_type i)
                           (sublist 0 i (heapgraph_block_cells_vals g a)) nv;
                   data_at_ sht (tarray int_or_ptr_type (n - i))
                            (offset_val (WORD_SIZE * i) nv); FRZL FR))%assert.
           ++ pose proof (block_fields__range2 (heapgraph_block g a)). simpl in H30.
              now rewrite <- Heqn in H30.
           ++ rewrite sublist_nil. replace (n - 0) with n by lia.
              replace (WORD_SIZE * 0)%Z with 0 by lia.
              rewrite isptr_offset_val_zero by assumption.
              rewrite data_at_zero_array_eq;
                [|reflexivity | assumption | reflexivity]. entailer!.
           ++ unfold vertex_rep, vertex_at. Intros.
              rewrite fields_eq_length, <- Heqn. forward.
              ** entailer!. pose proof (mfv_all_is_ptr_or_int _ _ H9 H10 H19).
                 rewrite Forall_forall in H45.
                 apply H45, Znth_In.
                 now rewrite fields_eq_length.
              ** rewrite (data_at__tarray_value _ _ 1) by lia. Intros.
                 rewrite data_at__singleton_array_eq.
                 assert_PROP
                   (field_compatible int_or_ptr_type []
                                     (offset_val (WORD_SIZE * i) nv)) by
                     (sep_apply (data_at__local_facts
                                   sht int_or_ptr_type
                                   (offset_val (WORD_SIZE * i) nv)); entailer!).
                 assert_PROP
                   ((if Archi.ptr64 then
                      force_val (sem_add_ptr_long int_or_ptr_type
                                                  nv (Vlong (Int64.repr i)))
                     else force_val (sem_add_ptr_int int_or_ptr_type
                                                     Signed nv (vint i)))=
                    field_address int_or_ptr_type []
                                  (offset_val (WORD_SIZE * i) nv)). {
                   unfold field_address. rewrite if_true by assumption.
                   clear. entailer!. } simpl in H32.
                 gather_SEP (data_at _ _ _
                                     (offset_val (- WORD_SIZE) (heapgraph_block_ptr g a)))
                            (data_at _ _ _ (heapgraph_block_ptr g a)).
                 replace_SEP 0 (vertex_rep shv g a) by
                     (unfold vertex_rep, vertex_at;
                      rewrite fields_eq_length; entailer!). forward.
                 rewrite offset_offset_val.
                 replace (n - i - 1) with (n - (i + 1)) by lia.
                 replace (WORD_SIZE * i + WORD_SIZE * 1) with
                     (WORD_SIZE * (i + 1))%Z by lia.
                 gather_SEP (data_at sht _ _ nv) (field_at _ _ _ _ _).
                 rewrite data_at_mfs_eq. 2: assumption.
                 2: subst n; assumption. entailer!.
           ++ thaw FR. rewrite v, <- Heqshv.
              gather_SEP (vertex_rep _ _ _) (_ -* _).
              replace_SEP 0 (graph_rep g) by (entailer!; apply wand_frame_elim).
              rewrite sublist_all by (rewrite fields_eq_length; lia).
              replace_SEP 2 emp. {
                replace (n - n) with 0 by lia. clear. entailer.
                apply data_at__value_0_size. }
              assert (nv = heapgraph_block_ptr g (new_copied_v g to)). {
                subst nv. unfold heapgraph_block_ptr. unfold new_copied_v. simpl. f_equal.
                - unfold heapgraph_block_offset. simpl. rewrite H25. reflexivity.
                - unfold heapgraph_generation_base. rewrite if_true by assumption.
                  rewrite H23. reflexivity. }
              gather_SEP (data_at _ _ _ nv) (emp)
              (data_at sht (if Archi.ptr64 then tulong else tuint) _ _).
              replace_SEP
                0 (vertex_at (heapgraph_generation_sh g to)
                             (heapgraph_block_ptr g (new_copied_v g to))
                             (heapgraph_block_header g a) (heapgraph_block_cells_vals g a)). {
                normalize. rewrite <- H24.
                change (generation_sh (heapgraph_generation g to)) with (heapgraph_generation_sh g to).
                rewrite <- fields_eq_length in Heqn.
                replace (offset_val (WORD_SIZE * space_allocated sp_to) (space_base sp_to))
                  with (offset_val (- WORD_SIZE) nv) by
                    (rewrite Heqnv; rewrite offset_offset_val; f_equal; rep_lia).
                rewrite <- H30. unfold vertex_at; entailer!. }
              gather_SEP (vertex_at _ _ _ _) (graph_rep _).
              rewrite (copied_v_derives_new_g g a to) by assumption.
              freeze [1; 2; 3; 4] FR. remember (lgraph_add_copied_v g a to) as g'.
              assert (heapgraph_block_ptr g' a = heapgraph_block_ptr g a) by
                  (subst g'; apply lacv_heapgraph_block_ptr_old; assumption).
              assert (heapgraph_block_ptr g' (new_copied_v g to) =
                      heapgraph_block_ptr g (new_copied_v g to)) by
                  (subst g'; apply lacv_heapgraph_block_ptr_new; assumption).
              rewrite <- H31. rewrite <- H32 in H30.
              assert (writable_share (heapgraph_generation_sh g' (addr_gen a))) by
                  (unfold heapgraph_generation_sh; apply generation_sh__writable).
              assert (heapgraph_has_block g' (new_copied_v g to)) by
                  (subst g'; apply lacv_heapgraph_has_block_new; assumption).
              sep_apply (graph_rep_valid_int_or_ptr _ _ H34). Intros.
              rewrite <- H30 in H35. assert (heapgraph_has_block g' a) by
                  (subst g'; apply lgraph_add_copied_v__heapgraph_has_block; assumption).
              remember (heapgraph_generation_sh g' (addr_gen a)) as sh'.
              sep_apply (graph_vertex_lmc_ramif g' a (new_copied_v g to) H36).
              rewrite <- Heqsh'. Intros. freeze [1; 2] FR1.
              unfold vertex_rep, vertex_at. Intros.
              sep_apply (data_at_minus1_address
                           sh' (Z2val (heapgraph_block_header g' a)) (heapgraph_block_ptr g' a)).
              Intros. forward. clear H37. try rewrite Int.signed_repr by rep_lia.
              sep_apply (field_at_data_at_cancel
                           sh' (if Archi.ptr64 then tulong else tuint)
                           (if Archi.ptr64 then (Vlong (Int64.repr 0)) else (vint 0))
                           (offset_val (- WORD_SIZE) (heapgraph_block_ptr g' a))).
              forward_call (nv). remember (heapgraph_block_cells_vals g' a) as l'.
              assert (0 < Zlength l'). {
                subst l'. rewrite fields_eq_length.
                apply (proj1 (block_fields__range (heapgraph_block g' a))). }
              rewrite data_at_tarray_value_split_1 by assumption. Intros.
              assert_PROP (force_val (sem_add_ptr_int int_or_ptr_type Signed
                                                      (heapgraph_block_ptr g' a) (vint 0)) =
                           field_address int_or_ptr_type [] (heapgraph_block_ptr g' a)). {
                clear. entailer!. unfold field_address. rewrite if_true by assumption.
                simpl. rewrite isptr_offset_val_zero. 1: reflexivity.
                destruct H7 ; try assumption. } forward. clear H38.
              sep_apply (field_at_data_at_cancel
                           sh' int_or_ptr_type nv (heapgraph_block_ptr g' a)).
              gather_SEP
                (data_at _ (if Archi.ptr64 then tulong else tuint) _ _)
                (data_at _ int_or_ptr_type nv _)
                (data_at _ _ _ _).
              rewrite H30. subst l'.
              rewrite <- lmc_vertex_rep_eq.
              thaw FR1.
              gather_SEP (vertex_rep _ _ _) (_ -* _).
              sep_apply
                (wand_frame_elim
                   (vertex_rep sh' (lgraph_mark_copied g' a (new_copied_v g to)) a)
                   (graph_rep (lgraph_mark_copied g' a (new_copied_v g to)))).
              rewrite <- (lmc_heapgraph_block_ptr g' a (new_copied_v g to)) in *. subst g'.
              change (lgraph_mark_copied
                        (lgraph_add_copied_v g a to) a (new_copied_v g to))
                with (lgraph_copy_v g a to) in *.
              remember (lgraph_copy_v g a to) as g'. rewrite <- H30 in *. thaw FR.
              forward_call (nv). subst p_addr.
              remember (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g a) Hi Hh)
                as t_info'. unfold thread_info_rep. Intros. forward.
              remember (Znth z (live_roots_indices f_info)) as lz.
              gather_SEP
                (data_at sh thread_info_type _ ti)
                (heap_struct_rep sh _ _)
                (heap_rest_rep _ ).
              replace_SEP 0 (thread_info_rep
                               sh (update_thread_info_arg t_info' lz nv H16) ti). {
                unfold thread_info_rep. simpl heap_head. simpl ti_heap_p.
                simpl ti_args. simpl ti_heap. clear Heqt_info'. entailer!. }
              remember (update_thread_info_arg t_info' lz nv H16) as t. subst t_info'.
              rename t into t_info'. rewrite H30 in H32.
              assert (forward_relation from to 0 (inl (inr a)) g g') by
                  (subst g'; constructor; assumption).
              assert (forward_condition g' t_info' from to). {
                subst g' t_info' from. apply lcv_forward_condition; try assumption.
                red. intuition. }
              remember (upd_bunch z f_info roots (inr (new_copied_v g to))) as roots'.
              assert (super_compatible (g', t_info', roots') f_info outlier). {
                subst g' t_info' roots' lz. rewrite H30, H32.
                apply lcv_super_compatible; try assumption. red. intuition. }
              assert (thread_info_relation t_info t_info'). {
                subst t_info'. split; [|split]; [reflexivity| |]; intros m.
                - rewrite utiacti_gen_size. reflexivity.
                - rewrite utiacti_space_base. reflexivity. }
              forward_if.
              ** destruct H41 as [? [? ?]]. replace fp with (heapgraph_generation_base g' from) by
                     (subst fp g'; apply lcv_gen_start; assumption).
                 replace (offset_val fn (heapgraph_generation_base g' from)) with
                     (limit_address g' t_info' from) by
                     (subst fn gn; rewrite H43; reflexivity).
                 replace n_addr with (next_address t_info' to) by
                     (subst n_addr; rewrite H41; reflexivity).
                 forward_for_simple_bound
                   n
                   (EX i: Z, EX g3: HeapGraph, EX t_info3: thread_info,
                    PROP (super_compatible (g3, t_info3, roots') f_info outlier;
                          forward_loop
                            from to (Z.to_nat (depth - 1))
                            (sublist 0 i (heapgraph_field_pairs g' (new_copied_v g to)))
                            g' g3;
                          forward_condition g3 t_info3 from to;
                          thread_info_relation t_info' t_info3)
                    LOCAL (temp _new nv;
                           temp _sz (if Archi.ptr64 then
                                       Vlong (Int64.repr n) else vint n);
                           temp _from_start (heapgraph_generation_base g3 from);
                           temp _from_limit (limit_address g3 t_info3 from);
                           temp _next (next_address t_info3 to);
                           temp _depth (vint depth))
                    SEP (all_string_constants rsh gv;
                         fun_info_rep rsh f_info fi;
                         outlier_rep outlier;
                         graph_rep g3;
                         thread_info_rep sh t_info3 ti))%assert.
                 --- pose proof (block_fields__range2 (heapgraph_block g a)). simpl in H45.
                     now rewrite <- Heqn in H45.
                 --- Exists g' t_info'. autorewrite with sublist.
                     assert (forward_loop from to (Z.to_nat (depth - 1)) [] g' g') by
                         constructor. unfold thread_info_relation. entailer!.
                 --- change (Tpointer tvoid {| attr_volatile := false;
                                               attr_alignas := Some 2%N |})
                       with (int_or_ptr_type). Intros.
                     assert (heapgraph_has_gen g' to) by
                         (rewrite Heqg', <- lcv_graph_has_gen; assumption).
                     assert (heapgraph_has_block g' (new_copied_v g to)) by
                         (rewrite Heqg'; apply lcv_heapgraph_has_block_new; assumption).
                     forward_call (rsh, sh, gv, fi, ti, g3, t_info3, f_info, roots',
                                   outlier, from, to, depth - 1,
                                   (@inr Z _ (new_copied_v g to, i))).
                     +++ apply prop_right. simpl. rewrite sub_repr, H30.
                         do 4 f_equal.
                         first [rewrite sem_add_pi_ptr_special' |
                                rewrite sem_add_pl_ptr_special']; auto.
                         *** simpl. f_equal. erewrite fl_heapgraph_block_ptr; eauto.
                             subst g'. apply heapgraph_has_block_in_closure. assumption.
                         *** rewrite <- H30. assumption.
                     +++ split3; [| |split].
                         *** apply (fl_heapgraph_has_block _ _ _ _ _ _ H50 H47 _ H51).
                         *** erewrite <- fl_block_fields; eauto. subst g'.
                             unfold lgraph_copy_v. subst n.
                             rewrite <- lmc_block_fields, lacv_vlabel_new.
                             assumption.
                         *** erewrite <- fl_block_mark; eauto. subst g' from.
                             rewrite lcv_vlabel_new. auto. assumption.
                         *** simpl. lia.
                     +++ Intros vret. destruct vret as [[g4 t_info4] roots4].
                         simpl fst in *. simpl snd in *. Exists g4 t_info4.
                         simpl in H53. subst roots4.
                         assert (heapgraph_generation_base g3 from = heapgraph_generation_base g4 from). {
                           eapply fr_gen_start; eauto.
                           erewrite <- fl_graph_has_gen; eauto. } rewrite H53.
                         assert (limit_address g3 t_info3 from =
                                 limit_address g4 t_info4 from). {
                           unfold limit_address. f_equal. 2: assumption. f_equal.
                           destruct H56 as [? [? _]]. rewrite H57. reflexivity. }
                         rewrite H57.
                         assert (next_address t_info3 to = next_address t_info4 to). {
                           unfold next_address. f_equal. destruct H56. assumption. }
                         rewrite H58. clear H53 H57 H58.
                         assert (thread_info_relation t_info' t_info4) by
                             (apply tir_trans with t_info3; assumption).
                         assert (forward_loop
                                   from to (Z.to_nat (depth - 1))
                                   (sublist 0 (i + 1)
                                            (heapgraph_field_pairs g' (new_copied_v g to)))
                                   g' g4). {
                           eapply forward_loop_add_tail_vpp; eauto. subst n g' from.
                           rewrite lcv_vlabel_new; assumption. }
                         entailer!.
                 --- Intros g3 t_info3.
                     assert (thread_info_relation t_info t_info3) by
                         (apply tir_trans with t_info';
                          [split; [|split]|]; assumption).
                     rewrite sublist_all in H46. clear Heqt.
                     2: { rewrite Z.le_lteq. right. subst n g' from.
                          rewrite heapgraph_field_pairs__Zlength, lcv_vlabel_new; auto. }
                     Opaque super_compatible.
                     Exists g3 t_info3 roots'. entailer!. simpl.
                     rewrite <- Heqroot, H21, if_true by reflexivity. split; auto.
                     replace (Z.to_nat depth) with (S (Z.to_nat (depth - 1))) by
                         (rewrite <- Z2Nat.inj_succ; [f_equal|]; lia).
                     constructor; easy.
                     Transparent super_compatible.
              ** assert (depth = 0) by lia. subst depth. clear H42.
                 clear Heqnv. forward.
                 remember (cut_thread_info
                             t_info (Z.of_nat to) (heapgraph_block_size g a) Hi Hh).
                 Exists (lgraph_copy_v g a to) (update_thread_info_arg t lz nv H16)
                        (upd_bunch z f_info roots (inr (new_copied_v g to))).
                 entailer!. simpl; rewrite <- Heqroot.
                 rewrite if_true by reflexivity; rewrite H21; easy.
      * forward_if. 1: exfalso; apply H21'; reflexivity.
        rewrite H20 in n. forward.
        Exists g t_info roots. entailer!; simpl.
        -- rewrite <- Heqroot, if_false by assumption.
           split3; [| |simpl root2forward; constructor]; try easy.
           now constructor.
        -- unfold thread_info_rep. entailer!.
  (* p is Vtype * Z, ie located in graph *)
  - destruct p as [v n]. destruct H0 as [? [? [? ?]]]. freeze [0; 1; 2; 4] FR.
    localize [vertex_rep (heapgraph_generation_sh g (addr_gen v)) g v].
    unfold vertex_rep, vertex_at. Intros.
    assert_PROP (offset_val (WORD_SIZE * n) (heapgraph_block_ptr g v) =
                 field_address (tarray int_or_ptr_type
                                       (Zlength (heapgraph_block_cells_vals g v)))
                               [ArraySubsc n] (heapgraph_block_ptr g v)). {
      entailer!. unfold field_address. rewrite if_true; [simpl; f_equal|].
      clear -H20 H11; rewrite <- fields_eq_length in H11.
      unfold field_compatible in *; simpl in *; intuition.
    }
    assert (readable_share (heapgraph_generation_sh g (addr_gen v))) by
      apply writable_readable, generation_sh__writable.
    assert (is_pointer_or_integer (Znth n (heapgraph_block_cells_vals g v))). {
      pose proof (mfv_all_is_ptr_or_int g v H9 H10 H0). rewrite Forall_forall in H16.
      apply H16, Znth_In. rewrite fields_eq_length. assumption. } forward.
    gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
    replace_SEP 0 (vertex_rep (heapgraph_generation_sh g (addr_gen v)) g v).
    1: unfold vertex_rep, vertex_at; entailer!.
    unlocalize [graph_rep g]. 1: apply graph_vertex_ramif_stable; assumption. thaw FR.
    unfold heapgraph_block_cells_vals.
    rewrite H12, Znth_map; [|rewrite heapgraph_block_cells_eq_length; assumption].
    assert_PROP (valid_int_or_ptr (heapgraph_cell_val g (Znth n (heapgraph_block_cells g v)))). {
      destruct (Znth n (heapgraph_block_cells g v)) eqn:?; [destruct s|].
      - unfold heapgraph_cell_val; unfold odd_Z2val.
        replace (2 * z + 1) with (z + z + 1) by lia.
        entailer!. apply valid_int_or_ptr_ii1.
      - unfold heapgraph_cell_val, outlier_rep.
        apply in_gcptr_outlier with (gcptr:= g0) (outlier:=outlier) (n:=n) in H0;
          try assumption.
        apply (in_map single_outlier_rep outlier g0) in H0.
        replace_SEP 3 (single_outlier_rep g0). {
          clear -H0.
          apply (list_in_map_inv single_outlier_rep) in H0; destruct H0 as [? [? ?]].
          rewrite H.
          apply (in_map single_outlier_rep) in H0.
          destruct (log_normalize.fold_right_andp
                     (map single_outlier_rep outlier)
                     (single_outlier_rep x) H0).
          rewrite H1. entailer!; now apply andp_left1.
        }
        sep_apply (single_outlier_rep_valid_int_or_ptr g0); entailer!.
      - rename f into e. unfold heapgraph_cell_val.
        unfold no_dangling_dst in H10.
        apply H10 with (e:=e) in H0.
        1: sep_apply (graph_rep_valid_int_or_ptr g (dst g e) H0); entailer!.
        unfold heapgraph_block_fields; rewrite <- filter_sum_right_In_iff, <- Heqc.
        now apply Znth_In; rewrite heapgraph_block_cells_eq_length. }
    forward_call (heapgraph_cell_val g (Znth n (heapgraph_block_cells g v))).
    remember (graph_rep g * heap_rest_rep (ti_heap t_info) * outlier_rep outlier) as P.
    pose proof (graph_and_heap_rest_data_at_ _ _ _ H7 H).
    unfold generation_data_at_ in H18. remember (heapgraph_generation_base g from) as fp.
    remember (heapgraph_generation_sh g from) as fsh. remember (gen_size t_info from) as gn.
    remember (WORD_SIZE * gn)%Z as fn.
    assert (P |-- (weak_derives P (memory_block fsh fn fp * TT) && emp) * P). {
      apply weak_derives_strong. subst. sep_apply H18.
      rewrite data_at__memory_block.
      rewrite sizeof_tarray_int_or_ptr; [Intros; cancel | unfold gen_size].
      destruct (space_capacity__tight_range (nth_space t_info from)). assumption. }
    destruct (Znth n (heapgraph_block_cells g v)) eqn:? ; [destruct s|].
    (* Z + GC_Pointer + EType *)
    + (* Z *)
      unfold heapgraph_cell_val, odd_Z2val. forward_if.
      1: exfalso; apply H20'; reflexivity.
      forward. Exists g t_info roots. entailer!. split.
      * easy.
      * unfold forward_condition, thread_info_relation.
        simpl. rewrite Heqc, H12. simpl. constructor; [constructor|easy].
    + (* GC_Pointer *)
      destruct g0. unfold heapgraph_cell_val, GC_Pointer2val. forward_if.
      2: exfalso; apply Int.one_not_zero; assumption.
      forward_call (Vptr b i). 
      unfold thread_info_rep; Intros.
      gather_SEP (graph_rep _) (heap_rest_rep _) (outlier_rep _).
      rewrite <- HeqP. destruct H5.
      replace_SEP 0 ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption). clear H19. Intros.
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        subst; cancel; apply andp_right; [|cancel].
        assert (HS: emp |-- TT) by entailer; sep_apply HS; clear HS.
        apply derives_weak. assert (In (GCPtr b i) outlier) by
            (eapply in_gcptr_outlier; eauto).
        sep_apply (outlier_rep_valid_pointer outlier (GCPtr b i) H19).
        simpl GC_Pointer2val. cancel. }
      replace_SEP 1 ((weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P) by
          (entailer; assumption). Intros. clear H19.
      forward_call (fsh, fp, fn, (Vptr b i), P).
      Intros vret. destruct vret. (* is_from? *)
      * (* yes *)
        rewrite HeqP. Intros.
        gather_SEP (graph_rep _) (heap_rest_rep _).
        sep_apply H18. rewrite Heqfn in v0.
        pose proof in_gcptr_outlier g (GCPtr b i) outlier n v H0 H6 H11 Heqc.
        sep_apply (outlier_rep_single_rep outlier (GCPtr b i)).
        Intros.
        gather_SEP (data_at_ _ _ _) (single_outlier_rep _).
        change (Vptr b i) with (GC_Pointer2val (GCPtr b i)) in v0.
        pose proof (generation_sh__writable (heapgraph_generation g from)).
        change (generation_sh (heapgraph_generation g from)) with (heapgraph_generation_sh g from) in H22.
        rewrite <- Heqfsh in H22. unfold generation_data_at_.
        sep_apply (single_outlier_rep_memory_block_FF (GCPtr b i) fp gn fsh H22 v0).
        assert_PROP False by entailer!. contradiction.
      * (* no *)
        forward_if. 1: exfalso; apply H19'; reflexivity.
        forward. Exists g t_info roots. entailer!.
        -- split3.
           ++ unfold roots_compatible. easy.
           ++ simpl. rewrite Heqc, H12. simpl. constructor.
           ++ easy.
        -- unfold thread_info_rep. entailer!.
    + (* EType *)
      rename f into e.
      unfold heapgraph_cell_val. remember (dst g e) as v'.
      assert (isptr (heapgraph_block_ptr g v')). { (**)
        unfold heapgraph_block_ptr; unfold offset_val.
        remember (addr_gen v') as n'.
        assert (heapgraph_has_block g v'). {
          unfold no_dangling_dst in H10.
          subst. clear -H0 H10 H11 e Heqc.
          apply (H10 v H0).
          unfold heapgraph_block_fields;
          rewrite <- filter_sum_right_In_iff, <- Heqc; apply Znth_In.
          now rewrite heapgraph_block_cells_eq_length.
        }
        pose proof (heapgraph_has_block__has_gen H20) as Hgen.
        rewrite <- Heqn' in Hgen.
        pose proof (heapgraph_generation_base__isptr g n' Hgen).
        destruct (heapgraph_generation_base g n'); try contradiction; auto.
      }
      destruct (heapgraph_block_ptr g v') eqn:?; try contradiction.
      forward_if. 2: exfalso; apply Int.one_not_zero in H21; assumption.
      clear H21 H21'. forward_call (Vptr b i).
      unfold thread_info_rep; Intros.
      gather_SEP (graph_rep _) (heap_rest_rep _) (outlier_rep _).
      rewrite <- HeqP.
      replace_SEP 0
                  ((weak_derives P (memory_block fsh fn fp * TT) && emp) * P) by
          (entailer; assumption).
      clear H19. Intros. assert (heapgraph_has_block g v'). { (**)
        rewrite Heqv'.
        unfold no_dangling_dst in H10.
        clear -H10 H0 e Heqc H11. apply (H10 v H0).
        unfold heapgraph_block_fields.
        rewrite <- filter_sum_right_In_iff.
        rewrite <- Heqc.
        apply Znth_In.
        rewrite heapgraph_block_cells_eq_length; assumption.
      }
      assert (P |-- (weak_derives P (valid_pointer (Vptr b i) * TT) && emp) * P). {
        apply weak_derives_strong. subst.
        remember (dst g e) as v'.
        sep_apply (graph_rep_vertex_rep g v' H19).
        Intros shh. unfold vertex_rep, vertex_at. rewrite Heqv0.
        sep_apply (data_at_valid_ptr
                     shh (tarray int_or_ptr_type (Zlength (heapgraph_block_cells_vals g v')))
                     (heapgraph_block_cells_vals g v') (Vptr b i)).
        - apply readable_nonidentity, writable_readable_share; assumption.
        - simpl. rewrite fields_eq_length.
          pose proof (proj1 (block_fields__range (heapgraph_block g v'))). rewrite Z.max_r; lia.
        - cancel.
      }
      replace_SEP 1 (weak_derives P (valid_pointer (Vptr b i) * TT) && emp * P)
        by entailer!. clear H21. Intros.
      forward_call (fsh, fp, fn, (Vptr b i), P).
      (* is_from *)
      Intros vv. rewrite HeqP.
      sep_apply (graph_and_heap_rest_v_in_range_iff _ _ _ _ H H7 H19).
      Intros. rewrite <- Heqfp, <- Heqgn, <- Heqfn, Heqv0 in H21. destruct vv.
      * (* yes, is_from *)
        rewrite H21 in v0. clear H21. forward_if.
        2: exfalso; inversion H21.
        freeze [1; 2; 3; 4; 5; 6] FR.
        clear H21 H21'. localize [vertex_rep (heapgraph_generation_sh g (addr_gen v')) g v'].
        unfold vertex_rep, vertex_at. Intros. rewrite v0.
        assert (readable_share (heapgraph_generation_sh g from)) by
            (unfold heapgraph_generation_sh; apply writable_readable, generation_sh__writable).
        rewrite <- Heqv0.
        sep_apply (data_at_minus1_address
                     (heapgraph_generation_sh g from) (Z2val (heapgraph_block_header g v')) (heapgraph_block_ptr g v')).
        Intros. forward. clear H22.
        gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
        replace_SEP 0 (vertex_rep (heapgraph_generation_sh g (addr_gen v')) g v') by
            (unfold vertex_rep, vertex_at; entailer!).
        unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
        forward_if.
        -- (* yes, already forwarded *)
          try apply Int64.same_if_eq in H22.
          pose proof (heapgraph_block_header__repr_iff g v'). simpl in H23.
          rewrite H23 in H22. clear H23.
          localize [vertex_rep (heapgraph_generation_sh g (addr_gen v')) g v'].
          rewrite v0. unfold vertex_rep, vertex_at. Intros.
          unfold heapgraph_block_cells_vals at 2. rewrite H22.
          assert (0 <= 0 < Zlength (heapgraph_block_cells_vals g v')). {
             split. 1: lia. rewrite fields_eq_length.
             apply (proj1 (block_fields__range (heapgraph_block g v'))).
          }
          assert (is_pointer_or_integer (heapgraph_block_ptr g (block_copied_vertex (heapgraph_block g v')))).
          {
            apply isptr_is_pointer_or_integer. unfold heapgraph_block_ptr.
            rewrite isptr_offset_val.
            apply heapgraph_generation_base__isptr, H9; assumption.
          }
          forward.
          rewrite Znth_0_cons.
          gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
          replace_SEP 0 (vertex_rep (heapgraph_generation_sh g (addr_gen v')) g v').
          {
            unfold vertex_rep, vertex_at. unfold heapgraph_block_cells_vals at 3.
            rewrite H22. entailer!.
          }
          unlocalize [graph_rep g]. 1: apply (graph_vertex_ramif_stable _ _ H19).
          localize [vertex_rep (heapgraph_generation_sh g (addr_gen v)) g v].
          unfold vertex_rep, vertex_at. Intros.
          assert (writable_share (heapgraph_generation_sh g (addr_gen v))) by (unfold heapgraph_generation_sh; apply generation_sh__writable).
          forward.
          sep_apply (field_at_data_at_cancel
                       (heapgraph_generation_sh g (addr_gen v))
                       (tarray int_or_ptr_type (Zlength (heapgraph_block_cells_vals g v)))
                       (upd_Znth n (heapgraph_block_cells_vals g v)
                       (heapgraph_block_ptr g (block_copied_vertex (heapgraph_block g v'))))
                       (heapgraph_block_ptr g v)).
          gather_SEP (data_at _ _ _ _ ) (data_at _ _ _ _).
          remember (block_copied_vertex (heapgraph_block g v')).
          remember (labeledgraph_gen_dst g e a) as g'.
          replace_SEP 0 (vertex_rep (heapgraph_generation_sh g' (addr_gen v)) g' v).
          1: { unfold vertex_rep, vertex_at.
               replace (heapgraph_generation_sh g' (addr_gen v)) with
                   (heapgraph_generation_sh g (addr_gen v)) by (subst g'; reflexivity).
               replace (Zlength (heapgraph_block_cells_vals g' v)) with
                   (Zlength (heapgraph_block_cells_vals g v)) by
                   (subst g'; repeat rewrite fields_eq_length;
                    apply lgd_raw_fld_length_eq).
               rewrite (lgd_mfv_change_in_one_spot g v e a n);
                 [|rewrite heapgraph_block_cells_eq_length| | ]; try assumption.
               entailer!. }
          subst g'; subst a.
          unlocalize [graph_rep (labeledgraph_gen_dst g e
                                                      (block_copied_vertex (heapgraph_block g v')))].
          1: apply (graph_vertex_lgd_ramif g v e (block_copied_vertex (heapgraph_block g v')) n);
            try (rewrite heapgraph_block_cells_eq_length); assumption.
          Exists (labeledgraph_gen_dst g e (block_copied_vertex (heapgraph_block g (dst g e))))
                 t_info roots.
          entailer!.
          2: unfold thread_info_rep; thaw FR; entailer!.
          pose proof (lgd_no_dangling_dst_copied_vert g e (dst g e) H9 H19 H22 H10).
          split; [|split; [|split; [|split]]]; try reflexivity.
          ++ constructor ; try easy.
             admit. (* more coercion problems? *)
          ++ simpl forward_p2forward_t.
             rewrite H12, Heqc. simpl. now constructor.
          ++ constructor ; try easy.
             admit. (* more coercion problems? *)
          ++ easy.
        -- (* not yet forwarded *)
           forward. thaw FR.  freeze [0; 1; 2; 3; 4; 5] FR.
           try apply Int64_eq_false in H22.
           pose proof (heapgraph_block_header__repr_iff g v'). simpl in H23.
           rewrite H23 in H22. clear H23. apply not_true_is_false in H22.
           rewrite heapgraph_block_header__Wosize by assumption.
           assert (0 <= Z.of_nat to < 12). {
             clear -H H8. destruct H as [_ [_ ?]]. red in H8.
             pose proof (heap_spaces__size (ti_heap t_info)).
             rewrite Zlength_correct in H0. rep_lia. } unfold heap_struct_rep.
           destruct (gt_gs_compatible _ _ H _ H8) as [? [? ?]].
           rewrite nth_space_Znth in *.
           remember (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) as sp_to.
           assert (isptr (space_base sp_to)) by (rewrite <- H24; apply generation_base__isptr).
           remember (map space_tri (heap_spaces (ti_heap t_info))).
           assert (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef))
                         (Z.of_nat to) l = space_tri sp_to). {
             subst l sp_to. rewrite Znth_map by (rewrite heap_spaces__size; rep_lia).
             reflexivity. }
           forward; rewrite H28; unfold space_tri. 1: entailer!.
           forward. simpl sem_binary_operation'.
           rewrite sapi_ptr_val; [| assumption | rep_lia].
           Opaque Znth. forward. Transparent Znth.
           rewrite sapil_ptr_val by easy. rewrite H28. unfold space_tri.
           rewrite <- Z.add_assoc.
           replace (1 + Zlength (block_fields (heapgraph_block g v'))) with (heapgraph_block_size g v') by
               (unfold heapgraph_block_size; lia). thaw FR. freeze [0; 2; 3; 4; 5; 6] FR.
           assert (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info))) by
               (rewrite heap_spaces__size; rep_lia).
           assert (Hh: has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info)))
                                 (heapgraph_block_size g v')). {
             red. split. 1: pose proof (heapgraph_block_size__one g v'); lia.
             transitivity (unmarked_gen_size g (addr_gen v')).
             - apply single_unmarked_le; assumption.
             - red in H1. unfold rest_gen_size in H1. subst from.
               rewrite nth_space_Znth in H1. assumption. }
           assert (Hn: space_base (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) <>
                       nullval). {
             rewrite <- Heqsp_to. destruct (space_base sp_to); try contradiction.
             intro Hn. inversion Hn. }
           rewrite (heap_rest_rep_cut
                      (ti_heap t_info) (Z.of_nat to) (heapgraph_block_size g v') Hi Hh Hn).
           rewrite <- Heqsp_to. thaw FR.
           gather_SEP (data_at _ _ _ ti) (data_at _ _ _ _) (heap_rest_rep _).
           replace_SEP 0 (thread_info_rep
                            sh (cut_thread_info t_info _ _ Hi Hh) ti). {
             entailer. unfold thread_info_rep. simpl ti_heap. simpl ti_heap_p. cancel.
             simpl heap_spaces. rewrite <- upd_Znth_map. unfold cut_space.
             unfold space_tri at 3. simpl. unfold heap_struct_rep. cancel. }
           sep_apply (graph_vertex_ramif_stable _ _ H19). Intros.
           freeze [1; 2; 3; 4; 5] FR. rewrite v0.
           remember (heapgraph_generation_sh g from) as shv.
           assert (writable_share (space_sh sp_to)) by
               (rewrite <- H25; apply generation_sh__writable).
           remember (space_sh sp_to) as sht.
           rewrite (data_at__tarray_value _ _ 1). 2: unfold heapgraph_block_size; rep_lia.
           Intros.
           remember (offset_val (WORD_SIZE * space_allocated sp_to) (space_base sp_to)).
           rewrite (data_at__int_or_ptr_integer sht v1).
           assert_PROP
             (force_val (sem_add_ptr_int
                           (if Archi.ptr64 then tulong else tuint) Signed
                           (offset_val (WORD_SIZE * (space_allocated sp_to + 1))
                                       (space_base sp_to))
                           (eval_unop Oneg tint (vint 1))) =
              field_address (if Archi.ptr64 then tulong else tuint) [] v1). {
             subst v1. entailer!. unfold field_address.
             simpl. rewrite neg_repr. rewrite sem_add_pi_ptr_special; auto. 2: rep_lia.
             rewrite if_true by assumption. simpl. rewrite !offset_offset_val.
             f_equal. unfold WORD_SIZE. lia. }
           forward. sep_apply (field_at_data_at_cancel
                                 sht (if Archi.ptr64 then tulong else tuint)
                                 (Z2val (heapgraph_block_header g v')) v1). clear H30.
           subst v1. rewrite offset_offset_val.
           replace (heapgraph_block_size g v' - 1) with (Zlength (block_fields (heapgraph_block g v')))
             by (unfold heapgraph_block_size; lia).
           replace (WORD_SIZE * space_allocated sp_to + WORD_SIZE * 1) with
               (WORD_SIZE * (space_allocated sp_to + 1))%Z by rep_lia.
           remember (offset_val (WORD_SIZE * (space_allocated sp_to + 1))
                                (space_base sp_to)) as nv.
           thaw FR. freeze [0; 1; 2; 3; 4; 5] FR. rename i into j.
           remember (Zlength (block_fields (heapgraph_block g v'))) as n'.
           assert (isptr nv) by (subst nv; rewrite isptr_offset_val; assumption).
           remember (field_address heap_type
                                   [StructField _next; ArraySubsc (Z.of_nat to);
                                    StructField _spaces] (ti_heap_p t_info)) as n_addr.
           forward_for_simple_bound
             n'
             (EX i: Z,
              PROP ( )
              LOCAL (temp _new nv;
                     temp _sz (if Archi.ptr64 then Vlong (Int64.repr n') else vint n');
                     temp _v (heapgraph_block_ptr g v');
                     temp _from_start fp;
                     temp _from_limit (offset_val fn fp);
                     temp _next n_addr;
                     temp _p (offset_val (WORD_SIZE * n) (heapgraph_block_ptr g v));
                     temp _depth (vint depth))
              SEP (vertex_rep shv g v';
                   data_at sht (tarray int_or_ptr_type i)
                           (sublist 0 i (heapgraph_block_cells_vals g v')) nv;
                   data_at_ sht (tarray int_or_ptr_type (n' - i))
                            (offset_val (WORD_SIZE * i) nv); FRZL FR))%assert.
           ++ pose proof (block_fields__range2 (heapgraph_block g v')). simpl in H31.
              now rewrite <- Heqn' in H31.
           ++ rewrite sublist_nil. replace (n' - 0) with n' by lia.
              replace (WORD_SIZE * 0)%Z with 0 by lia.
              rewrite isptr_offset_val_zero by assumption.
              rewrite data_at_zero_array_eq; [entailer! | easy..].
           ++ unfold vertex_rep, vertex_at. Intros.
              rewrite fields_eq_length, <- Heqn'. forward.
              ** entailer!. pose proof (mfv_all_is_ptr_or_int _ _ H9 H10 H19) as HH.
                 rewrite Forall_forall in HH.
                 apply HH, Znth_In.
                 now rewrite fields_eq_length.
              ** rewrite (data_at__tarray_value _ _ 1) by lia. Intros.
                 rewrite data_at__singleton_array_eq.
                 assert_PROP
                   (field_compatible int_or_ptr_type []
                                     (offset_val (WORD_SIZE * i) nv)) by
                     (sep_apply (data_at__local_facts
                                   sht int_or_ptr_type
                                   (offset_val (WORD_SIZE * i) nv)); entailer!).
                 assert_PROP
                   ((if Archi.ptr64 then
                      force_val (sem_add_ptr_long int_or_ptr_type
                                                  nv (Vlong (Int64.repr i)))
                     else force_val (sem_add_ptr_int int_or_ptr_type
                                                     Signed nv (vint i))) =
                    field_address int_or_ptr_type []
                                  (offset_val (WORD_SIZE * i) nv)). {
                   unfold field_address. rewrite if_true by assumption.
                   clear. entailer!. } simpl in H33.
                 gather_SEP (data_at shv _ _ _)
                            (data_at _ (_ n') _ _).
                 replace_SEP 0 (vertex_rep shv g v') by
                     (unfold vertex_rep, vertex_at;
                      rewrite fields_eq_length; entailer!). forward.
                 rewrite offset_offset_val.
                 replace (n' - i - 1) with (n' - (i + 1)) by lia.
                 replace (WORD_SIZE * i + WORD_SIZE * 1) with
                     (WORD_SIZE * (i + 1))%Z by rep_lia.
                 gather_SEP (data_at _ _ _ nv) (field_at _ _ _ _ _).
                 rewrite data_at_mfs_eq;
                                   [entailer! | assumption | subst n'; assumption].
           ++ thaw FR. rewrite v0, <- Heqshv.
              gather_SEP (vertex_rep _ _ _) (_ -* _).
              replace_SEP 0 (graph_rep g) by (entailer!; apply wand_frame_elim).
              rewrite sublist_all by (rewrite fields_eq_length; lia).
              replace_SEP 2 emp. {
                replace (n' - n') with 0 by lia. clear. entailer.
                apply data_at__value_0_size. }
              assert (nv = heapgraph_block_ptr g (new_copied_v g to)). {
                subst nv. unfold heapgraph_block_ptr. unfold new_copied_v. simpl. f_equal.
                - unfold heapgraph_block_offset. simpl. rewrite H26. reflexivity.
                - unfold heapgraph_generation_base. rewrite if_true by assumption.
                  rewrite H24. reflexivity. }
              gather_SEP (data_at sht _ _ nv) (emp) (data_at sht _ _ _).
              replace_SEP
                0 (vertex_at (heapgraph_generation_sh g to)
                             (heapgraph_block_ptr g (new_copied_v g to))
                             (heapgraph_block_header g v') (heapgraph_block_cells_vals g v')). {
                normalize. rewrite <- H25.
                change (generation_sh (heapgraph_generation g to)) with (heapgraph_generation_sh g to).
                rewrite <- fields_eq_length in Heqn'.
                replace (offset_val (WORD_SIZE * space_allocated sp_to) (space_base sp_to))
                  with (offset_val (- WORD_SIZE) nv) by
                    (rewrite Heqnv; rewrite offset_offset_val; f_equal; rep_lia).
                rewrite <- H31. unfold vertex_at; entailer!. }
              gather_SEP (vertex_at _ _ _ _) (graph_rep _).
              rewrite (copied_v_derives_new_g g v' to) by assumption.
              freeze [1; 2; 3; 4] FR. remember (lgraph_add_copied_v g v' to) as g'.
              assert (heapgraph_block_ptr g' v' = heapgraph_block_ptr g v') by
                  (subst g'; apply lacv_heapgraph_block_ptr_old; assumption).
              assert (heapgraph_block_ptr g' (new_copied_v g to) =
                      heapgraph_block_ptr g (new_copied_v g to)) by
                  (subst g'; apply lacv_heapgraph_block_ptr_new; assumption).
              rewrite <- H32. rewrite <- H33 in H31.
              assert (writable_share (heapgraph_generation_sh g' (addr_gen v'))) by
                  (unfold heapgraph_generation_sh; apply generation_sh__writable).
              assert (heapgraph_has_block g' (new_copied_v g to)) by
                  (subst g'; apply lacv_heapgraph_has_block_new; assumption).
              sep_apply (graph_rep_valid_int_or_ptr _ _ H35). Intros.
              rewrite <- H31 in H36. assert (heapgraph_has_block g' v') by
                  (subst g'; apply lgraph_add_copied_v__heapgraph_has_block; assumption).
              remember (heapgraph_generation_sh g' (addr_gen v')) as sh'.
              sep_apply (graph_vertex_lmc_ramif g' v' (new_copied_v g to) H37).
              rewrite <- Heqsh'. Intros. freeze [1; 2] FR1.
              unfold vertex_rep, vertex_at. Intros.
              sep_apply (data_at_minus1_address
                           sh' (Z2val (heapgraph_block_header g' v')) (heapgraph_block_ptr g' v')).
              Intros. forward. clear H38.
              sep_apply (field_at_data_at_cancel
                           sh' (if Archi.ptr64 then tulong else tuint) (Z2val 0)
                           (offset_val (- WORD_SIZE) (heapgraph_block_ptr g' v'))).
              forward_call (nv). remember (heapgraph_block_cells_vals g' v') as l'.
              assert (0 < Zlength l'). {
                subst l'. rewrite fields_eq_length.
                apply (proj1 (block_fields__range (heapgraph_block g' v'))). }
              rewrite data_at_tarray_value_split_1 by assumption. Intros.
              assert_PROP (force_val (sem_add_ptr_int int_or_ptr_type Signed
                                                      (heapgraph_block_ptr g' v') (vint 0))
                           =
                           field_address int_or_ptr_type [] (heapgraph_block_ptr g' v')).
              {
                clear. entailer!. unfold field_address. rewrite if_true by assumption.
                simpl. rewrite isptr_offset_val_zero. 1: reflexivity.
                now destruct H7.
              }
              forward. clear H39.
              sep_apply (field_at_data_at_cancel
                           sh' int_or_ptr_type nv (heapgraph_block_ptr g' v')).
              gather_SEP (data_at sh' (if Archi.ptr64 then tulong else tuint) _ _)
                         (data_at sh' int_or_ptr_type _ _) (data_at _ _ _ _).
              rewrite H31. subst l'.
              rewrite <- lmc_vertex_rep_eq.
              thaw FR1.
              gather_SEP (vertex_rep _ _ _) (_ -* _).
              sep_apply
                (wand_frame_elim
                   (vertex_rep sh' (lgraph_mark_copied g' v' (new_copied_v g to)) v')
                   (graph_rep (lgraph_mark_copied g' v' (new_copied_v g to)))).
              rewrite <- (lmc_heapgraph_block_ptr g' v' (new_copied_v g to)) in *. subst g'.
              change (lgraph_mark_copied
                        (lgraph_add_copied_v g v' to) v' (new_copied_v g to))
                with (lgraph_copy_v g v' to) in *.
              remember (lgraph_copy_v g v' to) as g'.

              assert (heapgraph_block_ptr g' v' = heapgraph_block_ptr g v') by
              (subst g'; apply lcv_heapgraph_block_ptr_old; assumption).
              assert (heapgraph_block_ptr g' (new_copied_v g to) =
                      heapgraph_block_ptr g (new_copied_v g to)) by
                  (subst g'; apply lcv_heapgraph_block_ptr_new; assumption).
              assert (writable_share (heapgraph_generation_sh g' (addr_gen v'))) by
                  (unfold heapgraph_generation_sh; apply generation_sh__writable).
              assert (heapgraph_has_block g' (new_copied_v g to)) by
                  (subst g'; apply lcv_heapgraph_has_block_new; assumption).
              forward_call (nv).
              rewrite <- H31 in *.
              rewrite lacv_heapgraph_block_ptr;
                [|apply heapgraph_has_block_in_closure|]; try assumption.
              rewrite <- H32.
              rewrite <- (lcv_heapgraph_block_ptr g v' to v);
                try rewrite <- (lcv_heapgraph_block_ptr g v' to v) in H14;
                try apply heapgraph_has_block_in_closure; try assumption.
              rewrite (lcv_mfv_Zlen_eq g v v' to H8 H0) in H14. rewrite <- Heqg' in *.
              remember (heapgraph_generation_sh g' (addr_gen v)) as shh.
              remember (heapgraph_block_cells_vals g' v) as mfv.
              remember (new_copied_v g to).
              remember (labeledgraph_gen_dst g' e a) as g1.
              assert (0 <= n < Zlength (heapgraph_block_cells_vals g' v)) by
                  (subst g'; rewrite fields_eq_length, <- lcv_block_fields; assumption).
              assert (Znth n (heapgraph_block_cells g' v) = inr e) by
                  (subst g'; unfold heapgraph_block_cells in *;
                   rewrite <- lcv_block_fields; assumption).
              assert (0 <= n < Zlength (heapgraph_block_cells g' v)) by
                  (rewrite heapgraph_block_cells_eq_length;
                   rewrite fields_eq_length in H43; assumption).
              assert (heapgraph_has_block g' v) by
                  (subst g'; apply lcv_heapgraph_has_block_old; assumption).
              assert (v <> v') by
                  (intro; subst v; clear -v0 H13; lia).
              assert (block_mark (heapgraph_block g' v) = false) by
                (subst g'; rewrite <- lcv_block_mark; assumption).
              assert (writable_share shh) by
                  (rewrite Heqshh; unfold heapgraph_generation_sh; apply generation_sh__writable).
              localize [vertex_rep (heapgraph_generation_sh g' (addr_gen v)) g' v].
              unfold vertex_rep, vertex_at. Intros.
              rewrite Heqmfv in *; rewrite <- Heqshh.
              forward.
              rewrite H31.
              sep_apply (field_at_data_at_cancel
                           shh
                           (tarray int_or_ptr_type (Zlength (heapgraph_block_cells_vals g' v)))
                           (upd_Znth n (heapgraph_block_cells_vals g' v) (heapgraph_block_ptr g' a))
                           (heapgraph_block_ptr g' v)).
              gather_SEP (data_at shh _ _ _) (data_at shh _ _ _).
              replace_SEP 0 (vertex_rep (heapgraph_generation_sh g1 (addr_gen v)) g1 v).
              1: { unfold vertex_rep, vertex_at.
                   replace (heapgraph_generation_sh g1 (addr_gen v)) with shh by
                       (subst shh g1; reflexivity).
                   replace (Zlength (heapgraph_block_cells_vals g1 v)) with
                       (Zlength (heapgraph_block_cells_vals g' v)) by
                       (subst g1; repeat rewrite fields_eq_length;
                        apply lgd_raw_fld_length_eq).
                   rewrite (lgd_mfv_change_in_one_spot g' v e a n);
                     try assumption. entailer!. }
              subst g1; subst a.
              unlocalize [graph_rep (labeledgraph_gen_dst g' e (new_copied_v g to))].
              1: apply (graph_vertex_lgd_ramif g' v e (new_copied_v g to) n);
                assumption.
              remember (new_copied_v g to) as v1.
              remember (labeledgraph_gen_dst g' e v1) as g1.
              thaw FR.
              remember (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g v') Hi Hh)
                as t_info'.
              unfold thread_info_rep. Intros.
              assert (0 <= 0 < Zlength (ti_args t_info')) by
                  (rewrite arg_size; rep_lia).
              gather_SEP
                (data_at _ _ _ _)
                (heap_struct_rep _ _ _)
                (heap_rest_rep _).
              replace_SEP 0 (thread_info_rep sh t_info' ti).
              { unfold thread_info_rep. simpl heap_head. simpl ti_heap_p.
                simpl ti_args. simpl ti_heap. entailer!. }
              rewrite H31 in H33.
                assert (forward_relation from to 0 (inr e) g g1) by
                    (subst g1 g' v1 v'; constructor; assumption).
                assert (In e (heapgraph_block_fields g v)). { (**)
                  unfold heapgraph_block_fields.
                  rewrite <- filter_sum_right_In_iff.
                  rewrite <- Heqc.
                  apply (Znth_In n (heapgraph_block_cells g v)).
                  rewrite heapgraph_block_cells_eq_length. assumption.
                }
                assert (forward_condition g1 t_info' from to). {
                  subst g1 g' t_info' from v'.
                  assert (heapgraph_has_block (lgraph_copy_v g (dst g e) to) (dst g e)) as HH.
                  {
                    destruct H37 ; now constructor.
                  }
                  apply lgd_forward_condition; try assumption.
                  apply lcv_forward_condition_unchanged; try assumption.
                  red. intuition. }
                remember roots as roots'.
                assert (super_compatible (g1, t_info', roots') f_info outlier). {

                  subst g1 g' t_info' roots'.
                  apply lgd_super_compatible, lcv_super_compatible_unchanged;
                    try assumption.
                  red; intuition. }
              assert (thread_info_relation t_info t_info'). {
                subst t_info'. split; [|split]; [reflexivity| |]; intros m.
                - rewrite cti_gen_size. reflexivity.
                - rewrite cti_space_base. reflexivity. }
                forward_if.
              ** destruct H55 as [? [? ?]]. replace fp with (heapgraph_generation_base g1 from) by
                     (subst fp g1 g'; apply lcv_gen_start; assumption).
                 replace (offset_val fn (heapgraph_generation_base g1 from)) with
                     (limit_address g1 t_info' from) by
                     (subst fn gn; rewrite H57; reflexivity).
                 replace n_addr with (next_address t_info' to) by
                     (subst n_addr; rewrite H55; reflexivity).
                 forward_for_simple_bound
                   n'
                   (EX i: Z, EX g3: HeapGraph, EX t_info3: thread_info,
                    PROP (super_compatible (g3, t_info3, roots') f_info outlier;
                          forward_loop
                            from to (Z.to_nat (depth - 1))
                            (sublist 0 i (heapgraph_field_pairs g1 (new_copied_v g to)))
                            g1 g3;
                          forward_condition g3 t_info3 from to;
                          thread_info_relation t_info' t_info3)
                    LOCAL (temp _new nv;
                           temp _sz (if Archi.ptr64 then Vlong (Int64.repr n')
                                     else vint n');
                           temp _from_start (heapgraph_generation_base g3 from);
                           temp _from_limit (limit_address g3 t_info3 from);
                           temp _next (next_address t_info3 to);
                           temp _depth (vint depth))
                    SEP (all_string_constants rsh gv;
                         fun_info_rep rsh f_info fi;
                         outlier_rep outlier;
                         graph_rep g3;
                         thread_info_rep sh t_info3 ti))%assert.
                 --- pose proof (block_fields__range2 (heapgraph_block g v')). simpl in H59.
                     now rewrite <- Heqn' in H59.
                 --- Exists g1 t_info'. autorewrite with sublist.
                     assert (forward_loop from to (Z.to_nat (depth - 1)) [] g1 g1) by
                         constructor. unfold thread_info_relation.
                     destruct H54 as [? [? [? ?]]].
                     entailer!. easy.
                 --- Intros.
                     assert (heapgraph_has_gen g1 to) by
                         (rewrite Heqg1, lgd_graph_has_gen; subst g';
                          rewrite <- lcv_graph_has_gen; assumption).
                     assert (heapgraph_has_block g1 (new_copied_v g to)) by
                       (subst g1; rewrite <- lgd_heapgraph_has_block;
                       rewrite Heqg'; apply lcv_heapgraph_has_block_new; assumption).
                     forward_call (rsh, sh, gv, fi, ti, g3, t_info3, f_info, roots',
                                   outlier, from, to, depth - 1,
                                   (@inr Z _ (new_copied_v g to, i))).
                     +++ apply prop_right. simpl. rewrite sub_repr.
                         do 4 f_equal. rewrite H31.
                         first [rewrite sem_add_pi_ptr_special' |
                                rewrite sem_add_pl_ptr_special']; auto.
                         *** simpl. f_equal.
                             rewrite <- (lgd_heapgraph_block_ptr_eq g' e v1), <- Heqg1.
                             subst v1. apply (fl_heapgraph_block_ptr _ _ _ _ _ _ H64 H61).
                             apply heapgraph_has_block_in_closure; assumption.
                         *** rewrite <- H31. assumption.
                     +++ split3; [| |split].
                         *** destruct H53 as [_ [_ [? _]]].
                             apply (fl_heapgraph_has_block _ _ _ _ _ _ H64 H61 _ H65).
                         *** erewrite <- fl_block_fields; eauto. subst g1.
                             unfold lgraph_copy_v. subst n'.
                             rewrite <- lgd_raw_fld_length_eq.
                             subst g'. rewrite lcv_vlabel_new.
                             assumption. rewrite v0. lia.
                         *** erewrite <- fl_block_mark; eauto. subst g1 from.
                             rewrite <- lgd_block_mark_eq. subst g'.
                             rewrite lcv_vlabel_new; try assumption.
                         *** simpl; lia.
                     +++ Intros vret. destruct vret as [[g4 t_info4] roots4].
                         simpl fst in *. simpl snd in *. Exists g4 t_info4.
                         simpl in H67. subst roots4.
                         assert (heapgraph_generation_base g3 from = heapgraph_generation_base g4 from). {
                           eapply fr_gen_start; eauto.
                           erewrite <- fl_graph_has_gen; eauto. } rewrite H67.
                         assert (limit_address g3 t_info3 from =
                                 limit_address g4 t_info4 from). {
                           unfold limit_address. f_equal. 2: assumption. f_equal.
                           destruct H70 as [? [? _]]. rewrite H71. reflexivity. }
                         rewrite H71.
                         assert (next_address t_info3 to = next_address t_info4 to). {
                           unfold next_address. f_equal. destruct H70. assumption. }
                         rewrite H72. clear H67 H71 H72.
                         assert (thread_info_relation t_info' t_info4) by
                             (apply tir_trans with t_info3; assumption).
                         assert (forward_loop
                                   from to (Z.to_nat (depth - 1))
                                   (sublist 0 (i + 1)
                                            (heapgraph_field_pairs g1 (new_copied_v g to)))
                                   g1 g4). {
                            eapply forward_loop_add_tail_vpp; eauto. subst n' g1 from.
                           rewrite <- lgd_raw_fld_length_eq. subst g'.
                           rewrite lcv_vlabel_new; assumption. }
                         entailer!.
                 --- Intros g3 t_info3.
                     assert (thread_info_relation t_info t_info3) by
                         (apply tir_trans with t_info';
                          [split; [| split]|]; assumption).
                     rewrite sublist_all in H60.
                     2: { rewrite Z.le_lteq. right. subst n' g1 from.
                          rewrite heapgraph_field_pairs__Zlength,  <- lgd_raw_fld_length_eq.
                          subst g'; rewrite lcv_vlabel_new; auto. }
                     Opaque super_compatible. Exists g3 t_info3 roots.
                     entailer!. simpl.
                     replace (Z.to_nat depth) with (S (Z.to_nat (depth - 1))) by
                         (rewrite <- Z2Nat.inj_succ; [f_equal|]; lia).
                     rewrite Heqc, H12. simpl.
                     constructor; [reflexivity | assumption..].
                     Transparent super_compatible.
              ** assert (depth = 0) by lia. subst depth. clear H56.
                 deadvars!. clear Heqnv. forward.
                 Exists g1 t_info' roots. entailer!. simpl. rewrite Heqc.
                 simpl field2forward. rewrite H12. simpl. now constructor.
      * forward_if. 1: exfalso; apply H22'; reflexivity.
        rewrite H21 in n0. forward.
        Exists g t_info roots. entailer!; simpl.
        -- rewrite H12, Heqc. simpl. split; auto. split; [|split].
           ++ constructor. auto.
           ++ split; auto.
           ++ apply tir_id.
        -- unfold thread_info_rep. entailer!.
Admitted.
