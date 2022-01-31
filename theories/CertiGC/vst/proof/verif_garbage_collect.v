From VST Require Import floyd.proofauto.
From VST Require Import floyd.library.

From CertiGC Require Import model.GCGraph.
From CertiGC Require Import vst.ast.env_graph_gc.
From CertiGC Require Import vst.clightgen.gc.
From CertiGC Require Import vst.model.c_constants.
From CertiGC Require Import vst.model.spatial_gcgraph.
From CertiGC Require Import vst.spec.gc_spec.

Local Open Scope logic.

Lemma sem_sub_pp_space_capacity: forall s,
    isptr (space_base s) ->
    force_val
      (sem_sub_pp
        int_or_ptr_type
        (offset_val (WORD_SIZE * space_capacity s) (space_base s))
        (space_base s)
      ) =
    if Archi.ptr64
      then Vlong (Int64.repr (space_capacity s))
      else Vint (Int.repr (space_capacity s)).
Proof.
  intros.
  destruct (space_base s); try contradiction ; simpl.
  destruct (eq_block b b) ; try congruence.
  unfold sem_sub_pp ; destruct eq_block ; try easy.
  inv_int i.
  rewrite ptrofs_add_repr, ptrofs_sub_repr.
  replace
    (ofs + WORD_SIZE * (space_capacity s) - ofs)
    with (WORD_SIZE * (space_capacity s))%Z
    by lia.
  simpl.
  pose proof (space_capacity__signed_range s).
  unfold Ptrofs.divs.
  rewrite !Ptrofs.signed_repr by rep_lia.
  unfold vptrofs, Archi.ptr64, WORD_SIZE.
  rewrite Z.mul_comm, Z.quot_mul by lia.
  now first [rewrite ptrofs_to_int64_repr | rewrite ptrofs_to_int_repr].
Qed.

Lemma sem_sub_pp_remaining_space: forall s,
    isptr (space_base s) ->
    force_val
      (sem_sub_pp
        int_or_ptr_type
        (offset_val (WORD_SIZE * (space_capacity s - space_remembered s)) (space_base s))
        (offset_val (WORD_SIZE * space_allocated s) (space_base s))
      ) =
    if Archi.ptr64
      then Vlong (Int64.repr (space_capacity s - space_remembered s - space_allocated s))
      else Vint (Int.repr (space_capacity s - space_remembered s - space_allocated s)).
Proof.
  intros.
  destruct (space_base s); try contradiction ; simpl.
  destruct (eq_block b b) ; try congruence.
  unfold sem_sub_pp ; destruct eq_block ; try easy.
  inv_int i.
  rewrite ptrofs_add_repr.
  rewrite ptrofs_add_repr.
  rewrite ptrofs_sub_repr.
  replace
    (ofs + WORD_SIZE * (space_capacity s - space_remembered s) - (ofs + WORD_SIZE * space_allocated s))
    with (WORD_SIZE * (space_capacity s - space_remembered s - space_allocated s))%Z
    by lia.
  simpl.
  pose proof (space_remaining__signed_range s).
  unfold Ptrofs.divs.
  rewrite !Ptrofs.signed_repr by rep_lia.
  unfold vptrofs, Archi.ptr64, WORD_SIZE.
  rewrite Z.mul_comm, Z.quot_mul by lia.
  now first [rewrite ptrofs_to_int64_repr | rewrite ptrofs_to_int_repr].
Qed.

Lemma t_info_space_address: forall t_info i,
    0 <= i -> isptr (ti_heap_p t_info) ->
    (if Archi.ptr64
      then force_val (sem_add_ptr_long space_type (offset_val 0 (ti_heap_p t_info)) (Vlong (Int64.repr i)))
      else force_val (sem_add_ptr_int space_type Signed (offset_val 0 (ti_heap_p t_info)) (vint i)))
      = space_address t_info (Z.to_nat i).
Proof.
  intros. rewrite isptr_offset_val_zero by assumption. simpl.
  first [rewrite sem_add_pi_ptr_special' | rewrite sem_add_pl_ptr_special']; auto.
  unfold space_address. rewrite Z2Nat.id by lia. simpl. f_equal.
Qed.

Ltac tc_val_Znth := entailer!; rewrite Znth_map by assumption;
                    unfold space_tri; apply isptr_is_pointer_or_null;
                    try assumption.

Lemma body_garbage_collect:
  semax_body Vprog Gprog f_garbage_collect garbage_collect_spec.
Proof.
  start_function.
  (* unfold a bunch of stuff. *)
  assert (Tf:
    forall (tif: thread_info) (j: Z) (Hj: 0 <= j),
    offset_val (sizeof (Tstruct _space noattr) * j) (ti_heap_p tif) = space_address tif (Z.to_nat j)
  ).
  {
    intros.
    unfold space_address.
    now rewrite Z2Nat.id.
  }
  sep_apply (create_mem_mgr gv).
  unfold before_gc_thread_info_rep, heap_struct_rep.
  Intros.
  (* lets go *)
  forward.
  (* unpack our super_compatible assumptions *)
  pose proof H as H2.
  destruct H as [H _].
  pose proof (gt_gs_compatible _ _ H _ (heapgraph_has_gen__O _)) as H3.
  destruct H3 as [H3 H4 H5 HH6].
  simpl in H3, H4, H5, HH6.
  (* get ready to talk about the nursery *)
  replace
    (heap_head (ti_heap t_info))
    with (nth_space t_info 0).
  2: {
    destruct (heap_head__cons (ti_heap t_info)) as [hs [hl [H6 H7]]].
    unfold nth_space.
    now rewrite H6, H7.
  }
  assert
    (isptr (space_base (nth_space t_info 0)))
    as H6
    by (rewrite <- H3; apply generation_base__isptr).
  (* lets go *)
  do 2 forward.
  (* cleanup & simplify the context *)
  deadvars!.
  rewrite upd_Znth0_old.
  2: {
    pose proof (@Zlength_nonneg (val * (val * (val * val))) (map space_tri (tl (heap_spaces (ti_heap t_info))))) as H7.
    rewrite Zlength_cons.
    lia.
  }
  rewrite sublist_1_cons, Zlength_cons, sublist_same, Znth_0_cons by lia.
  simpl fst ; simpl snd.
  (* fold everything back up again *)
  fold (space_tri (nth_space t_info 0)).
  rewrite <- map_cons.
  replace
    (nth_space t_info 0 :: tl (heap_spaces (ti_heap t_info)))
    with (heap_spaces (ti_heap t_info)).
  2: {
    destruct (heap_head__cons (ti_heap t_info)) as [hs [hl [H7 _]]].
    unfold nth_space.
    now rewrite H7.
  }
  gather_SEP (data_at sh heap_type _ _) (heap_rest_rep _).
  gather_SEP (data_at sh thread_info_type _ _) (data_at sh heap_type _ _ * heap_rest_rep _).
  replace_SEP 0 (thread_info_rep sh t_info ti).
  {
    unfold thread_info_rep, heap_struct_rep.
    entailer!.
    do 2 (unfold_data_at (data_at _ _ _ _); cancel).
  }
  (* lets go *)
  forward_for_simple_bound
    11
    (EX i: Z, EX g': HeapGraph, EX roots': roots_t, EX t_info': thread_info,
     PROP (super_compatible (g', t_info', roots') f_info outlier;
           garbage_collect_condition g' t_info' roots' f_info;
           heapgraph_can_copy_except g' (Z.to_nat i);
           firstn_gen_clear g' (Z.to_nat i);
           garbage_collect_loop f_info (nat_inc_list (Z.to_nat i)) roots g roots' g';
           heapgraph_has_gen g' (Z.to_nat i)
           )
     LOCAL (temp _h (ti_heap_p t_info'); temp _fi fi; temp _ti ti;
            gvars gv)
     SEP (thread_info_rep sh t_info' ti;
          mem_mgr gv; MSS_constant gv;
          all_string_constants rsh gv;
          fun_info_rep rsh f_info fi;
          outlier_rep outlier;
          graph_rep g';
          ti_token_rep t_info')).
  {
    Exists g roots t_info.
    destruct H2 as [H2 [H7 [H8 H9]]].
    pose proof (heapgraph_has_gen__O g) as H10.
    entailer!.
    split; [|split; [|split]] ; try easy.
    + now apply heapgraph_can_copy_except__O.
    + constructor.
  }
  {
    cbv beta.
    Intros g' roots' t_info'.
    unfold thread_info_rep.
    Intros.
    unfold heap_struct_rep.
    assert
      (0 <= i + 1 < Zlength (heap_spaces (ti_heap t_info')))
      as H14
      by (rewrite heap_spaces__size; rep_lia).
    pose proof (space_base_is_pointer_or_null _ _ _ (proj1 H8) H14) as H15.
    (* lets go *)
    forward.
    {
      entailer!.
      now rewrite Znth_map.
    }
    rewrite Znth_map by assumption.
    unfold space_tri at 1.
    forward_if
      (EX g1: HeapGraph, EX t_info1: thread_info,
       PROP (super_compatible (g1, t_info1, roots') f_info outlier;
             garbage_collect_condition g1 t_info1 roots' f_info;
             heapgraph_can_copy_except g1 (Z.to_nat i);
             firstn_gen_clear g1 (Z.to_nat i);
             new_gen_relation (Z.to_nat (i + 1)) g' g1;
             heapgraph_has_gen g1 (Z.to_nat (i + 1))
        )
       LOCAL (temp _h (ti_heap_p t_info1); temp _fi fi; temp _ti ti;
              gvars gv; temp _i (Vint (Int.repr i)))
       SEP (thread_info_rep sh t_info1 ti;
            ti_token_rep t_info1;
            mem_mgr gv; MSS_constant gv;
            all_string_constants rsh gv;
            fun_info_rep rsh f_info fi;
            outlier_rep outlier;
            graph_rep g1)).
    {
      remember
        (space_base (Znth (i + 1) (heap_spaces (ti_heap t_info'))))
        as v0 eqn:Heqv0.
      Transparent denote_tc_test_eq.
      destruct v0; try contradiction.
      - simpl in H15.
        subst i0.
        simpl.
        entailer!.
      - simpl.
        entailer!.
        assert (isptr (Vptr b i0)) as H23 by exact I.
        rewrite Heqv0 in *.
        pull_left (heap_rest_rep (ti_heap t_info')).
        pull_left (graph_rep g').
        destruct H8 as [H8 H24].
        rewrite <- (space_base_isptr_iff g') in H23 by assumption.
        sep_apply (graph_and_heap_rest_valid_ptr g' t_info' (Z.to_nat (i + 1))).
        {
          replace
            (Z.to_nat (i + 1))
            with (S (Z.to_nat i))
            in *
            by lia.
          apply (gc_cond_implies_do_gen_cons _ _ _ _ (Z.to_nat i)) in H9 ; try easy.
          destruct H9.
          lia.
        }
        {
          now destruct H9 as [? [? [? [? ?]]]].
        }
        rewrite nth_space_Znth, Z2Nat.id by lia.
        sep_apply (valid_pointer_weak (space_base (Znth (i + 1) (heap_spaces (ti_heap t_info'))))).
        apply extend_weak_valid_pointer.
    }
    {
      assert (0 <= i < Zlength (heap_spaces (ti_heap t_info'))) as H17 by lia.
      pose proof (space_base_isptr _ _ _ (proj1 H8) H17 H13) as H18.
      forward.
      {
        entailer!.
        rewrite Znth_map by assumption.
        unfold space_tri.
        now apply isptr_is_pointer_or_null, isptr_offset_val'.
      }
      rewrite Znth_map by assumption.
      unfold space_tri at 1.
      forward.
      {
        entailer!.
        rewrite Znth_map by assumption.
        unfold space_tri.
        now apply isptr_is_pointer_or_null.
      }
      rewrite Znth_map by assumption.
      unfold space_tri at 1.
      forward.
      {
        entailer!.
        destruct (space_base (Znth i (heap_spaces (ti_heap t_info')))) ; try contradiction.
        simpl.
        unfold denote_tc_samebase.
        apply prop_right.
        now destruct (peq b b).
      }
      change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 3%N |}) with int_or_ptr_type.
      simpl sem_binary_operation'.
      rewrite (sem_sub_pp_space_capacity (Znth i (heap_spaces (ti_heap t_info')))) by assumption.
      (* relate capacity to generation size *)
      replace
        (space_capacity (Znth i (heap_spaces (ti_heap t_info'))))
        with (generation_size (Z.to_nat i)).
      2: {
        pose proof H9 as H19.
        destruct H19 as [_ [_ [_ [_ H19]]]].
        pose proof (ti_size_gen _ _ _ (proj1 H8) H13 H19) as H20.
        unfold gen_size in H20.
        now rewrite nth_space_Znth, Z2Nat.id in H20 by lia.
      }
      (* cleanup *)
      assert_PROP (isptr (ti_heap_p t_info')) by entailer!.
      gather_SEP (data_at sh heap_type _ _) (heap_rest_rep _).
      gather_SEP (data_at sh thread_info_type _ ti) (data_at sh heap_type _ _ * heap_rest_rep _).
      replace_SEP 0 (thread_info_rep sh t_info' ti)
        by (unfold thread_info_rep, heap_struct_rep; entailer!).
      pose proof H14 as H20.
      rewrite heap_spaces__size in H20.
      unfold thread_info_rep.
      Intros.
      rewrite hsr_single_explicit with (i := i + 1) ; try easy.
      2: {
        now try rewrite Zlength_map, heap_spaces__size.
      }
      Intros.
      freeze [0;2;3;4;8;9;10] FR.
      sep_apply (
        data_at_data_at_
          sh space_type
          (Znth (i + 1) (map space_tri (heap_spaces (ti_heap t_info'))))
          (space_address t_info' (Z.to_nat (i + 1)))
      ).
      pose proof (t_info_space_address _ _ (proj1 H14) H19) as H21.
      simpl in H21.
      assert
        (0 <= 2 * generation_size (Z.to_nat i) < MAX_SPACE_SIZE)
        as H22
        by (rewrite ngs_S by lia; apply ngs_range; rep_lia).
      forward_call (sh, (space_address t_info' (Z.to_nat (i + 1))), (2 * generation_size (Z.to_nat i))%Z, gv, rsh).
      {
        pose proof (ngs_int_singed_range i ltac:(lia)) as H29.
        pose proof (ngs_int_singed_range (i + 1) ltac:(lia)) as H30.
        simpl in H29, H30.
        first [ rewrite Int64.signed_repr | rewrite Int.signed_repr ] ; try easy.
        now rewrite (ngs_S i ltac:(lia)).
      }
      {
        simpl.
        entailer!.
        f_equal ; now rewrite Tf.
      }
      rewrite ngs_S by lia.
      Intros p.
      rewrite ngs_S in H22 by lia.
      assert
        (0 <= 0 <= (generation_size (Z.to_nat (i + 1))))
        as Hso
        by lia.
      rewrite data_at__isptr.
      Intros.
      remember ({|
        space_base := p;
        space_allocated := 0;
        space_remembered := 0;
        space_capacity := generation_size (Z.to_nat (i + 1));
        space_sh := Ews;
        space_allocated__lower_bound := ltac:(easy);
        space_remembered__lower_bound := ltac:(easy);
        space__order := Hso;
        space__upper_bound := proj2 H22;
      |}) as sp.
      remember ({|
          generation_base := p;
          generation_block_count := O;
          generation_remember_count := O;
          generation_sh := Ews;
          generation_base__isptr := Pp;
          generation_sh__writable := writable_Ews;
        |}) as gi.
      assert
        (forall (gr: HeapGraph) (gen: nat), generation_space_compatible gr (gen, gi, sp))
        as H23.
      {
        intros.
        red.
        subst sp gi.
        constructor ; simpl ; dintuition idtac.
        
      }
      remember (heapgraph_generations_append g' gi) as g1.
      remember (ti_add_new_space t_info' sp _ H20) as t_info1.
      pose proof H16 as H24.
      rewrite <- (space_base_isnull_iff g') in H16 ; try easy.
      2: {
        apply (proj1 H8).
      }
      assert
        (generation_block_count gi = O)
        as H25
        by (subst gi; simpl; reflexivity).
      assert
        (super_compatible (g1, t_info1, roots') f_info outlier)
        as H26.
      {
        subst g1 t_info1.
        apply super_compatible_add ; try easy.
        now replace (i + 1 - 1) with i by lia.
      }
      assert
        (firstn_gen_clear g1 (Z.to_nat i))
        as H27
        by (subst g1; apply firstn_gen_clear_add; assumption).
      assert (new_gen_relation (Z.to_nat (i + 1)) g' g1) as H28.
      {
        subst g1.
        red.
        rewrite if_false by assumption.
        exists gi.
        now split.
      }
      gather_SEP (malloc_token Ews (tarray int_or_ptr_type (generation_size (Z.to_nat (i + 1)))) p) (ti_token_rep t_info').
      assert
        (space_capacity sp = generation_size (Z.to_nat (i + 1)))
        as H29
        by (subst sp; simpl; reflexivity).
      rewrite <- H29.
      assert
        (space_base sp = p)
        as H30
        by (subst sp; simpl; reflexivity).
      rewrite <- H30.
      assert
        (space_base sp <> nullval)
        as H31
        by (rewrite H30; destruct p; try contradiction; intro; inversion H31).
      sep_apply (ti_token_rep_add t_info' sp (i + 1) H20 H24 H31) ; try easy.
      replace ( space_base sp,
              ( space_base sp,
              ( offset_val (WORD_SIZE * space_capacity sp) (space_base sp)
              , offset_val (WORD_SIZE * space_capacity sp) (space_base sp)
              ))) with
          (space_tri sp).
      2: {
        unfold space_tri.
        subst sp ; simpl.
        rewrite isptr_offset_val_zero by assumption.
        now replace
          (generation_size (Z.to_nat (i + 1)) - 0)
          with (generation_size (Z.to_nat (i + 1)))
          by lia.
      }
      thaw FR.
      gather_SEP
        (data_at sh space_type _ _)
        (data_at sh (tarray space_type
                            (Zlength
                                (sublist (i + 1 + 1) 12 (map space_tri (heap_spaces (ti_heap t_info')))))) _
                  (offset_val (sizeof space_type)
                              (offset_val (SPACE_STRUCT_SIZE * (i + 1)) (ti_heap_p t_info'))))
        (data_at sh (tarray space_type (i + 1)) _
                  (ti_heap_p t_info')).
      rewrite sepcon_assoc, (heap_struct_rep_add t_info' sh sp (i + 1) H20), <- Heqt_info1.
      replace
        (ti_heap_p t_info')
        with (ti_heap_p t_info1)
        by (subst t_info1; simpl; reflexivity).
      replace
        (ti_args t_info')
        with (ti_args t_info1)
        by (subst t_info1; simpl; reflexivity).
      replace_SEP 5 (space_rest_rep sp).
      {
        unfold space_rest_rep.
        rewrite if_false by assumption.
        replace (space_sh sp) with Ews by (subst sp; simpl; reflexivity).
        replace (space_allocated sp) with 0 by (subst sp; simpl; reflexivity).
        rewrite Z.sub_0_r, Z.mul_0_r, isptr_offset_val_zero by (subst; simpl; assumption).
        entailer!.
      }
      gather_SEP (heap_rest_rep (ti_heap t_info')) (space_rest_rep sp).
      rewrite (heap_rest_rep_add _ _ (i + 1) H20), <- Heqt_info1 by assumption.
      gather_SEP
        (data_at sh thread_info_type _ _)
        (heap_struct_rep _ _ _)
        (heap_rest_rep _).
      replace_SEP 0 (thread_info_rep sh t_info1 ti) by (unfold thread_info_rep; entailer!).
      rewrite (graph_rep_add g' gi); auto.
      2: {
        apply graph_unmarked_copy_compatible.
        now destruct H9 as [? [? [? [? ?]]]].
      }
      2: {
        now destruct H9 as [? [? [? [? ?]]]].
      }
      rewrite <- Heqg1.
      assert (heapgraph_has_gen g1 (Z.to_nat (i + 1))) as H32.
      {
        subst g1.
        rewrite heapgraph_has_gen__heapgraph_generations_append.
        right.
        clear -H13 H16 H7.
        unfold heapgraph_has_gen in *.
        replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat in * ; try lia.
      }
      assert
        (heapgraph_can_copy_except g1 (Z.to_nat i))
        as H33
        by (subst g1; apply stcte_add; auto; subst gi; simpl; reflexivity).
      assert
        (garbage_collect_condition g1 t_info1 roots' f_info)
        as H34
        by (subst g1 t_info1; apply gcc_add; assumption).
      Opaque super_compatible.
      Exists g1 t_info1.
      entailer!.
    }
    {
      forward.
      remember
        (space_base (Znth (i + 1) (heap_spaces (ti_heap t_info'))))
        as v eqn:Heqv.
      assert (isptr (space_base (Znth (i + 1) (heap_spaces (ti_heap t_info'))))).
      {
        destruct v ; try easy.
        + simpl in H15.
          now subst i0.
        + now rewrite <- Heqv.
      }
      subst v.
      rewrite <- (space_base_isptr_iff g') in H17 ; try easy.
      2: {
        now destruct H8.
      }
      assert
        (new_gen_relation (Z.to_nat (i + 1)) g' g')
        as H18
        by (unfold new_gen_relation; rewrite if_true; auto).
      Exists g' t_info'.
      unfold thread_info_rep, heap_struct_rep.
      entailer!.
    }
    Intros g1 t_info1.
    forward_if True ; try easy.
    {
      forward.
      entailer!.
    }
    Intros.
    assert_PROP (isptr (ti_heap_p t_info1))
      as H22
      by (unfold thread_info_rep, heap_struct_rep; entailer!).
    assert
      (Z.to_nat (i + 1) = S (Z.to_nat i))
      as H23
      by (rewrite Z2Nat.inj_add by lia; simpl; lia).
    assert
      (do_generation_condition g1 t_info1 roots' f_info (Z.to_nat i) (Z.to_nat (i + 1)))
      as H24.
    {
      rewrite H23 in *.
      apply gc_cond_implies_do_gen_cons ; try easy.
      apply (proj1 H16).
    }
    pose proof (t_info_space_address _ _ (proj1 H7) H22) as H25.
    pose proof (t_info_space_address _ _ (proj1 H14) H22) as H26.
    forward_call (rsh, sh, gv, fi, ti, g1, t_info1, f_info, roots', outlier, (Z.to_nat i), (Z.to_nat (i + 1))).
    {
      simpl.
      entailer!.
      now rewrite !Tf.
    }
    Intros vret.
    destruct vret as [[g2 t_info2] roots2].
    simpl fst in *.
    simpl snd in *.
    replace
      (ti_heap_p t_info1)
      with (ti_heap_p t_info2)
      by (now rewrite (thread_info_relation__ti_heap H28)).
    unfold thread_info_rep, heap_struct_rep.
    Intros.
    assert
      (heapgraph_has_gen g2 (Z.to_nat (i + 1)))
      as H30
      by (rewrite <- do_gen_graph_has_gen; eauto).
    assert
      (heapgraph_has_gen g2 (Z.to_nat i))
      as H31
      by (red in H30 |-* ; lia).
    assert
      (isptr (space_base (Znth i (heap_spaces (ti_heap t_info2)))))
      as H32.
    {
      pose proof (generation__space__compatible__base (gt_gs_compatible _ _ (proj1 H27) _ H31)) as H32.
      simpl in H32.
      rewrite <- (Z2Nat.id i), <- nth_space_Znth, <- H32 by lia.
      apply generation_base__isptr.
    }
    assert
      (0 <= i < Zlength (heap_spaces (ti_heap t_info2)))
      as H33
      by (rewrite heap_spaces__size; rep_lia).
    forward.
    {
      tc_val_Znth.
      now rewrite isptr_offset_val.
    }
    forward.
    {
      tc_val_Znth.
    }
    rewrite Znth_map by assumption.
    unfold space_tri at 1 2.
    assert
      (0 <= i + 1 < Zlength (heap_spaces (ti_heap t_info2)))
      as H34
      by (rewrite heap_spaces__size; rep_lia).
    assert
      (isptr (space_base (Znth (i + 1) (heap_spaces (ti_heap t_info2)))))
      as H35.
    {
      pose proof (generation__space__compatible__base (gt_gs_compatible _ _ (proj1 H27) _ H30)) as HH.
      simpl in HH.
      rewrite <- (Z2Nat.id (i + 1)), <- nth_space_Znth, <- HH by lia.
      apply generation_base__isptr.
    }
    forward.
    {
      tc_val_Znth.
      now rewrite isptr_offset_val.
    }
    forward.
    {
      tc_val_Znth.
      now rewrite isptr_offset_val.
    }
    rewrite Znth_map by assumption.
    unfold space_tri at 1 2.
    rewrite H23 in *.
    assert
      (garbage_collect_condition g2 t_info2 roots2 f_info)
      as H36
      by (eapply (do_gen_gcc g1 t_info1 roots'); eauto).
    assert
      (firstn_gen_clear g2 (Z.to_nat (i + 1)))
      as H37
      by (rewrite H23; eapply do_gen_firstn_gen_clear; eauto).
    assert
      (heapgraph_can_copy_except g2 (Z.to_nat (i + 1)))
      as H38
      by (rewrite H23; eapply do_gen_stcte; eauto).
    gather_SEP
      (data_at sh thread_info_type _ _)
      (data_at sh heap_type _ (ti_heap_p t_info2))
      (heap_rest_rep (ti_heap t_info2)).
    rewrite sepcon_assoc.
    replace_SEP 0 (thread_info_rep sh t_info2 ti)
      by (unfold thread_info_rep, heap_struct_rep; entailer!).
    assert
      (garbage_collect_loop f_info (nat_inc_list (Z.to_nat (i + 1))) roots g roots2 g2)
      as H39
      by (rewrite H23, nat_inc_list_S; eapply gcl_add_tail; eauto).
    replace_SEP 5 (ti_token_rep t_info2)
      by (erewrite ti_rel_token_the_same; eauto; entailer!).
    forward_if.
    {
      destruct (space_base (Znth i (heap_spaces (ti_heap t_info2)))) ; try easy.
      destruct (space_base (Znth (i + 1) (heap_spaces (ti_heap t_info2)))) ; try easy.
      Transparent denote_tc_samebase.
      unfold denote_tc_samebase.
      simpl.
      Opaque denote_tc_samebase.
      entailer!.
    }
    {
      rewrite sem_sub_pp_space_capacity in H40 ; try easy.
      rewrite sem_sub_pp_remaining_space in H40; try easy.
      simpl in H40.
      apply typed_true_of_bool in H40.
      rewrite negb_true_iff in H40.
      match goal with
      | H : Int64.lt _ _ = false |- _ => apply lt64_repr_false in H
      | H : Int.lt _ _ = false |- _ => apply lt_repr_false in H
      end.
      2: {
        apply space_remaining__repable_signed.
      }
      2: {
        apply space_capacity__repable_signed.
      }
      assert (heapgraph_generation_can_copy g2 (Z.to_nat i) (S (Z.to_nat i))) as H41.
      {
        red.
        destruct H27 as [H27 _].
        destruct H36 as [_ [_ [_ [_ H36]]]].
        do 2 (erewrite <- ti_size_gen; eauto).
        rewrite <- H23 in *.
        unfold gen_size, heapgraph_generation_size.
        destruct (gt_gs_compatible _ _ H27 _ H30) as [_ _ H41 H42].
        simpl in H41, H42.
        pose proof (space_remembered__lower_bound (Znth (i + 1) (heap_spaces (ti_heap t_info2)))) as H43.
        unfold heapgraph_remember_size.
        rewrite H41, H42, !nth_space_Znth, !Z2Nat.id ; try lia.
      }
      assert
        (graph_thread_info_compatible g2 t_info2)
        as H42
        by (apply (proj1 H27)).
      assert
        (graph_gen_clear g2 O)
        as H43
        by (apply H37; rewrite H23; lia).
      forward_call (rsh, sh, gv, fi, ti, g2, t_info2, f_info, roots2).
      forward.
      Exists g2 t_info2 roots2.
      entailer!.
      split.
      - exists (Z.to_nat i).
        now rewrite <- H23 at 1.
      - rewrite H23 in H38.
        eapply heapgraph_can_copy__complete ; eauto.
    }
    forward.
    Intros.
    Exists g2 roots2 t_info2.
    rewrite <- H23 in *.
    entailer!.
  }
  Intros g2 roots2 t_info2.
  unfold all_string_constants.
  Intros.
  forward_call ((gv ___stringlit_12), (map init_data2byte (gvar_init v___stringlit_12)), rsh).
  now exfalso.
Qed.
