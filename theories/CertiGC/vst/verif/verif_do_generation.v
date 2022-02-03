From VST Require Import floyd.proofauto.

From CertiGC Require Import model.GCGraph.
From CertiGC Require Import vst.ast.env_graph_gc.
From CertiGC Require Import vst.clightgen.gc.
From CertiGC Require Import vst.cmodel.constants.
From CertiGC Require Import vst.cmodel.spatial_gcgraph.
From CertiGC Require Import vst.spec.gc_spec.

Local Open Scope logic.

Lemma body_do_generation: semax_body Vprog Gprog f_do_generation do_generation_spec.
Proof.
  start_function.
  pose proof H as H2.
  destruct H2 as [H2 _].
  pose proof H0 as H3.
  destruct H3 as [H3 [H4 [H5 _]]].
  assert
    (generation_space_compatible g (from, heapgraph_generation g from, nth_space t_info from))
    as H6
    by (apply gt_gs_compatible; assumption).
  destruct H6 as [H6 H7 H8 HH9].
  simpl in H6, H7, H8, HH9.
  assert
    (generation_space_compatible g (to, heapgraph_generation g to, nth_space t_info to))
    as H9
    by (apply gt_gs_compatible; assumption).
  destruct H9 as [H9 H10 H11].
  simpl in H9, H10, H11.
  assert
    (isptr (space_base (nth_space t_info from)))
    as H12
    by (rewrite <- H6; apply generation_base__isptr).
  assert
    (isptr (space_base (nth_space t_info to)))
    as H13
    by (rewrite <- H9; apply generation_base__isptr).
  assert
    (forall gen, heapgraph_has_gen g gen -> Z.of_nat gen < MAX_SPACES)
    as HS.
  {
    intros.
    unfold heapgraph_has_gen in H14.
    destruct H as [[_ [_ ?]] _].
    rewrite <- (heap_spaces__size (ti_heap t_info)).
    rewrite Zlength_correct.
    apply inj_lt.
    now apply Nat.lt_le_trans with (Datatypes.length (generations (heapgraph_generations g))).
  }
  assert
    (Z.of_nat from < MAX_SPACES)
    as H14
    by (apply HS; assumption).
  assert
    (Z.of_nat to < MAX_SPACES)
    as H15
    by (apply HS; assumption).
  clear HS.
  freeze [0;1;2;3] FR.
  localize [space_struct_rep sh t_info from; space_struct_rep sh t_info to].
  unfold space_struct_rep, space_tri.
  do 5 forward.
  gather_SEP
    (data_at sh space_type _ (space_address t_info from))
    (data_at sh space_type _ (space_address t_info to)).
  replace_SEP 0
    (space_struct_rep sh t_info from * space_struct_rep sh t_info to)
    by (unfold space_struct_rep; entailer!).
  unlocalize [thread_info_rep sh t_info ti].
  {
    now apply thread_info_rep_ramif_stable.
  }
  remember
    (space_base (nth_space t_info from))
    as from_p eqn:Heqfrom_p.
  remember
    (space_base (nth_space t_info to))
    as to_p eqn:Heqto_p.
  remember
    (WORD_SIZE * (space_capacity (nth_space t_info to) - space_remembered (nth_space t_info to)))%Z
    as to_total eqn:Heqto_total.
  remember
    (WORD_SIZE * space_allocated (nth_space t_info to))%Z
    as to_used eqn:Heqto_used.
  remember
    (WORD_SIZE * space_allocated (nth_space t_info from))%Z
    as from_used eqn:Heqfrom_used.
  assert
    (is_true (sameblock (offset_val from_used from_p) from_p))
    as H16.
  {
    destruct from_p; try contradiction.
    simpl.
    now destruct peq.
  }
  assert
    (is_true (sameblock (offset_val to_total to_p) (offset_val to_used to_p)))
    as H17.
  {
    destruct to_p; try contradiction.
    simpl.
    now destruct peq.
  }
  forward_if True.
  {
    forward.
    entailer!.
  }
  {
    exfalso.
    destruct from_p; try contradiction.
    inv_int i.
    rename H20 into H20.
    destruct to_p; try contradiction.
    inv_int i0.
    rename H21 into H21.
    simpl in H18; unfold sem_sub_pp in H18; destruct eq_block in H18; [|easy].
    rewrite !ptrofs_add_repr, !ptrofs_sub_repr, !if_true in H18 by easy.
    simpl in H18.
    replace
      (ofs0 + to_total - (ofs0 + to_used))
      with (to_total - to_used)
      in H18
      by lia.
    replace
      (ofs + from_used - ofs)
      with from_used
      in H18
      by lia.
    assert
      (Ptrofs.min_signed <= from_used <= Ptrofs.max_signed)
      as H19
      by (subst; apply space_allocated__signed_range).
    assert
      (Ptrofs.min_signed <= to_total - to_used <= Ptrofs.max_signed)
      as H22.
    {
      subst.
      pose proof (space_remaining__signed_range (nth_space t_info to)) as H22.
      repeat rewrite <- Z.mul_sub_distr_l.
      repeat rewrite <- Z.mul_sub_distr_l in H22.
      lia.
    }
    unfold Ptrofs.divs in H18.
    rewrite !Ptrofs.signed_repr in H18 by rep_lia.
    subst.
    unfold WORD_SIZE in H18.
    rewrite <- Z.mul_sub_distr_l, Z.mul_comm, Z.quot_mul, Z.mul_comm, Z.quot_mul in H18 by lia.
    first [rewrite !ptrofs_to_int_repr in H18 | rewrite !ptrofs_to_int64_repr in H18 by auto].
    red in H18.
    remember (if Archi.ptr64
              then Int64.lt
                    (
                      Int64.repr
                        ( space_capacity (nth_space t_info to)
                        - space_remembered (nth_space t_info to)
                        - space_allocated (nth_space t_info to))
                    )
                    (Int64.repr (space_allocated (nth_space t_info from)))
              else Int.lt
                    (
                      Int.repr
                        ( space_capacity (nth_space t_info to)
                        - space_remembered (nth_space t_info to)
                        - space_allocated (nth_space t_info to))
                    )
                    (Int.repr (space_allocated (nth_space t_info from)))) as lte.
    simpl in Heqlte.
    rewrite <- Heqlte in H18.
    destruct lte; simpl in H18.
    2: {
      inversion H18.
    }
    symmetry in Heqlte.
    match goal with
    | H : Int64.lt _ _ = true |- _ => apply lt64_repr in H
    | H : Int.lt _ _ = true |- _ => apply lt_repr in H
    end.
    2: {
      apply space_remaining__repable_signed.
    }
    2: {
      apply space_allocated__repable_signed.
    }
    clear -H8 H3 Heqlte.
    red in H3.
    unfold heapgraph_generation_size, rest_gen_size in H3.
    rewrite H8 in H3.
    repeat rewrite space_remembered__is_zero in *.
    lia.
  }
  Intros.
  localize [space_struct_rep sh t_info from].
  unfold space_struct_rep, space_tri.
  do 2 (forward; [subst from_p; entailer!|]).
  replace_SEP 0
    (space_struct_rep sh t_info from)
    by (unfold space_struct_rep, space_tri; entailer!).
  unlocalize [thread_info_rep sh t_info ti].
  {
    now apply thread_info_rep_ramif_stable_1.
  }
  apply dgc_imply_fc in H0.
  destruct H0 as [H0 [H18 [H19 H20]]].
  rewrite <- Heqfrom_p.
  replace
    from_p
    with (heapgraph_generation_base g from)
    by (subst; unfold heapgraph_generation_base; now rewrite if_true).
  change
    (offset_val (WORD_SIZE * (space_capacity (nth_space t_info from) - space_remembered (nth_space t_info from))) (heapgraph_generation_base g from))
    with (limit_address g t_info from).
  assert_PROP (isptr (space_address t_info to)).
  {
    unfold space_address, thread_info_rep, heap_struct_rep.
    rewrite isptr_offset_val.
    entailer!.
  }
  assert_PROP
    (offset_val WORD_SIZE (space_address t_info to) = next_address t_info to).
  {
    unfold thread_info_rep, heap_struct_rep.
    Intros.
    entailer!.
    unfold space_address, next_address, field_address.
    rewrite if_true.
    - simpl. now rewrite offset_offset_val.
    - destruct H as [[_ [_ H]] _].
      unfold field_compatible in *.
      simpl in *.
      unfold in_members.
      simpl.
      intuition lia.
  }
  thaw FR.
  forward_call (rsh, sh, gv, fi, ti, g, t_info, f_info, roots, outlier, from, to).
  Intros vret.
  rename H27 into HH27.
  destruct vret as [[g1 t_info1] roots1].
  simpl fst in *.
  simpl snd in *.
  freeze [0;1;2;3] FR. 
  replace
    (space_address t_info from)
    with (space_address t_info1 from)
    by (unfold space_address; now rewrite (thread_info_relation__ti_heap H26)).
  assert
    (space_base (nth_space t_info1 from) = heapgraph_generation_base g1 from)
    as H27.
  {
    destruct H23 as [? _].
    destruct H25 as [_ [? _]].
    destruct (gt_gs_compatible _ _ H23 _ H25) as [H27 _ _ _].
    simpl in H27.
    rewrite <- H27.
    unfold heapgraph_generation_base.
    now rewrite if_true.
  }
  assert
    (isptr (space_base (nth_space t_info1 from)))
    as H28.
  {
    rewrite H27.
    unfold heapgraph_generation_base.
    destruct H25 as [_ [H25 _]].
    rewrite if_true by assumption.
    apply generation_base__isptr.
  }
  localize [space_struct_rep sh t_info1 from].
  unfold space_struct_rep, space_tri.
  do 2 forward.
  replace_SEP 0
    (space_struct_rep sh t_info1 from)
    by (unfold space_struct_rep, space_tri; entailer!).
  unlocalize [thread_info_rep sh t_info1 ti].
  {
    now apply thread_info_rep_ramif_stable_1.
  }
  thaw FR.
  rewrite H27.
  replace
    (offset_val (WORD_SIZE * (space_capacity (nth_space t_info1 from) - space_remembered (nth_space t_info1 from))) (heapgraph_generation_base g1 from))
    with (limit_address g1 t_info1 from)
    by (unfold limit_address, gen_size; reflexivity).
  assert_PROP (offset_val WORD_SIZE (space_address t_info to) = next_address t_info1 to).
  {
    unfold thread_info_rep, heap_struct_rep.
    entailer!.
    unfold space_address, next_address, field_address.
    rewrite (thread_info_relation__ti_heap H26), if_true.
    - simpl. now rewrite offset_offset_val.
    - unfold field_compatible in *.
      simpl.
      unfold in_members.
      simpl.
      intuition lia.
  }
  assert
    (closure_has_v g {| addr_gen := to ; addr_block := generation_block_count (heapgraph_generation g to) |})
    as H30
    by (red; simpl; unfold closure_has_index; split; [assumption | lia]).
  replace
    (offset_val to_used to_p)
    with (offset_val (- WORD_SIZE) (heapgraph_block_ptr g1 {| addr_gen := to ; addr_block := generation_block_count (heapgraph_generation g to) |})).
  2: {
    rewrite <- (frr_heapgraph_block_ptr _ _ _ _ _ _ _ H5 H24 _ H30).
    subst.
    unfold heapgraph_block_ptr, heapgraph_block_offset, heapgraph_generation_base.
    simpl.
    rewrite offset_offset_val, H11, H9, if_true by assumption.
    f_equal.
    unfold WORD_SIZE.
    lia.
  }
  eapply frr_closure_has_v in H30; eauto.
  destruct H30 as [H30 H31].
  simpl in H30, H31.
  assert
    (0 < gen_size t_info1 to - space_remembered (nth_space t_info1 to))
    as H32.
  {
    now rewrite <- HH27, <- (thread_info_relation__gen_size H26).
  }
  assert
    (heapgraph_generation_is_unmarked g1 to)
    as H33
    by (eapply (frr_heapgraph_generation_is_unmarked _ _ _ _ g _ g1); eauto).
  forward_call (rsh, sh, gv, fi, ti, g1, t_info1, f_info, roots1, outlier, from, to, generation_block_count (heapgraph_generation g to)).
  Intros vret.
  destruct vret as [g2 t_info2].
  simpl fst in *.
  simpl snd in *.
  forward_if True; Intros; [contradiction | forward; entailer! |].
  replace
    (space_address t_info1 from)
    with (space_address t_info2 from)
    in *
    by (unfold space_address; now rewrite (thread_info_relation__ti_heap H37)).
  assert
    (space_base (nth_space t_info2 from) = heapgraph_generation_base g2 from)
    as HH38.
  {
    destruct H34 as [H34 _].
    destruct H35 as [_ [H35 _]].
    destruct (gt_gs_compatible _ _ H34 _ H35) as [HH38 _ _ _].
    simpl in HH38.
    rewrite <- HH38.
    unfold heapgraph_generation_base.
    now rewrite if_true.
  }
  assert
    (isptr (space_base (nth_space t_info2 from)))
    as H39.
  {
    rewrite HH38.
    unfold heapgraph_generation_base.
    destruct H35 as [_ [H35 _]].
    rewrite if_true by assumption.
    apply generation_base__isptr.
  }
  freeze [0;1;2;3] FR.
  localize [space_struct_rep sh t_info2 from].
  unfold space_struct_rep, space_tri.
  do 2 forward.
  replace_SEP 0
    (space_struct_rep sh t_info2 from)
    by (unfold space_struct_rep, space_tri; entailer!).
  unlocalize [thread_info_rep sh t_info2 ti].
  {
    now apply thread_info_rep_ramif_stable_1.
  }
  thaw FR.
  unfold thread_info_rep.
  Intros.
  freeze [0;2;3;4;6] FR.
  rewrite heap_struct_rep_eq.
  assert_PROP
    (space_address t_info2 from = field_address (tarray space_type 12) [ArraySubsc (Z.of_nat from)] (ti_heap_p t_info2))
    as Espace_address.
  {
    entailer!.
    unfold space_address, field_address.
    rewrite if_true.
    - f_equal.
    - unfold field_compatible in *.
      simpl in *.
      intuition lia.
  }
  rewrite Espace_address. clear Espace_address.
  Opaque Znth.
  forward. { Transparent Znth. entailer!. }
  forward. { Transparent Znth. entailer!. }
  repeat rewrite upd_Znth_twice by (rewrite heap_spaces__size ; rep_lia).
  repeat rewrite Znth_map by (rewrite heap_spaces__size ; rep_lia).
  repeat rewrite <- nth_space_Znth.
  repeat rewrite upd_Znth_same by (
    rewrite Zlength_map;
    rewrite heap_spaces__size;
    rep_lia
  ).
  rewrite upd_Znth_twice by (rewrite Zlength_map, heap_spaces__size ; rep_lia).
  unfold space_tri at 2 3 4 5 6 7.
  thaw FR.
  assert (heapgraph_has_gen g2 from) by (now destruct H35 as [_ [? _]]).
  rewrite (graph_rep_reset g2 from) by assumption.
  Intros.
  sep_apply (heap_rest_rep_reset g2 t_info2 from (proj1 H34) H40).
  rewrite <- heap_struct_rep_eq.
  gather_SEP (data_at _ _ _ _) (heap_struct_rep _ _ _) (heap_rest_rep _).
  replace_SEP 0 (thread_info_rep sh (reset_nth_heap_thread_info from t_info2) ti).
  {
    unfold thread_info_rep.
    simpl ti_heap_p.
    simpl ti_args.
    entailer!.
    assert (from < length (heap_spaces (ti_heap t_info2)))%nat by
        (destruct H34 as [[_ [_ ?]] _]; red in H40; lia).
    simpl.
    rewrite (reset_nth_space_Znth _ _ H54), <- nth_space_Znth, <- upd_Znth_map.
    unfold space_tri at 3.
    simpl.
    replace
      (space_capacity (nth_space t_info2 from) - 0)
      with (space_capacity (nth_space t_info2 from))
      by lia.
    rewrite isptr_offset_val_zero by assumption.
    cancel.
  }
  apply super_compatible_reset with (gen := from) in H34.
  2: {
    apply (frr_not_pointing from to f_info roots g roots1 g1); auto.
    - now destruct H0 as [_ [_ [_ [? _]]]].
    - now destruct H as [_ [_ [[_ ?] _]]].
  }
  remember (reset_nth_heap_thread_info from t_info2) as t_info3.
  remember (reset_graph from g2) as g3.
  assert
    (do_generation_relation from to f_info roots roots1 g g3)
    as H41
    by (exists g1, g2; split; [|split]; assumption).
  assert (thread_info_relation t_info t_info3) as H42.
  {
    apply tir_trans with t_info2.
    - apply tir_trans with t_info1; assumption.
    - subst t_info3.
      apply tir_reset.
  }
  Exists g3 t_info3 roots1.
  destruct H34 as [H34 [H43 [H44 H45]]].
  now entailer!.
Qed.
