From VST Require Import floyd.proofauto.

From CertiGC Require Import CertiGC.model.GCGraph.
From CertiGC Require Import CertiGC.model.spatial_gcgraph.
From CertiGC Require Import CertiGC.vst.ast.env_graph_gc.
From CertiGC Require Import CertiGC.vst.clightgen.gc.
From CertiGC Require Import CertiGC.vst.spec.gc_spec.

Local Open Scope logic.

Lemma typed_true_tag: forall (to : nat) (g : HeapGraph) (index : nat),
    typed_true tint
               (force_val
                  (option_map (fun b : bool => Val.of_bool (negb b))
                              (bool_val_i
                                 (Val.of_bool
                                    (negb (Int.lt (Int.repr (block_tag
                                                               (heapgraph_block g {| addr_gen := to ; addr_block := index |})))
                                                  (Int.repr 251))))))) ->
    ~ heapgraph_block_is_no_scan g {| addr_gen := to ; addr_block := index |}.
Proof.
  intros. remember (Int.lt (Int.repr (block_tag (heapgraph_block g {| addr_gen := to ; addr_block := index |}))) (Int.repr 251)).
  unfold typed_true in H. destruct b; simpl in H; [|inversion H].
  symmetry in Heqb. apply lt_repr in Heqb.
  - unfold heapgraph_block_is_no_scan. rep_lia.
  - red. pose proof (block_tag__range (heapgraph_block g {| addr_gen := to ; addr_block := index |})). rep_lia.
  - red. rep_lia.
Qed.

Lemma typed_false_tag: forall (to : nat) (g : HeapGraph) (index : nat),
    typed_false tint
               (force_val
                  (option_map (fun b : bool => Val.of_bool (negb b))
                              (bool_val_i
                                 (Val.of_bool
                                    (negb (Int.lt (Int.repr (block_tag
                                                               (heapgraph_block g {| addr_gen := to ; addr_block := index |})))
                                                  (Int.repr 251))))))) ->
    heapgraph_block_is_no_scan g {| addr_gen := to ; addr_block := index |}.
Proof.
  intros. remember (Int.lt (Int.repr (block_tag (heapgraph_block g {| addr_gen := to ; addr_block := index |}))) (Int.repr 251)).
  unfold typed_false in H. destruct b; simpl in H; [inversion H|].
  symmetry in Heqb. apply lt_repr_false in Heqb.
  - unfold heapgraph_block_is_no_scan. rep_lia.
  - red. pose proof (block_tag__range (heapgraph_block g {| addr_gen := to ; addr_block := index |})). rep_lia.
  - red. rep_lia.
Qed.

Lemma body_do_scan: semax_body Vprog Gprog f_do_scan do_scan_spec.
Proof.
  start_function.
  forward.
  forward_loop (EX n: nat, EX g': HeapGraph, EX t_info': thread_info,
                PROP (super_compatible (g', t_info', roots) f_info outlier;
                      forward_condition g' t_info' from to;
                      thread_info_relation t_info t_info';
                      closure_has_index g' to (to_index + n);
                      scan_vertex_while_loop from to (nat_seq to_index n) g g')
                LOCAL
                (temp _s (offset_val (- WORD_SIZE)
                                     (heapgraph_block_ptr g' {| addr_gen := to ; addr_block := (to_index + n)%nat |}));
                 temp _from_start (heapgraph_generation_base g' from);
                 temp _from_limit (limit_address g' t_info' from);
                 temp _next (next_address t_info' to))
                SEP (all_string_constants rsh gv; fun_info_rep rsh f_info fi;
               outlier_rep outlier; graph_rep g'; thread_info_rep sh t_info' ti))
  break: (EX g' : HeapGraph, EX t_info' : thread_info,
          PROP (super_compatible (g', t_info', roots) f_info outlier;
                forward_condition g' t_info' from to;
                do_scan_relation from to to_index g g';
                thread_info_relation t_info t_info')
          LOCAL ()
          SEP (all_string_constants rsh gv; fun_info_rep rsh f_info fi;
               outlier_rep outlier; graph_rep g'; thread_info_rep sh t_info' ti)).
  - Exists O g t_info. destruct H as [? [? [? ?]]].
    replace (to_index + 0)%nat with to_index by lia. entailer!.
    split; [|split]; [red; auto | apply tir_id | constructor].
  - Intros n g' t_info'. remember (to_index + n)%nat as index.
    unfold next_address, thread_info_rep. Intros.
    unfold heap_struct_rep. destruct H5 as [? [? [? ?]]].
    destruct H6 as [? [? [? [? ?]]]].
    assert (0 <= Z.of_nat to < 12). {
      clear -H5 H14. destruct H5 as [_ [_ ?]]. red in H14.
      pose proof (heap_spaces__size (ti_heap t_info')).
      rewrite Zlength_correct in H0. rep_lia. }
    destruct (gt_gs_compatible _ _ H5 _ H14) as [? [? ?]]. rewrite nth_space_Znth in *.
    remember (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info'))) as sp_to.
    assert (isptr (space_base sp_to)) by (rewrite <- H18; apply generation_base__isptr).
    remember (map space_tri (heap_spaces (ti_heap t_info'))).
    assert (@Znth (val * (val * val)) (Vundef, (Vundef, Vundef))
                  (Z.of_nat to) l = space_tri sp_to). {
      subst l sp_to. now rewrite Znth_map by (rewrite heap_spaces__size; rep_lia). }
    forward; rewrite H22; unfold space_tri. 1: entailer!.
    unfold heapgraph_block_ptr, heapgraph_block_offset. rewrite offset_offset_val.
    simpl addr_gen; simpl addr_block.
    replace (WORD_SIZE * (heapgraph_block_size_prev g' to index + 1) + - WORD_SIZE) with
        (WORD_SIZE * (heapgraph_block_size_prev g' to index))%Z by rep_lia.
    unfold heapgraph_generation_base at 1. rewrite if_true by assumption. rewrite H18.
    remember (WORD_SIZE * space_allocated sp_to)%Z as used_offset.
    remember (WORD_SIZE * heapgraph_block_size_prev g' to index)%Z as index_offset.
    freeze [0; 1; 2; 4; 5] FR.
    gather_SEP (graph_rep g') (heap_rest_rep (ti_heap t_info')).
    assert (
        forall b i,
          Vptr b i = space_base sp_to ->
          graph_rep g' * heap_rest_rep (ti_heap t_info') |--
      !! (WORD_SIZE * space_capacity sp_to + Ptrofs.unsigned i <= Ptrofs.max_unsigned)). {
      intros. sep_apply (graph_and_heap_rest_data_at_ _ _ _ H14 H5).
      assert (space_base sp_to = heapgraph_generation_base g' to) by
          (unfold heapgraph_generation_base; rewrite if_true by assumption;
           rewrite <- H18; reflexivity). rewrite H24 in H23.
      sep_apply (generation_data_at__ptrofs g' t_info' to b i H23).
      unfold gen_size; rewrite nth_space_Znth; entailer!. }
    assert_PROP (force_val
                   (sem_cmp_pp Clt (offset_val index_offset (space_base sp_to))
                               (offset_val used_offset (space_base sp_to))) =
                 Vint (if if zlt index_offset used_offset then true else false
                       then Int.one else Int.zero)). {
      remember (space_base sp_to). destruct v; try contradiction. inv_int i.
      specialize (H23 b (Ptrofs.repr ofs) eq_refl).
      rewrite Ptrofs.unsigned_repr in H23 by rep_lia. sep_apply H23. Intros.
      assert (0 <= ofs + used_offset <= Ptrofs.max_unsigned). {
        subst.
        pose proof (space__order (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info')))).
        unfold WORD_SIZE in *. rep_lia. }
      assert (0 <= ofs + index_offset <= Ptrofs.max_unsigned). {
        subst. red in H8. pose proof (heapgraph_block_size_prev__nonneg g' to (to_index + n)%nat).
        pose proof (heapgraph_block_size_prev__mono g' to _ _ H8). unfold WORD_SIZE in *. rep_lia. }
      apply prop_right.
      rewrite force_sem_cmp_pp; [|rewrite isptr_offset_val; assumption..].
      simpl. rewrite !ptrofs_add_repr, if_true. 2: reflexivity.
      unfold Ptrofs.ltu. rewrite !Ptrofs.unsigned_repr; auto. f_equal.
      if_tac; if_tac; try reflexivity; lia. }
    forward_if (heapgraph_generation_has_index g' to index).
    + remember (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info'))) as sp_to.
      sep_apply (graph_and_heap_rest_data_at_ _ _ _ H14 H5).
      unfold generation_data_at_.
      assert (heapgraph_generation_base g' to = space_base sp_to) by
          (subst; unfold heapgraph_generation_base; rewrite if_true; assumption). rewrite H31.
      rewrite data_at__memory_block. Intros. rewrite sizeof_tarray_int_or_ptr.
      2: unfold gen_size; apply space_capacity__range.
      remember (WORD_SIZE * space_allocated sp_to)%Z as used_offset.
      remember (to_index + n)%nat as index.
      remember (WORD_SIZE * heapgraph_block_size_prev g' to index)%Z as index_offset.
      destruct (space_base sp_to); try contradiction. simpl. unfold test_order_ptrs.
      simpl. case (peq b b); intros. 2: contradiction. simpl.
      assert (sepalg.nonidentity (heapgraph_generation_sh g' to)). {
        apply readable_nonidentity, writable_readable_share. unfold heapgraph_generation_sh.
        apply generation_sh__writable. }
      assert (forall offset,
                 0 <= offset <= used_offset ->
                 memory_block (heapgraph_generation_sh g' to) (WORD_SIZE * gen_size t_info' to)
                              (Vptr b i) * TT * FRZL FR |--
        weak_valid_pointer (Vptr b (Ptrofs.add i (Ptrofs.repr offset)))). {
        intros. change (Vptr b (Ptrofs.add i (Ptrofs.repr offset))) with
            (offset_val offset (Vptr b i)).
        sep_apply (memory_block_weak_valid_pointer
                     (heapgraph_generation_sh g' to) (WORD_SIZE * gen_size t_info' to)
                     (Vptr b i) offset); auto.
        3: apply extend_weak_valid_pointer.
        - subst. unfold gen_size. split. 1: apply (proj1 H34).
          transitivity (WORD_SIZE * space_allocated (nth_space t_info' to))%Z.
          + rewrite nth_space_Znth. apply (proj2 H34).
          + apply Zmult_le_compat_l. apply (proj2 (space__order _)).
            unfold WORD_SIZE. lia.
        - clear -H3 H7. destruct H7 as [? [? ?]].
          rewrite <- H0. unfold WORD_SIZE. lia. }
      apply andp_right; apply H34.
      * subst. split.
        1: pose proof (heapgraph_block_size_prev__nonneg g' to (to_index + n)%nat); unfold WORD_SIZE; lia.
        apply Zmult_le_compat_l. 2: unfold WORD_SIZE; lia. rewrite <- H20.
        apply heapgraph_block_size_prev__mono. assumption.
      * split; [|lia]; subst; apply Z.mul_nonneg_nonneg;
                                  [unfold WORD_SIZE; lia | apply space__order].
    + assert (index_offset < used_offset). {
        destruct (zlt index_offset used_offset); trivial.
        rewrite H24 in H25; unfold typed_true in H25. easy. }
      forward. entailer!. red. rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by (unfold WORD_SIZE; lia).
      apply heapgraph_block_size_prev__lt_rev in H26. assumption.
    + assert (~ index_offset < used_offset). {
        destruct (zlt index_offset used_offset); trivial.
        now rewrite H24 in H25; unfold typed_false in H25. }
      forward. thaw FR. unfold thread_info_rep, heap_struct_rep.
      Exists g' t_info'. unfold forward_condition. entailer!.
      split; [red; auto | exists n; split; trivial].
      unfold heapgraph_generation_has_index. rewrite <- H20 in H26.
      rewrite <- Z.mul_lt_mono_pos_l in H26 by (unfold WORD_SIZE; lia).
      intro; apply H26. now apply heapgraph_block_size_prev__mono_strict.
    + clear H8 H23 H24. Intros. thaw FR. freeze [1;2;3;4;5;6] FR.
      assert (heapgraph_has_block g' {| addr_gen := to ; addr_block := index |}) by easy.
      (* annotation theta 7 *)
      localize [vertex_rep (heapgraph_generation_sh g' to) g' {| addr_gen := to ; addr_block := index |}].
      assert (readable_share (heapgraph_generation_sh g' to)) by
          (unfold heapgraph_generation_sh; apply writable_readable_share, generation_sh__writable).
      unfold vertex_rep, vertex_at. Intros.
      assert (offset_val (- WORD_SIZE) (heapgraph_block_ptr g' {| addr_gen := to ; addr_block := index |}) =
              offset_val index_offset (space_base sp_to)). {
        unfold heapgraph_block_ptr. rewrite offset_offset_val. unfold heapgraph_block_offset.
        simpl addr_gen. simpl addr_block.
        replace (WORD_SIZE * (heapgraph_block_size_prev g' to index + 1) + - WORD_SIZE)
          with index_offset by rep_lia.
        f_equal. unfold heapgraph_generation_base.
        rewrite if_true by assumption; now rewrite H18. }
      rewrite H25. forward. rewrite <- H25.
      gather_SEP (data_at _ _ _ _) (data_at _ _ _ _).
      replace_SEP 0 (vertex_rep (heapgraph_generation_sh g' to) g' {| addr_gen := to ; addr_block := index |}) by
          (unfold vertex_rep, vertex_at; entailer!).
      unlocalize [graph_rep g']. 1: apply graph_vertex_ramif_stable; assumption.
      forward. forward. assert (heapgraph_generation_is_unmarked g' to). {
        eapply (svwl_heapgraph_generation_is_unmarked from to _ g); eauto.
        destruct H0 as [_ [_ [? _]]]. assumption. }
      specialize (H26 H14 _ H8).
      rewrite heapgraph_block_header__Wosize, block_mark__false by assumption.
      fold (next_address t_info' to). thaw FR.
      fold (heap_struct_rep sh l (ti_heap_p t_info')).
      gather_SEP
        (data_at _ thread_info_type _ _)
        (heap_struct_rep _ _ _ ) (heap_rest_rep _).
      replace_SEP 0 (thread_info_rep sh t_info' ti) by
          (unfold thread_info_rep; entailer!).
      forward_if
        (EX g'': HeapGraph, EX t_info'': thread_info,
         PROP (super_compatible (g'', t_info'', roots) f_info outlier;
               forward_condition g'' t_info'' from to;
               thread_info_relation t_info t_info'';
               (heapgraph_block_is_no_scan g' {| addr_gen := to ; addr_block := index |} /\ g'' = g') \/
               (~ heapgraph_block_is_no_scan g' {| addr_gen := to ; addr_block := index |} /\
                scan_vertex_for_loop
                  from to {| addr_gen := to ; addr_block := index |}
                  (nat_inc_list (length (heapgraph_block g' {| addr_gen := to ; addr_block := index |}).(block_fields))) g' g''))
         LOCAL (temp _tag (vint (block_tag (heapgraph_block g' {| addr_gen := to ; addr_block := index |})));
                temp _sz
                     (if Archi.ptr64 then
                        Vlong (Int64.repr
                                 (Zlength (block_fields (heapgraph_block g' {| addr_gen := to ; addr_block := index |}))))
                      else vint (Zlength (block_fields (heapgraph_block g' {| addr_gen := to ; addr_block := index |}))));
                temp _s (offset_val (- WORD_SIZE) (heapgraph_block_ptr g'' {| addr_gen := to ; addr_block := index |}));
                temp _from_start (heapgraph_generation_base g'' from);
                temp _from_limit (limit_address g'' t_info'' from);
                temp _next (next_address t_info'' to))
         SEP (thread_info_rep sh t_info'' ti; graph_rep g'';
              fun_info_rep rsh f_info fi;
              all_string_constants rsh gv; outlier_rep outlier)).
      * try (rewrite Int64.unsigned_repr in H27;
             [|pose proof (block_tag__range (heapgraph_block g' {| addr_gen := to ; addr_block := index |})); rep_lia]).
        apply typed_true_tag in H27.
        remember (Zlength (block_fields (heapgraph_block g' {| addr_gen := to ; addr_block := index |}))).
        assert (1 <= z < (if Archi.ptr64 then Int64.max_signed else Int.max_signed)).
        {
          subst z. pose proof (block_fields__range (heapgraph_block g' {| addr_gen := to ; addr_block := index |})).
          split; [lia|]. transitivity (two_p (WORD_SIZE * 8 - 10));
                           [lia | vm_compute; reflexivity]. }
        forward_loop
          (EX i: Z, EX g3: HeapGraph, EX t_info3: thread_info,
           PROP (scan_vertex_for_loop
                   from to {| addr_gen := to ; addr_block := index |}
                   (sublist 0 (i - 1)
                            (nat_inc_list
                               (length (heapgraph_block g' {| addr_gen := to ; addr_block := index |}).(block_fields)))) g' g3;
                super_compatible (g3, t_info3, roots) f_info outlier;
                forward_condition g3 t_info3 from to;
                thread_info_relation t_info t_info3;
                1 <= i <= z + 1)
           LOCAL (temp _tag (vint (block_tag (heapgraph_block g' {| addr_gen := to ; addr_block := index |})));
                  temp _j (if Archi.ptr64 then (Vlong (Int64.repr i)) else vint i);
                  temp _sz (if Archi.ptr64 then (Vlong (Int64.repr z)) else vint z);
                  temp _s (offset_val (- WORD_SIZE) (heapgraph_block_ptr g3 {| addr_gen := to ; addr_block := index |}));
                  temp _from_start (heapgraph_generation_base g3 from);
                  temp _from_limit (limit_address g3 t_info3 from);
                  temp _next (next_address t_info3 to))
           SEP (all_string_constants rsh gv;
                outlier_rep outlier;
                fun_info_rep rsh f_info fi;
                graph_rep g3;
                thread_info_rep sh t_info3 ti))
          continue: (EX i: Z, EX g3: HeapGraph, EX t_info3: thread_info,
           PROP (scan_vertex_for_loop
                   from to {| addr_gen := to ; addr_block := index |}
                   (sublist 0 i
                            (nat_inc_list
                               (length (heapgraph_block g' {| addr_gen := to ; addr_block := index |}).(block_fields)))) g' g3;
                super_compatible (g3, t_info3, roots) f_info outlier;
                forward_condition g3 t_info3 from to;
                thread_info_relation t_info t_info3;
                1 <= i + 1 <= z + 1)
           LOCAL (temp _tag (vint (block_tag (heapgraph_block g' {| addr_gen := to ; addr_block := index |})));
                  temp _j (if Archi.ptr64 then (Vlong (Int64.repr i)) else vint i);
                  temp _sz (if Archi.ptr64 then (Vlong (Int64.repr z)) else vint z);
                  temp _s (offset_val (- WORD_SIZE) (heapgraph_block_ptr g3 {| addr_gen := to ; addr_block := index |}));
                  temp _from_start (heapgraph_generation_base g3 from);
                  temp _from_limit (limit_address g3 t_info3 from);
                  temp _next (next_address t_info3 to))
           SEP (all_string_constants rsh gv;
                fun_info_rep rsh f_info fi;
                outlier_rep outlier;
                graph_rep g3;
                thread_info_rep sh t_info3 ti)).
        -- forward. Exists 1 g' t_info'. replace (1 - 1) with 0 by lia.
           autorewrite with sublist. unfold forward_condition. entailer!.
           try (rewrite Int64.unsigned_repr;
                [| pose proof (block_tag__range (heapgraph_block g' {| addr_gen := to ; addr_block := to_index + n |}));
                   rep_lia]).
           split; [apply svfl_nil | unfold super_compatible; auto].
        -- Intros i g3 t_info3. forward_if (i <= z).
           ++ forward. entailer!.
              first [rewrite !Int.unsigned_repr in H34 |
                     apply ltu64_repr_false in H34]; try lia.
              ** clear -H28 H33. simpl in H28. split. 1: lia.
                 transitivity
                   (Zlength (block_fields (heapgraph_block g' {| addr_gen := to ; addr_block := to_index + n |})) + 1);
                   rep_lia.
              ** clear -H28. simpl in H28. rep_lia.
           ++ forward. assert (i = z + 1). {
                try unfold Int64.ltu in H34.
                first [rewrite !Int.unsigned_repr in H34 |
                       rewrite !Int64.unsigned_repr in H34].
                - try (if_tac in H34; [|inversion H34]). lia.
                - simpl in H28. clear -H28 H33. rep_lia.
                - simpl in H28. clear -H28. rep_lia. } subst i. clear H33 H34.
              replace (z + 1 - 1) with z in H29 by lia.
              remember (block_fields (heapgraph_block g' {| addr_gen := to ; addr_block := index |})) as r.
              replace (sublist 0 z (nat_inc_list (Datatypes.length r))) with
                  (nat_inc_list (Datatypes.length r)) in H29.
              ** Exists g3 t_info3. entailer!.
              ** rewrite sublist_all; trivial. rewrite Z.le_lteq. right.
                 subst z. rewrite !Zlength_correct, nat_inc_list_length. reflexivity.
           ++ Intros.
              change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 2%N |}) with int_or_ptr_type.
              change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 3%N |}) with int_or_ptr_type.
              change (tptr tvoid) with int_or_ptr_type.
              assert (isptr (heapgraph_block_ptr g3 {| addr_gen := to ; addr_block := index |})). {
                erewrite <- svfl_heapgraph_block_ptr; eauto. rewrite <- H18 in H21.
                2: apply heapgraph_has_block_in_closure; assumption. clear -H21 H14.
                unfold heapgraph_block_ptr. unfold heapgraph_generation_base. simpl.
                rewrite if_true by assumption. rewrite isptr_offset_val. assumption. }
              assert (heapgraph_has_gen g3 to) by
                  (eapply svfl_graph_has_gen in H29; [rewrite <- H29|]; assumption).
              assert (heapgraph_has_block g3 {| addr_gen := to ; addr_block := index |}) by
                  (eapply svfl_heapgraph_has_block in H29; [apply H29| assumption..]).
              forward_call (rsh, sh, gv, fi, ti, g3, t_info3, f_info, roots,
                            outlier, from, to, 0, (@inr Z _ ({| addr_gen := to ; addr_block := index |}, i - 1))).
              ** simpl snd. apply prop_right. simpl.
                 do 4 f_equal.
                 first [rewrite sem_add_pi_ptr_special' |
                        rewrite sem_add_pl_ptr_special]; try easy;
                   [|rewrite isptr_offset_val; assumption].
                 simpl. rewrite offset_offset_val. f_equal. unfold WORD_SIZE; lia.
              ** repeat (split; try assumption). lia.
                 --- eapply svfl_block_fields in H29;
                       [rewrite <- H29; lia | assumption..].
                 --- rewrite <- H26. symmetry.
                     eapply svfl_block_mark in H29; [apply H29 | assumption..|].
                     simpl. lia.
                 --- simpl; auto.
              ** Intros vret. destruct vret as [[g4 t_info4] roots']. simpl fst in *.
                 simpl snd in *. simpl in H37. subst roots'. Exists i g4 t_info4.
                 destruct H38 as [? [? [? ?]]].
                 assert (heapgraph_generation_base g3 from = heapgraph_generation_base g4 from) by
                     (eapply fr_gen_start; eauto).
                 assert (limit_address g3 t_info3 from =
                         limit_address g4 t_info4 from). {
                   unfold limit_address. rewrite H45.
                   do 2 f_equal. apply (proj2 H42). }
                 assert (next_address t_info3 to = next_address t_info4 to) by
                     (unfold next_address; f_equal; apply (proj1 H42)). entailer!.
                 split; [|split; [|split]]; try easy.
                 --- remember (nat_inc_list
                                 (Datatypes.length
                                    (block_fields (heapgraph_block g' {| addr_gen := to ; addr_block := to_index + n |})))).
                     assert (i <= Zlength l). {
                       subst l. rewrite Zlength_correct, nat_inc_list_length.
                       rewrite Zlength_correct in H34. lia. }
                     rewrite (sublist_split 0 (i - 1) i) by lia.
                     rewrite (sublist_one (i - 1) i) by lia.
                     apply svfl_add_tail with roots g3; trivial.
                     assert (Z.of_nat (Znth (i - 1) l) = i - 1). {
                       rewrite <- nth_Znth by lia. subst l.
                       rewrite nat_inc_list_nth; [rewrite Z2Nat.id; lia|].
                       rewrite <- ZtoNat_Zlength. rewrite Zlength_correct in H52.
                       rewrite nat_inc_list_length in H52. rewrite Nat2Z.inj_lt.
                       rewrite !Z2Nat.id; lia. } rewrite H53. assumption.
                 --- apply tir_trans with t_info3; assumption.
                 --- f_equal. symmetry. eapply fr_heapgraph_block_ptr; eauto.
                     apply heapgraph_has_block_in_closure; assumption.
        -- Intros i g3 t_info3. cbv [Archi.ptr64]. forward.
           ++ entailer!. clear -H28 H33. simpl in H28.
              first [rewrite !Int.signed_repr | rewrite Int64.signed_repr]; rep_lia.
           ++ Exists (i + 1) g3 t_info3. replace (i + 1 - 1) with i by lia. entailer!.
      * try (rewrite Int64.unsigned_repr in H27;
             [|pose proof (block_tag__range (heapgraph_block g' {| addr_gen := to ; addr_block := index |})); rep_lia]).
        apply typed_false_tag in H27. forward. Exists g' t_info'.
        unfold forward_condition. entailer!.
        try (rewrite Int64.unsigned_repr;
             [|pose proof (block_tag__range (heapgraph_block g' {| addr_gen := to ; addr_block := to_index + n |}));
               rep_lia]). easy.
      * Intros g'' t_info''. assert (isptr (heapgraph_block_ptr g'' {| addr_gen := to ; addr_block := index |})). {
          assert (isptr (heapgraph_block_ptr g' {| addr_gen := to ; addr_block := index |})). {
            unfold heapgraph_block_ptr. rewrite isptr_offset_val. unfold heapgraph_generation_base.
            rewrite <- H18 in H21. rewrite if_true; assumption. }
          destruct H30 as [[? ?] | [? ?]]. 1: subst g''; assumption.
          eapply svfl_heapgraph_block_ptr in H32;
            [rewrite <- H32 | | apply heapgraph_has_block_in_closure]; assumption. }
        pose proof (block_fields__range (heapgraph_block g' {| addr_gen := to ; addr_block := index |})). forward.
        -- entailer!. split. 1: rep_lia.
           assert (two_p (WORD_SIZE * 8 - 10) <
                   if Archi.ptr64 then Int64.max_signed else Int.max_signed)
             by (vm_compute; reflexivity). cbv [Archi.ptr64] in H37. clear -H37 H32.
           first [rewrite Int.signed_repr | rewrite Int64.signed_repr]; rep_lia.
        -- change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 2%N |}) with int_or_ptr_type.
           change (Tpointer tvoid {| attr_volatile := false; attr_alignas := Some 3%N |}) with int_or_ptr_type.
           change (tptr tvoid) with int_or_ptr_type.
           cbv [Archi.ptr64]. simpl sem_binary_operation'.
           first [rewrite add_repr | rewrite add64_repr].
           try (rewrite Int.signed_repr; [|rep_lia]).
           assert (force_val
                     (if Archi.ptr64 then
                        (sem_add_ptr_long int_or_ptr_type
                           (offset_val (-8) (heapgraph_block_ptr g'' {| addr_gen := to ; addr_block := index |}))
                           (Vlong
                              (Int64.repr
                                 (1 + Zlength (block_fields (heapgraph_block g' {| addr_gen := to ; addr_block := index |}))))))
                      else
                        (sem_add_ptr_int int_or_ptr_type Unsigned
                           (offset_val (-4)
                                       (heapgraph_block_ptr g'' {| addr_gen := to ; addr_block := index |}))
                           (vint (1 + Zlength
                                        (block_fields (heapgraph_block g' {| addr_gen := to ; addr_block := index |}))))))
                   = offset_val (- WORD_SIZE)
                                (heapgraph_block_ptr g'' {| addr_gen := to ; addr_block := to_index + (n + 1) |})). {
             cbv [Archi.ptr64].
             first [rewrite sem_add_pi_ptr_special' |
                    rewrite sem_add_pl_ptr_special']; try easy.
             - assert (Zlength (block_fields (heapgraph_block g' {| addr_gen := to ; addr_block := index |})) =
                       Zlength (block_fields (heapgraph_block g'' {| addr_gen := to ; addr_block := index |}))). {
                 destruct H30 as [[? ?] | [? ?]]. 1: subst g''; reflexivity.
                 erewrite svfl_block_fields; eauto. } rewrite H33.
               simpl. replace (to_index + (n + 1))%nat with (S index) by lia.
               unfold heapgraph_block_ptr. rewrite !offset_offset_val.
               unfold heapgraph_block_offset. simpl addr_gen. simpl addr_block. f_equal.
               rewrite heapgraph_block_size_prev__S. unfold heapgraph_block_size. unfold WORD_SIZE. lia.
             - rewrite isptr_offset_val. assumption. }
           cbv [Archi.ptr64] in H33. rewrite H33. clear H33.
           assert (closure_has_index g'' to (to_index + (n + 1))). {
             replace (to_index + (n + 1))%nat with (index + 1)%nat by lia.
             cut (heapgraph_generation_has_index g'' to index). 1: red; intros; red in H33; lia.
             destruct H30 as [[? ?] | [? ?]].
             - subst g''. destruct H23. assumption.
             - eapply svfl_heapgraph_has_block in H33; eauto. destruct H33. assumption. }
           Exists (n + 1)%nat g'' t_info''. destruct H27 as [? [? [? ?]]]. entailer!.
           clear H37 H38 H39 H40. replace (n + 1)%nat with (S n) by lia.
           rewrite nat_seq_S, Nat.add_comm. destruct H30 as [[? ?] | [? ?]].
           ++ subst g''. split; [| apply svwl_add_tail_no_scan]; easy.
           ++ split; [|apply svwl_add_tail_scan with g']; easy.
  - Intros g' t_info'. Exists g' t_info'. entailer!.
Qed.
