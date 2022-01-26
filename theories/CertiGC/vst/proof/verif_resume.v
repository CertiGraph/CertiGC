From VST Require Import floyd.proofauto.

From CertiGC Require Import CertiGC.model.GCGraph.
From CertiGC Require Import CertiGC.model.spatial_gcgraph.
From CertiGC Require Import CertiGC.vst.ast.env_graph_gc.
From CertiGC Require Import CertiGC.vst.clightgen.gc.
From CertiGC Require Import CertiGC.vst.spec.gc_spec.

Lemma body_resume: semax_body Vprog Gprog f_resume resume_spec.
Proof.
  start_function.
  unfold thread_info_rep, heap_struct_rep. Intros.
  forward. unfold fun_info_rep. forward. 1: entailer!. rewrite Znth_0_cons.
  replace_SEP 1 (fun_info_rep rsh f_info fi) by (unfold fun_info_rep; entailer!).
  forward_if True.
  - forward; entailer!.
  - remember (ti_heap_p t_info). rewrite (data_at_isptr sh heap_type).
    Intros. exfalso. destruct t_info. simpl in *. subst. contradiction.
  - Intros. destruct (heap_head__cons (ti_heap t_info)) as [hs [hl [? ?]]].
    rewrite H1, <- H2, map_cons.
    destruct (gt_gs_compatible _ _ H _ (heapgraph_has_gen__O _)) as [H3 H4 H5 HH6].
    simpl in H3, H4, H5, HH6.
    assert (isptr (space_base (heap_head (ti_heap t_info)))). {
      rewrite H2. unfold nth_space in H3. rewrite H1 in H3. simpl in H3.
      rewrite <- H3. apply generation_base__isptr. } unfold space_tri at 1. do 2 forward.
    rewrite Znth_0_cons.
    destruct (space_base (heap_head (ti_heap t_info))) eqn:? ; try contradiction.
    forward_if (fun_word_size f_info <= space_capacity hs).
    + unfold denote_tc_samebase. simpl. entailer!.
    + unfold all_string_constants. Intros.
      forward_call ((gv ___stringlit_10),
                    (map init_data2byte (gvar_init v___stringlit_10)), rsh).
      exfalso; assumption.
    + forward. entailer!.
      unfold sem_sub_pp in H7. destruct eq_block in H7; [|easy]; simpl in H7.
      inv_int i. clear -H7. remember (heap_head (ti_heap t_info)) as h.
      rewrite ptrofs_add_repr, ptrofs_sub_repr, Z.add_comm, Z.add_simpl_r in H7.
      simpl in H7. unfold Ptrofs.divs in H7.
      first [rewrite (Ptrofs.signed_repr 8) in H7 by rep_lia |
             rewrite (Ptrofs.signed_repr 4) in H7 by rep_lia].
      rewrite Ptrofs.signed_repr in H7 by (apply space_limit__signed_range).
      unfold WORD_SIZE in H7. rewrite Z.mul_comm, Z.quot_mul in H7 by lia.
      first [rewrite ptrofs_to_int64_repr in H7 by easy |
             rewrite ptrofs_to_int_repr in H7]. hnf in H7.
      remember (if Archi.ptr64 then
                  (Int64.ltu (Int64.repr (space_capacity h - space_remembered h))
                             (Int64.repr (fun_word_size f_info))) else
                  (Int.ltu (Int.repr (space_capacity h - space_remembered h))
                           (Int.repr (fun_word_size f_info)))) as comp.
      cbv [Archi.ptr64] in Heqcomp.
      rewrite <- Heqcomp in H7.
      destruct comp eqn:? ; simpl in H7 ; try congruence.
      symmetry in Heqcomp.
      match goal with
      | H : Int64.ltu _ _ = false |- _ => apply ltu64_repr_false in H
      | H : Int.ltu _ _ = false |- _ => apply ltu_repr_false in H
      end.
      { pose proof (space_remembered__lower_bound h). lia. }
      {
        first [apply space_limit__range | apply word_size_range].
      }
      {
        first [apply space_limit__range | apply word_size_range].
      }
    + rewrite <- Heqv in *.
      red in H0.
      rewrite H0 in H5.
      unfold heapgraph_block_size_prev in H5. simpl in H5. unfold nth_space in H5.
      rewrite H1 in H5. simpl in H5. rewrite <- H2 in H5.
      replace_SEP 4
        (heap_struct_rep sh
          (
            ( space_base (heap_head (ti_heap t_info)),
            ( offset_val (WORD_SIZE * space_allocated (heap_head (ti_heap t_info))) (space_base (heap_head (ti_heap t_info))),
            ( offset_val (WORD_SIZE * (space_capacity (heap_head (ti_heap t_info)) - space_remembered (heap_head (ti_heap t_info)))) (space_base (heap_head (ti_heap t_info)))
            , offset_val (WORD_SIZE * space_capacity (heap_head (ti_heap t_info))) (space_base (heap_head (ti_heap t_info)))
            )))
            ::
              map space_tri hl
            )
            (ti_heap_p t_info)) by
          (unfold heap_struct_rep; entailer!).
      do 2 forward.
      unfold before_gc_thread_info_rep. rewrite !heap_struct_rep_eq. rewrite <- H5.
      replace (WORD_SIZE * 0)%Z with 0 by lia.
      rewrite !isptr_offset_val_zero by assumption. entailer!. rewrite H1. simpl tl.
      assert (12 = Zlength (map space_tri hl) + 1). {
        pose proof (heap_spaces__size (ti_heap t_info)). rewrite MAX_SPACES_eq in H2.
        rewrite <- H2, H1, Zlength_cons, Zlength_map. lia. } rewrite !H2.
      rewrite !data_at_tarray_split_1 by reflexivity. cancel.
      do 2 (unfold_data_at (data_at _ _ _ _)). cancel.
Qed.
