Require Import Coq.Lists.List.

From VST Require Import veric.compcert_rmaps.
From VST Require Import msl.shares.
From VST Require Import msl.wand_frame.
From VST Require Import floyd.proofauto.
From VST Require Import floyd.library.

From CertiGraph Require Import lib.List_ext.
From CertiGraph Require Import msl_ext.log_normalize.
From CertiGraph Require Import msl_ext.ramification_lemmas.
From CertiGraph Require Import msl_ext.iter_sepcon.
From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.

From CertiGC Require Export model.compatible.compatible.
From CertiGC Require Export model.constants.
From CertiGC Require Export model.heap.heap.
From CertiGC Require Export model.heapgraph.block.block.
From CertiGC Require Export model.heapgraph.block.cell.
From CertiGC Require Export model.heapgraph.block.field.
From CertiGC Require Export model.heapgraph.block.header.
From CertiGC Require Export model.heapgraph.block.ptr.
From CertiGC Require Export model.heapgraph.generation.generation.
From CertiGC Require Export model.heapgraph.graph.
From CertiGC Require Export model.heapgraph.has_block.
From CertiGC Require Export model.heapgraph.mark.
From CertiGC Require Export model.heapgraph.predicates.
From CertiGC Require Export model.heapgraph.roots.
From CertiGC Require Export model.op.copy.
From CertiGC Require Export model.op.cut.
From CertiGC Require Export model.op.reset.
From CertiGC Require Export model.thread_info.thread_info.
From CertiGC Require Export model.util.

From CertiGC Require Import vst.ast.env_graph_gc.
From CertiGC Require Import vst.clightgen.gc.
From CertiGC Require Import vst.cmodel.constants.


Local Open Scope logic.

(** * WARNING
    The following section contains lemmas copied from
    concurrency/conclib.v and other files. I put them here to avoid
    the compatible problem with VST-2.8 *)

(*+ TEMP LEMMAS BEGIN *)

Import FashNotation.

Lemma data_at__eq : forall {cs : compspecs} sh t p,
    data_at_ sh t p = data_at sh t (default_val t) p.
Proof. intros; unfold data_at_, data_at, field_at_; auto. Qed.

Lemma approx_eq_i':
  forall (P Q : pred rmap) n,
    (|> (P <=> Q))%pred n -> approx n P = approx n Q.
Proof.
  intros.
  apply pred_ext'; extensionality m'.
  unfold approx.
  apply and_ext'; auto; intros.
  specialize (H (level m')); spec H; [simpl; apply later_nat; auto |].
  specialize (H m').
  spec H; [lia |].
  destruct H.
  specialize (H m').
  specialize (H1 m').
  apply prop_ext; split; auto.
Qed.

Lemma nonexpansive_entail (F: pred rmap -> pred rmap) :
  nonexpansive F -> forall P Q, (P <=> Q |-- F P <=> F Q)%logic.
Proof.
  intros N P Q.
  specialize (N P Q).
  eapply derives_trans; [ eapply derives_trans | ]; [ | constructor; apply N | ];
    apply derives_refl.
Qed.

Lemma fash_equiv_approx: forall n (R: pred rmap), (|> (R <=> approx n R))%pred n.
Proof.
  intros.
  intros m ? x ?; split; intros y ? ?.
  + apply approx_lt; auto.
    apply necR_level in H1.
    apply later_nat in H; lia.
  + eapply approx_p; eauto.
Qed.

Lemma nonexpansive2_super_non_expansive: forall (F: mpred -> mpred -> mpred),
    (forall P, nonexpansive (fun Q => F P Q)) ->
    (forall Q, nonexpansive (fun P => F P Q)) ->
    forall P Q n,
      approx n (F P Q) = approx n (F (approx n P) (approx n Q)).
Proof.
  intros.
  apply approx_eq_i'.
  intros m ?.
  pose proof nonexpansive_entail _ (H P) Q (approx n Q) as H2.
  inv H2; rename derivesI into H2. specialize (H2 m); cbv beta in H2.
  spec H2; [apply (fash_equiv_approx n Q m); auto |].
  pose proof nonexpansive_entail _ (H0 (approx n Q)) P (approx n P) as H3.
  inv H3; rename derivesI into H3. specialize (H3 m); cbv beta in H3.
  spec H3; [apply (fash_equiv_approx n P m); auto |].
  remember (F P Q) as X1.
  remember (F P (approx n Q)) as X2.
  remember (F (approx n P) (approx n Q)) as X3.
  clear - H2 H3.
  change ((X1 <=> X2)%pred m) in H2.
  change ((X2 <=> X3)%pred m) in H3.
  intros y H; specialize (H2 y H); specialize (H3 y H).
  destruct H2 as [H2A H2B], H3 as [H3A H3B].
  split; intros z H0.
  + specialize (H2A z H0); specialize (H3A z H0); auto.
  + specialize (H2B z H0); specialize (H3B z H0); auto.
Qed.

Lemma nonexpansive_super_non_expansive: forall (F: mpred -> mpred),
    nonexpansive F -> forall R n, approx n (F R) = approx n (F (approx n R)).
Proof.
  intros.
  apply approx_eq_i'.
  intros m ?.
  apply nonexpansive_entail; auto.
  clear - H0.
  apply (fash_equiv_approx n R m); auto.
Qed.

Lemma firstn_all : forall {A} n (l : list A), (length l <= n)%nat -> firstn n l = l.
Proof.
  induction n; destruct l; auto; simpl; intros; try lia.
  rewrite IHn; auto; lia.
Qed.

Lemma sublist_all : forall {A} i (l : list A), Zlength l <= i -> sublist 0 i l = l.
Proof.
  intros; unfold_sublist_old; simpl.
  apply firstn_all.
  rewrite Zlength_correct in *; rep_lia.
Qed.

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
  (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
              (fun (ts: list Type) (x: t1*t2*t3*t4*t5) =>
                 match x with (x1,x2,x3,x4,x5) => P%argsassert end)
              (fun (ts: list Type) (x: t1*t2*t3*t4*t5) =>
                 match x with (x1,x2,x3,x4,x5) => Q%assert end) _ _)
    (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
      x5 at level 0,
      P at level 100, Q at level 100).

Lemma approx_idem : forall n P, compcert_rmaps.R.approx n (compcert_rmaps.R.approx n P) =
                                  compcert_rmaps.R.approx n P.
Proof.
  intros.
  transitivity (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) P); auto.
  rewrite compcert_rmaps.RML.approx_oo_approx; auto.
Qed.

Notation vint z := (Vint (Int.repr z)).
Notation vptrofs z := (Vptrofs (Ptrofs.repr z)).

(*+ TEMP LEMMAS END *)

Definition vertex_at (sh: share) (p: val) (header: Z) (lst_fields: list val) :=
  Eval cbv delta [Archi.ptr64] match
         in
         (data_at sh (if Archi.ptr64 then tulong else tuint)
                  (Z2val header) (offset_val (- WORD_SIZE) p) *
          data_at sh (tarray int_or_ptr_type (Zlength lst_fields)) lst_fields p).


Definition vertex_rep (sh: share) (g: HeapGraph) (v: Addr): mpred :=
  vertex_at sh (heapgraph_block_ptr g v) (heapgraph_block_header g v) (heapgraph_block_cells_vals g v).

Definition generation_rep (g: HeapGraph) (gen: nat): mpred :=
  iter_sepcon (map (fun x => {| addr_gen := gen ; addr_block := x |})
                   (nat_inc_list (heapgraph_generation g gen).(generation_block_count)))
              (vertex_rep (heapgraph_generation_sh g gen) g).

Definition graph_rep (g: HeapGraph): mpred :=
  iter_sepcon (nat_inc_list (length (heapgraph_generations g).(generations))) (generation_rep g).

Definition fun_info_rep (sh: share) (fi: fun_info) (p: val) : mpred :=
  Eval cbv delta [Archi.ptr64] match
         in
         let len := Zlength (live_roots_indices fi) in
         data_at
           sh (tarray (if Archi.ptr64 then tulong else tuint) (len + 2))
           (map Z2val (fun_word_size fi :: len :: live_roots_indices fi)) p.

Definition space_rest_rep (sp: Space): mpred :=
  if (Val.eq sp.(space_base) nullval)
  then emp
  else data_at_ (space_sh sp)
                (tarray int_or_ptr_type (sp.(space_capacity) - sp.(space_allocated)))
                (offset_val (WORD_SIZE * space_allocated sp) sp.(space_base)).

Definition heap_rest_rep (hp: Heap): mpred :=
  iter_sepcon hp.(heap_spaces) space_rest_rep.

Definition space_tri (sp: Space): (reptype space_type) :=
  let s := sp.(space_base) in
  ( s,
  ( offset_val (WORD_SIZE * sp.(space_allocated)) s,
  ( offset_val (WORD_SIZE * (sp.(space_capacity) - sp.(space_remembered))) s
  , offset_val (WORD_SIZE * sp.(space_capacity)) s
  ))).

Definition heap_struct_rep (sh: share) (sp_reps: list (reptype space_type)) (h: val):
  mpred := data_at sh heap_type sp_reps h.

Definition before_gc_thread_info_rep (sh: share) (ti: thread_info) (t: val) :=
  let nursery := heap_head ti.(ti_heap) in
  let p := nursery.(space_base) in
  let n_lim := offset_val (WORD_SIZE * (nursery.(space_capacity) - nursery.(space_remembered))) p in
  let n_end := offset_val (WORD_SIZE * nursery.(space_capacity)) p in
  data_at sh thread_info_type
          (offset_val (WORD_SIZE * nursery.(space_allocated)) p,
           (n_lim, (ti.(ti_heap_p), ti.(ti_args)))) t *
  heap_struct_rep
    sh ((p, (Vundef, (n_lim, n_end)))
          :: map space_tri (tl ti.(ti_heap).(heap_spaces))) ti.(ti_heap_p) *
  heap_rest_rep ti.(ti_heap).

Definition thread_info_rep (sh: share) (ti: thread_info) (t: val) :=
  data_at sh thread_info_type (Vundef, (Vundef, (ti.(ti_heap_p), ti.(ti_args)))) t *
  heap_struct_rep sh (map space_tri ti.(ti_heap).(heap_spaces)) ti.(ti_heap_p) *
  heap_rest_rep ti.(ti_heap).

Definition single_outlier_rep (p: GC_Pointer) :=
  EX sh: share, !!(readable_share sh) &&
                  (data_at_ sh int_or_ptr_type (GC_Pointer2val p) * TT).

Definition outlier_rep (outlier: outlier_t) :=
  fold_right andp TT (map single_outlier_rep outlier).

Lemma vertex_head_address_eq: forall g gen num,
    offset_val (- WORD_SIZE) (heapgraph_block_ptr g {| addr_gen := gen ; addr_block := num |}) =
    offset_val (WORD_SIZE * (heapgraph_block_size_prev g gen num)) (heapgraph_generation_base g gen).
Proof.
  intros. unfold heapgraph_block_ptr, heapgraph_block_offset. rewrite offset_offset_val.
  f_equal. rewrite Z.add_opp_r, Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_simpl_r.
Qed.

Lemma vertex_rep_isptr: forall sh g v,
    vertex_rep sh g v |-- !! (isptr (heapgraph_generation_base g (addr_gen v))).
Proof.
  intros. destruct v as [gen num]. unfold vertex_rep, vertex_at.
  rewrite vertex_head_address_eq. simpl. rewrite data_at_isptr. Intros.
  apply prop_right. unfold offset_val in H.
  destruct (heapgraph_generation_base g gen); try contradiction. exact I.
Qed.

Lemma vertex_rep_memory_block: forall sh g v,
    vertex_rep sh g v |--
               memory_block sh (WORD_SIZE * heapgraph_block_size g v)
               (offset_val (- WORD_SIZE) (heapgraph_block_ptr g v)).
Proof.
  intros. sep_apply (vertex_rep_isptr sh g v). Intros.
  destruct v as [gen num]. unfold vertex_rep, vertex_at. simpl in H.
  rewrite vertex_head_address_eq. unfold heapgraph_block_ptr, heapgraph_block_offset. simpl.
  remember (heapgraph_generation_base g gen). destruct v; try contradiction.
  remember (heapgraph_block_size_prev g gen num).
  assert (0 <= z) by (rewrite Heqz; apply heapgraph_block_size_prev__nonneg).
  unfold heapgraph_block_size. entailer. rewrite <- fields_eq_length.
  destruct H1 as [_ [_ [? _]]]. simpl in H1.
  destruct H3 as [_ [_ [? _]]]. simpl in H3. rewrite <- H4 in H3.
  remember (heapgraph_block_size_prev g gen num).
  remember (Zlength (heapgraph_block_cells_vals g {| addr_gen := gen; addr_block := num |})). rewrite (Z.add_comm z0).
  rewrite Z.mul_add_distr_l with (m := 1). rewrite Z.mul_1_r.
  simpl offset_val. remember (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * z))).
  rewrite <- (Ptrofs.repr_unsigned i0). remember (Ptrofs.unsigned i0) as ofs.
  assert (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * (z + 1))) =
          Ptrofs.repr (ofs + WORD_SIZE)). {
    unfold WORD_SIZE in *. rewrite Z.mul_add_distr_l, Z.mul_1_r.
    rewrite <- ptrofs_add_repr, <- Ptrofs.add_assoc.
    rewrite Ptrofs.add_unsigned. rewrite <- Heqi0. rewrite <- Heqofs. f_equal.
  } assert (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (WORD_SIZE * (z + 1)))) =
            ofs + WORD_SIZE). {
    rewrite H6, Ptrofs.unsigned_repr_eq. apply Z.mod_small.
    destruct (Ptrofs.unsigned_range i0). rewrite <- Heqofs in *. unfold WORD_SIZE. lia.
  } rewrite H6. assert (0 <= z0) by (subst z0; apply Zlength_nonneg).
  assert ((@Zlength (@reptype CompSpecs int_or_ptr_type)
                    (heapgraph_block_cells_vals g {| addr_gen := gen; addr_block := num |})) =
          (@Zlength val (heapgraph_block_cells_vals g {| addr_gen := gen; addr_block := num |}))) by reflexivity.
  rewrite H9 in H3. clear H9. rewrite <- Heqz0 in *.
  rewrite memory_block_split; [|unfold WORD_SIZE in *; rep_lia..].
  sep_apply (data_at_memory_block
               sh (if Archi.ptr64 then tulong else tuint)
               (Z2val (heapgraph_block_header g {| addr_gen := gen; addr_block := num |})) (Vptr b (Ptrofs.repr ofs))).
  simpl sizeof. unfold WORD_SIZE. apply cancel_left. fold WORD_SIZE.
  sep_apply (data_at_memory_block
               sh (tarray int_or_ptr_type z0) (heapgraph_block_cells_vals g {| addr_gen := gen; addr_block := num |})
               (Vptr b (Ptrofs.repr (ofs + WORD_SIZE)))).
  unfold WORD_SIZE. simpl sizeof. rewrite Z.max_r; auto.
Qed.

Lemma iter_sepcon_vertex_rep_ptrofs: forall g gen b i sh num,
    Vptr b i = heapgraph_generation_base g gen ->
    iter_sepcon (map (fun x : nat => {| addr_gen := gen; addr_block := x |}) (nat_inc_list num)) (vertex_rep sh g)
                |-- !! (WORD_SIZE * heapgraph_block_size_prev g gen num +
                        Ptrofs.unsigned i < Ptrofs.modulus).
Proof.
  intros. induction num. 1: entailer.
  rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
  assert_PROP (WORD_SIZE * heapgraph_block_size_prev g gen num +
               Ptrofs.unsigned i < Ptrofs.modulus) by
      (unfold generation_rep in IHnum; sep_apply IHnum; entailer!). clear IHnum.
  simpl iter_sepcon. entailer. unfold vertex_rep at 2. unfold vertex_at.
  rewrite vertex_head_address_eq. unfold heapgraph_block_ptr, heapgraph_block_offset. simpl.
  rewrite <- H. inv_int i. entailer. destruct H1 as [_ [_ [? _]]]. simpl in H1.
  destruct H4 as [_ [_ [? _]]]. simpl in H4. rewrite <- H5 in H4. clear H3 H6 H5.
  rewrite ptrofs_add_repr in *. apply prop_right.
  pose proof (heapgraph_block_size_prev__nonneg g gen num). rewrite Ptrofs.unsigned_repr_eq in H1.
  unfold WORD_SIZE in *. rewrite Z.mod_small in H1 by rep_lia. rewrite heapgraph_block_size_prev__S.
   unfold heapgraph_block_size. rewrite <- fields_eq_length.
  rewrite Z.mul_add_distr_l, Z.mul_1_r, Z.add_assoc in H4.
  rewrite Ptrofs.unsigned_repr_eq in H4. rewrite Z.mod_small in H4 by rep_lia.
   assert ((@Zlength (@reptype CompSpecs int_or_ptr_type)
                     (heapgraph_block_cells_vals g {| addr_gen := gen; addr_block := num |})) =
          (@Zlength val (heapgraph_block_cells_vals g {| addr_gen := gen; addr_block := num |}))) by reflexivity.
  rewrite H5 in *. rep_lia.
 Qed.

Lemma generation_rep_ptrofs: forall g gen b i,
    Vptr b i = heapgraph_generation_base g gen ->
    generation_rep g gen |--
                   !! (WORD_SIZE * heapgraph_generation_size g gen +
                       Ptrofs.unsigned i < Ptrofs.modulus).
Proof.
  intros.
  unfold heapgraph_generation_size.
  apply (iter_sepcon_vertex_rep_ptrofs g gen b i).
  assumption.
Qed.

Lemma generation_rep_memory_block: forall g gen,
    heapgraph_has_gen g gen ->
    generation_rep g gen |--
                   memory_block (heapgraph_generation_sh g gen) (WORD_SIZE * heapgraph_generation_size g gen)
                   (heapgraph_generation_base g gen).
Proof.
  intros. apply heapgraph_generation_base__isptr in H.
  remember (heapgraph_generation_base g gen). destruct v; try contradiction.
  unfold generation_rep, heapgraph_generation_size.
  remember (generation_block_count (heapgraph_generation g gen)) as num. clear Heqnum.
  remember (heapgraph_generation_sh g gen) as sh. clear Heqsh. induction num.
  - simpl. rewrite memory_block_zero_Vptr. auto.
  - sep_apply (iter_sepcon_vertex_rep_ptrofs g gen b i sh (S num) Heqv). Intros.
    rename H0 into HS. simpl in HS. unfold generation_rep.
    rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
    simpl. unfold generation_rep in IHnum. sep_apply IHnum. rewrite heapgraph_block_size_prev__S, Z.add_comm.
    rewrite <- (Ptrofs.repr_unsigned i) at 2.
    remember (heapgraph_block_size_prev g gen num) as zp.
    assert (0 <= zp) by (subst zp; apply heapgraph_block_size_prev__nonneg).
    pose proof (heapgraph_block_size__one g {| addr_gen := gen; addr_block := num |}) as HS1.
    pose proof (Ptrofs.unsigned_range i) as HS2.
    rewrite heapgraph_block_size_prev__S in HS.
    rewrite Z.add_comm, Z.mul_add_distr_l, memory_block_split by (unfold WORD_SIZE in *; rep_lia).
    rewrite (Ptrofs.repr_unsigned i).
    apply cancel_left.
    sep_apply (vertex_rep_memory_block sh g {| addr_gen := gen; addr_block := num |}).
    rewrite vertex_head_address_eq, <- Heqzp, <- Heqv.
    simpl offset_val.
    now rewrite <- ptrofs_add_repr, Ptrofs.repr_unsigned.
Qed.

Lemma generation_rep_align_compatible: forall g gen,
    heapgraph_has_gen g gen ->
    generation_rep g gen |--
                   !! (align_compatible (tarray int_or_ptr_type (heapgraph_generation_size g gen))
                                        (heapgraph_generation_base g gen)).
Proof.
  intros. apply heapgraph_generation_base__isptr in H.
  remember (heapgraph_generation_base g gen). destruct v; try contradiction.
  sep_apply (generation_rep_ptrofs g gen b i Heqv). Intros.
  unfold generation_rep, heapgraph_generation_size in *.
  remember (generation_block_count (heapgraph_generation g gen)) as num. clear Heqnum.
  remember (heapgraph_generation_sh g gen) as sh eqn:Heqsh. clear Heqsh.
  induction num.
  - unfold heapgraph_block_size_prev. simpl fold_left. apply prop_right.
    constructor.
    intros.
    lia.
  - unfold generation_rep. rewrite nat_inc_list_S, map_app, iter_sepcon_app_sepcon.
    simpl iter_sepcon. entailer. unfold vertex_rep at 2. unfold vertex_at.
    rename H0 into HS. rewrite vertex_head_address_eq. entailer!. clear H1 H2 H3 H4.
    destruct H0 as [_ [_ [_ [? _]]]]. rewrite <- Heqv in H0. inv_int i.
    hnf in H0. rewrite ptrofs_add_repr in H0. inv H0. simpl in H1. inv H1.
    simpl in H3. simpl in HS. pose proof (heapgraph_block_size__one g {| addr_gen := gen; addr_block := num |}).
    pose proof (heapgraph_block_size_prev__nonneg g gen num). rewrite heapgraph_block_size_prev__S in HS.
    rewrite Ptrofs.unsigned_repr_eq in H3. unfold WORD_SIZE in *.
    rewrite Z.mod_small in H3 by rep_lia.
    rewrite Z.add_comm in H3. apply Z.divide_add_cancel_r in H3.
    2: apply Z.divide_factor_l. constructor. intros.
    rewrite Ptrofs.unsigned_repr_eq. rewrite Z.mod_small by lia. simpl sizeof.
    apply align_compatible_rec_by_value with Mptr. 1: reflexivity. simpl.
    apply Z.divide_add_r; [assumption | apply Z.divide_factor_l].
Qed.

Lemma sizeof_tarray_int_or_ptr: forall n,
    0 <= n -> sizeof (tarray int_or_ptr_type n) = (WORD_SIZE * n)%Z.
Proof. intros. simpl. rewrite Z.max_r by assumption. unfold WORD_SIZE. rep_lia. Qed.

Lemma generation_rep_field_compatible: forall g gen,
    heapgraph_has_gen g gen ->
    generation_rep g gen |--
                   !! (field_compatible (tarray int_or_ptr_type (heapgraph_generation_size g gen))
                                        [] (heapgraph_generation_base g gen)).
Proof.
  intros. pose proof H. apply heapgraph_generation_base__isptr in H.
  remember (heapgraph_generation_base g gen). destruct v; try contradiction.
  unfold field_compatible. entailer. unfold size_compatible.
  rewrite sizeof_tarray_int_or_ptr by apply heapgraph_generation_size__nonneg.
  sep_apply (generation_rep_ptrofs g gen b i Heqv). entailer. rewrite Heqv.
  sep_apply (generation_rep_align_compatible g gen H0). entailer!.
Qed.

Lemma generation_rep_data_at_ g gen (H: heapgraph_has_gen g gen):
  generation_rep g gen
  |-- data_at_
        (heapgraph_generation_sh g gen)
        (tarray int_or_ptr_type (heapgraph_generation_size g gen))
        (heapgraph_generation_base g gen).
Proof.
  intros. sep_apply (generation_rep_field_compatible g gen H). Intros.
  sep_apply (generation_rep_memory_block g gen H).
  rewrite <- sizeof_tarray_int_or_ptr by apply heapgraph_generation_size__nonneg.
  rewrite memory_block_data_at_; auto.
Qed.

Lemma field_compatible_tarray_join:
  forall (n n1 : Z) (p : val) (t: type),
    0 <= n1 <= n -> complete_legal_cosu_type t = true ->
    field_compatible (tarray t n1) [] p ->
    field_compatible (tarray t (n - n1)) []
                     (offset_val (sizeof t * n1) p) ->
    field_compatible (tarray t n) [] p.
Proof.
  intros. unfold field_compatible. simpl. destruct H1 as [? [_ [? [? _]]]].
  destruct H2 as [_ [_ [? [? _]]]]. destruct p; try contradiction. clear H1.
  simpl isptr. inv_int i. unfold size_compatible in *. simpl in H2.
  simpl sizeof in *. rewrite Z.max_r in * by lia. pose proof (Ctypes.sizeof_pos t).
  unfold sizeof in H2. remember (Ctypes.sizeof t) as S. rewrite ptrofs_add_repr in H2.
  rewrite Ptrofs.unsigned_repr in * by rep_lia.
  assert (0 <= ofs + S * n1 <= Ptrofs.max_unsigned). {
    destruct H, H6. split. 2: rep_lia. apply Z.add_nonneg_nonneg. 1: lia.
    apply Z.mul_nonneg_nonneg; lia. }
  rewrite Ptrofs.unsigned_repr in * by assumption.
  assert (forall i, ofs + S * n1 + S * (i - n1) = ofs + S * i). {
    intros. rewrite <- Z.add_assoc. rewrite <- Z.mul_add_distr_l.
    do 2 f_equal. lia. } rewrite H8 in H2. do 4 (split; auto). constructor. intros.
  unfold tarray in *. inversion H4; subst. 1: simpl in H10; inversion H10.
  inversion H5; subst. 1: simpl in H10; inversion H10. unfold sizeof in *.
  remember (Ctypes.sizeof t) as S. rewrite ptrofs_add_repr in H15.
  rewrite Ptrofs.unsigned_repr in * by rep_lia.
  assert (0 <= i < n1 \/ n1 <= i < n) by lia. destruct H10.
  1: apply H14; assumption. assert (0 <= i - n1 < n - n1) by lia.
  specialize (H15 _ H11). rewrite H8 in H15. assumption.
Qed.

Lemma data_at_tarray_fold: forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    complete_legal_cosu_type t = true ->
    data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p) |--
            data_at sh (tarray t n) v p.
Proof.
  intros. rewrite (split2_data_at_Tarray sh t n n1 v v' v1 v2);
            [|assumption..]. entailer!. unfold field_address0. rewrite if_true.
  - simpl nested_field_offset. entailer!.
  - pose proof (field_compatible_tarray_join n _ p _ H H4 H5 H7). clear -H1 H.
    red in H1. red. simpl in *. intuition.
Qed.

Lemma data_at_tarray_unfold: forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    data_at sh (tarray t n) v p |--
            data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p).
Proof.
  intros. sep_apply (data_at_local_facts sh (tarray t n) v p).
  Intros. rewrite (split2_data_at_Tarray sh t n n1 v v' v1 v2);
            [|assumption..]. cancel. unfold field_address0. rewrite if_true.
  - simpl nested_field_offset. entailer!.
  - clear -H H4. red. red in H4. simpl in *. intuition.
Qed.

Lemma data_at_tarray_split: forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    complete_legal_cosu_type t = true ->
    data_at sh (tarray t n) v p =
    data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p).
Proof.
  intros. apply pred_ext.
  - apply data_at_tarray_unfold with v'; assumption.
  - apply data_at_tarray_fold with v'; assumption.
Qed.

Lemma data_at_tarray_value: forall sh n n1 p (v v' v1 v2: list val),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 n1 v' ->
    v2 = sublist n1 n v' ->
    data_at sh (tarray int_or_ptr_type n) v p =
    data_at sh (tarray int_or_ptr_type n1) v1 p *
    data_at sh (tarray int_or_ptr_type (n - n1)) v2 (offset_val (WORD_SIZE * n1) p).
Proof. intros. eapply data_at_tarray_split; eauto. Qed.

Lemma data_at_tarray_space: forall sh n n1 p (v: list (reptype space_type)),
    0 <= n1 <= n ->
    n = Zlength v ->
    data_at sh (tarray space_type n) v p =
    data_at sh (tarray space_type n1) (sublist 0 n1 v) p *
    data_at sh (tarray space_type (n - n1)) (sublist n1 n v)
            (offset_val (SPACE_STRUCT_SIZE * n1) p).
Proof.
  intros. eapply data_at_tarray_split; eauto. 1: lia.
  autorewrite with sublist. reflexivity.
Qed.

Lemma data_at__tarray_value: forall sh n n1 p,
    0 <= n1 <= n ->
    data_at_ sh (tarray int_or_ptr_type n) p =
    data_at_ sh (tarray int_or_ptr_type n1) p *
    data_at_ sh (tarray int_or_ptr_type (n - n1)) (offset_val (WORD_SIZE * n1) p).
Proof.
  intros. rewrite !data_at__eq.
  apply data_at_tarray_value with (default_val (tarray int_or_ptr_type n));
    [assumption | unfold default_val; simpl; autorewrite with sublist..];
    [lia | reflexivity..].
Qed.

(*
Lemma field_compatible_tarray_join':
  forall (n n1 : Z) (p : val) (t: type),
    0 <= n1 <= n -> complete_legal_cosu_type t = true ->
    field_compatible (tarray t (n - n1)) [] p ->
    field_compatible (tarray t n1) [] (offset_val (sizeof t * (n - n1)) p) ->
    field_compatible (tarray t n) [] p.
Proof.
  intros. unfold field_compatible. simpl. destruct H1 as [? [_ [? [? _]]]].
  destruct H2 as [_ [_ [? [? _]]]]. destruct p; try contradiction. clear H1.
  simpl isptr. inv_int i. unfold size_compatible in *. simpl in H2.
  simpl sizeof in *. rewrite Z.max_r in * by lia. pose proof (Ctypes.sizeof_pos t).
  unfold sizeof in H2. remember (Ctypes.sizeof t) as S. rewrite ptrofs_add_repr in H2.
  rewrite Ptrofs.unsigned_repr in * by rep_lia.
  assert (0 <= ofs + S * n1 <= Ptrofs.max_unsigned). {
    destruct H, H6. split. 2: rep_lia. apply Z.add_nonneg_nonneg. 1: lia.
    apply Z.mul_nonneg_nonneg; lia. }
  rewrite Ptrofs.unsigned_repr in * by assumption.
  assert (forall i, ofs + S * n1 + S * (i - n1) = ofs + S * i). {
    intros. rewrite <- Z.add_assoc. rewrite <- Z.mul_add_distr_l.
    do 2 f_equal. lia. } rewrite H8 in H2. do 4 (split; auto). constructor. intros.
  unfold tarray in *. inversion H4; subst. 1: simpl in H10; inversion H10.
  inversion H5; subst. 1: simpl in H10; inversion H10. unfold sizeof in *.
  remember (Ctypes.sizeof t) as S. rewrite ptrofs_add_repr in H15.
  rewrite Ptrofs.unsigned_repr in * by rep_lia.
  assert (0 <= i < n1 \/ n1 <= i < n) by lia. destruct H10.
  1: apply H14; assumption. assert (0 <= i - n1 < n - n1) by lia.
  specialize (H15 _ H11). rewrite H8 in H15. assumption.
Qed.

Lemma data_at_tarray_fold': forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 (n - n1) v' ->
    v2 = sublist (n - n1) n v' ->
    complete_legal_cosu_type t = true ->
    data_at sh (tarray t (n - n1)) v1 p *
    data_at sh (tarray t n1) v2 (offset_val (sizeof t * (n - n1)) p) |--
            data_at sh (tarray t n) v p.
Proof.
  intros.
  rewrite (split2_data_at_Tarray sh t n (n - n1) v v' v1 v2) ; try easy ; try lia.
  entailer!.
  unfold field_address0.
  rewrite if_true.
  - simpl nested_field_offset.
    replace
      (n - (n - Zlength v2))
      with (Zlength v2)
      by lia.
    entailer!.
  - pose proof (field_compatible_tarray_join' n _ p _ H H4 H5 H7).
    clear -H1 H.
    red in H1. red. simpl in *. intuition.
Qed.

Lemma data_at_tarray_unfold': forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 (n - n1) v' ->
    v2 = sublist (n - n1) n v' ->
    data_at sh (tarray t n) v p |--
            data_at sh (tarray t n1) v1 p *
    data_at sh (tarray t (n - n1)) v2 (offset_val (sizeof t * n1) p).
Proof.
  intros. sep_apply (data_at_local_facts sh (tarray t n) v p).
  Intros. rewrite (split2_data_at_Tarray sh t n n1 v v' v1 v2);
            [|assumption..]. cancel. unfold field_address0. rewrite if_true.
  - simpl nested_field_offset. entailer!.
  - clear -H H4. red. red in H4. simpl in *. intuition.
Qed.

Lemma data_at_tarray_split': forall sh n n1 p t (v v' v1 v2: list (reptype t)),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 (n - n1) v' ->
    v2 = sublist (n - n1) n v' ->
    complete_legal_cosu_type t = true ->
    data_at sh (tarray t n) v p =
    data_at sh (tarray t (n - n1)) v1 p *
    data_at sh (tarray t n1) v2 (offset_val (sizeof t * (n - n1)) p).
Proof.
  intros. apply pred_ext.
  - now apply data_at_tarray_unfold' with v'.
  - now apply data_at_tarray_fold' with v'.
Qed.

Lemma data_at_tarray_value': forall sh n n1 p (v v' v1 v2: list val),
    0 <= n1 <= n ->
    n <= Zlength v' ->
    v = sublist 0 n v' ->
    v1 = sublist 0 (n - n1) v' ->
    v2 = sublist (n - n1) n v' ->
    data_at sh (tarray int_or_ptr_type n) v p =
    data_at sh (tarray int_or_ptr_type (n - n1)) v1 p *
    data_at sh (tarray int_or_ptr_type n1) v2 (offset_val (WORD_SIZE * (n - n1)) p).
Proof.
  intros.
  eapply data_at_tarray_split'; eauto.
Qed.

Lemma data_at__tarray_value': forall sh n n1 p,
    0 <= n1 <= n ->
    data_at_ sh (tarray int_or_ptr_type n) p =
    data_at_ sh (tarray int_or_ptr_type (n - n1)) p *
    data_at_ sh (tarray int_or_ptr_type n1) (offset_val (WORD_SIZE * (n - n1)) p).
Proof.
  intros. rewrite !data_at__eq.
  apply data_at_tarray_value' with (default_val (tarray int_or_ptr_type n));
    [assumption | unfold default_val; simpl; autorewrite with sublist..];
    [lia | reflexivity..].
Qed.
*)

Definition valid_int_or_ptr (x: val) :=
  match x with
  | Vint i => if Archi.ptr64 then False else Int.testbit i 0 = true
  | Vptr _ z => Ptrofs.testbit z 0 = false /\ Ptrofs.testbit z 1 = false
  | Vlong i => if Archi.ptr64 then Int64.testbit i 0 = true else False
  | _ => False
  end.

Lemma valid_int_or_ptr_ii1:
  forall i, valid_int_or_ptr (Z2val (i + i + 1)).
Proof.
  intros.
  simpl.
  first [rewrite Int.unsigned_repr_eq | rewrite Int64.unsigned_repr_eq].
  rewrite Zodd_mod.
  apply Zeq_is_eq_bool.
  replace (i+i) with (2 * i)%Z by lia.
  rewrite <- Zmod_div_mod; try lia.
  - rewrite Z.mul_comm, Z.add_comm, Z_mod_plus_full. reflexivity.
  - compute; reflexivity.
  - first [now exists (Z.div Int.modulus 2) | now exists (Z.div Int64.modulus 2)].
Qed.

Lemma even_divided_odd_false: forall n z,
    Z.even n = true -> (n | z) -> Z.odd z = false.
Proof.
  intros. rewrite Zodd_mod. destruct (Zaux.Zeven_ex n) as [p ?].
  rewrite H, Z.add_0_r in H1. inversion H0. subst.
  replace (x * (2 * p))%Z with (x * p * 2)%Z by lia.
  rewrite Z_mod_mult; unfold Zeq_bool; reflexivity.
Qed.

Lemma four_divided_tenth_pl_false: forall n i,
    (4 | n) -> (n | Ptrofs.unsigned i) -> Ptrofs.testbit i 1 = false.
Proof.
  intros. unfold Ptrofs.testbit. inversion H. inversion H0. rewrite H2. subst.
  replace (x0 * (x * 4))%Z with (2 * (x * x0 * 2))%Z by lia.
  rewrite Z.double_bits. simpl. rewrite Zodd_mod, Z_mod_mult.
  unfold Zeq_bool; reflexivity.
Qed.

Lemma vertex_rep_valid_int_or_ptr: forall sh g v,
    vertex_rep sh g v |-- !! (valid_int_or_ptr (heapgraph_block_ptr g v)).
Proof.
  intros. sep_apply (vertex_rep_isptr sh g v). Intros.
  unfold vertex_rep, vertex_at, heapgraph_block_ptr.
  remember (heapgraph_generation_base g (addr_gen v)) as vv. destruct vv; try contradiction.
  inv_int i. entailer!.
  destruct H3 as [_ [_ [_ [? _]]]]. clear -H3. hnf in H3. inv H3.
  1: simpl in H; inversion H. assert (0 <= 0 < Zlength (heapgraph_block_cells_vals g v)). {
    split; [lia|]. rewrite fields_eq_length.
    destruct (block_fields_head__cons (heapgraph_block g v)) as [r [l [? _]]]. rewrite H.
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
  } apply H4 in H. rewrite Z.mul_0_r, Z.add_0_r in H. clear H4. inv H. inv H0.
  simpl in H1. fold WORD_SIZE in *. split.
  - simpl; rewrite !ptrofs_add_repr in *.
    apply (even_divided_odd_false WORD_SIZE); easy.
  - rewrite !ptrofs_add_repr in *.
    apply (four_divided_tenth_pl_false WORD_SIZE); [apply four_div_WORD_SIZE | easy].
Qed.

Lemma graph_rep_generation_rep: forall g gen,
    heapgraph_has_gen g gen -> graph_rep g |-- generation_rep g gen * TT.
Proof.
  intros. unfold graph_rep. red in H. rewrite <- nat_inc_list_In_iff in H.
  sep_apply (iter_sepcon_in_true (generation_rep g) _ _ H). apply derives_refl.
Qed.

Lemma generation_rep_vertex_rep: forall g gen index,
    heapgraph_generation_has_index g gen index ->
    generation_rep g gen |--
                   vertex_rep (heapgraph_generation_sh g gen) g {| addr_gen := gen; addr_block := index |} * TT.
Proof.
  intros. unfold generation_rep. remember (generation_block_count (heapgraph_generation g gen)) as num.
  assert (nth index (map (fun x : nat => {| addr_gen := gen; addr_block := x |}) (nat_inc_list num))
              {| addr_gen := gen; addr_block := O |} = {| addr_gen := gen; addr_block := index |}). {
    change {| addr_gen := gen; addr_block := O |} with ((fun x: nat => {| addr_gen := gen; addr_block := x |}) O). rewrite map_nth. red in H.
    rewrite nat_inc_list_nth by lia. reflexivity.
  } assert (In {| addr_gen := gen; addr_block := index |} (map (fun x : nat => {| addr_gen := gen; addr_block := x |}) (nat_inc_list num))). {
    rewrite <- H0. apply nth_In. rewrite map_length, nat_inc_list_length.
    red in H. subst num. assumption.
  } apply (iter_sepcon_in_true (vertex_rep _ g) _ _ H1).
Qed.

Lemma graph_rep_vertex_rep: forall g v,
    heapgraph_has_block g v -> graph_rep g |-- EX sh: share, !!(writable_share sh) &&
                                                       vertex_rep sh g v * TT.
Proof.
  intros.
  sep_apply (graph_rep_generation_rep g (addr_gen v) (heapgraph_has_block__has_gen H)).
  pose proof (heapgraph_has_block__has_index H) as Hindex.
  red in Hindex.
  sep_apply (generation_rep_vertex_rep g (addr_gen v) _ Hindex).
  Exists (heapgraph_generation_sh g (addr_gen v)).
  destruct v.
  simpl.
  entailer!.
  apply generation_sh__writable.
Qed.

Lemma graph_rep_valid_int_or_ptr: forall g v,
    heapgraph_has_block g v -> graph_rep g |-- !! (valid_int_or_ptr (heapgraph_block_ptr g v)).
Proof.
  intros. sep_apply (graph_rep_vertex_rep g v H). Intros sh.
  sep_apply (vertex_rep_valid_int_or_ptr sh g v). entailer!.
Qed.

(* weak derives for use in funspecs *)
Program Definition weak_derives (P Q: mpred): mpred :=
  fun w => predicates_hered.derives (approx (S (level w)) P) (approx (S (level w)) Q).
Next Obligation.
  repeat intro.
  destruct H1.
  apply age_level in H.
  lapply (H0 a0); [|split; auto; lia].
  intro HQ; destruct HQ.
  eexists; eauto.
Defined.

Lemma derives_nonexpansive: forall P Q n,
    approx n (weak_derives P Q) = approx n (weak_derives (approx n P) (approx n Q)).
Proof.
  apply nonexpansive2_super_non_expansive; repeat intro.
  - split; intros ??%necR_level Hshift ? HP;
      destruct (Hshift _ HP); destruct HP; eexists;  eauto; eapply H; auto; lia.
  - split; intros ??%necR_level Hshift ? []; apply Hshift;
      split; auto; apply (H a0); auto; lia.
Qed.

Lemma derives_nonexpansive_l: forall P Q n,
    approx n (weak_derives P Q) = approx n (weak_derives (approx n P) Q).
Proof.
  repeat intro.
  apply (nonexpansive_super_non_expansive (fun P => weak_derives P Q)); repeat intro.
  split; intros ??%necR_level Hshift ? [];
    apply Hshift; split; auto; apply (H a0); auto; lia.
Qed.

Lemma derives_nonexpansive_r: forall P Q n,
    approx n (weak_derives P Q) = approx n (weak_derives P (approx n Q)).
Proof.
  repeat intro.
  apply (nonexpansive_super_non_expansive (fun Q => weak_derives P Q)); repeat intro.
  split; intros ??%necR_level Hshift ? HP;
    destruct (Hshift _ HP); destruct HP;
      eexists;  eauto;
        eapply H; auto; lia.
Qed.

Lemma derives_weak: forall P Q, P |-- Q -> TT |-- weak_derives P Q.
Proof.
  intros. unseal_derives.
  intros w _ ? [? HP].
  specialize (H _ HP).
  eexists; eauto.
Qed.

Lemma apply_derives: forall P Q, (weak_derives P Q && emp) * P |-- Q.
Proof.
  intros. unseal_derives.
  intros ? (? & ? & ? & [Hderives Hemp] & HP).
  destruct (join_level _ _ _ H).
  apply Hemp in H; subst.
  lapply (Hderives a); [|split; auto; lia].
  intro X; destruct X; eauto 7.
Qed.

Definition heap_rest_gen_data_at_ (g: HeapGraph) (t_info: thread_info) (gen: nat) :=
  data_at_ (heapgraph_generation_sh g gen)
           (tarray int_or_ptr_type (space_capacity (nth_space t_info gen) - heapgraph_generation_size g gen))
           (offset_val (WORD_SIZE * heapgraph_generation_size g gen) (heapgraph_generation_base g gen)).

Lemma heap_rest_rep_iter_sepcon: forall g t_info,
    graph_thread_info_compatible g t_info ->
    heap_rest_rep (ti_heap t_info) =
    iter_sepcon (nat_inc_list (length (generations (heapgraph_generations g))))
                (heap_rest_gen_data_at_ g t_info).
Proof.
  intros. unfold heap_rest_rep.
  pose proof (gt_gs_compatible _ _ H). destruct H as [? [? ?]].
  rewrite <- (firstn_skipn (length (generations (heapgraph_generations g))) (heap_spaces (ti_heap t_info))).
  rewrite iter_sepcon_app_sepcon. rewrite <- map_skipn in H1.
  remember (skipn (length (generations (heapgraph_generations g))) (heap_spaces (ti_heap t_info))).
  assert (iter_sepcon l space_rest_rep = emp). {
    clear Heql. induction l; simpl. 1: reflexivity.
    rewrite IHl by (simpl in H1; apply Forall_tl in H1; assumption).
    rewrite Forall_forall in H1. simpl in H1. unfold space_rest_rep. rewrite if_true.
    - rewrite emp_sepcon; reflexivity.
    - symmetry. apply H1. left; reflexivity.
  } rewrite H3.
  replace (firstn (length (generations (heapgraph_generations g))) (heap_spaces (ti_heap t_info)))
    with (map (nth_space t_info) (nat_inc_list (length (generations (heapgraph_generations g))))).
  - rewrite <- iter_sepcon_map, sepcon_emp.
    apply iter_sepcon_func_strong. intros gen ?.
    unfold space_rest_rep, heap_rest_gen_data_at_.
    rewrite nat_inc_list_In_iff in H4.
    specialize (H0 _ H4).
    destruct H0 as [H0 H5 H6 H7].
    simpl in H0, H5, H6, H7.
    rewrite <- H0, if_false.
    + unfold heapgraph_generation_base, heapgraph_generation_size.
      rewrite if_true ; try easy.
      now rewrite <- H5, H6.
    + pose proof (generation_base__isptr (heapgraph_generation g gen)).
      destruct (generation_base (heapgraph_generation g gen)); try contradiction.
      intro H9. inversion H9.
  - unfold nth_space. remember (heap_spaces (ti_heap t_info)) as ls.
    remember (length (generations (heapgraph_generations g))) as m. clear -H2. revert ls H2.
    induction m; intros. 1: simpl; reflexivity. rewrite nat_inc_list_S, map_app.
    rewrite IHm by lia. simpl map. clear IHm. revert ls H2. induction m; intros.
    + destruct ls. 1: simpl in H2; exfalso; lia. simpl. reflexivity.
    + destruct ls. 1: simpl in H2; exfalso; lia.
      simpl firstn at 1. simpl nth. Opaque firstn. simpl. Transparent firstn.
      rewrite IHm by (simpl in H2; lia). simpl. destruct ls; reflexivity.
Qed.

Lemma heap_rest_rep_data_at_: forall (g: HeapGraph) (t_info: thread_info) gen,
    heapgraph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    heap_rest_rep (ti_heap t_info) |-- heap_rest_gen_data_at_ g t_info gen * TT.
Proof.
  intros. rewrite (heap_rest_rep_iter_sepcon g) by assumption.
  sep_apply (iter_sepcon_in_true (heap_rest_gen_data_at_ g t_info)
                                 (nat_inc_list (length (generations (heapgraph_generations g)))) gen).
  - rewrite nat_inc_list_In_iff. assumption.
  - apply derives_refl.
Qed.

Definition generation_data_at_ g t_info gen :=
  data_at_
    (heapgraph_generation_sh g gen)
    (tarray int_or_ptr_type (gen_size t_info gen - space_remembered (nth_space t_info gen)))
    (heapgraph_generation_base g gen).

Definition generation_remembered_data_at_ (g: HeapGraph) (t_info: thread_info) (gen: nat) :=
  data_at_ (heapgraph_generation_sh g gen)
           (tarray int_or_ptr_type (space_remembered (nth_space t_info gen)))
           (offset_val (WORD_SIZE * (gen_size t_info gen - space_remembered (nth_space t_info gen))) (heapgraph_generation_base g gen)).

Lemma gr_hrgda_data_at_ g t_info gen (H: heapgraph_has_gen g gen) (H0: graph_thread_info_compatible g t_info):
    generation_rep g gen * heap_rest_gen_data_at_ g t_info gen
    |-- generation_data_at_ g t_info gen * generation_remembered_data_at_ g t_info gen.
Proof.
  sep_apply (generation_rep_data_at_ g gen H).
  unfold heap_rest_gen_data_at_, generation_data_at_, generation_remembered_data_at_, gen_size.
  remember (nth_space t_info gen) as sp.
  pose proof (space_allocated__order sp) as Hsp_alloc.
  pose proof (space_remembered__order sp) as Hsp_rem.
  remember (heapgraph_generation_sh g gen) as sh.
  pose proof (generation__space__compatible__allocated (gt_gs_compatible _ _ H0 _ H)) as Hallocated.
  simpl in Hallocated.
  unfold heapgraph_generation_size.
  repeat rewrite Hallocated.
  clear Hallocated.
  rewrite <- (data_at__tarray_value sh _ _ (heapgraph_generation_base g gen)) by (now subst sp).
  remember
    (space_capacity sp) as n.
  remember
    (n - space_remembered sp)
    as n1.
  replace
    (space_remembered sp)
    with (n - n1)
    by lia.
  rewrite <- (data_at__tarray_value sh _ _ (heapgraph_generation_base g gen)) by (subst ; lia).
  cancel.
Qed.

Lemma graph_heap_rest_iter_sepcon: forall g t_info,
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep (ti_heap t_info)
    |-- iter_sepcon (nat_inc_list (length (generations (heapgraph_generations g)))) (generation_data_at_ g t_info)
      * iter_sepcon (nat_inc_list (length (generations (heapgraph_generations g)))) (generation_remembered_data_at_ g t_info).
Proof.
  intros.
  unfold graph_rep.
  rewrite (heap_rest_rep_iter_sepcon _ _ H).
  assert
    (forall gen, In gen (nat_inc_list (length (generations (heapgraph_generations g)))) -> heapgraph_has_gen g gen)
    as H0
    by (intros; rewrite nat_inc_list_In_iff in H0; assumption).
  remember (length (generations (heapgraph_generations g))) as n eqn:Heqn.
  clear Heqn.
  revert H0.
  induction n; intros.
  - simpl. rewrite emp_sepcon. apply derives_refl.
  - rewrite nat_inc_list_S, !iter_sepcon_app_sepcon. simpl.
    rewrite !sepcon_emp. pull_left (generation_rep g n). rewrite <- sepcon_assoc.
    rewrite (sepcon_assoc (generation_rep g n)). sep_apply IHn.
    + intros. apply H0. rewrite nat_inc_list_S, in_app_iff. left; assumption.
    + cancel. sep_apply (gr_hrgda_data_at_ g t_info n); auto.
      apply H0. rewrite nat_inc_list_S, in_app_iff. right. left. reflexivity.
Qed.

Lemma graph_and_heap_rest_data_at_: forall (g: HeapGraph) (t_info: thread_info) gen,
    heapgraph_has_gen g gen ->
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep (ti_heap t_info)
    |-- generation_data_at_ g t_info gen * generation_remembered_data_at_ g t_info gen * TT.
Proof.
  intros. sep_apply (graph_heap_rest_iter_sepcon _ _ H0).
  sep_apply (iter_sepcon_in_true (generation_data_at_ g t_info) (nat_inc_list (length (generations (heapgraph_generations g)))) gen).
  {
    now rewrite nat_inc_list_In_iff.
  }
  sep_apply (iter_sepcon_in_true (generation_remembered_data_at_ g t_info) (nat_inc_list (length (generations (heapgraph_generations g)))) gen).
  {
    now rewrite nat_inc_list_In_iff.
  }
  entailer!.
Qed.

Lemma graph_and_heap_rest_valid_ptr: forall (g: HeapGraph) (t_info: thread_info) gen
    (Hremembered: gen_size t_info gen > space_remembered (nth_space t_info gen)),
    heapgraph_has_gen g gen -> ti_size_spec t_info ->
    graph_thread_info_compatible g t_info ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
                                valid_pointer (space_base (nth_space t_info gen)).
Proof.
  intros. sep_apply (graph_and_heap_rest_data_at_ _ _ _ H H1).
  unfold generation_data_at_.
  destruct (gt_gs_compatible _ _ H1 _ H) as [H2 H3 H4 H6].
  simpl in *.
  sep_apply (data_at__memory_block_cancel
               (heapgraph_generation_sh g gen)
               (tarray int_or_ptr_type (gen_size t_info gen - space_remembered (nth_space t_info gen)))
               (heapgraph_generation_base g gen)).
  simpl sizeof.
  rewrite Z.max_r.
  2: {
    pose proof (space_remembered__order (nth_space t_info gen)).
    lia.
  }
  unfold heapgraph_generation_base.
  if_tac.
  2: {
    contradiction.
  }
  rewrite H2.
  fold WORD_SIZE.
  sep_apply (memory_block_valid_ptr
               (heapgraph_generation_sh g gen)
               (WORD_SIZE * (gen_size t_info gen - space_remembered (nth_space t_info gen)))
               (space_base (nth_space t_info gen))).
  {
    apply readable_nonidentity, writable_readable, generation_sh__writable.
  }
  {
    pose proof (ti_size_gt_0 g t_info gen H1 H5 H0).
    pose proof (space_remembered__order (nth_space t_info gen)).
    unfold gen_size, WORD_SIZE in *.
    lia.
  }
  {
    entailer!.
  }
Qed.

Lemma generation_data_at__ptrofs: forall g t_info gen b i,
    Vptr b i = heapgraph_generation_base g gen ->
    generation_data_at_ g t_info gen |--
                        !! (WORD_SIZE * (gen_size t_info gen - space_remembered (nth_space t_info gen)) + Ptrofs.unsigned i <=
                            Ptrofs.max_unsigned).
Proof.
  intros. unfold generation_data_at_. rewrite <- H. entailer!.
  destruct H0 as [_ [_ [? _]]]. red in H0. simpl sizeof in H0. unfold WORD_SIZE.
  unfold gen_size in *.
  rewrite Z.max_r in H0.
  {
    rep_lia.
  }
  pose proof (space_remembered__order (nth_space t_info gen)).
  lia.
Qed.

Lemma outlier_rep_single_rep: forall outlier p,
    In p outlier ->
    outlier_rep outlier |-- single_outlier_rep p * TT.
Proof.
  intros. unfold outlier_rep. apply (in_map single_outlier_rep) in H.
  apply log_normalize.fold_right_andp in H. destruct H as [Q ?]. rewrite H.
  apply andp_left1. cancel.
Qed.

Lemma roots_outlier_rep_single_rep: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier ->
    outlier_rep outlier |-- single_outlier_rep p * TT.
Proof. intros. apply outlier_rep_single_rep. eapply root_in_outlier; eauto. Qed.

Lemma single_outlier_rep_valid_pointer: forall p,
    single_outlier_rep p |-- valid_pointer (GC_Pointer2val p) * TT.
Proof.
  intros. unfold single_outlier_rep. Intros sh. remember (GC_Pointer2val p) as pp.
  sep_apply (data_at__memory_block_cancel sh int_or_ptr_type pp). simpl sizeof.
  fold WORD_SIZE. sep_apply (memory_block_valid_ptr sh WORD_SIZE pp);
                    [apply readable_nonidentity; assumption | apply derives_refl].
Qed.

Lemma outlier_rep_valid_pointer: forall outlier p,
    In p outlier ->
    outlier_rep outlier |-- valid_pointer (GC_Pointer2val p) * TT.
Proof.
  intros. sep_apply (outlier_rep_single_rep _ _ H).
  sep_apply (single_outlier_rep_valid_pointer p). cancel.
Qed.

Lemma roots_outlier_rep_valid_pointer: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier ->
    outlier_rep outlier |-- valid_pointer (GC_Pointer2val p) * TT.
Proof. intros. apply outlier_rep_valid_pointer. eapply root_in_outlier; eauto. Qed.

Lemma single_outlier_rep_valid_int_or_ptr: forall p,
    single_outlier_rep p |-- !! (valid_int_or_ptr (GC_Pointer2val p)).
Proof.
  intros. unfold single_outlier_rep. Intros sh. remember (GC_Pointer2val p) as pp.
  clear Heqpp. entailer!. destruct H0 as [? [_ [_ [? _]]]].
  destruct pp; try contradiction. unfold align_compatible in H1. inv H1.
  inv H2. simpl in H3. fold WORD_SIZE in *. split.
  - simpl; apply (even_divided_odd_false WORD_SIZE); easy.
  - apply (four_divided_tenth_pl_false WORD_SIZE); [apply four_div_WORD_SIZE | easy].
Qed.

Import Share.

Lemma writable_readable_share_common: forall rsh wsh,
    readable_share rsh -> writable_share wsh ->
    exists sh, nonunit sh /\ join_sub sh rsh /\ join_sub sh wsh.
Proof.
  intros. assert (join (glb Lsh rsh) (glb Rsh rsh) rsh). {
    apply (comp_parts_join comp_Lsh_Rsh).
    - rewrite glb_twice, <- glb_assoc, glb_Lsh_Rsh, (glb_commute bot), glb_bot.
      apply join_comm, bot_join_eq.
    - rewrite <- glb_assoc, (glb_commute Rsh), glb_Lsh_Rsh,
      (glb_commute bot), glb_bot, glb_twice. apply bot_join_eq.
  } assert (join (glb Rsh rsh) (glb Rsh (comp rsh)) Rsh). {
    rewrite !(glb_commute Rsh). apply (@comp_parts_join rsh (comp rsh)); auto.
    - rewrite glb_twice, <- glb_assoc, comp2, (glb_commute bot), glb_bot.
      apply join_comm, bot_join_eq.
    - rewrite <- glb_assoc, (glb_commute (comp _)), comp2, (glb_commute bot), glb_bot,
      glb_twice. apply bot_join_eq.
  } exists (glb Rsh rsh). split; [|split].
  - red in H. apply nonidentity_nonunit, H.
  - apply join_comm in H1. exists (glb Lsh rsh). assumption.
  - apply join_sub_trans with Rsh; [exists (glb Rsh (comp rsh))|destruct H0];
      assumption.
Qed.

Lemma readable_writable_memory_block_FF: forall rsh wsh m1 m2 p,
    readable_share rsh -> writable_share wsh ->
    0 < m1 <= Ptrofs.max_unsigned -> 0 < m2 <= Ptrofs.max_unsigned ->
    memory_block rsh m1 p * memory_block wsh m2 p |-- FF.
Proof.
  intros.
  destruct (writable_readable_share_common _ _ H H0) as [sh [? [[shr ?] [shw ?]]]].
  rewrite <- (memory_block_share_join _ _ _ _ _ H4).
  rewrite <- (memory_block_share_join _ _ _ _ _ H5).
  rewrite <- sepcon_assoc, (sepcon_comm (memory_block sh m1 p)),
  (sepcon_assoc (memory_block shr m1 p)).
  sep_apply (memory_block_conflict sh _ _ p H3 H1 H2). entailer!.
Qed.

Lemma v_in_range_data_at_: forall v p n sh,
    v_in_range v p (WORD_SIZE * n) ->
    data_at_ sh (tarray int_or_ptr_type n) p |--
             EX m: Z, !!(0 < m <= Ptrofs.max_unsigned) && memory_block sh m v * TT.
Proof.
  intros. destruct H as [o [? ?]]. rewrite data_at__memory_block. Intros.
  destruct H1 as [? [_ [? _]]]. destruct p; try contradiction. inv_int i.
  simpl offset_val in H0. rewrite ptrofs_add_repr in H0.
  assert (0 <= n)%Z by (unfold WORD_SIZE in *; rep_lia).
  rewrite sizeof_tarray_int_or_ptr by assumption.
  simpl in H2. rewrite Ptrofs.unsigned_repr in H2 by rep_lia.
  rewrite Z.max_r in H2 by assumption. fold WORD_SIZE in *.
  assert (WORD_SIZE * n = o + (WORD_SIZE * n - o))%Z by lia.
  remember (WORD_SIZE * n - o) as m.
  rewrite H5 in *. rewrite (memory_block_split sh b ofs o m) by lia.
  clear Heqm n H5 H3. rewrite <- H0. Exists m. entailer!.
Qed.

Lemma single_outlier_rep_memory_block_FF: forall gp p n wsh,
    writable_share wsh -> v_in_range (GC_Pointer2val gp) p (WORD_SIZE * n) ->
    single_outlier_rep gp * data_at_ wsh (tarray int_or_ptr_type n) p |-- FF.
Proof.
  intros. unfold single_outlier_rep. Intros rsh. remember (GC_Pointer2val gp) as ggp.
  clear gp Heqggp. rename ggp into gp.
  sep_apply (v_in_range_data_at_ _ _ _ wsh H0). Intros m.
  sep_apply (data_at__memory_block_cancel rsh int_or_ptr_type gp). simpl sizeof.
  rewrite <- sepcon_assoc. fold WORD_SIZE.
  now sep_apply (readable_writable_memory_block_FF _ _ WORD_SIZE m gp H1 H) ; try entailer.
Qed.

Lemma graph_and_heap_rest_v_in_range_iff: forall g t_info gen v,
    graph_thread_info_compatible g t_info ->
    heapgraph_has_gen g gen -> heapgraph_has_block g v ->
    graph_rep g * heap_rest_rep (ti_heap t_info) |--
    !! (v_in_range (heapgraph_block_ptr g v) (heapgraph_generation_base g gen)
                   (WORD_SIZE * (gen_size t_info gen - space_remembered (nth_space t_info gen))) <-> addr_gen v = gen).
Proof.
  intros. unfold iff. rewrite and_comm. apply prop_and_right.
  - intros. rewrite <- H2.
    now apply graph_thread_v_in_range.
  - rewrite prop_impl, <- imp_andp_adjoint; Intros.
    destruct (Nat.eq_dec (addr_gen v) gen). 1: apply prop_right; assumption.
    sep_apply (graph_heap_rest_iter_sepcon _ _ H).
    pose proof (graph_thread_v_in_range _ _ _ H H1).
    pose proof (heapgraph_has_block__has_gen H1) as Hgen.
    assert (NoDup [addr_gen v; gen]) by
        (constructor; [|constructor; [|constructor]]; intro HS;
         simpl in HS; destruct HS; auto).
    assert (incl [addr_gen v; gen] (nat_inc_list (length (generations (heapgraph_generations g))))) by
        (apply incl_cons; [|apply incl_cons];
         [rewrite nat_inc_list_In_iff; assumption..| apply incl_nil]).
    sep_apply (iter_sepcon_incl_true (generation_data_at_ g t_info) H4 H5); simpl.
    rewrite sepcon_emp. unfold generation_data_at_.
    remember (heapgraph_generation_sh g (addr_gen v)) as sh1.
    remember (heapgraph_generation_sh g gen) as sh2.
    sep_apply (v_in_range_data_at_ _ _ _ sh1 H3). Intros m1.
    sep_apply (v_in_range_data_at_ _ _ _ sh2 H2). Intros m2.
    remember (heapgraph_block_ptr g v) as p.
    rewrite <- sepcon_assoc, (sepcon_comm (memory_block sh2 m2 p)),
    (sepcon_assoc TT).
    sep_apply (readable_writable_memory_block_FF sh2 sh1 m2 m1 p); auto.
    + apply writable_readable. subst. apply generation_sh__writable.
    + subst. apply generation_sh__writable.
    + entailer!.
Qed.

Lemma graph_gen_ramif_stable: forall g gen,
    heapgraph_has_gen g gen ->
    graph_rep g |-- generation_rep g gen * (generation_rep g gen -* graph_rep g).
Proof.
  intros. unfold graph_rep. remember (nat_inc_list (length (generations (heapgraph_generations g)))).
  apply iter_sepcon_ramif_stable_1. subst l. rewrite nat_inc_list_In_iff. assumption.
Qed.

Lemma gen_vertex_ramif_stable: forall g gen index,
    heapgraph_generation_has_index g gen index ->
    generation_rep g gen |--
                   vertex_rep (heapgraph_generation_sh g gen) g {| addr_gen := gen; addr_block := index |} *
    (vertex_rep (heapgraph_generation_sh g gen) g {| addr_gen := gen; addr_block := index |} -* generation_rep g gen).
Proof.
  intros. unfold generation_rep. remember (heapgraph_generation_sh g gen) as sh.
  apply iter_sepcon_ramif_stable_1.
  change {| addr_gen := gen; addr_block := index |} with ((fun x : nat => {| addr_gen := gen; addr_block := x |}) index). apply in_map.
  rewrite nat_inc_list_In_iff. assumption.
Qed.

Lemma graph_vertex_ramif_stable: forall g v,
    heapgraph_has_block g v ->
    graph_rep g |-- vertex_rep (heapgraph_generation_sh g (addr_gen v)) g v *
    (vertex_rep (heapgraph_generation_sh g (addr_gen v)) g v -* graph_rep g).
Proof.
  intros.
  sep_apply (graph_gen_ramif_stable _ _ (heapgraph_has_block__has_gen H)).
  sep_apply (gen_vertex_ramif_stable _ _ _ (heapgraph_has_block__has_index H)).
  destruct v as [gen index].
  simpl. cancel. apply wand_frame_ver.
Qed.

Lemma heap_rest_rep_cut: forall (h: Heap) i s (H1: 0 <= i < Zlength (heap_spaces h))
                                (H2: has_space (Znth i (heap_spaces h)) s),
    space_base (Znth i (heap_spaces h)) <> nullval ->
    heap_rest_rep h =
    data_at_ (space_sh (Znth i (heap_spaces h))) (tarray int_or_ptr_type s)
             (offset_val (WORD_SIZE * space_allocated (Znth i (heap_spaces h)))
                         (space_base (Znth i (heap_spaces h)))) *
    heap_rest_rep (cut_heap h i s H1 H2).
Proof.
  intros. unfold heap_rest_rep.
  pose proof (split3_full_length_list
                0 i _ _ H1 (Zminus_0_l_reverse (Zlength (heap_spaces h)))).
  replace (i - 0) with i in H0 by lia. simpl in *.
  remember (firstn (Z.to_nat i) (heap_spaces h)) as l1.
  remember (skipn (Z.to_nat (i + 1)) (heap_spaces h)) as l2.
  assert (Zlength l1 = i). {
    rewrite Zlength_length by lia. subst l1. apply firstn_length_le.
    rewrite Zlength_correct in H1. rep_lia. }
  rewrite H0 at 5. rewrite (upd_Znth_char _ _ _ _ _ H3).
  rewrite H0 at 1. rewrite !iter_sepcon_app_sepcon. simpl.
  remember (data_at_ (space_sh (Znth i (heap_spaces h))) (tarray int_or_ptr_type s)
                     (offset_val (WORD_SIZE * space_allocated (Znth i (heap_spaces h)))
                                 (space_base (Znth i (heap_spaces h))))) as P.
  rewrite (sepcon_comm P), sepcon_assoc. f_equal.
  rewrite (sepcon_comm _ P), <- sepcon_assoc. f_equal.
  unfold space_rest_rep. simpl. do 2 rewrite if_false by assumption.
  red in H2. subst P.
  remember (Znth i (heap_spaces h)) as sp.
  assert
    (0 <= s <= space_capacity sp - space_allocated sp)
    as Hs
    by (pose proof (space_remembered__order sp) ; lia).
  rewrite (data_at__tarray_value (space_sh sp) _ _ _ Hs).
  rewrite offset_offset_val.
  f_equal.
  f_equal.
  - f_equal.
    lia.
  - f_equal.
    lia.
Qed.

Lemma data_at__singleton_array_eq:
  forall sh tp p, data_at_ sh (tarray tp 1) p = data_at_ sh tp p.
Proof.
  intros. rewrite data_at__tarray. simpl.
  rewrite data_at__eq, (data_at_singleton_array_eq _ _ (default_val tp)); reflexivity.
Qed.

Lemma field_compatible_int_or_ptr_integer_iff: forall p,
    field_compatible int_or_ptr_type [] p <->
    field_compatible (if Archi.ptr64 then tulong else tuint) [] p.
Proof.
  intros. unfold field_compatible. simpl.
  intuition; unfold align_compatible in *; destruct p; try constructor; inv H2;
    inv H3; apply align_compatible_rec_by_value with
                (ch := (if Archi.ptr64 then Mint64 else Mint32)); try reflexivity;
      simpl in *; assumption.
Qed.

Lemma data_at__int_or_ptr_integer: forall sh p,
    data_at_ sh (tarray int_or_ptr_type 1) p =
    data_at_ sh (if Archi.ptr64 then tulong else tuint) p.
Proof.
  intros. rewrite data_at__singleton_array_eq, !data_at__memory_block,
          field_compatible_int_or_ptr_integer_iff. reflexivity.
Qed.

Lemma lacv_generation_rep_not_eq: forall g v to n,
    n <> to -> heapgraph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    generation_rep (lgraph_add_copied_v g v to) n = generation_rep g n.
Proof.
  intros. unfold generation_rep. rewrite lacv_heapgraph_generation by assumption.
  apply iter_sepcon_func_strong. intros. apply list_in_map_inv in H3.
  destruct H3 as [m [? ?]]. unfold heapgraph_generation_sh. rewrite lacv_heapgraph_generation by assumption.
  remember (generation_sh (heapgraph_generation g n)) as sh. unfold vertex_rep. subst x.
  assert (heapgraph_has_block g {| addr_gen := n ; addr_block := m |}). {
    rewrite nat_inc_list_In_iff in H4.
    destruct (Nat.lt_ge_cases n (length (generations (heapgraph_generations g)))).
    - split; simpl; assumption.
    - exfalso. unfold heapgraph_generation in H4. rewrite nth_overflow in H4 by assumption.
      simpl in H4. lia. } f_equal.
  - apply lacv_heapgraph_block_ptr_old; assumption.
  - apply lacv_heapgraph_block_header__old. intro S; inversion S. contradiction.
  - apply lacv_heapgraph_block_cells_vals_old; assumption.
Qed.

Lemma lacv_icgr_not_eq: forall l g v to,
    ~ In to l -> heapgraph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    iter_sepcon l (generation_rep (lgraph_add_copied_v g v to)) =
    iter_sepcon l (generation_rep g).
Proof.
  intros. induction l; simpl. 1: reflexivity. rewrite IHl.
  - f_equal. apply lacv_generation_rep_not_eq; [|assumption..].
    intro. apply H. left. assumption.
  - intro. apply H. right. assumption.
Qed.

Lemma lacv_generation_rep_eq: forall g v to,
    heapgraph_has_block g v -> heapgraph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    generation_rep (lgraph_add_copied_v g v to) to =
    vertex_at (heapgraph_generation_sh g to) (heapgraph_block_ptr g (new_copied_v g to))
              (heapgraph_block_header g v) (heapgraph_block_cells_vals g v) * generation_rep g to.
Proof.
  intros. unfold generation_rep. rewrite lacv_nth_sh by assumption.
  remember (generation_block_count (heapgraph_generation g to)).
  unfold lgraph_add_copied_v at 1. unfold heapgraph_generation. simpl.
  rewrite cvmgil_eq by assumption. simpl. unfold heapgraph_generation in Heqn. rewrite <- Heqn.
  rewrite nat_inc_list_app, map_app, iter_sepcon_app_sepcon, sepcon_comm.
  simpl nat_seq. change (nth to (generations (heapgraph_generations g)) null_generation) with
                     (heapgraph_generation g to) in Heqn. f_equal.
  - simpl. normalize. replace {| addr_gen := to ; addr_block := n |} with (new_copied_v g to) by
        (unfold new_copied_v; subst n; reflexivity). unfold vertex_rep. f_equal.
    + apply lacv_heapgraph_block_ptr_new. assumption.
    + apply lacv_heapgraph_block_header__new.
    + apply lacv_heapgraph_block_cells_vals_new; assumption.
  - apply iter_sepcon_func_strong. intros. destruct x as [m x].
    apply list_in_map_inv in H3. destruct H3 as [? [? ?]]. inversion H3. subst x0.
    subst m. clear H3. remember (heapgraph_generation_sh g to) as sh. subst n.
    rewrite nat_inc_list_In_iff in H4. unfold vertex_rep.
    assert (heapgraph_has_block g {| addr_gen := to ; addr_block := x |}) by (split; simpl; assumption).
    rewrite lacv_heapgraph_block_ptr_old, lacv_heapgraph_block_header__old, lacv_heapgraph_block_cells_vals_old;
      [reflexivity | try assumption..].
    unfold new_copied_v. intro. inversion H5. lia.
Qed.

Lemma copied_v_derives_new_g: forall g v to,
    heapgraph_has_gen g to -> no_dangling_dst g -> copy_compatible g -> heapgraph_has_block g v ->
    vertex_at (heapgraph_generation_sh g to) (heapgraph_block_ptr g (new_copied_v g to))
              (heapgraph_block_header g v) (heapgraph_block_cells_vals g v) *
    graph_rep g = graph_rep (lgraph_add_copied_v g v to).
Proof.
  intros. unfold graph_rep. unfold lgraph_add_copied_v at 1. simpl. red in H.
  rewrite cvmgil_length by assumption. remember (length (generations (heapgraph_generations g))).
  assert (n = to + (n - to))%nat by lia. assert (0 < n - to)%nat by lia.
  remember (n - to)%nat as m. rewrite H3, nat_inc_list_app, !iter_sepcon_app_sepcon.
  rewrite (lacv_icgr_not_eq (nat_inc_list to) g v to); try assumption.
  3: subst n; apply H. 2: intro; rewrite nat_inc_list_In_iff in H5; lia.
  rewrite sepcon_comm, sepcon_assoc. f_equal. assert (m = 1 + (m - 1))%nat by lia.
  rewrite H5, nat_seq_app, !iter_sepcon_app_sepcon.
  assert (nat_seq to 1 = [to]) by reflexivity. rewrite H6. clear H6.
  rewrite (lacv_icgr_not_eq (nat_seq (to + 1) (m - 1)) g v to); try assumption.
  3: subst n; apply H. 2: intro; rewrite nat_seq_In_iff in H6; lia.
  rewrite sepcon_assoc, sepcon_comm, sepcon_assoc, sepcon_comm. f_equal.
  simpl iter_sepcon. normalize. clear m Heqm H3 H4 H5. subst n.
  rewrite <- lacv_generation_rep_eq; [reflexivity | assumption..].
Qed.

Lemma data_at_tarray_split_1:
  forall sh p (tt: type) (v: reptype tt) (l: list (reptype tt)),
    complete_legal_cosu_type tt = true ->
    data_at sh (tarray tt (Zlength l + 1)) (v :: l) p =
    data_at sh tt v p *
    data_at sh (tarray tt (Zlength l)) l (offset_val (sizeof tt) p).
Proof.
  intros.
  rewrite (data_at_tarray_split sh (Zlength l + 1) 1 p tt (v :: l) (v :: l) [v] l).
  - replace (sizeof tt * 1)%Z with (sizeof tt) by lia.
    replace (Zlength l + 1 - 1) with (Zlength l) by lia. f_equal.
    rewrite (data_at_singleton_array_eq _ tt v); reflexivity.
  - rep_lia.
  - rewrite Zlength_cons. lia.
  - autorewrite with sublist; reflexivity.
  - simpl. vm_compute. reflexivity.
  - simpl. rewrite sublist_1_cons.
    replace (Zlength l + 1 - 1) with (Zlength l) by lia.
    autorewrite with sublist. reflexivity.
  - assumption.
Qed.

Lemma data_at_tarray_value_split_1: forall sh p (l: list val),
    0 < Zlength l ->
    data_at sh (tarray int_or_ptr_type (Zlength l)) l p =
    data_at sh int_or_ptr_type (hd nullval l) p *
    data_at sh (tarray int_or_ptr_type (Zlength l-1)) (tl l) (offset_val WORD_SIZE p).
Proof.
  intros. destruct l. 1: rewrite Zlength_nil in H; lia. clear H. simpl hd.
  simpl tl. rewrite Zlength_cons.
  replace (Z.succ (Zlength l)) with (Zlength l + 1) by lia.
  replace (Zlength l + 1 - 1) with (Zlength l) by lia.
  eapply data_at_tarray_split_1; eauto.
Qed.

Lemma lmc_vertex_rep_eq: forall sh g v new_v,
    vertex_rep sh (lgraph_mark_copied g v new_v) v =
    data_at sh (if Archi.ptr64 then tulong else tuint) (Z2val 0)
            (offset_val (- WORD_SIZE) (heapgraph_block_ptr g v)) *
    data_at sh int_or_ptr_type (heapgraph_block_ptr g new_v)
            (heapgraph_block_ptr g v) *
    data_at sh (tarray int_or_ptr_type (Zlength (heapgraph_block_cells_vals g v) - 1))
            (tl (heapgraph_block_cells_vals g v)) (offset_val WORD_SIZE (heapgraph_block_ptr g v)).
Proof.
  intros. unfold vertex_rep. rewrite lmc_heapgraph_block_ptr. unfold vertex_at.
  rewrite sepcon_assoc. f_equal.
  - f_equal. unfold heapgraph_block_header. simpl heapgraph_block at 1.
    unfold update_copied_old_vlabel, graph_gen.update_vlabel.
    rewrite if_true by reflexivity. simpl. unfold Z2val. reflexivity.
  - rewrite lmc_heapgraph_block_cells_vals_eq, data_at_tarray_value_split_1.
    + simpl hd. f_equal. simpl tl.
      replace (Zlength (heapgraph_block_ptr g new_v :: tl (heapgraph_block_cells_vals g v)) - 1)
        with (Zlength (heapgraph_block_cells_vals g v) - 1). 1: reflexivity.
      transitivity (Zlength (tl (heapgraph_block_cells_vals g v))).
      2: rewrite Zlength_cons; rep_lia.
      assert (0 < Zlength (heapgraph_block_cells_vals g v)) by
          (rewrite fields_eq_length; apply (proj1 (block_fields__range (heapgraph_block g v)))).
      remember (heapgraph_block_cells_vals g v). destruct l.
      1: rewrite Zlength_nil in H; lia. rewrite Zlength_cons. simpl. lia.
    + rewrite Zlength_cons. rep_lia.
Qed.

Lemma lmc_vertex_rep_not_eq: forall sh g v new_v x,
    x <> v -> vertex_rep sh (lgraph_mark_copied g v new_v) x = vertex_rep sh g x.
Proof.
  intros. unfold vertex_rep. rewrite lmc_heapgraph_block_ptr, lmc_heapgraph_block_cells_vals_not_eq.
  2: assumption. f_equal. unfold heapgraph_block_header. rewrite lmc_vlabel_not_eq by assumption.
  reflexivity.
Qed.

Lemma lmc_generation_rep_not_eq: forall (g : HeapGraph) (v new_v : Addr) (x : nat),
    x <> addr_gen v ->
    generation_rep g x = generation_rep (lgraph_mark_copied g v new_v) x.
Proof.
  intros. unfold generation_rep. unfold heapgraph_generation_sh, heapgraph_generation. simpl.
  remember (nat_inc_list (generation_block_count (nth x (generations (heapgraph_generations g)) null_generation))).
  apply iter_sepcon_func_strong. intros. destruct x0 as [n m].
  apply list_in_map_inv in H0. destruct H0 as [x0 [? ?]]. inversion H0. subst n x0.
  clear H0. remember (generation_sh (nth x (generations (heapgraph_generations g)) null_generation)) as sh.
  rewrite lmc_vertex_rep_not_eq. 1: reflexivity. intro. destruct v. simpl in *.
  inversion H0. subst. contradiction.
Qed.

Lemma graph_gen_lmc_ramif: forall g v new_v,
    heapgraph_has_gen g (addr_gen v) ->
    graph_rep g |-- generation_rep g (addr_gen v) *
    (generation_rep (lgraph_mark_copied g v new_v) (addr_gen v) -*
                    graph_rep (lgraph_mark_copied g v new_v)).
Proof.
  intros. unfold graph_rep. simpl. apply iter_sepcon_ramif_pred_1.
  red in H. rewrite <- nat_inc_list_In_iff in H. apply In_Permutation_cons in H.
  destruct H as [f ?]. exists f. split. 1: assumption. intros.
  assert (NoDup (addr_gen v :: f)) by
      (apply (Permutation_NoDup H), nat_inc_list_NoDup). apply NoDup_cons_2 in H1.
  rewrite <- lmc_generation_rep_not_eq. 1: reflexivity. intro. subst. contradiction.
Qed.

Lemma gen_vertex_lmc_ramif: forall g gen index new_v,
    heapgraph_generation_has_index g gen index ->
    generation_rep g gen |-- vertex_rep (heapgraph_generation_sh g gen) g {| addr_gen := gen; addr_block := index |} *
    (vertex_rep (heapgraph_generation_sh g gen) (lgraph_mark_copied g {| addr_gen := gen; addr_block := index |} new_v)
                {| addr_gen := gen; addr_block := index |} -*
                generation_rep (lgraph_mark_copied g {| addr_gen := gen; addr_block := index |} new_v) gen).
Proof.
  intros. unfold generation_rep. unfold heapgraph_generation. simpl. apply iter_sepcon_ramif_pred_1.
  change (nth gen (generations (heapgraph_generations g)) null_generation) with (heapgraph_generation g gen).
  remember (map (fun x : nat => {| addr_gen := gen; addr_block := x |})
                (nat_inc_list (generation_block_count (heapgraph_generation g gen)))).
  assert (In {| addr_gen := gen; addr_block := index |} l) by
      (subst l; apply in_map; rewrite nat_inc_list_In_iff; assumption).
  apply In_Permutation_cons in H0. destruct H0 as [f ?]. exists f. split.
  1: assumption. intros. unfold heapgraph_generation_sh, heapgraph_generation. simpl. rewrite lmc_vertex_rep_not_eq.
  1: reflexivity. assert (NoDup l). {
    subst l. apply FinFun.Injective_map_NoDup. 2: apply nat_inc_list_NoDup.
    red. intros. inversion H2. reflexivity. }
  apply (Permutation_NoDup H0), NoDup_cons_2 in H2. intro. subst. contradiction.
Qed.

Lemma graph_vertex_lmc_ramif: forall g v new_v,
    heapgraph_has_block g v ->
    graph_rep g |-- vertex_rep (heapgraph_generation_sh g (addr_gen v)) g v *
    (vertex_rep (heapgraph_generation_sh g (addr_gen v))
                (lgraph_mark_copied g v new_v) v -*
                graph_rep (lgraph_mark_copied g v new_v)).
Proof.
  intros.
  sep_apply (graph_gen_lmc_ramif g v new_v (heapgraph_has_block__has_gen H)).
  destruct v as [gen index].
  simpl in *.
  sep_apply (gen_vertex_lmc_ramif g gen index new_v (heapgraph_has_block__has_index H)).
  cancel. apply wand_frame_ver.
Qed.

Lemma lgd_vertex_rep_eq_in_diff_vert: forall sh g v' v v1 e n,
    0 <= n < Zlength (heapgraph_block_cells g v) ->
    Znth n (heapgraph_block_cells g v) = inr e ->
    v1 <> v ->
    vertex_rep sh g v1 = vertex_rep sh (labeledgraph_gen_dst g e v') v1.
Proof.
  intros. unfold vertex_rep.
  rewrite lgd_heapgraph_block_ptr_eq, <- heapgraph_block_header__labeledgraph_gen_dst.
  f_equal. unfold heapgraph_block_cells_vals.
  rewrite <- lgd_block_mark_eq.
  simple_if_tac; [f_equal |];
    rewrite (lgd_map_f2v_diff_vert_eq g v v' v1 e n);
    try reflexivity; assumption.
Qed.

Lemma lgd_gen_rep_eq_in_diff_gen: forall (g : HeapGraph) (v v' : Addr) (x : nat) e n,
    0 <= n < Zlength (heapgraph_block_cells g v) ->
    Znth n (heapgraph_block_cells g v) = inr e ->
    x <> addr_gen v ->
     generation_rep g x = generation_rep (labeledgraph_gen_dst g e v') x.
Proof.
  intros. unfold generation_rep.
  unfold heapgraph_generation_sh, heapgraph_generation. simpl.
  fold (heapgraph_generations g).
  remember (nat_inc_list (generation_block_count
                            (nth x (generations (heapgraph_generations g)) null_generation))).
  apply iter_sepcon_func_strong. intros v1 H2.
  apply list_in_map_inv in H2.
  destruct H2 as [x1 [? ?]].
  remember (generation_sh (nth x (generations (heapgraph_generations g)) null_generation)) as sh.
  assert (v1 <> v). {
    intro. unfold addr_gen in H1.
    rewrite H4 in H2. rewrite H2 in H1. unfold not in H1.
    simpl in H1. lia. }
  apply (lgd_vertex_rep_eq_in_diff_vert sh g v' v v1 e n); assumption.
Qed.

Lemma graph_gen_lgd_ramif: forall g v v' e n,
    0 <= n < Zlength (heapgraph_block_cells g v) ->
    Znth n (heapgraph_block_cells g v) = inr e ->
    heapgraph_has_gen g (addr_gen v) ->
    graph_rep g |-- generation_rep g (addr_gen v) *
    (generation_rep (labeledgraph_gen_dst g e v') (addr_gen v) -*
                    graph_rep (labeledgraph_gen_dst g e v')).
Proof.
  intros. unfold graph_rep. simpl.
  apply iter_sepcon_ramif_pred_1.
  red in H1. rewrite <- nat_inc_list_In_iff in H1.
  apply In_Permutation_cons in H1.
  destruct H1 as [f ?]. exists f. split. 1: assumption. intros.
  assert (NoDup (addr_gen v :: f)) by
      (apply (Permutation_NoDup H1), nat_inc_list_NoDup).
  apply NoDup_cons_2 in H3.
  assert (x <> addr_gen v) by
      (unfold not; intro; subst; contradiction).
  apply (lgd_gen_rep_eq_in_diff_gen g v v' x e n); assumption.
Qed.

Lemma gen_vertex_lgd_ramif: forall g gen index new_v v n e,
    heapgraph_generation_has_index g gen index ->
0 <= n < Zlength (heapgraph_block_cells g v) ->
       Znth n (heapgraph_block_cells g v) = inr e ->
       v = {| addr_gen := gen; addr_block := index |} ->
    generation_rep g gen |-- vertex_rep (heapgraph_generation_sh g gen) g {| addr_gen := gen; addr_block := index |} *
    (vertex_rep (heapgraph_generation_sh g gen) (labeledgraph_gen_dst g e new_v)
                {| addr_gen := gen; addr_block := index |} -*
                generation_rep (labeledgraph_gen_dst g e new_v) gen).
Proof.
  intros. unfold generation_rep. unfold heapgraph_generation.
  simpl. apply iter_sepcon_ramif_pred_1.
  fold (heapgraph_generations g).
  change (nth gen (generations (heapgraph_generations g)) null_generation) with (heapgraph_generation g gen).
  remember (map (fun x : nat => {| addr_gen := gen; addr_block := x |})
                (nat_inc_list (generation_block_count (heapgraph_generation g gen)))).
  assert (In {| addr_gen := gen; addr_block := index |} l) by
      (subst l; apply in_map; rewrite nat_inc_list_In_iff; assumption).
  apply In_Permutation_cons in H3. destruct H3 as [f ?]. exists f. split.
  1: assumption. intros. unfold heapgraph_generation_sh, heapgraph_generation. simpl.
  fold (heapgraph_generations g).
  remember (generation_sh (nth gen (generations (heapgraph_generations g)) null_generation)) as sh.
  rewrite (lgd_vertex_rep_eq_in_diff_vert sh g new_v v x e n);
    try reflexivity; try assumption.
  assert (NoDup l). {
    subst l. apply FinFun.Injective_map_NoDup. 2: apply nat_inc_list_NoDup.
    red. intros. inversion H5. reflexivity. }
  apply (Permutation_NoDup H3), NoDup_cons_2 in H5. intro.
  rewrite H2 in H6. rewrite H6 in H4. intuition.
Qed.

Lemma graph_vertex_lgd_ramif: forall g v e v' n,
    0 <= n < Zlength (heapgraph_block_cells g v) ->
    Znth n (heapgraph_block_cells g v) = inr e ->
    heapgraph_has_block g v ->
    graph_rep g |-- vertex_rep (heapgraph_generation_sh g (addr_gen v)) g v *
    (vertex_rep (heapgraph_generation_sh g (addr_gen v))
                (labeledgraph_gen_dst g e v') v -*
                graph_rep (labeledgraph_gen_dst g e v')).
Proof.
  intros. destruct H1. sep_apply (graph_gen_lgd_ramif g v v' e n);
                         try assumption.
  destruct v as [gen index] eqn:Ev. simpl addr_gen in *.
  simpl in *. rewrite <- Ev in H, H0.
  sep_apply (gen_vertex_lgd_ramif g gen index v' v n e);
    try assumption.
  cancel. apply wand_frame_ver.
Qed.

Definition space_struct_rep (sh: share) (tinfo: thread_info) (gen: nat) :=
  data_at sh space_type (space_tri (nth_space tinfo gen)) (space_address tinfo gen).

Lemma heap_struct_rep_eq: forall sh l p,
    heap_struct_rep sh l p = data_at sh (tarray space_type 12) l p.
Proof.
  intros. unfold heap_struct_rep. apply pred_ext; rewrite data_at_isptr; Intros.
  - unfold_data_at (data_at _ heap_type _ _).
    entailer!. clear H0. rewrite field_at_data_at.
    unfold field_address. rewrite if_true by assumption. simpl.
    entailer!.
  - unfold_data_at (data_at _ heap_type _ _). entailer!. clear H0 H1.
    rewrite field_at_data_at. unfold field_address. rewrite if_true.
    + simpl. rewrite isptr_offset_val_zero by assumption. entailer!.
    + unfold field_compatible in *. simpl in *. intuition.
      * destruct p; try contradiction. clear -H2. unfold align_compatible in *.
        unfold heap_type.
        remember {|
          co_su := Struct;
          co_members := [(_spaces, tarray (Tstruct _space noattr) 12)];
          co_attr := noattr;
          co_sizeof := SPACE_STRUCT_SIZE * 12;
          co_alignof := WORD_SIZE;
          co_rank := 2;
          co_sizeof_pos := Zgeb0_ge0 (SPACE_STRUCT_SIZE * 12) eq_refl;
          co_alignof_two_p := prove_alignof_two_p WORD_SIZE eq_refl;
          co_sizeof_alignof :=
          prove_Zdivide WORD_SIZE (SPACE_STRUCT_SIZE * 12) eq_refl
        |} as c eqn:Heqnc.
        apply (align_compatible_rec_Tstruct cenv_cs _heap noattr c _); subst c.
        1: reflexivity. simpl co_members. intros. simpl in H.
        if_tac in H; inversion H. subst. clear H. inversion H0. subst z0.
        rewrite Z.add_0_r. apply H2.
      * red. simpl. left; reflexivity.
Qed.

Lemma heap_struct_rep_split_lt: forall sh l tinfo i1 i2,
    i1 < MAX_SPACES -> i2 < MAX_SPACES -> 0 <= i1 < i2 -> Zlength l = MAX_SPACES ->
    exists B,
      heap_struct_rep sh l (ti_heap_p tinfo) =
      data_at sh space_type (Znth i1 l) (space_address tinfo (Z.to_nat i1)) *
      data_at sh space_type (Znth i2 l) (space_address tinfo (Z.to_nat i2)) * B.
Proof.
  intros.
  exists (@data_at CompSpecs sh
                   (tarray space_type
                           (@Zlength (@reptype CompSpecs space_type)
                                     (@sublist (@reptype CompSpecs space_type)
                                               (i2 + 1) 12 l)))
                   (@sublist (@reptype CompSpecs space_type) (i2 + 1) 12 l)
                   (offset_val (SPACE_STRUCT_SIZE * (i2 + 1)) (ti_heap_p tinfo)) *
          @data_at CompSpecs sh (tarray space_type i1)
                   (@sublist (@reptype CompSpecs space_type) 0 i1 l)
                   (ti_heap_p tinfo) *
          @data_at CompSpecs sh (tarray space_type (i2 - i1 - 1))
                   (@sublist (@reptype CompSpecs space_type) (i1 + 1) i2 l)
                   (offset_val (SPACE_STRUCT_SIZE * (i1 + 1)) (ti_heap_p tinfo))).
  rewrite heap_struct_rep_eq. rewrite (data_at_tarray_space sh 12 i1) by rep_lia.
  rewrite (sublist_next i1 12 l) by rep_lia.
  replace (12 - i1) with (Zlength (sublist (i1 + 1) 12 l) + 1) by
      (rewrite Zlength_sublist; rep_lia).
  rewrite data_at_tarray_split_1 by reflexivity. unfold space_address.
  rewrite Z2Nat.id by lia. rewrite sepcon_comm, !sepcon_assoc. f_equal.
  rewrite offset_offset_val. rewrite Z2Nat.id by lia.
  replace (SPACE_STRUCT_SIZE * i1 + sizeof space_type) with
      (SPACE_STRUCT_SIZE * (i1 + 1))%Z by
      (simpl sizeof; unfold SPACE_STRUCT_SIZE; rep_lia).
  assert (Zlength (sublist (i1 + 1) 12 l) = 11 - i1) by
      (rewrite Zlength_sublist; rep_lia). rewrite H3.
  rewrite (data_at_tarray_space sh (11 - i1) (i2 - i1 - 1)).
  3: rewrite H3; reflexivity. 2: rep_lia. rewrite !sublist_sublist by rep_lia.
  replace (0 + (i1 + 1)) with (i1 + 1) by lia.
  replace (i2 - i1 - 1 + (i1 + 1)) with i2 by lia.
  replace (11 - i1 - (i2 - i1 - 1)) with (12 - i2) by lia.
  replace (11 - i1 + (i1 + 1)) with 12 by lia.
  rewrite offset_offset_val, <- Z.mul_add_distr_l.
  replace (i1 + 1 + (i2 - i1 - 1)) with i2 by lia.
  rewrite (sublist_next i2 12 l) by rep_lia.
  replace (12 - i2) with (Zlength (sublist (i2 + 1) 12 l) + 1) by
      (rewrite Zlength_sublist; rep_lia).
  rewrite data_at_tarray_split_1 by reflexivity.
  rewrite sepcon_assoc, sepcon_comm, !sepcon_assoc. f_equal.
  rewrite <- !sepcon_assoc. rewrite offset_offset_val. simpl sizeof.
  do 4 f_equal. unfold SPACE_STRUCT_SIZE; rep_lia.
Qed.

Lemma heap_struct_rep_split: forall sh l tinfo i1 i2,
    0 <= i1 < MAX_SPACES -> 0 <= i2 < MAX_SPACES ->
    i1 <> i2 -> Zlength l = MAX_SPACES -> exists B,
        heap_struct_rep sh l (ti_heap_p tinfo) =
        data_at sh space_type (Znth i1 l) (space_address tinfo (Z.to_nat i1)) *
        data_at sh space_type (Znth i2 l) (space_address tinfo (Z.to_nat i2)) * B.
Proof.
  intros. destruct H, H0. destruct (Z_dec i1 i2) as [[? | ?] | ?]. 3: contradiction.
  - destruct (heap_struct_rep_split_lt sh l tinfo i1 i2) as [B ?]; try rep_lia.
    exists B. assumption.
  - destruct (heap_struct_rep_split_lt sh l tinfo i2 i1) as [B ?]; try rep_lia.
    exists B. rewrite H5. f_equal. rewrite sepcon_comm. reflexivity.
Qed.

Lemma thread_info_rep_ramif_stable: forall sh tinfo ti gen1 gen2,
    gen1 <> gen2 -> Z.of_nat gen1 < MAX_SPACES -> Z.of_nat gen2 < MAX_SPACES ->
    thread_info_rep sh tinfo ti |--
                         (space_struct_rep sh tinfo gen1 *
                          space_struct_rep sh tinfo gen2) *
    ((space_struct_rep sh tinfo gen1 * space_struct_rep sh tinfo gen2)
       -* thread_info_rep sh tinfo ti).
Proof.
  intros. unfold thread_info_rep.
  remember (@data_at
              CompSpecs sh thread_info_type
              (@pair val (prod val (prod val (list val))) Vundef
                     (@pair val (prod val (list val)) Vundef
                            (@pair val (list val)
                                   (ti_heap_p tinfo) (ti_args tinfo)))) ti) as P.
  remember (heap_rest_rep (ti_heap tinfo)) as Q.
  rewrite (sepcon_comm P), sepcon_assoc. remember (P * Q) as R.
  clear P HeqP Q HeqQ HeqR. remember (map space_tri (heap_spaces (ti_heap tinfo))).
  assert (0 <= Z.of_nat gen1 < MAX_SPACES) by rep_lia.
  assert (0 <= Z.of_nat gen2 < MAX_SPACES) by rep_lia.
  assert (Z.of_nat gen1 <> Z.of_nat gen2) by lia.
  assert (Zlength l = MAX_SPACES) by (subst; rewrite Zlength_map; apply heap_spaces__size).
  destruct (heap_struct_rep_split sh l tinfo _ _ H2 H3 H4 H5) as [B ?].
  rewrite H6, !Nat2Z.id.
  assert (forall i, 0 <= Z.of_nat i < MAX_SPACES ->
                    data_at sh space_type (Znth (Z.of_nat i) l)
                            (space_address tinfo i) = space_struct_rep sh tinfo i). {
    intros. unfold space_struct_rep. subst l. rewrite Zlength_map in H5.
    rewrite nth_space_Znth, Znth_map by rep_lia. reflexivity. }
  rewrite !H7 by rep_lia. rewrite (sepcon_assoc _ B R).
  cancel. apply wand_frame_intro.
Qed.

Lemma hsr_single_explicit: forall sh l tinfo i,
    0 <= i < MAX_SPACES -> Zlength l = MAX_SPACES ->
      heap_struct_rep sh l (ti_heap_p tinfo) =
      data_at sh space_type (Znth i l) (space_address tinfo (Z.to_nat i)) *
      (@data_at
         CompSpecs sh
         (tarray space_type
                 (@Zlength (@reptype CompSpecs space_type)
                           (@sublist (@reptype CompSpecs space_type) (i + 1) 12 l)))
         (@sublist (@reptype CompSpecs space_type) (i + 1) 12 l)
         (offset_val (@sizeof CompSpecs space_type)
                     (offset_val (SPACE_STRUCT_SIZE * i) (ti_heap_p tinfo))) *
       @data_at CompSpecs sh (tarray space_type i)
                (@sublist (@reptype CompSpecs space_type) 0 i l) (ti_heap_p tinfo)).
Proof.
  intros. rewrite heap_struct_rep_eq.
  rewrite (data_at_tarray_space sh 12 i) by rep_lia.
  rewrite (sublist_next i 12 l) by rep_lia.
  replace (12 - i) with (Zlength (sublist (i + 1) 12 l) + 1) by
      (rewrite Zlength_sublist; rep_lia).
  rewrite data_at_tarray_split_1 by reflexivity. unfold space_address.
  rewrite Z2Nat.id by lia. rewrite sepcon_comm, !sepcon_assoc. reflexivity.
Qed.

Lemma heap_struct_rep_split_single: forall sh l tinfo i,
    0 <= i < MAX_SPACES -> Zlength l = MAX_SPACES ->
    exists B,
      heap_struct_rep sh l (ti_heap_p tinfo) =
      data_at sh space_type (Znth i l) (space_address tinfo (Z.to_nat i)) * B.
Proof.
  intros.
  exists (@data_at
            CompSpecs sh
            (tarray space_type
                    (@Zlength (@reptype CompSpecs space_type)
                              (@sublist (@reptype CompSpecs space_type) (i + 1) 12 l)))
            (@sublist (@reptype CompSpecs space_type) (i + 1) 12 l)
            (offset_val (@sizeof CompSpecs space_type)
                        (offset_val (SPACE_STRUCT_SIZE * i) (ti_heap_p tinfo))) *
          @data_at CompSpecs sh (tarray space_type i)
                   (@sublist (@reptype CompSpecs space_type) 0 i l) (ti_heap_p tinfo)).
  erewrite hsr_single_explicit; eauto.
Qed.

Lemma thread_info_rep_ramif_stable_1: forall sh tinfo ti gen,
    Z.of_nat gen < MAX_SPACES ->
    thread_info_rep sh tinfo ti |--
                    space_struct_rep sh tinfo gen *
    (space_struct_rep sh tinfo gen -* thread_info_rep sh tinfo ti).
Proof.
  intros. unfold thread_info_rep.
  remember (@data_at
              CompSpecs sh thread_info_type
              (@pair val (prod val (prod val (list val))) Vundef
                     (@pair val (prod val (list val)) Vundef
                            (@pair val (list val)
                                   (ti_heap_p tinfo) (ti_args tinfo)))) ti) as P.
  remember (heap_rest_rep (ti_heap tinfo)) as Q.
  rewrite (sepcon_comm P), sepcon_assoc. remember (P * Q) as R.
  clear P HeqP Q HeqQ HeqR. remember (map space_tri (heap_spaces (ti_heap tinfo))).
  assert (Zlength l = MAX_SPACES) by (subst; rewrite Zlength_map; apply heap_spaces__size).
  destruct (heap_struct_rep_split_single sh l tinfo (Z.of_nat gen))
    as [B ?]; try rep_lia; try assumption. rewrite H1, !Nat2Z.id. clear H1.
  assert (data_at sh space_type
                  (@Znth _ (@Inhabitant_reptype CompSpecs space_type)
                         (Z.of_nat gen) l) (space_address tinfo gen) =
          space_struct_rep sh tinfo gen). {
    intros. unfold space_struct_rep. subst l. rewrite Zlength_map in H0.
    rewrite Znth_map by rep_lia. rewrite nth_space_Znth. reflexivity. } rewrite !H1.
  rewrite (sepcon_assoc _ B R). cancel. apply wand_frame_intro.
Qed.

Lemma vertex_rep_reset: forall g i j x sh,
    vertex_rep sh (reset_graph j g) {| addr_gen := i ; addr_block := x |} = vertex_rep sh g {| addr_gen := i ; addr_block := x |}.
Proof.
  intros. unfold vertex_rep.
  rewrite heapgraph_block_ptr_reset, heapgraph_block_header__reset, heapgraph_block_cells_reset. reflexivity.
Qed.

Lemma generation_rep_reset_diff: forall (g: HeapGraph) i j,
    i <> j -> generation_rep (reset_graph j g) i = generation_rep g i.
Proof.
  intros. unfold generation_rep. rewrite <- !iter_sepcon_map.
  rewrite reset_heapgraph_generation_diff, reset_nth_sh_diff by assumption.
  apply iter_sepcon_func; intros. apply vertex_rep_reset.
Qed.

Lemma generation_rep_reset_same: forall (g: HeapGraph) i,
    heapgraph_has_gen g i -> generation_rep (reset_graph i g) i = emp.
Proof.
  intros. unfold generation_rep. rewrite <- !iter_sepcon_map.
  unfold heapgraph_generation, reset_graph at 1. simpl.
  rewrite reset_heapgraph_generation_info_same. simpl. reflexivity.
Qed.

Lemma graph_rep_reset: forall (g: HeapGraph) (gen: nat),
    heapgraph_has_gen g gen ->
    graph_rep g = graph_rep (reset_graph gen g) * generation_rep g gen.
Proof.
  intros. unfold graph_rep. simpl.
  rewrite reset_heapgraph_generation_info_length, remove_ve_glabel_unchanged.
  remember (length (generations (heapgraph_generations g))). pose proof H as HS. red in H.
  rewrite <- Heqn in H. destruct (nat_inc_list_Permutation_cons _ _ H) as [l ?].
  rewrite !(iter_sepcon_permutation _ H0). simpl.
  assert (iter_sepcon l (generation_rep (reset_graph gen g)) =
          iter_sepcon l (generation_rep g)). {
    apply iter_sepcon_func_strong. intros. rewrite generation_rep_reset_diff.
    1: reflexivity. pose proof (nat_inc_list_NoDup n).
    apply (Permutation_NoDup H0) in H2. apply NoDup_cons_2 in H2.
    intro. subst. contradiction. } rewrite H1. clear H1.
  rewrite generation_rep_reset_same by assumption.
  rewrite emp_sepcon, sepcon_comm. reflexivity.
Qed.

Lemma heap_rest_rep_reset: forall (g: HeapGraph) t_info gen,
    graph_thread_info_compatible g t_info -> heapgraph_has_gen g gen ->
    heap_rest_rep (ti_heap t_info) *
    generation_rep g gen |-- heap_rest_rep
                   (ti_heap (reset_nth_heap_thread_info gen t_info)).
Proof.
  intros. unfold heap_rest_rep. simpl.
  assert (gen < length (heap_spaces (ti_heap t_info)))%nat by
      (red in H0; destruct H as [_ [_ ?]]; lia).
  destruct (reset_nth_space_Permutation _ _ H1) as [l [? ?]].
  rewrite (iter_sepcon_permutation _ H3).
  rewrite (iter_sepcon_permutation _ H2).
  simpl. cancel.
  destruct (gt_gs_compatible _ _ H _ H0) as [H4 H5 H6 H7].
  simpl in *.
  fold (nth_space t_info gen). unfold space_rest_rep. unfold reset_space at 1.
  assert (isptr (space_base (nth_space t_info gen))) by
      (rewrite <- H4; apply generation_base__isptr).
  assert (space_base (nth_space t_info gen) <> nullval).
  {
    destruct (space_base (nth_space t_info gen)); try contradiction.
    intro H9; inversion H9.
  }
  simpl space_base. rewrite !if_false by assumption.
  sep_apply (generation_rep_data_at_ g gen H0).
  unfold heapgraph_generation_size. rewrite H6.
  unfold heapgraph_generation_base. rewrite if_true by assumption. rewrite H4.
  unfold heapgraph_generation_sh. rewrite H5.
  simpl.
  remember (nth_space t_info gen).
  rewrite isptr_offset_val_zero by assumption.
  replace (space_capacity s - 0) with (space_capacity s) by lia.
  rewrite <- data_at__tarray_value by apply (space_allocated__order s).
  cancel.
Qed.

Definition space_token_rep (sp: Space): mpred :=
  if Val.eq (space_base sp) nullval then emp
  else malloc_token Ews (tarray int_or_ptr_type (space_capacity sp)) (space_base sp).

Definition ti_token_rep (ti: thread_info): mpred :=
  malloc_token Ews heap_type (ti_heap_p ti) *
  iter_sepcon (heap_spaces (ti_heap ti)) space_token_rep.

Lemma ti_rel_token_the_same: forall (t1 t2: thread_info),
    thread_info_relation t1 t2 -> ti_token_rep t1 = ti_token_rep t2.
Proof.
  intros.
  destruct H as [H H0 H1].
  unfold ti_token_rep.
  rewrite H.
  f_equal.
  apply (iter_sepcon_pointwise_eq _ _ _ _ null_space null_space).
  - now rewrite <- !ZtoNat_Zlength, !heap_spaces__size.
  - intros.
    fold (nth_space t1 i).
    fold (nth_space t2 i).
    unfold gen_size in H0.
    unfold space_token_rep.
    now rewrite H0, H1.
Qed.

Lemma ti_token_rep_add: forall ti sp i (Hs: 0 <= i < MAX_SPACES),
    space_base (Znth i (heap_spaces (ti_heap ti))) = nullval ->
    space_base sp <> nullval ->
    malloc_token Ews (tarray int_or_ptr_type (space_capacity sp)) (space_base sp) *
    ti_token_rep ti |-- ti_token_rep (ti_add_new_space ti sp i Hs).
Proof.
  intros. unfold ti_token_rep. simpl. cancel. remember (heap_spaces (ti_heap ti)).
  rewrite <- (sublist_all (Zlength l) l) at 1 by lia.
  assert (Zlength l = MAX_SPACES) by (subst; rewrite heap_spaces__size; reflexivity).
  rewrite upd_Znth_unfold. 2: now rewrite H1.
  rewrite <- (sublist_rejoin 0 i) by lia. rewrite !iter_sepcon_app_sepcon. cancel.
  rewrite (sublist_next i) by lia. simpl. cancel. subst l.
  unfold space_token_rep at 1. rewrite H. rewrite if_true by reflexivity.
  unfold space_token_rep. rewrite if_false by assumption. cancel.
Qed.

Lemma heap_struct_rep_add: forall tinfo sh sp i (Hs: 0 <= i < MAX_SPACES),
    data_at sh space_type (space_tri sp) (space_address tinfo (Z.to_nat i)) *
    (@data_at
       CompSpecs sh
       (tarray space_type
               (@Zlength (@reptype CompSpecs space_type)
                         (@sublist (@reptype CompSpecs space_type) (i + 1) 12
                                   (map space_tri (heap_spaces (ti_heap tinfo))))))
       (@sublist (@reptype CompSpecs space_type) (i + 1) 12
                 (map space_tri (heap_spaces (ti_heap tinfo))))
       (offset_val (@sizeof CompSpecs space_type)
                   (offset_val (SPACE_STRUCT_SIZE * i) (ti_heap_p tinfo))) *
     @data_at CompSpecs sh (tarray space_type i)
              (@sublist (@reptype CompSpecs space_type) 0 i
                        (map space_tri (heap_spaces (ti_heap tinfo)))) (ti_heap_p tinfo)) =
    (heap_struct_rep
       sh (map space_tri (heap_spaces (ti_heap (ti_add_new_space tinfo sp i Hs))))
       (ti_heap_p (ti_add_new_space tinfo sp i Hs))).
Proof.
  intros. assert (Zlength (map space_tri (heap_spaces (ti_heap tinfo))) = MAX_SPACES) by
      (rewrite Zlength_map, heap_spaces__size; reflexivity).
  assert (Zlength (map space_tri (heap_spaces (ti_heap (ti_add_new_space tinfo sp i Hs)))) =
          MAX_SPACES) by (rewrite Zlength_map, heap_spaces__size; reflexivity).
  rewrite hsr_single_explicit with (i := i) by assumption. simpl.
  rewrite <- !upd_Znth_map, upd_Znth_same, ans_space_address by lia.
  rewrite sublist_upd_Znth_r; [| lia | pose proof Hs; rep_lia].
  rewrite sublist_upd_Znth_l by lia. reflexivity.
Qed.

Lemma heap_rest_rep_add: forall tinfo sp i (Hs: 0 <= i < MAX_SPACES),
    space_base (Znth i (heap_spaces (ti_heap tinfo))) = nullval ->
    heap_rest_rep (ti_heap tinfo) * space_rest_rep sp =
    heap_rest_rep (ti_heap (ti_add_new_space tinfo sp i Hs)).
Proof.
  intros. unfold heap_rest_rep. simpl. remember (heap_spaces (ti_heap tinfo)).
  rewrite <- (sublist_all (Zlength l) l) at 1 by lia.
  assert (Zlength l = MAX_SPACES) by (subst; rewrite heap_spaces__size; reflexivity).
  rewrite upd_Znth_unfold. 2: now rewrite H0.
  rewrite <- (sublist_rejoin 0 i) by lia. rewrite !iter_sepcon_app_sepcon.
  rewrite sepcon_assoc. f_equal. rewrite (sublist_next i) by lia. simpl.
  rewrite sepcon_emp, sepcon_comm. f_equal. subst l. unfold space_rest_rep at 1.
  rewrite if_true by assumption. rewrite emp_sepcon. reflexivity.
Qed.

Lemma vertex_rep_add: forall (g : HeapGraph) (gi : Generation) v sh,
    heapgraph_has_block g v -> copy_compatible g -> no_dangling_dst g ->
    vertex_rep sh g v = vertex_rep sh (heapgraph_generations_append g gi) v.
Proof.
  intros. unfold vertex_rep. rewrite heapgraph_generations_append__heapgraph_block_ptr; auto.
  rewrite <- heapgraph_block_header__heapgraph_generations_append, <- ang_heapgraph_block_cells_vals_old; auto.
Qed.

Lemma graph_rep_add: forall (g : HeapGraph) (gi : Generation),
    generation_block_count gi = O -> copy_compatible g -> no_dangling_dst g ->
    graph_rep g = graph_rep (heapgraph_generations_append g gi).
Proof.
  intros. unfold graph_rep. simpl. rewrite app_length. simpl.
  rewrite Nat.add_1_r, nat_inc_list_S, iter_sepcon_app_sepcon. simpl.
  unfold generation_rep at 3. unfold heapgraph_generation. simpl. rewrite app_nth2 by lia.
  replace (length (generations (heapgraph_generations g)) - length (generations (heapgraph_generations g)))%nat with O by lia.
  simpl. rewrite H. simpl. rewrite !sepcon_emp. apply iter_sepcon_func_strong. intros.
  rewrite nat_inc_list_In_iff in H2. unfold generation_rep. unfold heapgraph_generation_sh.
  rewrite !heapgraph_generation__heapgraph_generations_append__old by assumption. apply iter_sepcon_func_strong. intros v ?.
  rewrite in_map_iff in H3. destruct H3 as [idx [? ?]].
  rewrite nat_inc_list_In_iff in H4. apply vertex_rep_add; auto.
  split; subst; simpl; assumption.
Qed.
