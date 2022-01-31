From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.util.

From CertiGC Require Export model.heapgraph.backward_edge.
From CertiGC Require Export model.heapgraph.block.block.
From CertiGC Require Export model.heapgraph.block.block_rep.
From CertiGC Require Export model.heapgraph.block.cell.
From CertiGC Require Export model.heapgraph.block.field.
From CertiGC Require Export model.heapgraph.can_copy.
From CertiGC Require Export model.heapgraph.field_pairs.
From CertiGC Require Export model.heapgraph.generation.empty.
From CertiGC Require Export model.heapgraph.generation.generation.
From CertiGC Require Export model.heapgraph.has_block.
From CertiGC Require Export model.heapgraph.has_field.
From CertiGC Require Export model.heapgraph.remset.remset.
From CertiGC Require Export model.heapgraph.roots.


Import ListNotations.


Definition copy_compatible 
  (g : HeapGraph) : Prop :=
  forall v,
  heapgraph_has_block g v ->
  (heapgraph_block g v).(block_mark) = true ->
  heapgraph_has_block g (heapgraph_block g v).(block_copied_vertex) /\
  addr_gen v <> addr_gen (heapgraph_block g v).(block_copied_vertex).

Lemma lgd_copy_compatible 
  (g : HeapGraph) (v' : Addr) 
  (e : Field) (Hg : copy_compatible g) : 
  copy_compatible (labeledgraph_gen_dst g e v').
Proof.
  unfold copy_compatible in *.
  intro v. specialize (Hg v) as Hv. clear Hg.
  dintuition idtac ; simpl in *.
Qed.


Definition no_dangling_dst 
  (g : HeapGraph) : Prop :=
  forall v, heapgraph_has_block g v -> forall e, In e (heapgraph_block_fields g v) -> heapgraph_has_block g (dst g e).



Lemma mfv_unmarked_all_is_ptr_or_int :
  forall (g : HeapGraph) (v : Addr),
  no_dangling_dst g ->
  heapgraph_has_block g v -> Forall is_pointer_or_integer (map (heapgraph_cell_val g) (heapgraph_block_cells g v)).
Proof.
  (intros).
  (rewrite Forall_forall).
  (intros f ?).
  (apply list_in_map_inv in H1).
  (destruct H1 as [x [? ?]]).
  (destruct x as [[?| ?]| ?]; simpl in H1; subst).
  - (unfold odd_Z2val).
    exact I.
  - (destruct g0).
    exact I.
  - (apply isptr_is_pointer_or_integer).
    (unfold heapgraph_block_ptr).
    (rewrite isptr_offset_val).
    (apply heapgraph_generation_base__isptr).
    (apply filter_sum_right_In_iff, H in H2; [ destruct H2 |  ]; assumption).
Qed.


Definition heapgraph_generation_is_unmarked 
  (g : HeapGraph) (gen : nat) : Prop :=
  heapgraph_has_gen g gen ->
  forall idx,
  heapgraph_generation_has_index g gen idx ->
  (heapgraph_block g {| addr_gen := gen; addr_block := idx |}).(block_mark) = false.

Definition graph_unmarked 
  (g : HeapGraph) : Prop := 
  forall v, heapgraph_has_block g v -> block_mark (heapgraph_block g v) = false.

Lemma graph_heapgraph_generation_is_unmarked_iff 
  (g : HeapGraph) : graph_unmarked g <-> (forall gen, heapgraph_generation_is_unmarked g gen).
Proof.
  (unfold graph_unmarked, heapgraph_generation_is_unmarked).
  (split; intros).
  + (apply H).
    now refine {| heapgraph_has_block__has_gen := _; heapgraph_has_block__has_index := _ |}.
  + (pose proof (heapgraph_has_block__has_gen H0) as Hgen).
    (pose proof (heapgraph_has_block__has_index H0) as Hindex).
    (destruct v as [gen idx]).
    now apply H.
Qed.

Lemma graph_unmarked_copy_compatible : forall g, graph_unmarked g -> copy_compatible g.
Proof.
  (intros).
  (red in H |- *).
  (intros).
  (apply H in H0).
  (rewrite H0 in H1).
  (inversion H1).
Qed.

Lemma mfv_all_is_ptr_or_int :
  forall g v,
  copy_compatible g ->
  no_dangling_dst g -> heapgraph_has_block g v -> Forall is_pointer_or_integer (heapgraph_block_cells_vals g v).
Proof.
  (intros).
  (rewrite Forall_forall).
  (intros f ?).
  (unfold heapgraph_block_cells_vals in H2).
  (pose proof (mfv_unmarked_all_is_ptr_or_int _ _ H0 H1)).
  (rewrite Forall_forall in H3).
  specialize (H3 f).
  (destruct (block_mark (heapgraph_block g v)) eqn:?).
  2: (apply H3; assumption).
  (simpl in H2).
  (destruct H2).
  2: (apply H3, In_tail; assumption).
  subst f.
  (unfold heapgraph_block_ptr).
  (apply isptr_is_pointer_or_integer).
  (rewrite isptr_offset_val).
  (apply heapgraph_generation_base__isptr, (proj1 (H _ H1 Heqb))).
Qed.

Definition unmarked_gen_size 
  (g : HeapGraph) (gen : nat) :=
  fold_left (heapgraph_block_size_accum g gen)
    (filter (fun i => negb (heapgraph_block g {| addr_gen := gen; addr_block := i |}).(block_mark))
       (nat_inc_list (generation_block_count (heapgraph_generation g gen)))) 0.

Lemma unmarked_gen_size_le : forall g n, unmarked_gen_size g n <= heapgraph_generation_size g n.
Proof.
  (intros g gen).
  (unfold unmarked_gen_size, heapgraph_generation_size, heapgraph_block_size_prev).
  (apply fold_left_mono_filter;
    [ intros; rewrite Z.le_lteq; left; apply heapgraph_block_size_accum__mono
    | apply heapgraph_block_size_accum__comm ]).
Qed.

Lemma single_unmarked_le :
  forall g v,
  heapgraph_has_block g v ->
  block_mark (heapgraph_block g v) = false -> heapgraph_block_size g v <= unmarked_gen_size g (addr_gen v).
Proof.
  (intros).
  (unfold unmarked_gen_size).
  (remember
    (filter (fun i : nat => negb (block_mark (heapgraph_block g {| addr_gen := addr_gen v; addr_block := i |})))
       (nat_inc_list (generation_block_count (heapgraph_generation g (addr_gen v)))))).
  (assert (In (addr_block v) l)).
  {
    subst l.
    (rewrite filter_In).
    split.
    - (rewrite nat_inc_list_In_iff).
      now apply heapgraph_has_block__has_index.
    - (destruct v; simpl).
      (rewrite negb_true_iff).
      (apply H0).
  }
  (apply In_Permutation_cons in H1).
  (destruct H1 as [l1 ?]).
  symmetry in H1.
  (change (addr_block v :: l1) with ([addr_block v] ++ l1) in H1).
  (transitivity (fold_left (heapgraph_block_size_accum g (addr_gen v)) [addr_block v] 0)).
  - (simpl).
    (destruct v; simpl).
    (apply Z.le_refl).
  - (apply (fold_left_Z_mono (heapgraph_block_size_accum g (addr_gen v)) [addr_block v] l1 l 0);
      [ intros; apply Z.le_lteq; left; apply heapgraph_block_size_accum__mono
      | apply heapgraph_block_size_accum__comm
      | apply H1 ]).
Qed.


Lemma ang_heapgraph_block_cells_vals_old :
  forall g gi v,
  heapgraph_has_block g v ->
  copy_compatible g ->
  no_dangling_dst g ->
  heapgraph_block_cells_vals g v = heapgraph_block_cells_vals (heapgraph_generations_append g gi) v.
Proof.
  (intros).
  (unfold heapgraph_block_cells_vals).
  (simpl).
  (assert
    (map (heapgraph_cell_val g) (heapgraph_block_cells g v) =
     map (heapgraph_cell_val (heapgraph_generations_append g gi))
       (heapgraph_block_cells (heapgraph_generations_append g gi) v))).
  {
    (unfold heapgraph_block_cells).
    (simpl).
    (apply map_ext_in).
    (intros).
    (destruct a; [ destruct s |  ]; simpl; auto).
    (rewrite heapgraph_generations_append__heapgraph_block_ptr; auto).
    (red in H1).
    (apply (H1 v); auto).
    (unfold heapgraph_block_fields).
    (rewrite <- filter_sum_right_In_iff).
    assumption.
  }
  (rewrite <- H2).
  (destruct (block_mark (heapgraph_block g v)) eqn:?; auto).
  f_equal.
  (rewrite heapgraph_generations_append__heapgraph_block_ptr; auto).
  (destruct (H0 _ H Heqb)).
  assumption.
Qed.



Lemma stcte_add :
  forall g gi i,
  generation_block_count gi = O ->
  generation_remember_count gi = O ->
  heapgraph_can_copy_except g i -> heapgraph_can_copy_except (heapgraph_generations_append g gi) i.
Proof.
  (intros).
  rename H0 into HH.
  rename H1 into H0.
  (unfold heapgraph_can_copy_except in *).
  (intros).
  (rewrite heapgraph_has_gen__heapgraph_generations_append in H3).
  (destruct H3).
  - specialize (H0 _ H1 H2 H3).
    (unfold heapgraph_generation_can_copy in *).
    rewrite heapgraph_remember_size__heapgraph_generations_append__old ; try easy.
    now rewrite <- ang_graph_gen_size_old.
  - (unfold heapgraph_generation_can_copy).
    (simpl).
    (unfold heapgraph_generation_size, heapgraph_remember_size).
    (rewrite H3  at 4).
    (rewrite heapgraph_generation__heapgraph_generations_append__new, H).
    unfold heapgraph_generations_append at 2.
    unfold heapgraph_generation at 1.
    simpl.
    rewrite app_nth2 ; try lia.
    replace
      (n - Datatypes.length (generations (heapgraph_generations g)))%nat
      with O
      by (subst n ; lia).
    simpl.
    rewrite HH.
    simpl.
    (rewrite Z.sub_0_r).
    (unfold heapgraph_block_size_prev).
    (simpl).
    (destruct n).
    1: contradiction.
    (simpl).
    (rewrite Z.sub_0_r).
    pose proof (ngs_0_lt (S n)).
    pose proof (generation_size_le_S n).
    pose proof (heapgraph_remember_size__nonneg (heapgraph_generations_append g gi) (S n)).
    lia.
Qed.

Lemma graph_unmarked_add :
  forall g gi, generation_block_count gi = O -> graph_unmarked g -> graph_unmarked (heapgraph_generations_append g gi).
Proof.
  (intros).
  (unfold graph_unmarked in *).
  (intros).
  (apply heapgraph_generations_append__heapgraph_has_block_inv in H1; auto).
  (simpl).
  (apply H0).
  assumption.
Qed.




Lemma no_dangling_dst_add :
  forall g gi,
  generation_block_count gi = O -> no_dangling_dst g -> no_dangling_dst (heapgraph_generations_append g gi).
Proof.
  (intros).
  (unfold no_dangling_dst in *).
  (intros).
  (simpl).
  (apply heapgraph_generations_append__heapgraph_has_block_inv in H1; auto).
  (rewrite <- ang_heapgraph_block_fields in H2).
  (apply heapgraph_generations_append__heapgraph_has_block, (H0 v); auto).
Qed.


Lemma lgd_graph_has_gen : forall g e v x, heapgraph_has_gen (labeledgraph_gen_dst g e v) x <-> heapgraph_has_gen g x.
Proof.
  (intros; unfold heapgraph_has_gen; intuition idtac).
Qed.


Lemma lgd_block_mark_eq :
  forall (g : HeapGraph) e (v v' : Addr),
  block_mark (heapgraph_block g v) = block_mark (heapgraph_block (labeledgraph_gen_dst g e v') v).
Proof.
  reflexivity.
Qed.



Definition closure_has_index 
  (g : HeapGraph) (gen index : nat) := 
  (index <= generation_block_count (heapgraph_generation g gen))%nat.

Definition closure_has_v 
  (g : HeapGraph) (v : Addr) : Prop :=
  heapgraph_has_gen g (addr_gen v) /\ closure_has_index g (addr_gen v) (addr_block v).

Lemma heapgraph_has_block_in_closure (g : HeapGraph) (v : Addr) (Hv : heapgraph_has_block g v) : closure_has_v g v.
Proof.
  (destruct v as [gen index]).
  (destruct Hv).
  (unfold closure_has_v, closure_has_index).
  intuition.
Qed.

Lemma lgd_no_dangling_dst :
  forall g e v', heapgraph_has_block g v' -> no_dangling_dst g -> no_dangling_dst (labeledgraph_gen_dst g e v').
Proof.
  (intros).
  (unfold no_dangling_dst in *).
  (intros).
  (rewrite <- lgd_heapgraph_has_block).
  (simpl).
  (unfold updateEdgeFunc; if_tac; [ assumption | apply (H0 v) ]; try assumption).
  (destruct H1; simpl in *; now constructor).
Qed.

Lemma lgd_no_dangling_dst_copied_vert :
  forall g e v,
  copy_compatible g ->
  heapgraph_has_block g v ->
  block_mark (heapgraph_block g v) = true ->
  no_dangling_dst g -> no_dangling_dst (labeledgraph_gen_dst g e (block_copied_vertex (heapgraph_block g v))).
Proof.
  (intros).
  (assert (heapgraph_has_block g (block_copied_vertex (heapgraph_block g v))) by apply (H v H0 H1)).
  (apply lgd_no_dangling_dst; assumption).
Qed.

Lemma block_mark__false_prep64 :
  forall z,
  0 <= z < two_p (8 * 8) ->
  Int64.and (Int64.repr z) (Int64.repr 255) =
  Int64.sub (Int64.repr z) (Int64.mul (Int64.repr (z / two_p 8)) (Int64.repr (two_p 8))).
Proof.
  (intros).
  replace (Int64.repr 255) with (Int64.sub (Int64.repr 256) Int64.one) by now vm_compute.
  (rewrite <- (Int64.modu_and _ _ (Int64.repr 8)) by now vm_compute).
  (rewrite Int64.modu_divu by (vm_compute; intro S; inversion S)).
  (rewrite (Int64.divu_pow2 _ _ (Int64.repr 8)) by now vm_compute).
  (rewrite (Int64.mul_pow2 _ _ (Int64.repr 8)) by now vm_compute).
  (rewrite Int64.shru_div_two_p, !Int64.unsigned_repr; [  | rep_lia |  ]).
  - (rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia).
    easy.
  - (simpl Z.mul in H).
    (unfold Int64.max_unsigned, Int64.modulus).
    (unfold Int64.wordsize, Wordsize_64.wordsize).
    (rewrite two_power_nat_two_p).
    (simpl Z.of_nat).
    lia.
Qed.

Lemma block_mark__false_prep32 :
  forall z,
  0 <= z < two_p (4 * 8) ->
  Int.and (Int.repr z) (Int.repr 255) = Int.sub (Int.repr z) (Int.mul (Int.repr (z / two_p 8)) (Int.repr (two_p 8))).
Proof.
  (intros).
  replace (Int.repr 255) with (Int.sub (Int.repr 256) Int.one) by now vm_compute.
  (rewrite <- (Int.modu_and _ _ (Int.repr 8)) by now vm_compute).
  (rewrite Int.modu_divu by (vm_compute; intro S; inversion S)).
  (rewrite (Int.divu_pow2 _ _ (Int.repr 8)) by now vm_compute).
  (rewrite (Int.mul_pow2 _ _ (Int.repr 8)) by now vm_compute).
  (rewrite Int.shru_div_two_p, !Int.unsigned_repr; [  | rep_lia |  ]).
  - (rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia).
    easy.
  - (simpl Z.mul in H).
    (unfold Int.max_unsigned, Int.modulus).
    (unfold Int.wordsize, Wordsize_32.wordsize).
    (rewrite two_power_nat_two_p).
    (simpl Z.of_nat).
    lia.
Qed.

Lemma block_mark__false :
  forall g v,
  block_mark (heapgraph_block g v) = false ->
  if Archi.ptr64
  then
   Int64.and (Int64.repr (heapgraph_block_header g v)) (Int64.repr 255) = Int64.repr (block_tag (heapgraph_block g v))
  else Int.and (Int.repr (heapgraph_block_header g v)) (Int.repr 255) = Int.repr (block_tag (heapgraph_block g v)).
Proof.
  (intros).
  (cbv delta [Archi.ptr64]).
  (simpl).
  (first [ rewrite block_mark__false_prep32 | rewrite block_mark__false_prep64 ]).
  2: (apply heapgraph_block_header__range).
  (unfold heapgraph_block_header in *).
  (remember (heapgraph_block g v) as r eqn:E ).
  clear E.
  (rewrite H, !Zbits.Zshiftl_mul_two_p in * by lia).
  (rewrite <- Z.add_assoc).
  replace (block_color r * two_p 8 + Zlength (block_fields r) * two_p 10) with
   ((block_color r + Zlength (block_fields r) * two_p 2) * two_p 8)
   by (rewrite Z.mul_add_distr_r, <- Z.mul_assoc, <- two_p_is_exp by lia; reflexivity).
  (rewrite Z.div_add by (vm_compute; intros S; inversion S)).
  (assert (block_tag r / two_p 8 = 0) by apply Z.div_small, block_tag__range).
  (rewrite H0, Z.add_0_l).
  (first [ rewrite mul_repr, sub_repr | rewrite mul64_repr, sub64_repr ]).
  now rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
Qed.

