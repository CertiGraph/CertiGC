From Coq Require Import Lists.List.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.heapgraph.block.cell.
From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.block.ptr.
From CertiGC Require Import model.heapgraph.block.field.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.has_block.
From CertiGC Require Import model.heapgraph.has_field.
From CertiGC Require Import model.heapgraph.remset.remset.
From CertiGC Require Import model.util.


Definition heapgraph_generation_can_copy 
  g from to : Prop := 
  generation_size from <= generation_size to - heapgraph_generation_size g to - heapgraph_remember_size g to.

Definition heapgraph_can_copy 
  (g : HeapGraph) : Prop := 
  forall n, heapgraph_has_gen g (S n) -> heapgraph_generation_can_copy g n (S n).

Definition heapgraph_can_copy_except 
  (g : HeapGraph) (gen : nat) : Prop :=
  forall n, n <> O -> n <> gen -> heapgraph_has_gen g n -> heapgraph_generation_can_copy g (pred n) n.

Lemma heapgraph_can_copy_except__O (g : HeapGraph) : heapgraph_can_copy g <-> heapgraph_can_copy_except g O.
Proof.
  (unfold heapgraph_can_copy, heapgraph_can_copy_except).
  split.
  + (intros H n Hn _ Hgn).
    (destruct n as [| n]; try easy).
    now apply H.
  + (intros H n Hn).
    specialize (H (S n)).
    now apply H.
Qed.

Lemma heapgraph_can_copy__complete 
  (g : HeapGraph) (i : nat) 
  (Hg : heapgraph_can_copy_except g (S i)) 
  (Hi : heapgraph_generation_can_copy g i (S i)) : 
  heapgraph_can_copy g.
Proof.
  (unfold heapgraph_can_copy_except in Hg).
  (unfold heapgraph_can_copy in *).
  (intros n Hn).
  (destruct (Nat.eq_dec n i) as [E| Hn__i]).
  + now subst.
  + specialize (Hg (S n)).
    (apply Hg; now try congruence).
Qed.

Lemma stcte_add :
  forall g gi i,
  generation_block_count gi = O ->
  generation_remember_count gi = O ->
  heapgraph_can_copy_except g i ->
  heapgraph_can_copy_except (heapgraph_generations_append g gi) i.
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


Definition graph_gen_clear 
  (g : HeapGraph) (gen : nat) : Prop := 
  generation_block_count (heapgraph_generation g gen) = O.

Definition firstn_gen_clear (g : HeapGraph) (n : nat) : Prop := forall i, (i < n)%nat -> graph_gen_clear g i.

Lemma firstn_gen_clear_add :
  forall g gi i,
  heapgraph_has_gen g (Z.to_nat i) ->
  firstn_gen_clear g (Z.to_nat i) -> firstn_gen_clear (heapgraph_generations_append g gi) (Z.to_nat i).
Proof.
  (intros).
  (unfold firstn_gen_clear, graph_gen_clear in *).
  (intros).
  specialize (H0 _ H1).
  (rewrite heapgraph_generation__heapgraph_generations_append__old; auto).
  (unfold heapgraph_has_gen in *).
  lia.
Qed.


Definition gen2gen_no_edge 
  (g : HeapGraph) (gen1 gen2 : nat) : Prop :=
  forall vidx eidx,
  let e := {| field_addr := {| addr_gen := gen1; addr_block := vidx |}; field_index := eidx |} in
  heapgraph_has_field g e -> addr_gen (dst g e) <> gen2.

Definition no_edge2gen 
  (g : HeapGraph) (gen : nat) : Prop := 
  forall another, another <> gen -> gen2gen_no_edge g another gen.

Definition no_backward_edge 
  (g : HeapGraph) : Prop := 
  forall gen1 gen2, (gen1 > gen2)%nat -> gen2gen_no_edge g gen1 gen2.


Lemma fgc_nbe_no_edge2gen 
  (g : HeapGraph) (n : nat) 
  (Hn : firstn_gen_clear g n) 
  (Hg : no_backward_edge g) : 
  no_edge2gen g n.
Proof.
  (intros m Hm).
  (destruct (lt_eq_lt_dec m n) as [[Hmn| Hmn]| Hmn]; try easy).
  + (intros vidx eidx f Hf En).
    subst f.
    (pose proof (heapgraph_has_block__has_index (heapgraph_has_field__has_block Hf)) as F).
    specialize (Hn _ Hmn).
    (red in Hn, F).
    (simpl in F).
    (rewrite Hn in F).
    lia.
  + (apply Hg).
    lia.
Qed.

Lemma no_backward_edge_add :
  forall g gi,
  generation_block_count gi = O ->
  no_backward_edge g ->
  no_backward_edge (heapgraph_generations_append g gi).
Proof.
  (intros).
  (unfold no_backward_edge, gen2gen_no_edge in *).
  (intros).
  (simpl).
  (pose proof (heapgraph_has_field__in H2) as Hfield).
  (rewrite <- ang_heapgraph_block_fields in Hfield).
  (pose proof (heapgraph_has_field__has_block H2) as Hblock).
  (apply heapgraph_generations_append__heapgraph_has_block_inv in Hblock; auto).
  (apply H0; auto).
  (split; simpl; auto).
Qed.


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
  intro v.
  specialize (Hg v).
  dintuition idtac ; simpl in *.
Qed.


Definition no_dangling_dst 
  (g : HeapGraph) : Prop :=
  forall v, heapgraph_has_block g v -> forall e, In e (heapgraph_block_fields g v) -> heapgraph_has_block g (dst g e).

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


Lemma lgd_no_dangling_dst :
  forall g e v', heapgraph_has_block g v' -> no_dangling_dst g -> no_dangling_dst (labeledgraph_gen_dst g e v').
Proof.
  (intros).
  (unfold no_dangling_dst in *).
  (intros).
  (rewrite <- lgd_heapgraph_has_block).
  (simpl).
  (unfold updateEdgeFunc).
  if_tac ; try easy.
  apply (H0 v) ; try easy.
  (destruct H1; simpl in *; now constructor).
Qed.


Lemma mfv_unmarked_all_is_ptr_or_int :
  forall (g : HeapGraph) (v : Addr),
  no_dangling_dst g ->
  heapgraph_has_block g v ->
  Forall is_pointer_or_integer (map (heapgraph_cell_val g) (heapgraph_block_cells g v)).
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

Lemma mfv_all_is_ptr_or_int :
  forall g v,
  copy_compatible g ->
  no_dangling_dst g ->
  heapgraph_has_block g v ->
  Forall is_pointer_or_integer (heapgraph_block_cells_vals g v).
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
