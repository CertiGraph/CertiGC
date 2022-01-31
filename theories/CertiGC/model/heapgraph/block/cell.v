From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.block.ptr.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.util.

Local Open Scope Z.


Definition Cell : Type := Z + GC_Pointer + Field.

#[global]Instance Cell_inhabitant : (Inhabitant Cell) := (inl (inl Z.zero)).

Definition heapgraph_cell_val 
  (g : HeapGraph) (fd : Cell) : val :=
  match fd with
  | inl (inl z) => odd_Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr e => heapgraph_block_ptr g (dst g e)
  end.

Fixpoint fields_to_cells 
(l_raw : list FieldValue) 
(v : Addr) (n : nat) : 
list Cell :=
  match l_raw with
  | nil => nil
  | Some (inl z) :: l => inl (inl z) :: fields_to_cells l v (n + 1)
  | Some (inr ptr) :: l => inl (inr ptr) :: fields_to_cells l v (n + 1)
  | None :: l => inr {| field_addr := v; field_index := n |} :: fields_to_cells l v (n + 1)
  end.

Lemma fields_to_cells__in 
  (l : list FieldValue) 
  (v : Addr) (n : nat) 
  (e : Field) (He : In (inr e) (fields_to_cells l v n)) : 
  exists s, e = {| field_addr := v; field_index := s |}.
Proof.
  (revert v n e He; induction l as [| f l IHl]; intros v n e He; simpl in *; try easy).
  (destruct f as [f| ]).
  + (destruct f as [f| f]).
    all: (destruct He as [He| He]; now try apply IHl with (n + 1)%nat).
  + (destruct He as [He| He]).
    - exists n.
      congruence.
    - now apply IHl with (n + 1)%nat.
Qed.

Lemma fields_to_cells__length (l : list FieldValue) (v : Addr) (n : nat) : length (fields_to_cells l v n) = length l.
Proof.
  (revert n; induction l as [| f l IHl]; intro n; simpl; try easy).
  (destruct f as [f| ]; try destruct f as [f| f]; simpl).
  all: now rewrite IHl.
Qed.

Lemma fields_to_cells__Zlength (l : list FieldValue) (v : Addr) (n : nat) : Zlength (fields_to_cells l v n) = Zlength l.
Proof.
  now rewrite !Zlength_correct, fields_to_cells__length.
Qed.

Lemma fields_to_cells__nth 
  (n : nat) (l_raw : list FieldValue) 
  (i : nat) (v : Addr) 
  (e : Field) (Hn : 0 <= Z.of_nat n < Zlength l_raw) 
  (He : nth n (fields_to_cells l_raw v i) Cell_inhabitant = inr e) : 
  e = {| field_addr := v; field_index := n + i |}.
Proof.
  (revert l_raw i v e Hn He; induction n as [| n' IHn']; intros l_raw i v e Hn He).
  - (destruct l_raw as [| r l_raw]; try inversion He).
    (destruct r; [ destruct s |  ]; simpl in He; now inversion He).
  - (destruct l_raw as [| r l_raw]; try inversion He).
    replace (S n' + i)%nat with (n' + S i)%nat by lia.
    specialize (IHn' l_raw (S i) v e).
    (assert (Hn' : 0 <= Z.of_nat n' < Zlength l_raw)).
    {
      (rewrite Zlength_cons, Nat2Z.inj_succ in Hn).
      lia.
    }
    (assert (He' : nth n' (fields_to_cells l_raw v (S i)) Cell_inhabitant = inr e)).
    {
      (destruct r; [ destruct s |  ]; simpl in He; now replace (i + 1)%nat with (S i) in He by lia).
    }
    (destruct r; [ destruct s |  ]; simpl; now apply IHn').
Qed.

Lemma fields_to_cells__n_doesnt_matter 
  (i : nat) (l : list FieldValue) 
  (v : Addr) (n m : nat) 
  (gcptr : GC_Pointer) 
  (Hn : nth i (fields_to_cells l v n) Cell_inhabitant = inl (inr gcptr)) :
  nth i (fields_to_cells l v m) Cell_inhabitant = inl (inr gcptr).
Proof.
  (intros).
  (unfold fields_to_cells in *).
  generalize dependent i.
  generalize dependent n.
  generalize dependent m.
  (induction l).
  + (intros; assumption).
  + (induction i).
    - (destruct a; [ destruct s |  ]; simpl; intros; now try inversion Hn).
    - (destruct a; [ destruct s |  ]; simpl; intro; now apply IHl with (m := (m + 1)%nat) in Hn).
Qed.

Lemma fields_to_cells__id 
  (l : list FieldValue) 
  (v : Addr) (n : Z) 
  (gcptr : GC_Pointer) 
  (Hn : 0 <= n < Zlength l) 
  (Hgcptr : Znth n (fields_to_cells l v 0) = inl (inr gcptr)) : 
  Znth n l = Some (inr gcptr).
Proof.
  (rewrite <- nth_Znth; rewrite <- nth_Znth in Hgcptr; [ idtac | rewrite Zlength_correct in *.. ];
    try rewrite fields_to_cells__length; 
    [ idtac | assumption.. ]).
  generalize dependent n.
  (induction l).
  - (intros).
    (rewrite nth_Znth in Hgcptr; try assumption).
    (unfold fields_to_cells in Hgcptr; rewrite Znth_nil in Hgcptr; inversion Hgcptr).
  - intro n.
    (induction (Z.to_nat n) eqn:?).
    + (intros).
      (destruct a; [ destruct s |  ]; simpl in *; try inversion Hgcptr; try reflexivity).
    + (intros).
      (simpl in *).
      clear IHn0.
      replace n0 with (Z.to_nat (Z.of_nat n0)) by apply Nat2Z.id.
      (assert (Hn0 : 0 <= Z.of_nat n0 < Zlength l)).
      {
        (split; try lia).
        (apply Zsucc_lt_reg).
        (rewrite Zlength_cons in Hn).
        (rewrite <- Nat2Z.inj_succ, <- Heqn0, Z2Nat.id; lia).
      }
      (destruct a; [ destruct s |  ]; simpl in Hgcptr; apply IHl; try easy).
      all: (apply fields_to_cells__n_doesnt_matter with (n := 1%nat); now rewrite Nat2Z.id).
Qed.


Definition heapgraph_block_cells 
  (g : HeapGraph) (v : Addr) : 
  list Cell := fields_to_cells (heapgraph_block g v).(block_fields) v O.


Lemma heapgraph_block_cells_eq_length :
  forall g v, Zlength (heapgraph_block_cells g v) = Zlength (block_fields (heapgraph_block g v)).
Proof.
  (unfold heapgraph_block_cells).
  (intros).
  (rewrite !Zlength_correct, fields_to_cells__length).
  reflexivity.
Qed.

Lemma lgd_heapgraph_block_cells_eq :
  forall (g : HeapGraph) (v v' : Addr) e,
  heapgraph_block_cells (labeledgraph_gen_dst g e v') v = heapgraph_block_cells g v.
Proof.
  reflexivity.
Qed.


Lemma heapgraph_block_cells_Znth_edge :
  forall g v n e,
  0 <= n < Zlength (block_fields (heapgraph_block g v)) ->
  Znth n (heapgraph_block_cells g v) = inr e -> e = {| field_addr := v; field_index := Z.to_nat n |}.
Proof.
  (intros).
  (rewrite <- nth_Znth in H0).
  2: (rewrite heapgraph_block_cells_eq_length; assumption).
  (apply fields_to_cells__nth in H0).
  - now rewrite Nat.add_0_r in H0.
  - now rewrite Z2Nat.id.
Qed.

Lemma heapgraph_block_cells_edge_unique :
  forall g e v1 v2 n m,
  0 <= n < Zlength (heapgraph_block_cells g v1) ->
  0 <= m < Zlength (heapgraph_block_cells g v2) ->
  Znth n (heapgraph_block_cells g v1) = inr e -> Znth m (heapgraph_block_cells g v2) = inr e -> n = m /\ v1 = v2.
Proof.
  (intros).
  (unfold heapgraph_block_cells in *).
  (rewrite fields_to_cells__Zlength in *).
  (assert (0 <= Z.of_nat (Z.to_nat n) < Zlength (block_fields (heapgraph_block g v1))) by
    (destruct H; split; rewrite Z2Nat.id; assumption)).
  (rewrite <- nth_Znth in H1 by (rewrite fields_to_cells__Zlength; assumption)).
  (assert (0 <= Z.of_nat (Z.to_nat m) < Zlength (block_fields (heapgraph_block g v2))) by
    (destruct H0; split; rewrite Z2Nat.id; assumption)).
  (rewrite <- nth_Znth in H2 by (rewrite fields_to_cells__Zlength; assumption)).
  (pose proof (fields_to_cells__nth (Z.to_nat n) (block_fields (heapgraph_block g v1)) 0 v1 e H3 H1)).
  (pose proof (fields_to_cells__nth (Z.to_nat m) (block_fields (heapgraph_block g v2)) 0 v2 e H4 H2)).
  (rewrite H5 in H6).
  (inversion H6).
  (rewrite Nat.add_cancel_r, Z2Nat.inj_iff in H9 by lia).
  (split; [ assumption | reflexivity ]).
Qed.

Definition heapgraph_block_cells_vals 
  (g : HeapGraph) (v : Addr) : 
  list val :=
  let vb := heapgraph_block g v in
  let original_fields_val := map (heapgraph_cell_val g) (heapgraph_block_cells g v) in
  if vb.(block_mark)
  then heapgraph_block_ptr g vb.(block_copied_vertex) :: tl original_fields_val
  else original_fields_val.

Lemma fields_eq_length :
  forall g v, Zlength (heapgraph_block_cells_vals g v) = Zlength (block_fields (heapgraph_block g v)).
Proof.
  (intros).
  (rewrite !Zlength_correct).
  f_equal.
  (unfold heapgraph_block_cells_vals, heapgraph_block_cells).
  (destruct (block_mark (heapgraph_block g v))).
  - (destruct (block_fields_head__cons (heapgraph_block g v)) as [r [l [? ?]]]).
    (rewrite H; simpl; destruct r; [ destruct s |  ]; simpl; rewrite map_length, fields_to_cells__length; reflexivity).
  - (rewrite map_length, fields_to_cells__length).
    reflexivity.
Qed.

Lemma heapgraph_block_cells_the_same :
  forall (g1 g2 : HeapGraph) v,
  (forall e, dst g1 e = dst g2 e) ->
  (forall v, heapgraph_block g1 v = heapgraph_block g2 v) ->
  map generation_base (heapgraph_generations g1).(generations) =
  map generation_base (heapgraph_generations g2).(generations) ->
  heapgraph_block_cells_vals g1 v = heapgraph_block_cells_vals g2 v.
Proof.
  (intros).
  (unfold heapgraph_block_cells_vals, heapgraph_block_cells).
  (remember O).
  clear Heqn.
  (rewrite H0).
  (remember (block_fields (heapgraph_block g2 v)) as l).
  clear Heql.
  (cut (forall fl, map (heapgraph_cell_val g1) fl = map (heapgraph_cell_val g2) fl)).
  - (intros).
    (rewrite H2).
    (rewrite (heapgraph_block_ptr__eq g1 g2) by assumption).
    reflexivity.
  - (apply map_ext).
    (intros).
    (unfold heapgraph_cell_val).
    (destruct a).
    1: reflexivity.
    (rewrite H).
    (apply heapgraph_block_ptr__eq; assumption).
Qed.

Lemma lgd_f2v_eq_except_one :
  forall g fd e v', fd <> inr e -> heapgraph_cell_val g fd = heapgraph_cell_val (labeledgraph_gen_dst g e v') fd.
Proof.
  (intros; unfold heapgraph_cell_val; simpl).
  (destruct fd; [ destruct s |  ]; try reflexivity).
  (unfold updateEdgeFunc; if_tac; [ exfalso; apply H; rewrite H0 |  ]; reflexivity).
Qed.

Lemma lgd_map_f2v_diff_vert_eq :
  forall g v v' v1 e n,
  0 <= n < Zlength (heapgraph_block_cells g v) ->
  Znth n (heapgraph_block_cells g v) = inr e ->
  v1 <> v ->
  map (heapgraph_cell_val g) (heapgraph_block_cells g v1) =
  map (heapgraph_cell_val (labeledgraph_gen_dst g e v')) (heapgraph_block_cells (labeledgraph_gen_dst g e v') v1).
Proof.
  (intros).
  (rewrite lgd_heapgraph_block_cells_eq).
  (apply Znth_list_eq).
  split.
  1: (repeat rewrite Zlength_map; reflexivity).
  (intros).
  (rewrite Zlength_map in H2).
  (repeat rewrite Znth_map by assumption).
  (apply lgd_f2v_eq_except_one).
  intro.
  (pose proof (heapgraph_block_cells_edge_unique g e v v1 n j H H2 H0 H3)).
  (destruct H4).
  (unfold not in H1).
  symmetry in H5.
  (apply (H1 H5)).
Qed.

Lemma lgd_f2v_eq_after_update :
  forall g v v' e n j,
  0 <= n < Zlength (heapgraph_block_cells g v) ->
  0 <= j < Zlength (heapgraph_block_cells g v) ->
  Znth n (heapgraph_block_cells g v) = inr e ->
  Znth j (upd_Znth n (map (heapgraph_cell_val g) (heapgraph_block_cells g v)) (heapgraph_block_ptr g v')) =
  Znth j
    (map (heapgraph_cell_val (labeledgraph_gen_dst g e v')) (heapgraph_block_cells (labeledgraph_gen_dst g e v') v)).
Proof.
  (intros).
  (rewrite Znth_map).
  2: (rewrite lgd_heapgraph_block_cells_eq; assumption).
  (assert (j = n \/ j <> n) by lia; destruct H2).
  + (subst j; rewrite upd_Znth_same).
    2: (rewrite Zlength_map; assumption).
    replace (heapgraph_block_cells (labeledgraph_gen_dst g e v') v) with (heapgraph_block_cells g v) by reflexivity.
    (rewrite H1; simpl heapgraph_cell_val).
    (unfold updateEdgeFunc; if_tac; try reflexivity).
    (unfold RelationClasses.complement in H2; assert (e = e) by reflexivity).
    (apply H2 in H3; exfalso; assumption).
  + (rewrite upd_Znth_diff_strong; [  | rewrite Zlength_map |  ]; try assumption).
    (rewrite Znth_map by assumption).
    (apply (lgd_f2v_eq_except_one g (Znth j (heapgraph_block_cells g v)))).
    intro.
    (pose proof (heapgraph_block_cells_edge_unique g e v v n j H H0 H1 H3)).
    lia.
Qed.

Lemma lgd_mfv_change_in_one_spot :
  forall g v e v' n,
  0 <= n < Zlength (heapgraph_block_cells g v) ->
  block_mark (heapgraph_block g v) = false ->
  Znth n (heapgraph_block_cells g v) = inr e ->
  upd_Znth n (heapgraph_block_cells_vals g v) (heapgraph_block_ptr g v') =
  heapgraph_block_cells_vals (labeledgraph_gen_dst g e v') v.
Proof.
  (intros).
  (rewrite
    (Znth_list_eq (upd_Znth n (heapgraph_block_cells_vals g v) (heapgraph_block_ptr g v'))
       (heapgraph_block_cells_vals (labeledgraph_gen_dst g e v') v))).
  (rewrite upd_Znth_Zlength, fields_eq_length).
  2: (rewrite fields_eq_length; rewrite heapgraph_block_cells_eq_length in H; assumption).
  split.
  1: (rewrite fields_eq_length; reflexivity).
  (intros).
  (unfold heapgraph_block_cells_vals).
  replace (block_mark (heapgraph_block (labeledgraph_gen_dst g e v') v)) with 
   (block_mark (heapgraph_block g v)) 
   by reflexivity.
  (rewrite H0; rewrite <- heapgraph_block_cells_eq_length in H2).
  (apply lgd_f2v_eq_after_update; assumption).
Qed.
