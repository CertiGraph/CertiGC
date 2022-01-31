From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From CertiGC Require Import model.constants.

From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.remset.remset.

Local Open Scope Z.


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