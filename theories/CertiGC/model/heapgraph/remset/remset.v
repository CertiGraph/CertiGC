From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.

Local Open Scope Z.

Definition heapgraph_remember_size
  (g : HeapGraph) (gen : nat) : Z :=
  Zlength (generation_remember (heapgraph_generation g gen)).

Lemma heapgraph_remember_size__nonneg (g : HeapGraph) (gen : nat):
  0 <= heapgraph_remember_size g gen.
Proof.
  apply sublist.Zlength_nonneg.
Qed.

Lemma heapgraph_remember_size__heapgraph_generations_append__old 
  (g : HeapGraph) (gi : Generation) 
  (gen : nat) (Hgen : heapgraph_has_gen g gen) :
  heapgraph_remember_size (heapgraph_generations_append g gi) gen = heapgraph_remember_size g gen.
Proof.
  unfold heapgraph_remember_size.
  f_equal.
  unfold heapgraph_generations_append, heapgraph_generation.
  simpl.
  now rewrite app_nth1.
Qed.
