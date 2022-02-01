From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.

Local Open Scope Z.

Definition heapgraph_remember_upto (g : HeapGraph) (gen : nat): list Remember :=
  concat (map generation_remember (firstn (S gen) (generations (heapgraph_generations g)))).

Lemma heapgraph_remember_upto__heapgraph_generations_append__old 
  (g : HeapGraph) (gi : Generation) 
  (gen : nat) (Hgen : heapgraph_has_gen g gen) :
  heapgraph_remember_upto (heapgraph_generations_append g gi) gen = heapgraph_remember_upto g gen.
Proof.
  unfold heapgraph_remember_upto, heapgraph_generations_append, heapgraph_generation.
  f_equal.
  Opaque firstn.
  simpl.
  Transparent firstn.
  rewrite firstn_app.
  unfold heapgraph_has_gen in Hgen.
  replace
    (S gen - length (generations (heapgraph_generations g)))%nat
    with O
    by lia.
  now rewrite app_nil_r.
Qed.

Definition heapgraph_remember_range (g : HeapGraph) (gen1 gen2 : nat): list Remember :=
  concat (map generation_remember (firstn (gen2 - gen1) (skipn (S gen1) (generations (heapgraph_generations g))))).

Lemma heapgraph_remember_upto__heapgraph_remember_range g gen1 gen2 (Hgen: (gen1 <= gen2)%nat):
  heapgraph_remember_upto g gen2 = heapgraph_remember_upto g gen1 ++ heapgraph_remember_range g gen1 gen2.
Proof.
  unfold heapgraph_remember_upto, heapgraph_remember_range.
  rewrite <- concat_app.
  rewrite <- map_app.
  rewrite sublist.firstn_app.
  now replace
    (S gen1 + (gen2 - gen1))%nat
    with (S gen2)%nat
    by lia.
Qed.


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
