From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.

Local Open Scope Z.

Definition heapgraph_remember_upto (g : HeapGraph) (gen : nat): list Remember :=
  fold_left
    (fun rr g => rr ++ generation_remember g)
    (firstn (S gen) (generations (heapgraph_generations g)))
    nil.

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
