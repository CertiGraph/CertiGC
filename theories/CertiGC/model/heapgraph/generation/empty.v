From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From CertiGC Require Export model.heapgraph.generation.generation.
From CertiGC Require Export model.heapgraph.graph.

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
