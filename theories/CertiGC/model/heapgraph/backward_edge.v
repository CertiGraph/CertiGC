From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From CertiGraph Require Import graph.graph_model.

From CertiGC Require Export model.heapgraph.block.field.
From CertiGC Require Export model.heapgraph.generation.empty.
From CertiGC Require Export model.heapgraph.graph.
From CertiGC Require Export model.heapgraph.has_block.
From CertiGC Require Export model.heapgraph.has_field.

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
  generation_block_count gi = O -> no_backward_edge g -> no_backward_edge (heapgraph_generations_append g gi).
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