From Coq Require Import Lists.List.

From CertiGraph Require Import graph.graph_gen.

From CertiGC Require Import model.heapgraph.block.field.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.has_block.

Record heapgraph_has_field (g : HeapGraph) (e : Field) : Prop :=
 {
  heapgraph_has_field__has_block  : heapgraph_has_block g (field_addr e);
  heapgraph_has_field__in  : In e (heapgraph_block_fields g (field_addr e))
 }.

Arguments heapgraph_has_field__has_block [_ _].

Arguments heapgraph_has_field__in [_ _].

Lemma lgd_heapgraph_has_field
  (g : HeapGraph) (e f : Field)
  (v : Addr) : heapgraph_has_field g f <-> heapgraph_has_field (labeledgraph_gen_dst g e v) f.
Proof.
  dintuition idtac.
Qed.
