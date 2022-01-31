From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.util.

Local Open Scope Z.


Definition heapgraph_field_pairs 
  (g : HeapGraph) (v : Addr) : 
  list (Z + Addr * Z) :=
  map (fun x => inr (v, Z.of_nat x)) (nat_inc_list (length (block_fields (heapgraph_block g v)))).

Lemma heapgraph_field_pairs__Zlength 
  (g : HeapGraph) (v : Addr) : 
  Zlength (heapgraph_field_pairs g v) = Zlength (block_fields (heapgraph_block g v)).
Proof.
  (unfold heapgraph_field_pairs).
  now rewrite Zlength_map, !Zlength_correct, nat_inc_list_length.
Qed.

Lemma heapgraph_field_pairs__Znth 
  `[Inhabitant (Z + Addr * Z)] 
  (g : HeapGraph) (v : Addr) 
  (i : Z) (Hi : 0 <= i < Zlength (block_fields (heapgraph_block g v))) :
  Znth i (heapgraph_field_pairs g v) = inr (v, i).
Proof.
  (unfold heapgraph_field_pairs).
  (assert (Hi' : 0 <= i < Zlength (nat_inc_list (length (block_fields (heapgraph_block g v)))))).
  {
    now rewrite Zlength_correct, nat_inc_list_length, <- Zlength_correct.
  }
  (rewrite Znth_map by assumption).
  (do 2 f_equal).
  (rewrite <- nth_Znth by assumption).
  (rewrite nat_inc_list_nth).
  {
    (rewrite Z2Nat.id; lia).
  }
  (rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_lt; lia).
Qed.