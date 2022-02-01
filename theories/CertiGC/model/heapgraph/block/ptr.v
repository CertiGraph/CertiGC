From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.

From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.has_block.
From CertiGC Require Import vst.cmodel.constants. (* uses WORD_SIZE *)

Local Open Scope Z.


Definition heapgraph_block_ptr 
  (g : HeapGraph) (v : Addr) : val :=
  offset_val (WORD_SIZE * heapgraph_block_offset g v) (heapgraph_generation_base g (addr_gen v)).

Lemma lgd_heapgraph_block_ptr_eq :
  forall g e v' x, heapgraph_block_ptr (labeledgraph_gen_dst g e v') x = heapgraph_block_ptr g x.
Proof.
  reflexivity.
Qed.

Lemma heapgraph_block_ptr__eq 
  (g1 g2 : HeapGraph) 
  (v : Addr) (Hv : forall v, heapgraph_block g1 v = heapgraph_block g2 v)
  (Hg1g2 : map generation_base (heapgraph_generations g1).(generations) =
           map generation_base (heapgraph_generations g2).(generations)) :
  heapgraph_block_ptr g1 v = heapgraph_block_ptr g2 v.
Proof.
  (unfold heapgraph_block_ptr).
  f_equal.
  {
    f_equal.
    (unfold heapgraph_block_offset).
    f_equal.
    (remember (addr_block v) as n eqn:En ).
    clear En.
    (induction n as [| n IHn]; simpl; auto).
    (rewrite !heapgraph_block_size_prev__S, IHn).
    f_equal.
    (unfold heapgraph_block_size).
    now rewrite Hv.
  }
  {
    (assert (Hgen : forall gen, heapgraph_has_gen g1 gen <-> heapgraph_has_gen g2 gen)).
    {
      intro gen.
      (unfold heapgraph_has_gen).
      (assert (E : length (generations (heapgraph_generations g1)) = length (generations (heapgraph_generations g2)))).
      {
        now rewrite <- !(map_length generation_base), Hg1g2.
      }
      lia.
    }
    (unfold heapgraph_generation_base).
    (do 2 if_tac; rewrite Hgen in H; try easy).
    (unfold heapgraph_generation).
    now rewrite <- !(map_nth generation_base), Hg1g2.
  }
Qed.

Lemma heapgraph_generations_append__heapgraph_block_ptr 
  (g : HeapGraph) (gi : Generation) 
  (v : Addr) (Hv : heapgraph_has_block g v) :
  heapgraph_block_ptr (heapgraph_generations_append g gi) v = heapgraph_block_ptr g v.
Proof.
  (unfold heapgraph_block_ptr).
  f_equal.
  (unfold heapgraph_generation_base).
  (destruct Hv).
  (rewrite if_true by (rewrite heapgraph_has_gen__heapgraph_generations_append; now left)).
  (rewrite if_true by easy).
  now rewrite heapgraph_generation__heapgraph_generations_append__old.
Qed.
