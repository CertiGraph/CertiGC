From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.

From CertiGraph Require Import graph.graph_gen.

From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.


Record heapgraph_has_block (g : HeapGraph) (v : Addr) : Prop :=
{
    heapgraph_has_block__has_gen  : heapgraph_has_gen g (addr_gen v);
    heapgraph_has_block__has_index  : heapgraph_generation_has_index g (addr_gen v) (addr_block v)
}.

Arguments heapgraph_has_block__has_gen [_ _].

Arguments heapgraph_has_block__has_index [_ _].

Lemma heapgraph_generations_append__heapgraph_has_block 
    (g : HeapGraph) (gi : Generation) 
    (v : Addr) (Hv : heapgraph_has_block g v) : 
    heapgraph_has_block (heapgraph_generations_append g gi) v.
Proof.
    (destruct v as [gen idx]).
    (destruct Hv; split; simpl in *).
    - (unfold heapgraph_has_gen in *).
    (simpl).
    (rewrite app_length).
    (simpl).
    lia.
    - (unfold heapgraph_generation_has_index in *).
    (rewrite heapgraph_generation__heapgraph_generations_append__old; assumption).
Qed.

Lemma heapgraph_generations_append__heapgraph_has_block_inv 
    (g : HeapGraph) (gi : Generation) 
    (v : Addr) (Hgi : generation_block_count gi = O) 
    (Hv : heapgraph_has_block (heapgraph_generations_append g gi) v) : 
    heapgraph_has_block g v.
Proof.
    (pose proof (heapgraph_has_block__has_gen Hv) as Hgen).
    (pose proof (heapgraph_has_block__has_index Hv) as Hindex).
    (red in Hindex).
    (apply heapgraph_has_gen__heapgraph_generations_append in Hgen).
    refine {| heapgraph_has_block__has_gen := _; heapgraph_has_block__has_index := _ |}.
    + (destruct Hgen as [Hgen| Hgen]; try easy).
    (rewrite Hgen, heapgraph_generation__heapgraph_generations_append__new in Hindex).
    lia.
    + (destruct Hgen as [Hgen| Hgen]).
    - now rewrite heapgraph_generation__heapgraph_generations_append__old in Hindex.
    - (rewrite Hgen, heapgraph_generation__heapgraph_generations_append__new in Hindex).
        lia.
Qed.

Lemma lgd_heapgraph_has_block
  (g : HeapGraph) (e : Field)
  (v v' : Addr) : heapgraph_has_block g v <-> heapgraph_has_block (labeledgraph_gen_dst g e v') v.
Proof.
  dintuition idtac.
Qed.

Lemma lgd_forall_heapgraph_has_block
  (g : HeapGraph) (e : Field) (v : Addr) (rr : list Addr)
  (Hrr: Forall (heapgraph_has_block g) rr):
  Forall (heapgraph_has_block (labeledgraph_gen_dst g e v)) rr.
Proof.
  generalize Hrr ; clear Hrr.
  induction rr ; try easy.
  intro Hrr.
  inversion Hrr.
  constructor.
  + now apply lgd_heapgraph_has_block.
  + now apply IHrr.
Qed.
