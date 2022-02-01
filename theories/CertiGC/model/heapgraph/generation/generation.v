From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.graph.

Local Open Scope Z.


Definition heapgraph_generations (g : HeapGraph) : Generations := g.(glabel).

Definition heapgraph_generation 
  (g : HeapGraph) (gen : nat) : Generation := 
  nth gen (heapgraph_generations g).(generations) null_generation.

Definition heapgraph_generation_block_count 
  (g : HeapGraph) (gen : nat) : nat := 
  generation_block_count (heapgraph_generation g gen).

Lemma heapgraph_generation_block_count__labeledgraph_gen_dst 
  (g : HeapGraph) (e : Field) 
  (v : Addr) (to : nat) :
  heapgraph_generation_block_count (labeledgraph_gen_dst g e v) to = heapgraph_generation_block_count g to.
Proof.
  reflexivity.
Qed.

Definition heapgraph_generation_sh (g : HeapGraph) (gen : nat) : share := generation_sh (heapgraph_generation g gen).

Definition heapgraph_has_gen 
  (g : HeapGraph) (n : nat) : Prop := 
  (n < length (heapgraph_generations g).(generations))%nat.

Definition heapgraph_has_gen_dec 
  g n : {heapgraph_has_gen g n} + {~ heapgraph_has_gen g n} :=
  lt_dec n (length (generations (heapgraph_generations g))).

Lemma heapgraph_has_gen__O (g : HeapGraph) : heapgraph_has_gen g O.
Proof.
  (hnf).
  (destruct (generations (heapgraph_generations g)) as [| x xx] eqn:E; simpl; try lia).
  now pose proof (generations__not_nil (heapgraph_generations g)).
Qed.

Lemma lgd_graph_has_gen : forall g e v x, heapgraph_has_gen (labeledgraph_gen_dst g e v) x <-> heapgraph_has_gen g x.
Proof.
  (intros; unfold heapgraph_has_gen; intuition idtac).
Qed.


Definition heapgraph_generation_has_index 
  (g : HeapGraph) (gen index : nat) : Prop := 
  (index < generation_block_count (heapgraph_generation g gen))%nat.

Definition heapgraph_generation_size 
  (g : HeapGraph) (gen : nat) : Z :=
  heapgraph_block_size_prev g gen (generation_block_count (heapgraph_generation g gen)).

Lemma heapgraph_generation_size__nonneg (g : HeapGraph) (gen : nat):
  0 <= heapgraph_generation_size g gen.
Proof.
  unfold heapgraph_generation_size.
  pose proof (heapgraph_block_size_prev__nonneg g gen (generation_block_count (heapgraph_generation g gen))).
  lia.
Qed.

Lemma heapgraph_block_offset__heapgraph_generation_size 
  (g : HeapGraph) (v : Addr) 
  (Hgv : heapgraph_generation_has_index g (addr_gen v) (addr_block v)) :
  heapgraph_block_offset g v < heapgraph_generation_size g (addr_gen v).
Proof.
  (unfold heapgraph_block_offset, heapgraph_generation_size).
  (red in Hgv).
  (remember (generation_block_count (heapgraph_generation g (addr_gen v))) as n eqn:En ).
  (remember (addr_gen v) as gen eqn:Egen ).
  (assert (S (addr_block v) <= n)%nat by lia).
  (apply Z.lt_le_trans with (heapgraph_block_size_prev g gen (S (addr_block v)))).
  - (rewrite heapgraph_block_size_prev__S).
    pose proof (heapgraph_block_size__one g ({| addr_gen := gen; addr_block := addr_block v |})).
    lia.
  - pose proof (heapgraph_block_size_prev__mono g gen (S (addr_block v)) n ltac:(easy)).
    lia.
Qed.

Definition heapgraph_generations_append 
  (g : HeapGraph) (gen_i : Generation) : HeapGraph :=
  {|
    pg_lg := pg_lg g;
    vlabel := heapgraph_block g;
    elabel := elabel g;
    glabel := generations_append (heapgraph_generations g) gen_i
  |}.

Lemma heapgraph_has_gen__heapgraph_generations_append 
  (g : HeapGraph) (gi : Generation) 
  (gen : nat) :
  heapgraph_has_gen (heapgraph_generations_append g gi) gen <->
  heapgraph_has_gen g gen \/ gen = length (generations (heapgraph_generations g)).
Proof.
  (unfold heapgraph_has_gen; simpl).
  (rewrite app_length; simpl).
  lia.
Qed.


Lemma heapgraph_generation__heapgraph_generations_append__old 
  (g : HeapGraph) (gi : Generation) 
  (gen : nat) (Hgen : heapgraph_has_gen g gen) :
  heapgraph_generation (heapgraph_generations_append g gi) gen = heapgraph_generation g gen.
Proof.
  (unfold heapgraph_generation; simpl).
  now rewrite app_nth1.
Qed.

Lemma heapgraph_generation__heapgraph_generations_append__new 
  (g : HeapGraph) (gi : Generation) :
  heapgraph_generation (heapgraph_generations_append g gi) (length (generations (heapgraph_generations g))) = gi.
Proof.
  (unfold heapgraph_generation; simpl).
  (rewrite app_nth2 by lia).
  now rewrite Nat.sub_diag.
Qed.

Definition heapgraph_generation_base 
  (g : HeapGraph) (gen : nat) : val :=
  if heapgraph_has_gen_dec g gen then generation_base (heapgraph_generation g gen) else Vundef.

Lemma ang_graph_gen_size_old :
  forall g gi gen,
  heapgraph_has_gen g gen ->
  heapgraph_generation_size g gen = heapgraph_generation_size (heapgraph_generations_append g gi) gen.
Proof.
  (intros).
  (unfold heapgraph_generation_size).
  (rewrite heapgraph_generation__heapgraph_generations_append__old by assumption).
  (now apply fold_left_ext).
Qed.

Lemma heapgraph_generation_base__isptr 
  (g : HeapGraph) (n : nat) 
  (Hgn : heapgraph_has_gen g n) : 
  isptr (heapgraph_generation_base g n).
Proof.
  (unfold heapgraph_generation_base).
  (if_tac; try easy).
  (apply generation_base__isptr).
Qed.
