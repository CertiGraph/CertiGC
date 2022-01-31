From Coq Require Import ZArith.ZArith.

From CertiGC Require Import model.constants.

From CertiGC Require Export model.heapgraph.generation.generation.
From CertiGC Require Export model.heapgraph.graph.
From CertiGC Require Export model.heapgraph.remset.remset.

Local Open Scope Z.


Definition heapgraph_generation_can_copy 
  g from to : Prop := 
  generation_size from <= generation_size to - heapgraph_generation_size g to - heapgraph_remember_size g to.

Definition heapgraph_can_copy 
  (g : HeapGraph) : Prop := 
  forall n, heapgraph_has_gen g (S n) -> heapgraph_generation_can_copy g n (S n).

Definition heapgraph_can_copy_except 
  (g : HeapGraph) (gen : nat) : Prop :=
  forall n, n <> O -> n <> gen -> heapgraph_has_gen g n -> heapgraph_generation_can_copy g (pred n) n.

Lemma heapgraph_can_copy_except__O (g : HeapGraph) : heapgraph_can_copy g <-> heapgraph_can_copy_except g O.
Proof.
  (unfold heapgraph_can_copy, heapgraph_can_copy_except).
  split.
  + (intros H n Hn _ Hgn).
    (destruct n as [| n]; try easy).
    now apply H.
  + (intros H n Hn).
    specialize (H (S n)).
    now apply H.
Qed.

Lemma heapgraph_can_copy__complete 
  (g : HeapGraph) (i : nat) 
  (Hg : heapgraph_can_copy_except g (S i)) 
  (Hi : heapgraph_generation_can_copy g i (S i)) : 
  heapgraph_can_copy g.
Proof.
  (unfold heapgraph_can_copy_except in Hg).
  (unfold heapgraph_can_copy in *).
  (intros n Hn).
  (destruct (Nat.eq_dec n i) as [E| Hn__i]).
  + now subst.
  + specialize (Hg (S n)).
    (apply Hg; now try congruence).
Qed.
