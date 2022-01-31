From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.heapgraph.block.block_rep.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.util.

Local Open Scope Z.


Definition root_t : Type := Z + GC_Pointer + Addr.

#[global]Instance root_t_inhabitant : (Inhabitant root_t) := (inl (inl Z.zero)).

Definition root2val (g : HeapGraph) 
  (fd : root_t) : val :=
  match fd with
  | inl (inl z) => odd_Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr v => heapgraph_block_ptr g v
  end.

Definition roots_t : Type := list root_t.

Lemma root_in_outlier :
  forall (roots : roots_t) outlier p,
  In (inl (inr p)) roots -> incl (filter_sum_right (filter_sum_left roots)) outlier -> In p outlier.
Proof.
  (intros).
  (apply H0).
  (rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff).
  assumption.
Qed.

Definition roots_have_no_gen (roots : roots_t) (gen : nat) : Prop := forall v, In (inr v) roots -> addr_gen v <> gen.

Definition outlier_t : Type := list GC_Pointer.
