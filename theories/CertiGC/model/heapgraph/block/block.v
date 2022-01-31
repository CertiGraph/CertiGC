From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.util.

Local Open Scope Z.


Definition heapgraph_block (g : HeapGraph) (v : Addr) : Block := vlabel g v.

Lemma lgd_raw_fld_length_eq :
  forall (g : HeapGraph) v e v',
  Zlength (block_fields (heapgraph_block g v)) =
  Zlength (block_fields (heapgraph_block (labeledgraph_gen_dst g e v') v)).
Proof.
  reflexivity.
Qed.


Definition heapgraph_block_size (g : HeapGraph) (v : Addr) : Z := Zlength (heapgraph_block g v).(block_fields) + 1.

Lemma heapgraph_block_size__one (g : HeapGraph) (v : Addr) : 1 < heapgraph_block_size g v.
Proof.
  (unfold heapgraph_block_size).
  (pose proof (block_fields__range (heapgraph_block g v))).
  lia.
Qed.

Definition heapgraph_block_size_accum 
  (g : HeapGraph) (gen : nat) 
  (s : Z) (n : nat) : Z := 
  s + heapgraph_block_size g {| addr_gen := gen; addr_block := n |}.

Lemma heapgraph_block_size_accum__mono 
  (g : HeapGraph) (gen : nat) 
  (s : Z) (n : nat) : 
  s < heapgraph_block_size_accum g gen s n.
Proof.
  (unfold heapgraph_block_size_accum).
  (pose proof (heapgraph_block_size__one g {| addr_gen := gen; addr_block := n |}) as H).
  lia.
Qed.

Lemma heapgraph_block_size_accum__comm 
  (g : HeapGraph) (gen : nat) 
  (s : Z) (n1 n2 : nat) :
  heapgraph_block_size_accum g gen (heapgraph_block_size_accum g gen s n1) n2 =
  heapgraph_block_size_accum g gen (heapgraph_block_size_accum g gen s n2) n1.
Proof.
  (unfold heapgraph_block_size_accum).
  lia.
Qed.

Lemma heapgraph_block_size_accum__fold_lt 
  (g : HeapGraph) (gen : nat) 
  (s : Z) (l : list nat) 
  (Hl : l <> nil) : s < fold_left (heapgraph_block_size_accum g gen) l s.
Proof.
  (apply (fold_left_Z_mono_strict (heapgraph_block_size_accum g gen) nil l l); try assumption).
  + (apply heapgraph_block_size_accum__mono).
  + (apply heapgraph_block_size_accum__comm).
  + (apply Permutation_refl).
Qed.

Lemma heapgraph_block_size_accum__fold_le 
  (g : HeapGraph) (gen : nat) 
  (s : Z) (l : list nat) : 
  s <= fold_left (heapgraph_block_size_accum g gen) l s.
Proof.
  (destruct l as [| n l]; try easy).
  (rewrite Z.le_lteq).
  left.
  now apply heapgraph_block_size_accum__fold_lt.
Qed.

Lemma heapgraph_block_size_accum__fold_left 
  (g : HeapGraph) (gen : nat) 
  (l : list nat) (z1 z2 : Z) :
  fold_left (heapgraph_block_size_accum g gen) l (z2 + z1) = fold_left (heapgraph_block_size_accum g gen) l z2 + z1.
Proof.
  (revert z1 z2; induction l as [| s l IHl]; intros z1 z2; simpl; try easy).
  (rewrite <- IHl).
  f_equal.
  (unfold heapgraph_block_size_accum).
  lia.
Qed.

Definition heapgraph_block_size_prev 
  (g : HeapGraph) (gen i : nat) : Z := 
  fold_left (heapgraph_block_size_accum g gen) (nat_inc_list i) 0.

Lemma heapgraph_block_size_prev__S 
  (g : HeapGraph) (gen i : nat) :
  heapgraph_block_size_prev g gen (S i) =
  heapgraph_block_size_prev g gen i + heapgraph_block_size g {| addr_gen := gen; addr_block := i |}.
Proof.
  (unfold heapgraph_block_size_prev at 1).
  now rewrite nat_inc_list_S, fold_left_app.
Qed.

Lemma heapgraph_block_size_prev__nonneg (g : HeapGraph) (gen i : nat) : 0 <= heapgraph_block_size_prev g gen i.
Proof.
  (unfold heapgraph_block_size_prev).
  (apply heapgraph_block_size_accum__fold_le).
Qed.

Lemma heapgraph_block_size_prev__mono_strict 
  (g : HeapGraph) (gen i j : nat) 
  (Hij : (i < j)%nat) : 
  heapgraph_block_size_prev g gen i < heapgraph_block_size_prev g gen j.
Proof.
  (assert (Hij' : (j = i + (j - i))%nat) by lia).
  (rewrite Hij').
  (remember (j - i)%nat as n eqn:En ).
  subst j.
  (unfold heapgraph_block_size_prev).
  (rewrite nat_inc_list_app, fold_left_app).
  (apply heapgraph_block_size_accum__fold_lt).
  (pose proof (nat_seq_length i n) as Hin).
  (destruct (nat_seq i n); try easy).
  (simpl in Hin).
  lia.
Qed.

Lemma heapgraph_block_size_prev__mono 
  (g : HeapGraph) (gen i j : nat) 
  (Hij : (i <= j)%nat) : 
  heapgraph_block_size_prev g gen i <= heapgraph_block_size_prev g gen j.
Proof.
  (rewrite Nat.le_lteq in Hij).
  (destruct Hij as [Hij| Hij]).
  + (rewrite Z.le_lteq).
    left.
    now apply heapgraph_block_size_prev__mono_strict.
  + subst.
    lia.
Qed.

Lemma heapgraph_block_size_prev__lt_rev 
  (g : HeapGraph) (gen i j : nat) 
  (Hij : heapgraph_block_size_prev g gen i < heapgraph_block_size_prev g gen j) : 
  (i < j)%nat.
Proof.
  (destruct (le_lt_dec j i) as [Hij'| Hij']; try easy).
  (apply (heapgraph_block_size_prev__mono g gen) in Hij').
  lia.
Qed.


Definition heapgraph_block_offset 
  (g : HeapGraph) (v : Addr) : Z := 
  heapgraph_block_size_prev g (addr_gen v) (addr_block v) + 1.


Definition heapgraph_block_is_no_scan 
  (g : HeapGraph) (v : Addr) : Prop := 
  NO_SCAN_TAG <= (heapgraph_block g v).(block_tag).
