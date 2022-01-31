From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.block.block_rep.
From CertiGC Require Import model.heapgraph.predicates.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.has_block.
From CertiGC Require Import model.util.

Local Open Scope Z.
Import ListNotations.


Definition unmarked_gen_size 
  (g : HeapGraph) (gen : nat) :=
  fold_left (heapgraph_block_size_accum g gen)
    (filter (fun i => negb (heapgraph_block g {| addr_gen := gen; addr_block := i |}).(block_mark))
       (nat_inc_list (generation_block_count (heapgraph_generation g gen)))) 0.

Lemma unmarked_gen_size_le : forall g n, unmarked_gen_size g n <= heapgraph_generation_size g n.
Proof.
  (intros g gen).
  (unfold unmarked_gen_size, heapgraph_generation_size, heapgraph_block_size_prev).
  (apply fold_left_mono_filter;
    [ intros; rewrite Z.le_lteq; left; apply heapgraph_block_size_accum__mono
    | apply heapgraph_block_size_accum__comm ]).
Qed.

Lemma single_unmarked_le :
  forall g v,
  heapgraph_has_block g v ->
  block_mark (heapgraph_block g v) = false ->
  heapgraph_block_size g v <= unmarked_gen_size g (addr_gen v).
Proof.
  (intros).
  (unfold unmarked_gen_size).
  (remember
    (filter (fun i : nat => negb (block_mark (heapgraph_block g {| addr_gen := addr_gen v; addr_block := i |})))
       (nat_inc_list (generation_block_count (heapgraph_generation g (addr_gen v)))))).
  (assert (In (addr_block v) l)).
  {
    subst l.
    (rewrite filter_In).
    split.
    - (rewrite nat_inc_list_In_iff).
      now apply heapgraph_has_block__has_index.
    - (destruct v; simpl).
      (rewrite negb_true_iff).
      (apply H0).
  }
  (apply In_Permutation_cons in H1).
  (destruct H1 as [l1 ?]).
  symmetry in H1.
  (change (addr_block v :: l1) with ([addr_block v] ++ l1) in H1).
  (transitivity (fold_left (heapgraph_block_size_accum g (addr_gen v)) [addr_block v] 0)).
  - (simpl).
    (destruct v; simpl).
    (apply Z.le_refl).
  - (apply (fold_left_Z_mono (heapgraph_block_size_accum g (addr_gen v)) [addr_block v] l1 l 0);
      [ intros; apply Z.le_lteq; left; apply heapgraph_block_size_accum__mono
      | apply heapgraph_block_size_accum__comm
      | apply H1 ]).
Qed.

Lemma lgd_block_mark_eq :
  forall (g : HeapGraph) e (v v' : Addr),
  block_mark (heapgraph_block g v) = block_mark (heapgraph_block (labeledgraph_gen_dst g e v') v).
Proof.
  reflexivity.
Qed.

Lemma block_mark__false_prep64 :
  forall z,
  0 <= z < two_p (8 * 8) ->
  Int64.and (Int64.repr z) (Int64.repr 255) =
  Int64.sub (Int64.repr z) (Int64.mul (Int64.repr (z / two_p 8)) (Int64.repr (two_p 8))).
Proof.
  (intros).
  replace (Int64.repr 255) with (Int64.sub (Int64.repr 256) Int64.one) by now vm_compute.
  (rewrite <- (Int64.modu_and _ _ (Int64.repr 8)) by now vm_compute).
  (rewrite Int64.modu_divu by (vm_compute; intro S; inversion S)).
  (rewrite (Int64.divu_pow2 _ _ (Int64.repr 8)) by now vm_compute).
  (rewrite (Int64.mul_pow2 _ _ (Int64.repr 8)) by now vm_compute).
  (rewrite Int64.shru_div_two_p, !Int64.unsigned_repr; [  | rep_lia |  ]).
  - (rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia).
    easy.
  - (simpl Z.mul in H).
    (unfold Int64.max_unsigned, Int64.modulus).
    (unfold Int64.wordsize, Wordsize_64.wordsize).
    (rewrite two_power_nat_two_p).
    (simpl Z.of_nat).
    lia.
Qed.

Lemma block_mark__false_prep32 :
  forall z,
  0 <= z < two_p (4 * 8) ->
  Int.and (Int.repr z) (Int.repr 255) = Int.sub (Int.repr z) (Int.mul (Int.repr (z / two_p 8)) (Int.repr (two_p 8))).
Proof.
  (intros).
  replace (Int.repr 255) with (Int.sub (Int.repr 256) Int.one) by now vm_compute.
  (rewrite <- (Int.modu_and _ _ (Int.repr 8)) by now vm_compute).
  (rewrite Int.modu_divu by (vm_compute; intro S; inversion S)).
  (rewrite (Int.divu_pow2 _ _ (Int.repr 8)) by now vm_compute).
  (rewrite (Int.mul_pow2 _ _ (Int.repr 8)) by now vm_compute).
  (rewrite Int.shru_div_two_p, !Int.unsigned_repr; [  | rep_lia |  ]).
  - (rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia).
    easy.
  - (simpl Z.mul in H).
    (unfold Int.max_unsigned, Int.modulus).
    (unfold Int.wordsize, Wordsize_32.wordsize).
    (rewrite two_power_nat_two_p).
    (simpl Z.of_nat).
    lia.
Qed.

Lemma block_mark__false :
  forall g v,
  block_mark (heapgraph_block g v) = false ->
  if Archi.ptr64
  then
   Int64.and (Int64.repr (heapgraph_block_header g v)) (Int64.repr 255) = Int64.repr (block_tag (heapgraph_block g v))
  else Int.and (Int.repr (heapgraph_block_header g v)) (Int.repr 255) = Int.repr (block_tag (heapgraph_block g v)).
Proof.
  (intros).
  (cbv delta [Archi.ptr64]).
  (simpl).
  (first [ rewrite block_mark__false_prep32 | rewrite block_mark__false_prep64 ]).
  2: (apply heapgraph_block_header__range).
  (unfold heapgraph_block_header in *).
  (remember (heapgraph_block g v) as r eqn:E ).
  clear E.
  (rewrite H, !Zbits.Zshiftl_mul_two_p in * by lia).
  (rewrite <- Z.add_assoc).
  replace (block_color r * two_p 8 + Zlength (block_fields r) * two_p 10) with
   ((block_color r + Zlength (block_fields r) * two_p 2) * two_p 8)
   by (rewrite Z.mul_add_distr_r, <- Z.mul_assoc, <- two_p_is_exp by lia; reflexivity).
  (rewrite Z.div_add by (vm_compute; intros S; inversion S)).
  (assert (block_tag r / two_p 8 = 0) by apply Z.div_small, block_tag__range).
  (rewrite H0, Z.add_0_l).
  (first [ rewrite mul_repr, sub_repr | rewrite mul64_repr, sub64_repr ]).
  now rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
Qed.
