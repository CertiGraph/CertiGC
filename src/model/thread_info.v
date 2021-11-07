From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From compcert Require Import common.Values.

From VST Require Import floyd.sublist.
From VST Require Import msl.Coqlib2.
From VST Require Import veric.base.
From VST Require Import veric.val_lemmas.

From CertiGraph Require Export graph.graph_gen.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.heap.
From CertiGC Require Import model.util.

Import ListNotations.


Record thread_info: Type := {
    ti_heap_p: val;
    ti_heap: Heap;
    ti_args: list val;
    arg_size: Zlength ti_args = MAX_ARGS;
}.

Definition nth_space (t_info: thread_info) (n: nat): Space :=
  nth n t_info.(ti_heap).(heap_spaces) null_space.

Lemma nth_space_Znth: forall t n,
    nth_space t n = Znth (Z.of_nat n) (heap_spaces (ti_heap t)).
Proof.
  intros. unfold nth_space, Znth. rewrite if_false. 2: lia.
  rewrite Nat2Z.id. reflexivity.
Qed.

Definition gen_size t_info n := space_capacity (nth_space t_info n).

Definition rest_gen_size (t_info: thread_info) (gen: nat): Z :=
  space_capacity (nth_space t_info gen) - space_allocated (nth_space t_info gen).

Definition enough_space_to_copy g t_info from to: Prop :=
  (unmarked_gen_size g from <= rest_gen_size t_info to)%Z.

Lemma lgd_enough_space_to_copy: forall g e v' t_info gen sp,
    enough_space_to_copy g t_info gen sp ->
    enough_space_to_copy (labeledgraph_gen_dst g e v') t_info gen sp.
Proof.
  intros. unfold enough_space_to_copy in *. intuition. Qed.

Definition space_address (t_info: thread_info) (gen: nat) :=
  offset_val (SPACE_STRUCT_SIZE * Z.of_nat gen) (ti_heap_p t_info).

Definition enough_space_to_have_g g t_info from to: Prop :=
  (graph_gen_size g from <= rest_gen_size t_info to)%Z.



Definition thread_info_relation t t':=
  ti_heap_p t = ti_heap_p t' /\ (forall n, gen_size t n = gen_size t' n) /\
  forall n, space_base (nth_space t n) = space_base (nth_space t' n).

Lemma tir_id: forall t, thread_info_relation t t.
Proof. intros. red. split; [|split]; reflexivity. Qed.

Lemma tir_trans: forall t1 t2 t3,
    thread_info_relation t1 t2 -> thread_info_relation t2 t3 ->
    thread_info_relation t1 t3.
Proof.
  intros. destruct H as [? [? ?]], H0 as [? [? ?]].
  split; [|split]; [rewrite H; assumption | intros; rewrite H1; apply H3|
                   intros; rewrite H2; apply H4].
Qed.


Definition nth_gen_size (n: nat) := (NURSERY_SIZE * two_p (Z.of_nat n))%Z.

Definition nth_gen_size_spec (tinfo: thread_info) (n: nat): Prop :=
  if Val.eq (nth_space tinfo n).(space_base) nullval
  then True
  else gen_size tinfo n = nth_gen_size n.

Definition ti_size_spec (tinfo: thread_info): Prop :=
  Forall (nth_gen_size_spec tinfo) (nat_inc_list (Z.to_nat MAX_SPACES)).

Definition safe_to_copy_gen g from to: Prop :=
  nth_gen_size from <= nth_gen_size to - graph_gen_size g to.

Lemma ngs_range: forall i,
    0 <= i < MAX_SPACES -> 0 <= nth_gen_size (Z.to_nat i) < MAX_SPACE_SIZE.
Proof.
  intros. unfold nth_gen_size. rewrite MAX_SPACES_eq in H.
  rewrite Z2Nat.id, NURSERY_SIZE_eq, Zbits.Zshiftl_mul_two_p,
  Z.mul_1_l, <- two_p_is_exp by lia. split.
  - cut (two_p (16 + i) > 0). 1: intros; lia. apply two_p_gt_ZERO. lia.
  - transitivity (two_p 28). 1: apply two_p_monotone_strict; lia.
    vm_compute. reflexivity.
Qed.

Lemma ngs_int_singed_range: forall i,
    0 <= i < MAX_SPACES ->
    (if Archi.ptr64 then Int64.min_signed else Int.min_signed) <=
    nth_gen_size (Z.to_nat i) <=
    (if Archi.ptr64 then Int64.max_signed else Int.max_signed).
Proof.
  intros. apply ngs_range in H. destruct H. split.
  - transitivity 0. 2: assumption. vm_compute. intro HS; inversion HS.
  - apply Z.lt_le_incl. transitivity MAX_SPACE_SIZE. 1: assumption.
    unfold MAX_SPACE_SIZE. vm_compute. reflexivity.
Qed.

Lemma ngs_S: forall i,
    0 <= i -> 2 * nth_gen_size (Z.to_nat i) = nth_gen_size (Z.to_nat (i + 1)).
Proof.
  intros. unfold nth_gen_size. rewrite !Z2Nat.id by lia.
  rewrite Z.mul_comm, <- Z.mul_assoc, (Z.mul_comm (two_p i)), <- two_p_S by assumption.
  reflexivity.
Qed.


Record fun_info : Type := {
    fun_word_size: Z;
    live_roots_indices: list Z;
    fi_index_range: forall i, In i live_roots_indices -> (0 <= i < MAX_ARGS)%Z;
    lri_range: (Zlength (live_roots_indices) <= MAX_UINT - 2)%Z;
    word_size_range: (0 <= fun_word_size <= MAX_UINT)%Z;
}.


Definition np_roots_rel from f_info (roots roots': roots_t) (l: list Z) : Prop :=
  let lri := live_roots_indices f_info in
  let maped_lri := (map ((fun x y => Znth y x) lri) l) in
  forall v j, Znth j roots' = inr v ->
              (In (Znth j lri) maped_lri -> addr_gen v <> from) /\
              (~ In (Znth j lri) maped_lri -> Znth j roots = inr v).

Lemma np_roots_rel_cons: forall roots1 roots2 roots3 from f_info i l,
    np_roots_rel from f_info roots1 roots2 [i] ->
    np_roots_rel from f_info roots2 roots3 l ->
    np_roots_rel from f_info roots1 roots3 (i :: l).
Proof.
  intros. unfold np_roots_rel in *. intros. simpl. specialize (H0 _ _ H1).
  destruct H0. split; intros.
  - destruct (in_dec Z.eq_dec (Znth j (live_roots_indices f_info))
                     (map ((fun x y => Znth y x) (live_roots_indices f_info)) l)).
    1: apply H0; assumption. destruct H3. 2: contradiction.
    specialize (H2 n). specialize (H _ _ H2). destruct H. apply H. simpl.
    left; assumption.
  - apply Decidable.not_or in H3. destruct H3.
    specialize (H2 H4). specialize (H _ _ H2). destruct H. apply H5. simpl. tauto.
Qed.
