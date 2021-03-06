From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.heap.heap.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.mark.
From CertiGC Require Import model.heapgraph.roots.
From CertiGC Require Import model.util.
From CertiGC Require Import vst.cmodel.constants. (* uses WORD_SIZE *)


Record thread_info: Type := {
    ti_heap_p: val;
    ti_heap: Heap;
    ti_args: list val;
    arg_size: Zlength ti_args = MAX_ARGS;
}.

Definition ti_add_new_space (ti: thread_info) (sp: Space) i
           (Hs: 0 <= i < MAX_SPACES): thread_info :=
  Build_thread_info (ti_heap_p ti) (add_new_space (ti_heap ti) sp i Hs)
                    (ti_args ti) (arg_size ti).


Definition nth_space (t_info: thread_info) (n: nat): Space :=
  nth n t_info.(ti_heap).(heap_spaces) null_space.

Lemma nth_space_Znth: forall t n,
    nth_space t n = Znth (Z.of_nat n) (heap_spaces (ti_heap t)).
Proof.
  intros. unfold nth_space, Znth. rewrite if_false. 2: lia.
  rewrite Nat2Z.id. reflexivity.
Qed.

Lemma ans_nth_new: forall ti sp i (Hs: 0 <= i < MAX_SPACES),
    nth_space (ti_add_new_space ti sp i Hs) (Z.to_nat i) = sp.
Proof.
  intros. rewrite nth_space_Znth. simpl. rewrite Z2Nat.id by lia.
  rewrite upd_Znth_same; [reflexivity | rewrite heap_spaces__size; assumption].
Qed.

Lemma ans_nth_old: forall ti sp i (Hs: 0 <= i < MAX_SPACES) gen,
    gen <> Z.to_nat i -> nth_space (ti_add_new_space ti sp i Hs) gen =
                         nth_space ti gen.
Proof.
  intros. rewrite !nth_space_Znth. simpl. rewrite upd_Znth_diff_strong.
  - reflexivity.
  - rewrite heap_spaces__size. assumption.
  - intro. apply H. subst. rewrite Nat2Z.id. reflexivity.
Qed.


Definition gen_size t_info n := space_capacity (nth_space t_info n).

Definition rest_gen_size (t_info: thread_info) (gen: nat): Z :=
  space_capacity (nth_space t_info gen) - space_allocated (nth_space t_info gen) - space_remembered (nth_space t_info gen).

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
  (heapgraph_generation_size g from <= rest_gen_size t_info to)%Z.



Record thread_info_relation t t' :=
{
  thread_info_relation__ti_heap: ti_heap_p t = ti_heap_p t';
  thread_info_relation__gen_size (n: nat): gen_size t n = gen_size t' n;
  thread_info_relation__space_base (n: nat): space_base (nth_space t n) = space_base (nth_space t' n);
}.

Arguments thread_info_relation__ti_heap [_] [_].
Arguments thread_info_relation__gen_size [_] [_].
Arguments thread_info_relation__space_base [_] [_].

Definition thread_info__remembered_invariant t t' := forall (n: nat), space_remembered (nth_space t n) = space_remembered (nth_space t' n).


Lemma tir_id: forall t, thread_info_relation t t.
Proof.
  dintuition idtac.
Qed.

Lemma tir_trans: forall t1 t2 t3,
    thread_info_relation t1 t2 -> thread_info_relation t2 t3 ->
    thread_info_relation t1 t3.
Proof.
  dintuition congruence.
Qed.


Definition generation_size_spec (tinfo: thread_info) (n: nat): Prop :=
  if Val.eq (nth_space tinfo n).(space_base) nullval
  then True
  else gen_size tinfo n = generation_size n.

Definition ti_size_spec (tinfo: thread_info): Prop :=
  Forall (generation_size_spec tinfo) (nat_inc_list (Z.to_nat MAX_SPACES)).

Lemma ti_size_spec_add: forall ti sp i (Hs: 0 <= i < MAX_SPACES),
    space_capacity sp = generation_size (Z.to_nat i) -> ti_size_spec ti ->
    ti_size_spec (ti_add_new_space ti sp i Hs).
Proof.
  intros. unfold ti_size_spec in *. rewrite Forall_forall in *. intros.
  specialize (H0 _ H1). unfold generation_size_spec in *.
  destruct (Nat.eq_dec x (Z.to_nat i)); unfold gen_size.
  - subst x. rewrite !ans_nth_new. if_tac; auto.
  - rewrite !ans_nth_old; assumption.
Qed.

Lemma ti_relation_size_spec: forall t_info1 t_info2 : thread_info,
    thread_info_relation t_info1 t_info2 ->
    ti_size_spec t_info1 -> ti_size_spec t_info2.
Proof.
  intros.
  unfold ti_size_spec in *.
  rewrite Forall_forall in *.
  intros.
  specialize (H0 _ H1). unfold generation_size_spec in *.
  pose proof (thread_info_relation__gen_size H) as H2.
  pose proof (thread_info_relation__space_base H) as H3.
  now rewrite <- H2, <- H3.
Qed.


Lemma ans_space_address: forall ti sp i (Hs: 0 <= i < MAX_SPACES) j,
    space_address (ti_add_new_space ti sp i Hs) (Z.to_nat j) =
    space_address ti (Z.to_nat j).
Proof. intros. unfold space_address. simpl. reflexivity. Qed.



Lemma ngs_range: forall i,
    0 <= i < MAX_SPACES -> 0 <= generation_size (Z.to_nat i) < MAX_SPACE_SIZE.
Proof.
  intros. unfold generation_size. rewrite MAX_SPACES_eq in H.
  rewrite Z2Nat.id, NURSERY_SIZE_eq, Zbits.Zshiftl_mul_two_p,
  Z.mul_1_l, <- two_p_is_exp by lia. split.
  - cut (two_p (16 + i) > 0). 1: intros; lia. apply two_p_gt_ZERO. lia.
  - try (assert (E: MAX_SPACE_SIZE = two_p 28) by easy ; rewrite E ; clear E ; apply two_p_monotone_strict ; lia) ;
    try (transitivity (two_p 28) ; try easy ; apply two_p_monotone_strict ; lia).
Qed.

Lemma ngs_int_singed_range: forall i,
    0 <= i < MAX_SPACES ->
    (if Archi.ptr64 then Int64.min_signed else Int.min_signed) <=
    generation_size (Z.to_nat i) <=
    (if Archi.ptr64 then Int64.max_signed else Int.max_signed).
Proof.
  intros. apply ngs_range in H. destruct H. split.
  - transitivity 0. 2: assumption. vm_compute. intro HS; inversion HS.
  - apply Z.lt_le_incl. transitivity MAX_SPACE_SIZE. 1: assumption.
    unfold MAX_SPACE_SIZE. vm_compute. reflexivity.
Qed.

Lemma ngs_S: forall i,
    0 <= i -> 2 * generation_size (Z.to_nat i) = generation_size (Z.to_nat (i + 1)).
Proof.
  intros. unfold generation_size. rewrite !Z2Nat.id by lia.
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

Definition null_fun_info: fun_info.
Proof.
  apply (Build_fun_info 0 nil).
  - intros. inversion H.
  - rewrite Zlength_nil.
    unfold MAX_UINT. rep_lia.
  - unfold MAX_UINT. rep_lia.
Qed.

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
