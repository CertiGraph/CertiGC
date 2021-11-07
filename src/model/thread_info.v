From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From compcert Require Import common.Values.

From VST Require Import floyd.sublist.
From VST Require Import msl.Coqlib2.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.heap.


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


Record fun_info : Type := {
    fun_word_size: Z;
    live_roots_indices: list Z;
    fi_index_range: forall i, In i live_roots_indices -> (0 <= i < MAX_ARGS)%Z;
    lri_range: (Zlength (live_roots_indices) <= MAX_UINT - 2)%Z;
    word_size_range: (0 <= fun_word_size <= MAX_UINT)%Z;
}.
