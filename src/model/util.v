From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import Sorting.Permutation.
From Coq Require Import ZArith.ZArith.

From compcert Require Import lib.Integers.
From compcert Require Import common.Values.

From CertiGraph Require Import lib.List_ext.

Import ListNotations.


Definition odd_Z2val (x: Z): val
 := Eval cbv delta [Archi.ptr64] match
 in if Archi.ptr64
    then Vlong (Int64.repr (2 * x + 1)%Z)
    else Vint (Int.repr (2 * x + 1)%Z).

Definition Z2val (x: Z): val
 := Eval cbv delta [Archi.ptr64] match
 in if Archi.ptr64
    then Vlong (Int64.repr x)
    else Vint (Int.repr x).


Local Open Scope Z.
Definition range_signed (z: Z) :=
    (if Archi.ptr64 then Int64.min_signed else Int.min_signed) <= z <=
    (if Archi.ptr64 then Int64.max_signed else Int.max_signed).
Local Close Scope Z.

Lemma signed_range_repable_signed (z: Z):
    (Ptrofs.min_signed <= z <= Ptrofs.max_signed)%Z <-> range_signed z.
Proof.
    unfold range_signed.
    replace Ptrofs.max_signed
        with (if Archi.ptr64 then Int64.max_signed else Int.max_signed)
        by (vm_compute; reflexivity).
    replace Ptrofs.min_signed
        with (if Archi.ptr64 then Int64.min_signed else Int.min_signed)
        by (vm_compute; reflexivity).
    reflexivity.
Qed.

Definition repable64_signed (z: Z) := (Int64.min_signed <= z <= Int64.max_signed)%Z.
  
Lemma lt64_repr (i j: Z)
    (Hi: repable64_signed i)
    (Hj: repable64_signed j)
    (Hij: Int64.lt (Int64.repr i) (Int64.repr j) = true):
    (i < j)%Z.
Proof.
    unfold Int64.lt in Hij.
    rewrite Int64.signed_repr in Hij ; try assumption.
    rewrite Int64.signed_repr in Hij ; try assumption.
    now destruct (Coqlib.zlt i j) as [H|H] eqn:E.
Qed.

Lemma lt64_repr_false (i j: Z)
    (Hi: repable64_signed i)
    (Hj: repable64_signed j)
    (Hij: Int64.lt (Int64.repr i) (Int64.repr j) = false):
    (i >= j)%Z.
Proof.
    unfold Int64.lt in Hij.
    rewrite Int64.signed_repr in Hij ; try assumption.
    rewrite Int64.signed_repr in Hij ; try assumption.
    now destruct (Coqlib.zlt i j) as [H|H] eqn:E.
Qed.


Fixpoint nat_seq (s total: nat): list nat
 := match total with
    | O => nil
    | S n => s :: nat_seq (S s) n
    end.

Lemma nat_seq_length (s n: nat):
    length (nat_seq s n) = n.
Proof.
    revert s.
    induction n as [|n IHn] ; try easy.
    intro s. simpl. now f_equal.
Qed.

Lemma nat_seq_S (i num: nat):
    nat_seq i (S num) = nat_seq i num ++ [num + i].
Proof.
    revert i.
    induction num as [|num IHnum] ; try easy.
    intro i. remember (S num) as num' eqn:Enum'. simpl.
    rewrite (IHnum (S i)). subst. simpl.
    repeat f_equal.
    lia.
Qed.

Lemma nat_seq_In_iff (s n i: nat):
    In i (nat_seq s n) <-> s <= i < s + n.
Proof.
    revert s ; induction n as [|n IHn] ; intro s ; simpl.
    + lia.
    + rewrite IHn. lia.
Qed.

Lemma nat_seq_NoDup (s n: nat):
    NoDup (nat_seq s n).
Proof.
    revert s ; induction n as [| n IHn] ; intro s ; simpl ; constructor.
    + rewrite nat_seq_In_iff. lia.
    + apply IHn.
Qed.

Lemma nat_seq_nth (s num n a: nat) (Hn: n < num):
    nth n (nat_seq s num) a = s + n.
Proof.
    revert s n Hn ; induction num as [|num IHnum] ; intros s n Hn ; try lia.
    destruct n as [|n] ; simpl ; try lia.
    specialize (IHnum (S s) n) as IHnum.
    replace (s + S n) with (S s + n) by lia.
    rewrite IHnum ; lia.
Qed.

Lemma nat_seq_app (s n m: nat):
    nat_seq s (n + m) = nat_seq s n ++ nat_seq (s + n) m.
Proof.
  revert s ; induction n as [|n IHn] ; intro s ; simpl.
  + now replace (s + 0) with s by lia.
  + f_equal.
    rewrite IHn.
    now replace (S s + n) with (s + S n) by lia.
Qed.

Lemma nat_seq_Permutation_cons (s i n: nat) (Hin: i < n):
    exists l, Permutation (nat_seq s n) (s + i :: l).
Proof.
    induction n as [|n IHn] ; try lia.
    replace (S n) with (n + 1) by lia.
    rewrite nat_seq_app ; simpl.
    destruct (Nat.eq_dec i n) as [H|H].
    - subst.
      exists (nat_seq s n). symmetry ; apply Permutation_cons_append.
    - assert (i < n) as Hl by lia.
      apply IHn in Hl. destruct Hl as [l Hl].
      exists (l +:: (s + n)).
      rewrite app_comm_cons.
      now apply Permutation_app_tail.
Qed.

Definition nat_inc_list (n: nat): list nat := nat_seq O n.

Lemma nat_inc_list_length (num: nat):
    length (nat_inc_list num) = num.
Proof.
    unfold nat_inc_list.
    now rewrite nat_seq_length.
Qed.

Lemma nat_inc_list_S (num: nat):
    nat_inc_list (S num) = nat_inc_list num ++ [num].
Proof.
    unfold nat_inc_list.
    rewrite nat_seq_S.
    repeat f_equal.
    lia.
Qed.

Lemma nat_inc_list_In_iff (i n: nat):
    In i (nat_inc_list n) <-> i < n.
Proof.
    unfold nat_inc_list.
    rewrite nat_seq_In_iff.
    intuition.
Qed.

Lemma nat_inc_list_nth (i n a: nat) (Hin: i < n):
    nth i (nat_inc_list n) a = i.
Proof.
    unfold nat_inc_list.
    rewrite nat_seq_nth ; try assumption.
    lia.
Qed.

Lemma nat_inc_list_app (n m: nat):
    nat_inc_list (n + m) = nat_inc_list n ++ nat_seq n m.
Proof.
    unfold nat_inc_list.
    now rewrite nat_seq_app.
Qed.

Lemma nat_inc_list_NoDup (n: nat):
    NoDup (nat_inc_list n).
Proof.
    unfold nat_inc_list.
    apply nat_seq_NoDup.
Qed.

Lemma nat_inc_list_Permutation_cons (i n: nat) (Hin: i < n):
    exists l, Permutation (nat_inc_list n) (i :: l).
Proof.
  unfold nat_inc_list.
  replace i with (O + i) by lia.
  now apply nat_seq_Permutation_cons.
Qed.
