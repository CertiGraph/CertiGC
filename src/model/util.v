Require Import Coq.ZArith.ZArith.

From compcert Require Import lib.Integers.
From compcert Require Import common.Values.

Local Open Scope Z.


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


Definition range_signed (z: Z) :=
  (if Archi.ptr64 then Int64.min_signed else Int.min_signed) <= z <=
  (if Archi.ptr64 then Int64.max_signed else Int.max_signed).

Lemma signed_range_repable_signed (z: Z):
    Ptrofs.min_signed <= z <= Ptrofs.max_signed <-> range_signed z.
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

Definition repable64_signed (z: Z) := Int64.min_signed <= z <= Int64.max_signed.
  
Lemma lt64_repr (i j: Z)
    (Hi: repable64_signed i)
    (Hj: repable64_signed j)
    (Hij: Int64.lt (Int64.repr i) (Int64.repr j) = true):
    i < j.
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
    i >= j.
Proof.
    unfold Int64.lt in Hij.
    rewrite Int64.signed_repr in Hij ; try assumption.
    rewrite Int64.signed_repr in Hij ; try assumption.
    now destruct (Coqlib.zlt i j) as [H|H] eqn:E.
Qed.
