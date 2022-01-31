From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

Local Open Scope Z.

Definition MAX_SPACES: Z := 12.
Definition MAX_SPACES_eq: MAX_SPACES = 12 := eq_refl.
Hint Rewrite MAX_SPACES_eq: rep_lia.
Global Opaque MAX_SPACES.

Definition NURSERY_SIZE: Z := Z.shiftl 1 16.
Definition NURSERY_SIZE_eq: NURSERY_SIZE = Z.shiftl 1 16 := eq_refl.
Hint Rewrite NURSERY_SIZE_eq: rep_lia.
Global Opaque NURSERY_SIZE.

Definition generation_size (n: nat) := (NURSERY_SIZE * two_p (Z.of_nat n))%Z.

Lemma generation_size_le_S (n: nat): generation_size n <= generation_size (S n).
Proof.
  unfold generation_size.
  rewrite Nat2Z.inj_succ, two_p_S by lia.
  assert
    (two_p (Z.of_nat n) > 0)
    as H
    by (apply two_p_gt_ZERO; lia).
  assert
    (0 < NURSERY_SIZE)
    as H0
    by easy.
  rewrite Z.mul_assoc, (Z.mul_comm NURSERY_SIZE 2).
  assert
    (0 < NURSERY_SIZE * two_p (Z.of_nat n))
    as H1
    by (apply Z.mul_pos_pos; lia).
  rewrite <- Z.add_diag, Z.mul_add_distr_r.
  lia.
Qed.

Lemma ngs_0_lt (i: nat): 0 < generation_size i.
Proof.
  unfold generation_size.
  rewrite NURSERY_SIZE_eq.
  remember
    (Z.of_nat i)
    as z eqn:Heqz.
  unfold two_p.
  simpl Z.shiftl.
  destruct z as [|z|z] ; try lia.
  unfold two_power_pos.
  lia.
Qed.


Definition MAX_ARGS: Z := 1024.
Definition MAX_ARGS_eq: MAX_ARGS = 1024 := eq_refl.
Hint Rewrite MAX_ARGS_eq: rep_lia.
Global Opaque MAX_ARGS.

Definition NO_SCAN_TAG: Z := 251.
Definition NO_SCAN_TAG_eq: NO_SCAN_TAG = 251 := eq_refl.
Hint Rewrite NO_SCAN_TAG_eq: rep_lia.
Global Opaque NO_SCAN_TAG.
