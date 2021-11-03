From VST Require Import floyd.proofauto.

Definition WORD_SIZE: Z
 := Eval cbv [Archi.ptr64]
 in if Archi.ptr64 then 8 else 4.
Definition WORD_SIZE_pos: 0 < WORD_SIZE := eq_refl.

Definition MAX_UINT: Z
 := Eval cbv [Archi.ptr64]
 in if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned.

Definition MAX_SPACE_SIZE: Z
 := Eval cbv [Archi.ptr64]
 in if Archi.ptr64 then Z.shiftl 1 40 else Z.shiftl 1 29.

Definition SPACE_STRUCT_SIZE: Z
 := Eval cbv [Archi.ptr64]
 in if Archi.ptr64 then 24 else 12.


Definition MAX_SPACES: Z := 12.
Definition MAX_SPACES_eq: MAX_SPACES = 12 := eq_refl.
Hint Rewrite MAX_SPACES_eq: rep_lia.
Global Opaque MAX_SPACES.

Definition NURSERY_SIZE: Z := Z.shiftl 1 16.
Definition NURSERY_SIZE_eq: NURSERY_SIZE = Z.shiftl 1 16 := eq_refl.
Hint Rewrite NURSERY_SIZE_eq: rep_lia.
Global Opaque NURSERY_SIZE.

Definition MAX_ARGS: Z := 1024.
Definition MAX_ARGS_eq: MAX_ARGS = 1024 := eq_refl.
Hint Rewrite MAX_ARGS_eq: rep_lia.
Global Opaque MAX_ARGS.

Definition NO_SCAN_TAG: Z := 251.
Definition NO_SCAN_TAG_eq: NO_SCAN_TAG = 251 := eq_refl.
Hint Rewrite NO_SCAN_TAG_eq: rep_lia.
Global Opaque NO_SCAN_TAG.


Lemma four_div_WORD_SIZE: (4 | WORD_SIZE).
Proof. first [now exists 1 | now exists 2]. Qed.

Definition MSS_eq_unsigned: Int.unsigned (Int.shl (Int.repr 1) (Int.repr 29)) = Z.shiftl 1 29 := eq_refl.

Lemma MSS_max_unsigned_range (n: Z) (Hn: 0 <= n < MAX_SPACE_SIZE):
    0 <= n <= MAX_UINT.
Proof.
    split ; try lia.
    now transitivity MAX_SPACE_SIZE ; try lia.
Qed.

Lemma MSS_max_wordsize_unsigned_range (n: Z) (Hn: 0 <= n < MAX_SPACE_SIZE):
    0 <= WORD_SIZE * n <= MAX_UINT.
Proof.
    pose proof WORD_SIZE_pos as HH.
    split ; try lia.
    now transitivity (WORD_SIZE * MAX_SPACE_SIZE) ; try nia.
Qed.

Lemma MSS_max_wordsize_signed_range (n: Z) (Hn: 0 <= n < MAX_SPACE_SIZE):
    Ptrofs.min_signed <= WORD_SIZE * n <= Ptrofs.max_signed.
Proof.
  pose proof WORD_SIZE_pos as HH.
  split ; try rep_lia.
  now transitivity (WORD_SIZE * MAX_SPACE_SIZE) ; try nia.
Qed.
