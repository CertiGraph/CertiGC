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
 in if Archi.ptr64 then 32 else 16.

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
  destruct Hn as [Hn_lo Hn_hi].
  split.
  - unfold WORD_SIZE.
    transitivity 0 ; now try lia.
  - rewrite Z.le_lteq.
    left.
    rewrite Z.lt_le_pred in Hn_hi.
    apply Z.le_lt_trans with (WORD_SIZE * Z.pred MAX_SPACE_SIZE) ; unfold WORD_SIZE ; now try lia.
Qed.
