From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.EquivDec_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import util.


Record Space: Type := {
    space_base: val;
    space_allocated: Z;
    space_capacity: Z;
    space_sh: share;
    space__order: (0 <= space_allocated <= space_capacity)%Z;
    space__upper_bound: (space_capacity < MAX_SPACE_SIZE)%Z;
}.

Definition has_space (sp: Space) (s: Z): Prop :=
  0 <= s <= space_capacity sp - space_allocated sp.

Definition null_space: Space := {|
    space_base := nullval;
    space_allocated := 0;
    space_capacity := 0;
    space_sh := emptyshare;
    space__order := ltac:(easy);
    space__upper_bound := ltac:(easy);
|}.

#[global]Instance Space_Inhabitant: Inhabitant Space := null_space.

Lemma space_capacity__tight_range (sp: Space):
    0 <= space_capacity sp < MAX_SPACE_SIZE.
Proof.
    pose proof (space__order sp).
    pose proof (space__upper_bound sp).
    lia.
Qed.

Lemma space_capacity__range (sp: Space):
    0 <= space_capacity sp <= (if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned).
Proof.
    apply MSS_max_unsigned_range, space_capacity__tight_range.
Qed.

Lemma space_capacity__signed_range (sp: Space):
    Ptrofs.min_signed <= WORD_SIZE * space_capacity sp <= Ptrofs.max_signed.
Proof.
    apply MSS_max_wordsize_signed_range, space_capacity__tight_range.
Qed.

Lemma space_allocated__signed_range (sp: Space):
    Ptrofs.min_signed <= WORD_SIZE * space_allocated sp <= Ptrofs.max_signed.
Proof.
    apply MSS_max_wordsize_signed_range.
    pose proof (space__order sp).
    pose proof (space__upper_bound sp).
    lia.
Qed.

Lemma space_remaining__signed_range (sp: Space):
    Ptrofs.min_signed <= WORD_SIZE * space_capacity sp - WORD_SIZE * space_allocated sp <= Ptrofs.max_signed.
Proof.
    rewrite <- Z.mul_sub_distr_l. apply MSS_max_wordsize_signed_range.
    pose proof (space__order sp).
    pose proof (space_capacity__tight_range sp).
    lia.
Qed.

Lemma space_remaining__repable_signed (sp: Space):
    range_signed (space_capacity sp - space_allocated sp).
Proof.
    rewrite <- signed_range_repable_signed.
    pose proof (space_remaining__signed_range sp) as H.
    unfold WORD_SIZE in H.
    rep_lia.
Qed.

Lemma space_allocated__repable_signed (sp: Space):
    range_signed (space_allocated sp).
Proof.
    rewrite <- signed_range_repable_signed.
    pose proof (space_allocated__signed_range sp) as H.
    unfold WORD_SIZE in H.
    rep_lia.
Qed.

Lemma space_capacity__repable_signed (sp: Space):
    range_signed (space_capacity sp).
Proof.
    rewrite <- signed_range_repable_signed.
    pose proof (space_capacity__signed_range sp)as H.
    unfold WORD_SIZE in H.
    rep_lia.
Qed.


Record Heap: Type := {
    heap_spaces: list Space;
    heap_spaces__size: Zlength heap_spaces = MAX_SPACES;
}.

Lemma heap_spaces__nil (h: Heap):
    nil <> heap_spaces h.
Proof.
    intro F.
    pose proof (heap_spaces__size h) as H.
    now rewrite <- F, Zlength_nil in H.
Qed.

Definition heap_head (h: Heap): Space
 := match heap_spaces h as l return (l = heap_spaces h -> Space) with
    | nil => fun m => False_rect Space (heap_spaces__nil h m)
    | s :: _ => fun _ => s
    end eq_refl.

Lemma heap_head__cons (h: Heap):
    exists s l, heap_spaces h = s :: l /\ heap_head h = s.
Proof.
    destruct h eqn:? . simpl. unfold heap_head. simpl. destruct heap_spaces0.
    1: inversion heap_spaces__size0. exists s, heap_spaces0. split; reflexivity.
Qed.


Lemma upd_heap_Zlength: forall (hp : Heap) (sp : Space) (i : Z),
    0 <= i < MAX_SPACES -> Zlength (upd_Znth i (heap_spaces hp) sp) = MAX_SPACES.
Proof.
  intros. rewrite upd_Znth_Zlength; rewrite heap_spaces__size; [reflexivity | assumption].
Qed.

Definition add_new_space (hp: Heap) (sp: Space) i (Hs: 0 <= i < MAX_SPACES): Heap := {|
  heap_spaces := upd_Znth i (heap_spaces hp) sp;
  heap_spaces__size := upd_heap_Zlength hp sp i Hs
|}.
