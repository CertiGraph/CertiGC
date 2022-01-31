From Coq Require Import Lists.List.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.heap.heap.
From CertiGC Require Import model.thread_info.thread_info.


Lemma cut_space__order: forall (sp : Space) (s : Z),
    has_space sp s -> 0 <= space_allocated sp + s + space_remembered sp <= space_capacity sp.
Proof.
  intros.
  pose proof (space__order sp).
  red in H.
  lia.
Qed.


Lemma cut_space_allocated__lower_bound: forall (sp : Space) (s : Z),
    has_space sp s -> 0 <= space_allocated sp + s.
Proof.
  intros.
  pose proof (space_allocated__lower_bound sp).
  red in H.
  lia.
Qed.

Definition cut_space (sp: Space) (s: Z) (H: has_space sp s): Space := {|
    space_base := space_base sp;
    space_allocated := space_allocated sp + s;
    space_remembered := space_remembered sp;
    space_capacity := space_capacity sp;
    space_sh := space_sh sp;
    space_allocated__lower_bound := cut_space_allocated__lower_bound sp s H;
    space_remembered__lower_bound := space_remembered__lower_bound sp;
    space__order := cut_space__order sp s H;
    space__upper_bound := space__upper_bound sp;
|}.

Lemma cut_heap_size:
  forall (h : Heap) (i s : Z) (H : has_space (Znth i (heap_spaces h)) s),
    0 <= i < Zlength (heap_spaces h) ->
    Zlength (upd_Znth i (heap_spaces h) (cut_space (Znth i (heap_spaces h)) s H)) = MAX_SPACES.
Proof. intros. rewrite upd_Znth_Zlength; [apply heap_spaces__size | assumption]. Qed.

Definition cut_heap (h: Heap) (i s: Z) (H1: 0 <= i < Zlength (heap_spaces h))
           (H2: has_space (Znth i (heap_spaces h)) s): Heap := {|
  heap_spaces := upd_Znth i (heap_spaces h) (cut_space (Znth i (heap_spaces h)) s H2);
  heap_spaces__size := cut_heap_size h i s H2 H1
|}.

Lemma heap_head_cut_thread_info: forall
    h i s (H1: 0 <= i < Zlength (heap_spaces h)) (H2: has_space (Znth i (heap_spaces h)) s),
    i <> 0 -> heap_head (cut_heap h i s H1 H2) = heap_head h.
Proof.
  intros. destruct (heap_head__cons h) as [hs1 [l1 [? ?]]].
  destruct (heap_head__cons (cut_heap h i s H1 H2)) as [hs2 [l2 [? ?]]].
  rewrite H3, H5. simpl in H4.
  pose proof (split3_full_length_list
                0 i _ _ H1 (Zminus_0_l_reverse (Zlength (heap_spaces h)))).
  replace (i - 0) with i in H6 by lia. simpl in H6.
  remember (firstn (Z.to_nat i) (heap_spaces h)) as ls1.
  remember (skipn (Z.to_nat (i + 1)) (heap_spaces h)) as ls2.
  assert (Zlength ls1 = i). {
    rewrite Zlength_length by lia. subst ls1. apply firstn_length_le.
    clear H5. rewrite Zlength_correct in H1. lia. }
  rewrite H6 in H4 at 1. rewrite (upd_Znth_char _ _ _ _ _ H7) in H4.
  rewrite H6 in H0. clear -H0 H4 H H7. destruct ls1.
  - rewrite Zlength_nil in H7. exfalso. apply H. subst i. reflexivity.
  - simpl in H0, H4. inversion H0. subst hs1. inversion H4. reflexivity.
Qed.

Definition cut_thread_info (t: thread_info) (i s: Z)
           (H1: 0 <= i < Zlength (heap_spaces (ti_heap t)))
           (H2: has_space (Znth i (heap_spaces (ti_heap t))) s) : thread_info :=
  Build_thread_info (ti_heap_p t) (cut_heap (ti_heap t) i s H1 H2) (ti_args t)
                    (arg_size t).

Lemma cti_eq: forall t i s1 s2 (H1: 0 <= i < Zlength (heap_spaces (ti_heap t)))
                     (Hs1: has_space (Znth i (heap_spaces (ti_heap t))) s1)
                     (Hs2: has_space (Znth i (heap_spaces (ti_heap t))) s2),
    s1 = s2 -> cut_thread_info t i s1 H1 Hs1 = cut_thread_info t i s2 H1 Hs2.
Proof.
  intros. unfold cut_thread_info. f_equal. subst s1. f_equal. apply proof_irr.
Qed.


Lemma cti_rest_gen_size:
  forall t_info to s
         (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
         (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) s),
  rest_gen_size t_info to =
  rest_gen_size (cut_thread_info t_info (Z.of_nat to) s Hi Hh) to + s.
Proof.
  intros. unfold rest_gen_size. rewrite !nth_space_Znth. unfold cut_thread_info. simpl.
  rewrite upd_Znth_same by assumption. simpl. lia.
Qed.

Lemma cti_space_not_eq: forall t_info i s n
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s),
    (Z.of_nat n) <> i ->
    nth_space (cut_thread_info t_info i s Hi Hh) n = nth_space t_info n.
Proof.
  intros. rewrite !nth_space_Znth. simpl.
  pose proof (Nat2Z.is_nonneg n). remember (Z.of_nat n). clear Heqz.
  remember (heap_spaces (ti_heap t_info)). destruct (Z_lt_le_dec z (Zlength l)).
  - assert (0 <= z < Zlength l) by lia.
    rewrite upd_Znth_diff; [reflexivity |assumption..].
  - rewrite !Znth_overflow;
      [reflexivity | | rewrite upd_Znth_Zlength by assumption]; lia.
Qed.

Lemma cti_space_eq: forall t_info i s
    (Hi : 0 <= Z.of_nat i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat i) (heap_spaces (ti_heap t_info))) s),
    nth_space (cut_thread_info t_info (Z.of_nat i) s Hi Hh) i =
    cut_space (Znth (Z.of_nat i) (heap_spaces (ti_heap t_info))) s Hh.
Proof.
  intros. rewrite nth_space_Znth. simpl. rewrite upd_Znth_same by assumption.
  reflexivity.
Qed.

Lemma cti_gen_size: forall t_info i s n
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s),
    gen_size (cut_thread_info t_info i s Hi Hh) n =
    gen_size t_info n.
Proof.
  intros. unfold gen_size. destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i. rewrite cti_space_eq. simpl. rewrite nth_space_Znth. reflexivity.
  - rewrite cti_space_not_eq; [reflexivity | assumption].
Qed.

Lemma cti_space_base: forall t_info i s  n
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s),
    space_base (nth_space (cut_thread_info t_info i s Hi Hh) n) =
    space_base (nth_space t_info n).
Proof.
  intros. destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i. rewrite cti_space_eq. simpl. rewrite nth_space_Znth. reflexivity.
  - rewrite cti_space_not_eq; [reflexivity | assumption].
Qed.

Lemma cti__remembered_invariant: forall t_info i s  n
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s),
    space_remembered (nth_space (cut_thread_info t_info i s Hi Hh) n) =
    space_remembered (nth_space t_info n).
Proof.
  intros.
  destruct (Z.eq_dec (Z.of_nat n) i).
  - subst i.
    rewrite cti_space_eq.
    simpl.
    now rewrite nth_space_Znth.
  - now rewrite cti_space_not_eq.
Qed.
