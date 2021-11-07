From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import Sorting.Permutation.
From Coq Require Import ZArith.ZArith.

From compcert Require Import lib.Coqlib.
From compcert Require Import lib.Integers.
From compcert Require Import common.Values.

From VST Require Import floyd.list_solver.
From VST Require Import floyd.sublist.
From VST Require Import veric.val_lemmas.

From CertiGraph Require Import lib.List_ext.

Import ListNotations.


Lemma isptr_is_pointer_or_integer: forall p, isptr p -> is_pointer_or_integer p.
Proof. intros. destruct p; try contradiction. exact I. Qed.


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


Lemma sublist_pos_cons: forall {A: Type} (lo hi: Z) (al: list A) v,
    (0 < lo)%Z -> sublist lo hi (v :: al) = sublist (lo - 1) (hi - 1) al.
Proof.
  intros. unfold_sublist_old. f_equal. 1: f_equal; lia.
  replace (Z.to_nat lo) with (S (Z.to_nat (lo - 1))) by lia.
  simpl. reflexivity.
Qed.

Lemma upd_Znth_pos_cons: forall {A: Type} (i: Z) (l: list A) v x,
    (0 < i <= Zlength l)%Z -> upd_Znth i (v :: l) x = v :: upd_Znth (i - 1) l x.
Proof.
  intros. unfold_upd_Znth_old.
  rewrite (sublist_split 0 1 i); [| |rewrite Zlength_cons]; [| lia..].
  unfold sublist at 1. simpl. rewrite !sublist_pos_cons by lia. do 4 f_equal.
  1: lia. rewrite Zlength_cons; lia.
Qed.

Lemma upd_Znth_tl {A}: forall (i: Z) (l: list A) (x: A),
    (0 <= i)%Z -> l <> nil -> tl (upd_Znth (i + 1) l x) = upd_Znth i (tl l) x.
Proof.
  intros. destruct l; simpl. 1: contradiction.
  destruct (Z_lt_le_dec i (Zlength l)).
  2: rewrite !upd_Znth_out_of_range; auto; [|rewrite Zlength_cons]; lia.
  rewrite !upd_Znth_unfold; auto. 2: rewrite Zlength_cons; lia.
  unfold_sublist_old. replace (i - 0)%Z with i by lia.
  replace (i + 1 - 0)%Z with (i + 1)%Z by lia. simpl.
  assert (forall j, 0 <= j -> Z.to_nat (j + 1) = S (Z.to_nat j))%Z by
      (intros; rewrite <- Z2Nat.inj_succ; lia).
  rewrite (H1 _ H). simpl tl. do 3 f_equal.
  - f_equal. rewrite Zlength_cons. lia.
  - remember (S (Z.to_nat i)). replace (Z.to_nat (i + 1 + 1)) with (S n).
    + simpl. reflexivity.
    + do 2 rewrite H1 by lia. subst n. reflexivity.
Qed.


Lemma Znth_skip_hd_same: forall A (d: Inhabitant A) (l: list A) a n,
    (n > 0)%Z ->
    (Zlength l > 0)%Z ->
    Znth n (a :: tl l) = Znth n l.
Proof.
  intros. destruct l.
  - rewrite Zlength_nil in H0; inversion H0.
  - repeat rewrite Znth_pos_cons by lia. reflexivity.
Qed.


Fixpoint collect_Z_indices {A} (eqdec: forall (a b: A), {a = b} + {a <> b})
         (target: A) (l: list A) (ind: Z) : list Z :=
  match l with
  | nil => nil
  | li :: l => if eqdec target li
               then ind :: collect_Z_indices eqdec target l (ind + 1)
               else collect_Z_indices eqdec target l (ind + 1)
  end.

Lemma collect_Z_indices_spec:
  forall {A} {d: Inhabitant A} eqdec (target: A) (l: list A) (ind: Z) c,
    l = skipn (Z.to_nat ind) c -> (0 <= ind)%Z ->
    forall j, In j (collect_Z_indices eqdec target l ind) <->
              (ind <= j < Zlength c)%Z /\ Znth j c = target.
Proof.
  intros. revert ind H H0 j. induction l; intros.
  - simpl. split; intros. 1: exfalso; assumption. pose proof (Zlength_skipn ind c).
    destruct H1. rewrite <- H, Zlength_nil, (Z.max_r _ _ H0) in H2. symmetry in H2.
    rewrite Z.max_l_iff in H2. lia.
  - assert (l = skipn (Z.to_nat (ind + 1)) c). {
      clear -H H0. rewrite Z2Nat.inj_add by lia. simpl Z.to_nat at 2.
      remember (Z.to_nat ind). clear ind Heqn H0.
      replace (n + 1)%nat with (S n) by lia. revert a l c H.
      induction n; intros; simpl in H; destruct c; [inversion H | | inversion H|].
      - simpl. inversion H; reflexivity.
      - apply IHn in H. rewrite H. simpl. destruct c; reflexivity. }
    assert (0 <= ind + 1)%Z by lia. specialize (IHl _ H1 H2). simpl.
    assert (Znth ind c = a). {
      clear -H H0. apply Z2Nat.id in H0. remember (Z.to_nat ind). rewrite <- H0.
      clear ind Heqn H0. revert a l c H.
      induction n; intros; simpl in H; destruct c; [inversion H | | inversion H|].
      - simpl. inversion H. rewrite Znth_0_cons. reflexivity.
      - rewrite Nat2Z.inj_succ, Znth_pos_cons by lia. apply IHn in H.
        replace (Z.succ (Z.of_nat n) - 1)%Z with (Z.of_nat n) by lia.
        assumption. }
    destruct (eqdec target a).
    + simpl. rewrite IHl. clear IHl. split; intros; destruct H4; [|intuition|].
      * subst j. split; [split|]; [lia | | rewrite <- e in H3; assumption].
        pose proof (Zlength_skipn ind c). rewrite <- H in H4.
        rewrite Zlength_cons in H4. pose proof (Zlength_nonneg l).
        destruct (Z.max_spec 0 (Zlength c - Z.max 0 ind)). 2: exfalso; lia.
        destruct H6 as [? _]. rewrite Z.max_r in H6; lia.
      * assert (ind = j \/ ind + 1 <= j < Zlength c)%Z by lia.
        destruct H6; [left | right; split]; assumption.
    + rewrite IHl; split; intros; destruct H4; split;
        [lia | assumption | | assumption].
      assert (ind = j \/ ind + 1 <= j < Zlength c)%Z by lia. clear H4. destruct H6.
      2: assumption. exfalso; subst j. rewrite H5 in H3. rewrite H3 in n.
      apply n; reflexivity.
Qed.


Definition get_indices (index: Z) (live_indices: list Z) :=
  collect_Z_indices Z.eq_dec (Znth index live_indices) live_indices 0.

Lemma get_indices_spec: forall (l: list Z) (z j : Z),
    In j (get_indices z l) <-> (0 <= j < Zlength l)%Z /\ Znth j l = Znth z l.
Proof.
  intros. unfold get_indices. remember (Znth z l) as p. clear Heqp z.
  apply collect_Z_indices_spec. 2: lia. rewrite skipn_0. reflexivity.
Qed.


Lemma fold_right_upd_Znth_Zlength {A}: forall (l: list Z) (roots: list A) (v: A),
    (forall j, In j l -> 0 <= j < Zlength roots)%Z ->
    Zlength (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) =
    Zlength roots.
Proof.
  induction l; intros; simpl. 1: reflexivity. rewrite upd_Znth_Zlength.
  - apply IHl. intros. apply H. right. assumption.
  - rewrite IHl; intros; apply H; [left; reflexivity | right; assumption].
Qed.


Lemma fold_right_upd_Znth_same {A} {d: Inhabitant A}:
  forall (l: list Z) (roots: list A) (v: A),
    (forall j, In j l -> 0 <= j < Zlength roots)%Z ->
    forall j,
      In j l ->
      Znth j (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) = v.
Proof.
  intros. induction l; simpl in H0. 1: exfalso; assumption.
  assert (Zlength (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) =
          Zlength roots) by
      (apply fold_right_upd_Znth_Zlength; intros; apply H; right; assumption).
  simpl. destruct H0.
  - subst a. rewrite upd_Znth_same. reflexivity. rewrite H1. apply H.
    left; reflexivity.
  - destruct (Z.eq_dec j a).
    + subst a. rewrite upd_Znth_same. reflexivity. rewrite H1. apply H.
      left; reflexivity.
    + rewrite upd_Znth_diff; [|rewrite H1; apply H; intuition..| assumption].
      apply IHl; [intros; apply H; right |]; assumption.
Qed.


Lemma fold_right_upd_Znth_diff {A} {d: Inhabitant A}:
  forall (l: list Z) (roots: list A) (v: A),
    (forall j, In j l -> 0 <= j < Zlength roots)%Z ->
    forall j,
      ~ In j l -> (0 <= j < Zlength roots)%Z ->
      Znth j (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) =
      Znth j roots.
Proof.
  intros. induction l; simpl. 1: reflexivity.
  assert (Zlength (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) =
          Zlength roots) by
      (apply fold_right_upd_Znth_Zlength; intros; apply H; right; assumption).
  assert (j <> a) by (intro; apply H0; left; rewrite H3; reflexivity).
  rewrite upd_Znth_diff; [ | rewrite H2.. | assumption];
    [|assumption | apply H; intuition].
  apply IHl; repeat intro; [apply H | apply H0]; right; assumption.
Qed.

Lemma Znth_list_eq {X: Type} {d: Inhabitant X}: forall (l1 l2: list X),
    l1 = l2 <-> (Zlength l1 = Zlength l2 /\
                 forall j, 0 <= j < Zlength l1 -> Znth j l1 = Znth j l2)%Z.
Proof.
  induction l1; destruct l2; split; intros.
  - split; intros; reflexivity.
  - reflexivity.
  - inversion H.
  - destruct H. rewrite Zlength_nil, Zlength_cons in H. pose proof (Zlength_nonneg l2). lia.
  - inversion H.
  - destruct H. rewrite Zlength_nil, Zlength_cons in H. pose proof (Zlength_nonneg l1). lia.
  - inversion H. subst a. subst l1. split; intros; reflexivity.
  - destruct H.
    assert (0 <= 0 < Zlength (a :: l1))%Z. { rewrite Zlength_cons. pose proof (Zlength_nonneg l1). lia. }
    apply H0 in H1. rewrite !Znth_0_cons in H1.
    subst a. rewrite !Zlength_cons in H. f_equal. rewrite IHl1. split ; try lia.
    intros. assert (0 < j + 1)%Z by lia.
    assert (0 <= j + 1 < Zlength (x :: l1))%Z. { rewrite Zlength_cons. pose proof (Zlength_nonneg l1). lia. }
    specialize (H0 _ H3). rewrite !Znth_pos_cons in H0 by assumption.
    now replace (j + 1 - 1)%Z with j in H0 by lia.
Qed.

Lemma upd_Znth_unchanged: forall {A : Type} {d : Inhabitant A} (i : Z) (l : list A),
    (0 <= i < Zlength l)%Z -> upd_Znth i l (Znth i l) = l.
Proof.
  intros. assert (Zlength (upd_Znth i l (Znth i l)) = Zlength l) by
      (rewrite upd_Znth_Zlength; [reflexivity | assumption]). rewrite Znth_list_eq.
  split. 1: assumption. intros. rewrite H0 in H1. destruct (Z.eq_dec j i).
  - subst j. rewrite upd_Znth_same; [reflexivity | assumption].
  - rewrite upd_Znth_diff; [reflexivity | assumption..].
Qed.


Lemma In_Znth {A} {d: Inhabitant A}: forall (e: A) l,
    In e l -> exists i, (0 <= i < Zlength l)%Z /\ Znth i l = e.
Proof.
  intros. apply In_nth with (d := d) in H. destruct H as [n [? ?]].
  exists (Z.of_nat n). assert (0 <= Z.of_nat n < Zlength l)%Z by
      (rewrite Zlength_correct; lia). split. 1: assumption.
  rewrite <- nth_Znth by assumption. rewrite Nat2Z.id. assumption.
Qed.

Lemma upd_Znth_In {A}: forall (e: A) l i v, In v (upd_Znth i l e) -> In v l \/ v = e.
Proof.
  intros. destruct (Z_lt_le_dec i 0). 1: rewrite upd_Znth_out_of_range in H; auto; left; lia.
  destruct (Z_lt_le_dec i (Zlength l)).
  2: { rewrite upd_Znth_out_of_range in H; auto; right; lia. }
  rewrite upd_Znth_unfold in H; auto. rewrite in_app_iff in H. simpl in H.
  destruct H as [? | [? | ?]]; [|right; rewrite H; reflexivity|];
    apply sublist_In in H; left; assumption.
Qed.

Lemma fold_right_upd_Znth_In {A}: forall (l: list Z) (roots: list A) (v: A) e,
      In e (fold_right (fun (i : Z) (rs : list A) => upd_Znth i rs v) roots l) ->
      In e roots \/ e = v.
Proof.
  induction l; intros; simpl in H. 1: left; assumption.
  apply upd_Znth_In in H. destruct H; [apply IHl | right]; assumption.
Qed.


Lemma Znth_tl {A} {d: Inhabitant A}: forall (l: list A) i,
    (0 <= i)%Z -> Znth i (tl l) = Znth (i + 1) l.
Proof.
  intros. destruct l; simpl.
  - destruct i as [|p|p] ; try lia ; try easy. unfold Znth. simpl.
    destruct (Pos.to_nat p) ; now destruct (Pos.to_nat (p + 1)).
  - rewrite Znth_pos_cons by lia. now replace (i + 1 - 1)%Z with i by lia.
Qed.

Lemma Int64_eq_false: forall x y : int64, Int64.eq x y = false -> x <> y.
Proof.
  intros. destruct x, y. unfold Int64.eq in H. simpl in H.
  destruct (zeq intval intval0). 1: inversion H. intro. inversion H0. easy.
Qed.

Lemma ltu64_repr_false: forall x y,
    (0 <= y <= Int64.max_unsigned)%Z -> (0 <= x <= Int64.max_unsigned)%Z ->
    Int64.ltu (Int64.repr x) (Int64.repr y) = false -> (x >= y)%Z.
Proof.
  intros. unfold Int64.ltu in H1. rewrite !Int64.unsigned_repr in H1; auto.
  now destruct (zlt x y).
Qed.
