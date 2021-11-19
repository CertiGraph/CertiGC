From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.util.

Import ListNotations.
Local Coercion pg_lg: LabeledGraph >-> PreGraph.


Record Addr: Type := {
    addr_gen: nat;
    addr_block: nat;
}.
Instance Addr_EqDec: EqDec Addr eq.
Proof.
    intros [gen_x block_x] [gen_y block_y].
    destruct (equiv_dec gen_x gen_y) as [ H1 | H1 ] ;
    destruct (equiv_dec block_x block_y) as [ H2 | H2 ].
    all:
      cbv in * ; subst ; try firstorder ;
      right ; intro F ; congruence.
Defined.


Record Field: Type := {
    field_addr: Addr;
    field_index: nat;
}.
Instance Field_EqDec: EqDec Field eq.
Proof.
    intros [addr_x index_x] [addr_y index_y].
    destruct (equiv_dec addr_x addr_y) as [ H1 | H1 ] ;
    destruct (equiv_dec index_x index_y) as [ H2 | H2 ].
    all:
      cbv in * ; subst ; try firstorder ;
      right ; intro F ; congruence.
Defined.


Inductive GC_Pointer := | GCPtr: block -> ptrofs -> GC_Pointer.

Definition FieldValue: Type := option (Z + GC_Pointer).

Instance FieldValue_Inhabitant: Inhabitant FieldValue := None.


Record Block : Type := {
    block_mark: bool;
    block_copied_vertex: Addr;
    block_fields: list FieldValue;
    block_color: Z;
    block_tag: Z;
    block_tag__range: (0 <= block_tag < 256)%Z;
    block_color__range: (0 <= block_color < 4)%Z;
    block_fields__range: (0 < Zlength block_fields < two_p (WORD_SIZE * 8 - 10))%Z;
    block_tag__no_scan: (NO_SCAN_TAG <= block_tag -> ~ In None block_fields)%Z;
    (* TODO: what's up with this? why can raw_f be None at all? *)
}.

Lemma block_fields__range2: forall r,
    Zlength (block_fields r) <= if Archi.ptr64 then Int64.max_signed else Int.max_signed.
Proof.
  intros. pose proof (block_fields__range r). remember (Zlength (block_fields r)).
  clear Heqz. cbv delta[Archi.ptr64]. simpl. rewrite <- Z.lt_succ_r. destruct H.
  transitivity (two_p (WORD_SIZE * 8 - 10)); auto. now vm_compute.
Qed.

Lemma block_fields__not_nil (rvb: Block):
    block_fields rvb <> nil.
Proof.
    pose proof (block_fields__range rvb) as H.
    remember (block_fields rvb) as ff eqn:E.
    clear E rvb.
    now destruct ff.
Qed.

Definition block_fields_head (rvb: Block): FieldValue
 := match block_fields rvb as l return (block_fields rvb = l -> FieldValue) with
    | nil => fun E => False_rect _ (block_fields__not_nil _ E)
    | f :: _ => fun _ => f
    end eq_refl.

Lemma block_fields_head__cons (rvb: Block):
    exists f ff, block_fields rvb = f :: ff /\ block_fields_head rvb = f.
Proof.
    refine (
        match block_fields rvb as l return (block_fields rvb = l -> _) with
        | nil => fun E => False_rect _ (block_fields__not_nil _ E)
        | f :: ff => fun E => _
        end eq_refl
    ).
    exists f, ff. destruct rvb. simpl in E. now subst.
Qed.


Record Generation: Type := {
    generation_base: val;
    generation_block_count: nat;
    generation_sh: share;
    generation_base__isptr: isptr generation_base;
    generation_sh__writable: writable_share generation_sh;
}.

Definition null_generation: Generation := {|
    generation_base := Vptr xH Ptrofs.zero;
    generation_block_count := O;
    generation_sh := Tsh;
    generation_base__isptr := I;
    generation_sh__writable := writable_share_top;
|}.

Instance Generation_Inhabitant: Inhabitant Generation := null_generation.


Record Generations : Type := {
    generations: list Generation;
    generations__not_nil: generations <> nil;
}.

Definition generations_append (gi: Generations) (gen_i: Generation):
    Generations
 := {|
    generations := generations gi +:: gen_i;
    generations__not_nil := app_not_nil (generations gi) gen_i;
|}.


Definition HeapGraph := LabeledGraph Addr Field Block unit Generations.


Definition heapgraph_block (g: HeapGraph) (v: Addr):
    Block
 := vlabel g v
.


Definition heapgraph_field_pairs (g: HeapGraph) (v: Addr):
    list (Z + (Addr * Z))
 := map (fun x => inr (v, Z.of_nat x))
        (nat_inc_list (length (block_fields (heapgraph_block g v))))
.

Lemma heapgraph_field_pairs__Zlength (g: HeapGraph) (v: Addr):
    Zlength (heapgraph_field_pairs g v) = Zlength (block_fields (heapgraph_block g v)).
Proof.
    unfold heapgraph_field_pairs.
    now rewrite Zlength_map, !Zlength_correct, nat_inc_list_length.
Qed.

Lemma heapgraph_field_pairs__Znth `[Inhabitant (Z + Addr * Z)]
    (g: HeapGraph) (v: Addr) (i : Z)
    (Hi: 0 <= i < Zlength (block_fields (heapgraph_block g v))):
    Znth i (heapgraph_field_pairs g v) = inr (v, i).
Proof.
    unfold heapgraph_field_pairs.
    assert (0 <= i < Zlength (nat_inc_list (length (block_fields (heapgraph_block g v)))))  as Hi'.
    {
        now rewrite Zlength_correct, nat_inc_list_length, <- Zlength_correct.
    }
    rewrite Znth_map by assumption.
    do 2 f_equal.
    rewrite <- nth_Znth by assumption.
    rewrite nat_inc_list_nth.
    {
        rewrite Z2Nat.id ;  lia.
    }
    rewrite <- ZtoNat_Zlength, <- Z2Nat.inj_lt; lia.
Qed.


Definition heapgraph_block_size (g: HeapGraph) (v: Addr):
    Z
 := Zlength (heapgraph_block g v).(block_fields) + 1
.

Lemma heapgraph_block_size__one (g: HeapGraph) (v: Addr):
    1 < heapgraph_block_size g v.
Proof.
    unfold heapgraph_block_size.
    pose proof (block_fields__range (heapgraph_block g v)).
    lia.
Qed.


Definition heapgraph_block_size_accum (g: HeapGraph) (gen: nat) (s: Z) (n: nat):
    Z
 := s + heapgraph_block_size g {| addr_gen := gen; addr_block := n |}
.

Lemma heapgraph_block_size_accum__mono (g: HeapGraph) (gen: nat) (s: Z) (n: nat):
    s < heapgraph_block_size_accum g gen s n.
Proof.
    unfold heapgraph_block_size_accum.
    pose proof (heapgraph_block_size__one g {| addr_gen := gen; addr_block := n |}) as H.
    lia.
Qed.

Lemma heapgraph_block_size_accum__comm (g: HeapGraph) (gen: nat) (s: Z) (n1 n2: nat):
    heapgraph_block_size_accum g gen (heapgraph_block_size_accum g gen s n1) n2 =
    heapgraph_block_size_accum g gen (heapgraph_block_size_accum g gen s n2) n1.
Proof.
    unfold heapgraph_block_size_accum.
    lia.
Qed.

Lemma heapgraph_block_size_accum__fold_lt (g: HeapGraph) (gen: nat) (s: Z) (l: list nat)
    (Hl: l <> nil):
    s < fold_left (heapgraph_block_size_accum g gen) l s.
Proof.
    apply (fold_left_Z_mono_strict (heapgraph_block_size_accum g gen) nil l l) ; try assumption.
    + apply heapgraph_block_size_accum__mono.
    + apply heapgraph_block_size_accum__comm.
    + apply Permutation_refl.
Qed.

Lemma heapgraph_block_size_accum__fold_le (g: HeapGraph) (gen: nat) (s: Z) (l: list nat):
    s <= fold_left (heapgraph_block_size_accum g gen) l s.
Proof.
    destruct l as [|n l] ; try easy.
    rewrite Z.le_lteq.
    left.
    now apply heapgraph_block_size_accum__fold_lt.
Qed.

Lemma heapgraph_block_size_accum__fold_left (g : HeapGraph) (gen : nat) (l : list nat) (z1 z2 : Z):
    fold_left (heapgraph_block_size_accum g gen) l (z2 + z1) =
    fold_left (heapgraph_block_size_accum g gen) l z2 + z1.
Proof.
    revert z1 z2 ; induction l as [| s l IHl] ; intros z1 z2 ; simpl ; try easy.
    rewrite <- IHl.
    f_equal.
    unfold heapgraph_block_size_accum. lia.
Qed.


Definition heapgraph_block_size_prev (g: HeapGraph) (gen i: nat):
    Z
 := fold_left (heapgraph_block_size_accum g gen) (nat_inc_list i) 0
.

 Lemma heapgraph_block_size_prev__S (g: HeapGraph) (gen i: nat):
    heapgraph_block_size_prev g gen (S i) =
    heapgraph_block_size_prev g gen i + heapgraph_block_size g {| addr_gen := gen; addr_block := i |}.
Proof.
    unfold heapgraph_block_size_prev at 1.
    now rewrite nat_inc_list_S, fold_left_app.
Qed.

Lemma heapgraph_block_size_prev__nonneg (g: HeapGraph) (gen i: nat):
    0 <= heapgraph_block_size_prev g gen i.
Proof.
    unfold heapgraph_block_size_prev.
    apply heapgraph_block_size_accum__fold_le.
Qed.

Lemma heapgraph_block_size_prev__mono_strict (g: HeapGraph) (gen i j: nat)
    (Hij: (i < j)%nat):
    (heapgraph_block_size_prev g gen i < heapgraph_block_size_prev g gen j).
Proof.
    assert (j = i + (j - i))%nat as Hij' by lia. rewrite Hij'.
    remember (j - i)%nat as n eqn:En. subst j.
    unfold heapgraph_block_size_prev. rewrite nat_inc_list_app, fold_left_app.
    apply heapgraph_block_size_accum__fold_lt.
    pose proof (nat_seq_length i n) as Hin.
    destruct (nat_seq i n) ; try easy.
    simpl in Hin. lia.
Qed.

Lemma heapgraph_block_size_prev__mono (g: HeapGraph) (gen i j: nat)
    (Hij: (i <= j)%nat):
    heapgraph_block_size_prev g gen i <= heapgraph_block_size_prev g gen j.
Proof.
    rewrite Nat.le_lteq in Hij.
    destruct Hij as [Hij|Hij].
    + rewrite Z.le_lteq. left. now apply heapgraph_block_size_prev__mono_strict.
    + subst. lia.
Qed.

Lemma heapgraph_block_size_prev__lt_rev (g: HeapGraph) (gen i j: nat)
    (Hij: heapgraph_block_size_prev g gen i < heapgraph_block_size_prev g gen j):
    (i < j)%nat.
Proof.
    destruct (le_lt_dec j i) as [Hij'|Hij'] ; try easy.
    apply (heapgraph_block_size_prev__mono g gen) in Hij'.
    lia.
Qed.


Definition heapgraph_generations (g: HeapGraph):
    Generations
 := g.(glabel)
.


Definition heapgraph_generation (g: HeapGraph) (gen: nat):
    Generation
 := nth gen (heapgraph_generations g).(generations) null_generation
.


Definition heapgraph_generation_block_count (g: HeapGraph) (gen: nat):
    nat
 := generation_block_count (heapgraph_generation g gen)
.

Lemma heapgraph_generation_block_count__labeledgraph_gen_dst (g: HeapGraph) (e: Field) (v: Addr) (to: nat):
    heapgraph_generation_block_count (labeledgraph_gen_dst g e v) to = heapgraph_generation_block_count g to.
Proof. reflexivity. Qed.


Definition heapgraph_generation_sh (g: HeapGraph) (gen: nat): share
 := generation_sh (heapgraph_generation g gen)
.


Definition heapgraph_has_gen (g: HeapGraph) (n: nat):
    Prop
 := (n < length (heapgraph_generations g).(generations))%nat
.

Definition heapgraph_has_gen_dec g n:
    {heapgraph_has_gen g n} + {~ heapgraph_has_gen g n}
 := lt_dec n (length (generations (heapgraph_generations g)))
.

Lemma heapgraph_has_gen__O (g: HeapGraph):
    heapgraph_has_gen g O.
Proof.
    hnf.
    destruct (generations (heapgraph_generations g)) as [|x xx] eqn:E ; simpl; try lia.
    now pose proof (generations__not_nil (heapgraph_generations g)).
Qed.


Definition heapgraph_generation_has_index (g: HeapGraph) (gen index: nat):
    Prop
 := (index < generation_block_count (heapgraph_generation g gen))%nat
.


Definition heapgraph_block_offset (g: HeapGraph) (v: Addr):
  Z
 := heapgraph_block_size_prev g (addr_gen v) (addr_block v) + 1
.


Definition heapgraph_generation_size (g: HeapGraph) (gen: nat):
    Z
 := heapgraph_block_size_prev g gen (generation_block_count (heapgraph_generation g gen))
.

Lemma heapgraph_block_offset__heapgraph_generation_size (g: HeapGraph) (v: Addr)
    (Hgv: heapgraph_generation_has_index g (addr_gen v) (addr_block v)):
    heapgraph_block_offset g v < heapgraph_generation_size g (addr_gen v).
Proof.
    unfold heapgraph_block_offset, heapgraph_generation_size. red in Hgv.
    remember (generation_block_count (heapgraph_generation g (addr_gen v))) as n eqn:En.
    remember (addr_gen v) as gen eqn:Egen.
    assert (S (addr_block v) <= n)%nat by lia.
    apply Z.lt_le_trans with (heapgraph_block_size_prev g gen (S (addr_block v))).
    + rewrite heapgraph_block_size_prev__S. apply Zplus_lt_compat_l, heapgraph_block_size__one.
    + now apply heapgraph_block_size_prev__mono.
Qed.


Definition heapgraph_generations_append (g: HeapGraph) (gen_i: Generation):
    HeapGraph
 := {|
    pg_lg := pg_lg g;
    vlabel := heapgraph_block g;
    elabel := elabel g;
    glabel := generations_append (heapgraph_generations g) gen_i;
|}.

Lemma heapgraph_has_gen__heapgraph_generations_append (g: HeapGraph) (gi: Generation) (gen: nat):
    heapgraph_has_gen (heapgraph_generations_append g gi) gen <->
    heapgraph_has_gen g gen \/ gen = length (generations (heapgraph_generations g)).
Proof.
    unfold heapgraph_has_gen ; simpl.
    rewrite app_length ; simpl.
    lia.
Qed.

Lemma heapgraph_generation__heapgraph_generations_append__old (g : HeapGraph) (gi : Generation) (gen : nat)
    (Hgen: heapgraph_has_gen g gen):
    heapgraph_generation (heapgraph_generations_append g gi) gen = heapgraph_generation g gen.
Proof.
    unfold heapgraph_generation ; simpl.
    now rewrite app_nth1.
Qed.

Lemma heapgraph_generation__heapgraph_generations_append__new (g: HeapGraph) (gi: Generation):
    heapgraph_generation (heapgraph_generations_append g gi) (length (generations (heapgraph_generations g))) = gi.
Proof.
    unfold heapgraph_generation ; simpl.
    rewrite app_nth2 by lia.
    now rewrite Nat.sub_diag.
Qed.


Definition heapgraph_generation_base (g: HeapGraph) (gen: nat):
    val
 := if heapgraph_has_gen_dec g gen
    then generation_base (heapgraph_generation g gen)
    else Vundef
.

Lemma heapgraph_generation_base__isptr (g: HeapGraph) (n: nat)
    (Hgn: heapgraph_has_gen g n):
    isptr (heapgraph_generation_base g n).
Proof.
    unfold heapgraph_generation_base.
    if_tac ; try easy.
    apply generation_base__isptr.
Qed.


Definition heapgraph_block_ptr (g: HeapGraph) (v: Addr):
    val
 := offset_val
      (WORD_SIZE * heapgraph_block_offset g v)
      (heapgraph_generation_base g (addr_gen v))
.

Lemma heapgraph_block_ptr__eq (g1 g2: HeapGraph) (v: Addr)
    (Hv: forall v, heapgraph_block g1 v = heapgraph_block g2 v)
    (Hg1g2: map generation_base (heapgraph_generations g1).(generations) = map generation_base (heapgraph_generations g2).(generations)):
    heapgraph_block_ptr g1 v = heapgraph_block_ptr g2 v.
Proof.
    unfold heapgraph_block_ptr. f_equal.
    {
      f_equal. unfold heapgraph_block_offset. f_equal.
      remember (addr_block v) as n eqn:En. clear En.
      induction n as [|n IHn] ; simpl ; auto.
      rewrite !heapgraph_block_size_prev__S, IHn. f_equal.
      unfold heapgraph_block_size.
      now rewrite Hv.
    }
    {
      assert (forall gen, heapgraph_has_gen g1 gen <-> heapgraph_has_gen g2 gen) as Hgen.
      {
        intro gen. unfold heapgraph_has_gen.
        assert (length (generations (heapgraph_generations g1)) = length (generations (heapgraph_generations g2))) as E.
        {
          now rewrite <- !(map_length generation_base), Hg1g2.
        }
        lia.
      }
      unfold heapgraph_generation_base.
      do 2 if_tac ; rewrite Hgen in H ; try easy.
      unfold heapgraph_generation.
      now rewrite <- !(map_nth generation_base), Hg1g2.
    }
Qed.


Definition heapgraph_block_header (g: HeapGraph) (v: Addr):
    Z
 := let vb := heapgraph_block g v
 in if vb.(block_mark)
    then 0
    else vb.(block_tag) + (Z.shiftl vb.(block_color) 8) + (Z.shiftl (Zlength vb.(block_fields)) 10).

Lemma heapgraph_block_header__iff (g: HeapGraph) (v: Addr):
    heapgraph_block_header g v = 0 <-> block_mark (heapgraph_block g v) = true.
Proof.
    unfold heapgraph_block_header. destruct (block_mark (heapgraph_block g v)) ; try easy.
    split ; intro H ; try easy.
    pose proof (proj1 (block_fields__range (heapgraph_block g v))) as Hfields.
    assert (Z.shiftl (Zlength (block_fields (heapgraph_block g v))) 10 = 0) as F.
    {
      assert (0 <= Z.shiftl (block_color (heapgraph_block g v)) 8) as Hshift__color.
      {
        pose proof (proj1 (block_color__range (heapgraph_block g v))) as Hcolor.
        now rewrite Z.shiftl_nonneg.
      }
      pose proof (proj1 (block_tag__range (heapgraph_block g v))) as Htag.
      remember (Zlength (block_fields (heapgraph_block g v))) as z eqn:Ez ; clear Ez.
      assert (0 <= Z.shiftl z 10) as F'.
      {
        apply Z.shiftl_nonneg.
        lia.
      }
      lia.
    }
    rewrite Z.shiftl_eq_0_iff in F ; lia.
Qed.

Lemma heapgraph_block_header__range (g: HeapGraph) (v: Addr):
    0 <= heapgraph_block_header g v < two_p (WORD_SIZE * 8).
Proof.
    unfold heapgraph_block_header. destruct (block_mark (heapgraph_block g v)).
    {
      pose proof (two_p_gt_ZERO (WORD_SIZE * 8)).
      unfold WORD_SIZE in *.
      lia.
    }
    pose proof (block_tag__range (heapgraph_block g v)) as Htag.
    pose proof (block_color__range (heapgraph_block g v)) as Hcolor.
    pose proof (block_fields__range (heapgraph_block g v)) as Hfields.
    remember (block_tag (heapgraph_block g v)) as z1 eqn:Ez1 ; clear Ez1.
    remember (block_color (heapgraph_block g v)) as z2 eqn:Ez2 ; clear Ez2.
    remember (Zlength (block_fields (heapgraph_block g v))) as z3 eqn:Ez3 ; clear Ez3.
    assert (0 <= 8) as Hz2 by lia. apply (Zbits.Zshiftl_mul_two_p z2) in Hz2. rewrite Hz2. clear Hz2.
    assert (0 <= 10) as Hz3 by lia. apply (Zbits.Zshiftl_mul_two_p z3) in Hz3. rewrite Hz3. clear Hz3.
    assert (two_p 10 > 0) as Htwo_p10 by (apply two_p_gt_ZERO; lia).
    assert (two_p 8 > 0) as Htwo_p8 by (apply two_p_gt_ZERO; lia).
    split.
    {
      assert (0 <= z2 * two_p 8) as Hz2' by (apply Z.mul_nonneg_nonneg; lia).
      assert (0 <= z3 * two_p 10) as Hz3' by (apply Z.mul_nonneg_nonneg; lia).
      lia.
    }
    change 256 with (two_p 8) in Htag.
    change 4 with (two_p 2) in Hcolor.
    assert (z1 <= two_p 8 - 1) as Hz1' by lia. clear Htag.
    assert (z2 <= two_p 2 - 1) as Hz2' by lia. clear Hcolor.
    assert (z3 <= two_p (WORD_SIZE * 8 - 10) - 1) as Hz3' by lia. clear Hfields.
    apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in Hz1' ; try lia.
    apply Z.mul_le_mono_nonneg_r with (p := two_p 10) in Hz3' ; try lia.
    rewrite Z.mul_sub_distr_r, Z.mul_1_l in Hz1', Hz3'.
    assert (0 <= WORD_SIZE * 8 - 10) as Hwordsize by (unfold WORD_SIZE; lia).
    rewrite <- two_p_is_exp in Hz1', Hz3' by lia ; clear Hwordsize.
    simpl Z.add in Hz1', Hz3'.
    Opaque two_p. simpl. Transparent two_p.
    remember (two_p 2) as x eqn:E ; cbv in E ; subst x.
    remember (two_p 8) as x eqn:E ; cbv in E ; subst x.
    remember (two_p 10) as x eqn:E ; cbv in E ; subst x.
    remember (two_p 16) as x eqn:E ; cbv in E ; subst x.
    remember (two_p 64) as x eqn:E ; cbv in E ; subst x.
    lia.
Qed.

Lemma heapgraph_block_header__repr_iff (g: HeapGraph) (v: Addr):
    (if Archi.ptr64
        then Int64.repr (heapgraph_block_header g v) = Int64.repr 0
        else Int.repr (heapgraph_block_header g v) = Int.repr 0) <->
    block_mark (heapgraph_block g v) = true.
Proof.
    rewrite <- heapgraph_block_header__iff.
    split ; intro H ; [|rewrite H; reflexivity].
    cbv delta [Archi.ptr64] in H. simpl in H.
    Transparent Int.repr Int64.repr. inversion H. Opaque Int64.repr Int.repr. clear H.
    rewrite H1.
    match goal with
    | H : Int64.Z_mod_modulus _ = _ |- _ => rewrite Int64.Z_mod_modulus_eq in H
    | H : Int.Z_mod_modulus _ = _ |- _ => rewrite Int.Z_mod_modulus_eq in H
    end.
    rewrite Z.mod_small in H1; auto.
    apply heapgraph_block_header__range.
Qed.

Lemma heapgraph_block_header__Wosize (g: HeapGraph) (v: Addr)
    (H: block_mark (heapgraph_block g v) = false):
    if Archi.ptr64
    then
      Int64.shru (Int64.repr (heapgraph_block_header g v)) (Int64.repr 10) =
      Int64.repr (Zlength (block_fields (heapgraph_block g v)))
    else
      Int.shru (Int.repr (heapgraph_block_header g v)) (Int.repr 10) =
      Int.repr (Zlength (block_fields (heapgraph_block g v))).
Proof.
    cbv delta [Archi.ptr64]. simpl.
    match goal with
    | |- Int64.shru _ _ = Int64.repr _ => rewrite Int64.shru_div_two_p, !Int64.unsigned_repr
    | |- Int.shru _ _ = Int.repr _ => rewrite Int.shru_div_two_p, !Int.unsigned_repr
    end.
    - f_equal. unfold heapgraph_block_header.
      remember (heapgraph_block g v) as r eqn:E. clear E.
      rewrite H, !Zbits.Zshiftl_mul_two_p by lia. rewrite Z.div_add. 2: compute; lia.
      pose proof (block_tag__range r). pose proof (block_color__range r).
      cut ((block_tag r + block_color r * two_p 8) / two_p 10 = 0). 1: intros; lia.
      apply Z.div_small. change 256 with (two_p 8) in H0. change 4 with (two_p 2) in H1.
      assert (0 <= block_tag r <= two_p 8 - 1) by lia. clear H0. destruct H2.
      assert (0 <= block_color r <= two_p 2 - 1) by lia. clear H1. destruct H3.
      assert (two_p 8 > 0) by (apply two_p_gt_ZERO; lia). split.
      + assert (0 <= block_color r * two_p 8) by (apply Z.mul_nonneg_nonneg; lia). lia.
      + apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in H3. 2: lia.
        rewrite Z.mul_sub_distr_r, <- two_p_is_exp in H3 by lia. simpl Z.add in H3. lia.
    - rep_lia.
    - pose proof (heapgraph_block_header__range g v). unfold WORD_SIZE in *.
      match goal with
      | |- context [Int64.max_unsigned] =>
        unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize
      | |- context [Int.max_unsigned] =>
        unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize
      end. simpl Z.mul in H0. rewrite two_power_nat_two_p. simpl Z.of_nat. lia.
Qed.


Definition field_t: Type := Z + GC_Pointer + Field.

Instance field_t_inhabitant: Inhabitant field_t := inl (inl Z.zero).

Definition GC_Pointer2val (x: GC_Pointer) : val :=
  match x with | GCPtr b z => Vptr b z end.

Definition field2val (g: HeapGraph) (fd: field_t) : val :=
  match fd with
  | inl (inl z) => odd_Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr e => heapgraph_block_ptr g (dst g e)
  end.


Fixpoint make_fields' (l_raw: list FieldValue) (v: Addr) (n: nat): list field_t :=
  match l_raw with
  | nil => nil
  | Some (inl z) :: l => inl (inl z) :: make_fields' l v (n + 1)
  | Some (inr ptr) :: l => inl (inr ptr) :: make_fields' l v (n + 1)
  | None :: l => inr {| field_addr := v; field_index := n |} :: make_fields' l v (n + 1)
  end.

Lemma e_in_make_fields': forall l v n e,
    In (inr e) (make_fields' l v n) -> exists s, e = {| field_addr := v; field_index := s |}.
Proof.
  induction l; intros; simpl in *. 1: exfalso; assumption. destruct a; [destruct s|].
  - simpl in H. destruct H. 1: inversion H. apply IHl with (n + 1)%nat. assumption.
  - simpl in H. destruct H. 1: inversion H. apply IHl with (n + 1)%nat. assumption.
  - simpl in H. destruct H.
    + inversion H. exists n. reflexivity.
    + apply IHl with (n + 1)%nat. assumption.
Qed.

Lemma make_fields'_eq_length: forall l v n, length (make_fields' l v n) = length l.
Proof.
  intros. revert n. induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|]; simpl; rewrite IHl; reflexivity.
Qed.

Lemma make_fields'_eq_Zlength: forall l v n, Zlength (make_fields' l v n) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct. rewrite make_fields'_eq_length. reflexivity.
Qed.

Lemma make_fields'_edge_depends_on_index:
  forall n l_raw i v e,
    0 <= Z.of_nat n < Zlength l_raw ->
    nth n (make_fields' l_raw v i) field_t_inhabitant = inr e ->
    e = {| field_addr := v; field_index := n+i |}.
Proof.
  induction n as [|n' IHn'].
  - intros. destruct l_raw as [| r l_raw]; try inversion H0.
    destruct r; [destruct s|]; simpl in H0; inversion H0;
      reflexivity.
  - intro. destruct l_raw as [| r l_raw]; try inversion 2.
    replace (S n' + i)%nat with (n' + S i)%nat by lia.
    specialize (IHn' l_raw (S i) v e).
    assert (0 <= Z.of_nat n' < Zlength l_raw) by
          (rewrite Zlength_cons, Nat2Z.inj_succ in H; lia).
      assert (nth n' (make_fields' l_raw v (S i)) field_t_inhabitant = inr e) by
        (destruct r; [destruct s|]; simpl in H2;
        replace (i + 1)%nat with (S i) in H2 by lia; assumption).
      destruct r; [destruct s|]; simpl; apply IHn'; assumption.
Qed.

Lemma make_fields'_n_doesnt_matter: forall i l v n m gcptr,
    nth i (make_fields' l v n) field_t_inhabitant = inl (inr gcptr) ->
    nth i (make_fields' l v m) field_t_inhabitant = inl (inr gcptr).
Proof.
  intros.
  unfold make_fields' in *.
  generalize dependent i.
  generalize dependent n.
  generalize dependent m.
  induction l.
  + intros; assumption.
  + induction i.
    - destruct a; [destruct s|]; simpl; intros; try assumption; try inversion H.
    - destruct a; [destruct s|]; simpl; intro;
        apply IHl with (m:=(m+1)%nat) in H; assumption.
Qed.

Lemma make_fields'_item_was_in_list: forall l v n gcptr,
    0 <= n < Zlength l ->
    Znth n (make_fields' l v 0) = inl (inr gcptr) ->
    Znth n l = Some (inr gcptr).
Proof.
  intros.
  rewrite <- nth_Znth; rewrite <- nth_Znth in H0; [| rewrite Zlength_correct in *..];
    try rewrite make_fields'_eq_length; [|assumption..].
  generalize dependent n.
  induction l.
  - intros. rewrite nth_Znth in H0; try assumption.
    unfold make_fields' in H0; rewrite Znth_nil in H0; inversion H0.
  - intro n. induction (Z.to_nat n) eqn:?.
    + intros. destruct a; [destruct s|]; simpl in *; try inversion H0; try reflexivity.
    + intros. simpl in *. clear IHn0.
      replace n0 with (Z.to_nat (Z.of_nat n0)) by apply Nat2Z.id.
      assert (0 <= Z.of_nat n0 < Zlength l). {
        split; try lia.
        destruct H; rewrite Zlength_cons in H1.
        apply Zsucc_lt_reg; rewrite <- Nat2Z.inj_succ.
        rewrite <- Heqn0; rewrite Z2Nat.id; assumption.
      }
      destruct a; [destruct s|]; simpl in H0; apply IHl;
        try assumption; apply make_fields'_n_doesnt_matter with (n:=1%nat);
        rewrite Nat2Z.id; assumption.
Qed.


Definition make_fields (g: HeapGraph) (v: Addr): list field_t :=
  make_fields' (heapgraph_block g v).(block_fields) v O.

Definition get_edges (g: HeapGraph) (v: Addr): list Field :=
  filter_sum_right (make_fields g v).


Definition no_scan (g: HeapGraph) (v: Addr):
    Prop
 := NO_SCAN_TAG <= (heapgraph_block g v).(block_tag)
.


Lemma no_scan_no_edge: forall g v, no_scan g v -> get_edges g v = nil.
Proof.
  intros. unfold no_scan in H. apply block_tag__no_scan in H. unfold get_edges.
  destruct (filter_sum_right (make_fields g v)) eqn:? . 1: reflexivity. exfalso.
  assert (In f (filter_sum_right (make_fields g v))) by (rewrite Heql; left; auto).
  rewrite <- filter_sum_right_In_iff in H0. clear l Heql. apply H. clear H.
  unfold make_fields in H0. remember (block_fields (heapgraph_block g v)). clear Heql.
  remember O. clear Heqn. revert n H0. induction l; simpl; intros; auto.
  destruct a; [destruct s|]; simpl in H0;
    [right; destruct H0; [inversion H | eapply IHl; eauto]..|left]; auto.
Qed.


Definition graph_has_v (g: HeapGraph) (v: Addr): Prop
 := heapgraph_has_gen g (addr_gen v) /\ heapgraph_generation_has_index g (addr_gen v) (addr_block v).

Lemma ang_graph_has_v: forall g gi v,
    graph_has_v g v -> graph_has_v (heapgraph_generations_append g gi) v.
Proof.
  intros. destruct v as [gen idx]. destruct H; split; simpl in *.
  - unfold heapgraph_has_gen in *. simpl. rewrite app_length. simpl. lia.
  - unfold heapgraph_generation_has_index in *. rewrite heapgraph_generation__heapgraph_generations_append__old; assumption.
Qed.

Lemma ang_graph_has_v_inv: forall g gi v,
    generation_block_count gi = O -> graph_has_v (heapgraph_generations_append g gi) v ->
    graph_has_v g v.
Proof.
  intros. destruct v as [gen idx]. destruct H0; split; simpl in *.
  - apply heapgraph_has_gen__heapgraph_generations_append in H0. destruct H0; auto. red in H1. exfalso. subst.
    rewrite heapgraph_generation__heapgraph_generations_append__new, H in H1. lia.
  - apply heapgraph_has_gen__heapgraph_generations_append in H0. red in H1. destruct H0.
    + rewrite heapgraph_generation__heapgraph_generations_append__old in H1; assumption.
    + exfalso. subst. rewrite heapgraph_generation__heapgraph_generations_append__new, H in H1. lia.
Qed.

Lemma ang_heapgraph_block_ptr_old: forall (g : HeapGraph) (gi : Generation) (v : Addr),
    graph_has_v g v ->
    heapgraph_block_ptr (heapgraph_generations_append g gi) v = heapgraph_block_ptr g v.
Proof.
  intros. unfold heapgraph_block_ptr. f_equal. unfold heapgraph_generation_base. destruct H.
  rewrite if_true by (rewrite heapgraph_has_gen__heapgraph_generations_append; left; assumption).
  rewrite if_true by assumption. rewrite heapgraph_generation__heapgraph_generations_append__old by assumption. reflexivity.
Qed.


Definition safe_to_copy_gen g from to: Prop :=
  generation_size from <= generation_size to - heapgraph_generation_size g to.

Definition safe_to_copy (g: HeapGraph): Prop :=
  forall n, heapgraph_has_gen g (S n) -> safe_to_copy_gen g n (S n).

Definition safe_to_copy_to_except (g: HeapGraph) (gen: nat): Prop :=
  forall n, n <> O -> n <> gen -> heapgraph_has_gen g n -> safe_to_copy_gen g (pred n) n .

Lemma stc_stcte_O_iff: forall g, safe_to_copy g <-> safe_to_copy_to_except g O.
Proof.
  intros. unfold safe_to_copy, safe_to_copy_to_except. split; intros.
  - destruct n. 1: contradiction. simpl. apply H; assumption.
  - specialize (H (S n)). simpl in H. apply H; auto.
Qed.

Lemma safe_to_copy_complete: forall g i,
    safe_to_copy_to_except g (S i) -> safe_to_copy_gen g i (S i) -> safe_to_copy g.
Proof.
  intros. unfold safe_to_copy_to_except in H. unfold safe_to_copy. intros.
  destruct (Nat.eq_dec n i).
  - subst. assumption.
  - specialize (H (S n)). simpl in H. apply H; auto.
Qed.


Definition graph_has_e (g: HeapGraph) (e: Field): Prop :=
  let v := field_addr e in graph_has_v g v /\ In e (get_edges g v).

Definition gen2gen_no_edge (g: HeapGraph) (gen1 gen2: nat): Prop :=
  forall vidx eidx, let e := {| field_addr := {| addr_gen := gen1; addr_block := vidx |}; field_index := eidx |} in
                    graph_has_e g e -> addr_gen (dst g e) <> gen2.

Definition no_edge2gen (g: HeapGraph) (gen: nat): Prop :=
  forall another, another <> gen -> gen2gen_no_edge g another gen.

Definition no_backward_edge (g: HeapGraph): Prop :=
  forall gen1 gen2, (gen1 > gen2)%nat -> gen2gen_no_edge g gen1 gen2
.

Definition graph_gen_clear (g: HeapGraph) (gen: nat):
  Prop
 := generation_block_count (heapgraph_generation g gen) = O
.


Definition firstn_gen_clear (g: HeapGraph) (n: nat): Prop :=
  forall i, (i < n)%nat -> graph_gen_clear g i.

Lemma fgc_nbe_no_edge2gen: forall g n,
    firstn_gen_clear g n -> no_backward_edge g -> no_edge2gen g n.
Proof.
  intros. red in H, H0 |-* . intros. red. intros. destruct H2. simpl in *.
  destruct (lt_eq_lt_dec another n) as [[?|?]|?]. 2: contradiction.
  - specialize (H _ l). red in H. destruct H2. simpl in *.
    red in H4. rewrite H in H4. lia.
  - assert (another > n)%nat by lia. specialize (H0 _ _ H4). apply H0.
    split; simpl; assumption.
Qed.

Lemma firstn_gen_clear_add: forall g gi i,
    heapgraph_has_gen g (Z.to_nat i) -> firstn_gen_clear g (Z.to_nat i) ->
    firstn_gen_clear (heapgraph_generations_append g gi) (Z.to_nat i).
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros. specialize (H0 _ H1).
  rewrite heapgraph_generation__heapgraph_generations_append__old; auto. unfold heapgraph_has_gen in *. lia.
Qed.


Definition egeneration (e: Field): nat := addr_gen (field_addr e).


Definition no_dangling_dst (g: HeapGraph): Prop :=
  forall v, graph_has_v g v ->
            forall e, In e (get_edges g v) -> graph_has_v g (dst g e).

Lemma get_edges_In: forall g v s,
    In {| field_addr := v; field_index := s|} (get_edges g v) <-> In s (map field_index (get_edges g v)).
Proof.
  intros. unfold get_edges, make_fields. remember (block_fields (heapgraph_block g v)).
  remember O as n. clear Heqn Heql. revert n. induction l; intros; simpl ; try easy.
  destruct a as [a|] ; try destruct a as [a|a] ; simpl.
  all: rewrite IHl ; try easy.
  intuition. inversion H0. left; reflexivity.
Qed.

Lemma get_edges_fst: forall g v e, In e (get_edges g v) -> field_addr e = v.
Proof.
  intros g v e. unfold get_edges, make_fields. remember (block_fields (heapgraph_block g v)).
  remember O as n. clear Heqn Heql. revert n. induction l; intros; simpl in *.
  - exfalso; assumption.
  - destruct a; [destruct s|]; simpl in *;
      [| | destruct H; [subst e; simpl; reflexivity|]]; apply IHl in H; assumption.
Qed.


Definition v_in_range (v: val) (start: val) (n: Z): Prop :=
  exists i, 0 <= i < n /\ v = offset_val i start.


Lemma make_fields_eq_length: forall g v,
    Zlength (make_fields g v) = Zlength (block_fields (heapgraph_block g v)).
Proof.
  unfold make_fields. intros.
  rewrite !Zlength_correct, make_fields'_eq_length. reflexivity.
Qed.

Lemma make_fields_Znth_edge: forall g v n e,
    0 <= n < Zlength (block_fields (heapgraph_block g v)) ->
    Znth n (make_fields g v) = inr e -> e = {| field_addr := v; field_index := Z.to_nat n |}.
Proof.
  intros. rewrite <- nth_Znth in H0. 2: rewrite make_fields_eq_length; assumption.
  apply make_fields'_edge_depends_on_index in H0.
  - now rewrite Nat.add_0_r in H0.
  - now rewrite Z2Nat.id.
Qed.

Lemma make_fields_edge_unique: forall g e v1 v2 n m,
    0 <= n < Zlength (make_fields g v1) ->
    0 <= m < Zlength (make_fields g v2) ->
    Znth n (make_fields g v1) = inr e ->
    Znth m (make_fields g v2) = inr e ->
    n = m /\ v1 = v2.
Proof.
  intros. unfold make_fields in *.
  rewrite make_fields'_eq_Zlength in *.
  assert (0 <= Z.of_nat (Z.to_nat n) < Zlength (block_fields (heapgraph_block g v1))) by
      (destruct H; split; rewrite Z2Nat.id; assumption).
  rewrite <- nth_Znth in H1 by
      (rewrite make_fields'_eq_Zlength; assumption).
  assert (0 <= Z.of_nat (Z.to_nat m) < Zlength (block_fields (heapgraph_block g v2))) by
       (destruct H0; split; rewrite Z2Nat.id; assumption).
  rewrite <- nth_Znth in H2 by
      (rewrite make_fields'_eq_Zlength; assumption).
  pose proof (make_fields'_edge_depends_on_index
                (Z.to_nat n) (block_fields (heapgraph_block g v1)) 0 v1 e H3 H1).
  pose proof (make_fields'_edge_depends_on_index
                (Z.to_nat m) (block_fields (heapgraph_block g v2)) 0 v2 e H4 H2).
  rewrite H5 in H6. inversion H6.
  rewrite Nat.add_cancel_r, Z2Nat.inj_iff in H9 by lia.
  split; [assumption | reflexivity].
Qed.


Definition make_fields_vals (g: HeapGraph) (v: Addr): list val :=
  let vb := heapgraph_block g v in
  let original_fields_val := map (field2val g) (make_fields g v) in
  if vb.(block_mark)
  then heapgraph_block_ptr g vb.(block_copied_vertex) :: tl original_fields_val
  else original_fields_val.

Lemma fields_eq_length: forall g v,
    Zlength (make_fields_vals g v) = Zlength (block_fields (heapgraph_block g v)).
Proof.
  intros. rewrite !Zlength_correct. f_equal. unfold make_fields_vals, make_fields.
  destruct (block_mark (heapgraph_block g v)).
  - destruct (block_fields_head__cons (heapgraph_block g v)) as [r [l [? ?]]].
    rewrite H; simpl; destruct r; [destruct s|]; simpl;
      rewrite map_length, make_fields'_eq_length; reflexivity.
  - rewrite map_length, make_fields'_eq_length. reflexivity.
Qed.

Lemma mfv_unmarked_all_is_ptr_or_int: forall (g : HeapGraph) (v : Addr),
    no_dangling_dst g -> graph_has_v g v ->
    Forall is_pointer_or_integer (map (field2val g) (make_fields g v)).
Proof.
  intros. rewrite Forall_forall. intros f ?. apply list_in_map_inv in H1.
  destruct H1 as [x [? ?]]. destruct x as [[? | ?] | ?]; simpl in H1; subst.
  - unfold odd_Z2val. exact I.
  - destruct g0. exact I.
  - apply isptr_is_pointer_or_integer. unfold heapgraph_block_ptr.
    rewrite isptr_offset_val. apply heapgraph_generation_base__isptr.
    apply filter_sum_right_In_iff, H in H2; [destruct H2|]; assumption.
Qed.

Definition copy_compatible (g: HeapGraph): Prop :=
  forall v, graph_has_v g v -> (heapgraph_block g v).(block_mark) = true ->
            graph_has_v g (heapgraph_block g v).(block_copied_vertex) /\
            addr_gen v <> addr_gen (heapgraph_block g v).(block_copied_vertex).

Lemma lgd_copy_compatible: forall g v' e,
    copy_compatible g ->
    copy_compatible (labeledgraph_gen_dst g e v').
Proof.
  intros. unfold copy_compatible in *. intuition.
Qed.


Definition heapgraph_generation_is_unmarked (g: HeapGraph) (gen: nat):
    Prop
 := heapgraph_has_gen g gen ->
    forall idx,
    heapgraph_generation_has_index g gen idx ->
    (heapgraph_block g {| addr_gen := gen; addr_block := idx |}).(block_mark) = false
.


Definition graph_unmarked (g: HeapGraph): Prop := forall v,
    graph_has_v g v -> block_mark (heapgraph_block g v) = false.

Lemma graph_heapgraph_generation_is_unmarked_iff: forall g,
    graph_unmarked g <-> forall gen, heapgraph_generation_is_unmarked g gen.
Proof.
  intros. unfold graph_unmarked, heapgraph_generation_is_unmarked. split; intros.
  - apply H. unfold graph_has_v. simpl. split; assumption.
  - destruct v as [gen idx]. destruct H0. simpl in *. apply H; assumption.
Qed.

Lemma graph_unmarked_copy_compatible: forall g,
    graph_unmarked g -> copy_compatible g.
Proof.
  intros. red in H |-* . intros. apply H in H0. rewrite H0 in H1. inversion H1.
Qed.


Lemma mfv_all_is_ptr_or_int: forall g v,
    copy_compatible g -> no_dangling_dst g -> graph_has_v g v ->
    Forall is_pointer_or_integer (make_fields_vals g v).
Proof.
  intros. rewrite Forall_forall. intros f ?. unfold make_fields_vals in H2.
  pose proof (mfv_unmarked_all_is_ptr_or_int _ _ H0 H1). rewrite Forall_forall in H3.
  specialize (H3 f). destruct (block_mark (heapgraph_block g v)) eqn:? . 2: apply H3; assumption.
  simpl in H2. destruct H2. 2: apply H3, In_tail; assumption.
  subst f. unfold heapgraph_block_ptr. apply isptr_is_pointer_or_integer.
  rewrite isptr_offset_val. apply heapgraph_generation_base__isptr, (proj1 (H _ H1 Heqb)).
Qed.



Lemma make_fields_the_same: forall (g1 g2: HeapGraph) v,
    (forall e, dst g1 e = dst g2 e) ->
    (forall v, heapgraph_block g1 v = heapgraph_block g2 v) ->
    map generation_base (heapgraph_generations g1).(generations) = map generation_base (heapgraph_generations g2).(generations) ->
    make_fields_vals g1 v = make_fields_vals g2 v.
Proof.
  intros. unfold make_fields_vals, make_fields. remember O. clear Heqn. rewrite H0.
  remember (block_fields (heapgraph_block g2 v)) as l. clear Heql.
  cut (forall fl, map (field2val g1) fl = map (field2val g2) fl).
  - intros. rewrite H2. rewrite (heapgraph_block_ptr__eq g1 g2) by assumption.
    reflexivity.
  - apply map_ext. intros. unfold field2val. destruct a. 1: reflexivity.
    rewrite H. apply heapgraph_block_ptr__eq; assumption.
Qed.


Definition unmarked_gen_size (g: HeapGraph) (gen: nat) :=
  fold_left (heapgraph_block_size_accum g gen)
            (filter (fun i => negb (heapgraph_block g {| addr_gen := gen; addr_block := i |}).(block_mark))
                    (nat_inc_list (generation_block_count (heapgraph_generation g gen)))) 0.

Lemma unmarked_gen_size_le: forall g n, unmarked_gen_size g n <= heapgraph_generation_size g n.
Proof.
  intros g gen. unfold unmarked_gen_size, heapgraph_generation_size, heapgraph_block_size_prev.
  apply fold_left_mono_filter;
    [intros; rewrite Z.le_lteq; left; apply heapgraph_block_size_accum__mono | apply heapgraph_block_size_accum__comm].
Qed.

Lemma single_unmarked_le: forall g v,
    graph_has_v g v -> block_mark (heapgraph_block g v) = false ->
    heapgraph_block_size g v <= unmarked_gen_size g (addr_gen v).
Proof.
  intros. unfold unmarked_gen_size.
  remember (filter (fun i : nat => negb (block_mark (heapgraph_block g {| addr_gen := addr_gen v; addr_block := i |})))
                   (nat_inc_list (generation_block_count (heapgraph_generation g (addr_gen v))))).
  assert (In (addr_block v) l). {
    subst l. rewrite filter_In. split.
    - rewrite nat_inc_list_In_iff. apply (proj2 H).
    - destruct v; simpl. rewrite negb_true_iff. apply H0. }
  apply In_Permutation_cons in H1. destruct H1 as [l1 ?]. symmetry in H1.
  change (addr_block v :: l1) with ([addr_block v] ++ l1) in H1.
  transitivity (fold_left (heapgraph_block_size_accum g (addr_gen v)) [addr_block v] 0).
  - simpl. destruct v; simpl. apply Z.le_refl.
  - apply (fold_left_Z_mono (heapgraph_block_size_accum g (addr_gen v)) [addr_block v] l1 l 0);
      [intros; apply Z.le_lteq; left; apply heapgraph_block_size_accum__mono | apply heapgraph_block_size_accum__comm | apply H1].
Qed.


Lemma heapgraph_block_header__heapgraph_generations_append: forall g gi v,
    heapgraph_block_header g v = heapgraph_block_header (heapgraph_generations_append g gi) v.
Proof. intros. unfold heapgraph_block_header. reflexivity. Qed.

Lemma ang_make_fields_vals_old: forall g gi v,
    graph_has_v g v -> copy_compatible g -> no_dangling_dst g ->
    make_fields_vals g v = make_fields_vals (heapgraph_generations_append g gi) v.
Proof.
  intros. unfold make_fields_vals. simpl.
  assert (map (field2val g) (make_fields g v) =
          map (field2val (heapgraph_generations_append g gi))
              (make_fields (heapgraph_generations_append g gi) v)). {
    unfold make_fields. simpl. apply map_ext_in. intros.
    destruct a; [destruct s|]; simpl; auto. rewrite ang_heapgraph_block_ptr_old; auto.
    red in H1. apply (H1 v); auto. unfold get_edges.
    rewrite <- filter_sum_right_In_iff. assumption. } rewrite <- H2.
  destruct (block_mark (heapgraph_block g v)) eqn:?; auto. f_equal.
  rewrite ang_heapgraph_block_ptr_old; auto. destruct (H0 _ H Heqb). assumption.
Qed.

Lemma ang_graph_gen_size_old: forall g gi gen,
    heapgraph_has_gen g gen -> heapgraph_generation_size g gen =
                           heapgraph_generation_size (heapgraph_generations_append g gi) gen.
Proof.
  intros. unfold heapgraph_generation_size. rewrite heapgraph_generation__heapgraph_generations_append__old by assumption.
  apply fold_left_ext. intros. unfold heapgraph_block_size_accum. reflexivity.
Qed.

Lemma stcte_add: forall g gi i,
    generation_block_count gi = O -> safe_to_copy_to_except g i ->
    safe_to_copy_to_except (heapgraph_generations_append g gi) i.
Proof.
  intros. unfold safe_to_copy_to_except in *. intros. rewrite heapgraph_has_gen__heapgraph_generations_append in H3.
  destruct H3.
  - specialize (H0 _ H1 H2 H3). unfold safe_to_copy_gen in *.
    rewrite <- ang_graph_gen_size_old; assumption.
  - unfold safe_to_copy_gen. simpl. unfold heapgraph_generation_size.
    rewrite H3 at 4. rewrite heapgraph_generation__heapgraph_generations_append__new, H. unfold heapgraph_block_size_prev.
    simpl. destruct n. 1: contradiction. simpl. rewrite Z.sub_0_r.
    apply generation_size_le_S.
Qed.

Lemma graph_unmarked_add: forall g gi,
    generation_block_count gi = O -> graph_unmarked g ->
    graph_unmarked (heapgraph_generations_append g gi).
Proof.
  intros. unfold graph_unmarked in *. intros. apply ang_graph_has_v_inv in H1; auto.
  simpl. apply H0. assumption.
Qed.

Lemma ang_get_edges: forall g gi v,
    get_edges g v = get_edges (heapgraph_generations_append g gi) v.
Proof. intros. unfold get_edges, make_fields. simpl. reflexivity. Qed.

Lemma no_backward_edge_add: forall g gi,
    generation_block_count gi = O -> no_backward_edge g ->
    no_backward_edge (heapgraph_generations_append g gi).
Proof.
  intros. unfold no_backward_edge, gen2gen_no_edge in *. intros. simpl.
  destruct H2. simpl in *. rewrite <- ang_get_edges in H3.
  apply ang_graph_has_v_inv in H2; auto. apply H0; auto. split; simpl; auto.
Qed.

Lemma no_dangling_dst_add: forall g gi,
    generation_block_count gi = O -> no_dangling_dst g ->
    no_dangling_dst (heapgraph_generations_append g gi).
Proof.
  intros. unfold no_dangling_dst in *. intros. simpl.
  apply ang_graph_has_v_inv in H1; auto. rewrite <- ang_get_edges in H2.
  apply ang_graph_has_v, (H0 v); auto.
Qed.


Lemma lgd_graph_has_v: forall g e v v',
    graph_has_v g v <-> graph_has_v (labeledgraph_gen_dst g e v') v.
Proof. reflexivity. Qed.

Lemma lgd_graph_has_gen: forall g e v x,
    heapgraph_has_gen (labeledgraph_gen_dst g e v) x <-> heapgraph_has_gen g x.
Proof. intros; unfold heapgraph_has_gen; intuition. Qed.

Lemma lgd_raw_fld_length_eq: forall (g: HeapGraph) v e v',
    Zlength (block_fields (heapgraph_block g v)) =
    Zlength (block_fields (heapgraph_block (labeledgraph_gen_dst g e v') v)).
Proof. reflexivity. Qed.

Lemma lgd_heapgraph_block_ptr_eq: forall g e v' x,
    heapgraph_block_ptr (labeledgraph_gen_dst g e v') x = heapgraph_block_ptr g x.
Proof. reflexivity. Qed.

Lemma lgd_make_fields_eq: forall (g : HeapGraph) (v v': Addr) e,
    make_fields (labeledgraph_gen_dst g e v') v = make_fields g v.
Proof. reflexivity. Qed.

Lemma heapgraph_block_header__labeledgraph_gen_dst: forall g e v' x,
    heapgraph_block_header g x = heapgraph_block_header (labeledgraph_gen_dst g e v') x.
Proof. reflexivity. Qed.

Lemma lgd_block_mark_eq: forall (g: HeapGraph) e (v v' : Addr),
    block_mark (heapgraph_block g v) = block_mark (heapgraph_block (labeledgraph_gen_dst g e v') v).
Proof. reflexivity. Qed.

Lemma lgd_dst_old: forall (g: HeapGraph) e v e',
    e <> e' -> dst (labeledgraph_gen_dst g e v) e' = dst g e'.
Proof.
  intros. simpl. unfold updateEdgeFunc. rewrite if_false. 1: reflexivity. auto.
Qed.

Lemma lgd_dst_new: forall (g: HeapGraph) e v,
    dst (labeledgraph_gen_dst g e v) e = v.
Proof. intros. simpl. unfold updateEdgeFunc. rewrite if_true; reflexivity. Qed.

Definition closure_has_index (g: HeapGraph) (gen index: nat) :=
  (index <= generation_block_count (heapgraph_generation g gen))%nat.

Definition closure_has_v (g: HeapGraph) (v: Addr): Prop :=
  heapgraph_has_gen g (addr_gen v) /\ closure_has_index g (addr_gen v) (addr_block v).

Lemma graph_has_v_in_closure: forall g v, graph_has_v g v -> closure_has_v g v.
Proof.
  intros g v. destruct v as [gen index].
  unfold graph_has_v, closure_has_v, closure_has_index, heapgraph_generation_has_index.
  simpl. intros. intuition.
Qed.


Lemma lgd_f2v_eq_except_one: forall g fd e v',
    fd <> (inr e) ->
    field2val g fd = field2val (labeledgraph_gen_dst g e v') fd.
Proof.
  intros; unfold field2val; simpl.
  destruct fd; [destruct s|]; try reflexivity.
  unfold updateEdgeFunc; if_tac; [exfalso; apply H; rewrite H0|]; reflexivity.
Qed.

Lemma lgd_map_f2v_diff_vert_eq: forall g v v' v1 e n,
    0 <= n < Zlength (make_fields g v) ->
    Znth n (make_fields g v) = inr e ->
    v1 <> v ->
    map (field2val g) (make_fields g v1) =
    map (field2val (labeledgraph_gen_dst g e v'))
        (make_fields (labeledgraph_gen_dst g e v') v1).
Proof.
    intros.
    rewrite lgd_make_fields_eq.
    apply Znth_list_eq. split.
    1: repeat rewrite Zlength_map; reflexivity.
    intros. rewrite Zlength_map in H2.
    repeat rewrite Znth_map by assumption.
    apply lgd_f2v_eq_except_one. intro.
    pose proof (make_fields_edge_unique g e v
                                        v1 n j H H2 H0 H3).
    destruct H4. unfold not in H1. symmetry in H5.
    apply (H1 H5).
Qed.

Lemma lgd_f2v_eq_after_update: forall g v v' e n j,
  0 <= n < Zlength (make_fields g v) ->
  0 <= j < Zlength (make_fields g v) ->
  Znth n (make_fields g v) = inr e ->
  Znth j (upd_Znth n (map (field2val g)
                          (make_fields g v)) (heapgraph_block_ptr g v')) =
  Znth j
    (map (field2val (labeledgraph_gen_dst g e v'))
         (make_fields (labeledgraph_gen_dst g e v') v)).
Proof.
  intros.
  rewrite Znth_map.
  2: rewrite lgd_make_fields_eq; assumption.
  assert (j = n \/ j <> n) by lia; destruct H2.
  + subst j; rewrite upd_Znth_same.
    2: rewrite Zlength_map; assumption.
    replace (make_fields (labeledgraph_gen_dst g e v') v)
      with (make_fields g v) by reflexivity.
    rewrite H1; simpl field2val.
    unfold updateEdgeFunc; if_tac; try reflexivity.
    unfold complement in H2; assert (e = e) by reflexivity.
    apply H2 in H3; exfalso; assumption.
  + rewrite upd_Znth_diff_strong; [|rewrite Zlength_map|]; try assumption.
    rewrite Znth_map by assumption.
    apply (lgd_f2v_eq_except_one g (Znth j (make_fields g v))).
    intro. pose proof (make_fields_edge_unique g e v v n j H H0 H1 H3).
    lia.
Qed.

Lemma lgd_mfv_change_in_one_spot: forall g v e v' n,
    0 <= n < Zlength (make_fields g v) ->
    block_mark (heapgraph_block g v) = false ->
    Znth n (make_fields g v) = inr e ->
    upd_Znth n (make_fields_vals g v) (heapgraph_block_ptr g v') =
    (make_fields_vals (labeledgraph_gen_dst g e v') v).
Proof.
  intros.
  rewrite (Znth_list_eq (upd_Znth n (make_fields_vals g v)
               (heapgraph_block_ptr g v')) (make_fields_vals
                     (labeledgraph_gen_dst g e v') v)).
  rewrite upd_Znth_Zlength, fields_eq_length.
  2: rewrite fields_eq_length; rewrite make_fields_eq_length in H; assumption.
  split. 1: rewrite fields_eq_length; reflexivity.
  intros.
  unfold make_fields_vals.
  replace (block_mark (heapgraph_block (labeledgraph_gen_dst g e v') v))
    with (block_mark (heapgraph_block g v)) by reflexivity.
  rewrite H0; rewrite <- make_fields_eq_length in H2.
  apply lgd_f2v_eq_after_update; assumption.
Qed.

Lemma lgd_no_dangling_dst: forall g e v',
    graph_has_v g v' ->
    no_dangling_dst g ->
     no_dangling_dst (labeledgraph_gen_dst g e v').
Proof.
  intros. unfold no_dangling_dst in *.
  intros. rewrite <- lgd_graph_has_v.
  simpl. unfold updateEdgeFunc; if_tac; [assumption | apply (H0 v)]; assumption.
Qed.

Lemma lgd_no_dangling_dst_copied_vert: forall g e v,
    copy_compatible g ->
    graph_has_v g v ->
    block_mark (heapgraph_block g v) = true ->
    no_dangling_dst g ->
    no_dangling_dst (labeledgraph_gen_dst g e (block_copied_vertex (heapgraph_block g v))).
Proof.
  intros.
  assert (graph_has_v g (block_copied_vertex (heapgraph_block g v))) by apply (H v H0 H1).
  apply lgd_no_dangling_dst; assumption.
Qed.


Lemma block_mark__false_prep64: forall z,
    0 <= z < two_p (8 * 8) ->
    Int64.and (Int64.repr z) (Int64.repr 255) =
    Int64.sub (Int64.repr z)
              (Int64.mul (Int64.repr (z / two_p 8)) (Int64.repr (two_p 8))).
Proof.
  intros. replace (Int64.repr 255) with (Int64.sub (Int64.repr 256) Int64.one) by
      now vm_compute.
  rewrite <- (Int64.modu_and _ _ (Int64.repr 8)) by now vm_compute.
  rewrite Int64.modu_divu by (vm_compute; intro S; inversion S).
  rewrite (Int64.divu_pow2 _ _ (Int64.repr 8)) by now vm_compute.
  rewrite (Int64.mul_pow2 _ _ (Int64.repr 8)) by now vm_compute.
  rewrite Int64.shru_div_two_p, !Int64.unsigned_repr; [| rep_lia | ].
  - rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia. easy.
  - simpl Z.mul in H. unfold Int64.max_unsigned, Int64.modulus.
    unfold Int64.wordsize, Wordsize_64.wordsize. rewrite two_power_nat_two_p.
    simpl Z.of_nat. lia.
Qed.

Lemma block_mark__false_prep32: forall z,
    0 <= z < two_p (4 * 8) ->
    Int.and (Int.repr z) (Int.repr 255) =
    Int.sub (Int.repr z)
              (Int.mul (Int.repr (z / two_p 8)) (Int.repr (two_p 8))).
Proof.
  intros. replace (Int.repr 255) with (Int.sub (Int.repr 256) Int.one) by
      now vm_compute.
  rewrite <- (Int.modu_and _ _ (Int.repr 8)) by now vm_compute.
  rewrite Int.modu_divu by (vm_compute; intro S; inversion S).
  rewrite (Int.divu_pow2 _ _ (Int.repr 8)) by now vm_compute.
  rewrite (Int.mul_pow2 _ _ (Int.repr 8)) by now vm_compute.
  rewrite Int.shru_div_two_p, !Int.unsigned_repr; [| rep_lia | ].
  - rewrite Int.shl_mul_two_p, Int.unsigned_repr by rep_lia. easy.
  - simpl Z.mul in H. unfold Int.max_unsigned, Int.modulus.
    unfold Int.wordsize, Wordsize_32.wordsize. rewrite two_power_nat_two_p.
    simpl Z.of_nat. lia.
Qed.

Lemma block_mark__false: forall g v,
    block_mark (heapgraph_block g v) = false ->
    if Archi.ptr64 then
        Int64.and (Int64.repr (heapgraph_block_header g v)) (Int64.repr 255) =
        Int64.repr (block_tag (heapgraph_block g v))
    else Int.and (Int.repr (heapgraph_block_header g v)) (Int.repr 255) =
         Int.repr (block_tag (heapgraph_block g v)).
Proof.
  intros. cbv delta [Archi.ptr64]. simpl.
  first [rewrite block_mark__false_prep32 | rewrite block_mark__false_prep64].
  2: apply heapgraph_block_header__range.
  unfold heapgraph_block_header in *. remember (heapgraph_block g v) as r eqn:E. clear E.
  rewrite H, !Zbits.Zshiftl_mul_two_p in * by lia. rewrite <- Z.add_assoc.
  replace (block_color r * two_p 8 + Zlength (block_fields r) * two_p 10)
    with ((block_color r + Zlength (block_fields r) * two_p 2) * two_p 8) by
      (rewrite Z.mul_add_distr_r, <- Z.mul_assoc, <- two_p_is_exp by lia;
       reflexivity). rewrite Z.div_add by (vm_compute; intros S; inversion S).
  assert (block_tag r / two_p 8 = 0) by (apply Z.div_small, block_tag__range).
  rewrite H0, Z.add_0_l.
  first [rewrite mul_repr, sub_repr | rewrite mul64_repr, sub64_repr].
  now rewrite <- Z.add_sub_assoc, Z.sub_diag, Z.add_0_r.
Qed.


Definition root_t: Type := Z + GC_Pointer + Addr.

Instance root_t_inhabitant: Inhabitant root_t := inl (inl Z.zero).


Definition root2val (g: HeapGraph) (fd: root_t) : val :=
  match fd with
  | inl (inl z) => odd_Z2val z
  | inl (inr p) => GC_Pointer2val p
  | inr v => heapgraph_block_ptr g v
  end.


Definition roots_t: Type := list root_t.

Lemma root_in_outlier: forall (roots: roots_t) outlier p,
    In (inl (inr p)) roots ->
    incl (filter_sum_right (filter_sum_left roots)) outlier -> In p outlier.
Proof.
  intros. apply H0. rewrite <- filter_sum_right_In_iff, <- filter_sum_left_In_iff.
  assumption.
Qed.

Definition roots_have_no_gen (roots: roots_t) (gen: nat): Prop :=
  forall v, In (inr v) roots -> addr_gen v <> gen.

Definition outlier_t: Type := list GC_Pointer.

