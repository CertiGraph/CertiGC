From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From compcert Require Import common.Values.
From compcert Require Import lib.Integers.

From VST Require Import floyd.functional_base.
From VST Require Import floyd.sublist.
From VST Require Import msl.shares.
From VST Require Import veric.base.
From VST Require Import veric.shares.
From VST Require Import veric.val_lemmas.

From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.util.


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
    tag_no_scan: (NO_SCAN_TAG <= block_tag -> ~ In None block_fields)%Z;
    (* TODO: what's up with this? why can raw_f be None at all? *)
}.

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

Definition HeapGraph := LabeledGraph Addr Field Block unit Generations.


Definition vertex_size (g: HeapGraph) (v: Addr): Z
 := Zlength (vlabel g v).(block_fields) + 1.

Lemma vertex_size__one (g: HeapGraph) (v: Addr):
    1 < vertex_size g v.
Proof.
    unfold vertex_size.
    pose proof (block_fields__range (vlabel g v)).
    lia.
Qed.


Definition vertex_size_accum g gen (s: Z) (n: nat): Z
 := s + vertex_size g {| addr_gen := gen; addr_block := n |}.

Lemma vertex_size_accum__mono (g: HeapGraph) (gen: nat) (s: Z) (n: nat):
    s < vertex_size_accum g gen s n.
Proof.
    unfold vertex_size_accum.
    pose proof (vertex_size__one g {| addr_gen := gen; addr_block := n |}) as H.
    lia.
Qed.

Lemma vertex_size_accum__comm (g: HeapGraph) (gen: nat) (s: Z) (n1 n2: nat):
    vertex_size_accum g gen (vertex_size_accum g gen s n1) n2 =
    vertex_size_accum g gen (vertex_size_accum g gen s n2) n1.
Proof.
    unfold vertex_size_accum.
    lia.
Qed.

Lemma vertex_size_accum__fold_lt (g: HeapGraph) (gen: nat) (s: Z) (l: list nat) (Hl: l <> nil):
    s < fold_left (vertex_size_accum g gen) l s.
Proof.
    apply (fold_left_Z_mono_strict (vertex_size_accum g gen) nil l l) ; try assumption.
    + apply vertex_size_accum__mono.
    + apply vertex_size_accum__comm.
    + apply Permutation_refl.
Qed.

Lemma vertex_size_accum__fold_le (g: HeapGraph) (gen: nat) (s: Z) (l: list nat):
    s <= fold_left (vertex_size_accum g gen) l s.
Proof.
    destruct l as [|n l] ; try easy.
    rewrite Z.le_lteq.
    left.
    now apply vertex_size_accum__fold_lt.
Qed.


Definition previous_vertices_size (g: HeapGraph) (gen i: nat): Z
 := fold_left (vertex_size_accum g gen) (nat_inc_list i) 0.

 Lemma previous_vertices_size__S (g: HeapGraph) (gen i: nat):
    previous_vertices_size g gen (S i) =
    previous_vertices_size g gen i + vertex_size g {| addr_gen := gen; addr_block := i |}.
Proof.
    unfold previous_vertices_size at 1.
    now rewrite nat_inc_list_S, fold_left_app.
Qed.

Lemma previous_vertices_size__nonneg (g: HeapGraph) (gen i: nat):
    0 <= previous_vertices_size g gen i.
Proof.
    unfold previous_vertices_size.
    apply vertex_size_accum__fold_le.
Qed.
