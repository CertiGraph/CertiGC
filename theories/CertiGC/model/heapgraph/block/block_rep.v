From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.has_block.

Local Open Scope Z.


Definition heapgraph_block_ptr 
  (g : HeapGraph) (v : Addr) : val :=
  offset_val (WORD_SIZE * heapgraph_block_offset g v) (heapgraph_generation_base g (addr_gen v)).

Lemma lgd_heapgraph_block_ptr_eq :
  forall g e v' x, heapgraph_block_ptr (labeledgraph_gen_dst g e v') x = heapgraph_block_ptr g x.
Proof.
  reflexivity.
Qed.


Lemma heapgraph_block_ptr__eq 
  (g1 g2 : HeapGraph) 
  (v : Addr) (Hv : forall v, heapgraph_block g1 v = heapgraph_block g2 v)
  (Hg1g2 : map generation_base (heapgraph_generations g1).(generations) =
           map generation_base (heapgraph_generations g2).(generations)) :
  heapgraph_block_ptr g1 v = heapgraph_block_ptr g2 v.
Proof.
  (unfold heapgraph_block_ptr).
  f_equal.
  {
    f_equal.
    (unfold heapgraph_block_offset).
    f_equal.
    (remember (addr_block v) as n eqn:En ).
    clear En.
    (induction n as [| n IHn]; simpl; auto).
    (rewrite !heapgraph_block_size_prev__S, IHn).
    f_equal.
    (unfold heapgraph_block_size).
    now rewrite Hv.
  }
  {
    (assert (Hgen : forall gen, heapgraph_has_gen g1 gen <-> heapgraph_has_gen g2 gen)).
    {
      intro gen.
      (unfold heapgraph_has_gen).
      (assert (E : length (generations (heapgraph_generations g1)) = length (generations (heapgraph_generations g2)))).
      {
        now rewrite <- !(map_length generation_base), Hg1g2.
      }
      lia.
    }
    (unfold heapgraph_generation_base).
    (do 2 if_tac; rewrite Hgen in H; try easy).
    (unfold heapgraph_generation).
    now rewrite <- !(map_nth generation_base), Hg1g2.
  }
Qed.

Lemma heapgraph_generations_append__heapgraph_block_ptr 
  (g : HeapGraph) (gi : Generation) 
  (v : Addr) (Hv : heapgraph_has_block g v) :
  heapgraph_block_ptr (heapgraph_generations_append g gi) v = heapgraph_block_ptr g v.
Proof.
  (unfold heapgraph_block_ptr).
  f_equal.
  (unfold heapgraph_generation_base).
  (destruct Hv).
  (rewrite if_true by (rewrite heapgraph_has_gen__heapgraph_generations_append; now left)).
  (rewrite if_true by easy).
  now rewrite heapgraph_generation__heapgraph_generations_append__old.
Qed.



Definition heapgraph_block_header 
  (g : HeapGraph) (v : Addr) : Z :=
  let vb := heapgraph_block g v in
  if vb.(block_mark) then 0 else vb.(block_tag) + Z.shiftl vb.(block_color) 8 + Z.shiftl (Zlength vb.(block_fields)) 10.

Lemma heapgraph_block_header__heapgraph_generations_append :
  forall g gi v, heapgraph_block_header g v = heapgraph_block_header (heapgraph_generations_append g gi) v.
Proof.
  (intros).
  (unfold heapgraph_block_header).
  reflexivity.
Qed.

Lemma heapgraph_block_header__labeledgraph_gen_dst :
  forall g e v' x, heapgraph_block_header g x = heapgraph_block_header (labeledgraph_gen_dst g e v') x.
Proof.
  reflexivity.
Qed.


Lemma heapgraph_block_header__iff 
  (g : HeapGraph) (v : Addr) : 
  heapgraph_block_header g v = 0 <-> block_mark (heapgraph_block g v) = true.
Proof.
  (unfold heapgraph_block_header).
  (destruct (block_mark (heapgraph_block g v)); try easy).
  (split; intro H; try easy).
  (pose proof (proj1 (block_fields__range (heapgraph_block g v))) as Hfields).
  (assert (F : Z.shiftl (Zlength (block_fields (heapgraph_block g v))) 10 = 0)).
  {
    (assert (Hshift__color : 0 <= Z.shiftl (block_color (heapgraph_block g v)) 8)).
    {
      (pose proof (proj1 (block_color__range (heapgraph_block g v))) as Hcolor).
      now rewrite Z.shiftl_nonneg.
    }
    (pose proof (proj1 (block_tag__range (heapgraph_block g v))) as Htag).
    (remember (Zlength (block_fields (heapgraph_block g v))) as z eqn:Ez ; clear Ez).
    (assert (F' : 0 <= Z.shiftl z 10)).
    {
      (apply Z.shiftl_nonneg).
      lia.
    }
    lia.
  }
  (rewrite Z.shiftl_eq_0_iff in F; lia).
Qed.

Lemma heapgraph_block_header__range 
  (g : HeapGraph) (v : Addr) : 
  0 <= heapgraph_block_header g v < two_p (WORD_SIZE * 8).
Proof.
  (unfold heapgraph_block_header).
  (destruct (block_mark (heapgraph_block g v))).
  {
    (pose proof (two_p_gt_ZERO (WORD_SIZE * 8))).
    (unfold WORD_SIZE in *).
    lia.
  }
  (pose proof (block_tag__range (heapgraph_block g v)) as Htag).
  (pose proof (block_color__range (heapgraph_block g v)) as Hcolor).
  (pose proof (block_fields__range (heapgraph_block g v)) as Hfields).
  (remember (block_tag (heapgraph_block g v)) as z1 eqn:Ez1 ; clear Ez1).
  (remember (block_color (heapgraph_block g v)) as z2 eqn:Ez2 ; clear Ez2).
  (remember (Zlength (block_fields (heapgraph_block g v))) as z3 eqn:Ez3 ; clear Ez3).
  (assert (Hz2 : 0 <= 8) by lia).
  (apply (Zbits.Zshiftl_mul_two_p z2) in Hz2).
  (rewrite Hz2).
  clear Hz2.
  (assert (Hz3 : 0 <= 10) by lia).
  (apply (Zbits.Zshiftl_mul_two_p z3) in Hz3).
  (rewrite Hz3).
  clear Hz3.
  (assert (Htwo_p10 : two_p 10 > 0) by (apply two_p_gt_ZERO; lia)).
  (assert (Htwo_p8 : two_p 8 > 0) by (apply two_p_gt_ZERO; lia)).
  split.
  {
    (assert (Hz2' : 0 <= z2 * two_p 8) by (apply Z.mul_nonneg_nonneg; lia)).
    (assert (Hz3' : 0 <= z3 * two_p 10) by (apply Z.mul_nonneg_nonneg; lia)).
    lia.
  }
  (change 256 with (two_p 8) in Htag).
  (change 4 with (two_p 2) in Hcolor).
  (assert (Hz1' : z1 <= two_p 8 - 1) by lia).
  clear Htag.
  (assert (Hz2' : z2 <= two_p 2 - 1) by lia).
  clear Hcolor.
  (assert (Hz3' : z3 <= two_p (WORD_SIZE * 8 - 10) - 1) by lia).
  clear Hfields.
  (apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in Hz1'; try lia).
  (apply Z.mul_le_mono_nonneg_r with (p := two_p 10) in Hz3'; try lia).
  (rewrite Z.mul_sub_distr_r, Z.mul_1_l in Hz1', Hz3').
  (assert (Hwordsize : 0 <= WORD_SIZE * 8 - 10) by (unfold WORD_SIZE; lia)).
  (rewrite <- two_p_is_exp in Hz1', Hz3' by lia; clear Hwordsize).
  (simpl Z.add in Hz1', Hz3').
  Opaque two_p.
  (simpl).
  Transparent two_p.
  (remember (two_p 2) as x eqn:E ; compute in E; subst x).
  (remember (two_p 8) as x eqn:E ; compute in E; subst x).
  (remember (two_p 10) as x eqn:E ; compute in E; subst x).
  (remember (two_p 16) as x eqn:E ; compute in E; subst x).
  (remember (two_p 64) as x eqn:E ; compute in E; subst x).
  lia.
Qed.

Lemma heapgraph_block_header__repr_iff 
  (g : HeapGraph) (v : Addr) :
  (if Archi.ptr64
   then Int64.repr (heapgraph_block_header g v) = Int64.repr 0
   else Int.repr (heapgraph_block_header g v) = Int.repr 0) <-> 
  block_mark (heapgraph_block g v) = true.
Proof.
  (rewrite <- heapgraph_block_header__iff).
  (split; intro H; [  | rewrite H; reflexivity ]).
  (cbv delta [Archi.ptr64] in H).
  (simpl in H).
  Transparent Int.repr Int64.repr.
  (inversion H).
  Opaque Int64.repr Int.repr.
  clear H.
  (rewrite H1).
  (match goal with
   | H:Int64.Z_mod_modulus _ = _ |- _ => rewrite Int64.Z_mod_modulus_eq in H
   | H:Int.Z_mod_modulus _ = _ |- _ => rewrite Int.Z_mod_modulus_eq in H
   end).
  (rewrite Z.mod_small in H1; auto).
  (apply heapgraph_block_header__range).
Qed.

Lemma heapgraph_block_header__Wosize 
  (g : HeapGraph) (v : Addr) 
  (H : block_mark (heapgraph_block g v) = false) :
  if Archi.ptr64
  then
   Int64.shru (Int64.repr (heapgraph_block_header g v)) (Int64.repr 10) =
   Int64.repr (Zlength (block_fields (heapgraph_block g v)))
  else
   Int.shru (Int.repr (heapgraph_block_header g v)) (Int.repr 10) =
   Int.repr (Zlength (block_fields (heapgraph_block g v))).
Proof.
  (cbv delta [Archi.ptr64]).
  (simpl).
  (match goal with
   | |- Int64.shru _ _ = Int64.repr _ => rewrite Int64.shru_div_two_p, !Int64.unsigned_repr
   | |- Int.shru _ _ = Int.repr _ => rewrite Int.shru_div_two_p, !Int.unsigned_repr
   end).
  - f_equal.
    (unfold heapgraph_block_header).
    (remember (heapgraph_block g v) as r eqn:E ).
    clear E.
    (rewrite H, !Zbits.Zshiftl_mul_two_p by lia).
    (rewrite Z.div_add).
    2: (compute; lia).
    (pose proof (block_tag__range r)).
    (pose proof (block_color__range r)).
    (cut ((block_tag r + block_color r * two_p 8) / two_p 10 = 0)).
    1: (intros; lia).
    (apply Z.div_small).
    (change 256 with (two_p 8) in H0).
    (change 4 with (two_p 2) in H1).
    (assert (0 <= block_tag r <= two_p 8 - 1) by lia).
    clear H0.
    (destruct H2).
    (assert (0 <= block_color r <= two_p 2 - 1) by lia).
    clear H1.
    (destruct H3).
    (assert (two_p 8 > 0) by (apply two_p_gt_ZERO; lia)).
    split.
    + (assert (0 <= block_color r * two_p 8) by (apply Z.mul_nonneg_nonneg; lia)).
      lia.
    + (apply Z.mul_le_mono_nonneg_r with (p := two_p 8) in H3).
      2: lia.
      (rewrite Z.mul_sub_distr_r, <- two_p_is_exp in H3 by lia).
      (simpl Z.add in H3).
      lia.
  - rep_lia.
  - (pose proof (heapgraph_block_header__range g v)).
    (unfold WORD_SIZE in *).
    (match goal with
     | |- context [ Int64.max_unsigned ] =>
           unfold Int64.max_unsigned, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize
     | |- context [ Int.max_unsigned ] => unfold Int.max_unsigned, Int.modulus, Int.wordsize, Wordsize_32.wordsize
     end).
    (simpl Z.mul in H0).
    (rewrite two_power_nat_two_p).
    (simpl Z.of_nat).
    lia.
Qed.
