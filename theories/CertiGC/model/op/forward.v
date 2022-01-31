From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.
From VST Require Import floyd.functional_base.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.compatible.compatible.
From CertiGC Require Import model.constants.
From CertiGC Require Import model.heap.heap.
From CertiGC Require Import model.heapgraph.graph.
From CertiGC Require Import model.heapgraph.more.
From CertiGC Require Import model.op.copy.
From CertiGC Require Import model.op.cut.
From CertiGC Require Import model.op.update.
From CertiGC Require Import model.thread_info.thread_info.
From CertiGC Require Import model.util.

Definition forward_t: Type := Z + GC_Pointer + Addr + Field.

Definition root2forward (r: root_t): forward_t :=
  match r with
  | inl (inl z) => inl (inl (inl z))
  | inl (inr p) => inl (inl (inr p))
  | inr v => inl (inr v)
  end.

Definition field2forward (f: Cell): forward_t :=
  match f with
  | inl (inl z) => inl (inl (inl z))
  | inl (inr p) => inl (inl (inr p))
  | inr e => inr e
  end.

Definition forward_p_type: Type := Z + (Addr * Z).

#[global]Instance forward_p_type_Inhabitant: Inhabitant forward_p_type := inl 0.

Definition forward_p2forward_t
           (p: forward_p_type) (roots: roots_t) (g: HeapGraph): forward_t :=
  match p with
  | inl root_index => root2forward (Znth root_index roots)
  | inr (v, n) => if (heapgraph_block g v).(block_mark) && (n =? 0)
                  then (inl (inr (heapgraph_block g v).(block_copied_vertex)))
                  else field2forward (Znth n (heapgraph_block_cells g v))
  end.

Inductive forward_relation (from to: nat):
  nat -> forward_t -> HeapGraph -> HeapGraph -> Prop :=
| fr_z: forall depth z g, forward_relation from to depth (inl (inl (inl z))) g g
| fr_p: forall depth p g, forward_relation from to depth (inl (inl (inr p))) g g
| fr_v_not_in: forall depth v g,
    addr_gen v <> from -> forward_relation from to depth (inl (inr v)) g g
| fr_v_in_forwarded: forall depth v g,
    addr_gen v = from -> (heapgraph_block g v).(block_mark) = true ->
    forward_relation from to depth (inl (inr v)) g g
| fr_v_in_not_forwarded_O: forall v g,
    addr_gen v = from -> (heapgraph_block g v).(block_mark) = false ->
    forward_relation from to O (inl (inr v)) g (lgraph_copy_v g v to)
| fr_v_in_not_forwarded_Sn: forall depth v g g',
    addr_gen v = from -> (heapgraph_block g v).(block_mark) = false ->
    let new_g := lgraph_copy_v g v to in
    forward_loop from to depth (heapgraph_field_pairs new_g (new_copied_v g to)) new_g g' ->
    forward_relation from to (S depth) (inl (inr v)) g g'
| fr_e_not_to: forall depth e (g: HeapGraph),
    addr_gen (dst g e) <> from -> forward_relation from to depth (inr e) g g
| fr_e_to_forwarded: forall depth e (g: HeapGraph),
    addr_gen (dst g e) = from -> (heapgraph_block g (dst g e)).(block_mark) = true ->
    let new_g := labeledgraph_gen_dst g e (heapgraph_block g (dst g e)).(block_copied_vertex) in
    forward_relation from to depth (inr e) g new_g
| fr_e_to_not_forwarded_O: forall e (g: HeapGraph),
    addr_gen (dst g e) = from -> (heapgraph_block g (dst g e)).(block_mark) = false ->
    let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                      (new_copied_v g to) in
    forward_relation from to O (inr e) g new_g
| fr_e_to_not_forwarded_Sn: forall depth e (g g': HeapGraph),
    addr_gen (dst g e) = from -> (heapgraph_block g (dst g e)).(block_mark) = false ->
    let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                      (new_copied_v g to) in
    forward_loop from to depth (heapgraph_field_pairs new_g (new_copied_v g to)) new_g g' ->
    forward_relation from to (S depth) (inr e) g g'
with
forward_loop (from to: nat): nat -> list forward_p_type -> HeapGraph -> HeapGraph -> Prop :=
| fl_nil: forall depth g, forward_loop from to depth nil g g
| fl_cons: forall depth g1 g2 g3 f fl,
    forward_relation from to depth (forward_p2forward_t f nil g1) g1 g2 ->
    forward_loop from to depth fl g2 g3 -> forward_loop from to depth (f :: fl) g1 g3.

Lemma fr_general_prop_bootstrap: forall depth from to p g g'
                                        (P: nat -> HeapGraph -> HeapGraph -> Prop),
    (forall to g, P to g g) ->
    (forall to g1 g2 g3, P to g1 g2 -> P to g2 g3 -> P to g1 g3) ->
    (forall to g e v, P to g (labeledgraph_gen_dst g e v)) ->
    (forall to g v, P to g (lgraph_copy_v g v to)) ->
    forward_relation from to depth p g g' -> P to g g'.
Proof.
  induction depth; intros.
  - inversion H3; subst; try (specialize (H to g'); assumption).
    + apply H2.
    + subst new_g. apply H1.
    + subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
      remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
      cut (P to g1 g2). 2: subst; apply H1. intros. apply (H0 to g g1 g2).
      2: assumption. subst g1. apply H2.
  - assert (forall l from to g1 g2,
                 forward_loop from to depth l g1 g2 -> P to g1 g2). {
    induction l; intros; inversion H4. 1: apply H. subst.
    specialize (IHl _ _ _ _ H11). specialize (IHdepth _ _ _ _ _ _ H H0 H1 H2 H8).
    apply (H0 _ _ _ _ IHdepth IHl). }
    clear IHdepth. inversion H3; subst; try (specialize (H to g'); assumption).
    + cut (P to g new_g).
      * intros. apply (H0 to g new_g g'). 1: assumption. apply (H4 _ _ _ _ _ H8).
      * subst new_g. apply H2.
    + subst new_g. apply H1.
    + cut (P to g new_g).
      * intros. apply (H0 to g new_g g'). 1: assumption. apply (H4 _ _ _ _ _ H8).
      * subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
        remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
        cut (P to g1 g2). 2: subst; apply H1. intros. apply (H0 to g g1 g2).
        2: assumption. subst g1. apply H2.
Qed.

Lemma fr_graph_has_gen: forall depth from to p g g',
    heapgraph_has_gen g to -> forward_relation from to depth p g g' ->
    forall x, heapgraph_has_gen g x <-> heapgraph_has_gen g' x.
Proof.
  intros. remember (fun to g1 g2 =>
                      heapgraph_has_gen g1 to ->
                      forall x, heapgraph_has_gen g1 x <-> heapgraph_has_gen g2 x) as P.
  pose proof (fr_general_prop_bootstrap depth from to p g g' P). subst P.
  apply H1; clear H1; intros; try assumption; try reflexivity.
  - rewrite H1 by assumption. apply H2. rewrite <- H1; assumption.
  - apply lcv_graph_has_gen. assumption.
Qed.

Lemma fl_graph_has_gen: forall from to depth l g g',
    heapgraph_has_gen g to -> forward_loop from to depth l g g' ->
    forall x, heapgraph_has_gen g x <-> heapgraph_has_gen g' x.
Proof.
  intros. revert g g' H H0 x. induction l; intros; inversion H0. 1: reflexivity.
  subst. assert (forall y, heapgraph_has_gen g y <-> heapgraph_has_gen g2 y) by
      (intros; apply (fr_graph_has_gen _ _ _ _ _ _ H H4)).
  transitivity (heapgraph_has_gen g2 x). 1: apply H1. rewrite H1 in H.
  apply IHl; assumption.
Qed.

Lemma fr_general_prop:
  forall depth from to p g g' A (Q: HeapGraph -> A -> nat -> Prop)
         (P: HeapGraph -> HeapGraph -> A -> Prop) (R: nat -> nat -> Prop),
    R from to -> heapgraph_has_gen g to -> (forall g v, P g g v) ->
    (forall g1 g2 g3 v, P g1 g2 v -> P g2 g3 v -> P g1 g3 v) ->
    (forall g e v x, P g (labeledgraph_gen_dst g e v) x) ->
    (forall from g v to x,
        heapgraph_has_gen g to -> Q g x from -> (heapgraph_block g v).(block_mark) = false ->
        R from to -> addr_gen v = from -> P g (lgraph_copy_v g v to) x) ->
    (forall depth from to p g g',
        heapgraph_has_gen g to -> forward_relation from to depth p g g' ->
        forall v, Q g v from -> Q g' v from) ->
    (forall g v to x from, heapgraph_has_gen g to -> Q g x from ->
                           Q (lgraph_copy_v g v to) x from) ->
    (forall g e v x from, Q g x from -> Q (labeledgraph_gen_dst g e v) x from) ->
    forward_relation from to depth p g g' ->
    forall v, Q g v from -> P g g' v.
Proof.
  induction depth; intros.
  - inversion H8; subst; try (specialize (H1 g' v); assumption).
    + apply (H4 (addr_gen v0)); [assumption.. | reflexivity].
    + subst new_g. apply H3.
    + subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
      remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
      cut (P g1 g2 v). 2: subst; apply H3. intros. apply (H2 g g1 g2).
      2: assumption. subst g1.
      apply (H4 (addr_gen (dst g e))); [assumption.. | reflexivity].
  - assert (forall l from to g1 g2,
               heapgraph_has_gen g1 to -> forward_loop from to depth l g1 g2 ->
               R from to -> forall v, Q g1 v from -> P g1 g2 v). {
      induction l; intros; inversion H11. 1: apply H1. subst.
      specialize (IHdepth _ _ _ _ _ _ _ _ _ H12 H10 H1 H2 H3 H4 H5 H6 H7 H17 _ H13).
      apply (H5 _ _ _ _ _ _ H10 H17) in H13.
      rewrite (fr_graph_has_gen _ _ _ _ _ _ H10 H17) in H10.
      specialize (IHl _ _ _ _ H10 H20 H12 _ H13). apply (H2 _ _ _ _ IHdepth IHl). }
    clear IHdepth. inversion H8; subst; try (specialize (H1 g' v); assumption).
    + cut (P g new_g v).
      * intros. apply (H2 g new_g g'). 1: assumption.
        assert (heapgraph_has_gen new_g to) by
            (subst new_g; rewrite <- lcv_graph_has_gen; assumption).
        apply (H10 _ _ _ _ _ H12 H14 H). subst new_g. apply H6; assumption.
      * subst new_g. apply (H4 (addr_gen v0)); [assumption.. | reflexivity].
    + subst new_g. apply H3.
    + cut (P g new_g v).
      * intros. apply (H2 g new_g g'). 1: assumption.
        assert (heapgraph_has_gen new_g to) by
            (subst new_g; rewrite lgd_graph_has_gen, <- lcv_graph_has_gen; assumption).
        apply (H10 _ _ _ _ _ H12 H14 H). subst new_g. apply H7, H6; assumption.
      * subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
        remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
        cut (P g1 g2 v). 2: subst; apply H3. intros. apply (H2 g g1 g2).
        2: assumption. subst g1.
        apply (H4 (addr_gen (dst g e))); [assumption.. | reflexivity].
Qed.

Lemma fr_heapgraph_has_block (depth from to: nat) (p: forward_t) (g g': HeapGraph)
    (Hto: heapgraph_has_gen g to)
    (Hg__g': forward_relation from to depth p g g')
    (v: Addr)
    (Hv: heapgraph_has_block g v):
    heapgraph_has_block g' v.
Proof.
    remember (fun (g: HeapGraph) (v: Addr) (x: nat) => True) as Q.
    remember (fun g1 g2 v => heapgraph_has_block g1 v -> heapgraph_has_block g2 v) as P.
    remember (fun (x1 x2: nat) => True) as R.
    pose proof (fr_general_prop depth from to p g g' _ Q P R) as HP.
    subst Q P R.
    apply HP; clear HP ; try easy.
    + intros g1 g2 g3 w Hg1g2 Hg2g3 Hg1.
      now apply Hg2g3, Hg1g2.
    + intros g'' f w u Hu.
      destruct Hu ; now constructor.
    + intros from' g'' w to' u Hg'' _ Hw _ Efrom' Hu.
      unfold lgraph_copy_v ; rewrite <- lmc_heapgraph_has_block.
      now apply lgraph_add_copied_v__heapgraph_has_block.
Qed.


Lemma fr_gen_start: forall depth from to p g g',
    heapgraph_has_gen g to -> forward_relation from to depth p g g' ->
    forall x, heapgraph_generation_base g x = heapgraph_generation_base g' x.
Proof.
  intros. remember (fun (g: HeapGraph) (v: nat) (x: nat) => True) as Q.
  remember (fun g1 g2 x => heapgraph_generation_base g1 x = heapgraph_generation_base g2 x) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H1; clear H1; intros; try assumption; try reflexivity.
  - rewrite H1. assumption.
  - rewrite lcv_gen_start; [reflexivity | assumption].
Qed.

Lemma fl_gen_start: forall from to depth l g g',
    heapgraph_has_gen g to -> forward_loop from to depth l g g' ->
    forall x, heapgraph_generation_base g x = heapgraph_generation_base g' x.
Proof.
  intros. revert g g' H H0 x. induction l; intros; inversion H0. 1: reflexivity.
  subst. transitivity (heapgraph_generation_base g2 x).
  - apply (fr_gen_start _ _ _ _ _ _ H H4).
  - assert (heapgraph_has_gen g2 to) by
        (rewrite <- (fr_graph_has_gen _ _ _ _ _ _ H H4); assumption).
    apply IHl; assumption.
Qed.

Lemma fr_heapgraph_block_size (depth from to: nat) (p: forward_t) (g1 g2: HeapGraph)
    (Hg1: heapgraph_has_gen g1 to)
    (Hg1g2: forward_relation from to depth p g1 g2)
    (v: Addr)
    (Hv: heapgraph_has_block g1 v):
    heapgraph_block_size g1 v = heapgraph_block_size g2 v.
Proof.
    remember (fun g v (x: nat) => heapgraph_has_block g v) as Q.
    remember (fun g1 g2 v => heapgraph_block_size g1 v = heapgraph_block_size g2 v) as P.
    remember (fun (x1 x2: nat) => True) as R.
    pose proof (fr_general_prop depth from to p g1 g2 _ Q P R)as E. subst Q P R.
    apply E ; clear E ; try easy.
    + intros g3 g4 g5 w Hg3g4 Hg4g5.
      congruence.
    + intros from' g w to' u Hto' Hu Hw _ Efrom'.
      now rewrite lcv_heapgraph_block_size_old.
    + intros depth' from' to' p' g g' Hto' Hgg' w Hw.
      apply (fr_heapgraph_has_block _ _ _ _ _ _ Hto' Hgg' _ Hw).
    + intros g w to' u _ Hto' Hu.
      now apply lcv_heapgraph_has_block_old.
    + intros g f w u _ Hu.
      destruct Hu ; now constructor.
Qed.

Lemma fr_O_heapgraph_generation_unchanged: forall from to p g1 g2,
    heapgraph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen, gen <> to -> heapgraph_generation g1 gen = heapgraph_generation g2 gen.
Proof.
  intros. inversion H0; subst; try reflexivity.
  - rewrite lcv_heapgraph_generation; auto.
  - subst new_g. transitivity (heapgraph_generation (lgraph_copy_v g1 (dst g1 e) to) gen).
    2: reflexivity. rewrite lcv_heapgraph_generation; [reflexivity | assumption..].
Qed.

Lemma fr_O_graph_gen_size_unchanged: forall from to p g1 g2,
    heapgraph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen, heapgraph_has_gen g1 gen -> gen <> to ->
                heapgraph_generation_size g1 gen = heapgraph_generation_size g2 gen.
Proof.
  intros. unfold heapgraph_generation_size.
  erewrite <- (fr_O_heapgraph_generation_unchanged from to _ g1 g2); eauto.
  replace
    (heapgraph_block_size_prev g2 gen (generation_block_count (heapgraph_generation g1 gen)))
    with (heapgraph_block_size_prev g1 gen (generation_block_count (heapgraph_generation g1 gen))).
  {
    easy.
  }
  apply fold_left_ext.
  intros.
  unfold heapgraph_block_size_accum.
  f_equal.
  rewrite nat_inc_list_In_iff in H3.
  now apply (fr_heapgraph_block_size O from to p g1 g2).
Qed.

Lemma fr_O_graph_remember_size_unchanged: forall from to p g1 g2,
    heapgraph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen, heapgraph_has_gen g1 gen -> gen <> to ->
                heapgraph_remember_size g1 gen = heapgraph_remember_size g2 gen.
Proof.
  intros.
  unfold heapgraph_remember_size.
  erewrite <- (fr_O_heapgraph_generation_unchanged from to _ g1 g2); eauto.
Qed.


Definition forward_p_compatible
           (p: forward_p_type) (roots: roots_t) (g: HeapGraph) (from: nat): Prop :=
  match p with
  | inl root_index => 0 <= root_index < Zlength roots
  | inr (v, n) => heapgraph_has_block g v /\ 0 <= n < Zlength (heapgraph_block g v).(block_fields) /\
                  (heapgraph_block g v).(block_mark) = false /\ addr_gen v <> from
  end.


Definition upd_roots (from to: nat) (forward_p: forward_p_type)
           (g: HeapGraph) (roots: roots_t) (f_info: fun_info): roots_t :=
  match forward_p with
  | inr _ => roots
  | inl index => match Znth index roots with
                 | inl (inl z) => roots
                 | inl (inr p) => roots
                 | inr v => if Nat.eq_dec (addr_gen v) from
                            then if (heapgraph_block g v).(block_mark)
                                 then upd_bunch index f_info roots
                                                (inr (heapgraph_block g v).(block_copied_vertex))
                                 else upd_bunch index f_info roots
                                                (inr (new_copied_v g to))
                            else roots
                 end
  end.

Lemma upd_roots_Zlength: forall from to p g roots f_info,
    Zlength roots = Zlength (live_roots_indices f_info) ->
    Zlength (upd_roots from to p g roots f_info) = Zlength roots.
Proof.
  intros. unfold upd_roots. destruct p. 2: reflexivity.
  destruct (Znth z roots). 1: destruct s; reflexivity. if_tac. 2: reflexivity.
  destruct (block_mark (heapgraph_block g a)); rewrite upd_bunch_Zlength; auto.
Qed.


Inductive forward_roots_loop (from to: nat) (f_info: fun_info):
  list nat -> roots_t -> HeapGraph -> roots_t -> HeapGraph -> Prop :=
| frl_nil: forall g roots, forward_roots_loop from to f_info nil roots g roots g
| frl_cons: forall g1 g2 g3 i il roots1 roots3,
    forward_relation from to O (root2forward (Znth (Z.of_nat i) roots1)) g1 g2 ->
    forward_roots_loop from to f_info il
                       (upd_roots from to (inl (Z.of_nat i)) g1 roots1 f_info)
                       g2 roots3 g3 ->
    forward_roots_loop from to f_info (i :: il) roots1 g1 roots3 g3.

Definition forward_roots_relation from to f_info roots1 g1 roots2 g2 :=
  forward_roots_loop from to f_info (nat_inc_list (length roots1)) roots1 g1 roots2 g2.


Definition forward_condition g t_info from to: Prop :=
  enough_space_to_copy g t_info from to /\
  heapgraph_has_gen g from /\ heapgraph_has_gen g to /\
  copy_compatible g /\ no_dangling_dst g.

Lemma lgd_forward_condition: forall g t_info v to v' e,
    addr_gen v <> to ->
    heapgraph_has_block g v ->
    heapgraph_has_block g v' ->
    forward_condition g t_info (addr_gen v) to ->
    forward_condition (labeledgraph_gen_dst g e v') t_info (addr_gen v) to.
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply lgd_enough_space_to_copy; assumption.
  - apply lgd_graph_has_gen; assumption.
  - apply lgd_graph_has_gen; assumption.
  - apply lgd_copy_compatible; assumption.
  - apply lgd_no_dangling_dst; assumption.
Qed.


Lemma lcv_forward_condition: forall
    g t_info v to index uv
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (heapgraph_block_size g v))
    (Hm : 0 <= index < MAX_ARGS),
    addr_gen v <> to -> heapgraph_has_block g v -> block_mark (heapgraph_block g v) = false ->
    forward_condition g t_info (addr_gen v) to ->
    forward_condition
      (lgraph_copy_v g v to)
      (update_thread_info_arg
         (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g v) Hi Hh) index uv Hm)
      (addr_gen v) to.
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply forward_estc; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_copy_compatible; assumption.
  - apply lcv_no_dangling_dst; assumption.
Qed.

Lemma lcv_forward_condition_unchanged: forall
    g t_info v to
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (heapgraph_block_size g v)),
    addr_gen v <> to -> heapgraph_has_block g v -> block_mark (heapgraph_block g v) = false ->
    forward_condition g t_info (addr_gen v) to ->
    forward_condition (lgraph_copy_v g v to)
         (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g v) Hi Hh)
      (addr_gen v) to.
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply forward_estc_unchanged; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_copy_compatible; assumption.
  - apply lcv_no_dangling_dst; assumption.
Qed.


Lemma fr_closure_has_v: forall depth from to p g g',
    heapgraph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, closure_has_v g v -> closure_has_v g' v.
Proof.
  intros. remember (fun (g: HeapGraph) (v: Addr) (x: nat) => True) as Q.
  remember (fun g1 g2 v => closure_has_v g1 v -> closure_has_v g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - apply H3, H2. assumption.
  - apply lcv_closure_has_v; assumption.
Qed.


Lemma fl_heapgraph_has_block: forall from to depth l g g',
    heapgraph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, heapgraph_has_block g v -> heapgraph_has_block g' v.
Proof.
  intros. revert g g' H H0 v H1. induction l; intros; inversion H0; subst.
  1: assumption. cut (heapgraph_has_block g2 v).
  - intros. assert (heapgraph_has_gen g2 to) by
        (apply (fr_graph_has_gen _ _ _ _ _ _ H H5); assumption).
    apply (IHl _ _ H3 H8 _ H2).
  - apply (fr_heapgraph_has_block _ _ _ _ _ _ H H5 _ H1).
Qed.

Lemma fr_heapgraph_block_ptr: forall depth from to p g g',
    heapgraph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, closure_has_v g v -> heapgraph_block_ptr g v = heapgraph_block_ptr g' v.
Proof.
  intros. remember (fun g v (x: nat) => closure_has_v g v) as Q.
  remember (fun g1 g2 v => heapgraph_block_ptr g1 v = heapgraph_block_ptr g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - rewrite H2. assumption.
  - rewrite lcv_heapgraph_block_ptr; [reflexivity | assumption..].
  - apply (fr_closure_has_v _ _ _ _ _ _ H2 H3 _ H4).
  - apply lcv_closure_has_v; assumption.
Qed.

Lemma fl_heapgraph_block_ptr: forall from to depth l g g',
    heapgraph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, closure_has_v g v -> heapgraph_block_ptr g v = heapgraph_block_ptr g' v.
Proof.
  intros. revert g g' H H0 v H1. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (heapgraph_block_ptr g2 v).
  - apply (fr_heapgraph_block_ptr _ _ _ _ _ _ H H5 _ H1).
  - apply IHl; [|assumption|].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_closure_has_v; eauto.
Qed.

Lemma fr_block_fields (depth from to: nat) (p: forward_t) (g g': HeapGraph)
    (Hto: heapgraph_has_gen g to)
    (Hgg': forward_relation from to depth p g g')
    (v: Addr)
    (Hv: heapgraph_has_block g v):
    block_fields (heapgraph_block g v) = block_fields (heapgraph_block g' v).
Proof.
    remember (fun (g: HeapGraph) (v: Addr) (x: nat) => heapgraph_has_block g v) as Q.
    remember (fun g1 g2 v => block_fields (heapgraph_block g1 v) = block_fields (heapgraph_block g2 v)) as P.
    remember (fun (x1 x2: nat) => True) as R.
    pose proof (fr_general_prop depth from to p g g' _ Q P R) as HP.
    subst Q P R.
    apply HP ; clear HP ; try easy.
    + intros g1 g2 g3 w H12 H23.
      congruence.
    + intros from' g'' w to' u Hto' Hu Hw _ Efrom'.
      now rewrite <- lcv_block_fields.
    + intros depth' from' to' p' g1 g2 Hto' Hg1g2 w Hw.
      apply (fr_heapgraph_has_block _ _ _ _ _ _ Hto' Hg1g2 _ Hw).
    + intros g'' w to' u _ Hto' Hu.
      now apply lcv_heapgraph_has_block_old.
    + intros g'' f w u _ Hu.
      destruct Hu ; now constructor.
Qed.

Lemma fl_block_fields: forall from to depth l g g',
    heapgraph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, heapgraph_has_block g v -> block_fields (heapgraph_block g v) = block_fields (heapgraph_block g' v).
Proof.
  intros. revert g g' H H0 v H1. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (block_fields (heapgraph_block g2 v)).
  - apply (fr_block_fields _ _ _ _ _ _ H H5 _ H1).
  - apply IHl; [|assumption|].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_heapgraph_has_block; eauto.
Qed.


Lemma fr_block_mark (depth from to: nat) (p: forward_t) (g g': HeapGraph)
    (Hto: heapgraph_has_gen g to)
    (Hgg': forward_relation from to depth p g g')
    (v: Addr)
    (Hv: heapgraph_has_block g v)
    (Hv__from: addr_gen v <> from):
    block_mark (heapgraph_block g v) = block_mark (heapgraph_block g' v).
Proof.
    remember (fun g v x => heapgraph_has_block g v /\ addr_gen v <> x) as Q.
    remember (fun g1 g2 v => block_mark (heapgraph_block g1 v) = block_mark (heapgraph_block g2 v)) as P.
    remember (fun (x1 x2: nat) => True) as R.
    pose proof (fr_general_prop depth from to p g g' _ Q P R) as HP. subst Q P R.
    apply HP ; clear HP ; try easy.
    + intros g1 g2 g3 w Hg1g2 Hg2g3.
      congruence.
    + intros from' g'' w to' u Hto' [Hu Hx__from'] Hw _ Efrom'.
      rewrite <- lcv_block_mark ; try easy.
      congruence.
    + intros depth' from' to' p' g1 g2 Hto' Hg1g2 w [Hw Hw__from'].
      split ; try easy.
      apply (fr_heapgraph_has_block _ _ _ _ _ _ Hto' Hg1g2 _ Hw).
    + intros g'' w to' u from' Hto' [Hu Hu__from'].
      split ; try easy.
      now apply lcv_heapgraph_has_block_old.
    + intros g'' f w u from' [Hu Hu__from'].
      split ; try easy.
      destruct Hu ; now constructor.
Qed.

Lemma fl_block_mark: forall depth from to l g g',
    heapgraph_has_gen g to -> forward_loop from to depth l g g' ->
    forall v, heapgraph_has_block g v -> addr_gen v <> from ->
              block_mark (heapgraph_block g v) = block_mark (heapgraph_block g' v).
Proof.
  intros. revert g g' H H0 v H1 H2. induction l; intros; inversion H0; subst.
  1: reflexivity. transitivity (block_mark (heapgraph_block g2 v)).
  - apply (fr_block_mark _ _ _ _ _ _ H H6 _ H1 H2).
  - apply IHl; [|assumption| |assumption].
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply fr_heapgraph_has_block; eauto.
Qed.


Lemma forward_loop_add_tail: forall from to depth l x g1 g2 g3 roots,
    forward_loop from to depth l g1 g2 ->
    forward_relation from to depth (forward_p2forward_t (inr x) roots g2) g2 g3 ->
    forward_loop from to depth (l +:: (inr x)) g1 g3.
Proof.
  intros. revert x g1 g2 g3 H H0. induction l; intros.
  - simpl. inversion H. subst. apply fl_cons with g3. 2: constructor. apply H0.
  - inversion H. subst. clear H. simpl app. apply fl_cons with g4. 1: assumption.
    apply IHl with g2; assumption.
Qed.

Lemma forward_p2t_inr_roots: forall v n roots g,
    forward_p2forward_t (inr (v, n)) roots g = forward_p2forward_t (inr (v, n)) nil g.
Proof. intros. simpl. reflexivity. Qed.

Lemma forward_loop_add_tail_vpp: forall from to depth x g g1 g2 g3 roots i,
    (0 <= i < Zlength (block_fields (heapgraph_block g x)))%Z ->
    forward_loop from to depth (VST.floyd.sublist.sublist 0 i (heapgraph_field_pairs g x))%Z g1 g2 ->
    forward_relation from to depth (forward_p2forward_t (inr (x, i)) roots g2) g2 g3 ->
    forward_loop from to depth (VST.floyd.sublist.sublist 0 (i + 1) (heapgraph_field_pairs g x))%Z g1 g3.
Proof.
  intros. rewrite <- heapgraph_field_pairs__Zlength in H. rewrite sublist_last_1; [|lia..].
  rewrite heapgraph_field_pairs__Zlength in H. rewrite heapgraph_field_pairs__Znth by assumption.
  apply forward_loop_add_tail with (g2 := g2) (roots := roots); assumption.
Qed.


Lemma fr_heapgraph_generation_is_unmarked: forall from to depth p g g',
    heapgraph_has_gen g to -> forward_relation from to depth p g g' ->
    forall gen, from  <> gen -> heapgraph_generation_is_unmarked g gen -> heapgraph_generation_is_unmarked g' gen.
Proof.
  intros. remember (fun (g: HeapGraph) (gen: nat) (x: nat) => x <> gen) as Q.
  remember (fun (g1 g2: HeapGraph) gen =>
              heapgraph_generation_is_unmarked g1 gen -> heapgraph_generation_is_unmarked g2 gen) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H3; clear H3; intros; try assumption; try reflexivity.
  - apply H4, H3. assumption.
  - rewrite <- H7 in H4. apply lcv_heapgraph_generation_is_unmarked; assumption.
Qed.


Lemma frl_roots_Zlength: forall from to f_info l roots g roots' g',
    Zlength roots = Zlength (live_roots_indices f_info) ->
    forward_roots_loop from to f_info l roots g roots' g' ->
    Zlength roots' = Zlength roots.
Proof.
  intros. induction H0. 1: reflexivity. rewrite IHforward_roots_loop.
  - apply upd_roots_Zlength; assumption.
  - rewrite upd_roots_Zlength; assumption.
Qed.


Opaque upd_roots.

Lemma frl_add_tail: forall from to f_info l i g1 g2 g3 roots1 roots2,
    forward_roots_loop from to f_info l roots1 g1 roots2 g2 ->
    forward_relation from to O (root2forward (Znth (Z.of_nat i) roots2)) g2 g3 ->
    forward_roots_loop
      from to f_info (l +:: i) roots1 g1
      (upd_roots from to (inl (Z.of_nat i)) g2 roots2 f_info) g3.
Proof.
  intros ? ? ? ?. induction l; intros.
  - simpl. inversion H. subst. apply frl_cons with g3. 2: constructor. apply H0.
  - inversion H. subst. clear H. simpl app. apply frl_cons with g4. 1: assumption.
    apply IHl; assumption.
Qed.

Transparent upd_roots.

Lemma frr_heapgraph_block_ptr: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, closure_has_v g1 v -> heapgraph_block_ptr g1 v = heapgraph_block_ptr g2 v.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_heapgraph_block_ptr; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_closure_has_v; eauto.
Qed.

Lemma frr_closure_has_v: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, closure_has_v g1 v -> closure_has_v g2 v.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_loop.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_closure_has_v; eauto.
Qed.

Lemma frr_heapgraph_generation_is_unmarked: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, gen <> from -> heapgraph_generation_is_unmarked g1 gen -> heapgraph_generation_is_unmarked g2 gen.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_loop.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_heapgraph_generation_is_unmarked; eauto.
Qed.

Lemma upd_roots_rf_compatible: forall from to f_info roots p g,
    roots_fi_compatible roots f_info ->
    roots_fi_compatible (upd_roots from to p g roots f_info) f_info.
Proof.
  intros. unfold upd_roots. destruct p; [|assumption]. destruct (Znth z roots).
  1: destruct s; assumption. if_tac. 2: assumption.
  destruct (block_mark (heapgraph_block g a)); apply upd_bunch_rf_compatible; assumption.
Qed.


Lemma upd_roots_not_pointing: forall from to i g roots f_info roots',
    copy_compatible g -> roots_graph_compatible roots g -> from <> to ->
    0 <= i < Zlength roots -> roots_fi_compatible roots f_info ->
    roots' = upd_roots from to (inl i) g roots f_info ->
    np_roots_rel from f_info roots roots' [i].
Proof.
  intros. unfold np_roots_rel. intros. simpl.
  assert (Zlength roots' = Zlength roots) by
      (rewrite H4; apply upd_roots_Zlength, (proj1 H3)).
  assert (0 <= j < Zlength roots). {
    rewrite <- H6. destruct (Z_lt_le_dec j (Zlength roots')).
    2: rewrite Znth_outofbounds in H5 by lia; inversion H5. split; auto.
    destruct (Z_lt_le_dec j 0); auto. rewrite Znth_outofbounds in H5 by lia.
    inversion H5. } simpl in H4. destruct H3. destruct (Znth i roots) eqn:? .
  - assert (roots' = roots) by (destruct s; assumption). clear H4. subst roots'.
    split; intros; auto. destruct H4; auto.
    destruct H3. apply H8 in H4; try assumption. rewrite Heqr, H5 in H4. inversion H4.
  - if_tac in H4.
    + destruct (block_mark (heapgraph_block g a)) eqn: ?; subst; split; intros.
      * destruct H4; auto. symmetry in H4. rewrite upd_bunch_same in H5 by assumption.
        inversion H5. red in H0. rewrite Forall_forall in H0.
        assert (heapgraph_has_block g a). {
          apply H0. rewrite <- filter_sum_right_In_iff, <- Heqr.
          apply Znth_In; assumption. } destruct (H _ H9 Heqb) as [_ ?]. auto.
      * assert (Znth j (live_roots_indices f_info) <>
                Znth i (live_roots_indices f_info)) by intuition. clear H4.
        rewrite upd_bunch_diff in H5; assumption.
      * destruct H4; auto. symmetry in H4. rewrite upd_bunch_same in H5 by assumption.
        inversion H5. unfold new_copied_v. simpl. auto.
      * assert (Znth j (live_roots_indices f_info) <>
                Znth i (live_roots_indices f_info)) by intuition. clear H4.
        rewrite upd_bunch_diff in H5; assumption.
    + split; intros; subst roots'; auto. destruct H10; auto.
      apply H8 in H4; try assumption. rewrite Heqr, H5 in H4. inversion H4.
      subst a. assumption.
Qed.


Lemma fr_copy_compatible (depth from to: nat) (p: forward_t) (g g': HeapGraph)
    (Hfrom__to: from <> to)
    (Hto: heapgraph_has_gen g to)
    (Hgg': forward_relation from to depth p g g')
    (Hg: copy_compatible g):
    copy_compatible g'.
Proof.
    remember (fun (g: HeapGraph) (v: Addr) (x: nat) => True) as Q.
    remember (fun g1 g2 (v: Addr) => copy_compatible g1 -> copy_compatible g2) as P.
    remember (fun (x y: nat) => x <> y) as R.
    pose proof (fr_general_prop depth from to p g g' _ Q P R) as HP. subst Q P R.
    apply HP ; clear HP ; try easy.
    + intros g1 g2 g3 _ Hg1g2 Hg2g3 Hg1.
      now apply Hg2g3, Hg1g2.
    + intros g'' f w _ Hg'' u Hu Eu.
      apply lgd_heapgraph_has_block in Hu.
      destruct (Hg'' u Hu Eu) as [H1u H2u].
      split ; try easy.
      destruct H1u ; now constructor.
    + intros from' g'' w to' _ Hto' _ Hw Hto'__from' Efrom' Hg''.
      subst from'.
      now apply lcv_copy_compatible.
Qed.

Lemma fr_right_roots_graph_compatible (depth from to: nat) (e: Addr * Z) (g g': HeapGraph) (roots: roots_t)
    (Hto: heapgraph_has_gen g to)
    (Hfrom: forward_p_compatible (inr e) roots g from)
    (Hgg': forward_relation from to depth (forward_p2forward_t (inr e) [] g) g g')
    (Hroots: roots_graph_compatible roots g):
    roots_graph_compatible roots g'.
Proof.
    simpl in Hfrom, Hgg'.
    destruct e as [e_addr e_z].
    destruct Hfrom as [_ [_ [Hfrom _]]].
    rewrite Hfrom in Hgg'. simpl in Hgg'.
    remember (fun (g: HeapGraph) (v: nat) (x: nat) => True) as Q.
    remember (fun g1 g2 (x: nat) => roots_graph_compatible roots g1->
                                    roots_graph_compatible roots g2) as P.
    remember (fun (x1 x2: nat) => True) as R.
    pose proof (fr_general_prop depth from to (field2forward (Znth e_z (heapgraph_block_cells g e_addr))) g g' _ Q P R) as HP.
    subst Q P R.
    apply HP ; clear HP ; try easy.
    - intros g1 g2 g3 _ Hg1g2 Hg2g3 Hg1.
      now apply Hg2g3, Hg1g2.
    - intros g'' e v _ Hg''.
      unfold roots_graph_compatible in *.
      now apply lgd_forall_heapgraph_has_block.
    - intros from' g'' u to' _ Hto' _ Hu _ Efrom' Hg''.
      now apply lcv_rgc_unchanged.
Qed.

Lemma fl_edge_roots_graph_compatible: forall depth from to l g g' v roots,
    addr_gen v <> from ->
    heapgraph_has_gen g to -> heapgraph_has_block g v -> block_mark (heapgraph_block g v) = false ->
    forward_loop from to depth (map (fun x : nat => inr (v, Z.of_nat x)) l) g g' ->
    (forall i, In i l -> i < length (block_fields (heapgraph_block g v)))%nat ->
    roots_graph_compatible roots g -> roots_graph_compatible roots g'.
Proof.
  do 4 intro. induction l; intros; simpl in H3; inversion H3; subst. 1: assumption.
  cut (roots_graph_compatible roots g2).
  - intros. apply (IHl g2 _ v); try assumption.
    + rewrite <- fr_graph_has_gen; eauto.
    + eapply fr_heapgraph_has_block; eauto.
    + rewrite <- H2. symmetry. eapply fr_block_mark; eauto.
    + assert (block_fields (heapgraph_block g v) = block_fields (heapgraph_block g2 v)) by
          (eapply fr_block_fields; eauto). rewrite <- H7.
      intros; apply H4; right; assumption.
  - specialize (H4 _ (in_eq a l)). eapply fr_right_roots_graph_compatible; eauto.
    simpl. intuition. rewrite Zlength_correct. apply inj_lt; assumption.
Qed.

Lemma fr_roots_outlier_compatible: forall from to p g roots f_info outlier,
    roots_outlier_compatible roots outlier ->
    roots_outlier_compatible (upd_roots from to p g roots f_info) outlier.
Proof.
  intros. destruct p; simpl in *. 2: assumption. destruct (Znth z roots) eqn: ?.
  + destruct s; assumption.
  + if_tac. 2: assumption.
    destruct (block_mark (heapgraph_block g a)); apply upd_roots_outlier_compatible; assumption.
Qed.

Lemma fr_roots_graph_compatible (depth from to: nat) (p : forward_p_type) (g g' : HeapGraph) (roots : roots_t) (f_info : fun_info)
    (Hto: heapgraph_has_gen g to)
    (Hp: forward_p_compatible p roots g from)
    (Hg: copy_compatible g)
    (Hfwd: forward_relation from to depth (forward_p2forward_t p roots g) g g')
    (Hfrom_to: from <> to)
    (Hroots: roots_graph_compatible roots g):
    roots_graph_compatible (upd_roots from to p g roots f_info) g'.
Proof.
  destruct p.
  - simpl in *. destruct (Znth z roots) eqn: ?; simpl in *.
    + destruct s; inversion Hfwd; subst; assumption.
    + assert (heapgraph_has_block g a). {
        red in Hroots. rewrite Forall_forall in Hroots. apply Hroots.
        rewrite <- filter_sum_right_In_iff. rewrite <- Heqr. apply Znth_In.
        assumption. }
      inversion Hfwd ; destruct (Nat.eq_dec (addr_gen v) from) eqn:HE_v_from ; subst ; rewrite HE_v_from ; try easy.
      * rename H3 into Eblock_mark ; rewrite Eblock_mark.
        apply upd_bunch_graph_compatible ; try assumption.
        now apply Hg.
      * rename H3 into Eblock_mark ; rewrite Eblock_mark.
        now apply lcv_roots_graph_compatible.
      * rename H2 into Eblock_mark ; rewrite Eblock_mark.
        assert (heapgraph_has_block new_g (new_copied_v g to)) by
          (subst new_g; apply lcv_heapgraph_has_block_new; assumption).
        remember (nat_inc_list (length (block_fields (heapgraph_block new_g (new_copied_v g to))))) as new_fields.
        assert (heapgraph_has_block new_g (new_copied_v g to)) by (subst new_g; apply lcv_heapgraph_has_block_new; assumption).
        remember (upd_bunch z f_info roots (inr (new_copied_v g to))) as roots'.
        assert (roots_graph_compatible roots' new_g) by (subst; subst new_g; apply lcv_roots_graph_compatible; assumption).
        assert (block_mark (heapgraph_block new_g (new_copied_v g to)) = false). {
          subst new_g. unfold lgraph_copy_v. rewrite <- lmc_block_mark.
          - now rewrite lacv_vlabel_new.
          - unfold new_copied_v. destruct a. destruct Heqroots'. simpl in *.
            destruct H1. intro HS. inversion HS. lia. }
        eapply (fl_edge_roots_graph_compatible depth0 (addr_gen a) to new_fields new_g _ (new_copied_v g to)) ; eauto.
        -- subst new_g. now rewrite <- lcv_graph_has_gen.
        -- now subst new_fields.
        -- intros idx Hidx. subst new_fields. now rewrite nat_inc_list_In_iff in Hidx.
  - simpl. eapply fr_right_roots_graph_compatible; eauto.
Qed.

Lemma fr_roots_compatible: forall depth from to p g g' roots f_info outlier,
    heapgraph_has_gen g to -> forward_p_compatible p roots g from -> copy_compatible g ->
    forward_relation from to depth (forward_p2forward_t p roots g) g g' ->
    roots_compatible g outlier roots -> from <> to ->
    roots_compatible g' outlier (upd_roots from to p g roots f_info).
Proof.
  intros. destruct H3. split.
  - apply fr_roots_outlier_compatible; assumption.
  - eapply fr_roots_graph_compatible; eauto.
Qed.

Lemma frl_not_pointing: forall from to f_info l roots1 g1 roots2 g2,
    copy_compatible g1 -> roots_graph_compatible roots1 g1 -> from <> to ->
    (forall i, In i l -> i < length roots1)%nat -> roots_fi_compatible roots1 f_info ->
    forward_roots_loop from to f_info l roots1 g1 roots2 g2 -> heapgraph_has_gen g1 to ->
    np_roots_rel from f_info roots1 roots2 (map Z.of_nat l).
Proof.
  do 4 intro. induction l; intros; inversion H4; subst.
  1: red; simpl; intros; intuition.
  remember (upd_roots from to (inl (Z.of_nat a)) g1 roots1 f_info) as roots3.
  simpl. apply np_roots_rel_cons with roots3.
  - apply (upd_roots_not_pointing from to _ g1); try assumption.
    split. 1: lia. rewrite Zlength_correct. apply inj_lt. apply H2. left; auto.
  - assert (Zlength roots3 = Zlength roots1) by
        (subst roots3; apply upd_roots_Zlength; apply (proj1 H3)).
    apply (IHl _ g3 _ g2); auto.
    + apply fr_copy_compatible in H8; assumption.
    + subst roots3. eapply fr_roots_graph_compatible; eauto. simpl. split. 1: lia.
      specialize (H2 _ (in_eq a l)). rewrite Zlength_correct. apply inj_lt; assumption.
    + intros. subst roots3. rewrite <- ZtoNat_Zlength, H6, ZtoNat_Zlength.
      apply H2; right; assumption.
    + subst roots3; apply upd_roots_rf_compatible; assumption.
    + rewrite <- (fr_graph_has_gen _ _ _ _ _ _ H5 H8); assumption.
Qed.


Lemma frr_not_pointing: forall from to f_info roots1 g1 roots2 g2,
    copy_compatible g1 -> roots_graph_compatible roots1 g1 -> from <> to ->
    heapgraph_has_gen g1 to -> roots_fi_compatible roots1 f_info ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    roots_have_no_gen roots2 from.
Proof.
  intros. unfold forward_roots_relation in H0. eapply frl_not_pointing in H0; eauto.
  red; intros. 2: intros; rewrite nat_inc_list_In_iff in H5; assumption. red in H0.
  apply In_Znth in H5. destruct H5 as [i [? ?]]. specialize (H0 _ _ H6). destruct H0.
  apply H0. destruct H3 as [? _].
  replace (length roots1) with (length (live_roots_indices f_info)) by
      (rewrite <- !ZtoNat_Zlength, H3; reflexivity).
  remember (live_roots_indices f_info). rewrite map_map.
  assert (map (fun x : nat => Znth (Z.of_nat x) l) (nat_inc_list (length l)) = l). {
    clear. rewrite Znth_list_eq. split.
    - rewrite Zlength_map, !Zlength_correct, nat_inc_list_length. reflexivity.
    - intros. rewrite Zlength_map in H. rewrite Znth_map by assumption. f_equal.
      rewrite <- nth_Znth by assumption. rewrite nat_inc_list_nth.
      1: apply Z2Nat.id; lia. rewrite Zlength_correct, nat_inc_list_length in H.
      rep_lia. } rewrite H8. clear H8. apply Znth_In. apply frl_roots_Zlength in H4.
  2: subst; assumption. rewrite <- H3, <- H4. assumption.
Qed.


Lemma frr_graph_has_gen: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to ->
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, heapgraph_has_gen g1 gen <-> heapgraph_has_gen g2 gen.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_graph_has_gen; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
Qed.


Lemma fr_O_dst_unchanged_root (from to: nat) (r: root_t) (g g': HeapGraph)
    (Hgg': forward_relation from to O (root2forward r) g g')
    (e: Field)
    (He: heapgraph_has_block g (field_addr e)):
    dst g e = dst g' e.
Proof.
    destruct r; [destruct s|]; simpl in Hgg'; inversion Hgg'; subst; try reflexivity.
    simpl. rewrite pcv_dst_old. 1: reflexivity. destruct e as [[gen vidx] eidx].
    unfold new_copied_v. simpl in *. intro.
    inversion H. subst.
    pose proof (heapgraph_has_block__has_index He) as F.
    red in F. simpl in F.
    lia.
Qed.

Lemma frr_dst_unchanged: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall e, heapgraph_has_block g1 (field_addr e) -> dst g1 e = dst g2 e.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_O_dst_unchanged_root; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_heapgraph_has_block; eauto.
Qed.

Lemma fr_O_heapgraph_has_block_inv (from to: nat) (p: forward_t) (g g': HeapGraph)
    (Hto: heapgraph_has_gen g to)
    (Hgg': forward_relation from to O p g g')
    (v: Addr)
    (Hv: heapgraph_has_block g' v):
    heapgraph_has_block g v \/ v = new_copied_v g to.
Proof.
    inversion Hgg' ; subst ; try (now left).
    + now apply lcv_heapgraph_has_block_inv in Hv.
    + left.
      subst new_g.
      now rewrite <- lgd_heapgraph_has_block in Hv.
    + subst new_g.
      rewrite <- lgd_heapgraph_has_block in Hv.
      now apply lcv_heapgraph_has_block_inv in Hv.
Qed.


Lemma fr_O_gen_v_num_to: forall from to p g g',
    heapgraph_has_gen g to -> forward_relation from to O p g g' ->
    (heapgraph_generation_block_count g to <= heapgraph_generation_block_count g' to)%nat.
Proof.
  intros. inversion H0; subst; try lia; [|subst new_g..].
  - apply lcv_gen_v_num_to; auto.
  - rewrite heapgraph_generation_block_count__labeledgraph_gen_dst. lia.
  - rewrite heapgraph_generation_block_count__labeledgraph_gen_dst. apply lcv_gen_v_num_to. assumption.
Qed.

Lemma frr_gen_v_num_to: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    (heapgraph_generation_block_count g1 to <= heapgraph_generation_block_count g2 to)%nat.
Proof.
  intros. induction H0. 1: lia. transitivity (heapgraph_generation_block_count g2 to).
  - eapply fr_O_gen_v_num_to; eauto.
  - apply IHforward_roots_loop; rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma frr_heapgraph_has_block_inv (from to: nat) (f_info: fun_info) (roots1: list root_t) (g1: HeapGraph) (roots2: roots_t) (g2: HeapGraph)
    (Hto: heapgraph_has_gen g1 to)
    (Hg1g2: forward_roots_relation from to f_info roots1 g1 roots2 g2)
    (v: Addr)
    (Hv: heapgraph_has_block g2 v):
    heapgraph_has_block g1 v \/ (
      addr_gen v = to /\
      heapgraph_generation_block_count g1 to <= addr_block v < heapgraph_generation_block_count g2 to
    )%nat.
Proof.
    induction Hg1g2 ; try (now left).
    assert (heapgraph_has_gen g2 to) by (rewrite <- fr_graph_has_gen; eauto).
    specialize (IHHg1g2 H0 Hv).
    destruct IHHg1g2.
    - eapply (fr_O_heapgraph_has_block_inv from to _ g1 g2) in H1; eauto. destruct H1.
      1: left; assumption. right. unfold new_copied_v in H1. subst v.
      pose proof (heapgraph_has_block__has_index Hv) as Hindex.
      unfold heapgraph_generation_block_count.
      red in Hindex ; simpl in Hindex ; simpl.
      lia.
    - right.
      apply fr_O_gen_v_num_to in H ; try easy.
      lia.
Qed.

Lemma frr_block_fields: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, heapgraph_has_block g1 v -> block_fields (heapgraph_block g1 v) = block_fields (heapgraph_block g2 v).
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_block_fields; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_heapgraph_has_block; eauto.
Qed.

Lemma frr_gen2gen_no_edge (from to: nat) (f_info: fun_info) (roots1: list root_t) (g1: HeapGraph) (roots2: roots_t) (g2: HeapGraph)
    (Hto: heapgraph_has_gen g1 to)
    (Hg1g2: forward_roots_relation from to f_info roots1 g1 roots2 g2)
    (gen1 gen2: nat)
    (Hgen1: gen1 <> to)
    (Hgen1gen2: gen2gen_no_edge g1 gen1 gen2):
    gen2gen_no_edge g2 gen1 gen2.
Proof.
    unfold gen2gen_no_edge in *.
    intros vidx eidx Hg2.
    cut (heapgraph_has_field g1 {| field_addr := {| addr_gen := gen1; addr_block := vidx |} ; field_index := eidx |}).
    + intros. erewrite <- frr_dst_unchanged; eauto.
      apply (heapgraph_has_field__has_block H).
    + pose proof (heapgraph_has_field__has_block Hg2) as Hblock.
      eapply frr_heapgraph_has_block_inv in Hblock ; eauto.
      destruct Hblock as [Hblock | [Eto Hblock]] ; try easy.
      refine {|
        heapgraph_has_field__has_block := _;
        heapgraph_has_field__in := _;
      |} ; try easy.
      simpl in *.
      cut (heapgraph_block_fields g1 {| addr_gen := gen1 ; addr_block := vidx |} = heapgraph_block_fields g2 {| addr_gen := gen1 ; addr_block := vidx |}).
      - pose proof (heapgraph_has_field__in Hg2) as Hfield.
        intro Eg1g2.
        now rewrite Eg1g2.
      - unfold heapgraph_block_fields, heapgraph_block_cells.
        erewrite frr_block_fields; eauto.
Qed.

Lemma fr_O_dst_unchanged_field (from to: nat) (v: Addr) (n: nat) (g g': HeapGraph)
    (Hfrom: forward_p_compatible (inr (v, Z.of_nat n)) [] g from)
    (Hgg': forward_relation from to O (forward_p2forward_t (inr (v, Z.of_nat n)) [] g) g g')
    (e: Field)
    (He: heapgraph_has_block g (field_addr e))
    (H'e: e <> {| field_addr := v; field_index := n |}):
    dst g e = dst g' e.
Proof.
    simpl in *. destruct Hfrom as [Hv [Hn [Hmark_v Hv__from]]].
    rewrite Hmark_v in Hgg' ; simpl in Hgg'.
    remember (Znth (Z.of_nat n) (heapgraph_block_cells g v)) as c eqn:Ec.
    assert (forall e0, inr e0 = Znth (Z.of_nat n) (heapgraph_block_cells g v) -> e0 <> e) as Hnth.
    {
      intros.
      symmetry in H.
      apply heapgraph_block_cells_Znth_edge in H ; try easy.
      rewrite Nat2Z.id in H.
      congruence.
    }
    destruct c; [destruct s |]; simpl in Hgg'; inversion Hgg'; subst; try easy.
    + subst new_g.
      rewrite lgd_dst_old ; try easy.
      now apply Hnth.
    + subst new_g.
      rewrite lgd_dst_old ; try now apply Hnth.
      simpl.
      rewrite pcv_dst_old ; try easy.
      intro F. rewrite F in He.
      pose proof (heapgraph_has_block__has_index He) as F'.
      simpl in F'. red in F'.
      lia.
Qed.


Lemma frr_heapgraph_has_block: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall v, heapgraph_has_block g1 v -> heapgraph_has_block g2 v.
Proof.
  intros. induction H0; subst. 1: assumption. cut (heapgraph_has_block g2 v).
  - intros. apply IHforward_roots_loop; auto. erewrite <- fr_graph_has_gen; eauto.
  - eapply fr_heapgraph_has_block; eauto.
Qed.

Lemma fr_O_dst_changed_field: forall from to v n g g',
    copy_compatible g -> no_dangling_dst g -> from <> to -> heapgraph_has_gen g to ->
    forward_p_compatible (inr (v, Z.of_nat n)) [] g from ->
    forward_relation from to O (forward_p2forward_t (inr (v, Z.of_nat n)) [] g) g g' ->
    forall e, Znth (Z.of_nat n) (heapgraph_block_cells g' v) = inr e ->
              addr_gen (dst g' e) <> from.
Proof.
  intros. simpl in *. destruct H3 as [? [? [? ?]]]. rewrite H7 in H4. simpl in H4.
  assert (heapgraph_block_cells g v = heapgraph_block_cells g' v) by
      (unfold heapgraph_block_cells; erewrite fr_block_fields; eauto). rewrite <- H9 in *.
  clear H9. remember (Znth (Z.of_nat n) (heapgraph_block_cells g v)). destruct c; inversion H5.
  subst. clear H5. symmetry in Heqc. pose proof Heqc.
  apply heapgraph_block_cells_Znth_edge in Heqc. 2: assumption. simpl in H4. subst.
  rewrite Nat2Z.id in *.
  inversion H4; subst; try assumption; subst new_g; rewrite lgd_dst_new.
  - apply H in H12. 1: destruct H12; auto. specialize (H0 _ H3). apply H0.
    unfold heapgraph_block_fields. rewrite <- filter_sum_right_In_iff, <- H5. apply Znth_In.
    rewrite heapgraph_block_cells_eq_length. assumption.
  - unfold new_copied_v. simpl. auto.
Qed.

Lemma fr_O_no_dangling_dst: forall from to p g g' roots,
    forward_p_compatible p roots g from -> heapgraph_has_gen g to ->
    roots_graph_compatible roots g -> copy_compatible g ->
    forward_relation from to O (forward_p2forward_t p roots g) g g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros. inversion H3; subst; try assumption.
  - destruct p; simpl in H5.
    + destruct (Znth z roots) eqn:? ; [destruct s|]; simpl in H5; inversion H5.
      subst. clear H5. apply lcv_no_dangling_dst; auto. red in H1.
      rewrite Forall_forall in H1. apply H1. rewrite <- filter_sum_right_In_iff.
      rewrite <- Heqr. apply Znth_In. assumption.
    + destruct p. simpl in H. destruct H as [? [? [? ?]]]. rewrite H8 in H5.
      simpl in H5. destruct (Znth z (heapgraph_block_cells g a)); [destruct s|];
                     simpl in H5; inversion H5.
  - subst new_g. apply lgd_no_dangling_dst_copied_vert; auto.
    destruct p; simpl in H5.
    + destruct (Znth z roots); [destruct s|]; simpl in H5; inversion H5.
    + destruct p. simpl in H. destruct H as [? [? [? ?]]]. rewrite H7 in H5.
      simpl in H5. destruct (Znth z (heapgraph_block_cells g a)) eqn:? ; [destruct s|];
                     simpl in H5; inversion H5. subst. clear H5.
      specialize (H4 _ H). apply H4. unfold heapgraph_block_fields.
      rewrite <- filter_sum_right_In_iff, <- Heqc. apply Znth_In.
      rewrite heapgraph_block_cells_eq_length. assumption.
  - subst new_g. apply lgd_no_dangling_dst. 1: apply lcv_heapgraph_has_block_new; auto.
    apply lcv_no_dangling_dst; auto. destruct p; simpl in H5.
    + destruct (Znth z roots); [destruct s|]; simpl in H5; inversion H5.
    + destruct p. simpl in H. destruct H as [? [? [? ?]]]. rewrite H8 in H5.
      simpl in H5. destruct (Znth z (heapgraph_block_cells g a)) eqn:? ; [destruct s|];
                     simpl in H5; inversion H5. subst. clear H5.
      specialize (H4 _ H). apply H4. unfold heapgraph_block_fields.
      rewrite <- filter_sum_right_In_iff, <- Heqc. apply Znth_In.
      rewrite heapgraph_block_cells_eq_length. assumption.
Qed.

Lemma frr_heapgraph_generation_unchanged: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, gen <> to -> heapgraph_generation g1 gen = heapgraph_generation g2 gen.
Proof.
  intros. induction H0. 1: reflexivity. rewrite <- IHforward_roots_loop.
  - eapply fr_O_heapgraph_generation_unchanged; eauto.
  - rewrite <- fr_graph_has_gen; eauto.
Qed.

Lemma frr_firstn_gen_clear: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen, (gen <= to)%nat ->
                firstn_gen_clear g1 gen -> firstn_gen_clear g2 gen.
Proof.
  intros. unfold firstn_gen_clear, graph_gen_clear in *. intros.
  erewrite <- frr_heapgraph_generation_unchanged; eauto. lia.
Qed.

Lemma fr_O_stcg: forall from to p g1 g2,
    heapgraph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen1 gen2, heapgraph_has_gen g1 gen2 -> gen2 <> to ->
                      heapgraph_generation_can_copy g1 gen1 gen2 -> heapgraph_generation_can_copy g2 gen1 gen2.
Proof.
  intros. unfold heapgraph_generation_can_copy in *.
  erewrite <- (fr_O_graph_gen_size_unchanged from to); eauto.
  erewrite <- (fr_O_graph_remember_size_unchanged from to); eauto.
Qed.

Lemma frr_stcg: forall from to f_info roots1 g1 roots2 g2,
    heapgraph_has_gen g1 to -> forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    forall gen1 gen2, heapgraph_has_gen g1 gen2 -> gen2 <> to ->
                      heapgraph_generation_can_copy g1 gen1 gen2 -> heapgraph_generation_can_copy g2 gen1 gen2.
Proof.
  intros. induction H0. 1: assumption. apply IHforward_roots_loop.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - erewrite <- (fr_graph_has_gen O from to); eauto.
  - eapply (fr_O_stcg from to); eauto.
Qed.

Lemma frr_copy_compatible: forall from to f_info roots g roots' g',
    from <> to -> heapgraph_has_gen g to ->
    forward_roots_relation from to f_info roots g roots' g' ->
    copy_compatible g -> copy_compatible g'.
Proof.
  intros. induction H1. 1: assumption. apply IHforward_roots_loop.
  - rewrite <- fr_graph_has_gen; eauto.
  - eapply fr_copy_compatible; eauto.
Qed.

Lemma frl_no_dangling_dst: forall from to f_info l roots g roots' g',
    heapgraph_has_gen g to -> copy_compatible g -> from <> to ->
    (forall i, In i l -> i < length roots)%nat ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    roots_graph_compatible roots g ->
    forward_roots_loop from to f_info l roots g roots' g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  do 4 intro. induction l; intros; inversion H5; subst. 1: assumption.
  assert (forward_p_compatible (inl (Z.of_nat a)) roots g from). {
    simpl. split. 1: lia. rewrite Zlength_correct. apply inj_lt.
    apply H2; left; reflexivity. } cut (no_dangling_dst g2).
  - intros. eapply (IHl (upd_roots from to (inl (Z.of_nat a)) g roots f_info)
                        g2 roots'); eauto.
    + erewrite <- fr_graph_has_gen; eauto.
    + eapply (fr_copy_compatible O from to _ g); eauto.
    + intros. rewrite <- ZtoNat_Zlength, upd_roots_Zlength, ZtoNat_Zlength; auto.
      apply H2. right; assumption.
    + rewrite upd_roots_Zlength; assumption.
    + eapply fr_roots_graph_compatible; eauto.
  - fold (forward_p2forward_t (inl (Z.of_nat a)) roots g) in H9.
    eapply fr_O_no_dangling_dst; eauto.
Qed.

Lemma frr_no_dangling_dst: forall from to f_info roots g roots' g',
    heapgraph_has_gen g to -> copy_compatible g -> from <> to ->
    Zlength roots = Zlength (live_roots_indices f_info) ->
    roots_graph_compatible roots g ->
    forward_roots_relation from to f_info roots g roots' g' ->
    no_dangling_dst g -> no_dangling_dst g'.
Proof.
  intros. eapply frl_no_dangling_dst; eauto. intros.
  rewrite nat_inc_list_In_iff in H6. assumption.
Qed.

Lemma frr_roots_fi_compatible: forall from to f_info roots1 g1 roots2 g2,
    forward_roots_relation from to f_info roots1 g1 roots2 g2 ->
    roots_fi_compatible roots1 f_info -> roots_fi_compatible roots2 f_info.
Proof.
  intros. induction H; subst. 1: assumption. apply IHforward_roots_loop.
  apply upd_roots_rf_compatible; assumption.
Qed.
