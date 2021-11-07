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

From CertiGraph Require Export graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.compatible.
From CertiGC Require Import model.constants.
From CertiGC Require Import model.copy.
From CertiGC Require Import model.cut.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.heap.
From CertiGC Require Import model.thread_info.
From CertiGC Require Import model.update.
From CertiGC Require Import model.util.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.


Definition forward_t: Type := Z + GC_Pointer + Addr + Field.

Definition root2forward (r: root_t): forward_t :=
  match r with
  | inl (inl z) => inl (inl (inl z))
  | inl (inr p) => inl (inl (inr p))
  | inr v => inl (inr v)
  end.

Definition field2forward (f: field_t): forward_t :=
  match f with
  | inl (inl z) => inl (inl (inl z))
  | inl (inr p) => inl (inl (inr p))
  | inr e => inr e
  end.

Definition forward_p_type: Type := Z + (Addr * Z).

Definition forward_p2forward_t
           (p: forward_p_type) (roots: roots_t) (g: HeapGraph): forward_t :=
  match p with
  | inl root_index => root2forward (Znth root_index roots)
  | inr (v, n) => if (vlabel g v).(block_mark) && (n =? 0)
                  then (inl (inr (vlabel g v).(block_copied_vertex)))
                  else field2forward (Znth n (make_fields g v))
  end.

Definition vertex_pos_pairs (g: HeapGraph) (v: Addr) : list (forward_p_type) :=
  map (fun x => inr (v, Z.of_nat x))
      (nat_inc_list (length (block_fields (vlabel g v)))).

Inductive forward_relation (from to: nat):
  nat -> forward_t -> HeapGraph -> HeapGraph -> Prop :=
| fr_z: forall depth z g, forward_relation from to depth (inl (inl (inl z))) g g
| fr_p: forall depth p g, forward_relation from to depth (inl (inl (inr p))) g g
| fr_v_not_in: forall depth v g,
    addr_gen v <> from -> forward_relation from to depth (inl (inr v)) g g
| fr_v_in_forwarded: forall depth v g,
    addr_gen v = from -> (vlabel g v).(block_mark) = true ->
    forward_relation from to depth (inl (inr v)) g g
| fr_v_in_not_forwarded_O: forall v g,
    addr_gen v = from -> (vlabel g v).(block_mark) = false ->
    forward_relation from to O (inl (inr v)) g (lgraph_copy_v g v to)
| fr_v_in_not_forwarded_Sn: forall depth v g g',
    addr_gen v = from -> (vlabel g v).(block_mark) = false ->
    let new_g := lgraph_copy_v g v to in
    forward_loop from to depth (vertex_pos_pairs new_g (new_copied_v g to)) new_g g' ->
    forward_relation from to (S depth) (inl (inr v)) g g'
| fr_e_not_to: forall depth e (g: HeapGraph),
    addr_gen (dst g e) <> from -> forward_relation from to depth (inr e) g g
| fr_e_to_forwarded: forall depth e (g: HeapGraph),
    addr_gen (dst g e) = from -> (vlabel g (dst g e)).(block_mark) = true ->
    let new_g := labeledgraph_gen_dst g e (vlabel g (dst g e)).(block_copied_vertex) in
    forward_relation from to depth (inr e) g new_g
| fr_e_to_not_forwarded_O: forall e (g: HeapGraph),
    addr_gen (dst g e) = from -> (vlabel g (dst g e)).(block_mark) = false ->
    let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                      (new_copied_v g to) in
    forward_relation from to O (inr e) g new_g
| fr_e_to_not_forwarded_Sn: forall depth e (g g': HeapGraph),
    addr_gen (dst g e) = from -> (vlabel g (dst g e)).(block_mark) = false ->
    let new_g := labeledgraph_gen_dst (lgraph_copy_v g (dst g e) to) e
                                      (new_copied_v g to) in
    forward_loop from to depth (vertex_pos_pairs new_g (new_copied_v g to)) new_g g' ->
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
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall x, graph_has_gen g x <-> graph_has_gen g' x.
Proof.
  intros. remember (fun to g1 g2 =>
                      graph_has_gen g1 to ->
                      forall x, graph_has_gen g1 x <-> graph_has_gen g2 x) as P.
  pose proof (fr_general_prop_bootstrap depth from to p g g' P). subst P.
  apply H1; clear H1; intros; try assumption; try reflexivity.
  - rewrite H1 by assumption. apply H2. rewrite <- H1; assumption.
  - apply lcv_graph_has_gen. assumption.
Qed.

Lemma fl_graph_has_gen: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall x, graph_has_gen g x <-> graph_has_gen g' x.
Proof.
  intros. revert g g' H H0 x. induction l; intros; inversion H0. 1: reflexivity.
  subst. assert (forall y, graph_has_gen g y <-> graph_has_gen g2 y) by
      (intros; apply (fr_graph_has_gen _ _ _ _ _ _ H H4)).
  transitivity (graph_has_gen g2 x). 1: apply H1. rewrite H1 in H.
  apply IHl; assumption.
Qed.

Lemma fr_general_prop:
  forall depth from to p g g' A (Q: HeapGraph -> A -> nat -> Prop)
         (P: HeapGraph -> HeapGraph -> A -> Prop) (R: nat -> nat -> Prop),
    R from to -> graph_has_gen g to -> (forall g v, P g g v) ->
    (forall g1 g2 g3 v, P g1 g2 v -> P g2 g3 v -> P g1 g3 v) ->
    (forall g e v x, P g (labeledgraph_gen_dst g e v) x) ->
    (forall from g v to x,
        graph_has_gen g to -> Q g x from -> (vlabel g v).(block_mark) = false ->
        R from to -> addr_gen v = from -> P g (lgraph_copy_v g v to) x) ->
    (forall depth from to p g g',
        graph_has_gen g to -> forward_relation from to depth p g g' ->
        forall v, Q g v from -> Q g' v from) ->
    (forall g v to x from, graph_has_gen g to -> Q g x from ->
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
               graph_has_gen g1 to -> forward_loop from to depth l g1 g2 ->
               R from to -> forall v, Q g1 v from -> P g1 g2 v). {
      induction l; intros; inversion H11. 1: apply H1. subst.
      specialize (IHdepth _ _ _ _ _ _ _ _ _ H12 H10 H1 H2 H3 H4 H5 H6 H7 H17 _ H13).
      apply (H5 _ _ _ _ _ _ H10 H17) in H13.
      rewrite (fr_graph_has_gen _ _ _ _ _ _ H10 H17) in H10.
      specialize (IHl _ _ _ _ H10 H20 H12 _ H13). apply (H2 _ _ _ _ IHdepth IHl). }
    clear IHdepth. inversion H8; subst; try (specialize (H1 g' v); assumption).
    + cut (P g new_g v).
      * intros. apply (H2 g new_g g'). 1: assumption.
        assert (graph_has_gen new_g to) by
            (subst new_g; rewrite <- lcv_graph_has_gen; assumption).
        apply (H10 _ _ _ _ _ H12 H14 H). subst new_g. apply H6; assumption.
      * subst new_g. apply (H4 (addr_gen v0)); [assumption.. | reflexivity].
    + subst new_g. apply H3.
    + cut (P g new_g v).
      * intros. apply (H2 g new_g g'). 1: assumption.
        assert (graph_has_gen new_g to) by
            (subst new_g; rewrite lgd_graph_has_gen, <- lcv_graph_has_gen; assumption).
        apply (H10 _ _ _ _ _ H12 H14 H). subst new_g. apply H7, H6; assumption.
      * subst new_g. remember (lgraph_copy_v g (dst g e) to) as g1.
        remember (labeledgraph_gen_dst g1 e (new_copied_v g to)) as g2.
        cut (P g1 g2 v). 2: subst; apply H3. intros. apply (H2 g g1 g2).
        2: assumption. subst g1.
        apply (H4 (addr_gen (dst g e))); [assumption.. | reflexivity].
Qed.

Lemma fr_graph_has_v: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall v, graph_has_v g v -> graph_has_v g' v.
Proof.
  intros. remember (fun (g: HeapGraph) (v: Addr) (x: nat) => True) as Q.
  remember (fun g1 g2 v => graph_has_v g1 v -> graph_has_v g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - apply H3, H2. assumption.
  - unfold lgraph_copy_v. rewrite <- lmc_graph_has_v.
    apply lacv_graph_has_v_old; assumption.
Qed.


Lemma fr_gen_start: forall depth from to p g g',
    graph_has_gen g to -> forward_relation from to depth p g g' ->
    forall x, gen_start g x = gen_start g' x.
Proof.
  intros. remember (fun (g: HeapGraph) (v: nat) (x: nat) => True) as Q.
  remember (fun g1 g2 x => gen_start g1 x = gen_start g2 x) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g g' _ Q P R). subst Q P R.
  apply H1; clear H1; intros; try assumption; try reflexivity.
  - rewrite H1. assumption.
  - rewrite lcv_gen_start; [reflexivity | assumption].
Qed.

Lemma fl_gen_start: forall from to depth l g g',
    graph_has_gen g to -> forward_loop from to depth l g g' ->
    forall x, gen_start g x = gen_start g' x.
Proof.
  intros. revert g g' H H0 x. induction l; intros; inversion H0. 1: reflexivity.
  subst. transitivity (gen_start g2 x).
  - apply (fr_gen_start _ _ _ _ _ _ H H4).
  - assert (graph_has_gen g2 to) by
        (rewrite <- (fr_graph_has_gen _ _ _ _ _ _ H H4); assumption).
    apply IHl; assumption.
Qed.

Lemma fr_vertex_size: forall depth from to p g1 g2,
    graph_has_gen g1 to -> forward_relation from to depth p g1 g2 ->
    forall v, graph_has_v g1 v -> vertex_size g1 v = vertex_size g2 v.
Proof.
  intros. remember (fun g v (x: nat) => graph_has_v g v) as Q.
  remember (fun g1 g2 v => vertex_size g1 v = vertex_size g2 v) as P.
  remember (fun (x1 x2: nat) => True) as R.
  pose proof (fr_general_prop depth from to p g1 g2 _ Q P R). subst Q P R.
  apply H2; clear H2; intros; try assumption; try reflexivity.
  - rewrite H2. assumption.
  - rewrite lcv_vertex_size_old; [reflexivity | assumption..].
  - apply (fr_graph_has_v _ _ _ _ _ _ H2 H3 _ H4).
  - apply lcv_graph_has_v_old; assumption.
Qed.

Lemma fr_O_nth_gen_unchanged: forall from to p g1 g2,
    graph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen, gen <> to -> nth_gen g1 gen = nth_gen g2 gen.
Proof.
  intros. inversion H0; subst; try reflexivity.
  - rewrite lcv_nth_gen; auto.
  - subst new_g. transitivity (nth_gen (lgraph_copy_v g1 (dst g1 e) to) gen).
    2: reflexivity. rewrite lcv_nth_gen; [reflexivity | assumption..].
Qed.

Lemma fr_O_graph_gen_size_unchanged: forall from to p g1 g2,
    graph_has_gen g1 to -> forward_relation from to O p g1 g2 ->
    forall gen, graph_has_gen g1 gen -> gen <> to ->
                graph_gen_size g1 gen = graph_gen_size g2 gen.
Proof.
  intros. unfold graph_gen_size.
  erewrite <- (fr_O_nth_gen_unchanged from to _ g1 g2); eauto.
  unfold previous_vertices_size. apply fold_left_ext. intros.
  unfold vertex_size_accum. f_equal. rewrite nat_inc_list_In_iff in H3.
  eapply (fr_vertex_size O from to); eauto. split; simpl; assumption.
Qed.


Definition forward_p_compatible
           (p: forward_p_type) (roots: roots_t) (g: HeapGraph) (from: nat): Prop :=
  match p with
  | inl root_index => 0 <= root_index < Zlength roots
  | inr (v, n) => graph_has_v g v /\ 0 <= n < Zlength (vlabel g v).(block_fields) /\
                  (vlabel g v).(block_mark) = false /\ addr_gen v <> from
  end.


Definition upd_roots (from to: nat) (forward_p: forward_p_type)
           (g: HeapGraph) (roots: roots_t) (f_info: fun_info): roots_t :=
  match forward_p with
  | inr _ => roots
  | inl index => match Znth index roots with
                 | inl (inl z) => roots
                 | inl (inr p) => roots
                 | inr v => if Nat.eq_dec (addr_gen v) from
                            then if (vlabel g v).(block_mark)
                                 then upd_bunch index f_info roots
                                                (inr (vlabel g v).(block_copied_vertex))
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
  destruct (block_mark (vlabel g a)); rewrite upd_bunch_Zlength; auto.
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
  graph_has_gen g from /\ graph_has_gen g to /\
  copy_compatible g /\ no_dangling_dst g.

Lemma lcv_forward_condition: forall
    g t_info v to index uv
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (vertex_size g v))
    (Hm : 0 <= index < MAX_ARGS),
    addr_gen v <> to -> graph_has_v g v -> block_mark (vlabel g v) = false ->
    forward_condition g t_info (addr_gen v) to ->
    forward_condition
      (lgraph_copy_v g v to)
      (update_thread_info_arg
         (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh) index uv Hm)
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
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (vertex_size g v)),
    addr_gen v <> to -> graph_has_v g v -> block_mark (vlabel g v) = false ->
    forward_condition g t_info (addr_gen v) to ->
    forward_condition (lgraph_copy_v g v to)
         (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh)
      (addr_gen v) to.
Proof.
  intros. destruct H2 as [? [? [? [? ?]]]]. split; [|split; [|split; [|split]]].
  - apply forward_estc_unchanged; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_graph_has_gen; assumption.
  - apply lcv_copy_compatible; assumption.
  - apply lcv_no_dangling_dst; assumption.
Qed.