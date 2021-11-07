From Coq Require Import Logic.FinFun.
From Coq Require Import Lists.List.
From Coq Require Import micromega.Lia.
From Coq Require Import ZArith.ZArith.

From VST Require Import floyd.proofauto.

From CertiGraph Require Import graph.graph_gen.
From CertiGraph Require Import graph.graph_model.
From CertiGraph Require Import lib.EquivDec_ext.
From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.compatible.
From CertiGC Require Import model.cut.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.heap.
From CertiGC Require Import model.thread_info.
From CertiGC Require Import model.util.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.


Definition copy_v_add_edge
           (s: Addr) (g: PreGraph Addr Field) (p: Field * Addr):
  PreGraph Addr Field := pregraph_add_edge g (fst p) s (snd p).

Lemma flcvae_dst_old: forall g new (l: list (Field * Addr)) e,
    ~ In e (map fst l) -> dst (fold_left (copy_v_add_edge new) l g) e = dst g e.
Proof.
  intros. revert g H. induction l; intros; simpl. 1: reflexivity.
  rewrite IHl. 2: intro; apply H; simpl; right; assumption. simpl.
  unfold updateEdgeFunc. rewrite if_false. 1: reflexivity. unfold equiv. intro.
  apply H. simpl. left; assumption.
Qed.

Lemma flcvae_dst_new: forall g new (l: list (Field * Addr)) e v,
    NoDup (map fst l) -> In (e, v) l ->
    dst (fold_left (copy_v_add_edge new) l g) e = v.
Proof.
  intros. revert g. induction l. 1: simpl in H; exfalso; assumption.
  intros. simpl in *. destruct H0.
  - subst a. rewrite flcvae_dst_old.
    + simpl. unfold updateEdgeFunc. rewrite if_true; reflexivity.
    + simpl in H. apply NoDup_cons_2 in H. assumption.
  - apply IHl; [apply NoDup_cons_1 in H|]; assumption.
Qed.


Definition pregraph_copy_v (g: HeapGraph) (old_v new_v: Addr) : PreGraph Addr Field :=
  let old_edges := get_edges g old_v in
  let new_edges := combine (repeat new_v (length old_edges)) (map field_index old_edges) in
  let new_edge_dst_l := combine new_edges (map (dst g) old_edges) in
  let new_edge_dst_l' := map (fun x => ({| field_addr := fst (fst x); field_index := snd (fst x) |}, snd x)) new_edge_dst_l
  in fold_left (copy_v_add_edge new_v) new_edge_dst_l' (pregraph_add_vertex g new_v).

Lemma pcv_dst_old (g: HeapGraph) (old new: Addr) (e: Field)
    (He: field_addr e <> new):
    dst (pregraph_copy_v g old new) e = dst g e.
Proof.
  unfold pregraph_copy_v. rewrite flcvae_dst_old. 1: simpl; reflexivity.
  intro F.
  rewrite map_map in F.
  apply in_map_iff in F. destruct F as [[[e_gen e_block] dst] [Ee' F]]. subst. simpl in *.
  repeat apply in_combine_l in F. now apply repeat_spec in F.
Qed.

Lemma pcv_dst_new (g: HeapGraph) (old new: Addr) (n: nat)
    (Hn: In n (map field_index (get_edges g old))):
    dst (pregraph_copy_v g old new) {| field_addr := new; field_index := n|} = dst g {| field_addr := old; field_index := n|}.
Proof.
  unfold pregraph_copy_v. rewrite flcvae_dst_new with (v := dst g {| field_addr := old; field_index := n|}).
  - reflexivity.
  - assert (map_fst_map_combine: forall {X Y Z} {f: X -> Y} {a: list X} {b: list Z}, Datatypes.length a = Datatypes.length b -> map fst (map (fun x => (f (fst x), snd x)) (combine a b)) = map f a).
    {
      intros X Y Z f a b E.
      rewrite map_map. simpl.
      rewrite <- (map_map fst f).
      now rewrite map_fst_combine.
    }
    change
      (fun x : Addr * nat * Addr => ({| field_addr := fst (fst x); field_index := snd (fst x) |}, snd x))
      with
      (fun x : Addr * nat * Addr => ((fun y => {| field_addr := fst y; field_index := snd y |}) (fst x), snd x)).
    rewrite map_fst_map_combine.
    {
      apply Injective_map_NoDup.
      {
        intros x y E. destruct x as [x1 x2]. destruct y as [y1 y2]. now inversion E.
      }
      apply NoDup_combine_r.
      unfold get_edges, make_fields.
      remember (block_fields (vlabel g old)) as l eqn:El. clear El. remember O as m eqn:Em. clear Em.
      revert m. induction l as [|a l IHl] ; intro m ; simpl ; try constructor.
      destruct a; [destruct s|]; simpl ; try apply IHl. constructor.
      2: apply IHl. clear.
      cut (forall a b,
              In a (map field_index (filter_sum_right (make_fields' l old b))) -> b <= a)%nat.
      * repeat intro. apply H in H0. lia.
      * induction l; intros; simpl in H. 1: exfalso; assumption.
        destruct a; [destruct s|]; simpl in H; try (apply IHl in H; lia).
        destruct H; [|apply IHl in H]; lia.
    }
    {
      now rewrite combine_length, repeat_length, !map_length, Nat.min_id.
    }
  - apply list_in_map_inv in Hn. destruct Hn as [[x x_index] [En Hn]]. simpl in *. subst.
    assert (x = old). {
      unfold get_edges in Hn. rewrite <- filter_sum_right_In_iff in Hn.
      unfold make_fields in Hn. apply e_in_make_fields' in Hn. destruct Hn as [s ?].
      inversion H. reflexivity. } subst x. remember (get_edges g old). clear Heql.
    induction l; simpl in *. 1: assumption. destruct Hn.
    + subst a. simpl. left; reflexivity.
    + right. apply IHl. assumption.
Qed.


Definition copy_v_mod_rvb (rvb: Block) (new_v: Addr): Block := {|
  block_mark := true;
  block_copied_vertex := new_v;
  block_fields := block_fields rvb;
  block_color := block_color rvb;
  block_tag := block_tag rvb;
  block_tag__range := block_tag__range rvb;
  block_color__range := block_color__range rvb;
  block_fields__range := block_fields__range rvb;
  tag_no_scan := tag_no_scan rvb;
|}.

Definition update_copied_new_vlabel (g: HeapGraph) (old_v new_v: Addr) :=
  update_vlabel (vlabel g) new_v (vlabel g old_v).

Definition update_copied_old_vlabel (g: HeapGraph) (old_v new_v: Addr) :=
  update_vlabel (vlabel g) old_v (copy_v_mod_rvb (vlabel g old_v) new_v).

Definition copy_v_mod_gen_info (gi: Generation) : Generation := {|
  generation_base := generation_base gi;
  generation_block_count := generation_block_count gi + 1;
  generation_sh := generation_sh gi;
  generation_base__isptr := generation_base__isptr gi;
  generation_sh__writable := generation_sh__writable gi;
|}.

Definition copy_v_mod_gen_info_list
           (l: list Generation) (to: nat) : list Generation :=
  firstn to l ++ copy_v_mod_gen_info (nth to l null_generation) :: skipn (to + 1) l.

Lemma copy_v_mod_gen_no_nil: forall l to, copy_v_mod_gen_info_list l to <> nil.
Proof.
  repeat intro. unfold copy_v_mod_gen_info_list in H. apply app_eq_nil in H.
  destruct H. inversion H0.
Qed.

Definition copy_v_update_glabel (gi: Generations) (to: nat): Generations := {|
  generations := copy_v_mod_gen_info_list (generations gi) to;
  generations__not_nil := copy_v_mod_gen_no_nil (generations gi) to;
|}.

Definition new_copied_v (g: HeapGraph) (to: nat): Addr :=
  {| addr_gen := to; addr_block := generation_block_count (nth_gen g to) |}.

Lemma graph_has_v_not_eq: forall g to x,
    graph_has_v g x -> x <> new_copied_v g to.
Proof.
  intros. destruct H. unfold new_copied_v. destruct x as [gen idx]. simpl in *.
  destruct (Nat.eq_dec gen to).
  - subst gen. intro S; inversion S. red in H0. lia.
  - intro S; inversion S. apply n; assumption.
Qed.


Definition lgraph_add_copied_v (g: HeapGraph) (v: Addr) (to: nat): HeapGraph :=
  let new_v := new_copied_v g to in
  Build_LabeledGraph _ _ _ (pregraph_copy_v g v new_v)
                     (update_copied_new_vlabel g v new_v)
                     (elabel g) (copy_v_update_glabel (glabel g) to).

Definition lgraph_mark_copied (g: HeapGraph) (old new: Addr): HeapGraph :=
  Build_LabeledGraph _ _ _ (pg_lg g)
                     (update_copied_old_vlabel g old new) (elabel g) (glabel g).

Definition lgraph_copy_v (g: HeapGraph) (v: Addr) (to: nat): HeapGraph :=
  lgraph_mark_copied (lgraph_add_copied_v g v to) v (new_copied_v g to).

Lemma cvmgil_length: forall l to,
    (to < length l)%nat -> length (copy_v_mod_gen_info_list l to) = length l.
Proof.
  intros. unfold copy_v_mod_gen_info_list. rewrite app_length. simpl.
  rewrite firstn_length_le by lia. rewrite skipn_length. lia.
Qed.

Lemma cvmgil_not_eq: forall to n l,
    n <> to -> (to < length l)%nat ->
    nth n (copy_v_mod_gen_info_list l to) null_generation = nth n l null_generation.
Proof.
  intros. unfold copy_v_mod_gen_info_list.
  assert (length (firstn to l) = to) by (rewrite firstn_length_le; lia).
  destruct (Nat.lt_ge_cases n to).
  - rewrite app_nth1 by lia. apply nth_firstn. assumption.
  - rewrite Nat.lt_eq_cases in H2. destruct H2. 2: exfalso; intuition.
    rewrite <- (firstn_skipn (to + 1) l) at 4. rewrite app_cons_assoc, !app_nth2.
    + do 2 f_equal. rewrite app_length, H1, firstn_length_le by lia. reflexivity.
    + rewrite firstn_length_le; lia.
    + rewrite app_length, H1. simpl. lia.
Qed.

Lemma cvmgil_eq: forall to l,
    (to < length l)%nat -> nth to (copy_v_mod_gen_info_list l to) null_generation =
                     copy_v_mod_gen_info (nth to l null_generation).
Proof.
  intros. unfold copy_v_mod_gen_info_list.
  assert (length (firstn to l) = to) by (rewrite firstn_length_le; lia).
  rewrite app_nth2 by lia. rewrite H0. now replace (to - to)%nat with O by lia.
Qed.


Lemma lacv_graph_has_v_new: forall g v to,
    graph_has_gen g to -> graph_has_v (lgraph_add_copied_v g v to) (new_copied_v g to).
Proof.
  intros. split; simpl.
  - red. simpl. rewrite cvmgil_length; assumption.
  - red. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption. simpl. lia.
Qed.

Lemma lmc_graph_has_v: forall g old new x,
    graph_has_v g x <-> graph_has_v (lgraph_mark_copied g old new) x.
Proof.
  intros. unfold graph_has_v, graph_has_gen, gen_has_index, nth_gen. reflexivity.
Qed.

Lemma lcv_graph_has_gen: forall g v to x,
    graph_has_gen g to -> graph_has_gen g x <-> graph_has_gen (lgraph_copy_v g v to) x.
Proof. unfold graph_has_gen. intros. simpl. rewrite cvmgil_length; intuition. Qed.

Lemma lmc_gen_start: forall g old new n,
    gen_start (lgraph_mark_copied g old new) n = gen_start g n.
Proof.
  intros. unfold gen_start. do 2 if_tac.
  - unfold nth_gen. simpl. reflexivity.
  - unfold graph_has_gen in *. simpl in *. contradiction.
  - unfold graph_has_gen in *. simpl in *. contradiction.
  - reflexivity.
Qed.

Lemma lacv_nth_gen: forall g v to n,
    n <> to -> graph_has_gen g to ->
    nth_gen (lgraph_add_copied_v g v to) n = nth_gen g n.
Proof.
  intros. unfold lgraph_add_copied_v, nth_gen. simpl. remember (generations (glabel g)).
  apply cvmgil_not_eq; [|subst l]; assumption.
Qed.

Lemma lacv_graph_has_gen: forall g v to n,
    graph_has_gen g to ->
    graph_has_gen (lgraph_add_copied_v g v to) n <-> graph_has_gen g n.
Proof.
  intros. unfold graph_has_gen. simpl.
  rewrite cvmgil_length by assumption. reflexivity.
Qed.

Lemma lacv_gen_start: forall g v to n,
    graph_has_gen g to -> gen_start (lgraph_add_copied_v g v to) n = gen_start g n.
Proof.
  intros. unfold gen_start. do 2 if_tac.
  - destruct (Nat.eq_dec n to).
    + subst n. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption.
      simpl. reflexivity.
    + rewrite lacv_nth_gen by assumption. reflexivity.
  - rewrite lacv_graph_has_gen in H0 by assumption. contradiction.
  - exfalso. apply H0. rewrite lacv_graph_has_gen; assumption.
  - reflexivity.
Qed.

Lemma lacv_vlabel_old: forall (g : HeapGraph) (v : Addr) (to: nat) x,
    x <> new_copied_v g to -> vlabel (lgraph_add_copied_v g v to) x = vlabel g x.
Proof.
  intros. simpl.
  unfold update_copied_new_vlabel, graph_gen.update_vlabel.
  rewrite if_false. 1: reflexivity. unfold Equivalence.equiv; intro S; apply H.
  inversion S; reflexivity.
Qed.


Lemma lcv_gen_start: forall g v to n,
    graph_has_gen g to -> gen_start (lgraph_copy_v g v to) n = gen_start g n.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_gen_start, lacv_gen_start; [reflexivity | assumption].
Qed.


Lemma lcv_nth_gen: forall g v to n,
    n <> to -> graph_has_gen g to -> nth_gen (lgraph_copy_v g v to) n = nth_gen g n.
Proof.
  intros. unfold lgraph_copy_v, nth_gen. simpl.
  rewrite cvmgil_not_eq; [reflexivity | assumption..].
Qed.


Lemma lacv_make_fields_not_eq: forall (g : HeapGraph) (v : Addr) (to : nat) x,
    x <> new_copied_v g to ->
    make_fields (lgraph_add_copied_v g v to) x = make_fields g x.
Proof.
  intros. unfold make_fields. simpl. unfold update_copied_new_vlabel, update_vlabel.
  rewrite if_false. 1: reflexivity. intuition.
Qed.

Lemma lacv_vertex_address: forall (g : HeapGraph) (v : Addr) (to: nat) x,
    closure_has_v g x -> graph_has_gen g to ->
    vertex_address (lgraph_add_copied_v g v to) x = vertex_address g x.
Proof.
  intros. destruct x as [n m]. destruct H. simpl in *. unfold vertex_address. f_equal.
  - f_equal. unfold vertex_offset. f_equal. unfold previous_vertices_size.
    simpl. apply fold_left_ext. intros. unfold vertex_size_accum. f_equal.
    unfold vertex_size. f_equal. rewrite lacv_vlabel_old. 1: reflexivity.
    intro. unfold new_copied_v in H3. inversion H3.
    rewrite nat_inc_list_In_iff in H2. subst n. red in H1. lia.
  - simpl. apply lacv_gen_start. assumption.
Qed.


Lemma lacv_vertex_address_old: forall (g : HeapGraph) (v : Addr) (to: nat) x,
    graph_has_v g x -> graph_has_gen g to ->
    vertex_address (lgraph_add_copied_v g v to) x = vertex_address g x.
Proof.
  intros. apply lacv_vertex_address; [apply graph_has_v_in_closure |]; assumption.
Qed.

Lemma lacv_vertex_address_new: forall (g : HeapGraph) (v : Addr) (to: nat),
    graph_has_gen g to ->
    vertex_address (lgraph_add_copied_v g v to) (new_copied_v g to) =
    vertex_address g (new_copied_v g to).
Proof.
  intros. unfold new_copied_v. apply lacv_vertex_address. 2: assumption.
  red. simpl.  split; [assumption | apply Nat.le_refl].
Qed.

Lemma lacv_make_header_old: forall (g : HeapGraph) (v : Addr) (to : nat) x,
    x <> new_copied_v g to ->
    make_header (lgraph_add_copied_v g v to) x = make_header g x.
Proof.
  intros. unfold make_header. rewrite lacv_vlabel_old by assumption. reflexivity.
Qed.

Lemma lacv_field2val_make_fields_old:  forall (g : HeapGraph) (v : Addr) (to : nat) x,
    graph_has_v g x -> graph_has_gen g to -> no_dangling_dst g ->
    map (field2val (lgraph_add_copied_v g v to))
        (make_fields (lgraph_add_copied_v g v to) x) =
    map (field2val g) (make_fields g x).
Proof.
  intros. unfold make_fields. pose proof (graph_has_v_not_eq _ to _ H).
  rewrite lacv_vlabel_old by assumption. apply map_ext_in.
  intros [[? | ?] | ?] ?; simpl; try reflexivity. unfold new_copied_v.
  rewrite pcv_dst_old.
  - apply lacv_vertex_address_old. 2: assumption. specialize (H1 _ H). apply H1.
    unfold get_edges. rewrite <- filter_sum_right_In_iff. assumption.
  - apply e_in_make_fields' in H3. destruct H3 as [s ?]. subst. simpl. intro.
    unfold new_copied_v in H2. contradiction.
Qed.

Lemma lacv_make_fields_vals_old: forall (g : HeapGraph) (v : Addr) (to: nat) x,
    graph_has_v g x -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    make_fields_vals (lgraph_add_copied_v g v to) x = make_fields_vals g x.
Proof.
  intros. pose proof (lacv_field2val_make_fields_old _ v _ _ H H0 H1).
  unfold make_fields_vals. pose proof (graph_has_v_not_eq g to x H).
  rewrite lacv_vlabel_old by assumption. rewrite H3.
  destruct (block_mark (vlabel g x)) eqn:? ; [f_equal | reflexivity].
  apply lacv_vertex_address_old; [apply H2|]; assumption.
Qed.

Lemma lacv_nth_sh: forall (g : HeapGraph) (v : Addr) (to : nat) n,
    graph_has_gen g to -> nth_sh (lgraph_add_copied_v g v to) n = nth_sh g n.
Proof.
  intros. unfold nth_sh, nth_gen. simpl. destruct (Nat.eq_dec n to).
  - subst n. rewrite cvmgil_eq by assumption. simpl. reflexivity.
  - rewrite cvmgil_not_eq by assumption. reflexivity.
Qed.

Lemma lacv_vlabel_new: forall g v to,
    vlabel (lgraph_add_copied_v g v to) (new_copied_v g to) = vlabel g v.
Proof.
  intros. simpl. unfold update_copied_new_vlabel, graph_gen.update_vlabel.
  rewrite if_true; reflexivity.
Qed.

Lemma lacv_make_header_new: forall g v to,
    make_header (lgraph_add_copied_v g v to) (new_copied_v g to) = make_header g v.
Proof. intros. unfold make_header. rewrite lacv_vlabel_new. reflexivity. Qed.

Lemma lacv_field2val_make_fields_new: forall g v to,
    graph_has_v g v -> graph_has_gen g to -> no_dangling_dst g ->
    map (field2val (lgraph_add_copied_v g v to))
        (make_fields (lgraph_add_copied_v g v to) (new_copied_v g to)) =
    map (field2val g) (make_fields g v).
Proof.
  intros. unfold make_fields. rewrite lacv_vlabel_new.
  remember (block_fields (vlabel g v)). remember O as n.
  assert (forall m, In m (map field_index (filter_sum_right (make_fields' l v n))) ->
                    In m (map field_index (get_edges g v))). {
    unfold get_edges, make_fields. subst. intuition. }
  clear Heql Heqn. revert n H2. induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|].
  - simpl in *. rewrite IHl; [reflexivity | assumption].
  - simpl in *. rewrite IHl; [reflexivity | assumption].
  - simpl in *. rewrite IHl.
    + assert (In n (map field_index (get_edges g v))) by (apply H2; left; reflexivity).
      f_equal. rewrite pcv_dst_new by assumption. apply lacv_vertex_address_old.
      2: assumption. red in H1. apply (H1 v). 1: assumption. apply in_map_iff in H3.
      destruct H3 as [[x ?] [? ?]]. simpl in H3. subst. clear -H4. pose proof H4.
      unfold get_edges in H4. rewrite <- filter_sum_right_In_iff in H4.
      unfold make_fields in H4. apply e_in_make_fields' in H4. destruct H4 as [s ?].
      inversion H0. subst. assumption.
    + intros. apply H2. right; assumption.
Qed.

Lemma lacv_make_fields_vals_new: forall g v to,
    graph_has_v g v -> graph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    make_fields_vals (lgraph_add_copied_v g v to) (new_copied_v g to) =
    make_fields_vals g v.
Proof.
  intros. unfold make_fields_vals. rewrite lacv_vlabel_new.
  rewrite (lacv_field2val_make_fields_new _ _ _ H H0 H1).
  destruct (block_mark (vlabel g v)) eqn:? . 2: reflexivity. f_equal.
  apply lacv_vertex_address_old. 2: assumption. apply H2; assumption.
Qed.

Lemma lacv_graph_has_v_old: forall g v to x,
    graph_has_gen g to -> graph_has_v g x ->
    graph_has_v (lgraph_add_copied_v g v to) x.
Proof.
  intros. destruct H0. split.
  - rewrite lacv_graph_has_gen; assumption.
  - red. destruct (Nat.eq_dec (addr_gen x) to).
    + rewrite e in *. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption.
      simpl. red in H1. unfold nth_gen in H1. lia.
    + rewrite lacv_nth_gen; assumption.
Qed.


Lemma lcv_graph_has_v_new: forall g v to,
    graph_has_gen g to -> graph_has_v (lgraph_copy_v g v to) (new_copied_v g to).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_graph_has_v.
  apply lacv_graph_has_v_new. assumption.
Qed.

Lemma lcv_graph_has_v_old: forall g v to x,
    graph_has_gen g to -> graph_has_v g x -> graph_has_v (lgraph_copy_v g v to) x.
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_graph_has_v.
  apply lacv_graph_has_v_old; assumption.
Qed.

Lemma lcv_vertex_size_new: forall (g : HeapGraph) (v : Addr) (to : nat),
    vertex_size (lgraph_copy_v g v to) (new_copied_v g to) = vertex_size g v.
Proof.
  intros. unfold vertex_size, lgraph_copy_v. simpl.
  unfold update_copied_old_vlabel, update_vlabel. if_tac.
  - simpl. unfold update_copied_new_vlabel, update_vlabel. if_tac; reflexivity.
  - rewrite lacv_vlabel_new. reflexivity.
Qed.

Lemma lcv_vertex_size_old: forall (g : HeapGraph) (v : Addr) (to : nat) x,
        graph_has_gen g to -> graph_has_v g x ->
        vertex_size (lgraph_copy_v g v to) x = vertex_size g x.
Proof.
  intros. unfold vertex_size, lgraph_copy_v. simpl.
  unfold update_copied_old_vlabel, update_vlabel. if_tac.
  - simpl. unfold update_copied_new_vlabel, update_vlabel. unfold equiv in H1. subst.
    if_tac; reflexivity.
  - rewrite lacv_vlabel_old. 1: reflexivity. apply graph_has_v_not_eq. assumption.
Qed.

Lemma lcv_pvs_same: forall g v to,
    graph_has_gen g to ->
    previous_vertices_size (lgraph_copy_v g v to) to
                           (generation_block_count (nth_gen (lgraph_copy_v g v to) to)) =
    previous_vertices_size g to (generation_block_count (nth_gen g to)) + vertex_size g v.
Proof.
  intros. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption. simpl.
  remember (generation_block_count (nth to (generations (glabel g)) null_generation)).
  replace (n + 1)%nat with (S n) by lia. rewrite previous_vertices_size__S. f_equal.
  - unfold previous_vertices_size. apply fold_left_ext. intros.
    unfold vertex_size_accum. f_equal. apply lcv_vertex_size_old. 1: assumption.
    rewrite nat_inc_list_In_iff in H0; subst; split; simpl; assumption.
  - assert ({| addr_gen := to; addr_block := n |} = new_copied_v g to) by
        (unfold new_copied_v, nth_gen; subst n; reflexivity). rewrite H0.
    apply lcv_vertex_size_new.
Qed.

Lemma lcv_pvs_old: forall g v to gen,
    gen <> to -> graph_has_gen g to -> graph_has_gen g gen ->
    previous_vertices_size (lgraph_copy_v g v to) gen
                           (generation_block_count (nth_gen (lgraph_copy_v g v to) gen)) =
    previous_vertices_size g gen (generation_block_count (nth_gen g gen)).
Proof.
  intros. unfold nth_gen. simpl. rewrite cvmgil_not_eq by assumption.
  remember (generation_block_count (nth gen (generations (glabel g)) null_generation)).
  unfold previous_vertices_size. apply fold_left_ext. intros.
  unfold vertex_size_accum. f_equal. apply lcv_vertex_size_old. 1: assumption.
  rewrite nat_inc_list_In_iff in H2. subst. split; simpl; assumption.
Qed.

Lemma lmc_vertex_address: forall g v new_v x,
    vertex_address (lgraph_mark_copied g v new_v) x = vertex_address g x.
Proof.
  intros. unfold vertex_address. f_equal.
  f_equal. unfold vertex_offset. f_equal. unfold previous_vertices_size.
  apply fold_left_ext. intros. unfold vertex_size_accum. f_equal. unfold vertex_size.
  f_equal. simpl. unfold update_copied_old_vlabel, graph_gen.update_vlabel.
  destruct (EquivDec.equiv_dec v {| addr_gen := addr_gen x; addr_block := y |}).
  - unfold Equivalence.equiv in e. rewrite <- e. simpl. reflexivity.
  - reflexivity.
Qed.

Lemma lmc_make_fields: forall (g : HeapGraph) (old new v: Addr),
    make_fields (lgraph_mark_copied g old new) v = make_fields g v.
Proof.
  intros. unfold make_fields. simpl. unfold update_copied_old_vlabel, update_vlabel.
  if_tac; [unfold equiv in H; subst v |]; reflexivity.
Qed.

Lemma lmc_field2val_make_fields: forall (g : HeapGraph) (v new_v x: Addr),
    map (field2val (lgraph_mark_copied g v new_v))
        (make_fields (lgraph_mark_copied g v new_v) x) =
    map (field2val g) (make_fields g x).
Proof.
  intros. rewrite lmc_make_fields. apply map_ext; intros.
  destruct a; [destruct s|]; simpl; [| |rewrite lmc_vertex_address]; reflexivity.
Qed.

Lemma lmc_vlabel_not_eq: forall g v new_v x,
    x <> v -> vlabel (lgraph_mark_copied g v new_v) x = vlabel g x.
Proof.
  intros. unfold lgraph_mark_copied, update_copied_old_vlabel, update_vlabel. simpl.
  rewrite if_false. 1: reflexivity. unfold equiv. intuition.
Qed.

Lemma lmc_make_fields_vals_not_eq: forall (g : HeapGraph) (v new_v : Addr) x,
    x <> v -> make_fields_vals (lgraph_mark_copied g v new_v) x = make_fields_vals g x.
Proof.
  intros. unfold make_fields_vals.
  rewrite lmc_field2val_make_fields, lmc_vlabel_not_eq, lmc_vertex_address;
    [reflexivity | assumption].
Qed.

Lemma lmc_make_fields_vals_eq: forall (g : HeapGraph) (v new_v : Addr),
    make_fields_vals (lgraph_mark_copied g v new_v) v =
    vertex_address g new_v :: tl (make_fields_vals g v).
Proof.
  intros. unfold make_fields_vals at 1. simpl.
  unfold update_copied_old_vlabel, graph_gen.update_vlabel.
  rewrite if_true by reflexivity. simpl. rewrite lmc_vertex_address.
  assert (tl (make_fields_vals g v) = tl (map (field2val g) (make_fields g v))) by
      (unfold make_fields_vals; destruct (block_mark (vlabel g v)); simpl; reflexivity).
  rewrite H. clear H. do 2 f_equal. apply lmc_field2val_make_fields.
Qed.


Lemma lmc_copy_compatible: forall g old new,
    graph_has_v g new -> addr_gen old <> addr_gen new -> copy_compatible g ->
    copy_compatible (lgraph_mark_copied g old new).
Proof.
  repeat intro. destruct (Addr_EqDec old v).
  - compute in e. subst old. rewrite <- lmc_graph_has_v. simpl.
    unfold update_copied_old_vlabel, update_vlabel. rewrite if_true by reflexivity.
    simpl. split; assumption.
  - assert (v <> old) by intuition. clear c.
    rewrite lmc_vlabel_not_eq, <- lmc_graph_has_v in * by assumption.
    apply H1; assumption.
Qed.

Lemma lacv_graph_has_v_inv: forall (g : HeapGraph) (v : Addr) (to : nat) (x : Addr),
    graph_has_gen g to -> graph_has_v (lgraph_add_copied_v g v to) x ->
    graph_has_v g x \/ x = new_copied_v g to.
Proof.
  intros. destruct (Addr_EqDec x (new_copied_v g to)).
  - unfold equiv in e; right; assumption.
  - left. destruct H0. split.
    + rewrite lacv_graph_has_gen in H0; assumption.
    + assert (x <> (new_copied_v g to)) by intuition. clear c H0.
      unfold gen_has_index in *. unfold nth_gen, lgraph_add_copied_v in H1.
      simpl in H1. destruct x as [gen index]. simpl in *. unfold new_copied_v in H2.
      destruct (Nat.eq_dec gen to).
      * subst gen. rewrite cvmgil_eq in H1 by assumption. simpl in H1.
        change (nth to (generations (glabel g)) null_generation) with (nth_gen g to) in H1.
        remember (generation_block_count (nth_gen g to)).
        assert (index <> n) by (intro; apply H2; f_equal; assumption). lia.
      * rewrite cvmgil_not_eq in H1; assumption.
Qed.

Lemma lacv_copy_compatible: forall (g : HeapGraph) (v : Addr) (to : nat),
    block_mark (vlabel g v) = false -> graph_has_gen g to ->
    copy_compatible g -> copy_compatible (lgraph_add_copied_v g v to).
Proof.
  repeat intro. destruct (Addr_EqDec v0 (new_copied_v g to)).
  - unfold equiv in e. subst v0. rewrite lacv_vlabel_new in *.
    rewrite H3 in H. inversion H.
  - assert (v0 <> (new_copied_v g to)) by intuition. clear c.
    rewrite lacv_vlabel_old in * by assumption.
    assert (graph_has_v g v0). {
      apply lacv_graph_has_v_inv in H2. 2: assumption. destruct H2. 1: assumption.
      contradiction. } split.
    + apply lacv_graph_has_v_old; [|apply H1]; assumption.
    + apply H1; assumption.
Qed.

Lemma lcv_copy_compatible: forall g v to,
    block_mark (vlabel g v) = false -> graph_has_gen g to ->
    addr_gen v <> to -> copy_compatible g -> copy_compatible (lgraph_copy_v g v to).
Proof.
  intros. unfold lgraph_copy_v. apply lmc_copy_compatible. 2: simpl; assumption.
  - apply lacv_graph_has_v_new. assumption.
  - apply lacv_copy_compatible; assumption.
Qed.

Lemma lmc_no_dangling_dst: forall g old new,
    no_dangling_dst g -> no_dangling_dst (lgraph_mark_copied g old new).
Proof.
  repeat intro. simpl. rewrite <- lmc_graph_has_v in *.
  unfold get_edges in H1. rewrite lmc_make_fields in H1. apply (H v); assumption.
Qed.

Lemma lacv_get_edges_new: forall g v to,
  map field_index (get_edges (lgraph_add_copied_v g v to) (new_copied_v g to)) =
  map field_index (get_edges g v).
Proof.
  intros. unfold get_edges, make_fields. rewrite lacv_vlabel_new.
  remember (block_fields (vlabel g v)). remember O. clear Heql Heqn. revert n.
  induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|]; simpl; rewrite IHl; reflexivity.
Qed.

Lemma lacv_no_dangling_dst: forall (g : HeapGraph) (v : Addr) (to : nat),
    no_dangling_dst g -> graph_has_gen g to -> graph_has_v g v ->
    no_dangling_dst (lgraph_add_copied_v g v to).
Proof.
  intros; intro x; intros. simpl. destruct (Addr_EqDec x (new_copied_v g to)).
  - unfold equiv in e0. subst x. pose proof H3. remember (new_copied_v g to) as new.
    apply get_edges_fst in H3. destruct e as [? s]. simpl in H3. subst.
    rewrite get_edges_In, lacv_get_edges_new in H4. rewrite pcv_dst_new.
    2: assumption. apply lacv_graph_has_v_old. 1: assumption.
    apply (H v); [|rewrite get_edges_In]; assumption.
  - assert (x <> new_copied_v g to) by intuition. clear c. rewrite pcv_dst_old.
    + apply lacv_graph_has_v_old. 1: assumption. apply lacv_graph_has_v_inv in H2.
      2: assumption. destruct H2. 2: contradiction. apply (H x). 1: assumption.
      unfold get_edges in *. rewrite lacv_make_fields_not_eq in H3; assumption.
    + unfold get_edges in H3. rewrite <- filter_sum_right_In_iff in H3.
      apply e_in_make_fields' in H3. destruct H3 as [s ?]. subst e. simpl. assumption.
Qed.

Lemma lcv_no_dangling_dst: forall g v to,
    no_dangling_dst g -> graph_has_gen g to -> graph_has_v g v ->
    no_dangling_dst (lgraph_copy_v g v to).
Proof.
  intros. unfold lgraph_copy_v.
  apply lmc_no_dangling_dst, lacv_no_dangling_dst; assumption.
Qed.

Lemma lmc_outlier_compatible: forall g outlier old new,
    outlier_compatible g outlier ->
    outlier_compatible (lgraph_mark_copied g old new) outlier.
Proof.
  intros. intro v. intros. rewrite <- lmc_graph_has_v in H0.
  unfold lgraph_mark_copied, update_copied_old_vlabel, update_vlabel; simpl.
  if_tac; simpl; apply H; [unfold equiv in H1; subst|]; assumption.
Qed.

Lemma lacv_outlier_compatible: forall (g : HeapGraph) outlier (v : Addr) (to : nat),
    graph_has_gen g to -> graph_has_v g v -> outlier_compatible g outlier ->
    outlier_compatible (lgraph_add_copied_v g v to) outlier.
Proof.
  intros. intros x ?. apply lacv_graph_has_v_inv in H2. 2: assumption. destruct H2.
  - rewrite lacv_vlabel_old; [apply H1 | apply graph_has_v_not_eq]; assumption.
  - subst x. rewrite lacv_vlabel_new. apply H1; assumption.
Qed.

Lemma lcv_outlier_compatible: forall g outlier v to,
    graph_has_gen g to -> graph_has_v g v -> outlier_compatible g outlier ->
    outlier_compatible (lgraph_copy_v g v to) outlier.
Proof. intros. apply lmc_outlier_compatible, lacv_outlier_compatible; assumption. Qed.

Lemma lacv_unmarked_gen_size: forall g v to from,
    from <> to -> graph_has_gen g to ->
    unmarked_gen_size g from = unmarked_gen_size (lgraph_add_copied_v g v to) from.
Proof.
  intros. unfold unmarked_gen_size. rewrite lacv_nth_gen by assumption.
  remember (nat_inc_list (generation_block_count (nth_gen g from))) as l.
  assert (forall i, {| addr_gen := from; addr_block := i |} <> new_copied_v g to). {
    intros. intro. inversion H1. apply H. assumption. }
  assert (filter (fun i : nat => negb (block_mark (vlabel g {| addr_gen := from; addr_block := i |}))) l =
          filter (fun i : nat =>
                    negb(block_mark(vlabel(lgraph_add_copied_v g v to) {| addr_gen := from; addr_block := i |}))) l). {
    apply filter_ext. intros. rewrite lacv_vlabel_old by apply H1. reflexivity. }
  rewrite <- H2. apply fold_left_ext. intros. unfold vertex_size_accum. f_equal.
  unfold vertex_size. rewrite lacv_vlabel_old by apply H1. reflexivity.
Qed.

Lemma lacv_estc: forall g t_info from to v,
    from <> to -> graph_has_gen g to ->
    enough_space_to_copy g t_info from to ->
    enough_space_to_copy (lgraph_add_copied_v g v to) t_info from to.
Proof.
  unfold enough_space_to_copy. intros. rewrite <- lacv_unmarked_gen_size; assumption.
Qed.

Lemma lmc_unmarked_gen_size: forall g v v',
    graph_has_v g v -> block_mark (vlabel g v) = false ->
    unmarked_gen_size g (addr_gen v) =
    unmarked_gen_size (lgraph_mark_copied g v v') (addr_gen v) +
     vertex_size g v.
Proof.
  intros. unfold unmarked_gen_size. unfold nth_gen. simpl glabel.
  destruct v as [gen index]. simpl addr_gen.
  change (nth gen (generations (glabel g)) null_generation) with (nth_gen g gen).
  remember (nat_inc_list (generation_block_count (nth_gen g gen))).
  rewrite (fold_left_ext (vertex_size_accum (lgraph_mark_copied g {| addr_gen := gen; addr_block := index |} v') gen)
                         (vertex_size_accum g gen)).
  - simpl. remember (fun i : nat => negb (block_mark (vlabel g {| addr_gen := gen; addr_block := i |}))) as f1.
    remember (fun i : nat =>
                negb (block_mark (update_copied_old_vlabel g {| addr_gen := gen; addr_block := index |} v' {| addr_gen := gen; addr_block := i |})))
      as f2. cut (Permutation (filter f1 l) (index :: filter f2 l)).
    + intros. rewrite (fold_left_comm _ _ (index :: filter f2 l)). 3: assumption.
      * simpl. rewrite <- vsa_fold_left. f_equal.
      * apply vertex_size_accum__comm.
    + apply filter_singular_perm; subst.
      * intros. unfold update_copied_old_vlabel, update_vlabel.
        rewrite if_false. 1: reflexivity. unfold equiv. intro. apply H2.
        inversion H3. reflexivity.
      * rewrite nat_inc_list_In_iff. destruct H. simpl in *. assumption.
      * unfold update_copied_old_vlabel, update_vlabel. rewrite if_true; reflexivity.
      * rewrite H0. reflexivity.
      * apply nat_inc_list_NoDup.
  - intros. unfold vertex_size_accum. f_equal. unfold vertex_size. f_equal.
    simpl. unfold update_copied_old_vlabel, update_vlabel. if_tac. 2: reflexivity.
    simpl. unfold equiv in H2. rewrite H2. reflexivity.
Qed.

Lemma lmc_estc:
  forall (g : HeapGraph) (t_info : thread_info) (v v': Addr) (to : nat)
         (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info))),
    enough_space_to_copy g t_info (addr_gen v) to ->
    graph_has_v g v -> block_mark (vlabel g v) = false ->
    forall
      Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (vertex_size g v),
      enough_space_to_copy (lgraph_mark_copied g v v')
                           (cut_thread_info
                              t_info (Z.of_nat to) (vertex_size g v) Hi Hh)
                           (addr_gen v) to.
Proof.
  unfold enough_space_to_copy. intros.
  rewrite (lmc_unmarked_gen_size g v v') in H by assumption.
  rewrite (cti_rest_gen_size _ _ (vertex_size g v) Hi Hh) in H. lia.
Qed.

Lemma forward_estc_unchanged: forall
    g t_info v to
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (vertex_size g v)),
    addr_gen v <> to -> graph_has_gen g to ->
    graph_has_v g v -> block_mark (vlabel g v) = false ->
    enough_space_to_copy g t_info (addr_gen v) to ->
    enough_space_to_copy (lgraph_copy_v g v to)
         (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh)
      (addr_gen v) to.
Proof.
  intros. unfold lgraph_copy_v.
  apply (lacv_estc _ _ _ _ v) in H3; [| assumption..].
  assert (vertex_size g v = vertex_size (lgraph_add_copied_v g v to) v). {
    unfold vertex_size. rewrite lacv_vlabel_old. 1: reflexivity.
    intro. destruct v as [gen index]. simpl in H. unfold new_copied_v in H4.
    inversion H4. apply H. assumption. }
  remember (lgraph_add_copied_v g v to) as g'.
  pose proof Hh as Hh'. rewrite H4 in Hh'.
  replace (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh) with
      (cut_thread_info t_info (Z.of_nat to) (vertex_size g' v) Hi Hh') by
      (apply cti_eq; symmetry; assumption).
  apply lmc_estc.
  - assumption.
  - subst g'. apply lacv_graph_has_v_old; assumption.
  - subst g'. rewrite lacv_vlabel_old; [| apply graph_has_v_not_eq]; assumption.
Qed.

Lemma lcv_rgc_unchanged: forall g roots v to,
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    roots_graph_compatible roots (lgraph_copy_v g v to).
Proof.
  intros. red in H0 |-*. rewrite Forall_forall in *. intros.
  apply lcv_graph_has_v_old; [|apply H0]; assumption.
Qed.

Lemma lcv_roots_compatible_unchanged: forall g roots outlier v to,
    graph_has_gen g to ->
    roots_compatible g outlier roots ->
    roots_compatible (lgraph_copy_v g v to) outlier roots.
Proof. intros. destruct H0. split; [|apply lcv_rgc_unchanged]; assumption. Qed.

Lemma lcv_vertex_address: forall g v to x,
    graph_has_gen g to -> closure_has_v g x ->
    vertex_address (lgraph_copy_v g v to) x = vertex_address g x.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_vertex_address, lacv_vertex_address; [reflexivity | assumption..].
Qed.

Lemma lcv_vertex_address_new: forall g v to,
    graph_has_gen g to ->
    vertex_address (lgraph_copy_v g v to) (new_copied_v g to) =
    vertex_address g (new_copied_v g to).
Proof.
  intros.
  apply lcv_vertex_address;  [| red; simpl; split]; [assumption..| apply Nat.le_refl].
Qed.

Lemma lcv_vertex_address_old: forall g v to x,
    graph_has_gen g to -> graph_has_v g x ->
    vertex_address (lgraph_copy_v g v to) x = vertex_address g x.
Proof.
  intros. apply lcv_vertex_address; [|apply graph_has_v_in_closure]; assumption.
Qed.

Lemma lcv_fun_thread_arg_compatible_unchanged: forall
    g t_info f_info roots v to i s
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s),
    graph_has_gen g to ->
    roots_graph_compatible roots g ->
    fun_thread_arg_compatible g t_info f_info roots ->
    fun_thread_arg_compatible (lgraph_copy_v g v to)
         (cut_thread_info t_info i s Hi Hh) f_info roots.
Proof.
  intros.
  unfold fun_thread_arg_compatible in *. simpl. rewrite <- H1. apply map_ext_in.
  intros. destruct a; [destruct s0|]; [reflexivity..| simpl].
  apply lcv_vertex_address_old. 1: assumption. red in H0. rewrite Forall_forall in H0.
  apply H0. rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Lemma lcv_graph_thread_info_compatible: forall
    g t_info v to
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (vertex_size g v)),
    graph_has_gen g to ->
    graph_thread_info_compatible g t_info ->
    graph_thread_info_compatible (lgraph_copy_v g v to)
      (cut_thread_info t_info (Z.of_nat to) (vertex_size g v)
                       Hi Hh).
Proof.
  unfold graph_thread_info_compatible. intros. destruct H0 as [? [? ?]].
  assert (map space_base (heap_spaces (ti_heap t_info)) =
          map space_base
              (upd_Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))
                        (cut_space
                           (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info)))
                           (vertex_size g v) Hh))). {
    rewrite <- upd_Znth_map. simpl. rewrite <- Znth_map by assumption.
    rewrite upd_Znth_unchanged; [reflexivity | rewrite Zlength_map; assumption]. }
  split; [|split]; [|simpl; rewrite cvmgil_length by assumption..].
  - rewrite gsc_iff in *; simpl. 2: assumption.
    + intros. unfold nth_space. simpl.
      rewrite <- lcv_graph_has_gen in H4 by assumption. specialize (H0 _ H4).
      simpl in H0. destruct H0 as [? [? ?]]. split; [|split].
      * clear -H0 H3 H. rewrite <- map_nth, <- H3, map_nth. clear H3.
        unfold nth_gen, nth_space in *. simpl. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite cvmgil_eq; simpl; assumption.
        -- rewrite cvmgil_not_eq; assumption.
      * assert (map space_sh
                    (upd_Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))
                              (cut_space
                                 (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info)))
                                 (vertex_size g v) Hh)) =
                map space_sh (heap_spaces (ti_heap t_info))). {
          rewrite <- upd_Znth_map. simpl. rewrite <- Znth_map by assumption.
          rewrite upd_Znth_unchanged; [reflexivity|rewrite Zlength_map; assumption]. }
        rewrite <- map_nth, H7, map_nth. clear -H5 H. unfold nth_gen, nth_space in *.
        simpl. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite cvmgil_eq; simpl; assumption.
        -- rewrite cvmgil_not_eq; assumption.
      * assert (0 <= Z.of_nat gen < Zlength (heap_spaces (ti_heap t_info))). {
          split. 1: apply Nat2Z.is_nonneg. rewrite Zlength_correct.
          apply inj_lt. red in H4. lia. }
        rewrite <- (Nat2Z.id gen) at 3. rewrite nth_Znth.
        2: rewrite upd_Znth_Zlength; assumption. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite upd_Znth_same by assumption. simpl.
           rewrite lcv_pvs_same by assumption.
           rewrite H6, nth_space_Znth. reflexivity.
        -- assert (Z.of_nat gen <> Z.of_nat to) by
              (intro; apply n, Nat2Z.inj; assumption).
           rewrite upd_Znth_diff, <- nth_space_Znth, lcv_pvs_old; assumption.
    + rewrite cvmgil_length, <- !ZtoNat_Zlength, upd_Znth_Zlength, !ZtoNat_Zlength;
        assumption.
  - intros. rewrite <- H3. assumption.
  - rewrite <- !ZtoNat_Zlength, upd_Znth_Zlength, !ZtoNat_Zlength; assumption.
Qed.

Lemma lcv_super_compatible_unchanged: forall
    g t_info roots f_info outlier to v
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (vertex_size g v)),
    graph_has_gen g to -> graph_has_v g v ->
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible
      (lgraph_copy_v g v to,
       (cut_thread_info t_info (Z.of_nat to) (vertex_size g v) Hi Hh),
       roots) f_info outlier.
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lcv_graph_thread_info_compatible; assumption.
  - destruct H3. apply lcv_fun_thread_arg_compatible_unchanged; assumption.
  - apply lcv_roots_compatible_unchanged; assumption.
  - apply lcv_outlier_compatible; assumption.
Qed.

Lemma lcv_closure_has_v: forall g v to x,
    graph_has_gen g to -> closure_has_v g x -> closure_has_v (lgraph_copy_v g v to) x.
Proof.
  intros. unfold closure_has_v in *. destruct x as [gen index]. simpl in *.
  destruct H0. split. 1: rewrite <- lcv_graph_has_gen; assumption.
  destruct (Nat.eq_dec gen to).
  - subst gen. red. unfold nth_gen. simpl. rewrite cvmgil_eq by assumption.
    simpl. red in H1. unfold nth_gen in H1. lia.
  - red. rewrite lcv_nth_gen; assumption.
Qed.


Lemma lmc_block_fields: forall g old new x,
    block_fields (vlabel g x) = block_fields (vlabel (lgraph_mark_copied g old new) x).
Proof.
  intros. destruct (Addr_EqDec old x).
  - unfold equiv in e. subst. simpl. unfold update_copied_old_vlabel, update_vlabel.
    rewrite if_true by reflexivity. simpl. reflexivity.
  - assert (x <> old) by intuition.
    rewrite lmc_vlabel_not_eq; [reflexivity | assumption].
Qed.

Lemma lcv_block_fields: forall g v to x,
    graph_has_gen g to -> graph_has_v g x ->
    block_fields (vlabel g x) = block_fields (vlabel (lgraph_copy_v g v to) x).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_block_fields, lacv_vlabel_old.
  1: reflexivity. apply graph_has_v_not_eq; assumption.
Qed.

Lemma lcv_mfv_Zlen_eq: forall g v v' to,
    graph_has_gen g to ->
    graph_has_v g v ->
    Zlength (make_fields_vals g v) =
    Zlength (make_fields_vals (lgraph_copy_v g v' to) v).
Proof.
  intros. repeat rewrite fields_eq_length.
  rewrite <- lcv_block_fields by assumption; reflexivity.
Qed.


Lemma lmc_block_mark: forall g old new x,
    x <> old -> block_mark (vlabel g x) =
                block_mark (vlabel (lgraph_mark_copied g old new) x).
Proof.
  intros. destruct (Addr_EqDec x old).
  - unfold equiv in e. contradiction.
  - rewrite lmc_vlabel_not_eq; [reflexivity | assumption].
Qed.

Lemma lcv_block_mark: forall g v to x,
    x <> v -> graph_has_gen g to -> graph_has_v g x ->
    block_mark (vlabel g x) = block_mark (vlabel (lgraph_copy_v g v to) x).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_block_mark by assumption.
  rewrite lacv_vlabel_old. 1: reflexivity. apply graph_has_v_not_eq; assumption.
Qed.


Lemma lcv_vlabel_new: forall g v to,
    addr_gen v <> to ->
    vlabel (lgraph_copy_v g v to) (new_copied_v g to) = vlabel g v.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_vlabel_not_eq, lacv_vlabel_new;
    [| unfold new_copied_v; intro; apply H; inversion H0; simpl]; reflexivity.
Qed.


Lemma lcv_graph_has_v_inv: forall (g : HeapGraph) (v : Addr) (to : nat) (x : Addr),
    graph_has_gen g to -> graph_has_v (lgraph_copy_v g v to) x ->
    graph_has_v g x \/ x = new_copied_v g to.
Proof.
  intros. unfold lgraph_copy_v in H0. rewrite <- lmc_graph_has_v in H0.
  apply (lacv_graph_has_v_inv g v); assumption.
Qed.

Lemma lcv_gen_unmarked: forall (to : nat) (g : HeapGraph) (v : Addr),
    graph_has_gen g to -> block_mark (vlabel g v) = false ->
    forall gen, addr_gen v <> gen ->
                gen_unmarked g gen -> gen_unmarked (lgraph_copy_v g v to) gen.
Proof.
  intros. unfold gen_unmarked in *. intros.
  assert (graph_has_v (lgraph_copy_v g v to) {| addr_gen := gen; addr_block := idx |}) by (split; assumption).
  apply lcv_graph_has_v_inv in H5. 2: assumption. destruct H5.
  - pose proof H5. destruct H6. simpl in * |- . specialize (H2 H6 _ H7).
    rewrite <- lcv_block_mark; try assumption. destruct v. simpl in *. intro. apply H1.
    inversion H8. reflexivity.
  - rewrite H5. rewrite lcv_vlabel_new; try assumption. unfold new_copied_v in H5.
    inversion H5. subst. assumption.
Qed.

Lemma lcv_gen_v_num_to: forall g v to,
    graph_has_gen g to -> (gen_v_num g to <= gen_v_num (lgraph_copy_v g v to) to)%nat.
Proof.
  intros. unfold gen_v_num, nth_gen; simpl. rewrite cvmgil_eq by assumption.
  simpl. lia.
Qed.
