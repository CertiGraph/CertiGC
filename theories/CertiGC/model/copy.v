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
  let old_edges := heapgraph_block_fields g old_v in
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
    (Hn: In n (map field_index (heapgraph_block_fields g old))):
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
      unfold heapgraph_block_fields, heapgraph_block_cells.
      remember (block_fields (heapgraph_block g old)) as l eqn:El. clear El. remember O as m eqn:Em. clear Em.
      revert m. induction l as [|a l IHl] ; intro m ; simpl ; try constructor.
      destruct a; [destruct s|]; simpl ; try apply IHl. constructor.
      2: apply IHl. clear.
      cut (forall a b,
              In a (map field_index (filter_sum_right (fields_to_cells l old b))) -> b <= a)%nat.
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
      unfold heapgraph_block_fields in Hn. rewrite <- filter_sum_right_In_iff in Hn.
      unfold heapgraph_block_cells in Hn. apply fields_to_cells__in in Hn. destruct Hn as [s ?].
      inversion H. reflexivity. } subst x. remember (heapgraph_block_fields g old). clear Heql.
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
  block_tag__no_scan := block_tag__no_scan rvb;
|}.

Definition update_copied_new_vlabel (g: HeapGraph) (old_v new_v: Addr) :=
  update_vlabel (heapgraph_block g) new_v (heapgraph_block g old_v).

Definition update_copied_old_vlabel (g: HeapGraph) (old_v new_v: Addr) :=
  update_vlabel (heapgraph_block g) old_v (copy_v_mod_rvb (heapgraph_block g old_v) new_v).

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
  {| addr_gen := to; addr_block := generation_block_count (heapgraph_generation g to) |}.

Lemma heapgraph_has_block__ne__new_copied_v (g: HeapGraph) (to: nat) (x: Addr)
    (Hx: heapgraph_has_block g x):
    x <> new_copied_v g to.
Proof.
    unfold new_copied_v.
    destruct (Nat.eq_dec (addr_gen x) to) as [Eto|Hto].
    + subst to. intro F. rewrite F in Hx.
      pose proof (heapgraph_has_block__has_index Hx) as F'.
      red in F'. simpl in F'.
      lia.
    + intro F.
      rewrite F in Hto.
      now apply Hto.
Qed.


Definition lgraph_add_copied_v (g: HeapGraph) (v: Addr) (to: nat): HeapGraph :=
  let new_v := new_copied_v g to in
  Build_LabeledGraph _ _ _ (pregraph_copy_v g v new_v)
                     (update_copied_new_vlabel g v new_v)
                     (elabel g) (copy_v_update_glabel (heapgraph_generations g) to).

Definition lgraph_mark_copied (g: HeapGraph) (old new: Addr): HeapGraph :=
  Build_LabeledGraph _ _ _ (pg_lg g)
                     (update_copied_old_vlabel g old new) (elabel g) (heapgraph_generations g).

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


Lemma lacv_heapgraph_has_block_new: forall g v to,
    heapgraph_has_gen g to -> heapgraph_has_block (lgraph_add_copied_v g v to) (new_copied_v g to).
Proof.
  intros. split; simpl.
  - red. simpl. rewrite cvmgil_length; assumption.
  - red. unfold heapgraph_generation. simpl. rewrite cvmgil_eq by assumption. simpl. lia.
Qed.

Lemma lmc_heapgraph_has_block (g: HeapGraph) (old new x: Addr):
    heapgraph_has_block g x <-> heapgraph_has_block (lgraph_mark_copied g old new) x.
Proof.
    split ; intro H ; destruct H ; now constructor.
Qed.

Lemma lcv_graph_has_gen: forall g v to x,
    heapgraph_has_gen g to -> heapgraph_has_gen g x <-> heapgraph_has_gen (lgraph_copy_v g v to) x.
Proof. unfold heapgraph_has_gen. intros. simpl. rewrite cvmgil_length; intuition. Qed.

Lemma lmc_gen_start: forall g old new n,
    heapgraph_generation_base (lgraph_mark_copied g old new) n = heapgraph_generation_base g n.
Proof.
  intros. unfold heapgraph_generation_base. do 2 if_tac.
  - unfold heapgraph_generation. simpl. reflexivity.
  - unfold heapgraph_has_gen in *. simpl in *. contradiction.
  - unfold heapgraph_has_gen in *. simpl in *. contradiction.
  - reflexivity.
Qed.

Lemma lacv_heapgraph_generation: forall g v to n,
    n <> to -> heapgraph_has_gen g to ->
    heapgraph_generation (lgraph_add_copied_v g v to) n = heapgraph_generation g n.
Proof.
  intros. unfold lgraph_add_copied_v, heapgraph_generation. simpl. remember (generations (heapgraph_generations g)).
  apply cvmgil_not_eq; [|subst l]; assumption.
Qed.

Lemma lacv_graph_has_gen: forall g v to n,
    heapgraph_has_gen g to ->
    heapgraph_has_gen (lgraph_add_copied_v g v to) n <-> heapgraph_has_gen g n.
Proof.
  intros. unfold heapgraph_has_gen. simpl.
  rewrite cvmgil_length by assumption. reflexivity.
Qed.

Lemma lacv_gen_start: forall g v to n,
    heapgraph_has_gen g to -> heapgraph_generation_base (lgraph_add_copied_v g v to) n = heapgraph_generation_base g n.
Proof.
  intros. unfold heapgraph_generation_base. do 2 if_tac.
  - destruct (Nat.eq_dec n to).
    + subst n. unfold heapgraph_generation. simpl. rewrite cvmgil_eq by assumption.
      simpl. reflexivity.
    + rewrite lacv_heapgraph_generation by assumption. reflexivity.
  - rewrite lacv_graph_has_gen in H0 by assumption. contradiction.
  - exfalso. apply H0. rewrite lacv_graph_has_gen; assumption.
  - reflexivity.
Qed.

Lemma lacv_vlabel_old: forall (g : HeapGraph) (v : Addr) (to: nat) x,
    x <> new_copied_v g to -> heapgraph_block (lgraph_add_copied_v g v to) x = heapgraph_block g x.
Proof.
  intros. simpl.
  unfold update_copied_new_vlabel, graph_gen.update_vlabel.
  rewrite if_false. 1: reflexivity. unfold Equivalence.equiv; intro S; apply H.
  inversion S; reflexivity.
Qed.


Lemma lcv_gen_start: forall g v to n,
    heapgraph_has_gen g to -> heapgraph_generation_base (lgraph_copy_v g v to) n = heapgraph_generation_base g n.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_gen_start, lacv_gen_start; [reflexivity | assumption].
Qed.


Lemma lcv_heapgraph_generation: forall g v to n,
    n <> to -> heapgraph_has_gen g to -> heapgraph_generation (lgraph_copy_v g v to) n = heapgraph_generation g n.
Proof.
  intros. unfold lgraph_copy_v, heapgraph_generation. simpl.
  rewrite cvmgil_not_eq; [reflexivity | assumption..].
Qed.


Lemma lacv_heapgraph_block_cells_not_eq: forall (g : HeapGraph) (v : Addr) (to : nat) x,
    x <> new_copied_v g to ->
    heapgraph_block_cells (lgraph_add_copied_v g v to) x = heapgraph_block_cells g x.
Proof.
  intros. unfold heapgraph_block_cells. simpl. unfold update_copied_new_vlabel, update_vlabel.
  rewrite if_false. 1: reflexivity. intuition.
Qed.

Lemma lacv_heapgraph_block_ptr: forall (g : HeapGraph) (v : Addr) (to: nat) x,
    closure_has_v g x -> heapgraph_has_gen g to ->
    heapgraph_block_ptr (lgraph_add_copied_v g v to) x = heapgraph_block_ptr g x.
Proof.
  intros. destruct x as [n m]. destruct H. simpl in *. unfold heapgraph_block_ptr. f_equal.
  - f_equal. unfold heapgraph_block_offset. f_equal. unfold heapgraph_block_size_prev.
    simpl. apply fold_left_ext. intros. unfold heapgraph_block_size_accum. f_equal.
    unfold heapgraph_block_size. f_equal. rewrite lacv_vlabel_old. 1: reflexivity.
    intro. unfold new_copied_v in H3. inversion H3.
    rewrite nat_inc_list_In_iff in H2. subst n. red in H1. lia.
  - simpl. apply lacv_gen_start. assumption.
Qed.


Lemma lacv_heapgraph_block_ptr_old: forall (g : HeapGraph) (v : Addr) (to: nat) x,
    heapgraph_has_block g x -> heapgraph_has_gen g to ->
    heapgraph_block_ptr (lgraph_add_copied_v g v to) x = heapgraph_block_ptr g x.
Proof.
  intros. apply lacv_heapgraph_block_ptr; [apply heapgraph_has_block_in_closure |]; assumption.
Qed.

Lemma lacv_heapgraph_block_ptr_new: forall (g : HeapGraph) (v : Addr) (to: nat),
    heapgraph_has_gen g to ->
    heapgraph_block_ptr (lgraph_add_copied_v g v to) (new_copied_v g to) =
    heapgraph_block_ptr g (new_copied_v g to).
Proof.
  intros. unfold new_copied_v. apply lacv_heapgraph_block_ptr. 2: assumption.
  red. simpl.  split; [assumption | apply Nat.le_refl].
Qed.

Lemma lacv_heapgraph_block_header__old: forall (g : HeapGraph) (v : Addr) (to : nat) x,
    x <> new_copied_v g to ->
    heapgraph_block_header (lgraph_add_copied_v g v to) x = heapgraph_block_header g x.
Proof.
  intros. unfold heapgraph_block_header. rewrite lacv_vlabel_old by assumption. reflexivity.
Qed.

Lemma lacv_heapgraph_cell_val_heapgraph_block_cells_old:  forall (g : HeapGraph) (v : Addr) (to : nat) x,
    heapgraph_has_block g x -> heapgraph_has_gen g to -> no_dangling_dst g ->
    map (heapgraph_cell_val (lgraph_add_copied_v g v to))
        (heapgraph_block_cells (lgraph_add_copied_v g v to) x) =
    map (heapgraph_cell_val g) (heapgraph_block_cells g x).
Proof.
  intros. unfold heapgraph_block_cells. pose proof (heapgraph_has_block__ne__new_copied_v _ to _ H).
  rewrite lacv_vlabel_old by assumption. apply map_ext_in.
  intros [[? | ?] | ?] ?; simpl; try reflexivity. unfold new_copied_v.
  rewrite pcv_dst_old.
  - apply lacv_heapgraph_block_ptr_old. 2: assumption. specialize (H1 _ H). apply H1.
    unfold heapgraph_block_fields. rewrite <- filter_sum_right_In_iff. assumption.
  - apply fields_to_cells__in in H3. destruct H3 as [s ?]. subst. simpl. intro.
    unfold new_copied_v in H2. contradiction.
Qed.

Lemma lacv_heapgraph_block_cells_vals_old: forall (g : HeapGraph) (v : Addr) (to: nat) x,
    heapgraph_has_block g x -> heapgraph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    heapgraph_block_cells_vals (lgraph_add_copied_v g v to) x = heapgraph_block_cells_vals g x.
Proof.
  intros. pose proof (lacv_heapgraph_cell_val_heapgraph_block_cells_old _ v _ _ H H0 H1).
  unfold heapgraph_block_cells_vals. pose proof (heapgraph_has_block__ne__new_copied_v g to x H).
  rewrite lacv_vlabel_old by assumption. rewrite H3.
  destruct (block_mark (heapgraph_block g x)) eqn:? ; [f_equal | reflexivity].
  apply lacv_heapgraph_block_ptr_old; [apply H2|]; assumption.
Qed.

Lemma lacv_nth_sh: forall (g : HeapGraph) (v : Addr) (to : nat) n,
    heapgraph_has_gen g to -> heapgraph_generation_sh (lgraph_add_copied_v g v to) n = heapgraph_generation_sh g n.
Proof.
  intros. unfold heapgraph_generation_sh, heapgraph_generation. simpl. destruct (Nat.eq_dec n to).
  - subst n. rewrite cvmgil_eq by assumption. simpl. reflexivity.
  - rewrite cvmgil_not_eq by assumption. reflexivity.
Qed.

Lemma lacv_vlabel_new: forall g v to,
    heapgraph_block (lgraph_add_copied_v g v to) (new_copied_v g to) = heapgraph_block g v.
Proof.
  intros. simpl. unfold update_copied_new_vlabel, graph_gen.update_vlabel.
  rewrite if_true; reflexivity.
Qed.

Lemma lacv_heapgraph_block_header__new: forall g v to,
    heapgraph_block_header (lgraph_add_copied_v g v to) (new_copied_v g to) = heapgraph_block_header g v.
Proof. intros. unfold heapgraph_block_header. rewrite lacv_vlabel_new. reflexivity. Qed.

Lemma lacv_heapgraph_cell_val_heapgraph_block_cells_new: forall g v to,
    heapgraph_has_block g v -> heapgraph_has_gen g to -> no_dangling_dst g ->
    map (heapgraph_cell_val (lgraph_add_copied_v g v to))
        (heapgraph_block_cells (lgraph_add_copied_v g v to) (new_copied_v g to)) =
    map (heapgraph_cell_val g) (heapgraph_block_cells g v).
Proof.
  intros. unfold heapgraph_block_cells. rewrite lacv_vlabel_new.
  remember (block_fields (heapgraph_block g v)). remember O as n.
  assert (forall m, In m (map field_index (filter_sum_right (fields_to_cells l v n))) ->
                    In m (map field_index (heapgraph_block_fields g v))). {
    unfold heapgraph_block_fields, heapgraph_block_cells. subst. intuition. }
  clear Heql Heqn. revert n H2. induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|].
  - simpl in *. rewrite IHl; [reflexivity | assumption].
  - simpl in *. rewrite IHl; [reflexivity | assumption].
  - simpl in *. rewrite IHl.
    + assert (In n (map field_index (heapgraph_block_fields g v))) by (apply H2; left; reflexivity).
      f_equal. rewrite pcv_dst_new by assumption. apply lacv_heapgraph_block_ptr_old.
      2: assumption. red in H1. apply (H1 v). 1: assumption. apply in_map_iff in H3.
      destruct H3 as [[x ?] [? ?]]. simpl in H3. subst. clear -H4. pose proof H4.
      unfold heapgraph_block_fields in H4. rewrite <- filter_sum_right_In_iff in H4.
      unfold heapgraph_block_cells in H4. apply fields_to_cells__in in H4. destruct H4 as [s ?].
      inversion H0. subst. assumption.
    + intros. apply H2. right; assumption.
Qed.

Lemma lacv_heapgraph_block_cells_vals_new: forall g v to,
    heapgraph_has_block g v -> heapgraph_has_gen g to -> no_dangling_dst g -> copy_compatible g ->
    heapgraph_block_cells_vals (lgraph_add_copied_v g v to) (new_copied_v g to) =
    heapgraph_block_cells_vals g v.
Proof.
  intros. unfold heapgraph_block_cells_vals. rewrite lacv_vlabel_new.
  rewrite (lacv_heapgraph_cell_val_heapgraph_block_cells_new _ _ _ H H0 H1).
  destruct (block_mark (heapgraph_block g v)) eqn:? . 2: reflexivity. f_equal.
  apply lacv_heapgraph_block_ptr_old. 2: assumption. apply H2; assumption.
Qed.

Lemma lgraph_add_copied_v__heapgraph_has_block (g: HeapGraph) (v: Addr) (to: nat) (x: Addr)
    (Hto: heapgraph_has_gen g to)
    (Hx: heapgraph_has_block g x):
    heapgraph_has_block (lgraph_add_copied_v g v to) x.
Proof.
    refine {|
      heapgraph_has_block__has_gen := _;
      heapgraph_has_block__has_index := _;
    |}.
    + rewrite lacv_graph_has_gen. apply Hx. easy.
    + red.
      pose proof (heapgraph_has_block__has_index Hx) as Hgen.
      destruct (Nat.eq_dec (addr_gen x) to) as [Eto|Hx_to].
      - subst to.
        red in Hgen ; unfold heapgraph_generation in Hgen.
        unfold heapgraph_generation ; simpl.
        rewrite cvmgil_eq by assumption ; simpl.
        lia.
      - now rewrite lacv_heapgraph_generation.
Qed.


Lemma lcv_heapgraph_has_block_new: forall g v to,
    heapgraph_has_gen g to -> heapgraph_has_block (lgraph_copy_v g v to) (new_copied_v g to).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_heapgraph_has_block.
  apply lacv_heapgraph_has_block_new. assumption.
Qed.

Lemma lcv_heapgraph_has_block_old: forall g v to x,
    heapgraph_has_gen g to -> heapgraph_has_block g x -> heapgraph_has_block (lgraph_copy_v g v to) x.
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_heapgraph_has_block.
  apply lgraph_add_copied_v__heapgraph_has_block; assumption.
Qed.

Lemma lcv_heapgraph_block_size_new: forall (g : HeapGraph) (v : Addr) (to : nat),
    heapgraph_block_size (lgraph_copy_v g v to) (new_copied_v g to) = heapgraph_block_size g v.
Proof.
  intros. unfold heapgraph_block_size, lgraph_copy_v. simpl.
  unfold update_copied_old_vlabel, update_vlabel. if_tac.
  - simpl. unfold update_copied_new_vlabel, update_vlabel. if_tac; reflexivity.
  - rewrite lacv_vlabel_new. reflexivity.
Qed.

Lemma lcv_heapgraph_block_size_old: forall (g : HeapGraph) (v : Addr) (to : nat) x,
        heapgraph_has_gen g to -> heapgraph_has_block g x ->
        heapgraph_block_size (lgraph_copy_v g v to) x = heapgraph_block_size g x.
Proof.
  intros. unfold heapgraph_block_size, lgraph_copy_v. simpl.
  unfold update_copied_old_vlabel, update_vlabel. if_tac.
  - simpl. unfold update_copied_new_vlabel, update_vlabel. unfold equiv in H1. subst.
    if_tac; reflexivity.
  - rewrite lacv_vlabel_old. 1: reflexivity. apply heapgraph_has_block__ne__new_copied_v. assumption.
Qed.

Lemma lcv_pvs_same: forall g v to,
    heapgraph_has_gen g to ->
    heapgraph_block_size_prev (lgraph_copy_v g v to) to
                           (generation_block_count (heapgraph_generation (lgraph_copy_v g v to) to)) =
    heapgraph_block_size_prev g to (generation_block_count (heapgraph_generation g to)) + heapgraph_block_size g v.
Proof.
  intros. unfold heapgraph_generation. simpl. rewrite cvmgil_eq by assumption. simpl.
  remember (generation_block_count (nth to (generations (heapgraph_generations g)) null_generation)).
  replace (n + 1)%nat with (S n) by lia. rewrite heapgraph_block_size_prev__S. f_equal.
  - unfold heapgraph_block_size_prev. apply fold_left_ext. intros.
    unfold heapgraph_block_size_accum. f_equal. apply lcv_heapgraph_block_size_old. 1: assumption.
    rewrite nat_inc_list_In_iff in H0; subst; split; simpl; assumption.
  - assert ({| addr_gen := to; addr_block := n |} = new_copied_v g to) by
        (unfold new_copied_v, heapgraph_generation; subst n; reflexivity). rewrite H0.
    apply lcv_heapgraph_block_size_new.
Qed.

Lemma lcv_pvs_old: forall g v to gen,
    gen <> to -> heapgraph_has_gen g to -> heapgraph_has_gen g gen ->
    heapgraph_block_size_prev (lgraph_copy_v g v to) gen
                           (generation_block_count (heapgraph_generation (lgraph_copy_v g v to) gen)) =
    heapgraph_block_size_prev g gen (generation_block_count (heapgraph_generation g gen)).
Proof.
  intros. unfold heapgraph_generation. simpl. rewrite cvmgil_not_eq by assumption.
  remember (generation_block_count (nth gen (generations (heapgraph_generations g)) null_generation)).
  unfold heapgraph_block_size_prev. apply fold_left_ext. intros.
  unfold heapgraph_block_size_accum. f_equal. apply lcv_heapgraph_block_size_old. 1: assumption.
  rewrite nat_inc_list_In_iff in H2. subst. split; simpl; assumption.
Qed.

Lemma lmc_heapgraph_block_ptr: forall g v new_v x,
    heapgraph_block_ptr (lgraph_mark_copied g v new_v) x = heapgraph_block_ptr g x.
Proof.
  intros. unfold heapgraph_block_ptr. f_equal.
  f_equal. unfold heapgraph_block_offset. f_equal. unfold heapgraph_block_size_prev.
  apply fold_left_ext. intros. unfold heapgraph_block_size_accum. f_equal. unfold heapgraph_block_size.
  f_equal. simpl. unfold update_copied_old_vlabel, graph_gen.update_vlabel.
  destruct (EquivDec.equiv_dec v {| addr_gen := addr_gen x; addr_block := y |}).
  - unfold Equivalence.equiv in e. rewrite <- e. simpl. reflexivity.
  - reflexivity.
Qed.

Lemma lmc_heapgraph_block_cells: forall (g : HeapGraph) (old new v: Addr),
    heapgraph_block_cells (lgraph_mark_copied g old new) v = heapgraph_block_cells g v.
Proof.
  intros. unfold heapgraph_block_cells. simpl. unfold update_copied_old_vlabel, update_vlabel.
  if_tac; [unfold equiv in H; subst v |]; reflexivity.
Qed.

Lemma lmc_heapgraph_cell_val_heapgraph_block_cells: forall (g : HeapGraph) (v new_v x: Addr),
    map (heapgraph_cell_val (lgraph_mark_copied g v new_v))
        (heapgraph_block_cells (lgraph_mark_copied g v new_v) x) =
    map (heapgraph_cell_val g) (heapgraph_block_cells g x).
Proof.
  intros. rewrite lmc_heapgraph_block_cells. apply map_ext; intros.
  destruct a; [destruct s|]; simpl; [| |rewrite lmc_heapgraph_block_ptr]; reflexivity.
Qed.

Lemma lmc_vlabel_not_eq: forall g v new_v x,
    x <> v -> heapgraph_block (lgraph_mark_copied g v new_v) x = heapgraph_block g x.
Proof.
  intros. unfold lgraph_mark_copied, update_copied_old_vlabel, update_vlabel. simpl.
  rewrite if_false. 1: reflexivity. unfold equiv. intuition.
Qed.

Lemma lmc_heapgraph_block_cells_vals_not_eq: forall (g : HeapGraph) (v new_v : Addr) x,
    x <> v -> heapgraph_block_cells_vals (lgraph_mark_copied g v new_v) x = heapgraph_block_cells_vals g x.
Proof.
  intros. unfold heapgraph_block_cells_vals.
  rewrite lmc_heapgraph_cell_val_heapgraph_block_cells, lmc_vlabel_not_eq, lmc_heapgraph_block_ptr;
    [reflexivity | assumption].
Qed.

Lemma lmc_heapgraph_block_cells_vals_eq: forall (g : HeapGraph) (v new_v : Addr),
    heapgraph_block_cells_vals (lgraph_mark_copied g v new_v) v =
    heapgraph_block_ptr g new_v :: tl (heapgraph_block_cells_vals g v).
Proof.
  intros. unfold heapgraph_block_cells_vals at 1. simpl.
  unfold update_copied_old_vlabel, graph_gen.update_vlabel.
  rewrite if_true by reflexivity. simpl. rewrite lmc_heapgraph_block_ptr.
  assert (tl (heapgraph_block_cells_vals g v) = tl (map (heapgraph_cell_val g) (heapgraph_block_cells g v))) by
      (unfold heapgraph_block_cells_vals; destruct (block_mark (heapgraph_block g v)); simpl; reflexivity).
  rewrite H. clear H. do 2 f_equal. apply lmc_heapgraph_cell_val_heapgraph_block_cells.
Qed.


Lemma lmc_copy_compatible: forall g old new,
    heapgraph_has_block g new -> addr_gen old <> addr_gen new -> copy_compatible g ->
    copy_compatible (lgraph_mark_copied g old new).
Proof.
  repeat intro. destruct (Addr_EqDec old v).
  - compute in e. subst old. rewrite <- lmc_heapgraph_has_block. simpl.
    unfold update_copied_old_vlabel, update_vlabel. rewrite if_true by reflexivity.
    simpl. split; assumption.
  - assert (v <> old) by intuition. clear c.
    rewrite lmc_vlabel_not_eq, <- lmc_heapgraph_has_block in * by assumption.
    apply H1; assumption.
Qed.

Lemma lacv_heapgraph_has_block_inv (g: HeapGraph) (v: Addr) (to: nat) (x: Addr)
    (Hto: heapgraph_has_gen g to)
    (Hx: heapgraph_has_block (lgraph_add_copied_v g v to) x):
    heapgraph_has_block g x \/ x = new_copied_v g to.
Proof.
    destruct (Addr_EqDec x (new_copied_v g to)).
    + unfold equiv in e. now right.
    + left.
      refine {|
        heapgraph_has_block__has_gen := _;
        heapgraph_has_block__has_index := _;
      |}.
      - pose proof (heapgraph_has_block__has_gen Hx) as Hgen.
        now rewrite <- (lacv_graph_has_gen _ x to).
      - pose proof (heapgraph_has_block__has_index Hx) as Hindex.
        assert (x <> (new_copied_v g to)) as Hx__to by intuition.
        unfold heapgraph_generation_has_index in *.
        unfold heapgraph_generation, lgraph_add_copied_v in Hindex ; simpl in Hindex.
        destruct x as [x_gen x_index] ; unfold new_copied_v in Hx__to ; simpl in *.
        destruct (Nat.eq_dec x_gen to) as [E|Hx_gen__to].
        * subst x_gen.
          rewrite cvmgil_eq in Hindex by assumption ; simpl in Hindex.
          change (nth to (generations (heapgraph_generations g)) null_generation) with (heapgraph_generation g to) in Hindex.
          remember (generation_block_count (heapgraph_generation g to)) as n eqn:En.
          assert (x_index <> n) as Hn.
          {
            intro f.
            apply Hx__to.
            congruence.
          }
          lia.
        * now rewrite cvmgil_not_eq in Hindex.
Qed.

Lemma lacv_copy_compatible: forall (g : HeapGraph) (v : Addr) (to : nat),
    block_mark (heapgraph_block g v) = false -> heapgraph_has_gen g to ->
    copy_compatible g -> copy_compatible (lgraph_add_copied_v g v to).
Proof.
  repeat intro. destruct (Addr_EqDec v0 (new_copied_v g to)).
  - unfold equiv in e. subst v0. rewrite lacv_vlabel_new in *.
    rewrite H3 in H. inversion H.
  - assert (v0 <> (new_copied_v g to)) by intuition. clear c.
    rewrite lacv_vlabel_old in * by assumption.
    assert (heapgraph_has_block g v0). {
      apply lacv_heapgraph_has_block_inv in H2. 2: assumption. destruct H2. 1: assumption.
      contradiction. } split.
    + apply lgraph_add_copied_v__heapgraph_has_block; [|apply H1]; assumption.
    + apply H1; assumption.
Qed.

Lemma lcv_copy_compatible: forall g v to,
    block_mark (heapgraph_block g v) = false -> heapgraph_has_gen g to ->
    addr_gen v <> to -> copy_compatible g -> copy_compatible (lgraph_copy_v g v to).
Proof.
  intros. unfold lgraph_copy_v. apply lmc_copy_compatible. 2: simpl; assumption.
  - apply lacv_heapgraph_has_block_new. assumption.
  - apply lacv_copy_compatible; assumption.
Qed.

Lemma lmc_no_dangling_dst: forall g old new,
    no_dangling_dst g -> no_dangling_dst (lgraph_mark_copied g old new).
Proof.
  repeat intro. simpl. rewrite <- lmc_heapgraph_has_block in *.
  unfold heapgraph_block_fields in H1. rewrite lmc_heapgraph_block_cells in H1. apply (H v); assumption.
Qed.

Lemma lacv_heapgraph_block_fields_new: forall g v to,
  map field_index (heapgraph_block_fields (lgraph_add_copied_v g v to) (new_copied_v g to)) =
  map field_index (heapgraph_block_fields g v).
Proof.
  intros. unfold heapgraph_block_fields, heapgraph_block_cells. rewrite lacv_vlabel_new.
  remember (block_fields (heapgraph_block g v)). remember O. clear Heql Heqn. revert n.
  induction l; intros; simpl. 1: reflexivity.
  destruct a; [destruct s|]; simpl; rewrite IHl; reflexivity.
Qed.

Lemma lacv_no_dangling_dst: forall (g : HeapGraph) (v : Addr) (to : nat),
    no_dangling_dst g -> heapgraph_has_gen g to -> heapgraph_has_block g v ->
    no_dangling_dst (lgraph_add_copied_v g v to).
Proof.
  intros; intro x; intros. simpl. destruct (Addr_EqDec x (new_copied_v g to)).
  - unfold equiv in e0. subst x. pose proof H3. remember (new_copied_v g to) as new.
    apply heapgraph_block_fields_fst in H3. destruct e as [? s]. simpl in H3. subst.
    rewrite heapgraph_block_fields_In, lacv_heapgraph_block_fields_new in H4. rewrite pcv_dst_new.
    2: assumption. apply lgraph_add_copied_v__heapgraph_has_block. 1: assumption.
    apply (H v); [|rewrite heapgraph_block_fields_In]; assumption.
  - assert (x <> new_copied_v g to) by intuition. clear c. rewrite pcv_dst_old.
    + apply lgraph_add_copied_v__heapgraph_has_block. 1: assumption. apply lacv_heapgraph_has_block_inv in H2.
      2: assumption. destruct H2. 2: contradiction. apply (H x). 1: assumption.
      unfold heapgraph_block_fields in *. rewrite lacv_heapgraph_block_cells_not_eq in H3; assumption.
    + unfold heapgraph_block_fields in H3. rewrite <- filter_sum_right_In_iff in H3.
      apply fields_to_cells__in in H3. destruct H3 as [s ?]. subst e. simpl. assumption.
Qed.

Lemma lcv_no_dangling_dst: forall g v to,
    no_dangling_dst g -> heapgraph_has_gen g to -> heapgraph_has_block g v ->
    no_dangling_dst (lgraph_copy_v g v to).
Proof.
  intros. unfold lgraph_copy_v.
  apply lmc_no_dangling_dst, lacv_no_dangling_dst; assumption.
Qed.

Lemma lmc_outlier_compatible: forall g outlier old new,
    outlier_compatible g outlier ->
    outlier_compatible (lgraph_mark_copied g old new) outlier.
Proof.
  intros. intro v. intros. rewrite <- lmc_heapgraph_has_block in H0.
  unfold lgraph_mark_copied, update_copied_old_vlabel, update_vlabel; simpl.
  if_tac; simpl; apply H; [unfold equiv in H1; subst|]; assumption.
Qed.

Lemma lacv_outlier_compatible: forall (g : HeapGraph) outlier (v : Addr) (to : nat),
    heapgraph_has_gen g to -> heapgraph_has_block g v -> outlier_compatible g outlier ->
    outlier_compatible (lgraph_add_copied_v g v to) outlier.
Proof.
  intros. intros x ?. apply lacv_heapgraph_has_block_inv in H2. 2: assumption. destruct H2.
  - rewrite lacv_vlabel_old; [apply H1 | apply heapgraph_has_block__ne__new_copied_v]; assumption.
  - subst x. rewrite lacv_vlabel_new. apply H1; assumption.
Qed.

Lemma lcv_outlier_compatible: forall g outlier v to,
    heapgraph_has_gen g to -> heapgraph_has_block g v -> outlier_compatible g outlier ->
    outlier_compatible (lgraph_copy_v g v to) outlier.
Proof. intros. apply lmc_outlier_compatible, lacv_outlier_compatible; assumption. Qed.

Lemma lacv_unmarked_gen_size: forall g v to from,
    from <> to -> heapgraph_has_gen g to ->
    unmarked_gen_size g from = unmarked_gen_size (lgraph_add_copied_v g v to) from.
Proof.
  intros. unfold unmarked_gen_size. rewrite lacv_heapgraph_generation by assumption.
  remember (nat_inc_list (generation_block_count (heapgraph_generation g from))) as l.
  assert (forall i, {| addr_gen := from; addr_block := i |} <> new_copied_v g to). {
    intros. intro. inversion H1. apply H. assumption. }
  assert (filter (fun i : nat => negb (block_mark (heapgraph_block g {| addr_gen := from; addr_block := i |}))) l =
          filter (fun i : nat =>
                    negb(block_mark(heapgraph_block(lgraph_add_copied_v g v to) {| addr_gen := from; addr_block := i |}))) l). {
    apply filter_ext. intros. rewrite lacv_vlabel_old by apply H1. reflexivity. }
  rewrite <- H2. apply fold_left_ext. intros. unfold heapgraph_block_size_accum. f_equal.
  unfold heapgraph_block_size. rewrite lacv_vlabel_old by apply H1. reflexivity.
Qed.

Lemma lacv_estc: forall g t_info from to v,
    from <> to -> heapgraph_has_gen g to ->
    enough_space_to_copy g t_info from to ->
    enough_space_to_copy (lgraph_add_copied_v g v to) t_info from to.
Proof.
  unfold enough_space_to_copy. intros. rewrite <- lacv_unmarked_gen_size; assumption.
Qed.

Lemma lmc_unmarked_gen_size: forall g v v',
    heapgraph_has_block g v -> block_mark (heapgraph_block g v) = false ->
    unmarked_gen_size g (addr_gen v) =
    unmarked_gen_size (lgraph_mark_copied g v v') (addr_gen v) +
     heapgraph_block_size g v.
Proof.
  intros. unfold unmarked_gen_size. unfold heapgraph_generation. simpl heapgraph_generations.
  destruct v as [gen index]. simpl addr_gen.
  change (nth gen (generations (heapgraph_generations g)) null_generation) with (heapgraph_generation g gen).
  remember (nat_inc_list (generation_block_count (heapgraph_generation g gen))).
  rewrite (fold_left_ext (heapgraph_block_size_accum (lgraph_mark_copied g {| addr_gen := gen; addr_block := index |} v') gen)
                         (heapgraph_block_size_accum g gen)).
  - simpl. remember (fun i : nat => negb (block_mark (heapgraph_block g {| addr_gen := gen; addr_block := i |}))) as f1.
    remember (fun i : nat =>
                negb (block_mark (update_copied_old_vlabel g {| addr_gen := gen; addr_block := index |} v' {| addr_gen := gen; addr_block := i |})))
      as f2. cut (Permutation (filter f1 l) (index :: filter f2 l)).
    + intros. rewrite (fold_left_comm _ _ (index :: filter f2 l)). 3: assumption.
      * simpl. rewrite <- heapgraph_block_size_accum__fold_left. f_equal.
      * apply heapgraph_block_size_accum__comm.
    + apply filter_singular_perm; subst.
      * intros. unfold update_copied_old_vlabel, update_vlabel.
        rewrite if_false. 1: reflexivity. unfold equiv. intro. apply H2.
        inversion H3. reflexivity.
      * rewrite nat_inc_list_In_iff. destruct H. simpl in *. assumption.
      * unfold update_copied_old_vlabel, update_vlabel. rewrite if_true; reflexivity.
      * rewrite H0. reflexivity.
      * apply nat_inc_list_NoDup.
  - intros. unfold heapgraph_block_size_accum. f_equal. unfold heapgraph_block_size. f_equal.
    simpl. unfold update_copied_old_vlabel, update_vlabel. if_tac. 2: reflexivity.
    simpl. unfold equiv in H2. rewrite H2. reflexivity.
Qed.

Lemma lmc_estc:
  forall (g : HeapGraph) (t_info : thread_info) (v v': Addr) (to : nat)
         (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info))),
    enough_space_to_copy g t_info (addr_gen v) to ->
    heapgraph_has_block g v -> block_mark (heapgraph_block g v) = false ->
    forall
      Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (heapgraph_block_size g v),
      enough_space_to_copy (lgraph_mark_copied g v v')
                           (cut_thread_info
                              t_info (Z.of_nat to) (heapgraph_block_size g v) Hi Hh)
                           (addr_gen v) to.
Proof.
  unfold enough_space_to_copy. intros.
  rewrite (lmc_unmarked_gen_size g v v') in H by assumption.
  rewrite (cti_rest_gen_size _ _ (heapgraph_block_size g v) Hi Hh) in H. lia.
Qed.

Lemma forward_estc_unchanged: forall
    g t_info v to
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (heapgraph_block_size g v)),
    addr_gen v <> to -> heapgraph_has_gen g to ->
    heapgraph_has_block g v -> block_mark (heapgraph_block g v) = false ->
    enough_space_to_copy g t_info (addr_gen v) to ->
    enough_space_to_copy (lgraph_copy_v g v to)
         (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g v) Hi Hh)
      (addr_gen v) to.
Proof.
  intros. unfold lgraph_copy_v.
  apply (lacv_estc _ _ _ _ v) in H3; [| assumption..].
  assert (heapgraph_block_size g v = heapgraph_block_size (lgraph_add_copied_v g v to) v). {
    unfold heapgraph_block_size. rewrite lacv_vlabel_old. 1: reflexivity.
    intro. destruct v as [gen index]. simpl in H. unfold new_copied_v in H4.
    inversion H4. apply H. assumption. }
  remember (lgraph_add_copied_v g v to) as g'.
  pose proof Hh as Hh'. rewrite H4 in Hh'.
  replace (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g v) Hi Hh) with
      (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g' v) Hi Hh') by
      (apply cti_eq; symmetry; assumption).
  apply lmc_estc.
  - assumption.
  - subst g'. apply lgraph_add_copied_v__heapgraph_has_block; assumption.
  - subst g'. rewrite lacv_vlabel_old; [| apply heapgraph_has_block__ne__new_copied_v]; assumption.
Qed.

Lemma lcv_rgc_unchanged: forall g roots v to,
    heapgraph_has_gen g to ->
    roots_graph_compatible roots g ->
    roots_graph_compatible roots (lgraph_copy_v g v to).
Proof.
  intros. red in H0 |-*. rewrite Forall_forall in *. intros.
  apply lcv_heapgraph_has_block_old; [|apply H0]; assumption.
Qed.

Lemma lcv_roots_compatible_unchanged: forall g roots outlier v to,
    heapgraph_has_gen g to ->
    roots_compatible g outlier roots ->
    roots_compatible (lgraph_copy_v g v to) outlier roots.
Proof. intros. destruct H0. split; [|apply lcv_rgc_unchanged]; assumption. Qed.

Lemma lcv_heapgraph_block_ptr: forall g v to x,
    heapgraph_has_gen g to -> closure_has_v g x ->
    heapgraph_block_ptr (lgraph_copy_v g v to) x = heapgraph_block_ptr g x.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_heapgraph_block_ptr, lacv_heapgraph_block_ptr; [reflexivity | assumption..].
Qed.

Lemma lcv_heapgraph_block_ptr_new: forall g v to,
    heapgraph_has_gen g to ->
    heapgraph_block_ptr (lgraph_copy_v g v to) (new_copied_v g to) =
    heapgraph_block_ptr g (new_copied_v g to).
Proof.
  intros.
  apply lcv_heapgraph_block_ptr;  [| red; simpl; split]; [assumption..| apply Nat.le_refl].
Qed.

Lemma lcv_heapgraph_block_ptr_old: forall g v to x,
    heapgraph_has_gen g to -> heapgraph_has_block g x ->
    heapgraph_block_ptr (lgraph_copy_v g v to) x = heapgraph_block_ptr g x.
Proof.
  intros. apply lcv_heapgraph_block_ptr; [|apply heapgraph_has_block_in_closure]; assumption.
Qed.

Lemma lcv_fun_thread_arg_compatible_unchanged: forall
    g t_info f_info roots v to i s
    (Hi : 0 <= i < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth i (heap_spaces (ti_heap t_info))) s),
    heapgraph_has_gen g to ->
    roots_graph_compatible roots g ->
    fun_thread_arg_compatible g t_info f_info roots ->
    fun_thread_arg_compatible (lgraph_copy_v g v to)
         (cut_thread_info t_info i s Hi Hh) f_info roots.
Proof.
  intros.
  unfold fun_thread_arg_compatible in *. simpl. rewrite <- H1. apply map_ext_in.
  intros. destruct a; [destruct s0|]; [reflexivity..| simpl].
  apply lcv_heapgraph_block_ptr_old. 1: assumption. red in H0. rewrite Forall_forall in H0.
  apply H0. rewrite <- filter_sum_right_In_iff. assumption.
Qed.

Lemma lcv_graph_thread_info_compatible: forall
    g t_info v to
    (Hi : 0 <= Z.of_nat to < Zlength (heap_spaces (ti_heap t_info)))
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (heapgraph_block_size g v)),
    heapgraph_has_gen g to ->
    graph_thread_info_compatible g t_info ->
    graph_thread_info_compatible (lgraph_copy_v g v to)
      (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g v)
                       Hi Hh).
Proof.
  unfold graph_thread_info_compatible. intros. destruct H0 as [? [? ?]].
  assert (map space_base (heap_spaces (ti_heap t_info)) =
          map space_base
              (upd_Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))
                        (cut_space
                           (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info)))
                           (heapgraph_block_size g v) Hh))). {
    rewrite <- upd_Znth_map. simpl. rewrite <- Znth_map by assumption.
    rewrite upd_Znth_unchanged; [reflexivity | rewrite Zlength_map; assumption]. }
  split; [|split]; [|simpl; rewrite cvmgil_length by assumption..].
  - rewrite gsc_iff in *; simpl. 2: assumption.
    + intros. unfold nth_space. simpl.
      rewrite <- lcv_graph_has_gen in H4 by assumption. specialize (H0 _ H4).
      simpl in H0. destruct H0 as [? [? ?]]. split; [|split].
      * clear -H0 H3 H. rewrite <- map_nth, <- H3, map_nth. clear H3.
        unfold heapgraph_generation, nth_space in *. simpl. destruct (Nat.eq_dec gen to).
        -- subst gen. rewrite cvmgil_eq; simpl; assumption.
        -- rewrite cvmgil_not_eq; assumption.
      * assert (map space_sh
                    (upd_Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))
                              (cut_space
                                 (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info)))
                                 (heapgraph_block_size g v) Hh)) =
                map space_sh (heap_spaces (ti_heap t_info))). {
          rewrite <- upd_Znth_map. simpl. rewrite <- Znth_map by assumption.
          rewrite upd_Znth_unchanged; [reflexivity|rewrite Zlength_map; assumption]. }
        rewrite <- map_nth, H7, map_nth. clear -H5 H. unfold heapgraph_generation, nth_space in *.
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
    (Hh : has_space (Znth (Z.of_nat to) (heap_spaces (ti_heap t_info))) (heapgraph_block_size g v)),
    heapgraph_has_gen g to -> heapgraph_has_block g v ->
    super_compatible (g, t_info, roots) f_info outlier ->
    super_compatible
      (lgraph_copy_v g v to,
       (cut_thread_info t_info (Z.of_nat to) (heapgraph_block_size g v) Hi Hh),
       roots) f_info outlier.
Proof.
  intros. destruct H1 as [? [? [? ?]]]. split; [|split; [|split]].
  - apply lcv_graph_thread_info_compatible; assumption.
  - destruct H3. apply lcv_fun_thread_arg_compatible_unchanged; assumption.
  - apply lcv_roots_compatible_unchanged; assumption.
  - apply lcv_outlier_compatible; assumption.
Qed.

Lemma lcv_closure_has_v: forall g v to x,
    heapgraph_has_gen g to -> closure_has_v g x -> closure_has_v (lgraph_copy_v g v to) x.
Proof.
  intros. unfold closure_has_v in *. destruct x as [gen index]. simpl in *.
  destruct H0. split. 1: rewrite <- lcv_graph_has_gen; assumption.
  destruct (Nat.eq_dec gen to).
  - subst gen. red. unfold heapgraph_generation. simpl. rewrite cvmgil_eq by assumption.
    simpl. red in H1. unfold heapgraph_generation in H1. lia.
  - red. rewrite lcv_heapgraph_generation; assumption.
Qed.


Lemma lmc_block_fields: forall g old new x,
    block_fields (heapgraph_block g x) = block_fields (heapgraph_block (lgraph_mark_copied g old new) x).
Proof.
  intros. destruct (Addr_EqDec old x).
  - unfold equiv in e. subst. simpl. unfold update_copied_old_vlabel, update_vlabel.
    rewrite if_true by reflexivity. simpl. reflexivity.
  - assert (x <> old) by intuition.
    rewrite lmc_vlabel_not_eq; [reflexivity | assumption].
Qed.

Lemma lcv_block_fields: forall g v to x,
    heapgraph_has_gen g to -> heapgraph_has_block g x ->
    block_fields (heapgraph_block g x) = block_fields (heapgraph_block (lgraph_copy_v g v to) x).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_block_fields, lacv_vlabel_old.
  1: reflexivity. apply heapgraph_has_block__ne__new_copied_v; assumption.
Qed.

Lemma lcv_mfv_Zlen_eq: forall g v v' to,
    heapgraph_has_gen g to ->
    heapgraph_has_block g v ->
    Zlength (heapgraph_block_cells_vals g v) =
    Zlength (heapgraph_block_cells_vals (lgraph_copy_v g v' to) v).
Proof.
  intros. repeat rewrite fields_eq_length.
  rewrite <- lcv_block_fields by assumption; reflexivity.
Qed.


Lemma lmc_block_mark: forall g old new x,
    x <> old -> block_mark (heapgraph_block g x) =
                block_mark (heapgraph_block (lgraph_mark_copied g old new) x).
Proof.
  intros. destruct (Addr_EqDec x old).
  - unfold equiv in e. contradiction.
  - rewrite lmc_vlabel_not_eq; [reflexivity | assumption].
Qed.

Lemma lcv_block_mark: forall g v to x,
    x <> v -> heapgraph_has_gen g to -> heapgraph_has_block g x ->
    block_mark (heapgraph_block g x) = block_mark (heapgraph_block (lgraph_copy_v g v to) x).
Proof.
  intros. unfold lgraph_copy_v. rewrite <- lmc_block_mark by assumption.
  rewrite lacv_vlabel_old. 1: reflexivity. apply heapgraph_has_block__ne__new_copied_v; assumption.
Qed.


Lemma lcv_vlabel_new: forall g v to,
    addr_gen v <> to ->
    heapgraph_block (lgraph_copy_v g v to) (new_copied_v g to) = heapgraph_block g v.
Proof.
  intros. unfold lgraph_copy_v.
  rewrite lmc_vlabel_not_eq, lacv_vlabel_new;
    [| unfold new_copied_v; intro; apply H; inversion H0; simpl]; reflexivity.
Qed.


Lemma lcv_heapgraph_has_block_inv: forall (g : HeapGraph) (v : Addr) (to : nat) (x : Addr),
    heapgraph_has_gen g to -> heapgraph_has_block (lgraph_copy_v g v to) x ->
    heapgraph_has_block g x \/ x = new_copied_v g to.
Proof.
  intros. unfold lgraph_copy_v in H0. rewrite <- lmc_heapgraph_has_block in H0.
  apply (lacv_heapgraph_has_block_inv g v); assumption.
Qed.

Lemma lcv_heapgraph_generation_is_unmarked (to: nat) (g: HeapGraph) (v: Addr)
    (Hto: heapgraph_has_gen g to)
    (Hv: block_mark (heapgraph_block g v) = false)
    (gen: nat)
    (Hv__gen: addr_gen v <> gen)
    (Hgen: heapgraph_generation_is_unmarked g gen):
    heapgraph_generation_is_unmarked (lgraph_copy_v g v to) gen.
Proof.
    intros Hgen' index Hgen__index.
    assert (heapgraph_has_block (lgraph_copy_v g v to) {| addr_gen := gen; addr_block := index |}) as Hindex.
    {
      now refine {|
        heapgraph_has_block__has_gen := _;
        heapgraph_has_block__has_index := _;
      |}.
    }
    apply lcv_heapgraph_has_block_inv in Hindex ; try easy.
    destruct Hindex as [Hindex|Hindex].
    + pose proof (Hgen (heapgraph_has_block__has_gen Hindex) _ (heapgraph_has_block__has_index Hindex)) as Hgen''.
      rewrite <- lcv_block_mark ; try easy.
      intro F.
      apply Hv__gen.
      now subst v.
    + rewrite Hindex.
      rewrite lcv_vlabel_new ; try easy.
      unfold new_copied_v in Hindex.
      assert (gen = to) by now inversion Hindex.
      now subst to.
Qed.

Lemma lcv_gen_v_num_to: forall g v to,
    heapgraph_has_gen g to -> (heapgraph_generation_block_count g to <= heapgraph_generation_block_count (lgraph_copy_v g v to) to)%nat.
Proof.
  intros. unfold heapgraph_generation_block_count, heapgraph_generation; simpl. rewrite cvmgil_eq by assumption.
  simpl. lia.
Qed.
