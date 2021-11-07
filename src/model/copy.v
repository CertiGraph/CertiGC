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

From CertiGC Require Import model.constants.
From CertiGC Require Import model.graph.
From CertiGC Require Import model.heap.
From CertiGC Require Import model.thread_info.
From CertiGC Require Import model.util.

Local Coercion pg_lg: LabeledGraph >-> PreGraph.

Definition copy_v_add_edge
           (s: Addr) (g: PreGraph Addr Field) (p: Field * Addr):
  PreGraph Addr Field := pregraph_add_edge g (fst p) s (snd p).

Definition pregraph_copy_v (g: HeapGraph) (old_v new_v: Addr) : PreGraph Addr Field :=
  let old_edges := get_edges g old_v in
  let new_edges := combine (repeat new_v (length old_edges)) (map field_index old_edges) in
  let new_edge_dst_l := combine new_edges (map (dst g) old_edges) in
  let new_edge_dst_l' := map (fun x => ({| field_addr := fst (fst x); field_index := snd (fst x) |}, snd x)) new_edge_dst_l
  in fold_left (copy_v_add_edge new_v) new_edge_dst_l' (pregraph_add_vertex g new_v).

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