From Coq Require Import ZArith.ZArith.

From CertiGraph Require Import lib.List_ext.

From CertiGC Require Import model.heapgraph.block.block.
From CertiGC Require Import model.heapgraph.block.cell.
From CertiGC Require Import model.heapgraph.generation.generation.
From CertiGC Require Import model.heapgraph.graph.


Definition heapgraph_block_fields 
  (g : HeapGraph) (v : Addr) : 
  list Field := filter_sum_right (heapgraph_block_cells g v).


Lemma heapgraph_block_is_no_scan__no_fields 
  (g : HeapGraph) (v : Addr) 
  (Hv : heapgraph_block_is_no_scan g v) : 
  heapgraph_block_fields g v = nil.
Proof.
  (apply block_tag__no_scan in Hv).
  (unfold heapgraph_block_fields).
  (destruct (filter_sum_right (heapgraph_block_cells g v)) as [| f ff] eqn:E; try easy).
  (destruct Hv).
  (assert (Hf : In f (filter_sum_right (heapgraph_block_cells g v)))).
  {
    (rewrite E).
    now left.
  }
  (rewrite <- filter_sum_right_In_iff in Hf).
  clear ff E.
  (unfold heapgraph_block_cells in Hf).
  (remember (block_fields (heapgraph_block g v)) as xx eqn:Exx ).
  clear Exx.
  (remember O as n eqn:En ).
  clear En.
  revert n Hf.
  (induction xx as [| x xx IHxx]; simpl; intros n Hf; try easy).
  (destruct x as [x| ]; try destruct x as [x| x]; simpl in Hf; try now left).
  all: (destruct Hf as [Hf| Hf]; try easy).
  all: (right; now apply IHxx with (n + 1)%nat).
Qed.

Lemma heapgraph_block_fields_fst : forall g v e, In e (heapgraph_block_fields g v) -> field_addr e = v.
Proof.
  (intros g v e).
  (unfold heapgraph_block_fields, heapgraph_block_cells).
  (remember (block_fields (heapgraph_block g v))).
  (remember O as n).
  clear Heqn Heql.
  revert n.
  (induction l; intros; simpl in *).
  - (exfalso; assumption).
  - (destruct a; [ destruct s |  ]; simpl in *; [  |  | destruct H; [ subst e; simpl; reflexivity |  ] ];
      apply IHl in H; assumption).
Qed.


Lemma heapgraph_block_fields_In :
  forall g v s,
  In {| field_addr := v; field_index := s |} (heapgraph_block_fields g v) <->
  In s (map field_index (heapgraph_block_fields g v)).
Proof.
  (intros).
  (unfold heapgraph_block_fields, heapgraph_block_cells).
  (remember (block_fields (heapgraph_block g v))).
  (remember O as n).
  clear Heqn Heql.
  revert n.
  (induction l; intros; simpl; try easy).
  (destruct a as [a| ]; try destruct a as [a| a]; simpl).
  all: (rewrite IHl; try easy).
  intuition.
  (inversion H0).
  (left; reflexivity).
Qed.

Lemma ang_heapgraph_block_fields :
  forall g gi v, heapgraph_block_fields g v = heapgraph_block_fields (heapgraph_generations_append g gi) v.
Proof.
  (intros).
  (unfold heapgraph_block_fields, heapgraph_block_cells).
  (simpl).
  reflexivity.
Qed.
