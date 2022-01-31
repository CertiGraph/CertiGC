From VST Require Import floyd.proofauto.

From CertiGC Require Import vst.ast.env_graph_gc.
From CertiGC Require Import vst.clightgen.gc.
From CertiGC Require Import vst.spec.gc_spec.

Ltac hif_tac H :=
  match type of H with context [if ?a then _ else _] => destruct a eqn: ?H end.

Lemma body_Is_block: semax_body Vprog Gprog f_Is_block Is_block_spec.
Proof.
  start_function. forward_call x.
  forward.
  now destruct x.
Qed.
