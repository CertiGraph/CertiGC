From VST Require Import floyd.proofauto.

From CertiGC Require Export model.compatible.compatible.
From CertiGC Require Export model.constants.
From CertiGC Require Export model.heap.heap.
From CertiGC Require Export model.heapgraph.graph.
From CertiGC Require Export model.heapgraph.more.
From CertiGC Require Export model.op.copy.
From CertiGC Require Export model.op.cut.
From CertiGC Require Export model.op.do_generation.
From CertiGC Require Export model.op.forward.
From CertiGC Require Export model.op.reset.
From CertiGC Require Export model.op.scan.
From CertiGC Require Export model.op.update.
From CertiGC Require Export model.op.garbage_collect.
From CertiGC Require Export model.thread_info.thread_info.
From CertiGC Require Export model.util.

#[global]Instance share_inhabitant: Inhabitant share := emptyshare.
