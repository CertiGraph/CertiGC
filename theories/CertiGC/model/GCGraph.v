From VST Require Import floyd.proofauto.

From CertiGC Require Export model.constants.
From CertiGC Require Export model.compatible.
From CertiGC Require Export model.copy.
From CertiGC Require Export model.cut.
From CertiGC Require Export model.do_generation.
From CertiGC Require Export model.forward.
From CertiGC Require Export model.garbage_collect.
From CertiGC Require Export model.graph.
From CertiGC Require Export model.heap.
From CertiGC Require Export model.reset.
From CertiGC Require Export model.update.
From CertiGC Require Export model.util.
From CertiGC Require Export model.scan.
From CertiGC Require Export model.thread_info.

#[global]Instance share_inhabitant: Inhabitant share := emptyshare.
