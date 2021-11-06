From Coq Require Import ZArith.ZArith.

From compcert Require Import common.Values.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.heap.

Record thread_info: Type := {
    ti_heap_p: val;
    ti_heap: Heap;
    ti_args: list val;
    arg_size: Zlength ti_args = MAX_ARGS;
}.
