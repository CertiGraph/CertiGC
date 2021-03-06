From VST Require Import floyd.proofauto.
From VST Require Import floyd.library.
From CertiGC Require Import vst.clightgen.gc.

#[global]Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition thread_info_type : type := Tstruct _thread_info noattr.
Definition space_type : type := Tstruct _space noattr.
Definition nullspace: reptype space_type := (nullval, (nullval, (nullval, nullval))).
Definition heap_type: type := Tstruct _heap noattr.
