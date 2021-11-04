From VST Require Export floyd.proofauto.
From VST Require Export floyd.library.
From CertiGC Require Export ast.clightgen.gc.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition tvalue: type := tptr tvoid.

Definition thread_info_type : type := Tstruct _thread_info noattr.
Definition space_type : type := Tstruct _space noattr.
Definition heap_type: type := Tstruct _heap noattr.
