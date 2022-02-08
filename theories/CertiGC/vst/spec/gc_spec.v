From VST Require Import veric.rmaps.
From VST Require Import floyd.proofauto.
From VST Require Import floyd.library.
From CertiGraph Require Import lib.List_ext.
From CertiGraph Require Import msl_ext.iter_sepcon.
From CertiGraph Require Import graph.graph_model.

From CertiGC Require Import model.constants.
From CertiGC Require Import model.GCGraph.
From CertiGC Require Import vst.ast.env_graph_gc.
From CertiGC Require Import vst.clightgen.gc.
From CertiGC Require Import vst.cmodel.constants.
From CertiGC Require Import vst.cmodel.spatial_gcgraph.

Local Open Scope logic.

Definition gc_abort_t: type := tptr (Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tvoid cc_default).

Definition gc_abort_spec :=
  WITH e : val
  PRE [ tint ]
    PROP ()
    PARAMS (e)
    GLOBALS ()
    SEP ()
  POST [ tvoid ]
    PROP (False)
    LOCAL ()
    SEP ().

Definition MSS_constant (gv: globals): mpred :=
  data_at Ews (if Archi.ptr64 then tulong else tuint)
          (if Archi.ptr64 then Vlong (Int64.repr MAX_SPACE_SIZE) else
             Vint (Int.repr MAX_SPACE_SIZE)) (gv _MAX_SPACE_SIZE).

Definition Is_block_spec :=
  DECLARE _Is_block
  WITH x : val
  PRE [ int_or_ptr_type ]
    PROP (valid_int_or_ptr x)
    PARAMS (x)
    GLOBALS ()
    SEP()
  POST [ tint ]
    PROP()
    LOCAL(temp ret_temp
               (Vint (Int.repr (match x with
                                | Vptr _ _ => 1
                                | _ => 0
                                end))))
    SEP().

Definition IS_FROM_TYPE : TypeTree :=
  ProdType (ProdType (ProdType
                        (ProdType (ConstType share) (ConstType val))
                        (ConstType Z)) (ConstType val)) Mpred.

Program Definition Is_from_spec :=
  DECLARE _Is_from
  TYPE IS_FROM_TYPE
  WITH sh: share, start : val, n: Z, v: val, P: mpred
  PRE [tptr int_or_ptr_type,
       tptr int_or_ptr_type,
       tptr int_or_ptr_type]
    PROP ()
    PARAMS (start; offset_val n start; v)
    GLOBALS ()
    SEP (weak_derives P (memory_block sh n start * TT) && emp;
         weak_derives P (valid_pointer v * TT) && emp; P)
  POST [ tint ]
    EX b: {v_in_range v start n} + {~ v_in_range v start n},
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (if b then 1 else 0))))
    SEP (P).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, LAMBDAx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl;
    rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, ?approx_andp.
  f_equal; f_equal; [|f_equal]; now rewrite derives_nonexpansive_l.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  rewrite !approx_exp. apply f_equal; extensionality t.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal.
  rewrite !sepcon_emp, approx_idem. reflexivity.
Qed.

Definition forward_p_address
           (p: forward_p_type) (ti: val) (f_info: fun_info) (g: HeapGraph) : val :=
  match p with
  | inl root_index => field_address
                        thread_info_type
                        [ArraySubsc (Znth root_index (live_roots_indices f_info));
                           StructField _args] ti
  | inr (v, n) => offset_val (WORD_SIZE * n) (heapgraph_block_ptr g v)
  end.

Definition limit_address g t_info from : val :=
  offset_val (WORD_SIZE * (gen_size t_info from - space_remembered (nth_space t_info from))) (heapgraph_generation_base g from).

Definition next_address t_info to : val :=
  field_address heap_type
                [StructField _next;
                   ArraySubsc (Z.of_nat to); StructField _spaces] (ti_heap_p t_info).

Definition forward_spec :=
  DECLARE _forward
  WITH
    rsh: share, sh: share, gv: globals, fi: val, ti: val,
    g: HeapGraph, t_info: thread_info, f_info: fun_info,
    roots : roots_t, outlier: outlier_t,
    from: nat, to: nat, depth: Z, forward_p: forward_p_type
  PRE [ tptr int_or_ptr_type
      , tptr int_or_ptr_type
      , tptr (tptr int_or_ptr_type)
      , tptr int_or_ptr_type
      , tint
      ]
    PROP
      ( readable_share rsh; writable_share sh
      ; super_compatible (g, t_info, roots) f_info outlier
      ; forward_p_compatible forward_p roots g from
      ; forward_condition g t_info from to
      ; 0 <= depth <= Int.max_signed
      ; from <> to
      )
    PARAMS 
      ( heapgraph_generation_base g from
      ; limit_address g t_info from
      ; next_address t_info to
      ; forward_p_address forward_p ti f_info g
      ; Vint (Int.repr depth)
      )
    GLOBALS ()
    SEP
      ( fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g
      ; thread_info_rep sh t_info ti
      )
  POST [ tvoid ]
    EX g': HeapGraph,
    EX t_info': thread_info,
    EX roots': roots_t,
    PROP
      ( super_compatible (g', t_info', roots') f_info outlier
      ; roots' = upd_roots from to forward_p g roots f_info
      ; forward_relation from to (Z.to_nat depth) (forward_p2forward_t forward_p roots g) g g'
      ; forward_condition g' t_info' from to
      ; thread_info_relation t_info t_info'
      ; thread_info__remembered_invariant t_info t_info'
      )
    LOCAL ()
    SEP
      ( fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g'
      ; thread_info_rep sh t_info' ti
      ).

Definition forward_roots_spec :=
  DECLARE _forward_roots
  WITH
    rsh: share, sh: share, gv: globals, fi: val, ti: val,
    g: HeapGraph, t_info: thread_info, f_info: fun_info,
    roots: roots_t, outlier: outlier_t, from: nat, to: nat
  PRE [ tptr int_or_ptr_type
      , tptr int_or_ptr_type
      , tptr (tptr int_or_ptr_type)
      , tptr (if Archi.ptr64 then tulong else tuint)
      , tptr thread_info_type
      ]
    PROP
      ( readable_share rsh; writable_share sh
      ; super_compatible (g, t_info, roots) f_info outlier
      ; forward_condition g t_info from to
      ; from <> to
      )
    PARAMS
      ( heapgraph_generation_base g from
      ; limit_address g t_info from
      ; next_address t_info to
      ; fi
      ; ti
      )
    GLOBALS (gv)
    SEP
      ( fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g
      ; thread_info_rep sh t_info ti
      )
  POST [tvoid]
    EX g' : HeapGraph,
    EX t_info': thread_info,
    EX roots': roots_t,
    PROP
      ( super_compatible (g', t_info', roots') f_info outlier
      ; forward_roots_relation from to f_info roots g roots' g'
      ; forward_condition g' t_info' from to
      ; thread_info_relation t_info t_info'
      ; thread_info__remembered_invariant t_info t_info'
      )
    LOCAL ()
    SEP
      ( fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g'
      ; thread_info_rep sh t_info' ti
      ).

Definition do_scan_spec :=
  DECLARE _do_scan
  WITH
    rsh: share, sh: share, gv: globals, fi: val, ti: val,
    g: HeapGraph, t_info: thread_info, f_info: fun_info,
    roots : roots_t, outlier: outlier_t,
    from: nat, to: nat, to_index: nat
  PRE [ tptr int_or_ptr_type
      , tptr int_or_ptr_type
      , tptr int_or_ptr_type
      , tptr (tptr int_or_ptr_type)
      ]
    PROP
      ( readable_share rsh; writable_share sh
      ; super_compatible (g, t_info, roots) f_info outlier
      ; forward_condition g t_info from to
      ; from <> to; closure_has_index g to to_index
      ; 0 < gen_size t_info to - space_remembered (nth_space t_info to)
      ; heapgraph_generation_is_unmarked g to
      )
    PARAMS
      ( heapgraph_generation_base g from
      ; limit_address g t_info from
      ; offset_val (- WORD_SIZE) (heapgraph_block_ptr g {| addr_gen := to ; addr_block := to_index |})
      ; next_address t_info to
      )
    GLOBALS ()
    SEP
      ( fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g
      ; thread_info_rep sh t_info ti
      )
  POST [tvoid]
    EX g': HeapGraph,
    EX t_info': thread_info,
    PROP
      ( super_compatible (g', t_info', roots) f_info outlier
      ; forward_condition g' t_info' from to
      ; do_scan_relation from to to_index g g'
      ; thread_info_relation t_info t_info'
      ; thread_info__remembered_invariant t_info t_info'
      )
    LOCAL ()
    SEP
      ( fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g'
      ; thread_info_rep sh t_info' ti
      ).

Definition do_generation_spec :=
  DECLARE _do_generation
  WITH
    rsh: share, sh: share, gv: globals, fi: val, ti: val,
    g: HeapGraph, t_info: thread_info, f_info: fun_info,
    roots: roots_t, outlier: outlier_t, from: nat, to: nat
  PRE [ tptr space_type
      , tptr space_type
      , tptr (if Archi.ptr64 then tulong else tuint)
      , tptr thread_info_type
      ]
    PROP
      ( readable_share rsh; writable_share sh
      ; super_compatible (g, t_info, roots) f_info outlier
      ; do_generation_condition g t_info roots f_info from to
      ; from <> to
      )
    PARAMS
      ( space_address t_info from
      ; space_address t_info to
      ; fi
      ; ti
      )
    GLOBALS (gv)
    SEP
      ( fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g
      ; thread_info_rep sh t_info ti
      )
  POST [tvoid]
    EX g' : HeapGraph,
    EX t_info': thread_info,
    EX roots': roots_t,
    PROP
      ( super_compatible (g', t_info', roots') f_info outlier
      ; thread_info_relation t_info t_info'
      ; do_generation_relation from to f_info roots roots' g g'
      )
    LOCAL ()
    SEP
      ( fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g'
      ; thread_info_rep sh t_info' ti
      ).

Definition create_space_spec :=
  DECLARE _create_space
  WITH
    gc_abort: val, sh: share, s: val, n: Z, gv: globals, rsh: share
  PRE [ gc_abort_t
      , tptr space_type
      , if Archi.ptr64 then tulong else tuint
      ]
    PROP
      ( writable_share sh
      ; readable_share rsh
      ; 0 <= n < MAX_SPACE_SIZE
      )
    PARAMS
      ( gc_abort
      ; s
      ; if Archi.ptr64 then Vlong (Int64.repr n) else Vint (Int.repr n)
      )
    GLOBALS (gv)
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; mem_mgr gv
      ; data_at_ sh space_type s
      ; MSS_constant gv
      )
  POST [tvoid]
    EX p: val,
    PROP () LOCAL ()
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; mem_mgr gv
      ; MSS_constant gv
      ; malloc_token Ews (tarray int_or_ptr_type n) p
      ; data_at_ Ews (tarray int_or_ptr_type n) p
      ; data_at sh
          space_type
          ( p,
          ( p,
          ( offset_val (WORD_SIZE * n) p
          , offset_val (WORD_SIZE * n) p
          )))
          s
      ).

Definition create_heap_spec :=
  DECLARE _create_heap
  WITH gc_abort: val, sh: share, gv: globals
  PRE [gc_abort_t]
    PROP (readable_share sh)
    PARAMS (gc_abort)
    GLOBALS (gv)
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; mem_mgr gv
      ; MSS_constant gv
      )
  POST [tptr heap_type]
    EX h: val, EX p: val,
    PROP () LOCAL (temp ret_temp h)
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; mem_mgr gv
      ; MSS_constant gv
      ; malloc_token Ews heap_type h
      ; data_at Ews
          heap_type
          (
            ( p,
            ( p,
            ( offset_val (WORD_SIZE * NURSERY_SIZE) p
            , offset_val (WORD_SIZE * NURSERY_SIZE) p
            )))
          ::
            repeat nullspace (Z.to_nat (MAX_SPACES - 1))
          )
          h
      ; malloc_token Ews (tarray int_or_ptr_type NURSERY_SIZE) p
      ; data_at_ Ews (tarray int_or_ptr_type NURSERY_SIZE) p
      ).

Definition make_tinfo_spec :=
  DECLARE _make_tinfo
  WITH gc_abort:val, sh: share, gv: globals
  PRE [gc_abort_t]
    PROP (readable_share sh)
    PARAMS (gc_abort)
    GLOBALS (gv)
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; mem_mgr gv
      ; MSS_constant gv
      )
  POST [tptr thread_info_type]
    EX t: val,
    EX h: val,
    EX p: val,
    PROP () LOCAL (temp ret_temp t)
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; mem_mgr gv
      ; MSS_constant gv
      ; malloc_token Ews thread_info_type t
      ; data_at Ews
          thread_info_type
          ( p,
          ( offset_val (WORD_SIZE * NURSERY_SIZE) p,
          ( h
          , repeat Vundef (Z.to_nat MAX_ARGS)
          )))
          t
      ; malloc_token Ews heap_type h
      ; data_at Ews
          heap_type
          (
            ( p,
            ( p,
            ( offset_val (WORD_SIZE * NURSERY_SIZE) p
            , offset_val (WORD_SIZE * NURSERY_SIZE) p
            )))
          ::
            repeat nullspace (Z.to_nat (MAX_SPACES - 1))
          )
          h
      ; malloc_token Ews (tarray int_or_ptr_type NURSERY_SIZE) p
      ; data_at_ Ews (tarray int_or_ptr_type NURSERY_SIZE) p
      ).

Definition resume_spec :=
  DECLARE _resume
  WITH
    gc_abort: val, rsh: share, sh: share, gv: globals, fi: val, ti: val,
    g: HeapGraph, t_info: thread_info, f_info: fun_info,
    roots : roots_t
  PRE [ gc_abort_t
      , tptr (if Archi.ptr64 then tulong else tuint)
      , tptr thread_info_type
      ]
    PROP
      ( readable_share rsh
      ; writable_share sh
      ; graph_thread_info_compatible g t_info
      ; graph_gen_clear g O
      )
    PARAMS
      ( gc_abort
      ; fi
      ; ti
      )
    GLOBALS (gv)
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; fun_info_rep rsh f_info fi
      ; graph_rep g
      ; thread_info_rep sh t_info ti
      )
  POST [tvoid]
    PROP (fun_word_size f_info <= space_capacity (heap_head (ti_heap t_info)))
    LOCAL ()
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; fun_info_rep rsh f_info fi
      ; graph_rep g
      ; before_gc_thread_info_rep sh t_info ti
      ).

Definition garbage_collect_spec :=
  DECLARE _garbage_collect
  WITH
    gc_abort: val, rsh: share, sh: share, gv: globals, fi: val, ti: val,
    g: HeapGraph, t_info: thread_info, f_info: fun_info,
    roots : roots_t, outlier: outlier_t
  PRE [ gc_abort_t
      , tptr (if Archi.ptr64 then tulong else tuint)
      , tptr thread_info_type
      ]
    PROP
      ( readable_share rsh
      ; writable_share sh
      ; super_compatible (g, t_info, roots) f_info outlier
      ; garbage_collect_condition g t_info roots f_info
      ; heapgraph_can_copy g
      )
    PARAMS
      ( gc_abort
      ; fi
      ; ti
      )
    GLOBALS (gv)
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; MSS_constant gv
      ; fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g
      ; before_gc_thread_info_rep sh t_info ti
      ; ti_token_rep t_info
      )
  POST [tvoid]
    EX g': HeapGraph,
    EX t_info': thread_info,
    EX roots': roots_t,
    PROP
      ( super_compatible (g', t_info', roots') f_info outlier
      ; garbage_collect_relation f_info roots roots' g g'
      ; garbage_collect_condition g' t_info' roots' f_info
      ; heapgraph_can_copy g'
      )
    LOCAL ()
    SEP
      ( func_ptr' gc_abort_spec gc_abort
      ; mem_mgr gv
      ; MSS_constant gv
      ; fun_info_rep rsh f_info fi
      ; outlier_rep outlier
      ; graph_rep g'
      ; before_gc_thread_info_rep sh t_info' ti
      ; ti_token_rep t_info'
      ).

Definition reset_heap_spec :=
  DECLARE _reset_heap
  WITH h: val
  PRE [tptr heap_type]
    PROP ()
    PARAMS (h)
    GLOBALS ()
    SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

Definition free_heap_spec :=
  DECLARE _free_heap
  WITH h: val
  PRE [tptr heap_type]
    PROP () PARAMS (h) GLOBALS () SEP ()
  POST [tvoid]
  PROP () LOCAL () SEP ().

Definition Gprog: funspecs := ltac:(with_library prog
  [ Is_block_spec
  ; Is_from_spec
  ; forward_spec
  ; forward_roots_spec
  ; do_scan_spec
  ; do_generation_spec
  ; create_space_spec
  ; create_heap_spec
  ; make_tinfo_spec
  ; resume_spec
  ; garbage_collect_spec
  ; reset_heap_spec
  ; free_heap_spec
  ]).
