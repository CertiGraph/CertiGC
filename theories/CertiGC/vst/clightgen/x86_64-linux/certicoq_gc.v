From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "src/c/include/coq-vsu-gc/src/certicoq_gc.c".
  Definition normalized := true.
End Info.

Definition __461 : ident := $"_461".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _alloc : ident := $"alloc".
Definition _args : ident := $"args".
Definition _certicoq_block__copy : ident := $"certicoq_block__copy".
Definition _certicoq_block__field_ptr_iter : ident := $"certicoq_block__field_ptr_iter".
Definition _certicoq_block__header_get_ptr : ident := $"certicoq_block__header_get_ptr".
Definition _certicoq_block__of_header : ident := $"certicoq_block__of_header".
Definition _certicoq_block__size_get : ident := $"certicoq_block__size_get".
Definition _certicoq_gc__abort : ident := $"certicoq_gc__abort".
Definition _certicoq_gc__cell_modify : ident := $"certicoq_gc__cell_modify".
Definition _certicoq_gc__free_heap : ident := $"certicoq_gc__free_heap".
Definition _certicoq_gc__funs_init : ident := $"certicoq_gc__funs_init".
Definition _certicoq_gc__garbage_collect : ident := $"certicoq_gc__garbage_collect".
Definition _certicoq_gc__make_tinfo : ident := $"certicoq_gc__make_tinfo".
Definition _certicoq_gc__reset_heap : ident := $"certicoq_gc__reset_heap".
Definition _e : ident := $"e".
Definition _exit : ident := $"exit".
Definition _fi : ident := $"fi".
Definition _free_heap : ident := $"free_heap".
Definition _garbage_collect : ident := $"garbage_collect".
Definition _gc_abort : ident := $"gc_abort".
Definition _gc_block__copy : ident := $"gc_block__copy".
Definition _gc_block__header_get_ptr : ident := $"gc_block__header_get_ptr".
Definition _gc_block__of_header : ident := $"gc_block__of_header".
Definition _gc_block__ptr_iter : ident := $"gc_block__ptr_iter".
Definition _gc_block__size_get : ident := $"gc_block__size_get".
Definition _gc_funs : ident := $"gc_funs".
Definition _h : ident := $"h".
Definition _heap : ident := $"heap".
Definition _int_or_ptr__is_int : ident := $"int_or_ptr__is_int".
Definition _limit : ident := $"limit".
Definition _main : ident := $"main".
Definition _make_tinfo : ident := $"make_tinfo".
Definition _out : ident := $"out".
Definition _p_cell : ident := $"p_cell".
Definition _p_val : ident := $"p_val".
Definition _remember : ident := $"remember".
Definition _reset_heap : ident := $"reset_heap".
Definition _thread_info : ident := $"thread_info".
Definition _ti : ident := $"ti".
Definition _t'1 : ident := 128%positive.

Definition f_certicoq_gc__abort := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_e, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
  ((Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
|}.

Definition f_certicoq_gc__funs_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct __461 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct __461 noattr)))
        (Tstruct __461 noattr)) _gc_abort
      (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default)))
    (Evar _certicoq_gc__abort (Tfunction (Tcons tint Tnil) tvoid cc_default)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct __461 noattr)))
          (Tstruct __461 noattr)) _gc_block__header_get_ptr
        (tptr (Tfunction (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil)
                (tptr tulong) cc_default)))
      (Evar _certicoq_block__header_get_ptr (Tfunction
                                              (Tcons
                                                (tptr (talignas 3%N (tptr tvoid)))
                                                Tnil) (tptr tulong)
                                              cc_default)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct __461 noattr)))
            (Tstruct __461 noattr)) _gc_block__copy
          (tptr (Tfunction
                  (Tcons (tptr (talignas 3%N (tptr tvoid)))
                    (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil))
                  (tptr (talignas 3%N (tptr tvoid))) cc_default)))
        (Evar _certicoq_block__copy (Tfunction
                                      (Tcons
                                        (tptr (talignas 3%N (tptr tvoid)))
                                        (Tcons
                                          (tptr (talignas 3%N (tptr tvoid)))
                                          Tnil))
                                      (tptr (talignas 3%N (tptr tvoid)))
                                      cc_default)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct __461 noattr)))
              (Tstruct __461 noattr)) _gc_block__ptr_iter
            (tptr (Tfunction
                    (Tcons (tptr (talignas 3%N (tptr tvoid)))
                      (Tcons
                        (tptr (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                    Tnil)) tvoid cc_default))
                        (Tcons (tptr tvoid) Tnil))) tvoid cc_default)))
          (Evar _certicoq_block__field_ptr_iter (Tfunction
                                                  (Tcons
                                                    (tptr (talignas 3%N (tptr tvoid)))
                                                    (Tcons
                                                      (tptr (Tfunction
                                                              (Tcons
                                                                (tptr tvoid)
                                                                (Tcons
                                                                  (tptr (talignas 3%N (tptr tvoid)))
                                                                  Tnil))
                                                              tvoid
                                                              cc_default))
                                                      (Tcons (tptr tvoid)
                                                        Tnil))) tvoid
                                                  cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct __461 noattr)))
                (Tstruct __461 noattr)) _gc_block__of_header
              (tptr (Tfunction (Tcons (tptr tulong) Tnil)
                      (tptr (talignas 3%N (tptr tvoid))) cc_default)))
            (Evar _certicoq_block__of_header (Tfunction
                                               (Tcons (tptr tulong) Tnil)
                                               (tptr (talignas 3%N (tptr tvoid)))
                                               cc_default)))
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct __461 noattr)))
                (Tstruct __461 noattr)) _gc_block__size_get
              (tptr (Tfunction (Tcons (tptr tulong) Tnil) tulong cc_default)))
            (Evar _certicoq_block__size_get (Tfunction
                                              (Tcons (tptr tulong) Tnil)
                                              tulong cc_default))))))))
|}.

Definition f_certicoq_gc__make_tinfo := {|
  fn_return := (tptr (Tstruct _thread_info noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _make_tinfo (Tfunction
                        (Tcons
                          (tptr (Tfunction (Tcons tint Tnil) tvoid
                                  cc_default)) Tnil)
                        (tptr (Tstruct _thread_info noattr)) cc_default))
    ((Evar _certicoq_gc__abort (Tfunction (Tcons tint Tnil) tvoid cc_default)) ::
     nil))
  (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _thread_info noattr))))))
|}.

Definition f_certicoq_gc__free_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _free_heap (Tfunction (Tcons (tptr (Tstruct _heap noattr)) Tnil)
                     tvoid cc_default))
  ((Etempvar _h (tptr (Tstruct _heap noattr))) :: nil))
|}.

Definition f_certicoq_gc__reset_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _reset_heap (Tfunction (Tcons (tptr (Tstruct _heap noattr)) Tnil)
                      tvoid cc_default))
  ((Etempvar _h (tptr (Tstruct _heap noattr))) :: nil))
|}.

Definition f_certicoq_gc__cell_modify := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) ::
                (_p_cell, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_p_val, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef (Etempvar _p_cell (tptr (talignas 3%N (tptr tvoid))))
      (talignas 3%N (tptr tvoid)))
    (Etempvar _p_val (talignas 3%N (tptr tvoid))))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _int_or_ptr__is_int (Tfunction
                                  (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                  tint cc_default))
      ((Etempvar _p_val (talignas 3%N (tptr tvoid))) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Scall None
        (Evar _remember (Tfunction
                          (Tcons (tptr (Tstruct _thread_info noattr))
                            (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil))
                          tvoid cc_default))
        ((Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
         (Etempvar _p_cell (tptr (talignas 3%N (tptr tvoid)))) :: nil))
      Sskip)))
|}.

Definition f_certicoq_gc__garbage_collect := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tulong)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := ((_gc_funs, (Tstruct __461 noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _certicoq_gc__funs_init (Tfunction
                                    (Tcons (tptr (Tstruct __461 noattr))
                                      Tnil) tvoid cc_default))
    ((Eaddrof (Evar _gc_funs (Tstruct __461 noattr))
       (tptr (Tstruct __461 noattr))) :: nil))
  (Scall None
    (Evar _garbage_collect (Tfunction
                             (Tcons (tptr (Tstruct __461 noattr))
                               (Tcons (tptr tulong)
                                 (Tcons (tptr (Tstruct _thread_info noattr))
                                   Tnil))) tvoid cc_default))
    ((Eaddrof (Evar _gc_funs (Tstruct __461 noattr))
       (tptr (Tstruct __461 noattr))) :: (Etempvar _fi (tptr tulong)) ::
     (Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil)))
|}.

Definition composites : list composite_definition :=
(Composite __461 Struct
   ((_gc_abort, (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))) ::
    (_gc_block__header_get_ptr,
     (tptr (Tfunction (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil)
             (tptr tulong) cc_default))) ::
    (_gc_block__copy,
     (tptr (Tfunction
             (Tcons (tptr (talignas 3%N (tptr tvoid)))
               (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil))
             (tptr (talignas 3%N (tptr tvoid))) cc_default))) ::
    (_gc_block__ptr_iter,
     (tptr (Tfunction
             (Tcons (tptr (talignas 3%N (tptr tvoid)))
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil))
                         tvoid cc_default)) (Tcons (tptr tvoid) Tnil))) tvoid
             cc_default))) ::
    (_gc_block__of_header,
     (tptr (Tfunction (Tcons (tptr tulong) Tnil)
             (tptr (talignas 3%N (tptr tvoid))) cc_default))) ::
    (_gc_block__size_get,
     (tptr (Tfunction (Tcons (tptr tulong) Tnil) tulong cc_default))) :: nil)
   noattr ::
 Composite _thread_info Struct
   ((_alloc, (tptr (talignas 3%N (tptr tvoid)))) ::
    (_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
    (_heap, (tptr (Tstruct _heap noattr))) ::
    (_args, (tarray (talignas 3%N (tptr tvoid)) 1024)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_int_or_ptr__is_int,
   Gfun(External (EF_external "int_or_ptr__is_int"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil) tint cc_default)) ::
 (_certicoq_block__of_header,
   Gfun(External (EF_external "certicoq_block__of_header"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tulong) Tnil) (tptr (talignas 3%N (tptr tvoid)))
     cc_default)) ::
 (_certicoq_block__copy,
   Gfun(External (EF_external "certicoq_block__copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default))
     (Tcons (tptr (talignas 3%N (tptr tvoid)))
       (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil))
     (tptr (talignas 3%N (tptr tvoid))) cc_default)) ::
 (_certicoq_block__header_get_ptr,
   Gfun(External (EF_external "certicoq_block__header_get_ptr"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil) (tptr tulong)
     cc_default)) ::
 (_certicoq_block__size_get,
   Gfun(External (EF_external "certicoq_block__size_get"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tulong) Tnil) tulong cc_default)) ::
 (_certicoq_block__field_ptr_iter,
   Gfun(External (EF_external "certicoq_block__field_ptr_iter"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (talignas 3%N (tptr tvoid)))
       (Tcons
         (tptr (Tfunction
                 (Tcons (tptr tvoid)
                   (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil)) tvoid
                 cc_default)) (Tcons (tptr tvoid) Tnil))) tvoid cc_default)) ::
 (_make_tinfo,
   Gfun(External (EF_external "make_tinfo"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default)) Tnil)
     (tptr (Tstruct _thread_info noattr)) cc_default)) ::
 (_free_heap,
   Gfun(External (EF_external "free_heap"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _heap noattr)) Tnil) tvoid cc_default)) ::
 (_reset_heap,
   Gfun(External (EF_external "reset_heap"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _heap noattr)) Tnil) tvoid cc_default)) ::
 (_remember,
   Gfun(External (EF_external "remember"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _thread_info noattr))
       (Tcons (tptr (talignas 3%N (tptr tvoid))) Tnil)) tvoid cc_default)) ::
 (_garbage_collect,
   Gfun(External (EF_external "garbage_collect"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __461 noattr))
       (Tcons (tptr tulong)
         (Tcons (tptr (Tstruct _thread_info noattr)) Tnil))) tvoid
     cc_default)) ::
 (_certicoq_gc__abort, Gfun(Internal f_certicoq_gc__abort)) ::
 (_certicoq_gc__funs_init, Gfun(Internal f_certicoq_gc__funs_init)) ::
 (_certicoq_gc__make_tinfo, Gfun(Internal f_certicoq_gc__make_tinfo)) ::
 (_certicoq_gc__free_heap, Gfun(Internal f_certicoq_gc__free_heap)) ::
 (_certicoq_gc__reset_heap, Gfun(Internal f_certicoq_gc__reset_heap)) ::
 (_certicoq_gc__cell_modify, Gfun(Internal f_certicoq_gc__cell_modify)) ::
 (_certicoq_gc__garbage_collect, Gfun(Internal f_certicoq_gc__garbage_collect)) ::
 nil).

Definition public_idents : list ident :=
(_certicoq_gc__garbage_collect :: _certicoq_gc__cell_modify ::
 _certicoq_gc__reset_heap :: _certicoq_gc__free_heap ::
 _certicoq_gc__make_tinfo :: _certicoq_gc__funs_init ::
 _certicoq_gc__abort :: _garbage_collect :: _remember :: _reset_heap ::
 _free_heap :: _make_tinfo :: _certicoq_block__field_ptr_iter ::
 _certicoq_block__size_get :: _certicoq_block__header_get_ptr ::
 _certicoq_block__copy :: _certicoq_block__of_header ::
 _int_or_ptr__is_int :: _exit :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___builtin_expect :: ___builtin_unreachable :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


(*\nInput hashes (sha256):\n\n630c3547bf08e23466bf39d52436a4ad1c478a04dc68d6955a5c17b2a1cf48b2  src/c/include/coq-vsu-gc/src/certicoq_gc.c
c8423c1389e9864f1c3f32ed7b03deb669d6c7b4d48b7fd95f41f5420660edb8  src/c/include/coq-vsu-gc/certicoq_gc.h
c952f07ed3f3338c4635737fc467bd2f1901d5e89a2b68100d0b046573a26bbf  src/c/include/coq-vsu-gc/gc.h
a9b18c1959df2cb5404306021e5256eb25c78c20ef9ec326a1cac75cea375fe7  src/c/include/coq-vsu-gc/mem.h\n*)
