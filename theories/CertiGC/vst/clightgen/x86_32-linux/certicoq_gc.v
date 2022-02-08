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
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "src/c/include/coq-vsu-gc/src/certicoq_gc.c".
  Definition normalized := true.
End Info.

Definition __474 : ident := $"_474".
Definition __497 : ident := $"_497".
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
Definition _certicoq_gc__num_allocs : ident := $"certicoq_gc__num_allocs".
Definition _certicoq_gc__remember : ident := $"certicoq_gc__remember".
Definition _certicoq_gc__reset_heap : ident := $"certicoq_gc__reset_heap".
Definition _certicoq_gc__resume : ident := $"certicoq_gc__resume".
Definition _certicoq_gc__root_ptr_iter : ident := $"certicoq_gc__root_ptr_iter".
Definition _create_heap : ident := $"create_heap".
Definition _e : ident := $"e".
Definition _end : ident := $"end".
Definition _exit : ident := $"exit".
Definition _f : ident := $"f".
Definition _f_args : ident := $"f_args".
Definition _fi : ident := $"fi".
Definition _free_heap : ident := $"free_heap".
Definition _garbage_collect : ident := $"garbage_collect".
Definition _gc_abort : ident := $"gc_abort".
Definition _gc_block__copy : ident := $"gc_block__copy".
Definition _gc_block__header_get_ptr : ident := $"gc_block__header_get_ptr".
Definition _gc_block__of_base : ident := $"gc_block__of_base".
Definition _gc_block__ptr_iter : ident := $"gc_block__ptr_iter".
Definition _gc_block__size_get : ident := $"gc_block__size_get".
Definition _gc_funs : ident := $"gc_funs".
Definition _gc_rt__num_allocs : ident := $"gc_rt__num_allocs".
Definition _gc_rt__resume : ident := $"gc_rt__resume".
Definition _gc_rt__root_ptr_iter : ident := $"gc_rt__root_ptr_iter".
Definition _h : ident := $"h".
Definition _heap : ident := $"heap".
Definition _i : ident := $"i".
Definition _int_or_ptr__is_int : ident := $"int_or_ptr__is_int".
Definition _limit : ident := $"limit".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _n : ident := $"n".
Definition _next : ident := $"next".
Definition _odata : ident := $"odata".
Definition _out : ident := $"out".
Definition _p : ident := $"p".
Definition _p_cell : ident := $"p_cell".
Definition _p_val : ident := $"p_val".
Definition _remember : ident := $"remember".
Definition _reset_heap : ident := $"reset_heap".
Definition _roots : ident := $"roots".
Definition _rt : ident := $"rt".
Definition _space : ident := $"space".
Definition _spaces : ident := $"spaces".
Definition _start : ident := $"start".
Definition _thread_info : ident := $"thread_info".
Definition _ti : ident := $"ti".
Definition _tinfo : ident := $"tinfo".
Definition _void_rt : ident := $"void_rt".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.

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

Definition f_certicoq_gc__num_allocs := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_void_rt, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_rt, (tptr (Tstruct __497 noattr))) :: (_t'2, tuint) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _rt
    (Ecast (Etempvar _void_rt (tptr tvoid)) (tptr (Tstruct __497 noattr))))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _rt (tptr (Tstruct __497 noattr)))
          (Tstruct __497 noattr)) _fi (tptr tuint)))
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Etempvar _t'1 (tptr tuint))
            (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
      (Sreturn (Some (Etempvar _t'2 tuint))))))
|}.

Definition f_certicoq_gc__resume := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_void_rt, (tptr tvoid)) ::
                (_alloc, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_limit, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_rt, (tptr (Tstruct __497 noattr))) ::
               (_t'2, (tptr (Tstruct _thread_info noattr))) ::
               (_t'1, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _rt
    (Ecast (Etempvar _void_rt (tptr tvoid)) (tptr (Tstruct __497 noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _rt (tptr (Tstruct __497 noattr)))
            (Tstruct __497 noattr)) _ti (tptr (Tstruct _thread_info noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _t'2 (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _alloc
          (tptr (talignas 2%N (tptr tvoid))))
        (Etempvar _alloc (tptr (talignas 2%N (tptr tvoid))))))
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _rt (tptr (Tstruct __497 noattr)))
            (Tstruct __497 noattr)) _ti (tptr (Tstruct _thread_info noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _t'1 (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _limit
          (tptr (talignas 2%N (tptr tvoid))))
        (Etempvar _limit (tptr (talignas 2%N (tptr tvoid))))))))
|}.

Definition f_certicoq_gc__root_ptr_iter := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_void_rt, (tptr tvoid)) ::
                (_f,
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil))
                         tvoid cc_default))) :: (_f_args, (tptr tvoid)) ::
                nil);
  fn_vars := ((_f_args, (tptr tvoid)) :: nil);
  fn_temps := ((_rt, (tptr (Tstruct __497 noattr))) :: (_n, tuint) ::
               (_roots, (tptr tuint)) ::
               (_args, (tptr (talignas 2%N (tptr tvoid)))) :: (_i, tuint) ::
               (_p, (tptr (talignas 2%N (tptr tvoid)))) :: (_t'1, tint) ::
               (_t'6, (tptr tuint)) :: (_t'5, (tptr tuint)) ::
               (_t'4, (tptr (Tstruct _thread_info noattr))) ::
               (_t'3, tuint) :: (_t'2, (talignas 2%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _f_args (tptr tvoid)) (Etempvar _f_args (tptr tvoid)))
  (Ssequence
    (Sset _rt
      (Ecast (Etempvar _void_rt (tptr tvoid)) (tptr (Tstruct __497 noattr))))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _rt (tptr (Tstruct __497 noattr)))
              (Tstruct __497 noattr)) _fi (tptr tuint)))
        (Sset _n
          (Ederef
            (Ebinop Oadd (Etempvar _t'6 (tptr tuint))
              (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _rt (tptr (Tstruct __497 noattr)))
                (Tstruct __497 noattr)) _fi (tptr tuint)))
          (Sset _roots
            (Ebinop Oadd (Etempvar _t'5 (tptr tuint))
              (Econst_int (Int.repr 2) tint) (tptr tuint))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _rt (tptr (Tstruct __497 noattr)))
                  (Tstruct __497 noattr)) _ti
                (tptr (Tstruct _thread_info noattr))))
            (Sset _args
              (Efield
                (Ederef (Etempvar _t'4 (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _args
                (tarray (talignas 2%N (tptr tvoid)) 1024))))
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                               (Etempvar _n tuint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Ederef
                        (Ebinop Oadd (Etempvar _roots (tptr tuint))
                          (Etempvar _i tuint) (tptr tuint)) tuint))
                    (Sset _p
                      (Ebinop Oadd
                        (Etempvar _args (tptr (talignas 2%N (tptr tvoid))))
                        (Etempvar _t'3 tuint)
                        (tptr (talignas 2%N (tptr tvoid))))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'2
                        (Ederef
                          (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                          (talignas 2%N (tptr tvoid))))
                      (Scall (Some _t'1)
                        (Evar _int_or_ptr__is_int (Tfunction
                                                    (Tcons
                                                      (talignas 2%N (tptr tvoid))
                                                      Tnil) tint cc_default))
                        ((Etempvar _t'2 (talignas 2%N (tptr tvoid))) :: nil)))
                    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Scall None
                        (Etempvar _f (tptr (Tfunction
                                             (Tcons (tptr tvoid)
                                               (Tcons
                                                 (tptr (talignas 2%N (tptr tvoid)))
                                                 Tnil)) tvoid cc_default)))
                        ((Eaddrof (Evar _f_args (tptr tvoid))
                           (tptr (tptr tvoid))) ::
                         (Etempvar _p (tptr (talignas 2%N (tptr tvoid)))) ::
                         nil))
                      Sskip))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint)))))))))
|}.

Definition f_certicoq_gc__funs_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct __474 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct __474 noattr)))
        (Tstruct __474 noattr)) _gc_abort
      (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default)))
    (Ecast
      (Evar _certicoq_gc__abort (Tfunction (Tcons tint Tnil) tvoid
                                  cc_default))
      (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct __474 noattr)))
          (Tstruct __474 noattr)) _gc_block__header_get_ptr
        (tptr (Tfunction (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil)
                (tptr tuint) cc_default)))
      (Ecast
        (Evar _certicoq_block__header_get_ptr (Tfunction
                                                (Tcons
                                                  (tptr (talignas 2%N (tptr tvoid)))
                                                  Tnil) (tptr tuint)
                                                cc_default))
        (tptr (Tfunction (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil)
                (tptr tuint) cc_default))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct __474 noattr)))
            (Tstruct __474 noattr)) _gc_block__copy
          (tptr (Tfunction
                  (Tcons (tptr (talignas 2%N (tptr tvoid)))
                    (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil))
                  (tptr (talignas 2%N (tptr tvoid))) cc_default)))
        (Ecast
          (Evar _certicoq_block__copy (Tfunction
                                        (Tcons
                                          (tptr (talignas 2%N (tptr tvoid)))
                                          (Tcons
                                            (tptr (talignas 2%N (tptr tvoid)))
                                            Tnil))
                                        (tptr (talignas 2%N (tptr tvoid)))
                                        cc_default))
          (tptr (Tfunction
                  (Tcons (tptr (talignas 2%N (tptr tvoid)))
                    (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil))
                  (tptr (talignas 2%N (tptr tvoid))) cc_default))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct __474 noattr)))
              (Tstruct __474 noattr)) _gc_block__ptr_iter
            (tptr (Tfunction
                    (Tcons (tptr (talignas 2%N (tptr tvoid)))
                      (Tcons
                        (tptr (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                    Tnil)) tvoid cc_default))
                        (Tcons (tptr tvoid) Tnil))) tvoid cc_default)))
          (Ecast
            (Evar _certicoq_block__field_ptr_iter (Tfunction
                                                    (Tcons
                                                      (tptr (talignas 2%N (tptr tvoid)))
                                                      (Tcons
                                                        (tptr (Tfunction
                                                                (Tcons
                                                                  (tptr tvoid)
                                                                  (Tcons
                                                                    (tptr (talignas 2%N (tptr tvoid)))
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                                        (Tcons (tptr tvoid)
                                                          Tnil))) tvoid
                                                    cc_default))
            (tptr (Tfunction
                    (Tcons (tptr (talignas 2%N (tptr tvoid)))
                      (Tcons
                        (tptr (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                    Tnil)) tvoid cc_default))
                        (Tcons (tptr tvoid) Tnil))) tvoid cc_default))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct __474 noattr)))
                (Tstruct __474 noattr)) _gc_block__of_base
              (tptr (Tfunction
                      (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil)
                      (tptr (talignas 2%N (tptr tvoid))) cc_default)))
            (Ecast
              (Evar _certicoq_block__of_header (Tfunction
                                                 (Tcons (tptr tuint) Tnil)
                                                 (tptr (talignas 2%N (tptr tvoid)))
                                                 cc_default))
              (tptr (Tfunction
                      (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil)
                      (tptr (talignas 2%N (tptr tvoid))) cc_default))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _out (tptr (Tstruct __474 noattr)))
                  (Tstruct __474 noattr)) _gc_block__size_get
                (tptr (Tfunction (Tcons (tptr tuint) Tnil) tuint cc_default)))
              (Ecast
                (Evar _certicoq_block__size_get (Tfunction
                                                  (Tcons (tptr tuint) Tnil)
                                                  tuint cc_default))
                (tptr (Tfunction (Tcons (tptr tuint) Tnil) tuint cc_default))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct __474 noattr)))
                    (Tstruct __474 noattr)) _gc_rt__num_allocs
                  (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tuint
                          cc_default)))
                (Ecast
                  (Evar _certicoq_gc__num_allocs (Tfunction
                                                   (Tcons (tptr tvoid) Tnil)
                                                   tuint cc_default))
                  (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tuint
                          cc_default))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _out (tptr (Tstruct __474 noattr)))
                      (Tstruct __474 noattr)) _gc_rt__resume
                    (tptr (Tfunction
                            (Tcons (tptr tvoid)
                              (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                  Tnil))) tvoid cc_default)))
                  (Ecast
                    (Evar _certicoq_gc__resume (Tfunction
                                                 (Tcons (tptr tvoid)
                                                   (Tcons
                                                     (tptr (talignas 2%N (tptr tvoid)))
                                                     (Tcons
                                                       (tptr (talignas 2%N (tptr tvoid)))
                                                       Tnil))) tvoid
                                                 cc_default))
                    (tptr (Tfunction
                            (Tcons (tptr tvoid)
                              (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                  Tnil))) tvoid cc_default))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _out (tptr (Tstruct __474 noattr)))
                      (Tstruct __474 noattr)) _gc_rt__root_ptr_iter
                    (tptr (Tfunction
                            (Tcons (tptr tvoid)
                              (Tcons
                                (tptr (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons
                                            (tptr (talignas 2%N (tptr tvoid)))
                                            Tnil)) tvoid cc_default))
                                (Tcons (tptr tvoid) Tnil))) tvoid cc_default)))
                  (Ecast
                    (Evar _certicoq_gc__root_ptr_iter (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          (Tcons
                                                            (tptr (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr (talignas 2%N (tptr tvoid)))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil))) tvoid
                                                        cc_default))
                    (tptr (Tfunction
                            (Tcons (tptr tvoid)
                              (Tcons
                                (tptr (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons
                                            (tptr (talignas 2%N (tptr tvoid)))
                                            Tnil)) tvoid cc_default))
                                (Tcons (tptr tvoid) Tnil))) tvoid cc_default))))))))))))
|}.

Definition f_certicoq_gc__make_tinfo := {|
  fn_return := (tptr (Tstruct _thread_info noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) ::
               (_tinfo, (tptr (Tstruct _thread_info noattr))) ::
               (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _heap noattr))) ::
               (_t'4, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _create_heap (Tfunction
                           (Tcons
                             (tptr (Tfunction (Tcons tint Tnil) tvoid
                                     cc_default)) Tnil)
                           (tptr (Tstruct _heap noattr)) cc_default))
      ((Ecast
         (Evar _certicoq_gc__abort (Tfunction (Tcons tint Tnil) tvoid
                                     cc_default))
         (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))) :: nil))
    (Sset _h (Etempvar _t'1 (tptr (Tstruct _heap noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _thread_info noattr) tuint) :: nil))
      (Sset _tinfo
        (Ecast (Etempvar _t'2 (tptr tvoid))
          (tptr (Tstruct _thread_info noattr)))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                     tint)
        (Scall None
          (Evar _certicoq_gc__abort (Tfunction (Tcons tint Tnil) tvoid
                                      cc_default))
          ((Econst_int (Int.repr (-6)) tint) :: nil))
        Sskip)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _heap
            (tptr (Tstruct _heap noattr)))
          (Etempvar _h (tptr (Tstruct _heap noattr))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                        (Tstruct _heap noattr)) _spaces
                      (tarray (Tstruct _space noattr) 12))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
                _start (tptr (talignas 2%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc
                (tptr (talignas 2%N (tptr tvoid))))
              (Etempvar _t'4 (tptr (talignas 2%N (tptr tvoid))))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                          (Tstruct _heap noattr)) _spaces
                        (tarray (Tstruct _space noattr) 12))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _limit
                  (tptr (talignas 2%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _limit
                  (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _t'3 (tptr (talignas 2%N (tptr tvoid))))))
            (Sreturn (Some (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))))))))))
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

Definition f_certicoq_gc__remember := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) ::
                (_p_cell, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr (Tstruct _heap noattr))) ::
               (_t'2, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'1, (tptr (Tstruct _heap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
          (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
    (Scall None
      (Evar _remember (Tfunction
                        (Tcons (tptr (Tstruct _heap noattr))
                          (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil))
                        tvoid cc_default))
      ((Etempvar _t'3 (tptr (Tstruct _heap noattr))) ::
       (Etempvar _p_cell (tptr (talignas 2%N (tptr tvoid)))) :: nil)))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
          (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _t'1 (tptr (Tstruct _heap noattr)))
                  (Tstruct _heap noattr)) _spaces
                (tarray (Tstruct _space noattr) 12))
              (Econst_int (Int.repr 0) tint) (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _limit
          (tptr (talignas 2%N (tptr tvoid)))))
      (Sassign
        (Efield
          (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _limit
          (tptr (talignas 2%N (tptr tvoid))))
        (Etempvar _t'2 (tptr (talignas 2%N (tptr tvoid))))))))
|}.

Definition f_certicoq_gc__cell_modify := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) ::
                (_p_cell, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_p_val, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef (Etempvar _p_cell (tptr (talignas 2%N (tptr tvoid))))
      (talignas 2%N (tptr tvoid)))
    (Etempvar _p_val (talignas 2%N (tptr tvoid))))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _int_or_ptr__is_int (Tfunction
                                  (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                                  tint cc_default))
      ((Etempvar _p_val (talignas 2%N (tptr tvoid))) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Scall None
        (Evar _certicoq_gc__remember (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _thread_info noattr))
                                         (Tcons
                                           (tptr (talignas 2%N (tptr tvoid)))
                                           Tnil)) tvoid cc_default))
        ((Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
         (Etempvar _p_cell (tptr (talignas 2%N (tptr tvoid)))) :: nil))
      Sskip)))
|}.

Definition f_certicoq_gc__garbage_collect := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := ((_rt, (Tstruct __497 noattr)) ::
              (_gc_funs, (Tstruct __474 noattr)) :: nil);
  fn_temps := ((_t'1, (tptr (Tstruct _heap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _rt (Tstruct __497 noattr)) _fi (tptr tuint))
    (Etempvar _fi (tptr tuint)))
  (Ssequence
    (Sassign
      (Efield (Evar _rt (Tstruct __497 noattr)) _ti
        (tptr (Tstruct _thread_info noattr)))
      (Etempvar _ti (tptr (Tstruct _thread_info noattr))))
    (Ssequence
      (Scall None
        (Evar _certicoq_gc__funs_init (Tfunction
                                        (Tcons (tptr (Tstruct __474 noattr))
                                          Tnil) tvoid cc_default))
        ((Eaddrof (Evar _gc_funs (Tstruct __474 noattr))
           (tptr (Tstruct __474 noattr))) :: nil))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
              (Tstruct _thread_info noattr)) _heap
            (tptr (Tstruct _heap noattr))))
        (Scall None
          (Evar _garbage_collect (Tfunction
                                   (Tcons (tptr (Tstruct __474 noattr))
                                     (Tcons (tptr tvoid)
                                       (Tcons (tptr (Tstruct _heap noattr))
                                         Tnil))) tvoid cc_default))
          ((Eaddrof (Evar _gc_funs (Tstruct __474 noattr))
             (tptr (Tstruct __474 noattr))) ::
           (Eaddrof (Evar _rt (Tstruct __497 noattr))
             (tptr (Tstruct __497 noattr))) ::
           (Etempvar _t'1 (tptr (Tstruct _heap noattr))) :: nil))))))
|}.

Definition composites : list composite_definition :=
(Composite __474 Struct
   ((_gc_abort, (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))) ::
    (_gc_block__header_get_ptr,
     (tptr (Tfunction (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil)
             (tptr tuint) cc_default))) ::
    (_gc_block__copy,
     (tptr (Tfunction
             (Tcons (tptr (talignas 2%N (tptr tvoid)))
               (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil))
             (tptr (talignas 2%N (tptr tvoid))) cc_default))) ::
    (_gc_block__ptr_iter,
     (tptr (Tfunction
             (Tcons (tptr (talignas 2%N (tptr tvoid)))
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil))
                         tvoid cc_default)) (Tcons (tptr tvoid) Tnil))) tvoid
             cc_default))) ::
    (_gc_block__of_base,
     (tptr (Tfunction (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil)
             (tptr (talignas 2%N (tptr tvoid))) cc_default))) ::
    (_gc_block__size_get,
     (tptr (Tfunction (Tcons (tptr tuint) Tnil) tuint cc_default))) ::
    (_gc_rt__num_allocs,
     (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tuint cc_default))) ::
    (_gc_rt__resume,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons (tptr (talignas 2%N (tptr tvoid)))
                 (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil))) tvoid
             cc_default))) ::
    (_gc_rt__root_ptr_iter,
     (tptr (Tfunction
             (Tcons (tptr tvoid)
               (Tcons
                 (tptr (Tfunction
                         (Tcons (tptr tvoid)
                           (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil))
                         tvoid cc_default)) (Tcons (tptr tvoid) Tnil))) tvoid
             cc_default))) :: (_odata, (tptr tvoid)) :: nil)
   noattr ::
 Composite _space Struct
   ((_start, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_next, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_end, (tptr (talignas 2%N (tptr tvoid)))) :: nil)
   noattr ::
 Composite _heap Struct
   ((_spaces, (tarray (Tstruct _space noattr) 12)) :: nil)
   noattr ::
 Composite _thread_info Struct
   ((_alloc, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_heap, (tptr (Tstruct _heap noattr))) ::
    (_args, (tarray (talignas 2%N (tptr tvoid)) 1024)) :: nil)
   noattr ::
 Composite __497 Struct
   ((_fi, (tptr tuint)) :: (_ti, (tptr (Tstruct _thread_info noattr))) ::
    nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
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
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
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
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
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
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_int_or_ptr__is_int,
   Gfun(External (EF_external "int_or_ptr__is_int"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (talignas 2%N (tptr tvoid)) Tnil) tint cc_default)) ::
 (_certicoq_block__of_header,
   Gfun(External (EF_external "certicoq_block__of_header"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) (tptr (talignas 2%N (tptr tvoid)))
     cc_default)) ::
 (_certicoq_block__copy,
   Gfun(External (EF_external "certicoq_block__copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (talignas 2%N (tptr tvoid)))
       (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil))
     (tptr (talignas 2%N (tptr tvoid))) cc_default)) ::
 (_certicoq_block__header_get_ptr,
   Gfun(External (EF_external "certicoq_block__header_get_ptr"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil) (tptr tuint)
     cc_default)) ::
 (_certicoq_block__size_get,
   Gfun(External (EF_external "certicoq_block__size_get"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (_certicoq_block__field_ptr_iter,
   Gfun(External (EF_external "certicoq_block__field_ptr_iter"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (talignas 2%N (tptr tvoid)))
       (Tcons
         (tptr (Tfunction
                 (Tcons (tptr tvoid)
                   (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil)) tvoid
                 cc_default)) (Tcons (tptr tvoid) Tnil))) tvoid cc_default)) ::
 (_create_heap,
   Gfun(External (EF_external "create_heap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default)) Tnil)
     (tptr (Tstruct _heap noattr)) cc_default)) ::
 (_free_heap,
   Gfun(External (EF_external "free_heap"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _heap noattr)) Tnil) tvoid cc_default)) ::
 (_reset_heap,
   Gfun(External (EF_external "reset_heap"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _heap noattr)) Tnil) tvoid cc_default)) ::
 (_remember,
   Gfun(External (EF_external "remember"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _heap noattr))
       (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil)) tvoid cc_default)) ::
 (_garbage_collect,
   Gfun(External (EF_external "garbage_collect"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct __474 noattr))
       (Tcons (tptr tvoid) (Tcons (tptr (Tstruct _heap noattr)) Tnil))) tvoid
     cc_default)) ::
 (_certicoq_gc__abort, Gfun(Internal f_certicoq_gc__abort)) ::
 (_certicoq_gc__num_allocs, Gfun(Internal f_certicoq_gc__num_allocs)) ::
 (_certicoq_gc__resume, Gfun(Internal f_certicoq_gc__resume)) ::
 (_certicoq_gc__root_ptr_iter, Gfun(Internal f_certicoq_gc__root_ptr_iter)) ::
 (_certicoq_gc__funs_init, Gfun(Internal f_certicoq_gc__funs_init)) ::
 (_certicoq_gc__make_tinfo, Gfun(Internal f_certicoq_gc__make_tinfo)) ::
 (_certicoq_gc__free_heap, Gfun(Internal f_certicoq_gc__free_heap)) ::
 (_certicoq_gc__reset_heap, Gfun(Internal f_certicoq_gc__reset_heap)) ::
 (_certicoq_gc__remember, Gfun(Internal f_certicoq_gc__remember)) ::
 (_certicoq_gc__cell_modify, Gfun(Internal f_certicoq_gc__cell_modify)) ::
 (_certicoq_gc__garbage_collect, Gfun(Internal f_certicoq_gc__garbage_collect)) ::
 nil).

Definition public_idents : list ident :=
(_certicoq_gc__garbage_collect :: _certicoq_gc__cell_modify ::
 _certicoq_gc__remember :: _certicoq_gc__reset_heap ::
 _certicoq_gc__free_heap :: _certicoq_gc__make_tinfo ::
 _certicoq_gc__funs_init :: _certicoq_gc__root_ptr_iter ::
 _certicoq_gc__resume :: _certicoq_gc__num_allocs :: _certicoq_gc__abort ::
 _garbage_collect :: _remember :: _reset_heap :: _free_heap ::
 _create_heap :: _certicoq_block__field_ptr_iter ::
 _certicoq_block__size_get :: _certicoq_block__header_get_ptr ::
 _certicoq_block__copy :: _certicoq_block__of_header ::
 _int_or_ptr__is_int :: _exit :: _malloc :: ___builtin_debug ::
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


(*\nInput hashes (sha256):\n\n0ba92d6dd1cf086392df1f6491e0f3e33aad2562966a383abf21c10690a2675b  src/c/include/coq-vsu-gc/src/certicoq_gc.c
58b276737fd53c1ba1e9f79d19ff8c53c852c39ccd104fc18bd55e2746c65290  src/c/include/coq-vsu-gc/certicoq_gc.h
fbae3a2ccb582c5d63744223a73f45bea50c22865538b0bb1a7171f185214b13  src/c/include/coq-vsu-gc/gc.h
a9b18c1959df2cb5404306021e5256eb25c78c20ef9ec326a1cac75cea375fe7  src/c/include/coq-vsu-gc/mem.h\n*)
