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
  Definition source_file := "src/c/include/coq-vsu-gc/src/gc.c".
  Definition normalized := true.
End Info.

Definition _Is_block : ident := $"Is_block".
Definition _Is_from : ident := $"Is_from".
Definition _MAX_SPACE_SIZE : ident := $"MAX_SPACE_SIZE".
Definition __367 : ident := $"_367".
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
Definition _block : ident := $"block".
Definition _cell_modify : ident := $"cell_modify".
Definition _certicoq_block__copy : ident := $"certicoq_block__copy".
Definition _certicoq_block__field_ptr_iter : ident := $"certicoq_block__field_ptr_iter".
Definition _certicoq_block__header_get_ptr : ident := $"certicoq_block__header_get_ptr".
Definition _certicoq_block__of_header : ident := $"certicoq_block__of_header".
Definition _certicoq_block__size_get : ident := $"certicoq_block__size_get".
Definition _create_heap : ident := $"create_heap".
Definition _create_space : ident := $"create_space".
Definition _depth : ident := $"depth".
Definition _do_generation : ident := $"do_generation".
Definition _do_scan : ident := $"do_scan".
Definition _end : ident := $"end".
Definition _f_args : ident := $"f_args".
Definition _f_args__1 : ident := $"f_args__1".
Definition _fi : ident := $"fi".
Definition _forward : ident := $"forward".
Definition _forward_remset : ident := $"forward_remset".
Definition _forward_roots : ident := $"forward_roots".
Definition _free : ident := $"free".
Definition _free_heap : ident := $"free_heap".
Definition _from : ident := $"from".
Definition _from_limit : ident := $"from_limit".
Definition _from_start : ident := $"from_start".
Definition _garbage_collect : ident := $"garbage_collect".
Definition _gc_abort : ident := $"gc_abort".
Definition _h : ident := $"h".
Definition _has_been_forwarded : ident := $"has_been_forwarded".
Definition _hd : ident := $"hd".
Definition _heap : ident := $"heap".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _int_or_ptr__is_int : ident := $"int_or_ptr__is_int".
Definition _int_or_ptr__of_ptr : ident := $"int_or_ptr__of_ptr".
Definition _int_or_ptr__to_ptr : ident := $"int_or_ptr__to_ptr".
Definition _limit : ident := $"limit".
Definition _lo : ident := $"lo".
Definition _main : ident := $"main".
Definition _make_tinfo : ident := $"make_tinfo".
Definition _malloc : ident := $"malloc".
Definition _mark_as_forwarded : ident := $"mark_as_forwarded".
Definition _n : ident := $"n".
Definition _new : ident := $"new".
Definition _new_addr_from_forwarded : ident := $"new_addr_from_forwarded".
Definition _next : ident := $"next".
Definition _num_allocs : ident := $"num_allocs".
Definition _old : ident := $"old".
Definition _p : ident := $"p".
Definition _p_cell : ident := $"p_cell".
Definition _p_val : ident := $"p_val".
Definition _q : ident := $"q".
Definition _reset_heap : ident := $"reset_heap".
Definition _resume : ident := $"resume".
Definition _roots : ident := $"roots".
Definition _s : ident := $"s".
Definition _scan : ident := $"scan".
Definition _space : ident := $"space".
Definition _spaces : ident := $"spaces".
Definition _start : ident := $"start".
Definition _sz : ident := $"sz".
Definition _thread_info : ident := $"thread_info".
Definition _ti : ident := $"ti".
Definition _tinfo : ident := $"tinfo".
Definition _to : ident := $"to".
Definition _v : ident := $"v".
Definition _va : ident := $"va".
Definition _w : ident := $"w".
Definition _x : ident := $"x".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v_MAX_SPACE_SIZE := {|
  gvar_info := tulong;
  gvar_init := (Init_int64 (Int64.repr 1099511627776) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_Is_block := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _int_or_ptr__is_int (Tfunction
                                (Tcons (talignas 3%N (tptr tvoid)) Tnil) tint
                                cc_default))
    ((Etempvar _x (talignas 3%N (tptr tvoid))) :: nil))
  (Sreturn (Some (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 0) tint) tint))))
|}.

Definition f_Is_from := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_v, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole
                 (Etempvar _from_start (tptr (talignas 3%N (tptr tvoid))))
                 (Etempvar _v (tptr (talignas 3%N (tptr tvoid)))) tint)
    (Sset _t'1
      (Ecast
        (Ebinop Olt (Etempvar _v (tptr (talignas 3%N (tptr tvoid))))
          (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))) tint)
        tbool))
    (Sset _t'1 (Econst_int (Int.repr 0) tint)))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_has_been_forwarded := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Etempvar _v (tptr (talignas 3%N (tptr tvoid))))
        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
        (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid))))
  (Sreturn (Some (Ebinop Oeq (Etempvar _t'1 (talignas 3%N (tptr tvoid)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))))
|}.

Definition f_new_addr_from_forwarded := {|
  fn_return := (talignas 3%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Ederef
      (Ebinop Oadd (Etempvar _v (tptr (talignas 3%N (tptr tvoid))))
        (Econst_int (Int.repr 0) tint) (tptr (talignas 3%N (tptr tvoid))))
      (talignas 3%N (tptr tvoid))))
  (Sreturn (Some (Etempvar _t'1 (talignas 3%N (tptr tvoid))))))
|}.

Definition f_mark_as_forwarded := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_old, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_new, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (talignas 3%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar _old (tptr (talignas 3%N (tptr tvoid))))
        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
        (tptr (talignas 3%N (tptr tvoid)))) (talignas 3%N (tptr tvoid)))
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _int_or_ptr__of_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                  (talignas 3%N (tptr tvoid)) cc_default))
      ((Etempvar _new (tptr (talignas 3%N (tptr tvoid)))) :: nil))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _old (tptr (talignas 3%N (tptr tvoid))))
          (Econst_int (Int.repr 0) tint) (tptr (talignas 3%N (tptr tvoid))))
        (talignas 3%N (tptr tvoid)))
      (Etempvar _t'1 (talignas 3%N (tptr tvoid))))))
|}.

Definition f_forward := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_f_args, (tptr tvoid)) ::
                (_p, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_vars := ((_f_args__1, (Tstruct __367 noattr)) :: nil);
  fn_temps := ((_args, (tptr (Tstruct __367 noattr))) ::
               (_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_next, (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
               (_depth, tint) :: (_v, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_va, (talignas 3%N (tptr tvoid))) :: (_hd, (tptr tulong)) ::
               (_sz, tulong) :: (_new, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, (talignas 3%N (tptr tvoid))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, tulong) :: (_t'3, (tptr tulong)) ::
               (_t'2, (talignas 3%N (tptr tvoid))) :: (_t'1, (tptr tvoid)) ::
               (_t'11, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'10, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _args
    (Ecast (Etempvar _f_args (tptr tvoid)) (tptr (Tstruct __367 noattr))))
  (Ssequence
    (Sset _from_start
      (Efield
        (Ederef (Etempvar _args (tptr (Tstruct __367 noattr)))
          (Tstruct __367 noattr)) _from_start
        (tptr (talignas 3%N (tptr tvoid)))))
    (Ssequence
      (Sset _from_limit
        (Efield
          (Ederef (Etempvar _args (tptr (Tstruct __367 noattr)))
            (Tstruct __367 noattr)) _from_limit
          (tptr (talignas 3%N (tptr tvoid)))))
      (Ssequence
        (Sset _next
          (Efield
            (Ederef (Etempvar _args (tptr (Tstruct __367 noattr)))
              (Tstruct __367 noattr)) _next
            (tptr (tptr (talignas 3%N (tptr tvoid))))))
        (Ssequence
          (Sset _depth
            (Efield
              (Ederef (Etempvar _args (tptr (Tstruct __367 noattr)))
                (Tstruct __367 noattr)) _depth tint))
          (Ssequence
            (Sset _va
              (Ederef (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                (talignas 3%N (tptr tvoid))))
            (Ssequence
              (Scall (Some _t'9)
                (Evar _Is_block (Tfunction
                                  (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                                  tint cc_default))
                ((Etempvar _va (talignas 3%N (tptr tvoid))) :: nil))
              (Sifthenelse (Etempvar _t'9 tint)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'1)
                      (Evar _int_or_ptr__to_ptr (Tfunction
                                                  (Tcons
                                                    (talignas 3%N (tptr tvoid))
                                                    Tnil) (tptr tvoid)
                                                  cc_default))
                      ((Etempvar _va (talignas 3%N (tptr tvoid))) :: nil))
                    (Sset _v
                      (Ecast (Etempvar _t'1 (tptr tvoid))
                        (tptr (talignas 3%N (tptr tvoid))))))
                  (Ssequence
                    (Scall (Some _t'8)
                      (Evar _Is_from (Tfunction
                                       (Tcons
                                         (tptr (talignas 3%N (tptr tvoid)))
                                         (Tcons
                                           (tptr (talignas 3%N (tptr tvoid)))
                                           (Tcons
                                             (tptr (talignas 3%N (tptr tvoid)))
                                             Tnil))) tint cc_default))
                      ((Etempvar _from_start (tptr (talignas 3%N (tptr tvoid)))) ::
                       (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))) ::
                       (Etempvar _v (tptr (talignas 3%N (tptr tvoid)))) ::
                       nil))
                    (Sifthenelse (Etempvar _t'8 tint)
                      (Ssequence
                        (Scall (Some _t'7)
                          (Evar _has_been_forwarded (Tfunction
                                                      (Tcons
                                                        (tptr (talignas 3%N (tptr tvoid)))
                                                        Tnil) tint
                                                      cc_default))
                          ((Etempvar _v (tptr (talignas 3%N (tptr tvoid)))) ::
                           nil))
                        (Sifthenelse (Etempvar _t'7 tint)
                          (Ssequence
                            (Scall (Some _t'2)
                              (Evar _new_addr_from_forwarded (Tfunction
                                                               (Tcons
                                                                 (tptr (talignas 3%N (tptr tvoid)))
                                                                 Tnil)
                                                               (talignas 3%N (tptr tvoid))
                                                               cc_default))
                              ((Etempvar _v (tptr (talignas 3%N (tptr tvoid)))) ::
                               nil))
                            (Sassign
                              (Ederef
                                (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                                (talignas 3%N (tptr tvoid)))
                              (Etempvar _t'2 (talignas 3%N (tptr tvoid)))))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'3)
                                (Evar _certicoq_block__header_get_ptr 
                                (Tfunction
                                  (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                    Tnil) (tptr tulong) cc_default))
                                ((Etempvar _v (tptr (talignas 3%N (tptr tvoid)))) ::
                                 nil))
                              (Sset _hd (Etempvar _t'3 (tptr tulong))))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'4)
                                  (Evar _certicoq_block__size_get (Tfunction
                                                                    (Tcons
                                                                    (tptr tulong)
                                                                    Tnil)
                                                                    tulong
                                                                    cc_default))
                                  ((Etempvar _hd (tptr tulong)) :: nil))
                                (Sset _sz (Etempvar _t'4 tulong)))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'11
                                      (Ederef
                                        (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid)))))
                                        (tptr (talignas 3%N (tptr tvoid)))))
                                    (Scall (Some _t'5)
                                      (Evar _certicoq_block__copy (Tfunction
                                                                    (Tcons
                                                                    (tptr (talignas 3%N (tptr tvoid)))
                                                                    (Tcons
                                                                    (tptr (talignas 3%N (tptr tvoid)))
                                                                    Tnil))
                                                                    (tptr (talignas 3%N (tptr tvoid)))
                                                                    cc_default))
                                      ((Etempvar _t'11 (tptr (talignas 3%N (tptr tvoid)))) ::
                                       (Etempvar _v (tptr (talignas 3%N (tptr tvoid)))) ::
                                       nil)))
                                  (Sset _new
                                    (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid))))))
                                (Ssequence
                                  (Scall None
                                    (Evar _mark_as_forwarded (Tfunction
                                                               (Tcons
                                                                 (tptr (talignas 3%N (tptr tvoid)))
                                                                 (Tcons
                                                                   (tptr (talignas 3%N (tptr tvoid)))
                                                                   Tnil))
                                                               tvoid
                                                               cc_default))
                                    ((Etempvar _v (tptr (talignas 3%N (tptr tvoid)))) ::
                                     (Etempvar _new (tptr (talignas 3%N (tptr tvoid)))) ::
                                     nil))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'10
                                        (Ederef
                                          (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid)))))
                                          (tptr (talignas 3%N (tptr tvoid)))))
                                      (Sassign
                                        (Ederef
                                          (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid)))))
                                          (tptr (talignas 3%N (tptr tvoid))))
                                        (Ebinop Oadd
                                          (Etempvar _t'10 (tptr (talignas 3%N (tptr tvoid))))
                                          (Etempvar _sz tulong)
                                          (tptr (talignas 3%N (tptr tvoid))))))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'6)
                                          (Evar _new_addr_from_forwarded 
                                          (Tfunction
                                            (Tcons
                                              (tptr (talignas 3%N (tptr tvoid)))
                                              Tnil)
                                            (talignas 3%N (tptr tvoid))
                                            cc_default))
                                          ((Etempvar _v (tptr (talignas 3%N (tptr tvoid)))) ::
                                           nil))
                                        (Sassign
                                          (Ederef
                                            (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                                            (talignas 3%N (tptr tvoid)))
                                          (Etempvar _t'6 (talignas 3%N (tptr tvoid)))))
                                      (Sifthenelse (Ebinop Ogt
                                                     (Etempvar _depth tint)
                                                     (Econst_int (Int.repr 0) tint)
                                                     tint)
                                        (Ssequence
                                          (Sassign
                                            (Efield
                                              (Evar _f_args__1 (Tstruct __367 noattr))
                                              _from_start
                                              (tptr (talignas 3%N (tptr tvoid))))
                                            (Etempvar _from_start (tptr (talignas 3%N (tptr tvoid)))))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Evar _f_args__1 (Tstruct __367 noattr))
                                                _from_limit
                                                (tptr (talignas 3%N (tptr tvoid))))
                                              (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Evar _f_args__1 (Tstruct __367 noattr))
                                                  _next
                                                  (tptr (tptr (talignas 3%N (tptr tvoid)))))
                                                (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid))))))
                                              (Ssequence
                                                (Sassign
                                                  (Efield
                                                    (Evar _f_args__1 (Tstruct __367 noattr))
                                                    _depth tint)
                                                  (Ebinop Osub
                                                    (Etempvar _depth tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint))
                                                (Scall None
                                                  (Evar _certicoq_block__field_ptr_iter 
                                                  (Tfunction
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
                                                    cc_default))
                                                  ((Etempvar _new (tptr (talignas 3%N (tptr tvoid)))) ::
                                                   (Evar _forward (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr (talignas 3%N (tptr tvoid)))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default)) ::
                                                   (Eaddrof
                                                     (Evar _f_args__1 (Tstruct __367 noattr))
                                                     (tptr (Tstruct __367 noattr))) ::
                                                   nil))))))
                                        Sskip)))))))))
                      Sskip)))
                Sskip))))))))
|}.

Definition f_forward_roots := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
                (_fi, (tptr tulong)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := ((_f_args, (Tstruct __367 noattr)) :: nil);
  fn_temps := ((_i, tulong) :: (_n, tulong) :: (_roots, (tptr tulong)) ::
               (_args, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _n
    (Ederef
      (Ebinop Oadd (Etempvar _fi (tptr tulong))
        (Econst_int (Int.repr 1) tint) (tptr tulong)) tulong))
  (Ssequence
    (Sset _roots
      (Ebinop Oadd (Etempvar _fi (tptr tulong))
        (Econst_int (Int.repr 2) tint) (tptr tulong)))
    (Ssequence
      (Sset _args
        (Efield
          (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _args
          (tarray (talignas 3%N (tptr tvoid)) 1024)))
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                           (Etempvar _n tulong) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sassign
                (Efield (Evar _f_args (Tstruct __367 noattr)) _from_start
                  (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _from_start (tptr (talignas 3%N (tptr tvoid)))))
              (Ssequence
                (Sassign
                  (Efield (Evar _f_args (Tstruct __367 noattr)) _from_limit
                    (tptr (talignas 3%N (tptr tvoid))))
                  (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))))
                (Ssequence
                  (Sassign
                    (Efield (Evar _f_args (Tstruct __367 noattr)) _next
                      (tptr (tptr (talignas 3%N (tptr tvoid)))))
                    (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid))))))
                  (Ssequence
                    (Sassign
                      (Efield (Evar _f_args (Tstruct __367 noattr)) _depth
                        tint) (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sset _t'1
                        (Ederef
                          (Ebinop Oadd (Etempvar _roots (tptr tulong))
                            (Etempvar _i tulong) (tptr tulong)) tulong))
                      (Scall None
                        (Evar _forward (Tfunction
                                         (Tcons (tptr tvoid)
                                           (Tcons
                                             (tptr (talignas 3%N (tptr tvoid)))
                                             Tnil)) tvoid cc_default))
                        ((Eaddrof (Evar _f_args (Tstruct __367 noattr))
                           (tptr (Tstruct __367 noattr))) ::
                         (Ebinop Oadd
                           (Etempvar _args (tptr (talignas 3%N (tptr tvoid))))
                           (Etempvar _t'1 tulong)
                           (tptr (talignas 3%N (tptr tvoid)))) :: nil))))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong)))))))
|}.

Definition f_forward_remset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from, (tptr (Tstruct _space noattr))) ::
                (_to, (tptr (Tstruct _space noattr))) ::
                (_next, (tptr (tptr (talignas 3%N (tptr tvoid))))) :: nil);
  fn_vars := ((_f_args, (Tstruct __367 noattr)) :: nil);
  fn_temps := ((_q, (tptr (talignas 3%N (tptr tvoid)))) :: (_t'2, tint) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'11, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'10, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'9, (talignas 3%N (tptr tvoid))) ::
               (_t'8, (talignas 3%N (tptr tvoid))) ::
               (_t'7, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'6, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (talignas 3%N (tptr tvoid))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _q
    (Efield
      (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
        (Tstruct _space noattr)) _limit (tptr (talignas 3%N (tptr tvoid)))))
  (Sloop
    (Ssequence
      (Ssequence
        (Sset _t'11
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _end
            (tptr (talignas 3%N (tptr tvoid)))))
        (Sifthenelse (Ebinop One
                       (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
                       (Etempvar _t'11 (tptr (talignas 3%N (tptr tvoid))))
                       tint)
          Sskip
          Sbreak))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _start
                (tptr (talignas 3%N (tptr tvoid)))))
            (Ssequence
              (Sset _t'8
                (Ederef (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
                  (talignas 3%N (tptr tvoid))))
              (Sifthenelse (Ebinop Ole
                             (Etempvar _t'7 (tptr (talignas 3%N (tptr tvoid))))
                             (Ecast
                               (Etempvar _t'8 (talignas 3%N (tptr tvoid)))
                               (tptr (talignas 3%N (tptr tvoid)))) tint)
                (Ssequence
                  (Sset _t'9
                    (Ederef (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
                      (talignas 3%N (tptr tvoid))))
                  (Ssequence
                    (Sset _t'10
                      (Efield
                        (Ederef
                          (Etempvar _from (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _limit
                        (tptr (talignas 3%N (tptr tvoid)))))
                    (Sset _t'2
                      (Ecast
                        (Ebinop Olt
                          (Ecast (Etempvar _t'9 (talignas 3%N (tptr tvoid)))
                            (tptr (talignas 3%N (tptr tvoid))))
                          (Etempvar _t'10 (tptr (talignas 3%N (tptr tvoid))))
                          tint) tbool))))
                (Sset _t'2 (Econst_int (Int.repr 0) tint)))))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _start
                    (tptr (talignas 3%N (tptr tvoid)))))
                (Sassign
                  (Efield (Evar _f_args (Tstruct __367 noattr)) _from_start
                    (tptr (talignas 3%N (tptr tvoid))))
                  (Etempvar _t'6 (tptr (talignas 3%N (tptr tvoid))))))
              (Ssequence
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _limit
                      (tptr (talignas 3%N (tptr tvoid)))))
                  (Sassign
                    (Efield (Evar _f_args (Tstruct __367 noattr)) _from_limit
                      (tptr (talignas 3%N (tptr tvoid))))
                    (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid))))))
                (Ssequence
                  (Sassign
                    (Efield (Evar _f_args (Tstruct __367 noattr)) _next
                      (tptr (tptr (talignas 3%N (tptr tvoid)))))
                    (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid))))))
                  (Ssequence
                    (Sassign
                      (Efield (Evar _f_args (Tstruct __367 noattr)) _depth
                        tint) (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Ssequence
                        (Sset _t'4
                          (Ederef
                            (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
                            (talignas 3%N (tptr tvoid))))
                        (Scall None
                          (Evar _forward (Tfunction
                                           (Tcons (tptr tvoid)
                                             (Tcons
                                               (tptr (talignas 3%N (tptr tvoid)))
                                               Tnil)) tvoid cc_default))
                          ((Eaddrof (Evar _f_args (Tstruct __367 noattr))
                             (tptr (Tstruct __367 noattr))) ::
                           (Ecast (Etempvar _t'4 (talignas 3%N (tptr tvoid)))
                             (tptr (talignas 3%N (tptr tvoid)))) :: nil)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'3
                              (Efield
                                (Ederef
                                  (Etempvar _to (tptr (Tstruct _space noattr)))
                                  (Tstruct _space noattr)) _limit
                                (tptr (talignas 3%N (tptr tvoid)))))
                            (Sset _t'1
                              (Ecast
                                (Ebinop Osub
                                  (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr (talignas 3%N (tptr tvoid))))
                                (tptr (talignas 3%N (tptr tvoid))))))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _to (tptr (Tstruct _space noattr)))
                                (Tstruct _space noattr)) _limit
                              (tptr (talignas 3%N (tptr tvoid))))
                            (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))))
                        (Sassign
                          (Ederef
                            (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
                            (talignas 3%N (tptr tvoid)))
                          (Ecast
                            (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
                            (talignas 3%N (tptr tvoid))))))))))
            Sskip))
        (Sset _q
          (Ebinop Oadd (Etempvar _q (tptr (talignas 3%N (tptr tvoid))))
            (Econst_int (Int.repr 1) tint)
            (tptr (talignas 3%N (tptr tvoid)))))))
    Sskip))
|}.

Definition f_do_scan := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_scan, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 3%N (tptr tvoid))))) :: nil);
  fn_vars := ((_f_args, (Tstruct __367 noattr)) :: nil);
  fn_temps := ((_s, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_hd, (tptr tulong)) ::
               (_block, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_sz, tulong) :: (_t'2, tulong) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Etempvar _scan (tptr (talignas 3%N (tptr tvoid)))))
  (Sloop
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Ederef (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid)))))
            (tptr (talignas 3%N (tptr tvoid)))))
        (Sifthenelse (Ebinop Olt
                       (Etempvar _s (tptr (talignas 3%N (tptr tvoid))))
                       (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                       tint)
          Sskip
          Sbreak))
      (Ssequence
        (Sset _hd
          (Ecast (Etempvar _s (tptr (talignas 3%N (tptr tvoid))))
            (tptr tulong)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _certicoq_block__of_header (Tfunction
                                                 (Tcons (tptr tulong) Tnil)
                                                 (tptr (talignas 3%N (tptr tvoid)))
                                                 cc_default))
              ((Etempvar _hd (tptr tulong)) :: nil))
            (Sset _block (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _certicoq_block__size_get (Tfunction
                                                  (Tcons (tptr tulong) Tnil)
                                                  tulong cc_default))
                ((Etempvar _hd (tptr tulong)) :: nil))
              (Sset _sz (Etempvar _t'2 tulong)))
            (Ssequence
              (Sassign
                (Efield (Evar _f_args (Tstruct __367 noattr)) _from_start
                  (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _from_start (tptr (talignas 3%N (tptr tvoid)))))
              (Ssequence
                (Sassign
                  (Efield (Evar _f_args (Tstruct __367 noattr)) _from_limit
                    (tptr (talignas 3%N (tptr tvoid))))
                  (Etempvar _from_limit (tptr (talignas 3%N (tptr tvoid)))))
                (Ssequence
                  (Sassign
                    (Efield (Evar _f_args (Tstruct __367 noattr)) _next
                      (tptr (tptr (talignas 3%N (tptr tvoid)))))
                    (Etempvar _next (tptr (tptr (talignas 3%N (tptr tvoid))))))
                  (Ssequence
                    (Sassign
                      (Efield (Evar _f_args (Tstruct __367 noattr)) _depth
                        tint) (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Scall None
                        (Evar _certicoq_block__field_ptr_iter (Tfunction
                                                                (Tcons
                                                                  (tptr (talignas 3%N (tptr tvoid)))
                                                                  (Tcons
                                                                    (tptr 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    (Tcons
                                                                    (tptr (talignas 3%N (tptr tvoid)))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    (Tcons
                                                                    (tptr tvoid)
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                        ((Etempvar _block (tptr (talignas 3%N (tptr tvoid)))) ::
                         (Evar _forward (Tfunction
                                          (Tcons (tptr tvoid)
                                            (Tcons
                                              (tptr (talignas 3%N (tptr tvoid)))
                                              Tnil)) tvoid cc_default)) ::
                         (Eaddrof (Evar _f_args (Tstruct __367 noattr))
                           (tptr (Tstruct __367 noattr))) :: nil))
                      (Sset _s
                        (Ebinop Oadd
                          (Etempvar _s (tptr (talignas 3%N (tptr tvoid))))
                          (Etempvar _sz tulong)
                          (tptr (talignas 3%N (tptr tvoid))))))))))))))
    Sskip))
|}.

Definition f_do_generation := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from, (tptr (Tstruct _space noattr))) ::
                (_to, (tptr (Tstruct _space noattr))) ::
                (_fi, (tptr tulong)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_start, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_end, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
        (Tstruct _space noattr)) _next (tptr (talignas 3%N (tptr tvoid)))))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _start
          (tptr (talignas 3%N (tptr tvoid)))))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _limit
            (tptr (talignas 3%N (tptr tvoid)))))
        (Scall None
          (Evar _forward_roots (Tfunction
                                 (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                   (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                     (Tcons
                                       (tptr (tptr (talignas 3%N (tptr tvoid))))
                                       (Tcons (tptr tulong)
                                         (Tcons
                                           (tptr (Tstruct _thread_info noattr))
                                           Tnil))))) tvoid cc_default))
          ((Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid)))) ::
           (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid)))) ::
           (Eaddrof
             (Efield
               (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                 (Tstruct _space noattr)) _next
               (tptr (talignas 3%N (tptr tvoid))))
             (tptr (tptr (talignas 3%N (tptr tvoid))))) ::
           (Etempvar _fi (tptr tulong)) ::
           (Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil))))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _start
            (tptr (talignas 3%N (tptr tvoid)))))
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _limit
              (tptr (talignas 3%N (tptr tvoid)))))
          (Scall None
            (Evar _do_scan (Tfunction
                             (Tcons (tptr (talignas 3%N (tptr tvoid)))
                               (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                 (Tcons (tptr (talignas 3%N (tptr tvoid)))
                                   (Tcons
                                     (tptr (tptr (talignas 3%N (tptr tvoid))))
                                     Tnil)))) tvoid cc_default))
            ((Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid)))) ::
             (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid)))) ::
             (Etempvar _p (tptr (talignas 3%N (tptr tvoid)))) ::
             (Eaddrof
               (Efield
                 (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                   (Tstruct _space noattr)) _next
                 (tptr (talignas 3%N (tptr tvoid))))
               (tptr (tptr (talignas 3%N (tptr tvoid))))) :: nil))))
      (Ssequence
        (Sset _start
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _start
            (tptr (talignas 3%N (tptr tvoid)))))
        (Ssequence
          (Sset _end
            (Efield
              (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _end
              (tptr (talignas 3%N (tptr tvoid)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _next
                (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _start (tptr (talignas 3%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _limit
                (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _end (tptr (talignas 3%N (tptr tvoid)))))))))))
|}.

Definition f_create_space := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_gc_abort,
                 (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))) ::
                (_s, (tptr (Tstruct _space noattr))) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr tvoid)) :: (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2 (Evar _MAX_SPACE_SIZE tulong))
    (Sifthenelse (Ebinop Oge (Etempvar _n tulong) (Etempvar _t'2 tulong)
                   tint)
      (Scall None
        (Etempvar _gc_abort (tptr (Tfunction (Tcons tint Tnil) tvoid
                                    cc_default)))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul (Etempvar _n tulong)
           (Esizeof (talignas 3%N (tptr tvoid)) tulong) tulong) :: nil))
      (Sset _p
        (Ecast (Etempvar _t'1 (tptr tvoid))
          (tptr (talignas 3%N (tptr tvoid))))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Scall None
          (Etempvar _gc_abort (tptr (Tfunction (Tcons tint Tnil) tvoid
                                      cc_default)))
          ((Econst_int (Int.repr 2) tint) :: nil))
        Sskip)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _start
            (tptr (talignas 3%N (tptr tvoid))))
          (Etempvar _p (tptr (talignas 3%N (tptr tvoid)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _next
              (tptr (talignas 3%N (tptr tvoid))))
            (Etempvar _p (tptr (talignas 3%N (tptr tvoid)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _limit
                (tptr (talignas 3%N (tptr tvoid))))
              (Ebinop Oadd (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _n tulong) (tptr (talignas 3%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _end
                (tptr (talignas 3%N (tptr tvoid))))
              (Ebinop Oadd (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _n tulong) (tptr (talignas 3%N (tptr tvoid)))))))))))
|}.

Definition f_create_heap := {|
  fn_return := (tptr (Tstruct _heap noattr));
  fn_callconv := cc_default;
  fn_params := ((_gc_abort,
                 (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_h, (tptr (Tstruct _heap noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _heap noattr) tulong) :: nil))
    (Sset _h
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _heap noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _heap noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Etempvar _gc_abort (tptr (Tfunction (Tcons tint Tnil) tvoid
                                    cc_default)))
        ((Econst_int (Int.repr 3) tint) :: nil))
      Sskip)
    (Ssequence
      (Scall None
        (Evar _create_space (Tfunction
                              (Tcons
                                (tptr (Tfunction (Tcons tint Tnil) tvoid
                                        cc_default))
                                (Tcons (tptr (Tstruct _space noattr))
                                  (Tcons tulong Tnil))) tvoid cc_default))
        ((Etempvar _gc_abort (tptr (Tfunction (Tcons tint Tnil) tvoid
                                     cc_default))) ::
         (Ebinop Oadd
           (Efield
             (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
               (Tstruct _heap noattr)) _spaces
             (tarray (Tstruct _space noattr) 12))
           (Econst_int (Int.repr 0) tint) (tptr (Tstruct _space noattr))) ::
         (Ebinop Oshl (Econst_int (Int.repr 1) tint)
           (Econst_int (Int.repr 16) tint) tint) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 1) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 12) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                            (Tstruct _heap noattr)) _spaces
                          (tarray (Tstruct _space noattr) 12))
                        (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _start
                    (tptr (talignas 3%N (tptr tvoid))))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct _heap noattr)))
                              (Tstruct _heap noattr)) _spaces
                            (tarray (Tstruct _space noattr) 12))
                          (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _next
                      (tptr (talignas 3%N (tptr tvoid))))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _h (tptr (Tstruct _heap noattr)))
                                (Tstruct _heap noattr)) _spaces
                              (tarray (Tstruct _space noattr) 12))
                            (Etempvar _i tint)
                            (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _limit
                        (tptr (talignas 3%N (tptr tvoid))))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                    (Sassign
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _h (tptr (Tstruct _heap noattr)))
                                (Tstruct _heap noattr)) _spaces
                              (tarray (Tstruct _space noattr) 12))
                            (Etempvar _i tint)
                            (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _end
                        (tptr (talignas 3%N (tptr tvoid))))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sreturn (Some (Etempvar _h (tptr (Tstruct _heap noattr)))))))))
|}.

Definition f_make_tinfo := {|
  fn_return := (tptr (Tstruct _thread_info noattr));
  fn_callconv := cc_default;
  fn_params := ((_gc_abort,
                 (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) ::
               (_tinfo, (tptr (Tstruct _thread_info noattr))) ::
               (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _heap noattr))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _create_heap (Tfunction
                           (Tcons
                             (tptr (Tfunction (Tcons tint Tnil) tvoid
                                     cc_default)) Tnil)
                           (tptr (Tstruct _heap noattr)) cc_default))
      ((Etempvar _gc_abort (tptr (Tfunction (Tcons tint Tnil) tvoid
                                   cc_default))) :: nil))
    (Sset _h (Etempvar _t'1 (tptr (Tstruct _heap noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
        ((Esizeof (Tstruct _thread_info noattr) tulong) :: nil))
      (Sset _tinfo
        (Ecast (Etempvar _t'2 (tptr tvoid))
          (tptr (Tstruct _thread_info noattr)))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                     tint)
        (Scall None
          (Etempvar _gc_abort (tptr (Tfunction (Tcons tint Tnil) tvoid
                                      cc_default)))
          ((Econst_int (Int.repr 4) tint) :: nil))
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
                _start (tptr (talignas 3%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc
                (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid))))))
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
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid))))
                (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))))
            (Sreturn (Some (Etempvar _tinfo (tptr (Tstruct _thread_info noattr)))))))))))
|}.

Definition f_resume := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_gc_abort,
                 (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))) ::
                (_fi, (tptr tulong)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) ::
               (_lo, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_hi, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_num_allocs, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Ssequence
    (Sset _num_allocs
      (Ederef
        (Ebinop Oadd (Etempvar _fi (tptr tulong))
          (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong))
    (Ssequence
      (Sset _lo
        (Efield
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                  (Tstruct _heap noattr)) _spaces
                (tarray (Tstruct _space noattr) 12))
              (Econst_int (Int.repr 0) tint) (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _start
          (tptr (talignas 3%N (tptr tvoid)))))
      (Ssequence
        (Sset _hi
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                    (Tstruct _heap noattr)) _spaces
                  (tarray (Tstruct _space noattr) 12))
                (Econst_int (Int.repr 0) tint)
                (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
            _limit (tptr (talignas 3%N (tptr tvoid)))))
        (Ssequence
          (Sifthenelse (Ebinop Olt
                         (Ebinop Osub
                           (Etempvar _hi (tptr (talignas 3%N (tptr tvoid))))
                           (Etempvar _lo (tptr (talignas 3%N (tptr tvoid))))
                           tlong) (Etempvar _num_allocs tulong) tint)
            (Scall None
              (Etempvar _gc_abort (tptr (Tfunction (Tcons tint Tnil) tvoid
                                          cc_default)))
              ((Econst_int (Int.repr 5) tint) :: nil))
            Sskip)
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _alloc
                (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _lo (tptr (talignas 3%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _limit
                (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _hi (tptr (talignas 3%N (tptr tvoid)))))))))))
|}.

Definition f_garbage_collect := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_gc_abort,
                 (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))) ::
                (_fi, (tptr tulong)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) :: (_i, tint) ::
               (_w, tulong) :: (_t'7, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'6, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Ebinop Osub (Econst_int (Int.repr 12) tint)
                           (Econst_int (Int.repr 1) tint) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                          (Tstruct _heap noattr)) _spaces
                        (tarray (Tstruct _space noattr) 12))
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint)
                      (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _start
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid))))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'6
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _h (tptr (Tstruct _heap noattr)))
                                (Tstruct _heap noattr)) _spaces
                              (tarray (Tstruct _space noattr) 12))
                            (Etempvar _i tint)
                            (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _end
                        (tptr (talignas 3%N (tptr tvoid)))))
                    (Ssequence
                      (Sset _t'7
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct _heap noattr)))
                                  (Tstruct _heap noattr)) _spaces
                                (tarray (Tstruct _space noattr) 12))
                              (Etempvar _i tint)
                              (tptr (Tstruct _space noattr)))
                            (Tstruct _space noattr)) _start
                          (tptr (talignas 3%N (tptr tvoid)))))
                      (Sset _w
                        (Ebinop Osub
                          (Etempvar _t'6 (tptr (talignas 3%N (tptr tvoid))))
                          (Etempvar _t'7 (tptr (talignas 3%N (tptr tvoid))))
                          tlong))))
                  (Scall None
                    (Evar _create_space (Tfunction
                                          (Tcons
                                            (tptr (Tfunction
                                                    (Tcons tint Tnil) tvoid
                                                    cc_default))
                                            (Tcons
                                              (tptr (Tstruct _space noattr))
                                              (Tcons tulong Tnil))) tvoid
                                          cc_default))
                    ((Etempvar _gc_abort (tptr (Tfunction (Tcons tint Tnil)
                                                 tvoid cc_default))) ::
                     (Ebinop Oadd
                       (Efield
                         (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                           (Tstruct _heap noattr)) _spaces
                         (tarray (Tstruct _space noattr) 12))
                       (Ebinop Oadd (Etempvar _i tint)
                         (Econst_int (Int.repr 1) tint) tint)
                       (tptr (Tstruct _space noattr))) ::
                     (Ebinop Omul (Econst_int (Int.repr 2) tint)
                       (Etempvar _w tulong) tulong) :: nil)))
                Sskip))
            (Ssequence
              (Scall None
                (Evar _do_generation (Tfunction
                                       (Tcons (tptr (Tstruct _space noattr))
                                         (Tcons
                                           (tptr (Tstruct _space noattr))
                                           (Tcons (tptr tulong)
                                             (Tcons
                                               (tptr (Tstruct _thread_info noattr))
                                               Tnil)))) tvoid cc_default))
                ((Ebinop Oadd
                   (Efield
                     (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                       (Tstruct _heap noattr)) _spaces
                     (tarray (Tstruct _space noattr) 12)) (Etempvar _i tint)
                   (tptr (Tstruct _space noattr))) ::
                 (Ebinop Oadd
                   (Efield
                     (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                       (Tstruct _heap noattr)) _spaces
                     (tarray (Tstruct _space noattr) 12))
                   (Ebinop Oadd (Etempvar _i tint)
                     (Econst_int (Int.repr 1) tint) tint)
                   (tptr (Tstruct _space noattr))) ::
                 (Etempvar _fi (tptr tulong)) ::
                 (Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil))
              (Ssequence
                (Sset _t'1
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                            (Tstruct _heap noattr)) _spaces
                          (tarray (Tstruct _space noattr) 12))
                        (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _end
                    (tptr (talignas 3%N (tptr tvoid)))))
                (Ssequence
                  (Sset _t'2
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct _heap noattr)))
                              (Tstruct _heap noattr)) _spaces
                            (tarray (Tstruct _space noattr) 12))
                          (Etempvar _i tint) (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _start
                      (tptr (talignas 3%N (tptr tvoid)))))
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _h (tptr (Tstruct _heap noattr)))
                                (Tstruct _heap noattr)) _spaces
                              (tarray (Tstruct _space noattr) 12))
                            (Ebinop Oadd (Etempvar _i tint)
                              (Econst_int (Int.repr 1) tint) tint)
                            (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _limit
                        (tptr (talignas 3%N (tptr tvoid)))))
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct _heap noattr)))
                                  (Tstruct _heap noattr)) _spaces
                                (tarray (Tstruct _space noattr) 12))
                              (Ebinop Oadd (Etempvar _i tint)
                                (Econst_int (Int.repr 1) tint) tint)
                              (tptr (Tstruct _space noattr)))
                            (Tstruct _space noattr)) _next
                          (tptr (talignas 3%N (tptr tvoid)))))
                      (Sifthenelse (Ebinop Ole
                                     (Ebinop Osub
                                       (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
                                       (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))
                                       tlong)
                                     (Ebinop Osub
                                       (Etempvar _t'3 (tptr (talignas 3%N (tptr tvoid))))
                                       (Etempvar _t'4 (tptr (talignas 3%N (tptr tvoid))))
                                       tlong) tint)
                        (Ssequence
                          (Scall None
                            (Evar _resume (Tfunction
                                            (Tcons
                                              (tptr (Tfunction
                                                      (Tcons tint Tnil) tvoid
                                                      cc_default))
                                              (Tcons (tptr tulong)
                                                (Tcons
                                                  (tptr (Tstruct _thread_info noattr))
                                                  Tnil))) tvoid cc_default))
                            ((Etempvar _gc_abort (tptr (Tfunction
                                                         (Tcons tint Tnil)
                                                         tvoid cc_default))) ::
                             (Etempvar _fi (tptr tulong)) ::
                             (Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                             nil))
                          (Sreturn None))
                        Sskip))))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Scall None
      (Etempvar _gc_abort (tptr (Tfunction (Tcons tint Tnil) tvoid
                                  cc_default)))
      ((Econst_int (Int.repr 6) tint) :: nil))))
|}.

Definition f_cell_modify := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ti, (tptr (Tstruct _thread_info noattr))) ::
                (_p_cell, (tptr (talignas 3%N (tptr tvoid)))) ::
                (_p_val, (talignas 3%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'6, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'4, (tptr (Tstruct _heap noattr))) ::
               (_t'3, (tptr (Tstruct _heap noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef (Etempvar _p_cell (tptr (talignas 3%N (tptr tvoid))))
      (talignas 3%N (tptr tvoid)))
    (Etempvar _p_val (talignas 3%N (tptr tvoid))))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _Is_block (Tfunction (Tcons (talignas 3%N (tptr tvoid)) Tnil)
                        tint cc_default))
      ((Etempvar _p_val (talignas 3%N (tptr tvoid))) :: nil))
    (Sifthenelse (Etempvar _t'2 tint)
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Sset _t'1
                (Ecast
                  (Ebinop Osub
                    (Etempvar _t'6 (tptr (talignas 3%N (tptr tvoid))))
                    (Econst_int (Int.repr 1) tint)
                    (tptr (talignas 3%N (tptr tvoid))))
                  (tptr (talignas 3%N (tptr tvoid))))))
            (Sassign
              (Efield
                (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _limit
                (tptr (talignas 3%N (tptr tvoid))))
              (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))))
          (Sassign
            (Ederef
              (Ecast (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))
                (tptr (tptr (talignas 3%N (tptr tvoid)))))
              (tptr (talignas 3%N (tptr tvoid))))
            (Etempvar _p_cell (tptr (talignas 3%N (tptr tvoid))))))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                (Tstruct _thread_info noattr)) _heap
              (tptr (Tstruct _heap noattr))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                  (Tstruct _thread_info noattr)) _heap
                (tptr (Tstruct _heap noattr))))
            (Ssequence
              (Sset _t'5
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _t'4 (tptr (Tstruct _heap noattr)))
                          (Tstruct _heap noattr)) _spaces
                        (tarray (Tstruct _space noattr) 12))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _t'3 (tptr (Tstruct _heap noattr)))
                          (Tstruct _heap noattr)) _spaces
                        (tarray (Tstruct _space noattr) 12))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _limit
                  (tptr (talignas 3%N (tptr tvoid))))
                (Ebinop Osub
                  (Etempvar _t'5 (tptr (talignas 3%N (tptr tvoid))))
                  (Econst_int (Int.repr 1) tint)
                  (tptr (talignas 3%N (tptr tvoid)))))))))
      Sskip)))
|}.

Definition f_reset_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'2, (tptr (talignas 3%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 3%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                     (Econst_int (Int.repr 12) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tulong)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _start (tptr (talignas 3%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tulong)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _next (tptr (talignas 3%N (tptr tvoid))))
            (Etempvar _t'2 (tptr (talignas 3%N (tptr tvoid))))))
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tulong)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _end (tptr (talignas 3%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tulong)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _limit (tptr (talignas 3%N (tptr tvoid))))
            (Etempvar _t'1 (tptr (talignas 3%N (tptr tvoid))))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_free_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_p, (tptr (talignas 3%N (tptr tvoid)))) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                       (Econst_int (Int.repr 12) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _p
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tulong)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _start (tptr (talignas 3%N (tptr tvoid)))))
          (Sifthenelse (Ebinop One
                         (Etempvar _p (tptr (talignas 3%N (tptr tvoid))))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _p (tptr (talignas 3%N (tptr tvoid)))) :: nil))
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Etempvar _h (tptr (Tstruct _heap noattr))) :: nil)))
|}.

Definition composites : list composite_definition :=
(Composite _thread_info Struct
   ((_alloc, (tptr (talignas 3%N (tptr tvoid)))) ::
    (_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
    (_heap, (tptr (Tstruct _heap noattr))) ::
    (_args, (tarray (talignas 3%N (tptr tvoid)) 1024)) :: nil)
   noattr ::
 Composite _space Struct
   ((_start, (tptr (talignas 3%N (tptr tvoid)))) ::
    (_next, (tptr (talignas 3%N (tptr tvoid)))) ::
    (_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
    (_end, (tptr (talignas 3%N (tptr tvoid)))) :: nil)
   noattr ::
 Composite _heap Struct
   ((_spaces, (tarray (Tstruct _space noattr) 12)) :: nil)
   noattr ::
 Composite __367 Struct
   ((_from_start, (tptr (talignas 3%N (tptr tvoid)))) ::
    (_from_limit, (tptr (talignas 3%N (tptr tvoid)))) ::
    (_next, (tptr (tptr (talignas 3%N (tptr tvoid))))) :: (_depth, tint) ::
    nil)
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
 (_int_or_ptr__is_int,
   Gfun(External (EF_external "int_or_ptr__is_int"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil) tint cc_default)) ::
 (_int_or_ptr__to_ptr,
   Gfun(External (EF_external "int_or_ptr__to_ptr"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (talignas 3%N (tptr tvoid)) Tnil) (tptr tvoid) cc_default)) ::
 (_int_or_ptr__of_ptr,
   Gfun(External (EF_external "int_or_ptr__of_ptr"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) (talignas 3%N (tptr tvoid)) cc_default)) ::
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_MAX_SPACE_SIZE, Gvar v_MAX_SPACE_SIZE) ::
 (_Is_block, Gfun(Internal f_Is_block)) ::
 (_Is_from, Gfun(Internal f_Is_from)) ::
 (_has_been_forwarded, Gfun(Internal f_has_been_forwarded)) ::
 (_new_addr_from_forwarded, Gfun(Internal f_new_addr_from_forwarded)) ::
 (_mark_as_forwarded, Gfun(Internal f_mark_as_forwarded)) ::
 (_forward, Gfun(Internal f_forward)) ::
 (_forward_roots, Gfun(Internal f_forward_roots)) ::
 (_forward_remset, Gfun(Internal f_forward_remset)) ::
 (_do_scan, Gfun(Internal f_do_scan)) ::
 (_do_generation, Gfun(Internal f_do_generation)) ::
 (_create_space, Gfun(Internal f_create_space)) ::
 (_create_heap, Gfun(Internal f_create_heap)) ::
 (_make_tinfo, Gfun(Internal f_make_tinfo)) ::
 (_resume, Gfun(Internal f_resume)) ::
 (_garbage_collect, Gfun(Internal f_garbage_collect)) ::
 (_cell_modify, Gfun(Internal f_cell_modify)) ::
 (_reset_heap, Gfun(Internal f_reset_heap)) ::
 (_free_heap, Gfun(Internal f_free_heap)) :: nil).

Definition public_idents : list ident :=
(_free_heap :: _reset_heap :: _cell_modify :: _garbage_collect :: _resume ::
 _make_tinfo :: _create_heap :: _create_space :: _do_generation ::
 _do_scan :: _forward_remset :: _forward_roots :: _forward ::
 _mark_as_forwarded :: _new_addr_from_forwarded :: _has_been_forwarded ::
 _Is_from :: _Is_block :: _MAX_SPACE_SIZE :: _free :: _malloc ::
 _certicoq_block__field_ptr_iter :: _certicoq_block__size_get ::
 _certicoq_block__header_get_ptr :: _certicoq_block__copy ::
 _certicoq_block__of_header :: _int_or_ptr__of_ptr :: _int_or_ptr__to_ptr ::
 _int_or_ptr__is_int :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___builtin_expect :: ___builtin_unreachable ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


(*\nInput hashes (sha256):\n\n22e152cae42fd4e3ad0ee15055ddf5e91684cdfa9e691710804e66d81e9d3c13  src/c/include/coq-vsu-gc/src/gc.c
05098169e1d93373a5b4dd3ca0f4401d1b1a20483e0b61cdba8db81c76a380d7  src/c/include/coq-vsu-gc/gc.h
a9b18c1959df2cb5404306021e5256eb25c78c20ef9ec326a1cac75cea375fe7  src/c/include/coq-vsu-gc/mem.h\n*)
