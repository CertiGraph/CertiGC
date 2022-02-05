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
  Definition source_file := "src/c/include/coq-vsu-gc/src/gc.c".
  Definition normalized := true.
End Info.

Definition _Is_block : ident := $"Is_block".
Definition _Is_from : ident := $"Is_from".
Definition _MAX_SPACE_SIZE : ident := $"MAX_SPACE_SIZE".
Definition __IO_FILE : ident := $"_IO_FILE".
Definition __IO_backup_base : ident := $"_IO_backup_base".
Definition __IO_buf_base : ident := $"_IO_buf_base".
Definition __IO_buf_end : ident := $"_IO_buf_end".
Definition __IO_codecvt : ident := $"_IO_codecvt".
Definition __IO_marker : ident := $"_IO_marker".
Definition __IO_read_base : ident := $"_IO_read_base".
Definition __IO_read_end : ident := $"_IO_read_end".
Definition __IO_read_ptr : ident := $"_IO_read_ptr".
Definition __IO_save_base : ident := $"_IO_save_base".
Definition __IO_save_end : ident := $"_IO_save_end".
Definition __IO_wide_data : ident := $"_IO_wide_data".
Definition __IO_write_base : ident := $"_IO_write_base".
Definition __IO_write_end : ident := $"_IO_write_end".
Definition __IO_write_ptr : ident := $"_IO_write_ptr".
Definition ___assert_fail : ident := $"__assert_fail".
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
Definition ___func__ : ident := $"__func__".
Definition ___func____1 : ident := $"__func____1".
Definition ___func____2 : ident := $"__func____2".
Definition ___pad5 : ident := $"__pad5".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_10 : ident := $"__stringlit_10".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition ___stringlit_7 : ident := $"__stringlit_7".
Definition ___stringlit_8 : ident := $"__stringlit_8".
Definition ___stringlit_9 : ident := $"__stringlit_9".
Definition __chain : ident := $"_chain".
Definition __codecvt : ident := $"_codecvt".
Definition __cur_column : ident := $"_cur_column".
Definition __fileno : ident := $"_fileno".
Definition __flags : ident := $"_flags".
Definition __flags2 : ident := $"_flags2".
Definition __freeres_buf : ident := $"_freeres_buf".
Definition __freeres_list : ident := $"_freeres_list".
Definition __lock : ident := $"_lock".
Definition __markers : ident := $"_markers".
Definition __mode : ident := $"_mode".
Definition __offset : ident := $"_offset".
Definition __old_offset : ident := $"_old_offset".
Definition __shortbuf : ident := $"_shortbuf".
Definition __unused2 : ident := $"_unused2".
Definition __vtable_offset : ident := $"_vtable_offset".
Definition __wide_data : ident := $"_wide_data".
Definition _abort_with : ident := $"abort_with".
Definition _alloc : ident := $"alloc".
Definition _args : ident := $"args".
Definition _certicoq_block__get_field : ident := $"certicoq_block__get_field".
Definition _certicoq_block__get_field_ptr : ident := $"certicoq_block__get_field_ptr".
Definition _certicoq_block__get_header : ident := $"certicoq_block__get_header".
Definition _certicoq_block__get_size : ident := $"certicoq_block__get_size".
Definition _certicoq_block__get_tag : ident := $"certicoq_block__get_tag".
Definition _certicoq_block__init : ident := $"certicoq_block__init".
Definition _certicoq_block__set_field : ident := $"certicoq_block__set_field".
Definition _certicoq_block__set_header : ident := $"certicoq_block__set_header".
Definition _create_heap : ident := $"create_heap".
Definition _create_space : ident := $"create_space".
Definition _depth : ident := $"depth".
Definition _do_generation : ident := $"do_generation".
Definition _do_scan : ident := $"do_scan".
Definition _end : ident := $"end".
Definition _exit : ident := $"exit".
Definition _fi : ident := $"fi".
Definition _forward : ident := $"forward".
Definition _forward_remset : ident := $"forward_remset".
Definition _forward_roots : ident := $"forward_roots".
Definition _fprintf : ident := $"fprintf".
Definition _free : ident := $"free".
Definition _free_heap : ident := $"free_heap".
Definition _from : ident := $"from".
Definition _from_limit : ident := $"from_limit".
Definition _from_start : ident := $"from_start".
Definition _garbage_collect : ident := $"garbage_collect".
Definition _h : ident := $"h".
Definition _hd : ident := $"hd".
Definition _heap : ident := $"heap".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _int_or_ptr__is_int : ident := $"int_or_ptr__is_int".
Definition _int_or_ptr__of_ptr : ident := $"int_or_ptr__of_ptr".
Definition _int_or_ptr__to_ptr : ident := $"int_or_ptr__to_ptr".
Definition _j : ident := $"j".
Definition _limit : ident := $"limit".
Definition _lo : ident := $"lo".
Definition _main : ident := $"main".
Definition _make_tinfo : ident := $"make_tinfo".
Definition _malloc : ident := $"malloc".
Definition _n : ident := $"n".
Definition _new : ident := $"new".
Definition _next : ident := $"next".
Definition _num_allocs : ident := $"num_allocs".
Definition _p : ident := $"p".
Definition _q : ident := $"q".
Definition _reset_heap : ident := $"reset_heap".
Definition _resume : ident := $"resume".
Definition _roots : ident := $"roots".
Definition _s : ident := $"s".
Definition _scan : ident := $"scan".
Definition _space : ident := $"space".
Definition _spaces : ident := $"spaces".
Definition _start : ident := $"start".
Definition _stderr : ident := $"stderr".
Definition _sz : ident := $"sz".
Definition _tag : ident := $"tag".
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
Definition _t'12 : ident := 139%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 34);
  gvar_init := (Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 47) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 113) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 47) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_9 := {|
  gvar_info := (tarray tschar 48);
  gvar_init := (Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 39) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 38);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 20);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 91) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 93) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 77) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 88) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 43);
  gvar_init := (Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 27);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_7 := {|
  gvar_info := (tarray tschar 39);
  gvar_init := (Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 45);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 62) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 60) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_8 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_10 := {|
  gvar_info := (tarray tschar 24);
  gvar_init := (Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_stderr := {|
  gvar_info := (tptr (Tstruct __IO_FILE noattr));
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_MAX_SPACE_SIZE := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 536870912) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_abort_with := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct __IO_FILE noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1 (Evar _stderr (tptr (Tstruct __IO_FILE noattr))))
    (Scall None
      (Evar _fprintf (Tfunction
                       (Tcons (tptr (Tstruct __IO_FILE noattr))
                         (Tcons (tptr tschar) Tnil)) tint
                       {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
      ((Etempvar _t'1 (tptr (Tstruct __IO_FILE noattr))) ::
       (Etempvar _s (tptr tschar)) :: nil)))
  (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
    ((Econst_int (Int.repr 1) tint) :: nil)))
|}.

Definition f_Is_block := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _int_or_ptr__is_int (Tfunction
                                (Tcons (talignas 2%N (tptr tvoid)) Tnil) tint
                                cc_default))
    ((Etempvar _x (talignas 2%N (tptr tvoid))) :: nil))
  (Sreturn (Some (Ebinop Oeq (Etempvar _t'1 tint)
                   (Econst_int (Int.repr 0) tint) tint))))
|}.

Definition f_Is_from := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_v, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole
                 (Etempvar _from_start (tptr (talignas 2%N (tptr tvoid))))
                 (Etempvar _v (tptr (talignas 2%N (tptr tvoid)))) tint)
    (Sset _t'1
      (Ecast
        (Ebinop Olt (Etempvar _v (tptr (talignas 2%N (tptr tvoid))))
          (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) tint)
        tbool))
    (Sset _t'1 (Econst_int (Int.repr 0) tint)))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_forward := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                (_p, (tptr (talignas 2%N (tptr tvoid)))) :: (_depth, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_v, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_va, (talignas 2%N (tptr tvoid))) :: (_hd, tuint) ::
               (_i, tuint) :: (_sz, tuint) ::
               (_new, (tptr (talignas 2%N (tptr tvoid)))) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'8, (talignas 2%N (tptr tvoid))) ::
               (_t'7, (talignas 2%N (tptr tvoid))) ::
               (_t'6, (talignas 2%N (tptr tvoid))) ::
               (_t'5, (tptr (talignas 2%N (tptr tvoid)))) :: (_t'4, tuint) ::
               (_t'3, (talignas 2%N (tptr tvoid))) :: (_t'2, tuint) ::
               (_t'1, (tptr tvoid)) ::
               (_t'12, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _va
    (Ederef (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
      (talignas 2%N (tptr tvoid))))
  (Ssequence
    (Scall (Some _t'11)
      (Evar _Is_block (Tfunction (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                        tint cc_default))
      ((Etempvar _va (talignas 2%N (tptr tvoid))) :: nil))
    (Sifthenelse (Etempvar _t'11 tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _int_or_ptr__to_ptr (Tfunction
                                        (Tcons (talignas 2%N (tptr tvoid))
                                          Tnil) (tptr tvoid) cc_default))
            ((Etempvar _va (talignas 2%N (tptr tvoid))) :: nil))
          (Sset _v
            (Ecast (Etempvar _t'1 (tptr tvoid))
              (tptr (talignas 2%N (tptr tvoid))))))
        (Ssequence
          (Scall (Some _t'10)
            (Evar _Is_from (Tfunction
                             (Tcons (tptr (talignas 2%N (tptr tvoid)))
                               (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                 (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                   Tnil))) tint cc_default))
            ((Etempvar _from_start (tptr (talignas 2%N (tptr tvoid)))) ::
             (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) ::
             (Etempvar _v (tptr (talignas 2%N (tptr tvoid)))) :: nil))
          (Sifthenelse (Etempvar _t'10 tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _certicoq_block__get_header (Tfunction
                                                      (Tcons
                                                        (tptr (talignas 2%N (tptr tvoid)))
                                                        Tnil) tuint
                                                      cc_default))
                  ((Etempvar _v (tptr (talignas 2%N (tptr tvoid)))) :: nil))
                (Sset _hd (Etempvar _t'2 tuint)))
              (Sifthenelse (Ebinop Oeq (Etempvar _hd tuint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _certicoq_block__get_field (Tfunction
                                                       (Tcons
                                                         (tptr (talignas 2%N (tptr tvoid)))
                                                         (Tcons tuint Tnil))
                                                       (talignas 2%N (tptr tvoid))
                                                       cc_default))
                    ((Etempvar _v (tptr (talignas 2%N (tptr tvoid)))) ::
                     (Econst_int (Int.repr 0) tint) :: nil))
                  (Sassign
                    (Ederef (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                      (talignas 2%N (tptr tvoid)))
                    (Etempvar _t'3 (talignas 2%N (tptr tvoid)))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'4)
                      (Evar _certicoq_block__get_size (Tfunction
                                                        (Tcons tuint Tnil)
                                                        tuint cc_default))
                      ((Etempvar _hd tuint) :: nil))
                    (Sset _sz (Etempvar _t'4 tuint)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'12
                          (Ederef
                            (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid)))))
                            (tptr (talignas 2%N (tptr tvoid)))))
                        (Scall (Some _t'5)
                          (Evar _certicoq_block__init (Tfunction
                                                        (Tcons
                                                          (tptr (talignas 2%N (tptr tvoid)))
                                                          (Tcons tuint Tnil))
                                                        (tptr (talignas 2%N (tptr tvoid)))
                                                        cc_default))
                          ((Etempvar _t'12 (tptr (talignas 2%N (tptr tvoid)))) ::
                           (Etempvar _hd tuint) :: nil)))
                      (Sset _new
                        (Etempvar _t'5 (tptr (talignas 2%N (tptr tvoid))))))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid)))))
                          (tptr (talignas 2%N (tptr tvoid))))
                        (Ebinop Oadd
                          (Etempvar _new (tptr (talignas 2%N (tptr tvoid))))
                          (Etempvar _sz tuint)
                          (tptr (talignas 2%N (tptr tvoid)))))
                      (Ssequence
                        (Ssequence
                          (Sset _i (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                             (Etempvar _sz tuint) tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Scall (Some _t'6)
                                  (Evar _certicoq_block__get_field (Tfunction
                                                                    (Tcons
                                                                    (tptr (talignas 2%N (tptr tvoid)))
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                    (talignas 2%N (tptr tvoid))
                                                                    cc_default))
                                  ((Etempvar _v (tptr (talignas 2%N (tptr tvoid)))) ::
                                   (Etempvar _i tuint) :: nil))
                                (Scall None
                                  (Evar _certicoq_block__set_field (Tfunction
                                                                    (Tcons
                                                                    (tptr (talignas 2%N (tptr tvoid)))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (talignas 2%N (tptr tvoid))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                  ((Etempvar _new (tptr (talignas 2%N (tptr tvoid)))) ::
                                   (Etempvar _i tuint) ::
                                   (Etempvar _t'6 (talignas 2%N (tptr tvoid))) ::
                                   nil))))
                            (Sset _i
                              (Ebinop Oadd (Etempvar _i tuint)
                                (Econst_int (Int.repr 1) tint) tuint))))
                        (Ssequence
                          (Scall None
                            (Evar _certicoq_block__set_header (Tfunction
                                                                (Tcons
                                                                  (tptr (talignas 2%N (tptr tvoid)))
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                            ((Etempvar _v (tptr (talignas 2%N (tptr tvoid)))) ::
                             (Econst_int (Int.repr 0) tint) :: nil))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'7)
                                (Evar _int_or_ptr__of_ptr (Tfunction
                                                            (Tcons
                                                              (tptr tvoid)
                                                              Tnil)
                                                            (talignas 2%N (tptr tvoid))
                                                            cc_default))
                                ((Etempvar _new (tptr (talignas 2%N (tptr tvoid)))) ::
                                 nil))
                              (Scall None
                                (Evar _certicoq_block__set_field (Tfunction
                                                                   (Tcons
                                                                    (tptr (talignas 2%N (tptr tvoid)))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    (talignas 2%N (tptr tvoid))
                                                                    Tnil)))
                                                                   tvoid
                                                                   cc_default))
                                ((Etempvar _v (tptr (talignas 2%N (tptr tvoid)))) ::
                                 (Econst_int (Int.repr 0) tint) ::
                                 (Etempvar _t'7 (talignas 2%N (tptr tvoid))) ::
                                 nil)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'8)
                                  (Evar _int_or_ptr__of_ptr (Tfunction
                                                              (Tcons
                                                                (tptr tvoid)
                                                                Tnil)
                                                              (talignas 2%N (tptr tvoid))
                                                              cc_default))
                                  ((Etempvar _new (tptr (talignas 2%N (tptr tvoid)))) ::
                                   nil))
                                (Sassign
                                  (Ederef
                                    (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                                    (talignas 2%N (tptr tvoid)))
                                  (Etempvar _t'8 (talignas 2%N (tptr tvoid)))))
                              (Sifthenelse (Ebinop Ogt (Etempvar _depth tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Sset _i (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tuint)
                                                     (Etempvar _sz tuint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Scall (Some _t'9)
                                          (Evar _certicoq_block__get_field_ptr 
                                          (Tfunction
                                            (Tcons
                                              (tptr (talignas 2%N (tptr tvoid)))
                                              (Tcons tuint Tnil))
                                            (tptr (talignas 2%N (tptr tvoid)))
                                            cc_default))
                                          ((Etempvar _new (tptr (talignas 2%N (tptr tvoid)))) ::
                                           (Etempvar _i tuint) :: nil))
                                        (Scall None
                                          (Evar _forward (Tfunction
                                                           (Tcons
                                                             (tptr (talignas 2%N (tptr tvoid)))
                                                             (Tcons
                                                               (tptr (talignas 2%N (tptr tvoid)))
                                                               (Tcons
                                                                 (tptr (tptr (talignas 2%N (tptr tvoid))))
                                                                 (Tcons
                                                                   (tptr (talignas 2%N (tptr tvoid)))
                                                                   (Tcons
                                                                    tint
                                                                    Tnil)))))
                                                           tvoid cc_default))
                                          ((Etempvar _from_start (tptr (talignas 2%N (tptr tvoid)))) ::
                                           (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) ::
                                           (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                                           (Etempvar _t'9 (tptr (talignas 2%N (tptr tvoid)))) ::
                                           (Ebinop Osub
                                             (Etempvar _depth tint)
                                             (Econst_int (Int.repr 1) tint)
                                             tint) :: nil))))
                                    (Sset _i
                                      (Ebinop Oadd (Etempvar _i tuint)
                                        (Econst_int (Int.repr 1) tint) tuint))))
                                Sskip))))))))))
            Sskip)))
      Sskip)))
|}.

Definition v___func__ := {|
  gvar_info := (tarray tschar 14);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_forward_roots := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                (_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_n, tuint) :: (_roots, (tptr tuint)) ::
               (_args, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _n
    (Ederef
      (Ebinop Oadd (Etempvar _fi (tptr tuint)) (Econst_int (Int.repr 1) tint)
        (tptr tuint)) tuint))
  (Ssequence
    (Sset _roots
      (Ebinop Oadd (Etempvar _fi (tptr tuint)) (Econst_int (Int.repr 2) tint)
        (tptr tuint)))
    (Ssequence
      (Sset _args
        (Efield
          (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
            (Tstruct _thread_info noattr)) _args
          (tarray (talignas 2%N (tptr tvoid)) 1024)))
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _n tuint)
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd (Etempvar _roots (tptr tuint))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Sifthenelse (Ebinop Olt (Etempvar _t'2 tuint)
                               (Econst_int (Int.repr 1024) tint) tint)
                  Sskip
                  (Scall None
                    (Evar ___assert_fail (Tfunction
                                           (Tcons (tptr tschar)
                                             (Tcons (tptr tschar)
                                               (Tcons tuint
                                                 (Tcons (tptr tschar) Tnil))))
                                           tvoid cc_default))
                    ((Evar ___stringlit_2 (tarray tschar 20)) ::
                     (Evar ___stringlit_1 (tarray tschar 34)) ::
                     (Econst_int (Int.repr 160) tint) ::
                     (Evar ___func__ (tarray tschar 14)) :: nil))))
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Etempvar _roots (tptr tuint))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Scall None
                  (Evar _forward (Tfunction
                                   (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                     (Tcons
                                       (tptr (talignas 2%N (tptr tvoid)))
                                       (Tcons
                                         (tptr (tptr (talignas 2%N (tptr tvoid))))
                                         (Tcons
                                           (tptr (talignas 2%N (tptr tvoid)))
                                           (Tcons tint Tnil))))) tvoid
                                   cc_default))
                  ((Etempvar _from_start (tptr (talignas 2%N (tptr tvoid)))) ::
                   (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) ::
                   (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                   (Ebinop Oadd
                     (Etempvar _args (tptr (talignas 2%N (tptr tvoid))))
                     (Etempvar _t'1 tuint)
                     (tptr (talignas 2%N (tptr tvoid)))) ::
                   (Econst_int (Int.repr 0) tint) :: nil)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint)))))))
|}.

Definition f_forward_remset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from, (tptr (Tstruct _space noattr))) ::
                (_to, (tptr (Tstruct _space noattr))) ::
                (_next, (tptr (tptr (talignas 2%N (tptr tvoid))))) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (talignas 2%N (tptr tvoid)))) :: (_t'2, tint) ::
               (_t'1, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'11, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'10, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'9, (talignas 2%N (tptr tvoid))) ::
               (_t'8, (talignas 2%N (tptr tvoid))) ::
               (_t'7, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'6, (talignas 2%N (tptr tvoid))) ::
               (_t'5, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _q
    (Efield
      (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
        (Tstruct _space noattr)) _limit (tptr (talignas 2%N (tptr tvoid)))))
  (Sloop
    (Ssequence
      (Ssequence
        (Sset _t'11
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _end
            (tptr (talignas 2%N (tptr tvoid)))))
        (Sifthenelse (Ebinop One
                       (Etempvar _q (tptr (talignas 2%N (tptr tvoid))))
                       (Etempvar _t'11 (tptr (talignas 2%N (tptr tvoid))))
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
                (tptr (talignas 2%N (tptr tvoid)))))
            (Ssequence
              (Sset _t'8
                (Ederef (Etempvar _q (tptr (talignas 2%N (tptr tvoid))))
                  (talignas 2%N (tptr tvoid))))
              (Sifthenelse (Ebinop Ole
                             (Etempvar _t'7 (tptr (talignas 2%N (tptr tvoid))))
                             (Ecast
                               (Etempvar _t'8 (talignas 2%N (tptr tvoid)))
                               (tptr (talignas 2%N (tptr tvoid)))) tint)
                (Ssequence
                  (Sset _t'9
                    (Ederef (Etempvar _q (tptr (talignas 2%N (tptr tvoid))))
                      (talignas 2%N (tptr tvoid))))
                  (Ssequence
                    (Sset _t'10
                      (Efield
                        (Ederef
                          (Etempvar _from (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _limit
                        (tptr (talignas 2%N (tptr tvoid)))))
                    (Sset _t'2
                      (Ecast
                        (Ebinop Olt
                          (Ecast (Etempvar _t'9 (talignas 2%N (tptr tvoid)))
                            (tptr (talignas 2%N (tptr tvoid))))
                          (Etempvar _t'10 (tptr (talignas 2%N (tptr tvoid))))
                          tint) tbool))))
                (Sset _t'2 (Econst_int (Int.repr 0) tint)))))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
            (Ssequence
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                      (Tstruct _space noattr)) _start
                    (tptr (talignas 2%N (tptr tvoid)))))
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _limit
                      (tptr (talignas 2%N (tptr tvoid)))))
                  (Ssequence
                    (Sset _t'6
                      (Ederef
                        (Etempvar _q (tptr (talignas 2%N (tptr tvoid))))
                        (talignas 2%N (tptr tvoid))))
                    (Scall None
                      (Evar _forward (Tfunction
                                       (Tcons
                                         (tptr (talignas 2%N (tptr tvoid)))
                                         (Tcons
                                           (tptr (talignas 2%N (tptr tvoid)))
                                           (Tcons
                                             (tptr (tptr (talignas 2%N (tptr tvoid))))
                                             (Tcons
                                               (tptr (talignas 2%N (tptr tvoid)))
                                               (Tcons tint Tnil))))) tvoid
                                       cc_default))
                      ((Etempvar _t'4 (tptr (talignas 2%N (tptr tvoid)))) ::
                       (Etempvar _t'5 (tptr (talignas 2%N (tptr tvoid)))) ::
                       (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                       (Ecast (Etempvar _t'6 (talignas 2%N (tptr tvoid)))
                         (tptr (talignas 2%N (tptr tvoid)))) ::
                       (Econst_int (Int.repr 0) tint) :: nil)))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                          (Tstruct _space noattr)) _limit
                        (tptr (talignas 2%N (tptr tvoid)))))
                    (Sset _t'1
                      (Ecast
                        (Ebinop Osub
                          (Etempvar _t'3 (tptr (talignas 2%N (tptr tvoid))))
                          (Econst_int (Int.repr 1) tint)
                          (tptr (talignas 2%N (tptr tvoid))))
                        (tptr (talignas 2%N (tptr tvoid))))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                        (Tstruct _space noattr)) _limit
                      (tptr (talignas 2%N (tptr tvoid))))
                    (Etempvar _t'1 (tptr (talignas 2%N (tptr tvoid))))))
                (Sassign
                  (Ederef (Etempvar _t'1 (tptr (talignas 2%N (tptr tvoid))))
                    (talignas 2%N (tptr tvoid)))
                  (Ecast (Etempvar _q (tptr (talignas 2%N (tptr tvoid))))
                    (talignas 2%N (tptr tvoid))))))
            Sskip))
        (Sset _q
          (Ebinop Oadd (Etempvar _q (tptr (talignas 2%N (tptr tvoid))))
            (Econst_int (Int.repr 1) tint)
            (tptr (talignas 2%N (tptr tvoid)))))))
    Sskip))
|}.

Definition f_do_scan := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from_start, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_from_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_scan, (tptr (talignas 2%N (tptr tvoid)))) ::
                (_next, (tptr (tptr (talignas 2%N (tptr tvoid))))) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, (tptr (talignas 2%N (tptr tvoid)))) :: (_hd, tuint) ::
               (_sz, tuint) :: (_tag, tuchar) :: (_j, tuint) ::
               (_t'3, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'2, tuchar) :: (_t'1, tuint) ::
               (_t'4, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Etempvar _scan (tptr (talignas 2%N (tptr tvoid)))))
  (Sloop
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Ederef (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid)))))
            (tptr (talignas 2%N (tptr tvoid)))))
        (Sifthenelse (Ebinop Olt
                       (Etempvar _s (tptr (talignas 2%N (tptr tvoid))))
                       (Etempvar _t'4 (tptr (talignas 2%N (tptr tvoid))))
                       tint)
          Sskip
          Sbreak))
      (Ssequence
        (Sset _hd
          (Ederef
            (Ecast (Etempvar _s (tptr (talignas 2%N (tptr tvoid))))
              (tptr tuint)) tuint))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _certicoq_block__get_size (Tfunction (Tcons tuint Tnil)
                                                tuint cc_default))
              ((Etempvar _hd tuint) :: nil))
            (Sset _sz (Etempvar _t'1 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _certicoq_block__get_tag (Tfunction (Tcons tuint Tnil)
                                                 tuchar cc_default))
                ((Etempvar _hd tuint) :: nil))
              (Sset _tag (Ecast (Etempvar _t'2 tuchar) tuchar)))
            (Ssequence
              (Sifthenelse (Eunop Onotbool
                             (Ebinop Oge (Etempvar _tag tuchar)
                               (Econst_int (Int.repr 251) tint) tint) tint)
                (Ssequence
                  (Sset _j (Econst_int (Int.repr 1) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _j tuint)
                                     (Etempvar _sz tuint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Scall (Some _t'3)
                          (Evar _certicoq_block__get_field_ptr (Tfunction
                                                                 (Tcons
                                                                   (tptr (talignas 2%N (tptr tvoid)))
                                                                   (Tcons
                                                                    tuint
                                                                    Tnil))
                                                                 (tptr (talignas 2%N (tptr tvoid)))
                                                                 cc_default))
                          ((Etempvar _s (tptr (talignas 2%N (tptr tvoid)))) ::
                           (Etempvar _j tuint) :: nil))
                        (Scall None
                          (Evar _forward (Tfunction
                                           (Tcons
                                             (tptr (talignas 2%N (tptr tvoid)))
                                             (Tcons
                                               (tptr (talignas 2%N (tptr tvoid)))
                                               (Tcons
                                                 (tptr (tptr (talignas 2%N (tptr tvoid))))
                                                 (Tcons
                                                   (tptr (talignas 2%N (tptr tvoid)))
                                                   (Tcons tint Tnil)))))
                                           tvoid cc_default))
                          ((Etempvar _from_start (tptr (talignas 2%N (tptr tvoid)))) ::
                           (Etempvar _from_limit (tptr (talignas 2%N (tptr tvoid)))) ::
                           (Etempvar _next (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
                           (Etempvar _t'3 (tptr (talignas 2%N (tptr tvoid)))) ::
                           (Econst_int (Int.repr 0) tint) :: nil))))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tuint)
                        (Econst_int (Int.repr 1) tint) tuint))))
                Sskip)
              (Sset _s
                (Ebinop Oadd (Etempvar _s (tptr (talignas 2%N (tptr tvoid))))
                  (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                    (Etempvar _sz tuint) tuint)
                  (tptr (talignas 2%N (tptr tvoid))))))))))
    Sskip))
|}.

Definition v___func____1 := {|
  gvar_info := (tarray tschar 14);
  gvar_init := (Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_do_generation := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_from, (tptr (Tstruct _space noattr))) ::
                (_to, (tptr (Tstruct _space noattr))) ::
                (_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_start, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_end, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'8, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'7, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'6, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
        (Tstruct _space noattr)) _next (tptr (talignas 2%N (tptr tvoid)))))
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
            (Tstruct _space noattr)) _next
          (tptr (talignas 2%N (tptr tvoid)))))
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _start
            (tptr (talignas 2%N (tptr tvoid)))))
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _limit
              (tptr (talignas 2%N (tptr tvoid)))))
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _next
                (tptr (talignas 2%N (tptr tvoid)))))
            (Sifthenelse (Ebinop Ole
                           (Ebinop Osub
                             (Etempvar _t'5 (tptr (talignas 2%N (tptr tvoid))))
                             (Etempvar _t'6 (tptr (talignas 2%N (tptr tvoid))))
                             tint)
                           (Ebinop Osub
                             (Etempvar _t'7 (tptr (talignas 2%N (tptr tvoid))))
                             (Etempvar _t'8 (tptr (talignas 2%N (tptr tvoid))))
                             tint) tint)
              Sskip
              (Scall None
                (Evar ___assert_fail (Tfunction
                                       (Tcons (tptr tschar)
                                         (Tcons (tptr tschar)
                                           (Tcons tuint
                                             (Tcons (tptr tschar) Tnil))))
                                       tvoid cc_default))
                ((Evar ___stringlit_3 (tarray tschar 45)) ::
                 (Evar ___stringlit_1 (tarray tschar 34)) ::
                 (Econst_int (Int.repr 233) tint) ::
                 (Evar ___func____1 (tarray tschar 14)) :: nil)))))))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _start
            (tptr (talignas 2%N (tptr tvoid)))))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _limit
              (tptr (talignas 2%N (tptr tvoid)))))
          (Scall None
            (Evar _forward_roots (Tfunction
                                   (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                     (Tcons
                                       (tptr (talignas 2%N (tptr tvoid)))
                                       (Tcons
                                         (tptr (tptr (talignas 2%N (tptr tvoid))))
                                         (Tcons (tptr tuint)
                                           (Tcons
                                             (tptr (Tstruct _thread_info noattr))
                                             Tnil))))) tvoid cc_default))
            ((Etempvar _t'3 (tptr (talignas 2%N (tptr tvoid)))) ::
             (Etempvar _t'4 (tptr (talignas 2%N (tptr tvoid)))) ::
             (Eaddrof
               (Efield
                 (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                   (Tstruct _space noattr)) _next
                 (tptr (talignas 2%N (tptr tvoid))))
               (tptr (tptr (talignas 2%N (tptr tvoid))))) ::
             (Etempvar _fi (tptr tuint)) ::
             (Etempvar _ti (tptr (Tstruct _thread_info noattr))) :: nil))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _start
              (tptr (talignas 2%N (tptr tvoid)))))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _limit
                (tptr (talignas 2%N (tptr tvoid)))))
            (Scall None
              (Evar _do_scan (Tfunction
                               (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                 (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                   (Tcons (tptr (talignas 2%N (tptr tvoid)))
                                     (Tcons
                                       (tptr (tptr (talignas 2%N (tptr tvoid))))
                                       Tnil)))) tvoid cc_default))
              ((Etempvar _t'1 (tptr (talignas 2%N (tptr tvoid)))) ::
               (Etempvar _t'2 (tptr (talignas 2%N (tptr tvoid)))) ::
               (Etempvar _p (tptr (talignas 2%N (tptr tvoid)))) ::
               (Eaddrof
                 (Efield
                   (Ederef (Etempvar _to (tptr (Tstruct _space noattr)))
                     (Tstruct _space noattr)) _next
                   (tptr (talignas 2%N (tptr tvoid))))
                 (tptr (tptr (talignas 2%N (tptr tvoid))))) :: nil))))
        (Ssequence
          (Sset _start
            (Efield
              (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _start
              (tptr (talignas 2%N (tptr tvoid)))))
          (Ssequence
            (Sset _end
              (Efield
                (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _end
                (tptr (talignas 2%N (tptr tvoid)))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _next
                  (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _start (tptr (talignas 2%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _from (tptr (Tstruct _space noattr)))
                    (Tstruct _space noattr)) _limit
                  (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _end (tptr (talignas 2%N (tptr tvoid))))))))))))
|}.

Definition f_create_space := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _space noattr))) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'1, (tptr tvoid)) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2 (Evar _MAX_SPACE_SIZE tuint))
    (Sifthenelse (Ebinop Oge (Etempvar _n tuint) (Etempvar _t'2 tuint) tint)
      (Scall None
        (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                            cc_default))
        ((Evar ___stringlit_4 (tarray tschar 43)) :: nil))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul (Etempvar _n tuint)
           (Esizeof (talignas 2%N (tptr tvoid)) tuint) tuint) :: nil))
      (Sset _p
        (Ecast (Etempvar _t'1 (tptr tvoid))
          (tptr (talignas 2%N (tptr tvoid))))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Scall None
          (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                              cc_default))
          ((Evar ___stringlit_5 (tarray tschar 38)) :: nil))
        Sskip)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
              (Tstruct _space noattr)) _start
            (tptr (talignas 2%N (tptr tvoid))))
          (Etempvar _p (tptr (talignas 2%N (tptr tvoid)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                (Tstruct _space noattr)) _next
              (tptr (talignas 2%N (tptr tvoid))))
            (Etempvar _p (tptr (talignas 2%N (tptr tvoid)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _limit
                (tptr (talignas 2%N (tptr tvoid))))
              (Ebinop Oadd (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _n tuint) (tptr (talignas 2%N (tptr tvoid)))))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _space noattr)))
                  (Tstruct _space noattr)) _end
                (tptr (talignas 2%N (tptr tvoid))))
              (Ebinop Oadd (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _n tuint) (tptr (talignas 2%N (tptr tvoid)))))))))))
|}.

Definition f_create_heap := {|
  fn_return := (tptr (Tstruct _heap noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_h, (tptr (Tstruct _heap noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _heap noattr) tuint) :: nil))
    (Sset _h
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _heap noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _heap noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Scall None
        (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                            cc_default))
        ((Evar ___stringlit_6 (tarray tschar 27)) :: nil))
      Sskip)
    (Ssequence
      (Scall None
        (Evar _create_space (Tfunction
                              (Tcons (tptr (Tstruct _space noattr))
                                (Tcons tuint Tnil)) tvoid cc_default))
        ((Ebinop Oadd
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
                    (tptr (talignas 2%N (tptr tvoid))))
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
                      (tptr (talignas 2%N (tptr tvoid))))
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
                        (tptr (talignas 2%N (tptr tvoid))))
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
                        (tptr (talignas 2%N (tptr tvoid))))
                      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sreturn (Some (Etempvar _h (tptr (Tstruct _heap noattr)))))))))
|}.

Definition f_make_tinfo := {|
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
      (Evar _create_heap (Tfunction Tnil (tptr (Tstruct _heap noattr))
                           cc_default)) nil)
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
          (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                              cc_default))
          ((Evar ___stringlit_7 (tarray tschar 39)) :: nil))
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

Definition v___func____2 := {|
  gvar_info := (tarray tschar 7);
  gvar_init := (Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_resume := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) ::
               (_lo, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_hi, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_num_allocs, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
        (Tstruct _thread_info noattr)) _heap (tptr (Tstruct _heap noattr))))
  (Ssequence
    (Sset _num_allocs
      (Ederef
        (Ebinop Oadd (Etempvar _fi (tptr tuint))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sifthenelse (Etempvar _h (tptr (Tstruct _heap noattr)))
        Sskip
        (Scall None
          (Evar ___assert_fail (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons (tptr tschar)
                                     (Tcons tuint (Tcons (tptr tschar) Tnil))))
                                 tvoid cc_default))
          ((Evar ___stringlit_8 (tarray tschar 2)) ::
           (Evar ___stringlit_1 (tarray tschar 34)) ::
           (Econst_int (Int.repr 314) tint) ::
           (Evar ___func____2 (tarray tschar 7)) :: nil)))
      (Ssequence
        (Sset _lo
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
              _limit (tptr (talignas 2%N (tptr tvoid)))))
          (Ssequence
            (Sifthenelse (Ebinop Olt
                           (Ebinop Osub
                             (Etempvar _hi (tptr (talignas 2%N (tptr tvoid))))
                             (Etempvar _lo (tptr (talignas 2%N (tptr tvoid))))
                             tint) (Etempvar _num_allocs tuint) tint)
              (Scall None
                (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                                    cc_default))
                ((Evar ___stringlit_9 (tarray tschar 48)) :: nil))
              Sskip)
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _alloc
                  (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _lo (tptr (talignas 2%N (tptr tvoid)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _ti (tptr (Tstruct _thread_info noattr)))
                    (Tstruct _thread_info noattr)) _limit
                  (tptr (talignas 2%N (tptr tvoid))))
                (Etempvar _hi (tptr (talignas 2%N (tptr tvoid))))))))))))
|}.

Definition f_garbage_collect := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_fi, (tptr tuint)) ::
                (_ti, (tptr (Tstruct _thread_info noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _heap noattr))) :: (_i, tint) ::
               (_w, tuint) :: (_t'7, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'6, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'5, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'4, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'3, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'2, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
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
                  (tptr (talignas 2%N (tptr tvoid)))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _t'5 (tptr (talignas 2%N (tptr tvoid))))
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
                        (tptr (talignas 2%N (tptr tvoid)))))
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
                          (tptr (talignas 2%N (tptr tvoid)))))
                      (Sset _w
                        (Ebinop Osub
                          (Etempvar _t'6 (tptr (talignas 2%N (tptr tvoid))))
                          (Etempvar _t'7 (tptr (talignas 2%N (tptr tvoid))))
                          tint))))
                  (Scall None
                    (Evar _create_space (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _space noattr))
                                            (Tcons tuint Tnil)) tvoid
                                          cc_default))
                    ((Ebinop Oadd
                       (Efield
                         (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                           (Tstruct _heap noattr)) _spaces
                         (tarray (Tstruct _space noattr) 12))
                       (Ebinop Oadd (Etempvar _i tint)
                         (Econst_int (Int.repr 1) tint) tint)
                       (tptr (Tstruct _space noattr))) ::
                     (Ebinop Omul (Econst_int (Int.repr 2) tint)
                       (Etempvar _w tuint) tuint) :: nil)))
                Sskip))
            (Ssequence
              (Scall None
                (Evar _do_generation (Tfunction
                                       (Tcons (tptr (Tstruct _space noattr))
                                         (Tcons
                                           (tptr (Tstruct _space noattr))
                                           (Tcons (tptr tuint)
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
                 (Etempvar _fi (tptr tuint)) ::
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
                    (tptr (talignas 2%N (tptr tvoid)))))
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
                      (tptr (talignas 2%N (tptr tvoid)))))
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
                        (tptr (talignas 2%N (tptr tvoid)))))
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
                          (tptr (talignas 2%N (tptr tvoid)))))
                      (Sifthenelse (Ebinop Ole
                                     (Ebinop Osub
                                       (Etempvar _t'1 (tptr (talignas 2%N (tptr tvoid))))
                                       (Etempvar _t'2 (tptr (talignas 2%N (tptr tvoid))))
                                       tint)
                                     (Ebinop Osub
                                       (Etempvar _t'3 (tptr (talignas 2%N (tptr tvoid))))
                                       (Etempvar _t'4 (tptr (talignas 2%N (tptr tvoid))))
                                       tint) tint)
                        (Ssequence
                          (Scall None
                            (Evar _resume (Tfunction
                                            (Tcons (tptr tuint)
                                              (Tcons
                                                (tptr (Tstruct _thread_info noattr))
                                                Tnil)) tvoid cc_default))
                            ((Etempvar _fi (tptr tuint)) ::
                             (Etempvar _ti (tptr (Tstruct _thread_info noattr))) ::
                             nil))
                          (Sreturn None))
                        Sskip))))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Scall None
      (Evar _abort_with (Tfunction (Tcons (tptr tschar) Tnil) tvoid
                          cc_default))
      ((Evar ___stringlit_10 (tarray tschar 24)) :: nil))))
|}.

Definition f_reset_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'2, (tptr (talignas 2%N (tptr tvoid)))) ::
               (_t'1, (tptr (talignas 2%N (tptr tvoid)))) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
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
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tuint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _start (tptr (talignas 2%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tuint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _next (tptr (talignas 2%N (tptr tvoid))))
            (Etempvar _t'2 (tptr (talignas 2%N (tptr tvoid))))))
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tuint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _end (tptr (talignas 2%N (tptr tvoid)))))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _h (tptr (Tstruct _heap noattr)))
                      (Tstruct _heap noattr)) _spaces
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tuint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _limit (tptr (talignas 2%N (tptr tvoid))))
            (Etempvar _t'1 (tptr (talignas 2%N (tptr tvoid))))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition f_free_heap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _heap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_p, (tptr (talignas 2%N (tptr tvoid)))) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
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
                    (tarray (Tstruct _space noattr) 12)) (Etempvar _i tuint)
                  (tptr (Tstruct _space noattr))) (Tstruct _space noattr))
              _start (tptr (talignas 2%N (tptr tvoid)))))
          (Sifthenelse (Ebinop One
                         (Etempvar _p (tptr (talignas 2%N (tptr tvoid))))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
              ((Etempvar _p (tptr (talignas 2%N (tptr tvoid)))) :: nil))
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Etempvar _h (tptr (Tstruct _heap noattr))) :: nil)))
|}.

Definition composites : list composite_definition :=
(Composite __IO_FILE Struct
   ((__flags, tint) :: (__IO_read_ptr, (tptr tschar)) ::
    (__IO_read_end, (tptr tschar)) :: (__IO_read_base, (tptr tschar)) ::
    (__IO_write_base, (tptr tschar)) :: (__IO_write_ptr, (tptr tschar)) ::
    (__IO_write_end, (tptr tschar)) :: (__IO_buf_base, (tptr tschar)) ::
    (__IO_buf_end, (tptr tschar)) :: (__IO_save_base, (tptr tschar)) ::
    (__IO_backup_base, (tptr tschar)) :: (__IO_save_end, (tptr tschar)) ::
    (__markers, (tptr (Tstruct __IO_marker noattr))) ::
    (__chain, (tptr (Tstruct __IO_FILE noattr))) :: (__fileno, tint) ::
    (__flags2, tint) :: (__old_offset, tint) :: (__cur_column, tushort) ::
    (__vtable_offset, tschar) :: (__shortbuf, (tarray tschar 1)) ::
    (__lock, (tptr tvoid)) :: (__offset, tlong) ::
    (__codecvt, (tptr (Tstruct __IO_codecvt noattr))) ::
    (__wide_data, (tptr (Tstruct __IO_wide_data noattr))) ::
    (__freeres_list, (tptr (Tstruct __IO_FILE noattr))) ::
    (__freeres_buf, (tptr tvoid)) :: (___pad5, tuint) :: (__mode, tint) ::
    (__unused2, (tarray tschar 40)) :: nil)
   noattr ::
 Composite _thread_info Struct
   ((_alloc, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_heap, (tptr (Tstruct _heap noattr))) ::
    (_args, (tarray (talignas 2%N (tptr tvoid)) 1024)) :: nil)
   noattr ::
 Composite _space Struct
   ((_start, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_next, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_limit, (tptr (talignas 2%N (tptr tvoid)))) ::
    (_end, (tptr (talignas 2%N (tptr tvoid)))) :: nil)
   noattr ::
 Composite _heap Struct
   ((_spaces, (tarray (Tstruct _space noattr) 12)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_9, Gvar v___stringlit_9) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_7, Gvar v___stringlit_7) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_8, Gvar v___stringlit_8) ::
 (___stringlit_10, Gvar v___stringlit_10) ::
 (___builtin_ais_annot,
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
 (_stderr, Gvar v_stderr) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct __IO_FILE noattr)) (Tcons (tptr tschar) Tnil))
     tint {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|})) ::
 (___assert_fail,
   Gfun(External (EF_external "__assert_fail"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tschar)
       (Tcons (tptr tschar) (Tcons tuint (Tcons (tptr tschar) Tnil)))) tvoid
     cc_default)) ::
 (_int_or_ptr__is_int,
   Gfun(External (EF_external "int_or_ptr__is_int"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (talignas 2%N (tptr tvoid)) Tnil) tint cc_default)) ::
 (_int_or_ptr__to_ptr,
   Gfun(External (EF_external "int_or_ptr__to_ptr"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (talignas 2%N (tptr tvoid)) Tnil) (tptr tvoid) cc_default)) ::
 (_int_or_ptr__of_ptr,
   Gfun(External (EF_external "int_or_ptr__of_ptr"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) (talignas 2%N (tptr tvoid)) cc_default)) ::
 (_certicoq_block__init,
   Gfun(External (EF_external "certicoq_block__init"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (talignas 2%N (tptr tvoid))) (Tcons tuint Tnil))
     (tptr (talignas 2%N (tptr tvoid))) cc_default)) ::
 (_certicoq_block__get_header,
   Gfun(External (EF_external "certicoq_block__get_header"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr (talignas 2%N (tptr tvoid))) Tnil) tuint cc_default)) ::
 (_certicoq_block__set_header,
   Gfun(External (EF_external "certicoq_block__set_header"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (talignas 2%N (tptr tvoid))) (Tcons tuint Tnil)) tvoid
     cc_default)) ::
 (_certicoq_block__get_size,
   Gfun(External (EF_external "certicoq_block__get_size"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (_certicoq_block__get_tag,
   Gfun(External (EF_external "certicoq_block__get_tag"
                   (mksignature (AST.Tint :: nil) AST.Tint8unsigned
                     cc_default)) (Tcons tuint Tnil) tuchar cc_default)) ::
 (_certicoq_block__get_field_ptr,
   Gfun(External (EF_external "certicoq_block__get_field_ptr"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (talignas 2%N (tptr tvoid))) (Tcons tuint Tnil))
     (tptr (talignas 2%N (tptr tvoid))) cc_default)) ::
 (_certicoq_block__get_field,
   Gfun(External (EF_external "certicoq_block__get_field"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (talignas 2%N (tptr tvoid))) (Tcons tuint Tnil))
     (talignas 2%N (tptr tvoid)) cc_default)) ::
 (_certicoq_block__set_field,
   Gfun(External (EF_external "certicoq_block__set_field"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (talignas 2%N (tptr tvoid)))
       (Tcons tuint (Tcons (talignas 2%N (tptr tvoid)) Tnil))) tvoid
     cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_MAX_SPACE_SIZE, Gvar v_MAX_SPACE_SIZE) ::
 (_abort_with, Gfun(Internal f_abort_with)) ::
 (_Is_block, Gfun(Internal f_Is_block)) ::
 (_Is_from, Gfun(Internal f_Is_from)) ::
 (_forward, Gfun(Internal f_forward)) :: (___func__, Gvar v___func__) ::
 (_forward_roots, Gfun(Internal f_forward_roots)) ::
 (_forward_remset, Gfun(Internal f_forward_remset)) ::
 (_do_scan, Gfun(Internal f_do_scan)) ::
 (___func____1, Gvar v___func____1) ::
 (_do_generation, Gfun(Internal f_do_generation)) ::
 (_create_space, Gfun(Internal f_create_space)) ::
 (_create_heap, Gfun(Internal f_create_heap)) ::
 (_make_tinfo, Gfun(Internal f_make_tinfo)) ::
 (___func____2, Gvar v___func____2) :: (_resume, Gfun(Internal f_resume)) ::
 (_garbage_collect, Gfun(Internal f_garbage_collect)) ::
 (_reset_heap, Gfun(Internal f_reset_heap)) ::
 (_free_heap, Gfun(Internal f_free_heap)) :: nil).

Definition public_idents : list ident :=
(_free_heap :: _reset_heap :: _garbage_collect :: _resume :: _make_tinfo ::
 _create_heap :: _create_space :: _do_generation :: _do_scan ::
 _forward_remset :: _forward_roots :: _forward :: _Is_from :: _Is_block ::
 _abort_with :: _MAX_SPACE_SIZE :: _exit :: _free :: _malloc ::
 _certicoq_block__set_field :: _certicoq_block__get_field ::
 _certicoq_block__get_field_ptr :: _certicoq_block__get_tag ::
 _certicoq_block__get_size :: _certicoq_block__set_header ::
 _certicoq_block__get_header :: _certicoq_block__init ::
 _int_or_ptr__of_ptr :: _int_or_ptr__to_ptr :: _int_or_ptr__is_int ::
 ___assert_fail :: _fprintf :: _stderr :: ___builtin_debug ::
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


(*\nInput hashes (sha256):\n\n0e597ca47ce2c843e4fdd36994e52e9dbe9aa5a71608e1e1f7e714a2a47a97a0  src/c/include/coq-vsu-gc/src/gc.c
6bea924bf5a3177230cf4c22ea8dd6268a47cff689bfb32c85c5c96177c566ad  src/c/include/coq-vsu-gc/gc.h
a9b18c1959df2cb5404306021e5256eb25c78c20ef9ec326a1cac75cea375fe7  src/c/include/coq-vsu-gc/mem.h\n*)
