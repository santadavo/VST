From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.4"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "crypto/mem.c"%string.
  Definition normalized := true.
End Info.

Definition _BIO_snprintf : ident := 101%positive.
Definition _BIO_vsnprintf : ident := 100%positive.
Definition _CRYPTO_memcmp : ident := 83%positive.
Definition _OPENSSL_cleanse : ident := 69%positive.
Definition _OPENSSL_free : ident := 70%positive.
Definition _OPENSSL_hash32 : ident := 88%positive.
Definition _OPENSSL_malloc : ident := 67%positive.
Definition _OPENSSL_memcpy : ident := 62%positive.
Definition _OPENSSL_memset : ident := 64%positive.
Definition _OPENSSL_realloc : ident := 75%positive.
Definition _OPENSSL_strcasecmp : ident := 95%positive.
Definition _OPENSSL_strdup : ident := 91%positive.
Definition _OPENSSL_strncasecmp : ident := 96%positive.
Definition _OPENSSL_strnlen : ident := 90%positive.
Definition _OPENSSL_tolower : ident := 92%positive.
Definition ___builtin_ais_annot : ident := 1%positive.
Definition ___builtin_annot : ident := 8%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_bswap : ident := 2%positive.
Definition ___builtin_bswap16 : ident := 4%positive.
Definition ___builtin_bswap32 : ident := 3%positive.
Definition ___builtin_bswap64 : ident := 34%positive.
Definition ___builtin_clz : ident := 35%positive.
Definition ___builtin_clzl : ident := 36%positive.
Definition ___builtin_clzll : ident := 37%positive.
Definition ___builtin_ctz : ident := 38%positive.
Definition ___builtin_ctzl : ident := 39%positive.
Definition ___builtin_ctzll : ident := 40%positive.
Definition ___builtin_debug : ident := 52%positive.
Definition ___builtin_fabs : ident := 5%positive.
Definition ___builtin_fmadd : ident := 43%positive.
Definition ___builtin_fmax : ident := 41%positive.
Definition ___builtin_fmin : ident := 42%positive.
Definition ___builtin_fmsub : ident := 44%positive.
Definition ___builtin_fnmadd : ident := 45%positive.
Definition ___builtin_fnmsub : ident := 46%positive.
Definition ___builtin_fsqrt : ident := 6%positive.
Definition ___builtin_membar : ident := 10%positive.
Definition ___builtin_memcpy_aligned : ident := 7%positive.
Definition ___builtin_nop : ident := 51%positive.
Definition ___builtin_read16_reversed : ident := 47%positive.
Definition ___builtin_read32_reversed : ident := 48%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition ___builtin_write16_reversed : ident := 49%positive.
Definition ___builtin_write32_reversed : ident := 50%positive.
Definition ___compcert_i64_dtos : ident := 19%positive.
Definition ___compcert_i64_dtou : ident := 20%positive.
Definition ___compcert_i64_sar : ident := 31%positive.
Definition ___compcert_i64_sdiv : ident := 25%positive.
Definition ___compcert_i64_shl : ident := 29%positive.
Definition ___compcert_i64_shr : ident := 30%positive.
Definition ___compcert_i64_smod : ident := 27%positive.
Definition ___compcert_i64_smulh : ident := 32%positive.
Definition ___compcert_i64_stod : ident := 21%positive.
Definition ___compcert_i64_stof : ident := 23%positive.
Definition ___compcert_i64_udiv : ident := 26%positive.
Definition ___compcert_i64_umod : ident := 28%positive.
Definition ___compcert_i64_umulh : ident := 33%positive.
Definition ___compcert_i64_utod : ident := 22%positive.
Definition ___compcert_i64_utof : ident := 24%positive.
Definition ___compcert_va_composite : ident := 18%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition _a : ident := 79%positive.
Definition _aa : ident := 93%positive.
Definition _args : ident := 99%positive.
Definition _b : ident := 80%positive.
Definition _bb : ident := 94%positive.
Definition _buf : ident := 97%positive.
Definition _c : ident := 63%positive.
Definition _dst : ident := 59%positive.
Definition _format : ident := 98%positive.
Definition _free : ident := 54%positive.
Definition _h : ident := 87%positive.
Definition _i : ident := 82%positive.
Definition _in : ident := 86%positive.
Definition _in_a : ident := 77%positive.
Definition _in_b : ident := 78%positive.
Definition _kOffsetBasis : ident := 85%positive.
Definition _kPrime : ident := 84%positive.
Definition _len : ident := 76%positive.
Definition _main : ident := 102%positive.
Definition _malloc : ident := 53%positive.
Definition _memcpy : ident := 56%positive.
Definition _memset : ident := 57%positive.
Definition _n : ident := 61%positive.
Definition _new_size : ident := 71%positive.
Definition _old_size : ident := 72%positive.
Definition _orig_ptr : ident := 68%positive.
Definition _ptr : ident := 66%positive.
Definition _ret : ident := 73%positive.
Definition _s : ident := 89%positive.
Definition _size : ident := 65%positive.
Definition _src : ident := 60%positive.
Definition _strlen : ident := 58%positive.
Definition _to_copy : ident := 74%positive.
Definition _vsnprintf : ident := 55%positive.
Definition _x : ident := 81%positive.
Definition _t'1 : ident := 103%positive.
Definition _t'2 : ident := 104%positive.
Definition _t'3 : ident := 105%positive.
Definition _t'4 : ident := 106%positive.

Definition f_OPENSSL_memcpy := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tvoid)) :: (_src, (tptr tvoid)) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _n tuint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Etempvar _dst (tptr tvoid))))
    Sskip)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _memcpy (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                      cc_default))
      ((Etempvar _dst (tptr tvoid)) :: (Etempvar _src (tptr tvoid)) ::
       (Etempvar _n tuint) :: nil))
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_OPENSSL_memset := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tvoid)) :: (_c, tint) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _n tuint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Etempvar _dst (tptr tvoid))))
    Sskip)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _memset (Tfunction
                      (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                      (tptr tvoid) cc_default))
      ((Etempvar _dst (tptr tvoid)) :: (Etempvar _c tint) ::
       (Etempvar _n tuint) :: nil))
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_OPENSSL_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_size, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ptr, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Ebinop Oadd (Etempvar _size tuint) (Econst_int (Int.repr 8) tint)
         tuint) :: nil))
    (Sset _ptr (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _ptr (tptr tvoid))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Sassign
        (Ederef (Ecast (Etempvar _ptr (tptr tvoid)) (tptr tuint)) tuint)
        (Etempvar _size tuint))
      (Sreturn (Some (Ebinop Oadd
                       (Ecast (Etempvar _ptr (tptr tvoid)) (tptr tuchar))
                       (Econst_int (Int.repr 8) tint) (tptr tuchar)))))))
|}.

Definition f_OPENSSL_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_orig_ptr, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ptr, (tptr tvoid)) :: (_size, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _orig_ptr (tptr tvoid))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sset _ptr
      (Ebinop Osub (Ecast (Etempvar _orig_ptr (tptr tvoid)) (tptr tuchar))
        (Econst_int (Int.repr 8) tint) (tptr tuchar)))
    (Ssequence
      (Sset _size
        (Ederef (Ecast (Etempvar _ptr (tptr tvoid)) (tptr tuint)) tuint))
      (Ssequence
        (Scall None
          (Evar _OPENSSL_cleanse (Tfunction
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil))
                                   tvoid cc_default))
          ((Etempvar _ptr (tptr tvoid)) ::
           (Ebinop Oadd (Etempvar _size tuint) (Econst_int (Int.repr 8) tint)
             tuint) :: nil))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _ptr (tptr tvoid)) :: nil))))))
|}.

Definition f_OPENSSL_realloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_orig_ptr, (tptr tvoid)) :: (_new_size, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ptr, (tptr tvoid)) :: (_old_size, tuint) ::
               (_ret, (tptr tvoid)) :: (_to_copy, tuint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _orig_ptr (tptr tvoid))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _OPENSSL_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                cc_default))
        ((Etempvar _new_size tuint) :: nil))
      (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))
    Sskip)
  (Ssequence
    (Sset _ptr
      (Ebinop Osub (Ecast (Etempvar _orig_ptr (tptr tvoid)) (tptr tuchar))
        (Econst_int (Int.repr 8) tint) (tptr tuchar)))
    (Ssequence
      (Sset _old_size
        (Ederef (Ecast (Etempvar _ptr (tptr tvoid)) (tptr tuint)) tuint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _OPENSSL_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                    cc_default))
            ((Etempvar _new_size tuint) :: nil))
          (Sset _ret (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _ret (tptr tvoid))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid))))
            Sskip)
          (Ssequence
            (Sset _to_copy (Etempvar _new_size tuint))
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _old_size tuint)
                             (Etempvar _to_copy tuint) tint)
                (Sset _to_copy (Etempvar _old_size tuint))
                Sskip)
              (Ssequence
                (Scall None
                  (Evar _memcpy (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                  (tptr tvoid) cc_default))
                  ((Etempvar _ret (tptr tvoid)) ::
                   (Etempvar _orig_ptr (tptr tvoid)) ::
                   (Etempvar _to_copy tuint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _OPENSSL_free (Tfunction (Tcons (tptr tvoid) Tnil)
                                          tvoid cc_default))
                    ((Etempvar _orig_ptr (tptr tvoid)) :: nil))
                  (Sreturn (Some (Etempvar _ret (tptr tvoid)))))))))))))
|}.

Definition f_OPENSSL_cleanse := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ptr, (tptr tvoid)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _OPENSSL_memset (Tfunction
                          (Tcons (tptr tvoid)
                            (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
                          cc_default))
  ((Etempvar _ptr (tptr tvoid)) :: (Econst_int (Int.repr 0) tint) ::
   (Etempvar _len tuint) :: nil))
|}.

Definition f_CRYPTO_memcmp := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_in_a, (tptr tvoid)) :: (_in_b, (tptr tvoid)) ::
                (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, (tptr tuchar)) :: (_b, (tptr tuchar)) :: (_x, tuchar) ::
               (_i, tuint) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _a (Etempvar _in_a (tptr tvoid)))
  (Ssequence
    (Sset _b (Etempvar _in_b (tptr tvoid)))
    (Ssequence
      (Sset _x (Ecast (Econst_int (Int.repr 0) tint) tuchar))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Etempvar _len tuint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Etempvar _a (tptr tuchar))
                      (Etempvar _i tuint) (tptr tuchar)) tuchar))
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd (Etempvar _b (tptr tuchar))
                        (Etempvar _i tuint) (tptr tuchar)) tuchar))
                  (Sset _x
                    (Ecast
                      (Ebinop Oor (Etempvar _x tuchar)
                        (Ebinop Oxor (Etempvar _t'1 tuchar)
                          (Etempvar _t'2 tuchar) tint) tint) tuchar)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint))))
        (Sreturn (Some (Etempvar _x tuchar)))))))
|}.

Definition v_kPrime := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 16777619) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_kOffsetBasis := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr (-2128831035)) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_OPENSSL_hash32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ptr, (tptr tvoid)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_in, (tptr tuchar)) :: (_h, tuint) :: (_i, tuint) ::
               (_t'2, tuchar) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _in (Etempvar _ptr (tptr tvoid)))
  (Ssequence
    (Sset _h (Evar _kOffsetBasis tuint))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Etempvar _len tuint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd (Etempvar _in (tptr tuchar))
                      (Etempvar _i tuint) (tptr tuchar)) tuchar))
                (Sset _h
                  (Ebinop Oxor (Etempvar _h tuint) (Etempvar _t'2 tuchar)
                    tuint)))
              (Ssequence
                (Sset _t'1 (Evar _kPrime tuint))
                (Sset _h
                  (Ebinop Omul (Etempvar _h tuint) (Etempvar _t'1 tuint)
                    tuint)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Sreturn (Some (Etempvar _h tuint))))))
|}.

Definition f_OPENSSL_strnlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _len tuint)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _s (tptr tschar)) (Etempvar _i tuint)
                (tptr tschar)) tschar))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tschar)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Etempvar _i tuint)))
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Sreturn (Some (Etempvar _len tuint))))
|}.

Definition f_OPENSSL_strdup := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tuint) :: (_ret, (tptr tschar)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tuint cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _len
      (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
        tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _OPENSSL_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                cc_default)) ((Etempvar _len tuint) :: nil))
      (Sset _ret (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _ret (tptr tschar))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip)
      (Ssequence
        (Scall None
          (Evar _OPENSSL_memcpy (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                  (tptr tvoid) cc_default))
          ((Etempvar _ret (tptr tschar)) :: (Etempvar _s (tptr tschar)) ::
           (Etempvar _len tuint) :: nil))
        (Sreturn (Some (Etempvar _ret (tptr tschar))))))))
|}.

Definition f_OPENSSL_tolower := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Oge (Etempvar _c tint)
                   (Econst_int (Int.repr 65) tint) tint)
      (Sset _t'1
        (Ecast
          (Ebinop Ole (Etempvar _c tint) (Econst_int (Int.repr 90) tint)
            tint) tbool))
      (Sset _t'1 (Econst_int (Int.repr 0) tint)))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Ebinop Oadd (Etempvar _c tint)
                       (Ebinop Osub (Econst_int (Int.repr 97) tint)
                         (Econst_int (Int.repr 65) tint) tint) tint)))
      Sskip))
  (Sreturn (Some (Etempvar _c tint))))
|}.

Definition f_OPENSSL_strcasecmp := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tschar)) :: (_b, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_aa, tint) :: (_bb, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'4, tschar) :: (_t'3, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tschar)) (Etempvar _i tuint)
                  (tptr tschar)) tschar))
            (Scall (Some _t'1)
              (Evar _OPENSSL_tolower (Tfunction (Tcons tint Tnil) tint
                                       cc_default))
              ((Etempvar _t'4 tschar) :: nil)))
          (Sset _aa (Etempvar _t'1 tint)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tschar))
                    (Etempvar _i tuint) (tptr tschar)) tschar))
              (Scall (Some _t'2)
                (Evar _OPENSSL_tolower (Tfunction (Tcons tint Tnil) tint
                                         cc_default))
                ((Etempvar _t'3 tschar) :: nil)))
            (Sset _bb (Etempvar _t'2 tint)))
          (Sifthenelse (Ebinop Olt (Etempvar _aa tint) (Etempvar _bb tint)
                         tint)
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
            (Sifthenelse (Ebinop Ogt (Etempvar _aa tint) (Etempvar _bb tint)
                           tint)
              (Sreturn (Some (Econst_int (Int.repr 1) tint)))
              (Sifthenelse (Ebinop Oeq (Etempvar _aa tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition f_OPENSSL_strncasecmp := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tschar)) :: (_b, (tptr tschar)) :: (_n, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_aa, tint) :: (_bb, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'4, tschar) :: (_t'3, tschar) :: nil);
  fn_body :=
(Ssequence
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
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Etempvar _a (tptr tschar))
                    (Etempvar _i tuint) (tptr tschar)) tschar))
              (Scall (Some _t'1)
                (Evar _OPENSSL_tolower (Tfunction (Tcons tint Tnil) tint
                                         cc_default))
                ((Etempvar _t'4 tschar) :: nil)))
            (Sset _aa (Etempvar _t'1 tint)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Etempvar _b (tptr tschar))
                      (Etempvar _i tuint) (tptr tschar)) tschar))
                (Scall (Some _t'2)
                  (Evar _OPENSSL_tolower (Tfunction (Tcons tint Tnil) tint
                                           cc_default))
                  ((Etempvar _t'3 tschar) :: nil)))
              (Sset _bb (Etempvar _t'2 tint)))
            (Sifthenelse (Ebinop Olt (Etempvar _aa tint) (Etempvar _bb tint)
                           tint)
              (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
              (Sifthenelse (Ebinop Ogt (Etempvar _aa tint)
                             (Etempvar _bb tint) tint)
                (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                (Sifthenelse (Ebinop Oeq (Etempvar _aa tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_BIO_snprintf := {|
  fn_return := tint;
  fn_callconv := {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|};
  fn_params := ((_buf, (tptr tschar)) :: (_n, tuint) ::
                (_format, (tptr tschar)) :: nil);
  fn_vars := ((_args, (tptr tvoid)) :: nil);
  fn_temps := ((_ret, tint) :: (_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar ___builtin_va_start (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
    ((Eaddrof (Evar _args (tptr tvoid)) (tptr (tptr tvoid))) :: nil))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'2 (Evar _args (tptr tvoid)))
        (Scall (Some _t'1)
          (Evar _BIO_vsnprintf (Tfunction
                                 (Tcons (tptr tschar)
                                   (Tcons tuint
                                     (Tcons (tptr tschar)
                                       (Tcons (tptr tvoid) Tnil)))) tint
                                 cc_default))
          ((Etempvar _buf (tptr tschar)) :: (Etempvar _n tuint) ::
           (Etempvar _format (tptr tschar)) ::
           (Etempvar _t'2 (tptr tvoid)) :: nil)))
      (Sset _ret (Etempvar _t'1 tint)))
    (Sreturn (Some (Etempvar _ret tint)))))
|}.

Definition f_BIO_vsnprintf := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_buf, (tptr tschar)) :: (_n, tuint) ::
                (_format, (tptr tschar)) :: (_args, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _vsnprintf (Tfunction
                       (Tcons (tptr tschar)
                         (Tcons tuint
                           (Tcons (tptr tschar) (Tcons (tptr tvoid) Tnil))))
                       tint cc_default))
    ((Etempvar _buf (tptr tschar)) :: (Etempvar _n tuint) ::
     (Etempvar _format (tptr tschar)) :: (Etempvar _args (tptr tvoid)) ::
     nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_vsnprintf,
   Gfun(External (EF_external "vsnprintf"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tschar)
       (Tcons tuint (Tcons (tptr tschar) (Tcons (tptr tvoid) Tnil)))) tint
     cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_strlen,
   Gfun(External (EF_external "strlen"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tschar) Tnil) tuint cc_default)) ::
 (_OPENSSL_memcpy, Gfun(Internal f_OPENSSL_memcpy)) ::
 (_OPENSSL_memset, Gfun(Internal f_OPENSSL_memset)) ::
 (_OPENSSL_malloc, Gfun(Internal f_OPENSSL_malloc)) ::
 (_OPENSSL_free, Gfun(Internal f_OPENSSL_free)) ::
 (_OPENSSL_realloc, Gfun(Internal f_OPENSSL_realloc)) ::
 (_OPENSSL_cleanse, Gfun(Internal f_OPENSSL_cleanse)) ::
 (_CRYPTO_memcmp, Gfun(Internal f_CRYPTO_memcmp)) ::
 (_kPrime, Gvar v_kPrime) :: (_kOffsetBasis, Gvar v_kOffsetBasis) ::
 (_OPENSSL_hash32, Gfun(Internal f_OPENSSL_hash32)) ::
 (_OPENSSL_strnlen, Gfun(Internal f_OPENSSL_strnlen)) ::
 (_OPENSSL_strdup, Gfun(Internal f_OPENSSL_strdup)) ::
 (_OPENSSL_tolower, Gfun(Internal f_OPENSSL_tolower)) ::
 (_OPENSSL_strcasecmp, Gfun(Internal f_OPENSSL_strcasecmp)) ::
 (_OPENSSL_strncasecmp, Gfun(Internal f_OPENSSL_strncasecmp)) ::
 (_BIO_snprintf, Gfun(Internal f_BIO_snprintf)) ::
 (_BIO_vsnprintf, Gfun(Internal f_BIO_vsnprintf)) :: nil).

Definition public_idents : list ident :=
(_BIO_vsnprintf :: _BIO_snprintf :: _OPENSSL_strncasecmp ::
 _OPENSSL_strcasecmp :: _OPENSSL_tolower :: _OPENSSL_strdup ::
 _OPENSSL_strnlen :: _OPENSSL_hash32 :: _CRYPTO_memcmp :: _OPENSSL_cleanse ::
 _OPENSSL_realloc :: _OPENSSL_free :: _OPENSSL_malloc :: _strlen ::
 _memset :: _memcpy :: _vsnprintf :: _free :: _malloc :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


