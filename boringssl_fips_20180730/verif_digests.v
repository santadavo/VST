Require Import boringssl_fips_20180730.spec_digest_base.
Require Import boringssl_fips_20180730.thread_none.
Require Import boringssl_fips_20180730.digests.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition EVP_do_init_SPEC (x:ident) (D:EVP_MD) := 
DECLARE x
  WITH gv:globals, p:val, sh:share
  PRE [ _out OF tptr (Tstruct _env_md_st noattr) ]
     PROP (writable_share sh)
     LOCAL (gvars gv; temp _out p)
     SEP (data_at_ sh (Tstruct _env_md_st noattr) p)
  POST [ tvoid ]
    PROP () 
    LOCAL ()
    SEP (EVP_MD_rep D p).

Definition EVP_md4_do_init_SPEC := EVP_do_init_SPEC _EVP_md4_do_init md4_md.
Definition EVP_md5_do_init_SPEC := EVP_do_init_SPEC _EVP_md5_do_init md5_md.
Definition EVP_sha1_do_init_SPEC := EVP_do_init_SPEC _EVP_sha1_do_init sha1_md.
Definition EVP_sha224_do_init_SPEC := EVP_do_init_SPEC _EVP_sha224_do_init sha224_md.
Definition EVP_sha256_do_init_SPEC := EVP_do_init_SPEC _EVP_sha256_do_init sha256_md.
Definition EVP_sha384_do_init_SPEC := EVP_do_init_SPEC _EVP_sha384_do_init sha384_md.
Definition EVP_sha512_do_init_SPEC := EVP_do_init_SPEC _EVP_sha512_do_init sha512_md.
Definition EVP_md5_sha1_do_init_SPEC := EVP_do_init_SPEC _EVP_md5_sha1_do_init md5_sha1_md.

Definition md4_init_SPEC := DECLARE _md4_init (init_spec md4_md).
Definition md4_update_SPEC := DECLARE _md4_update (update_spec md4_md).
Definition md4_final_SPEC := DECLARE _md4_final (final_spec md4_md).
Definition Gprog_md4_do_init: funspecs := [md4_init_SPEC; md4_update_SPEC; md4_final_SPEC].

Definition md5_init_SPEC := DECLARE _md5_init (init_spec md5_md).
Definition md5_update_SPEC := DECLARE _md5_update (update_spec md5_md).
Definition md5_final_SPEC := DECLARE _md5_final (final_spec md5_md).
Definition Gprog_md5_do_init: funspecs := [md5_init_SPEC; md5_update_SPEC; md5_final_SPEC].

Definition sha1_init_SPEC := DECLARE _sha1_init (init_spec sha1_md).
Definition sha1_update_SPEC := DECLARE _sha1_update (update_spec sha1_md).
Definition sha1_final_SPEC := DECLARE _sha1_final (final_spec sha1_md).
Definition Gprog_sha1_do_init: funspecs := [sha1_init_SPEC; sha1_update_SPEC; sha1_final_SPEC].

Definition sha224_init_SPEC := DECLARE _sha224_init (init_spec sha224_md).
Definition sha224_update_SPEC := DECLARE _sha224_update (update_spec sha224_md).
Definition sha224_final_SPEC := DECLARE _sha224_final (final_spec sha224_md).
Definition Gprog_sha224_do_init: funspecs := [sha224_init_SPEC; sha224_update_SPEC; sha224_final_SPEC].

Definition sha256_init_SPEC := DECLARE _sha256_init (init_spec sha256_md).
Definition sha256_update_SPEC := DECLARE _sha256_update (update_spec sha256_md).
Definition sha256_final_SPEC := DECLARE _sha256_final (final_spec sha256_md).
Definition Gprog_sha256_do_init: funspecs := [sha256_init_SPEC; sha256_update_SPEC; sha256_final_SPEC].

Definition sha384_init_SPEC := DECLARE _sha384_init (init_spec sha384_md).
Definition sha384_update_SPEC := DECLARE _sha384_update (update_spec sha384_md).
Definition sha384_final_SPEC := DECLARE _sha384_final (final_spec sha384_md).
Definition Gprog_sha384_do_init: funspecs := [sha384_init_SPEC; sha384_update_SPEC; sha384_final_SPEC].

Definition sha512_init_SPEC := DECLARE _sha512_init (init_spec sha512_md).
Definition sha512_update_SPEC := DECLARE _sha512_update (update_spec sha512_md).
Definition sha512_final_SPEC := DECLARE _sha512_final (final_spec sha512_md).
Definition Gprog_sha512_do_init: funspecs := [sha512_init_SPEC; sha512_update_SPEC; sha512_final_SPEC].

Definition md5_sha1_init_SPEC := DECLARE _md5_sha1_init (init_spec md5_sha1_md).
Definition md5_sha1_update_SPEC := DECLARE _md5_sha1_update (update_spec md5_sha1_md).
Definition md5_sha1_final_SPEC := DECLARE _md5_sha1_final (final_spec md5_sha1_md).
Definition Gprog_md5_sha1_do_init: funspecs := [md5_sha1_init_SPEC; md5_sha1_update_SPEC; md5_sha1_final_SPEC].
(*
Ltac verif_do_init :=
  start_function; do 9 forward; unfold EVP_MD_rep;
  let z := fresh "z" in
  evar (z: reptype (Tstruct _env_md_st noattr));
  match goal with [ sh : share |- ?P ] => 
    Exists sh z; subst z; entailer!; simpl; intuition
  end.*)

Ltac verif_do_init i u f :=
  start_function;
  make_func_ptr i; make_func_ptr u; make_func_ptr f;
  do 9 forward; unfold EVP_MD_rep;
  let z := fresh "z" in
  evar (z: reptype (Tstruct _env_md_st noattr));
  match goal with [ sh : share |- ?P ] => 
    Exists sh z; subst z; entailer!; simpl; entailer!
  end.

Lemma body_EVP_md4_do_init: semax_body Vprog Gprog_md4_do_init f_EVP_md4_do_init EVP_md4_do_init_SPEC.
Proof. verif_do_init _md4_init _md4_update _md4_final. Qed.

Lemma body_EVP_md5_do_init: semax_body Vprog Gprog_md5_do_init f_EVP_md5_do_init EVP_md5_do_init_SPEC.
Proof. verif_do_init _md5_init _md5_update _md5_final. Qed.

Lemma body_EVP_sha1_do_init: semax_body Vprog Gprog_sha1_do_init f_EVP_sha1_do_init EVP_sha1_do_init_SPEC.
Proof. verif_do_init _sha1_init _sha1_update _sha1_final. Qed.

Lemma body_EVP_sha224_do_init: semax_body Vprog Gprog_sha224_do_init f_EVP_sha224_do_init EVP_sha224_do_init_SPEC.
Proof. verif_do_init _sha224_init _sha224_update _sha224_final. Qed.

Lemma body_EVP_sha256_do_init: semax_body Vprog Gprog_sha256_do_init f_EVP_sha256_do_init EVP_sha256_do_init_SPEC.
Proof. verif_do_init _sha256_init _sha256_update _sha256_final. Qed.

Lemma body_EVP_sha384_do_init: semax_body Vprog Gprog_sha384_do_init f_EVP_sha384_do_init EVP_sha384_do_init_SPEC.
Proof. verif_do_init _sha384_init _sha384_update _sha384_final. Qed.

Lemma body_EVP_sha512_do_init: semax_body Vprog Gprog_sha512_do_init f_EVP_sha512_do_init EVP_sha512_do_init_SPEC.
Proof. verif_do_init _sha512_init _sha512_update _sha512_final. Qed.

Lemma body_EVP_md5_sha1_do_init: semax_body Vprog Gprog_md5_sha1_do_init f_EVP_md5_sha1_do_init EVP_md5_sha1_do_init_SPEC.
Proof. verif_do_init _md5_sha1_init _md5_sha1_update _md5_sha1_final. Qed.

Definition EVP_storage_bss_get_SPEC (f g: ident):= 
DECLARE f
  WITH gv:globals
  PRE [ ] PROP () LOCAL (gvars gv) SEP ()
  POST [ tptr (Tstruct _env_md_st noattr) ]
    PROP () LOCAL (temp ret_temp (gv g)) SEP ().

Definition EVP_md4_storage_bss_get_SPEC := EVP_storage_bss_get_SPEC _EVP_md4_storage_bss_get _EVP_md4_storage.
Definition EVP_md5_storage_bss_get_SPEC := EVP_storage_bss_get_SPEC _EVP_md5_storage_bss_get _EVP_md5_storage.
Definition EVP_sha1_storage_bss_get_SPEC := EVP_storage_bss_get_SPEC _EVP_sha1_storage_bss_get _EVP_sha1_storage.
Definition EVP_sha224_storage_bss_get_SPEC := EVP_storage_bss_get_SPEC _EVP_sha224_storage_bss_get _EVP_sha224_storage.
Definition EVP_sha256_storage_bss_get_SPEC := EVP_storage_bss_get_SPEC _EVP_sha256_storage_bss_get _EVP_sha256_storage.
Definition EVP_sha384_storage_bss_get_SPEC := EVP_storage_bss_get_SPEC _EVP_sha384_storage_bss_get _EVP_sha384_storage.
Definition EVP_sha512_storage_bss_get_SPEC := EVP_storage_bss_get_SPEC _EVP_sha512_storage_bss_get _EVP_sha512_storage.
Definition EVP_md5_sha1_storage_bss_get_SPEC := EVP_storage_bss_get_SPEC _EVP_md5_sha1_storage_bss_get _EVP_md5_sha1_storage.

Lemma body_EVP_md4_storage_bss_get: semax_body Vprog EmptyGprog f_EVP_md4_storage_bss_get EVP_md4_storage_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_md5_storage_bss_get: semax_body Vprog EmptyGprog f_EVP_md5_storage_bss_get EVP_md5_storage_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha1_storage_bss_get: semax_body Vprog EmptyGprog f_EVP_sha1_storage_bss_get EVP_sha1_storage_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha224_storage_bss_get: semax_body Vprog EmptyGprog f_EVP_sha224_storage_bss_get EVP_sha224_storage_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha256_storage_bss_get: semax_body Vprog EmptyGprog f_EVP_sha256_storage_bss_get EVP_sha256_storage_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha386_storage_bss_get: semax_body Vprog EmptyGprog f_EVP_sha384_storage_bss_get EVP_sha384_storage_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha512_storage_bss_get: semax_body Vprog EmptyGprog f_EVP_sha512_storage_bss_get EVP_sha512_storage_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_md5_sha1_storage_bss_get: semax_body Vprog EmptyGprog f_EVP_md5_sha1_storage_bss_get EVP_md5_sha1_storage_bss_get_SPEC.
Proof. start_function. forward. Qed.

Definition EVP_init_PRE (D:EVP_MD) (g: ident) gv := EX sh:share, !!(writable_share sh) && data_at_ sh (Tstruct _env_md_st noattr) (gv g).
Definition EVP_init_POST (D:EVP_MD) (g: ident) gv:= EVP_MD_rep D (gv g).

Definition EVP_init_SPEC (D:EVP_MD) (f g: ident):= 
DECLARE f
  WITH gv:globals
  PRE [ ] PROP ()
     LOCAL (gvars gv) 
     SEP (EVP_init_PRE D g gv) 
  POST [ tvoid ]
    PROP () LOCAL () SEP (EVP_init_POST D g gv). 

Definition EVP_md4_init_SPEC:= EVP_init_SPEC md4_md _EVP_md4_init _EVP_md4_storage.
Definition md4_init_Gprog:funspecs := [EVP_md4_storage_bss_get_SPEC; EVP_md4_do_init_SPEC].
Lemma body_EVP_md4_init: semax_body Vprog md4_init_Gprog f_EVP_md4_init EVP_md4_init_SPEC.
Proof. start_function. unfold EVP_init_PRE; Intros sh. forward_call gv. forward_call (gv, gv _EVP_md4_storage, sh). forward. Qed.

Definition EVP_md5_init_SPEC:= EVP_init_SPEC md5_md _EVP_md5_init _EVP_md5_storage.
Definition md5_init_Gprog:funspecs := [EVP_md5_storage_bss_get_SPEC; EVP_md5_do_init_SPEC].
Lemma body_EVP_md5_init: semax_body Vprog md5_init_Gprog f_EVP_md5_init EVP_md5_init_SPEC.
Proof. start_function. unfold EVP_init_PRE; Intros sh. forward_call gv. forward_call (gv, gv _EVP_md5_storage, sh). forward. Qed.

Definition EVP_sha1_init_SPEC:= EVP_init_SPEC sha1_md _EVP_sha1_init _EVP_sha1_storage.
Definition sha1_init_Gprog:funspecs := [EVP_sha1_storage_bss_get_SPEC; EVP_sha1_do_init_SPEC].
Lemma body_EVP_sha1_init: semax_body Vprog sha1_init_Gprog f_EVP_sha1_init EVP_sha1_init_SPEC.
Proof. start_function. unfold EVP_init_PRE; Intros sh. forward_call gv. forward_call (gv, gv _EVP_sha1_storage, sh). forward. Qed.

Definition EVP_sha224_init_SPEC:= EVP_init_SPEC sha224_md _EVP_sha224_init _EVP_sha224_storage.
Definition sha224_init_Gprog:funspecs := [EVP_sha224_storage_bss_get_SPEC; EVP_sha224_do_init_SPEC].
Lemma body_EVP_sha224_init: semax_body Vprog sha224_init_Gprog f_EVP_sha224_init EVP_sha224_init_SPEC.
Proof. start_function. unfold EVP_init_PRE; Intros sh. forward_call gv. forward_call (gv, gv _EVP_sha224_storage, sh). forward. Qed.

Definition EVP_sha256_init_SPEC:= EVP_init_SPEC sha256_md _EVP_sha256_init _EVP_sha256_storage.
Definition sha256_init_Gprog:funspecs := [EVP_sha256_storage_bss_get_SPEC; EVP_sha256_do_init_SPEC].
Lemma body_EVP_sha256_init: semax_body Vprog sha256_init_Gprog f_EVP_sha256_init EVP_sha256_init_SPEC.
Proof. start_function. unfold EVP_init_PRE; Intros sh. forward_call gv. forward_call (gv, gv _EVP_sha256_storage, sh). forward. Qed.

Definition EVP_sha384_init_SPEC:= EVP_init_SPEC sha384_md _EVP_sha384_init _EVP_sha384_storage.
Definition sha384_init_Gprog:funspecs := [EVP_sha384_storage_bss_get_SPEC; EVP_sha384_do_init_SPEC].
Lemma body_EVP_sha384_init: semax_body Vprog sha384_init_Gprog f_EVP_sha384_init EVP_sha384_init_SPEC.
Proof. start_function. unfold EVP_init_PRE; Intros sh. forward_call gv. forward_call (gv, gv _EVP_sha384_storage, sh). forward. Qed.

Definition EVP_sha512_init_SPEC:= EVP_init_SPEC sha512_md _EVP_sha512_init _EVP_sha512_storage.
Definition sha512_init_Gprog:funspecs := [EVP_sha512_storage_bss_get_SPEC; EVP_sha512_do_init_SPEC].
Lemma body_EVP_sha512_init: semax_body Vprog sha512_init_Gprog f_EVP_sha512_init EVP_sha512_init_SPEC.
Proof. start_function. unfold EVP_init_PRE; Intros sh. forward_call gv. forward_call (gv, gv _EVP_sha512_storage, sh). forward. Qed.

Definition EVP_md5_sha1_init_SPEC:= EVP_init_SPEC md5_sha1_md _EVP_md5_sha1_init _EVP_md5_sha1_storage.
Definition md5_sha1_init_Gprog:funspecs := [EVP_md5_sha1_storage_bss_get_SPEC; EVP_md5_sha1_do_init_SPEC].
Lemma body_EVP_md5_sha1_init: semax_body Vprog md5_sha1_init_Gprog f_EVP_md5_sha1_init EVP_md5_sha1_init_SPEC.
Proof. start_function. unfold EVP_init_PRE; Intros sh. forward_call gv. forward_call (gv, gv _EVP_md5_sha1_storage, sh). forward. Qed.

Definition EVP_once_bss_get_SPEC (f g: ident):= 
DECLARE f
  WITH gv:globals
  PRE [ ] PROP () LOCAL (gvars gv) SEP ()
  POST [ tptr tuint ]
    PROP () LOCAL (temp ret_temp (gv g)) SEP ().

Definition EVP_md4_once_bss_get_SPEC := EVP_once_bss_get_SPEC _EVP_md4_once_bss_get _EVP_md4_once.
Definition EVP_md5_once_bss_get_SPEC := EVP_once_bss_get_SPEC _EVP_md5_once_bss_get _EVP_md5_once.
Definition EVP_sha1_once_bss_get_SPEC := EVP_once_bss_get_SPEC _EVP_sha1_once_bss_get _EVP_sha1_once.
Definition EVP_sha224_once_bss_get_SPEC := EVP_once_bss_get_SPEC _EVP_sha224_once_bss_get _EVP_sha224_once.
Definition EVP_sha256_once_bss_get_SPEC := EVP_once_bss_get_SPEC _EVP_sha256_once_bss_get _EVP_sha256_once.
Definition EVP_sha384_once_bss_get_SPEC := EVP_once_bss_get_SPEC _EVP_sha384_once_bss_get _EVP_sha384_once.
Definition EVP_sha512_once_bss_get_SPEC := EVP_once_bss_get_SPEC _EVP_sha512_once_bss_get _EVP_sha512_once.
Definition EVP_md5_sha1_once_bss_get_SPEC := EVP_once_bss_get_SPEC _EVP_md5_sha1_once_bss_get _EVP_md5_sha1_once.

Lemma body_EVP_md4_once_bss_get: semax_body Vprog EmptyGprog f_EVP_md4_once_bss_get EVP_md4_once_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_md5_once_bss_get: semax_body Vprog EmptyGprog f_EVP_md5_once_bss_get EVP_md5_once_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha1_once_bss_get: semax_body Vprog EmptyGprog f_EVP_sha1_once_bss_get EVP_sha1_once_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha224_once_bss_get: semax_body Vprog EmptyGprog f_EVP_sha224_once_bss_get EVP_sha224_once_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha256_once_bss_get: semax_body Vprog EmptyGprog f_EVP_sha256_once_bss_get EVP_sha256_once_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha386_once_bss_get: semax_body Vprog EmptyGprog f_EVP_sha384_once_bss_get EVP_sha384_once_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_sha512_once_bss_get: semax_body Vprog EmptyGprog f_EVP_sha512_once_bss_get EVP_sha512_once_bss_get_SPEC.
Proof. start_function. forward. Qed.

Lemma body_EVP_md5_sha1_once_bss_get: semax_body Vprog EmptyGprog f_EVP_md5_sha1_once_bss_get EVP_md5_sha1_once_bss_get_SPEC.
Proof. start_function. forward. Qed.

Definition IFZ_mpred (i:int) (P Q:mpred): mpred :=
  if Int.eq i Int.zero then P else Q.

(*
Definition simple_CRYPTO_ONCE_SubjectSPEC (P Q: mpred):funspec :=
  WITH a:unit
  PRE [] PROP () LOCAL () SEP (P)
  POST [tvoid] PROP () LOCAL () SEP (Q).

Definition simple_CRYPTO_once_SPEC P Q:= 
DECLARE _CRYPTO_once
  WITH i:int, once:val, init:val, osh:share
  PRE [ _once OF tptr tuint,
        _init OF tptr (Tfunction Tnil tvoid cc_default) ]
      PROP (writable_share osh) LOCAL (temp _once once; temp _init init) 
      SEP (data_at osh tuint (Vint i) once; IFZ_mpred i P Q; func_ptr' (simple_CRYPTO_ONCE_SubjectSPEC P Q) init )
  POST [ tvoid ]
    EX j:int,
    PROP (j <> Int.zero) LOCAL () SEP (data_at osh tuint (Vint j) once; Q; func_ptr' (simple_CRYPTO_ONCE_SubjectSPEC P Q) init).

Lemma simple_body_CRYPTO_once P Q: semax_body Vprog EmptyGprog f_CRYPTO_once (simple_CRYPTO_once_SPEC P Q).
Proof. start_function.
forward.
  forward_if (PROP (i=Int.zero) LOCAL (temp _t'1 (Vint i); temp _once once; temp _init init)
      SEP (data_at osh tuint (Vint i) once; P; func_ptr' (simple_CRYPTO_ONCE_SubjectSPEC P Q) init)).
+ forward. Exists i. entailer!. unfold IFZ_mpred. rewrite Int.eq_false; trivial.
+ forward. entailer!. unfold IFZ_mpred. rewrite Int.eq_true. trivial.
+ Intros; subst. forward. forward_call tt. forward. Exists (Int.repr 1). entailer!. inv H1.
Qed.
*)
Definition CRYPTO_ONCE_SubjectSPEC (P Q: globals -> mpred):funspec :=
  WITH gv:globals
  PRE [] PROP () LOCAL (gvars gv) SEP (P gv)
  POST [tvoid] PROP () LOCAL () SEP (Q gv).

Definition CRYPTO_once_SPEC P Q:= 
DECLARE _CRYPTO_once
  WITH i:int, once:val, init:val, osh:share, gv:globals
  PRE [ _once OF tptr tuint,
        _init OF tptr (Tfunction Tnil tvoid cc_default) ]
      PROP (writable_share osh) LOCAL (temp _once once; temp _init init; gvars gv) 
      SEP (data_at osh tuint (Vint i) once; IFZ_mpred i (P gv) (Q gv); func_ptr' (CRYPTO_ONCE_SubjectSPEC P Q) init )
  POST [ tvoid ]
    EX j:int,
    PROP (j <> Int.zero) LOCAL () SEP (data_at osh tuint (Vint j) once; Q gv; func_ptr' (CRYPTO_ONCE_SubjectSPEC P Q) init).

Lemma body_CRYPTO_once P Q: semax_body Vprog EmptyGprog thread_none.f_CRYPTO_once (CRYPTO_once_SPEC P Q).
Proof. start_function.
forward.
  forward_if (
      PROP (i=Int.zero) 
      LOCAL ((*temp thread_none._t'1 (Vint i);*) temp _once once; temp _init init; gvars gv)
      SEP (data_at osh tuint (Vint i) once; P gv; func_ptr' (CRYPTO_ONCE_SubjectSPEC P Q) init)).
+ forward. Exists i. entailer!. unfold IFZ_mpred. rewrite Int.eq_false; trivial.
+ forward. entailer.
+ Intros; subst. forward. forward_call gv. forward. Exists (Int.repr 1). entailer!. inv H1.
Qed.

Definition EVP_digest_SPEC D (f once storage: ident):= 
DECLARE f
  WITH gv:globals,i:int
  PRE [ ] PROP () 
          LOCAL (gvars gv) 
          SEP (data_at Tsh tuint (Vint i) (gv once);
               IFZ_mpred i (EVP_init_PRE D storage gv) (EVP_init_POST D storage gv))
  POST [ tptr (Tstruct _env_md_st noattr) ]
    EX rv:int,
    PROP (rv <> Int.zero) LOCAL (temp ret_temp (gv storage))
    SEP (EVP_MD_rep D (gv storage); data_at Tsh tuint (Vint rv) (gv once)).

Definition EVP_md4_SPEC:= EVP_digest_SPEC md4_md _EVP_md4 _EVP_md4_once _EVP_md4_storage.

Definition EVP_md4_Gprog:funspecs :=
 [EVP_md4_once_bss_get_SPEC; 
  CRYPTO_once_SPEC (EVP_init_PRE md4_md _EVP_md4_storage)
                   (EVP_init_POST md4_md _EVP_md4_storage);
  EVP_md4_init_SPEC; EVP_md4_storage_bss_get_SPEC].

(*explicit version of proof:
Lemma body_EVP_md4: semax_body Vprog EVP_md4_Gprog f_EVP_md4 EVP_md4_SPEC.
Proof. start_function.
  forward_call gv.
  make_func_ptr _EVP_md4_init.
  forward_call (i, gv _EVP_md4_once, gv _EVP_md4_init, Tsh, gv).
  assert (FR: Frame=[]); subst Frame; [reflexivity | simpl].
  cancel. apply derives_refl.
  Intros rv.
  forward_call gv.
  forward. Exists rv. entailer!. unfold EVP_init_POST. cancel. apply andp_left2 ; trivial.
Qed.*)

Ltac verif_body_EVP_digest f once storage := 
start_function;
match goal with [ gv : globals |- ?P ] =>
match goal with [ i : int |- ?P ] =>
  forward_call gv;
  make_func_ptr f;
  forward_call (i, gv once, gv f, Tsh, gv);
  [ (*assert (FR: Frame=[]); subst Frame; [reflexivity | simpl; cancel; apply derives_refl]*)
     rewrite <- sepcon_emp at 1; apply sepcon_derives; [ apply derives_refl | cancel ]
  | Intros rv;
    match goal with [ H: ?rv <> Int.zero |- ?P ] =>
      forward_call gv; forward; Exists rv
    end;
    entailer!; unfold EVP_init_POST; cancel; apply andp_left2 ; trivial ]
end end.

Lemma body_EVP_md4: semax_body Vprog EVP_md4_Gprog f_EVP_md4 EVP_md4_SPEC.
Proof. verif_body_EVP_digest _EVP_md4_init _EVP_md4_once _EVP_md4_storage. Qed. 

Definition EVP_md5_SPEC:= EVP_digest_SPEC md5_md _EVP_md5 _EVP_md5_once _EVP_md5_storage.

Definition EVP_md5_Gprog:funspecs :=
 [EVP_md5_once_bss_get_SPEC; 
  CRYPTO_once_SPEC (EVP_init_PRE md5_md _EVP_md5_storage)
                   (EVP_init_POST md5_md _EVP_md5_storage);
  EVP_md5_init_SPEC; EVP_md5_storage_bss_get_SPEC].

Lemma body_EVP_md5: semax_body Vprog EVP_md5_Gprog f_EVP_md5 EVP_md5_SPEC.
Proof. verif_body_EVP_digest _EVP_md5_init _EVP_md5_once _EVP_md5_storage. Qed.

Definition EVP_sha1_SPEC:= EVP_digest_SPEC sha1_md _EVP_sha1 _EVP_sha1_once _EVP_sha1_storage.

Definition EVP_sha1_Gprog:funspecs :=
 [EVP_sha1_once_bss_get_SPEC; 
  CRYPTO_once_SPEC (EVP_init_PRE sha1_md _EVP_sha1_storage)
                   (EVP_init_POST sha1_md _EVP_sha1_storage);
  EVP_sha1_init_SPEC; EVP_sha1_storage_bss_get_SPEC].

Lemma body_EVP_sha1: semax_body Vprog EVP_sha1_Gprog f_EVP_sha1 EVP_sha1_SPEC.
Proof. verif_body_EVP_digest _EVP_sha1_init _EVP_sha1_once _EVP_sha1_storage. Qed.

Definition EVP_sha224_SPEC:= EVP_digest_SPEC sha224_md _EVP_sha224 _EVP_sha224_once _EVP_sha224_storage.

Definition EVP_sha224_Gprog:funspecs :=
 [EVP_sha224_once_bss_get_SPEC; 
  CRYPTO_once_SPEC (EVP_init_PRE sha224_md _EVP_sha224_storage)
                   (EVP_init_POST sha224_md _EVP_sha224_storage);
  EVP_sha224_init_SPEC; EVP_sha224_storage_bss_get_SPEC].

Lemma body_EVP_sha224: semax_body Vprog EVP_sha224_Gprog f_EVP_sha224 EVP_sha224_SPEC.
Proof. verif_body_EVP_digest _EVP_sha224_init _EVP_sha224_once _EVP_sha224_storage. Qed.

Definition EVP_sha256_SPEC:= EVP_digest_SPEC sha256_md _EVP_sha256 _EVP_sha256_once _EVP_sha256_storage.

Definition EVP_sha256_Gprog:funspecs :=
 [EVP_sha256_once_bss_get_SPEC; 
  CRYPTO_once_SPEC (EVP_init_PRE sha256_md _EVP_sha256_storage)
                   (EVP_init_POST sha256_md _EVP_sha256_storage);
  EVP_sha256_init_SPEC; EVP_sha256_storage_bss_get_SPEC].

Lemma body_EVP_sha256: semax_body Vprog EVP_sha256_Gprog f_EVP_sha256 EVP_sha256_SPEC.
Proof. verif_body_EVP_digest _EVP_sha256_init _EVP_sha256_once _EVPsha256_storage. Qed.

Definition EVP_sha384_SPEC:= EVP_digest_SPEC sha384_md _EVP_sha384 _EVP_sha384_once _EVP_sha384_storage.

Definition EVP_sha384_Gprog:funspecs :=
 [EVP_sha384_once_bss_get_SPEC; 
  CRYPTO_once_SPEC (EVP_init_PRE sha384_md _EVP_sha384_storage)
                   (EVP_init_POST sha384_md _EVP_sha384_storage);
  EVP_sha384_init_SPEC; EVP_sha384_storage_bss_get_SPEC].

Lemma body_EVP_sha384: semax_body Vprog EVP_sha384_Gprog f_EVP_sha384 EVP_sha384_SPEC.
Proof. verif_body_EVP_digest _EVP_sha384_init _EVP_sha384_once _EVP_sha384_storage. Qed.

Definition EVP_sha512_SPEC:= EVP_digest_SPEC sha512_md _EVP_sha512 _EVP_sha512_once _EVP_sha512_storage.

Definition EVP_sha512_Gprog:funspecs :=
 [EVP_sha512_once_bss_get_SPEC; 
  CRYPTO_once_SPEC (EVP_init_PRE sha512_md _EVP_sha512_storage)
                   (EVP_init_POST sha512_md _EVP_sha512_storage);
  EVP_sha512_init_SPEC; EVP_sha512_storage_bss_get_SPEC].

Lemma body_EVP_sha512: semax_body Vprog EVP_sha512_Gprog f_EVP_sha512 EVP_sha512_SPEC.
Proof. verif_body_EVP_digest _EVP_sha512_init _EVP_sha512_once _EVP_sha512_storage. Qed.

Definition EVP_md5_sha1_SPEC:= EVP_digest_SPEC md5_sha1_md _EVP_md5_sha1 _EVP_md5_sha1_once _EVP_md5_sha1_storage.

Definition EVP_md5_sha1_Gprog:funspecs :=
 [EVP_md5_sha1_once_bss_get_SPEC; 
  CRYPTO_once_SPEC (EVP_init_PRE md5_sha1_md _EVP_md5_sha1_storage)
                   (EVP_init_POST md5_sha1_md _EVP_md5_sha1_storage);
  EVP_md5_sha1_init_SPEC; EVP_md5_sha1_storage_bss_get_SPEC].

Lemma body_EVP_md5_sha1: semax_body Vprog EVP_md5_sha1_Gprog f_EVP_md5_sha1 EVP_md5_sha1_SPEC. 
Proof. verif_body_EVP_digest _EVP_md5_sha1_init _EVP_md5_sha1_once _EVP_md5_sha1_storage. Qed.

(*
Definition CRYPTO_ONCE_SubjectSPEC A (P Q: A -> globals -> mpred):funspec :=
  WITH a:A, gv:globals
  PRE [] PROP () LOCAL (gvars gv) SEP (P a gv)
  POST [tvoid] PROP () LOCAL () SEP (Q a gv).

Definition CRYPTO_once_SPEC A P Q:= 
DECLARE _CRYPTO_once
  WITH i:int, once:val, init:val, osh:share, a:A, gv:globals
  PRE [ _once OF tptr tuint,
        _init OF tptr (Tfunction Tnil tvoid cc_default) ]
      PROP (writable_share osh) LOCAL (temp _once once; temp _init init; gvars gv) 
      SEP (data_at osh tuint (Vint i) once; IFZ_mpred i (P a gv) (Q a gv); func_ptr' (CRYPTO_ONCE_SubjectSPEC A P Q) init )
  POST [ tvoid ]
    EX j:int,
    PROP (j <> Int.zero) LOCAL () SEP (data_at osh tuint (Vint j) once; Q a gv; func_ptr' (CRYPTO_ONCE_SubjectSPEC A P Q) init).

Lemma body_CRYPTO_once A P Q: semax_body Vprog EmptyGprog f_CRYPTO_once (CRYPTO_once_SPEC A P Q).
Proof. start_function.
forward.
  forward_if (PROP (i=Int.zero) LOCAL (temp _t'1 (Vint i); temp _once once; temp _init init; gvars gv)
      SEP (data_at osh tuint (Vint i) once; P a gv; func_ptr' (CRYPTO_ONCE_SubjectSPEC A P Q) init)).
+ forward. Exists i. entailer!. unfold IFZ_mpred. rewrite Int.eq_false; trivial.
+ forward. entailer!. unfold IFZ_mpred. rewrite Int.eq_true. trivial.
+ Intros; subst. forward. forward_call (a, gv). forward. Exists (Int.repr 1). entailer!. inv H1.
Qed.

Definition EVP_digest_SPEC D (f once g: ident):= 
DECLARE f
  WITH gv:globals,i:int
  PRE [ ] PROP () 
          LOCAL (gvars gv) 
          SEP (data_at Tsh tuint (Vint i) (gv once);
               IFZ_mpred i (EVP_init_PRE D gv g) (EVP_init_POST D gv g))
  POST [ tptr (Tstruct _env_md_st noattr) ]
    EX rv:int,
    PROP (rv <> Int.zero) LOCAL (temp ret_temp (gv g))
    SEP (EVP_MD_rep D (gv g); data_at Tsh tuint (Vint rv) (gv once)).

Axiom funspec_entails: forall fs1 fs2 p, subsume_funspec fs1 fs2 -> func_ptr' fs1 p |-- func_ptr' fs2 p.

Definition EVP_md4_SPEC:= EVP_digest_SPEC md4_md _EVP_md4 _EVP_md4_once _EVP_md4_storage.

Definition EVP_md4_Gprog:funspecs :=
 [EVP_md4_once_bss_get_SPEC; 
  CRYPTO_once_SPEC unit (fun a gv => EVP_init_PRE md4_md gv _EVP_md4_storage)
                           (fun a gv => EVP_init_POST md4_md gv _EVP_md4_storage);
  EVP_md4_init_SPEC;
  EVP_md4_storage_bss_get_SPEC].

Lemma ss: subsume_funspec
  (WITH gv : globals 
     PRE [ ] PROP ( )  LOCAL (gvars gv)  SEP (EVP_init_PRE md4_md gv _EVP_md4_storage)
     POST [tvoid] PROP ( )  LOCAL ()  SEP (EVP_init_POST md4_md gv _EVP_md4_storage))
  (CRYPTO_ONCE_SubjectSPEC unit
     (fun a gv => EVP_init_PRE md4_md gv _EVP_md4_storage)
     (fun a gv => EVP_init_POST md4_md gv _EVP_md4_storage)).
Proof. apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [a p]. Exists p emp. 
change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
entailer!.
Qed.

Lemma body_EVP_md4: semax_body Vprog EVP_md4_Gprog f_EVP_md4 EVP_md4_SPEC.
Proof. start_function.
  forward_call gv.
  make_func_ptr _EVP_md4_init.
  forward_call (i, gv _EVP_md4_once, gv _EVP_md4_init, Tsh, tt, gv).
  assert (FR: Frame=[]); subst Frame; [reflexivity | simpl].
  cancel.
  apply funspec_entails. apply ss.

  Intros rv.
  forward_call gv.
  forward. Exists rv. entailer!. unfold EVP_init_POST. cancel. apply andp_left2 ; trivial.
Qed.






Definition EVP_md4_Gprog:funspecs :=
 [EVP_md4_once_bss_get_SPEC; 
  CRYPTO_once_SPEC globals (fun g gv => !!(g=gv) && EVP_init_PRE md4_md gv _EVP_md4_storage)
                           (fun g gv => !!(g=gv) && EVP_init_POST md4_md gv _EVP_md4_storage);
  EVP_md4_init_SPEC;
  EVP_md4_storage_bss_get_SPEC].

Lemma ss: subsume_funspec
  (WITH gv : globals 
     PRE [ ] PROP ( )  LOCAL (gvars gv)  SEP (EVP_init_PRE md4_md gv _EVP_md4_storage)
     POST [tvoid] PROP ( )  LOCAL ()  SEP (EVP_init_POST md4_md gv _EVP_md4_storage))
  (CRYPTO_ONCE_SubjectSPEC globals
     (fun g gv : globals => !! (g = gv) && EVP_init_PRE md4_md gv _EVP_md4_storage)
     (fun g gv : globals => !! (g = gv) && EVP_init_POST md4_md gv _EVP_md4_storage)).
Proof. apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [gv p]. Exists gv emp. 
change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
entailer!.
Qed.

Lemma body_EVP_md4: semax_body Vprog EVP_md4_Gprog f_EVP_md4 EVP_md4_SPEC.
Proof. start_function.
  forward_call gv.
  make_func_ptr _EVP_md4_init.
  forward_call (i, gv _EVP_md4_once, gv _EVP_md4_init, Tsh, gv, gv).
  assert (FR: Frame=[]); subst Frame; [reflexivity | simpl].
  cancel. rewrite sepcon_comm. apply sepcon_derives. entailer!.
  apply funspec_entails. apply ss.

  Intros rv.
  forward_call gv.
  forward. Exists rv. entailer!. unfold EVP_init_POST. cancel. apply andp_left2 ; trivial.
Qed.

Definition PP (x: globals * val * share) (g:globals): mpred := match x with
   (gv, v, sh) => !!(gv=g /\ writable_share sh) && data_at_ sh (Tstruct _env_md_st noattr) (gv _EVP_md4_storage)
end.

Definition QQ (x: globals * val * share) (g:globals): mpred := match x with
   (gv, v, sh) => !!(gv=g) && EVP_MD_rep md4_md (gv _EVP_md4_storage)
end.
(*
Definition  P (v:val): mpred := EX sh:share, !!writable_share sh && (data_at_ sh (Tstruct _env_md_st noattr) v).
*)
Definition EVP_md4_SPEC:= EVP_digest_SPEC md4_md _EVP_md4 _EVP_md4_once _EVP_md4_storage.
Lemma ss: subsume_funspec
(WITH gv0 : globals PRE
           [ ] PROP ( )  LOCAL (gvars gv0)  SEP (EVP_init_PRE md4_md gv0 _EVP_md4_storage)
           POST [tvoid] PROP ( )  LOCAL ()  SEP (EVP_init_POST md4_md gv0 _EVP_md4_storage))
  (CRYPTO_ONCE_SubjectSPEC (globals * val * share) PP QQ).
Proof. apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [m p]. Exists m emp. destruct m as [[gv v] sh]. 
change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
entailer!.
(*
Lemma ss: subsume_funspec
 (WITH gv : globals
   [ ] (PROP (writable_share sh)
        LOCAL (gvars gv0)  SEP (data_at_ sh (Tstruct _env_md_st noattr) (gv0 _EVP_md4_storage)))
   POST [tvoid] (let (p0, _) := x in
                 let (gv0, _) := p0 in PROP ( )  LOCAL ()  SEP (EVP_MD_rep md4_md (gv0 _EVP_md4_storage))))
  (CRYPTO_ONCE_SubjectSPEC (globals * val * share) PP QQ).
Proof. apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [m p]. Exists m emp. destruct m as [[gv v] sh]. 
change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
entailer!.
Qed.*)

Definition EVP_md4_Gprog:funspecs :=
 [EVP_md4_once_bss_get_SPEC; 
  CRYPTO_once_SPEC (globals * val * share) PP QQ;
  EVP_md4_init_SPEC;
  EVP_md4_storage_bss_get_SPEC].
Parameter sshh:share. Parameter v:val.

Axiom funspec_entails: forall fs1 fs2 p, subsume_funspec fs1 fs2 -> func_ptr' fs1 p |-- func_ptr' fs2 p.

Lemma body_EVP_md4: semax_body Vprog EVP_md4_Gprog f_EVP_md4 EVP_md4_SPEC.
Proof. start_function.
  forward_call gv.
  make_func_ptr _EVP_md4_init.
  replace_SEP 0 (func_ptr' (CRYPTO_ONCE_SubjectSPEC (globals * val * share) PP QQ) (gv _EVP_md4_init)).
  { go_lower. entailer. apply funspec_entails. apply ss. rewrite sepcon_emp.  apply ss.
  forward_call(Int.one, gv _EVP_md4_once, gv _EVP_md4_init, Tsh, (gv, v, sshh), gv).
  assert (FR: Frame=[data_at Tsh tuint (Vint i) (gv _EVP_md4_once)]); subst Frame; [reflexivity | simpl].
  cancel. rewrite sepcon_comm. apply sepcon_derives. admit. (*yields instantiation of P and Q*)
  apply funspec_entails. apply ss.

  Intros rv.
  forward_call gv.
  forward. Exists rv. entailer!. cancel. 


(*
Definition CRYPTO_once_SPEC P Q:= 
DECLARE _CRYPTO_once
  WITH i:int, once:val, init:val, osh:share
  PRE [ _once OF tptr tuint,
        _init OF tptr (Tfunction Tnil tvoid cc_default) ]
      PROP (writable_share osh) LOCAL (temp _once once; temp _init init) 
      SEP (data_at osh tuint (Vint i) once; IFZ_mpred i P Q(*; func_ptr' (CRYPTO_ONCE_SubjectSPEC P Q) init*) )
  POST [ tvoid ]
    EX j:int,
    PROP (j <> Int.zero) LOCAL () SEP (data_at osh tuint (Vint j) once; Q; func_ptr' (CRYPTO_ONCE_SubjectSPEC P Q) init).

Definition myG P Q:funspecs:= [DECLARE _init (CRYPTO_ONCE_SubjectSPEC P Q)].

Lemma body_CRYPTO_once P Q: semax_body Vprog (*EmptyGprog*)(myG P Q) f_CRYPTO_once (CRYPTO_once_SPEC P Q).
Proof. start_function. VST: unhelpful error message*)


Gprog_md5_sha1_do_initf_EVP_md4_storage_bss_get

  entailer!. simpl.  
go_lower. simpl. Print  
  replace_SEP 0 (data_at sh (Tstruct _env_md_st noattr) (default_val (Tstruct _env_md_st noattr)) p).
  { entailer!. }
  rewrite data_at_isptr. Intros. destruct p; simpl in Pp; try contradiction. clear Pp.
  forward. simpl. unfold Delta, abbreviate. simpl. cbv. admit.
  forward. simpl. unfold EVP_MD_rep. Intros vsh vals.
  destruct_vals vals H. Intros. assert (vsh = sh). admit. subst vsh. forward. unfold _type.
  old_go_lower. Locate _id. entailer. simpl.
 sh.
  rewrite EVP_MD_rep_isptr.
  rewrite data_at__isptr. Intros. forward. *)