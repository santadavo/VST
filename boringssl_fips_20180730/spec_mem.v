Require Export VST.floyd.proofauto.
Require Import boringssl_fips_20180730.mem.

Parameter mm_inv: globals -> mpred.
Parameter WORD:Z.
Parameter ALIGN:Z.
Parameter WORD_ALIGN_nonneg: 0 <= WORD * ALIGN.
Definition WA: Z := (WORD*ALIGN) - WORD. (* WASTE at start of block *)

Parameter malloc_token: forall (sh: share) (t: type) (p: val), mpred.
Axiom malloc_token_local_facts:
  forall {cs:compspecs} sh t p, malloc_token sh t p 
  |-- !!( malloc_compatible (sizeof t) p /\ 
          0 <= (sizeof t) <= Ptrofs.max_unsigned - (WA+WORD)).
Hint Resolve malloc_token_local_facts : saturate_local.

Lemma WA_WORD_nonneg: 0 <= WA + WORD.
Proof. unfold WA. specialize WORD_ALIGN_nonneg; omega. Qed.

Lemma malloc_token_local_facts' {cs:compspecs} sh t p:
  malloc_token sh t p = 
  ( !!( malloc_compatible (sizeof t) p /\ 
          0 <= (sizeof t) <= Ptrofs.max_unsigned - (WA+WORD))
    && malloc_token sh t p).
Proof. apply pred_ext; entailer. Qed.

(*From Dave Naumann's malloc/free library, but with Ews instead of Tsh in
  both spatial conjuncts in the postcondition*)
Definition malloc_funspec {cs:compspecs} : funspec := WITH t:type, gv:globals
   PRE [ 1%positive OF size_t ]
       PROP (0 < sizeof t <= Ptrofs.max_unsigned - (WA+WORD);
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       LOCAL (temp 1%positive (Vptrofs (Ptrofs.repr (sizeof t))); gvars gv)
       SEP ( mm_inv gv )
   POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP ( mm_inv gv;
             if eq_dec p nullval then emp
             else (malloc_token Ews t p * data_at_ Ews t p)).

Definition malloc_spec {cs: compspecs} := DECLARE _malloc malloc_funspec.

(*From Dave Naumann's malloc/free library, but with Ews instead of Tsh in
  both spatial conjuncts in the postcondition*)
Definition free_funspec {cs:compspecs} : funspec := 
   WITH p:_, t:_, gv:globals
   PRE [ 1%positive OF tptr tvoid ]
       PROP ()
       LOCAL (temp 1%positive p; gvars gv)
       SEP (mm_inv gv; 
            if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p))
   POST [ Tvoid ]
       PROP ()
       LOCAL ( )
SEP (mm_inv gv).

Definition free_spec {cs:compspecs} := DECLARE _free free_funspec.

(*Taken from spec_sha*)
Definition memcpy_SPEC {cs:compspecs} := DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, contents: list int
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share (fst sh); writable_share (snd sh); 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr n)))
       SEP (data_at (fst sh) (tarray tuchar n) (map Vint contents) q;
              memory_block (snd sh) n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at (fst sh) (tarray tuchar n) (map Vint contents) q;
             data_at (snd sh) (tarray tuchar n) (map Vint contents) p).

(*Taken from spec_sha; indeed, it seems p==null yields undef behavior in C11 standard*)
Definition memset_spec {cs:compspecs} :=
  DECLARE _memset
   WITH sh : share, p: val, n: Z, c: int
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive (Vint c);
                   temp 3%positive (Vint (Int.repr n)))
       SEP (memory_block sh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) p).

Inductive memcpyCase :=
  memcpyNull: memcpyCase
| memcpyNonnull: forall (dsh ssh: share) (data: list int), memcpyCase.

Definition OPENSSL_memcpy_SPEC {cs:compspecs} := DECLARE _OPENSSL_memcpy
   WITH dst: val, src: val, n: Z, c:memcpyCase
   PRE [ _dst OF tptr tvoid, _src OF tptr tvoid, _n OF tuint ]
       PROP ()
       LOCAL (temp _dst dst; temp _src src; temp _n (Vint (Int.repr n)))
       SEP (match c with
            | memcpyNull => !!(n=0) && emp
            | memcpyNonnull dsh ssh data =>
                !!(readable_share ssh /\ writable_share dsh /\ 0 < n <= Int.max_unsigned)
                && data_at ssh (tarray tuchar n) (map Vint data) src *
                   memory_block dsh n dst
            end)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp dst)
       SEP(match c with 
            | memcpyNull => emp
            | memcpyNonnull dsh ssh data =>
               data_at dsh (tarray tuchar n) (map Vint data) dst *
               data_at ssh (tarray tuchar n) (map Vint data) src
           end).

Inductive memsetCase :=
  memsetNull: memsetCase
| memsetNonnull: share -> memsetCase.

Definition OPENSSL_memset_SPEC {cs:compspecs} := DECLARE _OPENSSL_memset  
   WITH dst: val, n: Z, c: int, case: memsetCase
   PRE [ _dst OF tptr tvoid, _c OF tint, _n OF tuint ]
       PROP ()
       LOCAL (temp _dst dst; temp _c (Vint c); temp _n (Vint (Int.repr n)))
       SEP (match case with
            | memsetNull => !!(n=0) && emp
            | memsetNonnull sh => !!(writable_share sh /\ 0 < n <= Int.max_unsigned) 
                            && memory_block sh n dst
            end)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp dst)
       SEP(match case with 
           | memsetNull => emp
           | memsetNonnull sh => data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) dst
           end).

(* Specification in mem.h: OPENSSL_cleanse zeros out |len| bytes of memory at |ptr|. 
                           This is similar to |memset_s| from C11.
   Our spec is essentially identical to the one of memset (with value 0)*)
(*Definition OPENSSL_cleanse_SPEC := DECLARE _OPENSSL_cleanse
  WITH p: val, sh : share, n:Z, case: unit + unit
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tuint]
      PROP(writable_share sh; 0 <= n <= Int.max_unsigned) 
      LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (match case with
             inl _ => memory_block sh n p
           | inr _ => !!(n=sizeof (Tstruct _env_md_ctx_st noattr)) 
                      && data_at_ sh (Tstruct _env_md_ctx_st noattr) p
           end)
  POST [ tvoid ]
    PROP () LOCAL () 
    SEP (match case with
           inl _ => data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) p
         | inr _ => data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) p
         end).*)
Definition OPENSSL_cleanse_SPEC {cs:compspecs} := DECLARE _OPENSSL_cleanse
  WITH p: val, sh : share, n:Z
  PRE [ _ptr OF tptr tvoid, _len OF tuint]
      PROP(writable_share sh; 0 <= n <= Int.max_unsigned) 
      LOCAL (temp _ptr p; temp _len (Vint (Int.repr n)))
      SEP (memory_block sh n p)
  POST [ tvoid ]
    PROP () LOCAL () 
    SEP (data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) p).

Definition OPENSSL_malloc_token {cs:compspecs} n v: mpred := 
   let u := offset_val (-8) v in
   !!(0<n) && malloc_token Ews (tarray tuchar (n + 8)) u * data_at Ews tuint (Vint (Int.repr n)) u *
   data_at_ Ews (Tarray tuchar 4 noattr) (field_address0 (Tarray tuchar 8 noattr) [ArraySubsc 4] u).

Definition OPENSSLmalloc_compatible n v := malloc_compatible (n + 8) (offset_val (-8) v).

Lemma OPENSSL_malloc_token_compatible {cs:compspecs} n v:
      OPENSSL_malloc_token n v |-- !!(OPENSSLmalloc_compatible n v /\ isptr v /\ 0<n<= Ptrofs.max_unsigned - (WA + WORD) -8).
Proof. unfold OPENSSL_malloc_token, OPENSSLmalloc_compatible.
 rewrite malloc_token_local_facts'; Intros; simpl in *.
 rewrite Z.mul_1_l, Z.max_r in * by omega; entailer. 
Qed.

Lemma OPENSSL_malloc_token_compatible' {cs:compspecs} n v:
      OPENSSL_malloc_token n v = 
      (!!(OPENSSLmalloc_compatible n v /\ isptr v /\ 0<n<= Ptrofs.max_unsigned - (WA + WORD) -8)
        && OPENSSL_malloc_token n v).
Proof. apply pred_ext; entailer; apply OPENSSL_malloc_token_compatible; trivial. Qed.

Definition OPENSSL_malloc_SPEC {cs:compspecs} := DECLARE _OPENSSL_malloc
  WITH n:Z, gv:globals
  PRE [ _size OF tuint]
     PROP (0 < n <= Int.max_unsigned - (WA + WORD)-8)
     LOCAL (temp _size (Vint (Int.repr n)); gvars gv)
     SEP (mm_inv gv)
  POST [ tptr tvoid ]
     EX v: val,
     PROP ()
     LOCAL (temp ret_temp v)
     SEP ((!!(v=nullval) && emp)
           || (memory_block Ews n v * OPENSSL_malloc_token n v); 
          mm_inv gv).

Definition OPENSSL_free_SPEC {cs:compspecs} := DECLARE _OPENSSL_free
  WITH p:val, n:Z, gv:globals
  PRE [ _orig_ptr OF tptr tvoid]
     PROP ()
     LOCAL (temp _orig_ptr p; gvars gv)
     SEP (mm_inv gv; 
          if Val.eq p nullval then emp else (!!(0<n)&& memory_block Ews n p * OPENSSL_malloc_token n p))
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (mm_inv gv).

Lemma PtrofsInt_unsigned_eq: Ptrofs.max_unsigned = Int.max_unsigned. reflexivity. Qed.

Lemma malloc_compatible_tuint_array {cs:compspecs} {n v} (N: 0 < n) 
      (M: malloc_compatible (n+4) v):
      field_compatible (Tarray tuint 1 noattr) [] v.
Proof.
 red; destruct v; try contradiction. simpl in *; intuition.
 apply align_compatible_rec_Tarray. intros. assert (i0=0) by omega; subst; simpl.
 rewrite Zplus_0_r. eapply align_compatible_rec_by_value. reflexivity.
 clear -H; unfold natural_alignment in H; destruct H as [k K].
 simpl; exists (k*2)%Z; omega.
Qed.

Lemma malloc_compatible_sub { n m v} (M:m < n) (N: malloc_compatible n v):malloc_compatible m v.
Proof.
 red; destruct v; try contradiction. simpl in *; intuition.
Qed.

Lemma malloc_compatible_tuintarray8 {cs:compspecs} {n v} (N: 0 < n) 
      (M: malloc_compatible (n + 8) v):
      field_compatible (Tarray tuint 1 noattr) [] v.
Proof.
 apply (malloc_compatible_tuint_array N).
 eapply malloc_compatible_sub; [ | eassumption]; omega.
Qed.

Lemma malloc_compatible_offsetNA {n v} (N: 0 <= n)
      (MC: malloc_compatible (n + natural_alignment) v):
      malloc_compatible n (offset_val natural_alignment v).
Proof. 
 destruct v; try contradiction. destruct MC as [[k K] P]. simpl.
 unfold natural_alignment in *; simpl.
 rewrite Ptrofs.add_unsigned, (Ptrofs.unsigned_repr 8) by rep_omega.
 rewrite Ptrofs.unsigned_repr by rep_omega.
      split; 
      [ exists (k+1); rewrite Z.mul_add_distr_r, <- K, Z.mul_1_l; reflexivity
      | rep_omega ].
Qed.

Lemma memory_block_split' sh b i (n m : Z) (N: 0 <= n <= Ptrofs.max_unsigned)
       (M: 0 <= m) (NM: n + m + Ptrofs.unsigned i < Ptrofs.modulus):
       memory_block sh (n + m) (Vptr b i) =
       memory_block sh n (Vptr b i) * memory_block sh m (offset_val n (Vptr b i)).
Proof.
destruct N as [N1 N2].
specialize (memory_block_split sh b (Ptrofs.unsigned i) n m N1 M).
rewrite (Ptrofs.repr_unsigned i) by omega; intros I; rewrite I; clear I; simpl.
unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr; trivial; omega.
specialize (Ptrofs.unsigned_range_2 i); omega.
Qed.

Lemma OPENSSLmalloc_compatible_field_compatible {cs: compspecs} t v:
      OPENSSLmalloc_compatible (sizeof t) v -> isptr v ->
      complete_legal_cosu_type t = true -> natural_aligned natural_alignment t = true ->
     field_compatible t [] v.
Proof. intros.
eapply  malloc_compatible_field_compatible; simpl; trivial. 
apply (@malloc_compatible_offsetNA (sizeof t)) in H.
rewrite offset_offset_val, isptr_offset_val_zero in H; trivial.
specialize (sizeof_pos t); omega.
Qed.