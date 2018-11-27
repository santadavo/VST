Require Export VST.floyd.proofauto.
Require Import boringssl_fips_20180730.mem.
Require Import boringssl_fips_20180730.spec_mem.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition GprogMemcpy: funspecs := [memcpy_SPEC].
Lemma body_OPENSSL_memcpy_SPEC: semax_body Vprog GprogMemcpy f_OPENSSL_memcpy OPENSSL_memcpy_SPEC.
Proof.
  start_function. destruct c; Intros; subst.
+ (*memcpyNull*)
  forward_if (PROP ( False ) LOCAL () SEP ()); [ forward | inv H] .
+ (*memcpyNonnull*)
  forward_if (
    PROP ( )
    LOCAL (temp _dst dst; temp _src src; temp _n (Vint (Int.repr n)))
    SEP (data_at ssh (tarray tuchar n) (map Vubyte data) src; memory_block dsh n dst)); [ omega |  forward; entailer! | ].
  forward_call ((ssh,dsh), dst, src, n, data); [ simpl; cancel | simpl; intuition | forward].
  cancel.
Qed.

Definition GprogMemset: funspecs := [memset_spec].
Lemma body_OPENSSL_memset_SPEC: semax_body Vprog GprogMemset f_OPENSSL_memset OPENSSL_memset_SPEC.
Proof.
  start_function. destruct case; Intros; subst.
+ (*memsetNull*)
  forward_if (PROP ( False ) LOCAL () SEP ()); [ forward | inv H] .
+ (*memsetPtr*)
  forward_if (
    PROP ( )
    LOCAL (temp _dst dst; temp _c (Vubyte c); temp _n (Vint (Int.repr n)))
    SEP (memory_block s n dst)); [ omega | forward ; entailer! | ].
  forward_call (s,dst,n,c); [ intuition | forward ].
Qed.

Definition GprogOPENSSL_cleanse: funspecs := [OPENSSL_memset_SPEC].
Lemma body_OPENSSL_cleanse_SPEC: semax_body Vprog GprogOPENSSL_cleanse f_OPENSSL_cleanse OPENSSL_cleanse_SPEC.
Proof.
  start_function. rewrite memory_block_isptr; Intros. destruct p; try contradiction.
  destruct (zeq n 0).
+ subst. forward_call (Vptr b i, Z0, Byte.zero, memsetNull).
  { rewrite memory_block_zero_Vptr. entailer!. }
  forward. rewrite data_at_zero_array_eq; trivial.
+ forward_call (Vptr b i, n, Byte.zero, memsetNonnull sh).
  { entailer!. }
  forward.
Qed.

Definition GprogFree: funspecs:=[OPENSSL_cleanse_SPEC; free_spec].
Lemma body_OPENSSL_free: semax_body Vprog GprogFree f_OPENSSL_free OPENSSL_free_SPEC.
Proof.
  start_function.
  forward_if (
    PROP (0<n)
    LOCAL (temp _orig_ptr p; gvars gv)
    SEP (mm_inv gv; memory_block Ews n p; OPENSSL_malloc_token n p)).
  { destruct (Val.eq p nullval); subst; entailer!. }
  { forward. }
  { forward. rewrite if_false; trivial. entailer!. }
  Intros. forward. simpl. rewrite memory_block_isptr; Intros.
  destruct p; try contradiction. simpl. unfold OPENSSL_malloc_token. Intros.
  assert_PROP (Vptr b (Ptrofs.sub i (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 8)))) 
    =  offset_val (-8) (Vptr b i)) as P.
  { rewrite Ptrofs.sub_add_opp; entailer!. }
  rewrite P; forward.
  assert_PROP (malloc_compatible (sizeof (tarray tuchar (n + 8))) (offset_val (-8) (Vptr b i)) /\ 
          0 <= (sizeof (tarray tuchar (n + 8))) <= Ptrofs.max_unsigned - (WA+WORD)) as LF by entailer!.
  destruct LF as [LF1 LF2]; simpl in LF2. rewrite Z.mul_1_l, Z.max_r in LF2 by omega.

  replace (field_address0 (Tarray tuchar 8 noattr) [ArraySubsc 4] (offset_val (-8) (Vptr b i))) with (offset_val (-4) (Vptr b i)).
  2: { rewrite field_compatible0_field_address0. simpl. rewrite Ptrofs.add_assoc.
       do 2 f_equal.
       apply malloc_compatible_field_compatible in LF1; try reflexivity.
       auto with field_compatible. }

  replace (offset_val (-4) (Vptr b i)) with (offset_val 4 (offset_val (-8) (Vptr b i))).
  2: { rewrite offset_offset_val; f_equal. }

  remember (offset_val (-8) (Vptr b i)) as p; clear P.
  replace (Vptr b i) with (offset_val 8 p).
  2: { subst. rewrite offset_offset_val. 
       replace (-8+8) with 0 by omega. apply isptr_offset_val_zero; trivial. }
  clear Pp Heqp b i.

  rewrite data_at_isptr; Intros. destruct p; try contradiction.
  sep_apply (data_at_data_at_ Ews tuint (Vint (Int.repr n)) (Vptr b i)).
  rewrite 2 data_at__memory_block; Intros.
  gather_SEP 0 2 4.

  replace_SEP 0 (memory_block Ews (n + 8) (Vptr b i)).
  { entailer!. replace (n+8) with (4 + (4+n)) by omega.
    rewrite memory_block_split'; try rep_omega.
    2:{ red in LF1; simpl in LF1. rewrite Z.mul_1_l, Z.max_r in LF1; try omega. }
    cancel.
    replace (Vptr b (Ptrofs.add i (Ptrofs.repr 8))) with (offset_val 4 (offset_val 4 (Vptr b i))) by (rewrite offset_offset_val; reflexivity).
    replace (Vptr b (Ptrofs.add i (Ptrofs.repr 4))) with (offset_val 4 (Vptr b i)) by reflexivity.
    remember (offset_val 4 (Vptr b i)) as p.
    destruct p; simpl in Heqp; try congruence.
    rewrite memory_block_split'; try rep_omega. cancel.
    inv Heqp. red in LF1. simpl in LF1. rewrite Z.mul_1_l, Z.max_r in LF1 by omega.
    unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr 4) by rep_omega.
    rewrite Ptrofs.unsigned_repr; rep_omega. }
  forward_call (Vptr b i, Ews, n+8).
  { rewrite PtrofsInt_unsigned_eq in LF2. specialize WA_WORD_nonneg; intuition. }
  forward_call (Vptr b i, tarray tuchar (n + 8),gv).
  { simpl; cancel. }
  forward.
Qed.

Definition GprogMalloc: funspecs:=[malloc_spec].
Lemma body_OPENSSL_malloc: semax_body Vprog GprogMalloc f_OPENSSL_malloc OPENSSL_malloc_SPEC.
Proof.
  start_function. make_func_ptr _malloc.
  forward_call (tarray (Tint I8 Unsigned noattr) (n+8), gv).
  { simpl. rewrite Z.mul_1_l, Z.max_r, PtrofsInt_unsigned_eq by omega.
    split. omega. split; trivial. }
  Intros v. if_tac; subst.
  + forward_if (PROP (False) LOCAL () SEP ()).
    { forward. Exists nullval. entailer!. apply orp_right1. apply andp_left2; trivial. }
    discriminate. 
  + assert_PROP (isptr v) by entailer!.
    rewrite malloc_token_local_facts'; Intros. simpl in H2, H3. rename H0 into V1. rename H1 into V2.
    rename H2 into V3. rename H3 into SZ.
    forward_if (
    PROP ( )
     LOCAL (temp _ptr v; temp _size (Vint (Int.repr n)); gvars gv)
     SEP (mm_inv gv;
          malloc_token Ews (tarray tuchar (n + 8)) v;
          data_at_ Ews (tarray  tuchar (n + 8)) v)).
    { clear - H. apply denote_tc_test_eq_split; [ |  apply valid_pointer_null ].
      apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
      eapply derives_trans; [ apply data_at__data_at; reflexivity | entailer! ]. }
    { subst; forward. }
    { forward. unfold tuchar. entailer!. apply andp_left2; trivial. }
    assert_PROP (field_compatible (Tarray tuchar (n + 8) noattr) [] v) as FC by entailer!.
    rewrite (split2_data_at__Tarray_tuchar Ews (n + 8) 8 v); trivial; [| omega].
    Intros. replace (n+8-8) with n by omega.
    replace (field_address0 (Tarray tuchar (n + 8) noattr) [ArraySubsc 8] v) with (offset_val 8 v).
    2 :{ unfold field_address0. rewrite if_true.
         destruct v; try contradiction. simpl; trivial.
         eapply (field_compatible0_cons_Tarray 8) in FC. trivial. reflexivity. omega. }
    assert (FC1: field_compatible (Tarray tuchar 8 noattr) [] v).
    { auto with field_compatible. }
    rewrite (split2_data_at__Tarray_tuchar Ews 8 4 v); trivial; [| omega].
    Intros. replace (8-4) with 4 by omega.
    replace_SEP 2 (data_at_ Ews (Tarray tuint 1 noattr) v).
    { rewrite 2 data_at__memory_block; entailer!. destruct H as [H _]. clear -H V3.
      rewrite Z.mul_1_l, Z.max_r in V3; try omega.
      eapply malloc_compatible_tuintarray8; eauto. }

    rewrite data_at__Tarray. simpl. 
    erewrite (data_at_singleton_array_eq Ews tuint); [ | reflexivity]. 
    forward. rewrite data_at__memory_block with (p:= offset_val 8 v); simpl; Intros.
    rewrite Z.mul_1_l, Z.max_r in * by omega. 
    forward.
    Exists (offset_val 8 v); entailer!. apply orp_right2. 
    unfold OPENSSL_malloc_token. 
    replace (offset_val (-8) (offset_val 8 v)) with v; 
    [ entailer! | destruct v; try contradiction; simpl; rewrite Ptrofs.add_assoc, Ptrofs.add_neg_zero, Ptrofs.add_zero; trivial].
    (*destruct H as [H _]. clear - H V3.
    apply malloc_compatible_offsetNA; [omega | assumption].*)
Qed.
