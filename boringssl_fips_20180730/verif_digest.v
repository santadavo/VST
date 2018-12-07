Require Export VST.floyd.proofauto.
Require Import boringssl_fips_20180730.spec_mem.
Require Import boringssl_fips_20180730.digest.
Require Import boringssl_fips_20180730.spec_digest_base.
Require Import boringssl_fips_20180730.spec_digest.

(*Qinxiang says: proving this needs more work in floyd, namely
  conversion between different base types (4 null byes = 1 null integer etc.
  Also, walking through the array then and to "spin off" values in the right chunks*)
Lemma convert sh (SH: readable_share sh) p
  (P: field_compatible (Tstruct _env_md_ctx_st noattr) [] p):
  data_at sh (tarray tuchar 16)
  [Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero] p
|-- data_at sh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) p.
Proof. intros. unfold data_at at 2.
rewrite data_at_isptr; Intros. destruct p; try contradiction. clear Pp.
entailer. clear H0. 
erewrite (split2_data_at_Tarray_tuchar sh 16 4); [ simpl | omega | reflexivity].
rewrite field_address0_clarify.
2: { unfold field_address0; rewrite if_true; simpl; trivial.
     apply (field_compatible0_app_inv' [ArraySubsc 4] _ _ _ H); simpl; split; trivial; omega. }
erewrite (split2_data_at_Tarray_tuchar sh 12 4); [ autorewrite with sublist | omega | reflexivity].
rewrite field_address0_clarify; simpl.
2: { unfold field_address0; rewrite if_true; simpl; trivial.
     eapply field_compatible0_Tarray_offset with (p:=Vptr b i)(i':=8)(n':=16); simpl; intuition. }
erewrite (split2_data_at_Tarray_tuchar sh 8 4); [ autorewrite with sublist | omega | reflexivity].
rewrite field_address0_clarify; simpl.
2: { unfold field_address0; rewrite if_true; simpl; trivial.
     eapply field_compatible0_Tarray_offset with (p:=Vptr b i)(i':=12)(n':=16); simpl; intuition.
     rewrite Ptrofs.add_assoc; f_equal. }
erewrite (field_at_Tstruct sh (Tstruct _env_md_ctx_st noattr)); 
  [ | reflexivity | apply JMeq_refl ].
simpl. unfold withspacer, sublist. simpl.
apply sepcon_derives.
{ entailer. unfold data_at, field_at. unfold at_offset;  simpl. entailer.
  unfold data_at_rec, unfold_reptype; simpl. rewrite mapsto_size_t_tptr_nullval.
  (*
  unfold mapsto. simpl. rewrite if_true; trivial.
  apply orp_right1. apply andp_right. apply prop_right; trivial.*)
  rewrite (split_array_pred 0 1 4); [ unfold sublist; simpl; rewrite array_pred_len_1 | omega | reflexivity].
  rewrite (split_array_pred 1 2 4); [ unfold sublist; simpl; rewrite array_pred_len_1 | omega | reflexivity].
  rewrite (split_array_pred 2 3 4); [ unfold sublist; simpl; rewrite 2 array_pred_len_1 | omega | reflexivity].

  unfold at_offset; simpl. admit. } (* unfold mapsto. simpl. rewrite ! if_true; trivial. apply orp_right1.
  rewrite distrib_orp_sepcon. apply orp_left; Intros.
  repeat rewrite <- sepcon_assoc. rewrite sepcon_comm.
  rewrite distrib_orp_sepcon. apply orp_left; Intros.
  repeat rewrite <- sepcon_assoc. rewrite sepcon_comm.
  rewrite distrib_orp_sepcon. apply orp_left; Intros.
  repeat rewrite <- sepcon_assoc. rewrite sepcon_comm.
  rewrite distrib_orp_sepcon. apply orp_left; Intros.
Search address_mapsto.
  unfold nullval. destruct (Archi.ptr64). admit. 
  unfold address_mapsto. unfold  predicates_hered.exp. simpl.
   (*
  rewrite <- mapsto_memory_block.VALspec_range_exp_address_mapsto_eq.
  Search predicates_hered.exp.
 admit.

 normalize.
  repeat rewrite <- sepcon_assoc. rewrite sepcon_comm.
Search orp sepcon.
  rewrite <- sepcon_assoc. 
  rewrite ! sepcon_assoc. rewrite sepcon_comm.
  rewrite ! distrib_orp_sepcon. apply orp_left; Intros.
  Search sepcon orp.

rewrite array_pred_len_1.
  specialize (array_pred_len_1 0); intros AP1; simpl in AP1.
  Search array_pred. erewrite <- at_offset_array_pred. unfold at_offset. simpl.
  unfold res_predicates.address_mapsto. simpl. apply orp
Search mapsto size_t.
  unfold array_pred, aggregate_pred.array_pred, mapsto, at_offset. simpl.
  repeat rewrite if_true; trivial. Intros. apply orp_right1. apply andp_right. apply prop_right; trivial.
  unfold Znth; simpl. rewrite sepcon_emp. Search res_predicates.address_mapsto. (*
  unfold nullval. destruct Archi.ptr64. simpl. unfold res_predicates.address_mapsto. simpl.
Search predicates_hered.exp predicates_hered.andp.
  eapply predicates_hered.exp_derives. spredicates_hered.exp_right.
Search predicates_hered.exp.

  Exists (list_repeat 4 (Byte Byte.zero)). red. res_predicates.address_mapsto nullval. , predicates_hered.exp. simpl.
  Search derives orp.
 normalize. rewrite if_true.
  Search array_pred mapsto. unfold unfold_reptype. simpl.
  simpl.
  + destruct H as [A [B [C [D E]]]]. simpl in A, B, C, E.
    specialize (align_compatible_rec_Tarray_inv _ _ _ _ _ D); intros.
    red; intuition. 2: split; [ trivial | left; reflexivity].
    red. red in D.  Search align_compatible_rec Tstruct. eapply align_compatible_rec_Tstruct.
    
    reflexivity. intros. hnf in H1.  simpl. intros. simpl. by_copy. simpl.  unfold align_compatible_rec. simpl. red in D.  simpl in D. cbv. hnf. compute.  apply D. red. red in H; simpl in H. intuition.  destruct p; try contradiction. clear Pp. intuition.
  Search data_at_rec.
Check field_at_change_composite. field_at_stronger. stronger
field_at_change_composite:cs_preserve_type 

 simpl. _field_at. entailer. rewrite data_at_isptr, field_at_data_at'; simpl. entailer!. admit.

headptr_field_compatible
  + red; simpl. red in H; simpl in H. destruct p; try contradiction. clear Pp. intuition.
    red; simpl. red in H2; simpl in H2. omega. 
 rewrite field_at_data_at'. simpl.  unfold data_at.
Search field_at. 
rewrite 2 field_at_data_at. simpl. at 2. 1%nat.
field_at_stronger: stronger
field_at_change_composite:cs_preserve_type 
Search data_at.data_at_tuchar_singleton_array_inv, data_at_tuchar_singleton_array
data_at_singleton_array_eq*)*)*)
Admitted.

Lemma ERRGV' gv: ERRGV gv |-- ERR (gv ___stringlit_1).
Proof. unfold ERRGV. assert (digests.___stringlit_1 = ___stringlit_1) by reflexivity.
 rewrite H; trivial. 
Qed. 

Lemma ERRGV'' gv: ERR (gv ___stringlit_1) |-- ERRGV gv.
Proof. unfold ERRGV. assert (digests.___stringlit_1 = ___stringlit_1) by reflexivity.
 rewrite H; trivial. 
Qed. 

Hint Resolve ERRGV': cancel.
Hint Resolve ERRGV'': cancel.

Ltac destruct_vals vals X :=
   destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]];
   simpl in type, mds, flags, ini, upd, fin, blsize, ctxsize, X; subst; simpl.

(*
Ltac verif_EVP_MD_component :=
  start_function;
  let sh := fresh "sh" in
  let vals := fresh "vals" in
  unfold EVP_MD_rep; Intros sh vals;
  match goal with [ M : match_EVP_MD ?D vals |- ?P ] 
        => destruct_vals vals M; destruct M as [? [? [? [? ?]]]]
  end;
  do 2 forward;
  let z := fresh "z" in
  evar (z:reptype (Tstruct _env_md_st noattr));
  Exists sh z; subst z; entailer!; simpl; intuition.*)

Ltac verif_EVP_MD_component :=
  start_function;
  let sh := fresh "sh" in
  let vals := fresh "vals" in
  unfold EVP_MD_rep; Intros sh vals;
  match goal with [ vals : reptype (Tstruct digests._env_md_st noattr) |- ?P ] 
        => destruct_vals vals sh; Intros
  end;
  do 2 forward;
  let z := fresh "z" in
  evar (z:reptype (Tstruct _env_md_st noattr));
  Exists sh z; subst z; entailer!; simpl; entailer!.

Lemma EVP_MD_CTX_NNnode_isptr sh vals p:
  EVP_MD_CTX_NNnode sh vals p |-- !!(isptr p).
Proof.
  unfold EVP_MD_CTX_NNnode. destruct vals as [d [mdd [pc pcops]]]. normalize.
  rewrite data_at_isptr. entailer!.
Qed.
Lemma EVP_MD_CTX_NNnode_isptr' sh vals p:
  EVP_MD_CTX_NNnode sh vals p  = (!!(isptr p) &&  EVP_MD_CTX_NNnode sh vals p).
Proof.
  apply pred_ext; [ entailer; apply EVP_MD_CTX_NNnode_isptr | entailer!].
Qed.

Lemma EVP_MD_CTX_NNnode_props sh vals p:
  EVP_MD_CTX_NNnode sh vals p |-- !!(is_pointer_or_null (fst vals) /\ is_pointer_or_null (fst(snd vals))).
Proof. destruct vals as [d [mdd [pc pcops]]]. simpl; entailer!. Qed.

Lemma EVP_MD_CTX_NNnode_props' sh vals p:
  EVP_MD_CTX_NNnode sh vals p = (!!(is_pointer_or_null (fst vals) /\ is_pointer_or_null (fst(snd vals))) &&  EVP_MD_CTX_NNnode sh vals p).
Proof.
  apply pred_ext; [ entailer; apply EVP_MD_CTX_NNnode_props | entailer!].
Qed.

Lemma EVP_MD_CTX_NNnode_props'' sh x1 x2 x3 p:
  EVP_MD_CTX_NNnode sh (x1,(x2,x3)) p = (!!(is_pointer_or_null x1 /\ is_pointer_or_null x2) &&  EVP_MD_CTX_NNnode sh (x1,(x2,x3)) p).
Proof.
  rewrite EVP_MD_CTX_NNnode_props'. simpl. destruct x3.
  apply pred_ext; entailer!.
Qed.

Lemma EVP_MD_CTX_NNnode_validptr sh vals p (SH:readable_share sh):
      EVP_MD_CTX_NNnode sh vals p |-- valid_pointer p.
Proof. unfold EVP_MD_CTX_NNnode. destruct vals as [? [? [? ?]]]. entailer!. Qed.

Hint Resolve EVP_MD_CTX_NNnode_validptr: entailer.


Lemma EVP_MD_CTX_node_null sh vals: EVP_MD_CTX_node sh vals nullval |-- emp.
Proof. apply orp_left; [| rewrite EVP_MD_CTX_NNnode_isptr']; normalize. Qed.

Hint Resolve EVP_MD_CTX_node_null: cancel.

Lemma EVP_MD_CTX_node_validptr sh vals p (SH:readable_share sh):
      EVP_MD_CTX_node sh vals p |-- valid_pointer p.
Proof. apply orp_left; Intros; subst.
  entailer!. apply EVP_MD_CTX_NNnode_validptr; trivial.
Qed.

Hint Resolve EVP_MD_CTX_node_validptr: entailer.

Lemma EVP_MD_NNnode_isptr sh vals p:
  EVP_MD_NNnode sh vals p |-- !!(isptr p).
Proof.
  unfold EVP_MD_NNnode.
  rewrite data_at_isptr. entailer!.
Qed.
Lemma EVP_MD_NNnode_isptr' sh vals p:
  EVP_MD_NNnode sh vals p  = (!!(isptr p) &&  EVP_MD_NNnode sh vals p).
Proof.
  apply pred_ext; [ entailer; apply EVP_MD_NNnode_isptr | entailer!].
Qed.

Lemma EVP_MD_NNnode_validptr sh vals p:  EVP_MD_NNnode sh vals p |-- valid_pointer p.
Proof. unfold EVP_MD_NNnode. entailer!. Qed.

Lemma EVP_MD_node_null vals: EVP_MD_node vals nullval |-- emp.
Proof. apply orp_left; [| Intros sh; rewrite EVP_MD_NNnode_isptr' ]; normalize. Qed.

Hint Resolve EVP_MD_node_null: cancel.

Lemma EVP_MD_node_validptr vals p:  EVP_MD_node vals p |-- valid_pointer p.
Proof. unfold EVP_MD_node.
  apply orp_left; normalize. apply valid_pointer_null.
  apply EVP_MD_NNnode_validptr. 
Qed.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition Gprog_copy : funspecs :=
  [EVP_MD_CTX_init_SPEC; EVP_MD_CTX_copy_ex_SPEC].

Lemma body_EVP_MD_CTX_copy: semax_body Vprog Gprog_copy f_EVP_MD_CTX_copy EVP_MD_CTX_copy_SPEC.
Proof. 
  start_function. 
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCO by entailer!.
  forward_call (octx, osh). (*, (sizeof (Tstruct _env_md_ctx_st noattr))).*)
  destruct case; simpl; Intros.
+ forward_call (gv, octx, nullval, copyEx_ictxNull). simpl; entailer!.
  Intros v. forward. Exists nullval; entailer!.
+ forward_call (gv, octx, ictx, copyEx_indigestNull ish md pv1 pv2). simpl; entailer!.
  Intros v. forward. Exists nullval; entailer!.
+ replace_SEP 0 (data_at osh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) octx).
  { unfold CTX_NULL. entailer!. }
(*  solve [(*holds because of FCout*) entailer!; apply convert; [ apply writable_readable | ]; trivial ].*)
  rewrite data_at_isptr with (p:=d); Intros. 
  forward_call (gv, octx, ictx, copyEx_other ish d md nullval nullval dsh vals 
                osh nullval nullval nullval ctxsz imdsh idata (@None (share * reptype (Tstruct _env_md_st noattr) * int))).
  { simpl. rewrite if_false; [ entailer! | intros N; subst; contradiction]. }

  Intros rv. forward. rewrite if_false by (intros N; subst; contradiction).
  Exists (Vint rv); entailer!.
  apply orp_left; [ apply orp_right1; cancel | apply orp_right2; Intros buf; Exists buf; entailer!].
Time Qed. (*1.3s*)

Definition Gprog_reset : funspecs :=
  [EVP_MD_CTX_init_SPEC; EVP_MD_CTX_cleanup_SPEC].

Lemma body_EVP_MD_CTX_reset: semax_body Vprog Gprog_reset f_EVP_MD_CTX_reset EVP_MD_CTX_reset_SPEC.
Proof. 
  match goal with |- semax_body _ _ ?F ?spec =>
    unfold spec
  end;
  match goal with |- semax_body _ _ ?F (_, ?spec) =>
    unfold spec
  end; start_function.
  forward_call (gv, ctx, sh, mdd, c). Intros.
  forward_call (ctx, sh). (*, sizeof (Tstruct _env_md_ctx_st noattr)).*)
  { unfold CTX_NULL. (*rewrite 2 data_at__memory_block. simpl;*) entailer!. }
  forward.
Qed.

Inductive strong_memcpyCase :=
  smemcpyNull: strong_memcpyCase
| smemcpyNonnull: forall (dsh ssh: share) (data: type_with_content(*list byte*)), strong_memcpyCase.

Definition OPENSSL_memcpy_SPEC_strong {cs:compspecs} := DECLARE _OPENSSL_memcpy
   WITH dst: val, src: val, n: Z, c:strong_memcpyCase
   PRE [ _dst OF tptr tvoid, _src OF tptr tvoid, _n OF tuint ]
       PROP ()
       LOCAL (temp _dst dst; temp _src src; temp _n (Vint (Int.repr n)))
       SEP (match c with
            | smemcpyNull => !!(n=0) && emp
            | smemcpyNonnull dsh ssh data =>
                !!(readable_share ssh /\ writable_share dsh /\ 0 < n <= Int.max_unsigned)
                && data_at ssh (__type data) (__values data) src *
                   memory_block dsh n dst
            end)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp dst)
       SEP(match c with 
            | smemcpyNull => emp
            | smemcpyNonnull dsh ssh data =>
               data_at dsh (__type data) (__values data) dst *
               data_at ssh (__type data) (__values data) src
           end).

Definition Gprog_copy_ex : funspecs :=
  [OPENSSL_memcpy_SPEC_strong; OPENSSL_PUT_ERROR_SPEC; OPENSSL_malloc_SPEC; EVP_MD_CTX_cleanup_SPEC].

Lemma body_EVP_MD_CTX_copy_ex: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC.
Proof.  
  start_function. destruct case; simpl; Intros.
+ (*Case 1: ictxNull*)
  forward_if (PROP ( )
   LOCAL (gvars gv; temp _t'1 (Vint Int.one))  
   SEP (ERRGV gv)); [ clear H; forward; entailer! | inv H | ] .
  subst.
  forward_if (PROP (False) LOCAL () SEP()); [ clear H | inv H ].
  forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                gv ___stringlit_1, Vint (Int.repr 120)).
  forward. Exists nullval. entailer!.
+ (*Case 2: indigestNull*)
  rename H into ISH. rewrite data_at_isptr; Intros.
  forward_if (
   PROP ( )
   LOCAL (gvars gv; temp _t'1 (Vint Int.one); temp _in ictx)
   SEP (ERRGV gv; data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2)))
          ictx)); [ subst; contradiction | forward; forward; entailer! | ]. 

  forward_if (PROP (False) LOCAL () SEP()); [ | inv H ].
  forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                gv ___stringlit_1, Vint (Int.repr 120)).
  forward. Exists nullval. entailer!. 
+ (*Case outdigestNull *)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. subst.
  rename H4 into SZ. rewrite data_at_isptr with (p:=ictx); Intros.
  rewrite data_at_isptr with (p:=d); Intros. 
  freeze [3;4;5;6] FR1. 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'1 (Vint Int.zero); temp _out octx; temp _in ictx)
    SEP (FRZL FR1; ERRGV gv; data_at dsh (Tstruct _env_md_st noattr) vals d;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)).
  { subst; contradiction. }
  { clear H. do 2 forward. entailer!. destruct d; try contradiction; trivial. }

  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _out octx; temp _in ictx)
    SEP (FRZL FR1; ERRGV gv; data_at dsh (Tstruct _env_md_st noattr) vals d;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx));
  [ congruence | forward; entailer! | do 2 forward ].

  forward_if (
    PROP ( )
    LOCAL (temp _pctx (Vint (Int.repr 0)); 
    gvars gv; temp _out octx; temp _in ictx)
    SEP (FRZL FR1; ERRGV gv; data_at dsh (Tstruct _env_md_st noattr) vals d;
    data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx));
  [ contradiction | forward; entailer! | thaw FR1; do 2 forward ].

  destruct_vals vals H3.
  focus_SEP 3.
  forward_if (EX buf:_, EX m:val,
    (PROP ()
    LOCAL (temp _tmp_buf buf; temp _pctx (Vint (Int.repr 0)); gvars gv; temp _out octx; temp _in ictx)
    SEP (memory_block Ews (Int.unsigned ctxsz) buf; 
         OPENSSL_malloc_token (Int.unsigned ctxsz) buf; mm_inv gv;
(*         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vubyte idata) md;*)
         data_at imdsh (__type idata) (__values idata) md *
         data_at osh (Tstruct _env_md_ctx_st noattr) (d', (m, (pv1', nullval))) octx;
         EX dsh' : share, EX vals' : _, EX ctxsz':_, 
         if Val.eq d d' 
         then !!(buf=md' /\ m=nullval) && emp
         else match pp with 
         | None => !!(d'=nullval /\ md'=nullval /\ m=nullval) && emp
         | Some (dsh'', vals'', ctxsz'') =>
                  !! (d<>d' /\ m=md' /\ dsh''=dsh' /\ vals''=vals'/\ctxsz''=ctxsz' /\
                      readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz')
                  && (data_at dsh' (Tstruct _env_md_st noattr) vals' d') * 
                     (   (!!(md' = nullval)&& emp) 
                      || (OPENSSL_malloc_token (Int.unsigned ctxsz') md' * memory_block Ews (Int.unsigned ctxsz') md'))
         end;
         ERRGV gv;
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)))%assert.
  { clear H.
    destruct (Val.eq d d'); Intros; subst. entailer!.
    destruct pp as [[[dsh' vals'] ctxsz'] | ]; entailer!. }
  { (*d' <> d*) 
    apply ptr_comp_Cne_t in H; trivial. rename H into DD'. rewrite if_false by congruence. 
    do 2 forward.
    forward_call (Int.unsigned ctxsz, gv). 
    { rewrite Int.repr_unsigned; simpl; entailer!. }
    { omega. }
    Intros m.
    forward.
    apply semax_orp_SEPx; Intros; subst. 
    { freeze [0;1;2;3;4;6;7] FR2. 
      forward_if (PROP (False) LOCAL () SEP ()).
      + clear H H'. 
        forward_if (
          PROP ( )
          LOCAL (gvars gv; temp _out octx; temp _in ictx)
          SEP (FRZL FR2; ERRGV gv)).
        - contradiction.
        - forward. entailer!.
        - forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                gv ___stringlit_1, Vint (Int.repr 142)).
          forward. Exists nullval; thaw FR2; entailer!.
          rewrite if_false by congruence. apply orp_right1. entailer!. 
          destruct pp as [[[dsh' vals'] ctxsz'] | ]; entailer!. 
      + discriminate.
      + entailer!. }
    { (*rename H into M.*)
      rewrite memory_block_isptr; Intros. freeze [1;2;3;4;5;6;7;8] FR3.
      forward_if (
        PROP ( )
        LOCAL (temp _tmp_buf m; temp _pctx (Vint (Int.repr 0)); 
               gvars gv; temp _out octx; temp _in ictx)
        SEP (memory_block Ews (Int.unsigned ctxsz) m; FRZL FR3)).
      { subst; contradiction. }
      { forward. entailer!. }
      thaw FR3. Exists m md'. entailer!.
      destruct pp as [[[dsh' vals'] ctxsz'] | ]; Intros.
      + Exists dsh' vals' ctxsz'. rewrite if_false by congruence. entailer!.  
      + Exists Ews (default_val (Tstruct _env_md_st noattr)) Int.zero. rewrite if_false by congruence. entailer!. } }
  { (*d' = d*) 
    apply ptr_comp_Cne_f in H; trivial. subst d'. rewrite if_true; trivial; Intros; subst.
    (*rename H0 into M.*)
    do 2 forward; entailer!.
    Exists md' nullval. Exists Ews (default_val (Tstruct _env_md_st noattr)) Int.zero.
    rewrite if_true; trivial. entailer!. }

  Intros buf m dsh' vals' ctxsz'.

  freeze [0;3;6;7;8] FRAME1.
  assert_PROP (if Val.eq d d' then (buf = md' /\ m = nullval)
   else match pp with
      | Some (dsh'', vals'', ctxsz'') =>
          (m = md' /\
              dsh'' = dsh' /\
              vals'' = vals' /\
              ctxsz'' = ctxsz' /\
              readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz')
      | None => (d' = nullval /\ md' = nullval /\ m = nullval)
      end) as PP.
  { destruct (Val.eq d d'). entailer!. destruct pp as [[[? ?] ?] | ]; entailer!. }

  forward_call (gv,octx, osh, m, 
                if Val.eq m nullval 
                then None 
                else match pp with None => None
                           | Some _ => Some (Int.unsigned ctxsz') end).
  { assert (Frame = [FRZL FRAME1; if Val.eq d d' 
             then OPENSSL_malloc_token (Int.unsigned ctxsz) buf
             else 
             match pp with None => OPENSSL_malloc_token (Int.unsigned ctxsz) buf
                  | Some _ => OPENSSL_malloc_token (Int.unsigned ctxsz) buf * 
                              data_at dsh' (Tstruct _env_md_st noattr) vals' d' end]);
       subst Frame. reflexivity. clear H.
    simpl; cancel.
    destruct (Val.eq d d'); Intros.
    + destruct PP; subst. clear H H0. rewrite if_true; trivial. Exists d' pv1'; entailer!.
    + destruct pp as [[[dhs'' vals''] ctxsz''] | ]; Intros.
      - destruct PP as [? [? [? [? ?]]]]. subst. Exists d' pv1'; entailer!.
        
        apply orp_left; Intros; subst.
        * rewrite if_true; trivial. entailer!.
        * rewrite memory_block_isptr; Intros. rewrite if_false; trivial. cancel.
          intros N; subst md'; contradiction.
      - subst. Exists nullval pv1'. rewrite if_true; trivial. entailer!. }
  Intros. rename H into FC0. 
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout rewrite 2 data_at__memory_block; entailer!.*)
    unfold CTX_NULL. entailer!. }
  thaw FRAME1. do 7 forward. simpl. deadvars!.
  forward_call (buf, md, Int.unsigned ctxsz, smemcpyNonnull Ews imdsh idata).
  { rewrite Int.repr_unsigned. simpl; entailer!. }
  { entailer!. }
  Intros. deadvars!.
  do 4 forward.
  Exists (Vint Int.one); entailer!.
  destruct (Val.eq d d'). 
  - destruct PP as [? ?]. subst d' buf m. cancel.
  - apply orp_right2; Exists buf; entailer!. 
    destruct pp as [[[? ?] ?] | ].
    * destruct PP as [? [? [? [? [? ?]]]]]; subst; trivial.
    * destruct PP as [? [? ?]]; subst; cancel.
Time Qed. (*20s*)

Lemma body_EVP_MD_type: semax_body Vprog EmptyGprog f_EVP_MD_type EVP_MD_type_SPEC.
Proof. verif_EVP_MD_component. Qed.

Lemma body_EVP_MD_flags: semax_body Vprog EmptyGprog f_EVP_MD_flags EVP_MD_flags_SPEC.
Proof. verif_EVP_MD_component. Qed.

Lemma body_EVP_MD_size: semax_body Vprog EmptyGprog f_EVP_MD_size EVP_MD_size_SPEC.
Proof. verif_EVP_MD_component. Qed.

Lemma body_EVP_MD_block_size: semax_body Vprog EmptyGprog f_EVP_MD_block_size EVP_MD_block_size_SPEC.
Proof. verif_EVP_MD_component. Qed.

Lemma body_EVP_add_digest: semax_body Vprog EmptyGprog
                           f_EVP_add_digest EVP_add_digest_SPEC.
Proof. start_function. forward. Qed. 

Definition Gprog_EVP_MD_CTX_new : funspecs :=
  [EVP_MD_CTX_init_SPEC; (*OPENSSL_memset_SPEC;*) OPENSSL_malloc_SPEC].

Lemma body_EVP_MD_CTX_new: semax_body Vprog Gprog_EVP_MD_CTX_new f_EVP_MD_CTX_new EVP_MD_CTX_new_SPEC.
Proof.
  match goal with |- semax_body _ _ ?F ?spec =>
    unfold spec
  end;
  match goal with |- semax_body _ _ ?F (_, ?spec) =>
    unfold spec
  end;
  start_function. rename H into ARITH.
  forward_call (sizeof (Tstruct _env_md_ctx_st noattr), gv); [simpl in *; rep_omega | Intros v].
  apply semax_orp_SEPx; Intros; subst.
+ forward_if (PROP ( )  LOCAL (temp _ctx (Vint Int.zero); gvars gv)  SEP (mm_inv gv)).
  - simpl in H; contradiction.
  - forward. entailer!.
  - forward. Exists (Vint Int.zero). entailer!. apply orp_right1; trivial.
+ rewrite OPENSSL_malloc_token_compatible' by (simpl; omega); Intros.
  rename H into MC.
  rewrite memory_block_data_at_ by (apply OPENSSLmalloc_compatible_field_compatible; simpl; trivial).
  forward_if (PROP ( ) LOCAL (temp _ctx v; gvars gv)  
              SEP (mm_inv gv; OPENSSL_malloc_token 16 v; 
                   CTX_NULL Ews v (*data_at_ Ews (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) v*))).
  - apply denote_tc_test_eq_split. 
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    eapply data_at__valid_pointer. apply writable_nonidentity. apply writable_Ews. (*top_share_nonidentity.*) simpl; omega.
    apply valid_pointer_null.
  - forward_call (v, Ews). (*, sizeof (Tstruct _env_md_ctx_st noattr)).*) entailer!.
  - subst; rewrite data_at__isptr. normalize.
  - forward. Exists v. entailer!. apply orp_right2; trivial. 
Qed.

Definition Gprog_EVP_MD_CTX_create : funspecs := [ EVP_MD_CTX_new_SPEC].

Lemma body_EVP_MD_CTX_create: semax_body Vprog Gprog_EVP_MD_CTX_create f_EVP_MD_CTX_create EVP_MD_CTX_create_SPEC.
Proof.
  match goal with |- semax_body _ _ ?F ?spec =>
    unfold spec
  end;
  match goal with |- semax_body _ _ ?F (_, ?spec) =>
    unfold spec
  end;
  start_function.
  forward_call gv. Intros ctx. forward. Exists ctx. entailer!.
Qed.

Definition Gprog_EVPMDCTX_1 : funspecs :=
  [EVP_MD_CTX_create_SPEC; EVP_MD_CTX_init_SPEC; OPENSSL_memset_SPEC; OPENSSL_malloc_SPEC].

Lemma body_EVP_MD_CTX_init: semax_body Vprog Gprog_EVPMDCTX_1 f_EVP_MD_CTX_init EVP_MD_CTX_init_SPEC.
Proof.
  start_function.
  rewrite data_at__memory_block; simpl; Intros. 
  forward_call (ctx, 16, Byte.zero, memsetNonnull sh). entailer!.
  forward.
  unfold CTX_NULL. apply convert; trivial. apply writable_readable; trivial.
Qed.

Definition Gprog_DigAccessOps : funspecs :=
  ltac:(with_library prog [EVP_MD_block_size_SPEC; EVP_MD_type_SPEC; EVP_MD_size_SPEC  (*called*);
   EVP_MD_CTX_md_SPEC; EVP_MD_CTX_size_SPEC; EVP_MD_CTX_block_size_SPEC; EVP_MD_CTX_type_SPEC] ).
(*  [EVP_MD_block_size_SPEC; EVP_MD_type_SPEC; EVP_MD_size_SPEC  (*called*);
   EVP_MD_CTX_md_SPEC; EVP_MD_CTX_size_SPEC; EVP_MD_CTX_block_size_SPEC; EVP_MD_CTX_type_SPEC].*)

Ltac verif_EVP_MD_CTX_component :=
  start_function;
  match goal with [ ctx:val, sh:share, d:val, x : val * (val * val), D: EVP_MD  |- ?P ] =>
       rewrite  EVP_MD_CTX_NNnode_isptr'; Intros;
       forward_call (ctx, sh, d, x);
       [ apply sepcon_derives; [apply orp_right2; trivial | cancel]
       | rewrite if_false by (destruct ctx; try contradiction; discriminate);
         forward_call (d,D); forward; cancel;
         apply orp_left; [ Intros; subst; contradiction | simpl; entailer! ] ]
  end.

Lemma body_EVP_MD_CTX_block_size: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_block_size EVP_MD_CTX_block_size_SPEC.
Proof. verif_EVP_MD_CTX_component. Qed.

Lemma body_EVP_MD_CTX_type: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_type EVP_MD_CTX_type_SPEC.
Proof. verif_EVP_MD_CTX_component. Qed.

Lemma body_EVP_MD_CTX_size: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_size EVP_MD_CTX_size_SPEC.
Proof. verif_EVP_MD_CTX_component. Qed.

Lemma body_EVP_MD_CTX_md: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_md EVP_MD_CTX_md_SPEC.
Proof.
  match goal with |- semax_body _ _ ?F ?spec =>
    first [ unfold spec | idtac]
  end;
  match goal with |- semax_body _ _ ?F (?G, ?spec) =>
    first [ unfold spec | idtac]
  end;
  start_function.
  destruct x as [mddata [pctx pctxops]].
  forward_if (
      PROP ()
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, (mddata, (pctx, pctxops))) ctx)). 
+ clear H. apply orp_left; [ entailer! | unfold EVP_MD_CTX_NNnode; normalize; entailer!].
+ subst. forward.
+ forward. entailer. apply orp_left; normalize. simpl; trivial.
+ simpl. rewrite data_at_isptr; Intros. destruct ctx; try contradiction. clear Pctx. (*unfold EVP_MD_CTX_NNnode.*)
  forward. forward.
  apply orp_right2. simpl. entailer!.
Qed.

Definition Gprog_cleanup : funspecs :=
  (*FAILS: ltac:(with_library prog [OPENSSL_cleanse_SPEC; OPENSSL_free_SPEC; EVP_MD_CTX_init_SPEC]). *)
  [(*OPENSSL_cleanse_SPEC;*) OPENSSL_free_SPEC; EVP_MD_CTX_init_SPEC].

Lemma body_EVP_MD_CTX_cleanup: semax_body Vprog Gprog_cleanup f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC.
Proof. 
  match goal with |- semax_body _ _ ?F ?spec =>
    unfold spec
  end;
  match goal with |- semax_body _ _ ?F (_, ?spec) =>
    unfold spec
  end; start_function. Intros d pv1. unfold EVP_MD_CTX_NNnode; Intros. forward.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] ctx) as FC by entailer!.
  destruct c.
+ rewrite OPENSSL_malloc_token_compatible', memory_block_isptr; Intros.
  rename H into MC; rename H0 into Zpos.
  forward_call (mdd, z, gv).
  { rewrite if_false by (intros N; subst mdd; contradiction). 
    (* rewrite distrib_orp_sepcon; apply orp_right2;*) entailer!. }
  forward.
  forward_if (
     PROP ( )
     LOCAL (temp _ctx ctx)
     SEP (mm_inv gv; data_at sh (Tstruct _env_md_ctx_st noattr)
          (d, (mdd, (pv1, nullval))) ctx));
  [ contradiction | forward; entailer! | ].
  forward_call (ctx, sh). (*, sizeof (Tstruct _env_md_ctx_st noattr)).*)
  forward. (*cancel.*)
+ Intros; subst mdd. forward_call (nullval, 0, gv). 
  { (*rewrite distrib_orp_sepcon; apply orp_right1;*) rewrite if_true by trivial; entailer!. }
  forward.
  forward_if (
     PROP ( )
     LOCAL (temp _ctx ctx)
     SEP (mm_inv gv; data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1, nullval))) ctx));
  [ contradiction | forward; entailer! | ].
  forward_call (ctx, sh). (*, sizeof (Tstruct _env_md_ctx_st noattr)).*)
  forward. (*cancel.*)
Qed.
(*Alternative:
Variant cleanup_cases :=
  CleanupCase_DataNull: cleanup_cases
| CleanupCase_dataPtr : share -> reptype (Tstruct _env_md_st noattr) -> val -> cleanup_cases.

Definition cleanupPRE (c: cleanup_cases) d (mdd:val): mpred :=
  match c with
  CleanupCase_DataNull => !!(mdd=nullval) && emp
| CleanupCase_dataPtr dsh vals dd =>
            EX ctxsz:int,
             !!(dd=d /\ get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false) &&
             EVP_MD_NNnode dsh vals d * memory_block Ews (Int.unsigned ctxsz) mdd
  end.
Definition cleanupPOST (c: cleanup_cases) d (mdd:val): mpred :=
  match c with
  CleanupCase_DataNull => emp
| CleanupCase_dataPtr dsh vals dd =>
             EVP_MD_NNnode dsh vals d
  end.

Definition EVP_MD_CTX_cleanup_SPEC5 := DECLARE _EVP_MD_CTX_cleanup
  WITH ctx:val, sh:share, d: val, pv1:val, c: cleanup_cases, mdd:val
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (writable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, (mdd, (pv1, nullval))) ctx; 
           cleanupPRE c d mdd)
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (data_at_ sh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx;
            cleanupPOST c d mdd).
(*could (should?) strengthen at data_at_ to data_at list_repeat .. 0*)

Lemma body_EVP_MD_CTX_cleanup5: semax_body Vprog Gprog_cleanup f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC5.
Proof. 
  start_function. unfold EVP_MD_CTX_NNnode; Intros. forward.
  destruct c; simpl; Intros.
+ subst mdd. forward_call (nullval, 0). 
  { rewrite distrib_orp_sepcon; apply orp_right1; entailer!. }
  forward.
  forward_if (
     PROP ( )
     LOCAL (temp _ctx ctx)
     SEP (data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1, nullval))) ctx));
  [ contradiction | forward; entailer! | ].
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
  forward. cancel.
+ Intros sz; subst.
  forward_call (mdd, Int.unsigned sz).
  { rewrite distrib_orp_sepcon; apply orp_right2; entailer!. }
  forward.
  forward_if (
     PROP ( )
     LOCAL (temp _ctx ctx)
     SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (d, (mdd, (pv1, nullval))) ctx; EVP_MD_NNnode s r d));
  [ contradiction | forward; entailer! | ].
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
  forward. cancel.
Qed.
*)

Definition Gprog_free : funspecs :=
  [OPENSSL_free_SPEC; EVP_MD_CTX_cleanup_SPEC].

Lemma body_EVP_MD_CTX_free: semax_body Vprog Gprog_free f_EVP_MD_CTX_free EVP_MD_CTX_free_SPEC.
Proof. 
  match goal with |- semax_body _ _ ?F ?spec =>
    unfold spec
  end;
  match goal with |- semax_body _ _ ?F (_, ?spec) =>
    unfold spec
  end; 
  start_function.
  apply semax_orp_SEPx; Intros; subst.
{ (*ctx=nullval*)
  forward_if (PROP ( False )  LOCAL ()  SEP ()).
  + forward.
  + discriminate. }
unfold EVP_MD_CTX_NNnode; Intros. rewrite data_at_isptr; Intros.
forward_if (PROP ( )  LOCAL (gvars gv; temp _ctx ctx)  
            SEP (data_at Ews (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, nullval))) ctx;
   match c with
   | Some sz => memory_block Ews sz md * OPENSSL_malloc_token sz md
   | None => !! (md = nullval) && emp
   end; OPENSSL_malloc_token (sizeof (Tstruct _env_md_ctx_st noattr)) ctx; mm_inv gv)).
{ subst; contradiction. }
{ forward. entailer!. } 
forward_call (gv, ctx, Ews, md, c).
{ unfold EVP_MD_CTX_NNnode. Exists d pv1. entailer!. }
unfold CTX_NULL. sep_apply (data_at_memory_block Ews (Tstruct _env_md_ctx_st noattr)
          (nullval, (nullval, (nullval, nullval))) ctx); simpl.
(* rewrite data_at__memory_block; Intros.*)
forward_call (ctx, sizeof (Tstruct _env_md_ctx_st noattr), gv).
{ (*rewrite distrib_orp_sepcon. apply orp_right2.*)
  rewrite if_false by (destruct ctx; try contradiction; discriminate). simpl; entailer!. }
forward.
Qed. 

Definition Gprog_destroy : funspecs :=
  [EVP_MD_CTX_free_SPEC].

Lemma body_EVP_MD_CTX_destroy: semax_body Vprog Gprog_destroy f_EVP_MD_CTX_destroy EVP_MD_CTX_destroy_SPEC.
Proof.
  match goal with |- semax_body _ _ ?F ?spec =>
    unfold spec
  end;
  match goal with |- semax_body _ _ ?F (_, ?spec) =>
    unfold spec
  end; 
  start_function.
  forward_call (gv, ctx, d, md, pv1, c).
  forward.
Qed.

Lemma body_DigestUpdate: 
      semax_body Vprog EmptyGprog f_EVP_DigestUpdate EVP_DigestUpdate_SPEC.
Proof. 
  start_function. rename SH0 into DSH. rename SH1 into WSH.
  rename H into SC. rewrite EVP_MD_rep_isptr'; Intros. rename H into isptrTp.
  destruct CTX as [tp [md [pv1 pv2]]]. simpl in tp, md, pv1, pv2, isptrTp; simpl. forward.
  unfold EVP_MD_rep. Intros sht vals. rename H into Rsht. 
  destruct_vals vals Rsht; Intros. forward.
  freeze [3;5;6] FR1.  
  Time forward_call (DC, ctx, sh, (tp, (md, (pv1, pv2))),
                d, dsh, data, len, mdsh). (*37s*)
  { simpl; cancel. }
  forward. (*4s*) thaw FR1; unfold EVP_MD_rep. cancel.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists sht z; subst z. entailer!. simpl. entailer!.
Qed.

Definition Gprog_DigestFinal_ex : funspecs :=
  [OPENSSL_cleanse_SPEC].

Lemma body_DigestFinal_ex: semax_body Vprog Gprog_DigestFinal_ex f_EVP_DigestFinal_ex EVP_DigestFinal_ex_SPEC.
Proof. 
  start_function. subst.  (*rename H into CTXSZ.*)
  rename SH0 into OSH. rename SH1 into MDSH.
  rewrite EVP_MD_rep_isptr'; Intros. rename H into isptrD.
  unfold EVP_MD_rep. Intros csh vals. rename H into Rcsh. rename H0 into SZ.
  destruct CTX as [d [md [pv1 pv2]]]; simpl in d, md, pv1, pv2, isptrD; simpl.
  forward.
  destruct_vals vals Rcsh. Intros.
  forward. 
  forward_call (DC, ctx, sh, (d, (md, (pv1, pv2))), 
                out, osh, mdsh, md_size_of_MD (__EVP_MD DC)).
  { simpl; cancel. }
  simpl. replace_SEP 1 (!!(is_pointer_or_null md) &&
               postFin mdsh (__EVP_MD DC) md).
  { entailer. apply postFin_pTN. } 
  Intros. 
  forward_if (PROP ( )
   LOCAL (temp _ctx ctx; temp _md_out out; temp _size sz)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ctx;
        postFin mdsh (__EVP_MD DC) md;
        data_block osh (FIN DC) out;
        if Val.eq sz nullval then emp else data_at Ews tuint (Vint (Int.repr (md_size_of_MD (__EVP_MD DC)))) sz;
        EVP_MD_rep (__EVP_MD DC) d)).
   { apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer2 | apply valid_pointer_null].
     destruct (Val.eq sz nullval); [subst; apply valid_pointer_null | apply data_at__valid_pointer; intuition ]. }
   { forward. forward. rewrite if_false; trivial.
     forward. rewrite if_false; trivial. entailer!. unfold EVP_MD_rep.
     evar (z:reptype (Tstruct digests._env_md_st noattr)).
     Exists csh z; subst z. entailer!. simpl. entailer!. }
   { subst. forward. entailer!. unfold EVP_MD_rep.
     evar (z:reptype (Tstruct digests._env_md_st noattr)).
     Exists csh z; subst z. entailer!. simpl. entailer!. }
   clear csh Rcsh.
   forward. forward. unfold EVP_MD_rep. Intros csh vals. rename H4 into Rcsh. subst. clear upd ini fin.
   destruct_vals vals Rcsh. Intros. forward.
   specialize WA_WORD_nonneg; intros WAW. deadvars!.
(*   unfold postFin; Intros findata. unfold MD_state; Intros finbytes.
   replace_SEP 1 (memory_block mdsh (ctx_size_of_MD (__EVP_MD DC)) md).
   { entailer!. unfold data_block. rewrite H4; simpl.
     eapply derives_trans. apply data_at_memory_block.
     simpl. rewrite Z.mul_1_l, Z.max_r. trivial. omega. }*)
   forward_call (md, mdsh, ctx_size_of_MD (__EVP_MD DC)).
   { unfold postFin; Intros findata. unfold (*MD_state, *)data_block(*; Intros finbytes*).
     (*sep_apply (data_at_memory_block mdsh (tarray tuchar (Zlength findata)) (map Vubyte findata) md). 
     simpl in H4. rewrite <- H4.
     simpl. rewrite Z.mul_1_l, Z.max_r. cancel. omega.*)
     sep_apply (data_at_memory_block mdsh (__type findata) (__values findata) md); simpl.
     rewrite <- H4. cancel. }
   { intuition. }
(*   replace_SEP 1 (memory_block mdsh (ctx_size_of_MD (__EVP_MD DC)) md).
   { entailer!. unfold data_block. rewrite H4; simpl.
     eapply derives_trans. apply data_at_memory_block.
     simpl. rewrite Z.mul_1_l, Z.max_r. trivial. omega.split; trivial; rep_omega. }*)
   forward. unfold EVP_MD_rep. entailer!.
   evar (z:reptype (Tstruct digests._env_md_st noattr)).
   Exists csh z; subst z. entailer!. simpl. entailer!.
   unfold postFin, MD_state, data_block. cancel. 
   (*Exists (list_repeat (Z.to_nat (ctx_size_of_MD (__EVP_MD DC))) Byte.zero).
   rewrite Zlength_list_repeat by (rewrite <- H5; apply Zlength_nonneg).
   entailer!.
   rewrite map_list_repeat. trivial.*)
   Exists ((*Build_type_with_content _*)twc
              (tarray tuchar (ctx_size_of_MD (__EVP_MD DC)))
              (list_repeat (Z.to_nat (ctx_size_of_MD (__EVP_MD DC))) (Vubyte Byte.zero))); simpl.
   entailer!.
Qed.

Definition Gprog_DigestFinal : funspecs :=
  [EVP_DigestFinal_ex_SPEC; EVP_MD_CTX_cleanup_SPEC].

Lemma body_DigestFinal: semax_body Vprog Gprog_DigestFinal f_EVP_DigestFinal EVP_DigestFinal_SPEC.
Proof. 
  start_function. rename H into CTXSZ. (*rename H0 into PV2.*)
  rename SH0 into Wosh.
  (*specialize WA_WORD_nonneg; intros WW. *)
  forward_call (ctx, sh, CTX, out, osh, sz, DC, Ews). 
 (* { intuition. }*)
  destruct CTX as [d [mdd [pv1 pv2]]]; simpl in d, mdd, pv1, pv2(*, PV2*),CTXSZ; subst; simpl.
  rewrite EVP_MD_rep_isptr'; Intros; simpl.
  assert_PROP (4 <= ctx_size_of_MD (__EVP_MD DC) <= Int.max_unsigned - (WA + WORD) - 8) as SZ by (unfold EVP_MD_rep; entailer).
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] ctx) as FC by entailer!.
  replace_SEP 1 (memory_block Ews (ctx_size_of_MD (__EVP_MD DC)) mdd).
  { entailer!. apply postFin_memory_block. }
  unfold EVP_MD_rep. Intros csh vals. rename H into Rcsh.
  freeze [4;5] FR1.
  destruct_vals vals Rcsh. Intros.
  assert_PROP (is_pointer_or_null mdd) as PtrN_Mdd by entailer!. 
  forward_call (gv, ctx, sh, mdd, Some (ctx_size_of_MD (__EVP_MD DC))).
  { Exists d pv1. unfold EVP_MD_CTX_NNnode. entailer!. }
  forward. thaw FR1; cancel. unfold EVP_MD_rep, EVP_MD_NNnode.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists csh z; subst z. (*unfold CTX_NULL.*) (* rewrite 2 data_at__memory_block.*) entailer!. simpl. entailer!.
Qed.

Ltac remember_vals vals :=
  let f := fresh "f" in
  remember vals as f;
   destruct f as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]];
  simpl in type, mds, flags, ini, upd, fin, blsize, ctxsize; simpl; Intros.

Definition Gprog_DigestInit_ex : funspecs :=
  [OPENSSL_PUT_ERROR_SPEC; OPENSSL_free_SPEC; OPENSSL_malloc_SPEC].

Lemma body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC.
Proof. 
  start_function. (*rename H into SZ.*) destruct pv as [pv1 pv2]. 
  specialize WA_WORD_nonneg; intros WAWnn. 
  unfold EVP_MD_CTX_NNnode; Intros.
  forward.
  rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  deadvars!. destruct c; Intros; subst.
+ (*Case DIEC_EQ*)
  forward_if (PROP ( )
     LOCAL (gvars gv; temp _ctx ctx)
     SEP (data_at csh (Tstruct _env_md_ctx_st noattr) (t, (mdd, (pv1, pv2))) ctx;
          ERRGV gv; match_EVP_MD T tvals; preInit Ews (ctx_size_of_MD T) mdd;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { apply ptr_comp_Cne_t in H; congruence. }
    { forward. entailer!. }
  forward.
  remember_vals tvals.
  freeze [1;3;4] FR1.
  forward.
  Time forward_call (ctx, csh, (t, (mdd, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews). (*23s*)
    { rewrite Int.unsigned_repr by omega. simpl; cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
  deadvars!. thaw FR1. subst; simpl. forward.
  Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists tsh z; subst z. entailer!. simpl. entailer!.
+ (*Case DIEC_NEQ*)
  rename H into DT.
  forward_if (
     PROP ()
     LOCAL(gvars gv; temp _ctx ctx)
     SEP (EX m:_, ((*!!(malloc_compatible (ctx_size_of_MD T) m) 
                   &&*) memory_block Ews (ctx_size_of_MD T) m *
                      OPENSSL_malloc_token (ctx_size_of_MD T) m *
                      data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx); 
          ERRGV gv; mm_inv gv;
          match_EVP_MD T tvals;
          match o with
           | None => emp
           | Some (dsh, dvals) => EVP_MD_NNnode dsh dvals d
          end;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
  3: solve [apply ptr_comp_Cne_f in H; subst; trivial; [ contradiction | apply isptr_is_pointer_or_null; trivial]].
  solve [ destruct o as [[dsh dvals] | ]; Intros; [unfold EVP_MD_NNnode | ]; entailer!].
  { clear H; deadvars!. remember_vals tvals.
      freeze [0;1;2;3;4;6;8] FR1.
      forward.
      forward_call (ctx_size_of_MD T, gv). omega.
      Intros m. forward. deadvars!.
      apply semax_orp_SEPx; Intros.
      + subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - clear H H'; thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          forward. Exists nullval; unfold EVP_MD_rep; entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z; simpl. entailer!.
          simpl. entailer!. unfold DIE_postMpred. simpl.
          apply sepcon_derives;
          [ apply orp_right1; destruct o0 as [[l L] | ]; simpl; entailer!
          | destruct o as [[v D] | ]; Intros; trivial ].
        - discriminate.
      + rewrite memory_block_isptr; Intros.
        forward_if (PROP ( )
            LOCAL (gvars gv; temp _md_data m; temp _type t; temp _ctx ctx)
            SEP (memory_block Ews (ctx_size_of_MD T) m;
                 OPENSSL_malloc_token (ctx_size_of_MD T) m;
                 mm_inv gv; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - abbreviate_semax; thaw FR1.
          freeze [0;1;3;5;6;7;9;10] FR2.
          forward. unfold DIE_preMpred. 
          forward_call (mdd, match o0 with None => 0 | Some (D,tpv) => (sizeof (__type tpv))(*ctx_size_of_MD D*) end, gv).
          { destruct o0 as [[D [tp v]] | ]; simpl. 
            * Time (rewrite OPENSSL_malloc_token_compatible' ; Intros).
              (*sep_apply (data_at_memory_block Ews (tarray tuchar (ctx_size_of_MD D)) v mdd).
                simpl; rewrite Z.mul_1_l, Z.max_r by omega.*)
              (*sep_apply (MD_state_memoryblock Ews DC mdd).*)
              (*sep_apply (data_at_memory_block Ews (tarray tuchar (ctx_size_of_MD D)) (map Vubyte v) mdd); simpl.
              rewrite if_false by (destruct mdd; try contradiction; discriminate).
              entailer!. cancel.*)
              sep_apply (data_at_memory_block Ews tp v mdd); simpl.
              rewrite if_false by (destruct mdd; try contradiction; discriminate).
              rewrite H5. entailer!.
            * Intros; subst. rewrite if_true by reflexivity. cancel. }
          deadvars!. do 2 forward. thaw FR2. Exists m; entailer!.
          destruct o as [[dsh dvals] | ]; Intros; trivial.  }
  Intros m. 
  freeze [1;3;4;6] FR3. forward.
  remember_vals tvals. (* subst type mds flags blsize ctxsize.*)
  freeze [0;4;5] FR4.
  forward.
  sep_apply (preInit_fresh_EWS (ctx_size_of_MD T) m); [ rep_omega |].
  forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
  { rewrite Int.unsigned_repr by omega. simpl; cancel. }
  { rewrite Int.unsigned_repr by omega. subst tvals; repeat (split; trivial); omega. }
  deadvars!. subst tvals; simpl. forward.
  Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists tsh z; subst z. entailer!.
  simpl. entailer!. thaw FR4; thaw FR3. cancel. apply orp_right2. simpl. Exists m; entailer!.
Time Qed. (*57s*)

Definition Gprog_DigestInit : funspecs :=
  [EVP_DigestInit_ex_SPEC; EVP_MD_CTX_init_SPEC].

Lemma body_DigestInit: semax_body Vprog Gprog_DigestInit f_EVP_DigestInit EVP_DigestInit_SPEC.
Proof. 
  start_function.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] ctx) as FC by entailer!.
  forward_call (ctx, csh). 
  replace_SEP 0 (data_at csh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx).
  unfold CTX_NULL; entailer!. (*solve [entailer!; apply convert; [ apply writable_readable | ]; trivial ].*)
  rewrite EVP_MD_rep_isptr'; Intros.
  forward_call (ctx, t, nullval, nullval, nullval, (nullval, nullval), T, gv, csh, DIEC_NEQ None None).
  solve [simpl; entailer!].
  Intros rv. forward. Exists (Vint rv). entailer!.
Qed.

Definition Gprog_EVP_Digest : funspecs :=
  [EVP_MD_CTX_init_SPEC; EVP_DigestInit_ex_SPEC; EVP_DigestUpdate_SPEC;
   EVP_DigestFinal_ex_SPEC; EVP_MD_CTX_cleanup_SPEC].

Lemma body_EVP_Digest: semax_body Vprog Gprog_EVP_Digest
                           f_EVP_Digest EVP_Digest_SPEC.
Proof. start_function.
  rename H into CTXSZ. (*rename H0 into UPDSC.*)
  rename SH into DSH. rename SH0 into OSH.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] v_ctx) as FCctx by entailer!.
  rewrite (EVP_MD_rep_isptr'); Intros.
  forward_call (v_ctx, Tsh). (*, sizeof (Tstruct _env_md_ctx_st noattr)).*)
  replace_SEP 0 (data_at Tsh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) v_ctx).
  unfold CTX_NULL; entailer!.
  (*solve [entailer!; apply convert; [ apply writable_readable | ]; trivial ].*)
  forward_call (v_ctx, t, e, nullval, nullval, (nullval, nullval), D, gv, Tsh, DIEC_NEQ None None).
  { simpl; entailer!. }
  Intros ret1. deadvars!. focus_SEP 2.
  apply semax_orp_SEPx; simpl.
+ (* ret1 == null*)
  Intros; subst. freeze [0;1;2;3;4;5;6;7;8] FR3.
  forward_if (
   PROP ( )
   LOCAL (temp _t'2 (Vint Int.zero); lvar _ctx (Tstruct _env_md_ctx_st noattr) v_ctx;
          gvars gv; temp _data d; 
          temp _count (Vint cnt); temp _out_md md; temp _out_size sz)
   SEP (FRZL FR3)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }
  forward_if (
   PROP ( )
   LOCAL (temp _t'4 (Vint Int.zero); lvar _ctx (Tstruct _env_md_ctx_st noattr) v_ctx;
          gvars gv; temp _data d; 
          temp _count (Vint cnt); temp _out_md md; temp _out_size sz)  SEP (FRZL FR3)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }
  forward. deadvars!. thaw FR3. unfold EVP_MD_rep. Intros tsh tvals. rename H into Rtsh.
  destruct_vals tvals CTXSZ; Intros.
  forward_call (gv,v_ctx, Tsh, nullval, @None Z).
  { Exists nullval nullval. unfold EVP_MD_CTX_NNnode. entailer!. }
  replace_SEP 0 (data_at_ Tsh (Tstruct _env_md_ctx_st noattr) v_ctx).
  { unfold CTX_NULL; entailer!. (* rewrite 2 data_at__memory_block. simpl; entailer!.*) }
  forward.
  Exists Int.zero. entailer!. unfold EVP_MD_rep, EVP_MD_NNnode.
  evar (z:reptype (Tstruct _env_md_st noattr)).
  Exists tsh z; subst z. entailer!. simpl. entailer!. apply orp_right1; cancel.
+ Intros m; subst.
  specialize readable_share_top; specialize WA_WORD_nonneg; intros WAWnn RST.
  forward_if (
     PROP () 
     LOCAL (temp _t'2 (Vint Int.one);
            lvar _ctx (Tstruct _env_md_ctx_st noattr) v_ctx;
            gvars gv; temp _data d; 
            temp _count (Vint cnt); temp _out_md md; temp _out_size sz)
     SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) v_ctx; 
          data_block dsh Data d; 
          MD_state Ews (UPD (INI D) Data (Int.unsigned cnt)) m;
          EVP_MD_rep D t;  ERRGV gv;
          OPENSSL_malloc_token (ctx_size_of_MD D) m; mm_inv gv;
          if Val.eq sz nullval then emp else data_at_ Ews tuint sz; memory_block osh (md_size_of_MD D) md));
    [ clear H H' | solve [inv H] |].
  {  (*Maybe add case to updspec for d==nullval? maybe 
        enforce ctxsz=get_ctxsize tvals again in precond of update?*) 
    forward_call (v_ctx, Tsh, (t, (m, (nullval, nullval))), d, dsh, Data, INI D, Int.unsigned cnt, Ews).
    * rewrite Int.repr_unsigned; trivial; entailer!.
    * simpl; cancel.
    * forward. entailer!. }
  forward_if (
    PROP ( )
    LOCAL (temp _t'4 (Vint Int.one);
           lvar _ctx (Tstruct _env_md_ctx_st noattr) v_ctx;
           gvars gv; temp _data d; 
           temp _count (Vint cnt); temp _out_md md; temp _out_size sz)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) v_ctx;
         postFin Ews D m;
         EVP_MD_rep D t;OPENSSL_malloc_token (ctx_size_of_MD D) m; mm_inv gv;
         if Val.eq sz nullval then emp else data_at Ews tuint (Vint (Int.repr (md_size_of_MD D))) sz;
         data_block osh (FIN (UPD (INI D) Data (Int.unsigned cnt))) md; data_block dsh Data d; ERRGV gv));
    [ clear H | solve [inv H] |].
  { forward_call (v_ctx, Tsh, (t, (m, (nullval, nullval))), md, osh, sz, UPD (INI D) Data (Int.unsigned cnt), Ews).
    { simpl; cancel. }
(*    { simpl. repeat (split; trivial); try omega.  }*)
    forward. entailer!. }
  forward. deadvars!.
  replace_SEP 1 (memory_block Ews (ctx_size_of_MD D) m).
  { go_lower. apply postFin_memory_block. }
  (*VSTbug: sep_apply (postFin_memory_block Ews D m). fails*)
  unfold EVP_MD_rep. Intros tsh tvals. rename H into Rtsh.
  destruct_vals tvals tsh. Intros.
  forward_call (gv,v_ctx, Tsh, m, Some (ctx_size_of_MD D)).
  { Exists t nullval; unfold EVP_MD_NNnode; simpl. entailer!. }
  replace_SEP 0 (data_at_ Tsh (Tstruct _env_md_ctx_st noattr) v_ctx).
  { unfold CTX_NULL; entailer!. (* rewrite 2 data_at__memory_block. simpl; entailer!.*) }
  forward. Exists Int.one. entailer!.
  unfold EVP_MD_rep, EVP_MD_NNnode.
  evar (z:reptype (Tstruct _env_md_st noattr)).
  Exists tsh z; subst z. entailer!. simpl. entailer!.
  apply orp_right2. entailer!.
Time Qed. (*6s*)