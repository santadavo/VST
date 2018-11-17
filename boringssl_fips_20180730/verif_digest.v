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

  unfold at_offset; simpl. unfold mapsto. simpl. rewrite ! if_true; trivial. apply orp_right1.
  rewrite distrib_orp_sepcon. apply orp_left; Intros.
  repeat rewrite <- sepcon_assoc. rewrite sepcon_comm.
  rewrite distrib_orp_sepcon. apply orp_left; Intros.
  repeat rewrite <- sepcon_assoc. rewrite sepcon_comm.
  rewrite distrib_orp_sepcon. apply orp_left; Intros.
  repeat rewrite <- sepcon_assoc. rewrite sepcon_comm.
  rewrite distrib_orp_sepcon. apply orp_left; Intros.
  unfold nullval. destruct (Archi.ptr64). admit. 
  unfold res_predicates.address_mapsto. 
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
data_at_singleton_array_eq*)*)
Admitted.

Lemma Valeq_Vint {A} i j (a b:A):
      (if Val.eq (Vint i) (Vint j) then a else b) =
      (if Int.eq i j then a else b).
Proof. 
 remember (Int.eq i j). destruct b0.
+ rewrite ( binop_lemmas2.int_eq_true _ _ Heqb0). rewrite if_true; trivial.
+ remember (Val.eq (Vint i )(Vint j)) as d.
  destruct d; trivial.
  inversion e; subst; simpl in *.
  specialize (int_eq_false_e j j); intuition.
Qed. 

Require Import List.  Import ListNotations.

Lemma ptr_comp_Cne_t p q (P: is_pointer_or_null p) (Q: is_pointer_or_null q): 
      typed_true tint (force_val (sem_cmp_pp Cne p q)) <-> ~(p=q).
Proof.
  destruct p; destruct q; try contradiction; simpl in *; subst;
  unfold typed_true, sem_cmp_pp; simpl; split; intros; trivial; try solve [inv H].
+ elim H; trivial.
+ intros N; inv N. rewrite if_true, Ptrofs.eq_true in H; trivial; inv H.
+ destruct (eq_block b b0); subst; trivial.
  destruct (Ptrofs.eq_dec i i0); subst; [ elim H; trivial | rewrite Ptrofs.eq_false; trivial].
Qed.

Lemma ptr_comp_Cne_t' {T} p q 
      (H: typed_true tint (force_val (sem_cmp_pp Cne p q)))
       (a b:T) (P: is_pointer_or_null p)
               (Q: is_pointer_or_null q):
      (if Val.eq p q then a else b) = b.
Proof. apply ptr_comp_Cne_t in H; trivial.
  rewrite if_false; trivial.
Qed.

Lemma ptr_comp_Cne_f p q (P: is_pointer_or_null p) (Q: is_pointer_or_null q): 
      typed_false tint (force_val (sem_cmp_pp Cne p q)) <-> (p=q).
Proof.
  destruct p; destruct q; try contradiction; simpl in *; subst;
  unfold typed_false, sem_cmp_pp; simpl; split; intros; trivial; try solve [inv H].
+ destruct (eq_block b b0); [subst; simpl in H | inv H].
  destruct (Ptrofs.eq_dec i i0); subst; trivial.
  rewrite Ptrofs.eq_false in H; trivial; inv H. 
+ inv H. rewrite if_true, Ptrofs.eq_true; trivial. 
Qed.

Lemma ptr_comp_Cne_f' {T} p q 
      (H: typed_false tint (force_val (sem_cmp_pp Cne p q)))
       (a b:T) (P: is_pointer_or_null p)
               (Q: is_pointer_or_null q):
      (if Val.eq p q then a else b) = a.
Proof. apply ptr_comp_Cne_f in H; trivial.
  rewrite if_true; trivial.
Qed.

Lemma data_at__valid_pointer {cs : compspecs} sh t p:
  sepalg.nonidentity sh ->
  sizeof t > 0 ->
  @data_at_ cs sh t p |-- valid_pointer p.
Proof. intros. unfold data_at_, field_at_. apply field_at_valid_ptr0; simpl; trivial. Qed.

Lemma func_ptr'_isptr' v f: (func_ptr' f v) = ((!! isptr v) && func_ptr' f v).
Proof. apply pred_ext; entailer!. Qed.

Lemma writable_nonidentity sh (W:writable_share sh): sepalg.nonidentity sh.
Proof. apply readable_nonidentity. apply writable_readable; trivial. Qed.

Lemma semax_orp {cs Espec Delta P1 P2 Q c}
  (HR1: @semax cs Espec Delta P1 c Q)
  (HR2: @semax cs Espec Delta P2 c Q):
  @semax cs Espec Delta (P1 || P2) c Q.
Proof.
 eapply semax_pre with (P':=EX x:bool, if x then P1 else P2).
+ old_go_lower. apply orp_left; [Exists true | Exists false]; entailer!.
+ Intros b. destruct b; trivial.
Qed.

Lemma semax_orp_SEPx (cs : compspecs) (Espec : OracleKind)
      (Delta : tycontext) (P : list Prop) (Q : list localdef)
      (R1 R2 : mpred) (R:list mpred) (T : ret_assert) (c : statement)
  (HR1 : semax Delta
         (PROPx P (LOCALx Q (SEPx (cons R1 R)))) c T)
  (HR2 : semax Delta
         (PROPx P (LOCALx Q (SEPx (cons R2 R)))) c T):
semax Delta
  (PROPx P (LOCALx Q (SEPx (cons (orp R1 R2) R)))) c T.
Proof.
 eapply semax_pre; [| apply (semax_orp HR1 HR2)].
 old_go_lower.
 rewrite distrib_orp_sepcon. normalize. 
Qed.

Lemma semax_orp_SEPnil cs Espec Delta P Q R1 R2 T c
  (HR1: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R1)) c T)
  (HR2: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R2)) c T):
  @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R1 || R2)) c T.
Proof. apply semax_orp_SEPx; trivial. Qed.
Lemma semax_orp_SEP cs Espec Delta P Q R1 R2 R T c
  (HR1: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R1; R)) c T)
  (HR2: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R2; R)) c T):
  @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP ((R1 || R2); R)) c T.
Proof. apply semax_orp_SEPx; trivial. Qed.

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
  forward_call (octx, osh, (sizeof (Tstruct _env_md_ctx_st noattr))).
  destruct case; simpl; Intros.
+ forward_call (gv, octx, nullval, copyEx_ictxNull). simpl; entailer!.
  Intros v. forward. Exists nullval; entailer!.
+ forward_call (gv, octx, ictx, copyEx_indigestNull ish md pv1 pv2). simpl; entailer!.
  Intros v. forward. Exists nullval; entailer!.
+ replace_SEP 0 (data_at osh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) octx).
  solve [(*holds because of FCout*) entailer!; apply convert; [ apply writable_readable | ]; trivial ].
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
  start_function.
  forward_call (gv, ctx, sh, mdd, c). Intros.
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
  { rewrite 2 data_at__memory_block. simpl; entailer!. }
  forward.
Qed.

Definition Gprog_copy_ex : funspecs :=
  [OPENSSL_memcpy_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_malloc_SPEC; EVP_MD_CTX_cleanup_SPEC].

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
  { unfold ERRGV; cancel. }
  forward. Exists nullval. unfold ERRGV; entailer!. 
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
  { unfold ERRGV; cancel. }
  forward. Exists nullval. unfold ERRGV; entailer!. 
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
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
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
          { unfold ERRGV; cancel. }
          forward. Exists nullval; thaw FR2; unfold ERRGV; entailer!.
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
  { (*holds because of FCout*) rewrite 2 data_at__memory_block; entailer!. }
  thaw FRAME1. do 7 forward. simpl. deadvars!.
  forward_call (buf, md, Int.unsigned ctxsz, memcpyNonnull Ews imdsh idata).
  { rewrite Int.repr_unsigned. simpl; entailer!. }
  { entailer!. }
  Intros.
  do 4 forward.
  Exists (Vint Int.one); entailer!.
  destruct (Val.eq d d'). 
  - destruct PP as [? ?]. subst d' buf m. cancel.
  - apply orp_right2; Exists buf; entailer!. 
    destruct pp as [[[? ?] ?] | ].
    * destruct PP as [? [? [? [? [? ?]]]]]; subst; trivial.
    * destruct PP as [? [? ?]]; subst; cancel.
Time Qed. (*24s*)

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
  forward_if (PROP ( ) LOCAL (temp _ctx v; gvars gv)  SEP (mm_inv gv; OPENSSL_malloc_token 16 v; data_at_ Ews (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) v)).
  - apply denote_tc_test_eq_split. 
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    eapply data_at__valid_pointer. apply writable_nonidentity. apply writable_Ews. (*top_share_nonidentity.*) simpl; omega.
    apply valid_pointer_null.
  - forward_call (v, Ews, sizeof (Tstruct _env_md_ctx_st noattr)). entailer!.
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
  forward_call (ctx, 16, Int.zero, memsetNonnull sh). entailer!.
  forward.
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
  start_function. Intros d pv1. unfold EVP_MD_CTX_NNnode; Intros. forward.
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
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
  forward. cancel.
+ Intros; subst mdd. forward_call (nullval, 0, gv). 
  { (*rewrite distrib_orp_sepcon; apply orp_right1;*) rewrite if_true by trivial; entailer!. }
  forward.
  forward_if (
     PROP ( )
     LOCAL (temp _ctx ctx)
     SEP (mm_inv gv; data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1, nullval))) ctx));
  [ contradiction | forward; entailer! | ].
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
  forward. cancel.
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
rewrite data_at__memory_block; Intros.
forward_call (ctx, sizeof (Tstruct _env_md_ctx_st noattr), gv).
{ (*rewrite distrib_orp_sepcon. apply orp_right2.*)
  rewrite if_false by (destruct ctx; try contradiction; discriminate). simpl; entailer!. }
forward.
Qed. 

Definition Gprog_destroy : funspecs :=
  [EVP_MD_CTX_free_SPEC].

Lemma body_EVP_MD_CTX_destroy: semax_body Vprog Gprog_destroy f_EVP_MD_CTX_destroy EVP_MD_CTX_destroy_SPEC.
Proof. 
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
  start_function. subst. rename H into CTXSZ.
  rename SH0 into OSH. rename SH1 into MDSH.
  rewrite EVP_MD_rep_isptr'; Intros. rename H into isptrD.
  unfold EVP_MD_rep. Intros csh vals. rename H into Rcsh.
  destruct CTX as [d [md [pv1 pv2]]]; simpl in d, md, pv1, pv2, isptrD; simpl.
  forward.
  destruct_vals vals Rcsh. Intros.
  forward. 
  forward_call (DC, ctx, sh, (d, (md, (pv1, pv2))), 
                out, osh, mdsh, md_size_of_MD (__EVP_MD DC)).
  { simpl; cancel. }
  simpl. replace_SEP 1 (!!(is_pointer_or_null md) &&
               postFin mdsh (ctx_size_of_MD (__EVP_MD DC)) md).
  { entailer. apply postFin_pTN. } 
  Intros. 
  forward_if (PROP ( )
   LOCAL (temp _ctx ctx; temp _md_out out; temp _size sz)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ctx;
        postFin mdsh (ctx_size_of_MD (__EVP_MD DC)) md;
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
   replace_SEP 1 (memory_block mdsh (ctx_size_of_MD (__EVP_MD DC)) md).
   { entailer!. apply postFin_memory_block. }
   forward_call (md, mdsh, ctx_size_of_MD (__EVP_MD DC)).
   forward. unfold EVP_MD_rep, postFin. entailer!.
   evar (z:reptype (Tstruct digests._env_md_st noattr)).
   Exists csh z; subst z. entailer!. simpl. entailer!.
Qed.


Definition Gprog_DigestFinal : funspecs :=
  [EVP_DigestFinal_ex_SPEC; EVP_MD_CTX_cleanup_SPEC].

Lemma body_DigestFinal: semax_body Vprog Gprog_DigestFinal f_EVP_DigestFinal EVP_DigestFinal_SPEC.
Proof. 
  start_function. rename H into CTXSZ. rename H0 into PV2.
  rename SH0 into Wosh.
  forward_call (ctx, sh, CTX, out, osh, sz, DC, Ews). 
  { intuition. }
  destruct CTX as [d [mdd [pv1 pv2]]]; simpl in d, mdd, pv1, pv2, PV2; subst; simpl.
  rewrite EVP_MD_rep_isptr'; Intros; simpl.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] ctx) as FC by entailer!.
  replace_SEP 1 (memory_block Ews (Int.unsigned (Int.repr (ctx_size_of_MD (__EVP_MD DC)))) mdd).
  { entailer!. apply postFin_memory_block. }
  unfold EVP_MD_rep. Intros csh vals. rename H into Rcsh.
  freeze [4;5] FR1.
  destruct_vals vals Rcsh. Intros.
  assert_PROP (is_pointer_or_null mdd) as PtrN_Mdd by entailer!. 
  forward_call (gv, ctx, sh, mdd, Some (Int.unsigned (Int.repr (ctx_size_of_MD (__EVP_MD DC))))).
  { Exists d pv1. unfold EVP_MD_CTX_NNnode. entailer!. cancel. }
  forward. thaw FR1; cancel. unfold EVP_MD_rep, EVP_MD_NNnode.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists csh z; subst z. rewrite 2 data_at__memory_block. entailer!. simpl. entailer!.
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
  start_function. rename H into SZ. destruct pv as [pv1 pv2]. 
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
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep; entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z; simpl. entailer!.
          simpl. entailer!. unfold DIE_postMpred.
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
          forward.
          forward_call (mdd, match o0 with None => 0 | Some (v,D) => ctx_size_of_MD D end, gv).
          { destruct o0 as [[v D] | ]; simpl. 
            * rewrite OPENSSL_malloc_token_compatible'; Intros. 
              sep_apply (data_at_memory_block Ews (tarray tuchar (ctx_size_of_MD D)) v mdd).
              simpl; rewrite Z.mul_1_l, Z.max_r by omega.
              rewrite if_false by (destruct mdd; try contradiction; discriminate).
              entailer!.
            * Intros; subst. rewrite if_true by reflexivity. cancel. }
          deadvars!. do 2 forward. thaw FR2. Exists m; entailer!.
          destruct o as [[dsh dvals] | ]; Intros; trivial. }
  Intros m. 
  freeze [1;3;4;6] FR3. forward.
  remember_vals tvals. (* subst type mds flags blsize ctxsize.*)
  freeze [0;4;5] FR4.
  forward.
  sep_apply (preInit_fresh_EWS (ctx_size_of_MD T) m).
  forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
  { rewrite Int.unsigned_repr by omega. simpl; cancel. }
  { rewrite Int.unsigned_repr by omega. subst tvals; repeat (split; trivial); omega. }
  deadvars!. subst tvals; simpl. forward.
  Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists tsh z; subst z. entailer!. 
  simpl. entailer!. thaw FR4; thaw FR3. cancel. apply orp_right2. simpl. Exists m; entailer!.
Time Qed. (*67s*)

Definition Gprog_DigestInit : funspecs :=
  [EVP_DigestInit_ex_SPEC; EVP_MD_CTX_init_SPEC].

Lemma body_DigestInit: semax_body Vprog Gprog_DigestInit f_EVP_DigestInit EVP_DigestInit_SPEC.
Proof. 
  start_function. destruct pv as [pv1 pv2]; unfold EVP_MD_CTX_NNnode; Intros.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] ctx) as FC by entailer!.
  forward_call (ctx, csh, sizeof (Tstruct _env_md_ctx_st noattr)).
  replace_SEP 0 (data_at csh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx).
  solve [entailer!; apply convert; [ apply writable_readable | ]; trivial ].
  rewrite EVP_MD_rep_isptr'; Intros.
  forward_call (ctx, t, nullval, nullval, nullval, (nullval, nullval), T, gv, csh, DIEC_NEQ None None).
  solve [simpl; entailer!].
  Intros rv. forward. Exists (Vint rv). entailer!.
Qed.
(*
Variant DigestInitExCase :=
  DIEC_EQ
| DIEC_NULL: option (list val * EVP_MD) -> DigestInitExCase
| DIEC_OTHER: share * reptype (Tstruct digests._env_md_st noattr) * option (list val * EVP_MD) -> DigestInitExCase.

Definition EVP_DigestInit_ex_SPEC := DECLARE _EVP_DigestInit_ex
  WITH ctx:val, t:val, e:val, d:val, mdd:val, pv: val * val, T: EVP_MD,
       gv:globals, csh:share, c: DigestInitExCase
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (4 <= ctx_size_of_MD T <= Int.max_unsigned; writable_share csh)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERRGV gv; EVP_MD_CTX_NNnode csh (d,(mdd,pv)) ctx; 
           EVP_MD_rep T t;
           match c with 
           | DIEC_EQ => !!(d=t) && preInit Ews (ctx_size_of_MD T) mdd
           | DIEC_NULL p => !!(d=nullval) && DIE_preMpred mdd p
           | DIEC_OTHER (dsh, dvals, p) => !!(d <> t) && EVP_MD_NNnode dsh dvals d * DIE_preMpred mdd p
           end)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; EVP_MD_rep T t;
            match c with
            | DIEC_EQ => !!(rv = Vint Int.one) && EVP_MD_CTX_NNnode csh (d,(mdd,pv)) ctx *
                         MD_state Ews (INI T) mdd
            | DIEC_NULL p => DIE_postMpred rv d t pv mdd ctx csh T p
            | DIEC_OTHER (dsh, dvals, p) => EVP_MD_NNnode dsh dvals d * DIE_postMpred rv d t pv mdd ctx csh T p
            end).

Lemma body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC.
Proof. 
  start_function. destruct pv as [pv1 pv2]. unfold EVP_MD_CTX_NNnode; Intros.
  rename H into SZ. forward.
  rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  destruct c; Intros; subst.
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
  forward_call (ctx, csh, (t, (mdd, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
  deadvars!. simpl. thaw FR1. subst. forward.
  Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists tsh z; subst z. entailer!. simpl. entailer!.
+ (*Case DIEC_NULL*)
  forward_if (
     PROP ()
     LOCAL(gvars gv; temp _ctx ctx)
     SEP (EX m:_, (!!(malloc_compatible (ctx_size_of_MD T) m) 
                   && memory_block Ews (ctx_size_of_MD T) m *
                      data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx); 
          ERRGV gv;
          match_EVP_MD T tvals;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
  2: solve [ apply ptr_comp_Cne_f in H; subst; trivial; [ contradiction | apply isptr_is_pointer_or_null; trivial]].
  { clear H; deadvars!. remember_vals tvals.
      freeze [0;1;2; 3;4;6] FR1.
      forward.
      forward_call (ctx_size_of_MD T).
      Intros m. forward.
      apply semax_orp_SEPx; Intros.
      + subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - clear H H'; thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep, DIE_preMpred. entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z. entailer!.
          simpl. entailer!.
          apply orp_right1. entailer!. destruct o; entailer.
        - discriminate.
      + rename H4 into M. rewrite memory_block_isptr; Intros. deadvars!.
        forward_if (PROP ( )
            LOCAL (temp _md_data m; gvars gv; temp _type t; temp _ctx ctx)
            SEP (memory_block Ews (ctx_size_of_MD T) m; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr)
                   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - thaw FR1. forward.
          destruct o as [[v D] | ]; Intros.
          * replace_SEP 6 (memory_block Ews (sizeof (tarray tuchar (ctx_size_of_MD D))) mdd).
            { entailer!. eapply derives_trans. apply data_at_memory_block. simpl. rewrite Z.mul_1_l. cancel. }
            forward_call (mdd, sizeof (tarray tuchar (ctx_size_of_MD D))). 
            { rewrite distrib_orp_sepcon. apply orp_right2. cancel. }
            forward. forward. entailer!; Exists m; entailer!.
          * forward_call (nullval, 0).
            { rewrite distrib_orp_sepcon. apply orp_right1. entailer!. }
            forward. forward. entailer!; Exists m; entailer!. }
  Intros m. rename H into M. forward. 
  remember_vals tvals. subst type mds flags blsize ctxsize.
  forward.
  replace_SEP 0 (preInit Ews (ctx_size_of_MD T) m). 
  { entailer!. apply preInit_fresh_EWS. }
  forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
  { rewrite Int.unsigned_repr by omega. simpl. cancel. }
  { rewrite Int.unsigned_repr by omega. subst; intuition. }
  deadvars!. simpl. subst. forward.
  Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
  simpl. entailer!. apply orp_right2.
  Exists m. entailer!.
+ (*Case OTHER*)
  destruct p as [[dsh dvals] p]; Intros. rename H into DT. unfold EVP_MD_NNnode; Intros. rename H into DSH.
  forward_if (PROP ( )
     LOCAL (gvars gv; temp _ctx ctx)
     SEP (ERRGV gv; match_EVP_MD T tvals; data_at tsh (Tstruct digests._env_md_st noattr) tvals t;
          data_at dsh (Tstruct _env_md_st noattr) dvals d *
          EX m:_, !!(malloc_compatible (ctx_size_of_MD T) m) 
                  && memory_block Ews (ctx_size_of_MD T) m *
                     data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx)).
  2 : solve [ apply ptr_comp_Cne_f in H; subst; trivial; [ contradiction | apply isptr_is_pointer_or_null; trivial]].
  { clear H; deadvars!. remember_vals tvals.
      freeze [0;1;2;3;4;6;7] FR1.
      forward.
      forward_call (ctx_size_of_MD T).
      Intros m. forward.
      apply semax_orp_SEPx; Intros.
      + subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep. entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z. unfold EVP_MD_NNnode, DIE_preMpred; entailer!.
          simpl. entailer!.
          apply orp_right1. destruct p as [[v D] |]; Intros; entailer!.
        - discriminate.
      + rewrite memory_block_isptr; Intros.  deadvars!.
        forward_if (PROP ( )
            LOCAL (temp _md_data m; gvars gv; temp _ctx ctx; temp _type t)
            SEP (memory_block Ews (ctx_size_of_MD T) m; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr)
                   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - thaw FR1. forward.
          destruct p as [[v D] | ]; Intros.
          * replace_SEP 7 (memory_block Ews (sizeof (tarray tuchar (ctx_size_of_MD D))) mdd).
            { entailer!. eapply derives_trans. apply data_at_memory_block. simpl. rewrite Z.mul_1_l. cancel. }
            forward_call (mdd, sizeof (tarray tuchar (ctx_size_of_MD D))). 
            { rewrite distrib_orp_sepcon. apply orp_right2. cancel. }
            forward. forward. entailer!. Exists m; entailer!.
          * forward_call (nullval, 0).
            { rewrite distrib_orp_sepcon. apply orp_right1. entailer!. }
            forward. forward. entailer!; Exists m; entailer!. }
  Intros m. rename H into M. forward. 
  remember_vals tvals.
  forward.
  replace_SEP 6 (preInit Ews (ctx_size_of_MD T) m). 
  { entailer!. apply preInit_fresh_EWS. }
  forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
  { rewrite Int.unsigned_repr by omega. simpl. cancel. }
  { rewrite Int.unsigned_repr by omega. subst; intuition. }
  deadvars!. simpl. subst. forward.
  Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
  simpl. entailer!. apply orp_right2.
  Exists m. entailer!.
Time Qed. (*cases eq and dnull: 34s; all three cases: 66s; second run:90s*)

Definition EVP_DigestInit_ex_SPEC_dnull:= DECLARE _EVP_DigestInit_ex
  WITH ctx:val, t:val, e:val, mdd:val, pv: val * val, T: EVP_MD,
       gv:globals, csh:share,
       c: option (list val * EVP_MD)
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (4 <= ctx_size_of_MD T <= Int.max_unsigned; writable_share csh)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERRGV gv; EVP_MD_CTX_NNnode csh (nullval,(mdd,pv)) ctx; 
           EVP_MD_rep T t;
           match c with None => !!(mdd = nullval) && emp
             | Some (v, DD) => (*!!(get_ctxsize dvals = Vint (Int.repr (ctx_size_of_MD DD))
                                       (* /\ Int.ltu Int.zero sz = true*))
                                  &&*) data_at Ews (tarray tuchar (ctx_size_of_MD DD)) v mdd
           end)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; (*digestInitEx_post c ctx t rv*)
            EVP_MD_rep T t;
            (!!(rv= nullval) && 
               data_at csh (Tstruct _env_md_ctx_st noattr) (nullval,(mdd,pv)) ctx * 
               match c with None => emp
               | Some (v, DD) => (*!!(get_ctxsize dvals = Vint (Int.repr (ctx_size_of_MD DD))
                                       (* /\ Int.ltu Int.zero sz = true*))
                                  &&*) data_at Ews (tarray tuchar (ctx_size_of_MD DD)) v mdd
               end)
            || (EX m :_, (!!(rv= Vint Int.one /\ malloc_compatible (ctx_size_of_MD T) m)
                && data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, pv)) ctx * 
                MD_state Ews (INI T) m))).

Lemma body_DigestInit_ex_dnull: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC_dnull.
Proof. 
  start_function. destruct pv as [pv1 pv2]. unfold EVP_MD_CTX_NNnode; Intros.
  rename H into SZ. forward.
  rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  forward_if (
     PROP ()
     LOCAL(gvars gv; temp _ctx ctx)
     SEP (EX m:_, (!!(malloc_compatible (ctx_size_of_MD T) m) 
                   && memory_block Ews (ctx_size_of_MD T) m *
                      data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx); 
          ERRGV gv;
          match_EVP_MD T tvals;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { (*apply ptr_comp_Cne_t in H.*) clear H. deadvars!. remember_vals tvals.
      freeze [0;1;2; 3;4;6] FR1.
      forward.
      forward_call (ctx_size_of_MD T).
      Intros m. forward.
      apply semax_orp_SEPx; Intros.
      + subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep. entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z. entailer!.
          simpl. entailer!.
          apply orp_right1. entailer!. destruct c; entailer.
        - discriminate.
      + rewrite memory_block_isptr; Intros. deadvars!.
        forward_if (PROP ( )
            LOCAL (temp _md_data m; gvars gv; temp _type t; temp _ctx ctx)
            SEP (memory_block Ews (ctx_size_of_MD T) m; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr)
                   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - thaw FR1. forward.
          destruct c.
          { (* Some (v, D)*) destruct p as [v D]; Intros.
            replace_SEP 6 (memory_block Ews (sizeof (tarray tuchar (ctx_size_of_MD D))) mdd).
            { entailer!. eapply derives_trans. apply data_at_memory_block. simpl. rewrite Z.mul_1_l. cancel. }
            forward_call (mdd, sizeof (tarray tuchar (ctx_size_of_MD D))). 
            { rewrite distrib_orp_sepcon. apply orp_right2. cancel. }
            forward. forward. entailer!. Exists m; entailer!. }
          { (*None*) 
             forward_call (mdd, 0).
             { rewrite distrib_orp_sepcon. apply orp_right1. cancel. }
             forward. forward. entailer!. Exists m; entailer!. } }
    { apply ptr_comp_Cne_f in H; trivial. subst. contradiction. apply isptr_is_pointer_or_null; trivial. }
    Intros m. rename H into M. forward. 
    remember_vals tvals.
    forward.
    replace_SEP 0 (preInit Ews (ctx_size_of_MD T) m). 
    { entailer!. apply preInit_fresh_EWS. }
    forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
    deadvars!. simpl. subst. forward.
    Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
    evar (z:reptype (Tstruct digests._env_md_st noattr)).
    Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
    simpl. entailer!. apply orp_right2.
    Exists m. entailer!.
Qed.
*)
(*
Definition EVP_DigestInit_ex_SPEC := DECLARE _EVP_DigestInit_ex
  WITH ctx:val, t:val, e:val, d:val, mdd:val, pv: val * val, T: EVP_MD, gv:globals, csh:share,
       c: option (share * reptype (Tstruct digests._env_md_st noattr) * option (list val * EVP_MD))
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (4 <= ctx_size_of_MD T <= Int.max_unsigned; writable_share csh)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERRGV gv; EVP_MD_CTX_NNnode csh (d,(mdd,pv)) ctx;
           EVP_MD_rep T t; 
           match c with 
             None => (!!(d=t) && preInit Ews (ctx_size_of_MD T) mdd)
           | Some (dsh, dvals, x) => !!(d <> t) && EVP_MD_node (*dsh*) dvals d *
              match x with
                None => !!(mdd = nullval) && emp
              | Some (v, D) => !!(get_ctxsize dvals = Vint (Int.repr (ctx_size_of_MD D)))
                                 && data_at Ews (tarray tuchar (ctx_size_of_MD D)) v mdd
              end
           end)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; EVP_MD_rep T t;
            match c with
              None => !!(rv = Vint Int.one) && (EVP_MD_CTX_NNnode csh (t,(mdd,pv)) ctx * MD_state Ews (INI T) mdd)
            | Some (dsh, dvals, x) => EVP_MD_NNnode dsh dvals d *
               ( (!!(rv= nullval) 
                    && data_at csh (Tstruct _env_md_ctx_st noattr) (d,(mdd,pv)) ctx * 
                       match x with
                         None => emp
                       | Some (v, D) => !!(get_ctxsize dvals = Vint (Int.repr (ctx_size_of_MD D)))
                                           && data_at Ews (tarray tuchar (ctx_size_of_MD D)) v mdd
                       end)
               || (EX m :_, !!(rv= Vint Int.one /\ malloc_compatible (ctx_size_of_MD T) m)
                            && data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, pv)) ctx * 
                            MD_state Ews (INI T) m))
            end).
(*
Lemma body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC.
Proof. 
  start_function. destruct pv as [pv1 pv2]. unfold EVP_MD_CTX_NNnode; Intros.
  rename H into SZ. forward.
  rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.



  forward_if (PROP ( )
     LOCAL (gvars gv; temp _ctx ctx; temp _type t; temp _engine e)
     SEP (ERRGV gv; match_EVP_MD T tvals; data_at tsh (Tstruct digests._env_md_st noattr) tvals t;
          match c with
            None => data_at csh (Tstruct _env_md_ctx_st noattr) (t, (mdd, (pv1, pv2))) ctx *
                    preInit Ews (ctx_size_of_MD T) mdd
          | Some (dsh, dvals, x) => data_at dsh (Tstruct _env_md_st noattr) dvals d *
                 EX m:_, !!(malloc_compatible (ctx_size_of_MD T) m) 
                       && memory_block Ews (ctx_size_of_MD T) m *
                          data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx
           end
          )).

+ destruct c as [ [[dsh dvals] x] | ]; Intros; [ unfold EVP_MD_NNnode; Intros | subst]; entailer!.
+ apply ptr_comp_Cne_t in H; trivial. deadvars!. remember_vals tvals.
      freeze [0;1;2; 3;4;6;7] FR1.
      forward.
      forward_call (ctx_size_of_MD T).
      Intros m. forward. deadvars!.
      apply semax_orp_SEPx; Intros.
      * subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep. entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
          simpl. entailer!.
          destruct c as [ [[dsh dvals] x] | ]; Intros.
          { destruct x as [[v D] | ]; Intros. 
            + entailer; cancel; apply orp_right1; entailer!.
            + entailer!; apply orp_right1; cancel. }
          subst; congruence. 
        -  discriminate.
      * rewrite memory_block_isptr; Intros.
        forward_if (PROP ( )
            LOCAL (temp _md_data m; gvars gv; temp _type t; temp _ctx ctx)
            SEP (memory_block Ews (ctx_size_of_MD T) m; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr)
                   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - thaw FR1. forward.
          destruct c as [ [[dsh dvals] x] | ]; Intros; [ destruct x as [[v D] | ]; Intros |  congruence].
          replace_SEP 7 (memory_block Ews (sizeof (tarray tuchar (ctx_size_of_MD D))) mdd).
            { entailer!. eapply derives_trans. apply data_at_memory_block. simpl. rewrite Z.mul_1_l. cancel. }
            forward_call (mdd, sizeof (tarray tuchar (ctx_size_of_MD D))). 
            { rewrite distrib_orp_sepcon. apply orp_right2. cancel. }
            forward. forward. go_lower. . entailer!. Exists m; entailer!. } (*
          { (*None*) 
             forward_call (mdd, 0).
             { rewrite distrib_orp_sepcon. apply orp_right1. cancel. }
             forward. forward. entailer!. Exists m; entailer!. } }*)
    { apply ptr_comp_Cne_f in H; trivial. congruence. apply isptr_is_pointer_or_null; trivial. }
    Intros m. rename H into M. forward. 
    remember_vals tvals.
    forward.
    replace_SEP 0 (preInit Ews (ctx_size_of_MD T) m). 
    { entailer!. apply preInit_fresh_EWS. }
    forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
    deadvars!. simpl. subst. forward.
    Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
    evar (z:reptype (Tstruct digests._env_md_st noattr)).
    Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
    simpl. entailer!. apply orp_right2.
    Exists m. entailer!.
- forward_if (
     PROP ()
     LOCAL(gvars gv; temp _ctx ctx)
     SEP (EX m:_, (!!(malloc_compatible (ctx_size_of_MD T) m) 
                   && memory_block Ews (ctx_size_of_MD T) m *
                      data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx); 
          ERRGV gv;
          data_at dsh (Tstruct _env_md_st noattr) dvals d;
          match_EVP_MD T tvals;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { clear H. deadvars!. remember_vals tvals.
      freeze [0;1;2; 3;4;6;7] FR1.
      forward.
      forward_call (ctx_size_of_MD T).
      Intros m. forward. deadvars!.
      apply semax_orp_SEPx; Intros.
      + subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep. entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
          simpl. entailer!.
          apply orp_right1. Intros; entailer!.
        - discriminate.
      + rewrite memory_block_isptr; Intros.
        forward_if (PROP ( )
            LOCAL (temp _md_data m; gvars gv; temp _type t; temp _ctx ctx)
            SEP (memory_block Ews (ctx_size_of_MD T) m; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr)
                   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - thaw FR1. forward.
             forward_call (mdd, 0).
             { rewrite distrib_orp_sepcon. apply orp_right1. entailer!. }
             forward. forward. entailer!. Exists m; entailer!. }
    { apply ptr_comp_Cne_f in H; trivial. congruence. apply isptr_is_pointer_or_null; trivial. }
    Intros m. rename H into M. forward. 
    remember_vals tvals.
    forward.
    replace_SEP 0 (preInit Ews (ctx_size_of_MD T) m). 
    { entailer!. apply preInit_fresh_EWS. }
    forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
    deadvars!. simpl. subst. forward.
    Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
    evar (z:reptype (Tstruct digests._env_md_st noattr)).
    Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
    simpl. entailer!. apply orp_right2.
    Exists m. entailer!.
+ rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  forward_if (PROP ( )
     LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
     SEP (data_at csh (Tstruct _env_md_ctx_st noattr) (t, (mdd, (pv1, pv2))) ctx;
          ERRGV gv; match_EVP_MD T tvals; preInit Ews (ctx_size_of_MD T) mdd;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { apply ptr_comp_Cne_t in H; congruence. }
    { forward. entailer!. }
  forward.
  remember_vals tvals.
  freeze [1;3;4] FR1.
  forward.
  forward_call (ctx, csh, (t, (mdd, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
  deadvars!. simpl. thaw FR1. subst. forward.
  Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists tsh z; subst z. entailer!. simpl. entailer!.
Time Qed.*)

Lemma body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC.
Proof. 
  start_function. destruct pv as [pv1 pv2]. unfold EVP_MD_CTX_NNnode; Intros.
  rename H into SZ. forward.
  destruct c; Intros; subst.
+ destruct p as [[dsh dvals] x]; Intros. rename H into DT.
  rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  rewrite EVP_MD_NNnode_isptr'; Intros. unfold EVP_MD_NNnode; Intros. rename H into DSH.
  forward_if (
     PROP ()
     LOCAL(gvars gv; temp _ctx ctx)
     SEP (EX m:_, (!!(malloc_compatible (ctx_size_of_MD T) m) 
                   && memory_block Ews (ctx_size_of_MD T) m *
                      data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx); 
          ERRGV gv;
          data_at dsh (Tstruct _env_md_st noattr) dvals d;
          match_EVP_MD T tvals;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { clear H. deadvars!. remember_vals tvals.
      freeze [0;1;2; 3;4;6;7] FR1.
      forward.
      forward_call (ctx_size_of_MD T).
      Intros m. forward. deadvars!.
      apply semax_orp_SEPx; Intros.
      + subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep. entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
          simpl. entailer!.
          apply orp_right1. destruct x; Intros; entailer!.
        - discriminate.
      + rewrite memory_block_isptr; Intros.
        forward_if (PROP ( )
            LOCAL (temp _md_data m; gvars gv; temp _type t; temp _ctx ctx)
            SEP (memory_block Ews (ctx_size_of_MD T) m; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr)
                   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - thaw FR1. forward.
          destruct x.
          { (* Some (v, D)*) destruct p as [v D]; Intros.
            replace_SEP 7 (memory_block Ews (sizeof (tarray tuchar (ctx_size_of_MD D))) mdd).
            { entailer!. eapply derives_trans. apply data_at_memory_block. simpl. rewrite Z.mul_1_l. cancel. }
            forward_call (mdd, sizeof (tarray tuchar (ctx_size_of_MD D))). 
            { rewrite distrib_orp_sepcon. apply orp_right2. cancel. }
            forward. forward. entailer!. Exists m; entailer!. }
          { (*None*) 
             forward_call (mdd, 0).
             { rewrite distrib_orp_sepcon. apply orp_right1. cancel. }
             forward. forward. entailer!. Exists m; entailer!. } }
    { apply ptr_comp_Cne_f in H; trivial. congruence. apply isptr_is_pointer_or_null; trivial. }
    Intros m. rename H into M. forward. 
    remember_vals tvals.
    forward.
    replace_SEP 0 (preInit Ews (ctx_size_of_MD T) m). 
    { entailer!. apply preInit_fresh_EWS. }
    forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
    deadvars!. simpl. subst. forward.
    Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
    evar (z:reptype (Tstruct digests._env_md_st noattr)).
    Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
    simpl. entailer!. apply orp_right2.
    Exists m. entailer!.
+ rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  forward_if (PROP ( )
     LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
     SEP (data_at csh (Tstruct _env_md_ctx_st noattr) (t, (mdd, (pv1, pv2))) ctx;
          ERRGV gv; match_EVP_MD T tvals; preInit Ews (ctx_size_of_MD T) mdd;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { apply ptr_comp_Cne_t in H; congruence. }
    { forward. entailer!. }
  forward.
  remember_vals tvals.
  freeze [1;3;4] FR1.
  forward.
  forward_call (ctx, csh, (t, (mdd, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
  deadvars!. simpl. thaw FR1. subst. forward.
  Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists tsh z; subst z. entailer!. simpl. entailer!.
Time Qed.

(*Individual proof of neq case
Definition EVP_DigestInit_ex_SPEC_d_neq_t:= DECLARE _EVP_DigestInit_ex
  WITH ctx:val, t:val, e:val, mdd:val, pv: val * val, T: EVP_MD,
       gv:globals, csh:share, d:val, dsh:share, dvals: reptype (Tstruct digests._env_md_st noattr),
       c: option (list val * EVP_MD)
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (4 <= ctx_size_of_MD T <= Int.max_unsigned; writable_share csh; d <> t)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERRGV gv; EVP_MD_CTX_NNnode csh (d,(mdd,pv)) ctx; 
           EVP_MD_NNnode dsh dvals d; EVP_MD_rep T t;
           match c with None => !!(mdd = nullval) && emp
             | Some (v, DD) => !!(get_ctxsize dvals = Vint (Int.repr (ctx_size_of_MD DD))
                                       (* /\ Int.ltu Int.zero sz = true*))
                                  && data_at Ews (tarray tuchar (ctx_size_of_MD DD)) v mdd
           end)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; (*digestInitEx_post c ctx t rv*)
            EVP_MD_rep T t; EVP_MD_NNnode dsh dvals d;
            (!!(rv= nullval) && 
               data_at csh (Tstruct _env_md_ctx_st noattr) (d,(mdd,pv)) ctx * 
               match c with None => emp
               | Some (v, DD) => !!(get_ctxsize dvals = Vint (Int.repr (ctx_size_of_MD DD))
                                       (* /\ Int.ltu Int.zero sz = true*))
                                  && data_at Ews (tarray tuchar (ctx_size_of_MD DD)) v mdd
               end)
            || (EX m :_, (!!(rv= Vint Int.one /\ malloc_compatible (ctx_size_of_MD T) m)
                && data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, pv)) ctx * 
                MD_state Ews (INI T) m))).

Lemma body_DigestInit_ex_neq: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC_d_neq_t.
Proof. 
  start_function. destruct pv as [pv1 pv2]. unfold EVP_MD_CTX_NNnode; Intros.
  rename H into SZ. rename H0 into DT. forward.
  rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  rewrite EVP_MD_NNnode_isptr'; Intros. unfold EVP_MD_NNnode; Intros. rename H into DSH.
  forward_if (
     PROP ()
     LOCAL(gvars gv; temp _ctx ctx)
     SEP (EX m:_, (!!(malloc_compatible (ctx_size_of_MD T) m) 
                   && memory_block Ews (ctx_size_of_MD T) m *
                      data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx); 
          ERRGV gv;
          data_at dsh (Tstruct _env_md_st noattr) dvals d;
          match_EVP_MD T tvals;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { clear H. deadvars!. remember_vals tvals.
      freeze [0;1;2; 3;4;5;7] FR1.
      forward.
      forward_call (ctx_size_of_MD T).
      Intros m. forward.
      apply semax_orp_SEPx; Intros.
      + subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep. entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
          simpl. entailer!.
          apply orp_right1. destruct c; Intros; entailer!.
        - discriminate.
      + rewrite memory_block_isptr; Intros. deadvars!.
        forward_if (PROP ( )
            LOCAL (temp _md_data m; gvars gv; temp _type t; temp _ctx ctx)
            SEP (memory_block Ews (ctx_size_of_MD T) m; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr)
                   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - thaw FR1. forward.
          destruct c.
          { (* Some (v, D)*) destruct p as [v D]; Intros.
            replace_SEP 7 (memory_block Ews (sizeof (tarray tuchar (ctx_size_of_MD D))) mdd).
            { entailer!. eapply derives_trans. apply data_at_memory_block. simpl. rewrite Z.mul_1_l. cancel. }
            forward_call (mdd, sizeof (tarray tuchar (ctx_size_of_MD D))). 
            { rewrite distrib_orp_sepcon. apply orp_right2. cancel. }
            forward. forward. entailer!. Exists m; entailer!. }
          { (*None*) 
             forward_call (mdd, 0).
             { rewrite distrib_orp_sepcon. apply orp_right1. cancel. }
             forward. forward. entailer!. Exists m; entailer!. } }
    { apply ptr_comp_Cne_f in H; trivial. congruence. apply isptr_is_pointer_or_null; trivial. }
    Intros m. rename H into M. forward. 
    remember_vals tvals.
    forward.
    replace_SEP 0 (preInit Ews (ctx_size_of_MD T) m). 
    { entailer!. apply preInit_fresh_EWS. }
    forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD T), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
    deadvars!. simpl. subst. forward.
    Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
    evar (z:reptype (Tstruct digests._env_md_st noattr)).
    Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
    simpl. entailer!. apply orp_right2.
    Exists m. entailer!.
Qed.*)

(* Variant of neq with preInit
Definition EVP_DigestInit_ex_SPEC_d_neq_t:= DECLARE _EVP_DigestInit_ex
  WITH ctx:val, t:val, e:val, d:val, mdd:val, pv: val * val, D: EVP_MD,
       gv:globals, csh:share, dsh:share, dvals: reptype (Tstruct digests._env_md_st noattr),
       c: option (share * MD_with_content)
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (4 <= ctx_size_of_MD D <= Int.max_unsigned; writable_share csh; d <> t)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERRGV gv; EVP_MD_CTX_NNnode csh (d,(mdd,pv)) ctx; 
           EVP_MD_NNnode dsh dvals d; EVP_MD_rep D t;
           match c with None => !!(mdd = nullval) && emp
             | Some (mdsh, ST) => !!(get_ctxsize dvals = Vint (Int.repr (EVP_MD_rec_ctx_size _ (EVPMD_record_of_EVPMD (__EVP_MD ST))))
                                       (* /\ Int.ltu Int.zero sz = true*))
                                  && preInit Ews (ctx_size_of_MD (__EVP_MD ST)) mdd(*MD_state mdsh ST mdd*)
           end)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; (*digestInitEx_post c ctx t rv*)
            EVP_MD_rep D t; EVP_MD_NNnode dsh dvals d;
            (!!(rv= nullval) && 
               data_at csh (Tstruct _env_md_ctx_st noattr) (d,(mdd,pv)) ctx * 
               match c with None => !!(mdd = nullval) && emp
               | Some (mdsh, ST) => !!(get_ctxsize dvals = Vint (Int.repr (EVP_MD_rec_ctx_size _ (EVPMD_record_of_EVPMD (__EVP_MD ST))))
                                       (* /\ Int.ltu Int.zero sz = true*))
                                  && preInit Ews (ctx_size_of_MD (__EVP_MD ST)) mdd(*MD_state mdsh ST mdd*)
               end)
            || (EX m :_, (!!(rv= Vint Int.one /\ malloc_compatible (ctx_size_of_MD D) m)
                && data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, pv)) ctx * 
                MD_state Ews (INI D) m))).

Lemma body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC_d_neq_t.
Proof. 
  start_function. destruct pv as [pv1 pv2]. unfold EVP_MD_CTX_NNnode; Intros.
  rename H into SZ. rename H0 into DT. forward.
  rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  rewrite EVP_MD_NNnode_isptr'; Intros. unfold EVP_MD_NNnode; Intros. rename H into DSH.
  forward_if (
     PROP ()
     LOCAL(gvars gv; temp _ctx ctx)
     SEP (EX m:_, (!!(malloc_compatible (ctx_size_of_MD D) m) 
                   && memory_block Ews (ctx_size_of_MD D) m *
                      data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx); 
          ERRGV gv;
          data_at dsh (Tstruct _env_md_st noattr) dvals d;
          match_EVP_MD D tvals;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { clear H. deadvars!. remember_vals tvals.
      freeze [0;1;2; 3;4;5;7] FR1.
      forward.
      forward_call (ctx_size_of_MD D).
      Intros m. forward.
      apply semax_orp_SEPx; Intros.
      + subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep. entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
          simpl. entailer!.
          apply orp_right1. entailer!.
        - discriminate.
      + rewrite memory_block_isptr; Intros. deadvars!.
        forward_if (PROP ( )
            LOCAL (temp _md_data m; gvars gv; temp _type t; temp _ctx ctx)
            SEP (memory_block Ews (ctx_size_of_MD D) m; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr)
                   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - thaw FR1. forward.
          destruct c.
          { (* Some (mdsh, ST)*) destruct p as [mdsh ST]; Intros.
            replace_SEP 7 (memory_block Ews (EVP_MD_rec_ctx_size _ (EVPMD_record_of_EVPMD (__EVP_MD ST))) mdd).
              entailer. admit. (*TODO*)
            forward_call (mdd, EVP_MD_rec_ctx_size (__EVP_MD ST)
                   (EVPMD_record_of_EVPMD (__EVP_MD ST))).
            { rewrite distrib_orp_sepcon. apply orp_right2. cancel. }
            forward. forward. entailer!. Exists m; entailer!. }
          { (*None*) 
             forward_call (mdd, 0).
             { rewrite distrib_orp_sepcon. apply orp_right1. cancel. }
             forward. forward. entailer!. Exists m; entailer!. } }
    { apply ptr_comp_Cne_f in H; trivial. congruence. apply isptr_is_pointer_or_null; trivial. }
    Intros m. rename H into M. forward. 
    remember_vals tvals.
    forward.
    replace_SEP 0 (preInit Ews (ctx_size_of_MD D) m). 
    { entailer!. apply preInit_fresh_EWS. }
    forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD D), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
    deadvars!. simpl. subst. forward.
    Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
    evar (z:reptype (Tstruct digests._env_md_st noattr)).
    Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
    simpl. entailer!. apply orp_right2.
    Exists m. entailer!.
Admitted.
*)

(*Variant of neq  with MD_state
Definition EVP_DigestInit_ex_SPEC_d_neq_t:= DECLARE _EVP_DigestInit_ex
  WITH ctx:val, t:val, e:val, d:val, mdd:val, pv: val * val, D: EVP_MD,
       gv:globals, csh:share, dsh:share, dvals: reptype (Tstruct digests._env_md_st noattr),
       c: option (share * MD_with_content)
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (4 <= ctx_size_of_MD D <= Int.max_unsigned; writable_share csh; d <> t)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERRGV gv; EVP_MD_CTX_NNnode csh (d,(mdd,pv)) ctx; 
           EVP_MD_NNnode dsh dvals d; EVP_MD_rep D t(*; preInit Ews (ctx_size_of_MD D) mdd*);
           match c with None => !!(mdd = nullval) && emp
             | Some (mdsh, ST) => !!(get_ctxsize dvals = Vint (Int.repr (EVP_MD_rec_ctx_size _ (EVPMD_record_of_EVPMD (__EVP_MD ST))))
                                       (* /\ Int.ltu Int.zero sz = true*))
                                  && MD_state mdsh ST mdd
           end)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; (*digestInitEx_post c ctx t rv*)
            EVP_MD_rep D t; EVP_MD_NNnode dsh dvals d;
            (!!(rv= nullval) && 
               data_at csh (Tstruct _env_md_ctx_st noattr) (d,(mdd,pv)) ctx * 
               match c with None => !!(mdd = nullval) && emp
               | Some (mdsh, ST) => !!(get_ctxsize dvals = Vint (Int.repr (EVP_MD_rec_ctx_size _ (EVPMD_record_of_EVPMD (__EVP_MD ST))))
                                       (* /\ Int.ltu Int.zero sz = true*))
                                  && MD_state mdsh ST mdd
               end)
            || (EX m :_, (!!(rv= Vint Int.one /\ malloc_compatible (ctx_size_of_MD D) m)
                && data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, pv)) ctx * 
                MD_state Ews (INI D) m))).

Lemma body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC_d_neq_t.
Proof. 
  start_function. destruct pv as [pv1 pv2]. unfold EVP_MD_CTX_NNnode; Intros.
  rename H into SZ. rename H0 into DT. forward.
  rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  rewrite EVP_MD_NNnode_isptr'; Intros. unfold EVP_MD_NNnode; Intros. rename H into DSH.
  forward_if (
     PROP ()
     LOCAL(gvars gv; temp _ctx ctx)
     SEP (EX m:_, (!!(malloc_compatible (ctx_size_of_MD D) m) 
                   && memory_block Ews (ctx_size_of_MD D) m *
                      data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, (pv1, pv2))) ctx); 
          ERRGV gv;
          data_at dsh (Tstruct _env_md_st noattr) dvals d;
          match_EVP_MD D tvals;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { clear H. deadvars!. remember_vals tvals.
      freeze [0;1;2; 3;4;5;7] FR1.
      forward.
      forward_call (ctx_size_of_MD D).
      Intros m. forward.
      apply semax_orp_SEPx; Intros.
      + subst.
        forward_if (PROP (False) LOCAL () SEP()).
        - thaw FR1.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 gv ___stringlit_1, Vint (Int.repr 180)).
          { unfold ERRGV; cancel. }
          forward. Exists nullval; unfold ERRGV, EVP_MD_rep. entailer!.
          evar (z:reptype (Tstruct digests._env_md_st noattr)).
          Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
          simpl. entailer!.
          apply orp_right1. entailer!.
        - discriminate.
      + rewrite memory_block_isptr; Intros. deadvars!.
        forward_if (PROP ( )
            LOCAL (temp _md_data m; gvars gv; temp _type t; temp _ctx ctx)
            SEP (memory_block Ews (ctx_size_of_MD D) m; FRZL FR1;
                 data_at tsh (Tstruct digests._env_md_st noattr)
                   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) t)).
        - subst; contradiction.
        - forward. entailer!.
        - thaw FR1. forward.
          destruct c.
          { (* Some (mdsh, ST)*) destruct p as [mdsh ST]; Intros.
            replace_SEP 7 (memory_block Ews (EVP_MD_rec_ctx_size _ (EVPMD_record_of_EVPMD (__EVP_MD ST))) mdd).
              entailer. admit. (*TODO*)
            forward_call (mdd, EVP_MD_rec_ctx_size (__EVP_MD ST)
                   (EVPMD_record_of_EVPMD (__EVP_MD ST))).
            { rewrite distrib_orp_sepcon. apply orp_right2. cancel. }
            forward. forward. entailer!. Exists m; entailer!. }
          { (*None*) 
             forward_call (mdd, 0).
             { rewrite distrib_orp_sepcon. apply orp_right1. cancel. }
             forward. forward. entailer!. Exists m; entailer!. } }
    { apply ptr_comp_Cne_f in H; trivial. congruence. apply isptr_is_pointer_or_null; trivial. }
    Intros m. rename H into M. forward. 
    remember_vals tvals.
    forward.
    replace_SEP 0 (preInit Ews (ctx_size_of_MD D) m). 
    { entailer!. apply preInit_fresh_EWS. }
    forward_call (ctx, csh, (t, (m, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD D), Ews).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
    deadvars!. simpl. subst. forward.
    Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
    evar (z:reptype (Tstruct digests._env_md_st noattr)).
    Exists tsh z; subst z. unfold EVP_MD_NNnode; entailer!.
    simpl. entailer!. apply orp_right2.
    Exists m. entailer!.
Qed.
*)


(*Individual proof of eq case
Definition EVP_DigestInit_ex_SPEC_d_eq_t := DECLARE _EVP_DigestInit_ex
  WITH ctx:val, t:val, e:val, mdd:val, pv: val * val, D: EVP_MD, gv:globals, csh:share
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (4 <= ctx_size_of_MD D <= Int.max_unsigned; writable_share csh)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERRGV gv; EVP_MD_CTX_NNnode csh (t,(mdd,pv)) ctx; 
           EVP_MD_rep D t; preInit Ews (ctx_size_of_MD D) mdd)
  POST [ tint] EX rv:_,
       PROP (rv = Vint Int.one)
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; (*digestInitEx_post c ctx t rv*)
            EVP_MD_CTX_NNnode csh (t,(mdd,pv)) ctx; 
            EVP_MD_rep D t;MD_state Ews (INI D) mdd).

Lemma body_DigestInit_ex_eq: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC_d_eq_t.
Proof. 
  start_function. destruct pv as [pv1 pv2]. unfold EVP_MD_CTX_NNnode; Intros. forward.
  rewrite EVP_MD_rep_isptr'; Intros. unfold EVP_MD_rep; Intros tsh tvals. rename H into Rtsh.
  forward_if (PROP ( )
     LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
     SEP (data_at csh (Tstruct _env_md_ctx_st noattr) (t, (mdd, (pv1, pv2))) ctx;
          ERRGV gv; match_EVP_MD D tvals; preInit Ews (ctx_size_of_MD D) mdd;
          data_at tsh (Tstruct digests._env_md_st noattr) tvals t)).
    { apply ptr_comp_Cne_t in H; congruence. }
    { forward. entailer!. }
  forward.
  remember_vals tvals.
  freeze [1;3;4] FR1.
  forward.
  forward_call (ctx, csh, (t, (mdd, (pv1,pv2))), tsh, tvals, Int.repr (ctx_size_of_MD D), Ews(*mdsh*)).
    { rewrite Int.unsigned_repr by omega. simpl. cancel. }
    { rewrite Int.unsigned_repr by omega. subst; intuition. }
  deadvars!. simpl. thaw FR1. subst. forward.
  Exists (Vint (Int.repr 1)); unfold EVP_MD_rep; entailer!.
  evar (z:reptype (Tstruct digests._env_md_st noattr)).
  Exists tsh z; subst z. entailer!. simpl. entailer!.
Qed.
*)
*)

Definition Gprog_EVP_Digest : funspecs :=
  [EVP_MD_CTX_init_SPEC; EVP_DigestInit_ex_SPEC; EVP_DigestUpdate_SPEC;
   EVP_DigestFinal_ex_SPEC; EVP_MD_CTX_cleanup_SPEC].

Lemma body_EVP_Digest: semax_body Vprog Gprog_EVP_Digest
                           f_EVP_Digest EVP_Digest_SPEC.
Proof. start_function.
  rename H into CTXSZ. rename H0 into UPDSC.
  rename SH into DSH. rename SH0 into OSH.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] v_ctx) as FCctx by entailer!.
  rewrite (EVP_MD_rep_isptr'); Intros. 
(*  assert (CTXSZ3: Int.eq (Int.repr (ctx_size_of_MD D)) Int.zero = false).
  { destruct (Int.eq_dec (Int.repr (ctx_size_of_MD D)) Int.zero); subst.
    + assert (Int.unsigned (Int.repr (ctx_size_of_MD D)) = 0). rewrite e0; reflexivity. rewrite Int.unsigned_repr in H; omega.
    + rewrite Int.eq_false; trivial. }*)
  forward_call (v_ctx, Tsh, sizeof (Tstruct _env_md_ctx_st noattr)).
  replace_SEP 0 (data_at Tsh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) v_ctx).
  solve [entailer!; apply convert; [ apply writable_readable | ]; trivial ].
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
  { entailer!. rewrite 2 data_at__memory_block. simpl; entailer!. }
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
         postFin Ews (ctx_size_of_MD D) m;
         EVP_MD_rep D t;OPENSSL_malloc_token (ctx_size_of_MD D) m; mm_inv gv;
         if Val.eq sz nullval then emp else data_at Ews tuint (Vint (Int.repr (md_size_of_MD D))) sz;
         data_block osh (FIN (UPD (INI D) Data (Int.unsigned cnt))) md; data_block dsh Data d; ERRGV gv));
    [ clear H | solve [inv H] |].
  { forward_call (v_ctx, Tsh, (t, (m, (nullval, nullval))), md, osh, sz, UPD (INI D) Data (Int.unsigned cnt), Ews).
    { simpl; cancel. }
    { simpl. repeat (split; trivial); try omega. }
    forward. entailer!. }
  forward. deadvars!.
  sep_apply (postFin_memory_block Ews (ctx_size_of_MD D) m).
  unfold EVP_MD_rep. Intros tsh tvals. rename H into Rtsh.
  destruct_vals tvals tsh. Intros.
  forward_call (gv,v_ctx, Tsh, m, Some (ctx_size_of_MD D)).
  { Exists t nullval; unfold EVP_MD_NNnode; simpl. entailer!. }
  replace_SEP 0 (data_at_ Tsh (Tstruct _env_md_ctx_st noattr) v_ctx).
  { entailer!. rewrite 2 data_at__memory_block. simpl; entailer!. }
  forward. Exists Int.one. entailer!.
  unfold EVP_MD_rep, EVP_MD_NNnode.
  evar (z:reptype (Tstruct _env_md_st noattr)).
  Exists tsh z; subst z. entailer!. simpl. entailer!.
  apply orp_right2. entailer!.
Time Qed. (*6s*)
(*
Definition mdDATA sh sz data md: mpred :=
  (!!(md=nullval) && emp) || ((!!isptr md) && data_at sh (tarray tuchar (Int.unsigned sz)) data md).

Lemma mdDATA_validptr ctxsz sh data md (SH: readable_share sh)
      (SZ: sizeof (tarray tuchar (Int.unsigned ctxsz)) > 0):
      mdDATA sh ctxsz data md |-- valid_pointer md.
Proof. apply orp_left; normalize. apply valid_pointer_null. apply data_at_valid_ptr.
  intuition. trivial.
Qed. *)

(*
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
  { unfold ERRGV; cancel. }
  forward. Exists nullval. unfold ERRGV; entailer!. 
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
  { unfold ERRGV; cancel. }
  forward. Exists nullval. unfold ERRGV; entailer!. 
+ (*Case outdigestNull *)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. subst.
  rename H4 into SZ. rewrite data_at_isptr with (p:=ictx); Intros.
  rewrite data_at_isptr with (p:=d); Intros. 
  freeze [3;4;5(*;6*)] FR1.
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
  focus_SEP 2.
  forward_if (EX buf:_, EX m:val,
    (PROP (malloc_compatible (Int.unsigned ctxsz) buf )
    LOCAL (temp _tmp_buf buf; temp _pctx (Vint (Int.repr 0)); gvars gv; temp _out octx; temp _in ictx)
    SEP (memory_block Ews (Int.unsigned ctxsz) buf;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
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
                     ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md')
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
    Intros m.
    forward.
    apply semax_orp_SEPx; Intros; subst. 
    { freeze [0;1;2;3;5;6] FR2. 
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
          { unfold ERRGV; cancel. }
          forward. Exists nullval; thaw FR2; unfold ERRGV; entailer!.
          rewrite if_false by congruence. apply orp_right1. entailer!. 
          destruct pp as [[[dsh' vals'] ctxsz'] | ]; entailer!.  
      + discriminate.
      + entailer!. }
    { rename H into M.
      rewrite memory_block_isptr; Intros. freeze [1;2;3;4;5;6] FR3.
      forward_if (
        PROP ( )
        LOCAL (temp _tmp_buf m; temp _pctx (Vint (Int.repr 0)); 
               gvars gv; temp _out octx; temp _in ictx)
        SEP (memory_block Ews (Int.unsigned ctxsz) m; FRZL FR3)).
      { subst; contradiction. }
      { forward. entailer!. }
      thaw FR3. Exists m md'. entailer!. destruct pp as [[[dsh' vals'] ctxsz'] | ]; Intros.
      + Exists dsh' vals' ctxsz'. rewrite if_false by congruence. entailer!.
      + Exists Ews (default_val (Tstruct _env_md_st noattr)) Int.zero. rewrite if_false by congruence. entailer!. } }
  { (*d' = d*) 
    apply ptr_comp_Cne_f in H; trivial. subst d'. rewrite if_true; trivial; Intros; subst.
    rename H0 into M.
    do 2 forward; entailer!. 
    Exists md' nullval. Exists Ews (default_val (Tstruct _env_md_st noattr)) Int.zero.
    rewrite if_true; trivial. entailer!. }

  Intros buf m dsh' vals' ctxsz'. rename H into BUF.

  freeze [0;1;4;5;6] FRAME1.
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

  forward_call (octx, osh, m, if Val.eq m nullval then None else match pp with None => None | Some _ => Some (Int.unsigned ctxsz') end).
  { assert (Frame = [FRZL FRAME1; if Val.eq d d' then emp else 
             match pp with None => emp | Some _ => data_at dsh' (Tstruct _env_md_st noattr) vals' d' end]);
       subst Frame. reflexivity. clear H.
    simpl; cancel.
    destruct (Val.eq d d'); Intros.
    + destruct PP; subst. clear H H0. rewrite if_true; trivial. Exists d' pv1'; entailer!.
    + destruct pp as [[[dhs'' vals''] ctxsz''] | ]; Intros.
      - destruct PP as [? [? [? [? ?]]]]. subst. Exists d' pv1'; entailer!.
        apply orp_left; Intros; subst.
        * rewrite if_true; trivial. entailer!.
        * rewrite memory_block_isptr; Intros. rewrite if_false; trivial.
          intros N; subst md'; contradiction.
      - subst. Exists nullval pv1'. rewrite if_true; trivial. entailer!. }
  Intros. rename H into FC0.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block; entailer!. }
  thaw FRAME1. do 7 forward. simpl. deadvars!.
  forward_call ((imdsh, Ews), buf, md, Int.unsigned ctxsz, idata).
  { rewrite Int.repr_unsigned. simpl; entailer!. }
  { simpl; cancel. }
  { simpl; intuition. }
  do 4 forward.
  Exists (Vint Int.one); entailer!.
  destruct (Val.eq d d'). 
  - destruct PP as [? ?]. subst d' buf m. cancel.
  - apply orp_right2; Exists buf; entailer!. 
    destruct pp as [[[? ?] ?] | ];
    [ destruct PP as [? [? [? [? [? ?]]]]]; subst; trivial
    | destruct PP as [? [? ?]]; subst; trivial ].
Time Qed.
*)
(*
+ (*Case other *)
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
  focus_SEP 2.
  forward_if (EX buf:_, EX m:val,
    (PROP (malloc_compatible (Int.unsigned ctxsz) buf )
    LOCAL (temp _tmp_buf buf; temp _pctx (Vint (Int.repr 0)); gvars gv; temp _out octx; temp _in ictx)
    SEP (memory_block Ews (Int.unsigned ctxsz) buf;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at osh (Tstruct _env_md_ctx_st noattr) (d', (m, (pv1', nullval))) octx;
         EX dsh' : share, EX vals' : _, EX ctxsz':_, (*
         if Val.eq d d'
         then !!(m=nullval) && emp
         else (!! (m=md' /\ readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' ) 
                  && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                     ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md'));*)
         match pp with 
         | None => !!(d=d' /\ buf=md' /\ m=nullval) && emp
         | Some (dsh'', vals'', ctxsz'') =>
                  !! (d<>d' /\ m=md' /\ dsh''=dsh' /\ vals''=vals'/\ctxsz''=ctxsz' /\
                      readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz')
                  && ((*(!!(d'=nullval)&&emp) ||*) data_at dsh' (Tstruct _env_md_st noattr) vals' d') *
                     ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md')
         end;
         ERRGV gv;
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)))%assert.
  { clear H. destruct pp as [[[dsh' vals'] ctxsz'] | ]; entailer!. (*
    rewrite ! sepcon_assoc. rewrite distrib_orp_sepcon.
    apply orp_left; Intros. subst; entailer!. entailer!.
    (* if_tac; subst; [ entailer! | ]. Intros dsh' vals ctxsz'; entailer! ].*)*) }
  { (*d' <> d*) 
    apply ptr_comp_Cne_t in H; trivial. (* rewrite if_false by congruence. *)
    destruct pp as [[[dsh' vals'] ctxsz'] | ]; Intros; [ | congruence].
    rename H into DD'. (*Intros dsh' vals' ctxsz'.*)  rename H0 into DSH'.
    do 2 forward.
    forward_call (Int.unsigned ctxsz). 
    { rewrite Int.repr_unsigned; simpl; entailer!. }
    Intros m.
    apply semax_orp_SEPx; Intros; subst.
    { forward. freeze [0;1;2;3;4;6;7] FR2.
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
          { unfold ERRGV; cancel. }
          forward. Exists nullval; thaw FR2; unfold ERRGV; entailer!. 
          rewrite ! sepcon_assoc. (*rewrite distrib_orp_sepcon. 
          apply orp_left; Intros. *)
          apply orp_right1. entailer!. 
      + discriminate.
      + entailer!. }
    { rename H into M. forward.
      rewrite memory_block_isptr; Intros. freeze [1;2;3;4;5;6;7] FR3.
      forward_if (
        PROP ( )
        LOCAL (temp _tmp_buf m; temp _pctx (Vint (Int.repr 0)); 
               gvars gv; temp _out octx; temp _in ictx)
        SEP (memory_block Ews (Int.unsigned ctxsz) m; FRZL FR3)).
      { subst; contradiction. }
      { forward. entailer!. }
      thaw FR3. Exists m md'; entailer!. Exists dsh' vals' ctxsz'; entailer!.
      (* rewrite if_false by congruence. entailer!.*) } }
  { (*d' = d*) 
    apply ptr_comp_Cne_f in H; trivial; subst d'. (* rewrite if_true; trivial.*)
    destruct pp as [[[dsh' vals'] ctxsz'] | ]; Intros; [ congruence | ].
    rename H into M.
    do 2 forward; entailer!. 
    Exists md' nullval Ews (default_val (Tstruct digests._env_md_st noattr)) ctxsz.
    (*rewrite if_true; trivial.*) entailer!. }

  Intros buf m dsh' vals' ctxsz'. rename H into BUF.

  freeze [0;1;4;5;6;7] FRAME1.
  (*assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCO by entailer!.*)
  assert_PROP (match pp with
     | Some (dsh'', vals'', ctxsz'') =>
          (d <> d' /\ m = md' /\ dsh'' = dsh' /\ vals'' = vals' /\ ctxsz'' = ctxsz' /\
           readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz')
     | None => (d = d' /\ buf=md' /\ m = nullval)
     end) as PP by (destruct pp as [[[? ?] ?] | ]; entailer!). 
  forward_call (octx, osh, m, if Val.eq m nullval then None else Some (Int.unsigned ctxsz')).
  { assert (Frame = [FRZL FRAME1; if Val.eq d d' then emp else data_at dsh' (Tstruct _env_md_st noattr) vals' d']); subst Frame. reflexivity. clear H.
    simpl; cancel.
    destruct pp as [[[dhs'' vals''] ctxsz''] | ]; Intros.
    + subst. Exists d' pv1'; entailer!.
      rewrite sepcon_comm; rewrite distrib_orp_sepcon. apply orp_left; Intros.
      - rewrite if_true, if_false; trivial. entailer!.
      - rewrite memory_block_isptr; Intros. rewrite 2 if_false; trivial. 
        intros N; subst md'; contradiction.
    + subst; Exists d' pv1'. rewrite 2 if_true; trivial. entailer!. }
  Intros. rename H into FC0.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block; entailer!. }
  thaw FRAME1. do 7 forward. simpl. deadvars!.
  forward_call ((imdsh, Ews), buf, md, Int.unsigned ctxsz, idata).
  { rewrite Int.repr_unsigned. simpl; entailer!. }
  { simpl; cancel. }
  { simpl; intuition. }
  do 4 forward.
  Exists (Vint Int.one); entailer!. apply orp_right2; Exists buf; entailer!.
  destruct pp as [[[? ?] ?] | ];
  [ destruct PP as [? [? [? [? [? ?]]]]]; subst; rewrite if_false; trivial
  | destruct PP as [? [? ?]]; subst; rewrite if_true; trivial; entailer! ].
Time Qed. (*20s*)

(*require that d'null implies md'=null - otherwise, cleanup wouln't know how much to free (sanity invariant)*)
Definition copyExPre (c:copyEx_cases) (ictx octx:val) : mpred :=
match c with 
  copyEx_ictxNull => !!(ictx=nullval)&&emp
| copyEx_indigestNull ish md pv1 pv2 => !!(readable_share ish)
                            && EVP_MD_CTX_NNnode ish (nullval, (md, (pv1, pv2))) ictx
| copyEx_outdigestNull ish d md pv1 pv2 dsh vals osh d' md' pv1' ctxsz imdsh idata pp =>
       !!(isptr octx /\ readable_share ish /\
          readable_share dsh /\ writable_share osh /\ pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned /\
          readable_share imdsh /\ d'=nullval /\ md'=nullval)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (d', (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md (*
          match pp with
          | None => !! (d = d' /\ malloc_compatible (Int.unsigned ctxsz) md') && 
                    memory_block Ews (Int.unsigned ctxsz) md'  
          | Some (dsh', vals', ctxsz') => 
               !!(d' <> d /\ readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz'(*Int.lt Int.zero ctxsz = true *)(*/\ Int.eq ctxsz' Int.zero = false*)) 
               && (data_at dsh' (Tstruct _env_md_st noattr) vals' d') *
                   ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md')
          end*)
| copyEx_other ish d md pv1 pv2 dsh vals osh d' md' pv1' ctxsz imdsh idata pp =>
       !!(isptr octx /\ readable_share ish /\
          readable_share dsh /\ writable_share osh /\ pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned /\
          readable_share imdsh)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (d', (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
          match pp with
          | None => !! (d = d' /\ malloc_compatible (Int.unsigned ctxsz) md') && 
                    memory_block Ews (Int.unsigned ctxsz) md'  
          | Some (dsh', vals', ctxsz') => 
               !!(d' <> d /\ readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz'(*Int.lt Int.zero ctxsz = true *)(*/\ Int.eq ctxsz' Int.zero = false*)) 
               && (data_at dsh' (Tstruct _env_md_st noattr) vals' d') *
                   ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md')
          end
end.
Parameter PP: mpred.
Definition copyExPost (c: copyEx_cases) (ictx octx:val) rv : mpred := 
match c with
  copyEx_ictxNull => !!(rv=Vint Int.zero) && emp
| copyEx_indigestNull ish md pv1 pv2 => !!(rv=Vint Int.zero) && data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2))) ictx
| copyEx_outdigestNull ish d md pv1 pv2 dsh vals osh d' md' pv1' ctxsz imdsh idata pp => PP
| copyEx_other ish d md pv1 pv2 dsh vals osh d' md' pv1' ctxsz imdsh idata pp => 
    ( !!(rv=Vint Int.zero /\ d' <> d) && 
        match pp with 
        | None => FF
        | Some (dsh', vals', ctxsz') =>
          data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
          data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx *
          data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
          (!! (md' = nullval) && emp || memory_block Ews (Int.unsigned ctxsz') md')
        end)
  ||
    ( EX buf:val, !!(rv=Vint Int.one /\ malloc_compatible (Int.unsigned ctxsz) buf) &&
      data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx *
      data_at dsh (Tstruct _env_md_st noattr) vals d *
      data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
      data_at osh (Tstruct _env_md_ctx_st noattr) (d, (buf, (Vint (Int.repr 0), pv2))) octx *
      data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) buf * 
      match pp with
      | None => !!(buf=md') && emp
      | Some (dsh', vals', ctxsz') => data_at dsh' (Tstruct _env_md_st noattr) vals' d'
      end)
end.

Definition EVP_MD_CTX_copy_ex_SPEC := DECLARE _EVP_MD_CTX_copy_ex
  WITH gv:globals, octx:val, ictx:val, case:copyEx_cases
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvars gv; temp _out octx; temp _in ictx)
      SEP (ERRGV gv; copyExPre case ictx octx)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; copyExPost case ictx octx rv).

Definition Gprog_copy_ex : funspecs :=
  [OPENSSL_memcpy_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_malloc_SPEC; EVP_MD_CTX_cleanup_SPEC].

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
  { unfold ERRGV; cancel. }
  forward. Exists nullval. unfold ERRGV; entailer!. 
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
  { unfold ERRGV; cancel. }
  forward. Exists nullval. unfold ERRGV; entailer!. 
+ (*Case outdigestNull *)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. subst.
  rename H4 into SZ. rewrite data_at_isptr with (p:=ictx); Intros.
  rewrite data_at_isptr with (p:=d); Intros. 
  freeze [3;4(*;5;6*)] FR1.
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
  focus_SEP 2.
  forward_if (EX buf:_, (*EX m:val,*)
    (PROP (malloc_compatible (Int.unsigned ctxsz) buf )
    LOCAL (temp _tmp_buf buf; temp _pctx (Vint (Int.repr 0)); gvars gv; temp _out octx; temp _in ictx)
    SEP (memory_block Ews (Int.unsigned ctxsz) buf;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at osh (Tstruct _env_md_ctx_st noattr) ((*d'*)nullval, ((*m*)nullval, (pv1', nullval))) octx;
         (*EX dsh' : share, EX vals' : _, EX ctxsz':_, 
         match pp with 
         | None => !!(d=d' /\ buf=md' /\ m=nullval) && emp
         | Some (dsh'', vals'', ctxsz'') =>
                  !! (d<>d' /\ m=md' /\ dsh''=dsh' /\ vals''=vals'/\ctxsz''=ctxsz' /\
                      readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz')
                  && ((*(!!(d'=nullval)&&emp) ||*) data_at dsh' (Tstruct _env_md_st noattr) vals' d') *
                     ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md')
         end;*)
         ERRGV gv;
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)))%assert.
(*  { clear H. destruct pp as [[[dsh' vals'] ctxsz'] | ]; entailer!. (*
    rewrite ! sepcon_assoc. rewrite distrib_orp_sepcon.
    apply orp_left; Intros. subst; entailer!. entailer!.
    (* if_tac; subst; [ entailer! | ]. Intros dsh' vals ctxsz'; entailer! ].*)*) }*)
  { (*d' <> d*) 
    apply ptr_comp_Cne_t in H; trivial. clear H.  (*
    destruct pp as [[[dsh' vals'] ctxsz'] | ]; Intros; [ | congruence].
    rename H into DD'.  rename H0 into DSH'.*)
    do 2 forward.
    forward_call (Int.unsigned ctxsz). 
    { rewrite Int.repr_unsigned; simpl; entailer!. }
    Intros m.
    forward.
    apply semax_orp_SEPx; Intros; subst. 
    { freeze [0;(*1;*)2;3;4;5(*;6;7*)] FR2. 
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
          { unfold ERRGV; cancel. }
          forward. Exists nullval; thaw FR2; unfold ERRGV; entailer!. admit. (*case rv=null:PP*) 
          (*apply orp_right1. entailer!. *)
      + discriminate.
      + entailer!. }
    { rename H into M.
      rewrite memory_block_isptr; Intros. freeze [1;2;3;4;5(*;6;7*)] FR3.
      forward_if (
        PROP ( )
        LOCAL (temp _tmp_buf m; temp _pctx (Vint (Int.repr 0)); 
               gvars gv; temp _out octx; temp _in ictx)
        SEP (memory_block Ews (Int.unsigned ctxsz) m; FRZL FR3)).
      { subst; contradiction. }
      { forward. entailer!. }
      thaw FR3. Exists m (*md'*); entailer!. (* Exists dsh' vals' ctxsz'; entailer!.*) } }
  { (*d' = d*) 
    apply ptr_comp_Cne_f in H; trivial. subst; contradiction. (*; subst d'.
    destruct pp as [[[dsh' vals'] ctxsz'] | ]; Intros; [ congruence | ].
    rename H into M.
    do 2 forward; entailer!. 
    Exists md' nullval Ews (default_val (Tstruct digests._env_md_st noattr)) ctxsz.
    (*rewrite if_true; trivial.*) entailer!.*) }

  Intros buf (*m dsh' vals' ctxsz'*). rename H into BUF.

  freeze [0;1;3;4;5(*;6;7*)] FRAME1.
(*  assert_PROP (match pp with
     | Some (dsh'', vals'', ctxsz'') =>
          (d <> d' /\ m = md' /\ dsh'' = dsh' /\ vals'' = vals' /\ ctxsz'' = ctxsz' /\
           readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz')
     | None => (d = d' /\ buf=md' /\ m = nullval)
     end) as PP by (destruct pp as [[[? ?] ?] | ]; entailer!). *)
  forward_call (octx, osh, (*m*)nullval, @None Z). (*if Val.eq m nullval then None else Some (Int.unsigned ctxsz')).*)
  { assert (Frame = [FRZL FRAME1(*; if Val.eq d d' then emp else data_at dsh' (Tstruct _env_md_st noattr) vals' d'*)]);
       subst Frame. reflexivity. clear H.
    simpl; cancel.
    (*destruct pp as [[[dhs'' vals''] ctxsz''] | ]; Intros.
    + subst. Exists d' pv1'; entailer!.
      rewrite sepcon_comm; rewrite distrib_orp_sepcon. apply orp_left; Intros.
      - rewrite if_true, if_false; trivial. entailer!.
      - rewrite memory_block_isptr; Intros. rewrite 2 if_false; trivial. 
        intros N; subst md'; contradiction.
    + subst; Exists d' pv1'. rewrite 2 if_true; trivial. entailer!. *)
    Exists nullval pv1'. entailer!. }
  Intros. rename H into FC0.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block; entailer!. }
  thaw FRAME1. do 7 forward. simpl. deadvars!.
  forward_call ((imdsh, Ews), buf, md, Int.unsigned ctxsz, idata).
  { rewrite Int.repr_unsigned. simpl; entailer!. }
  { simpl; cancel. }
  { simpl; intuition. }
  do 4 forward.
  Exists (Vint Int.one); entailer!. apply orp_right2; Exists buf; entailer!.
  destruct pp as [[[? ?] ?] | ];
  [ destruct PP as [? [? [? [? [? ?]]]]]; subst; rewrite if_false; trivial
  | destruct PP as [? [? ?]]; subst; rewrite if_true; trivial; entailer! ].
+ (*Case other *)
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
  focus_SEP 2.
  forward_if (EX buf:_, EX m:val,
    (PROP (malloc_compatible (Int.unsigned ctxsz) buf )
    LOCAL (temp _tmp_buf buf; temp _pctx (Vint (Int.repr 0)); gvars gv; temp _out octx; temp _in ictx)
    SEP (memory_block Ews (Int.unsigned ctxsz) buf;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at osh (Tstruct _env_md_ctx_st noattr) (d', (m, (pv1', nullval))) octx;
         EX dsh' : share, EX vals' : _, EX ctxsz':_, (*
         if Val.eq d d'
         then !!(m=nullval) && emp
         else (!! (m=md' /\ readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' ) 
                  && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                     ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md'));*)
         match pp with 
         | None => !!(d=d' /\ buf=md' /\ m=nullval) && emp
         | Some (dsh'', vals'', ctxsz'') =>
                  !! (d<>d' /\ m=md' /\ dsh''=dsh' /\ vals''=vals'/\ctxsz''=ctxsz' /\
                      readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz')
                  && ((*(!!(d'=nullval)&&emp) ||*) data_at dsh' (Tstruct _env_md_st noattr) vals' d') *
                     ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md')
         end;
         ERRGV gv;
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)))%assert.
  { clear H. destruct pp as [[[dsh' vals'] ctxsz'] | ]; entailer!. (*
    rewrite ! sepcon_assoc. rewrite distrib_orp_sepcon.
    apply orp_left; Intros. subst; entailer!. entailer!.
    (* if_tac; subst; [ entailer! | ]. Intros dsh' vals ctxsz'; entailer! ].*)*) }
  { (*d' <> d*) 
    apply ptr_comp_Cne_t in H; trivial. (* rewrite if_false by congruence. *)
    destruct pp as [[[dsh' vals'] ctxsz'] | ]; Intros; [ | congruence].
    rename H into DD'. (*Intros dsh' vals' ctxsz'.*)  rename H0 into DSH'.
    do 2 forward.
    forward_call (Int.unsigned ctxsz). 
    { rewrite Int.repr_unsigned; simpl; entailer!. }
    Intros m.
    apply semax_orp_SEPx; Intros; subst.
    { forward. freeze [0;1;2;3;4;6;7] FR2.
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
          { unfold ERRGV; cancel. }
          forward. Exists nullval; thaw FR2; unfold ERRGV; entailer!. 
          rewrite ! sepcon_assoc. (*rewrite distrib_orp_sepcon. 
          apply orp_left; Intros. *)
          apply orp_right1. entailer!. 
      + discriminate.
      + entailer!. }
    { rename H into M. forward.
      rewrite memory_block_isptr; Intros. freeze [1;2;3;4;5;6;7] FR3.
      forward_if (
        PROP ( )
        LOCAL (temp _tmp_buf m; temp _pctx (Vint (Int.repr 0)); 
               gvars gv; temp _out octx; temp _in ictx)
        SEP (memory_block Ews (Int.unsigned ctxsz) m; FRZL FR3)).
      { subst; contradiction. }
      { forward. entailer!. }
      thaw FR3. Exists m md'; entailer!. Exists dsh' vals' ctxsz'; entailer!.
      (* rewrite if_false by congruence. entailer!.*) } }
  { (*d' = d*) 
    apply ptr_comp_Cne_f in H; trivial; subst d'. (* rewrite if_true; trivial.*)
    destruct pp as [[[dsh' vals'] ctxsz'] | ]; Intros; [ congruence | ].
    rename H into M.
    do 2 forward; entailer!. 
    Exists md' nullval Ews (default_val (Tstruct digests._env_md_st noattr)) ctxsz.
    (*rewrite if_true; trivial.*) entailer!. }

  Intros buf m dsh' vals' ctxsz'. rename H into BUF.

  freeze [0;1;4;5;6;7] FRAME1.
  (*assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCO by entailer!.*)
  assert_PROP (match pp with
     | Some (dsh'', vals'', ctxsz'') =>
          (d <> d' /\ m = md' /\ dsh'' = dsh' /\ vals'' = vals' /\ ctxsz'' = ctxsz' /\
           readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz')
     | None => (d = d' /\ buf=md' /\ m = nullval)
     end) as PP by (destruct pp as [[[? ?] ?] | ]; entailer!). 
  forward_call (octx, osh, m, if Val.eq m nullval then None else Some (Int.unsigned ctxsz')).
  { assert (Frame = [FRZL FRAME1; if Val.eq d d' then emp else data_at dsh' (Tstruct _env_md_st noattr) vals' d']); subst Frame. reflexivity. clear H.
    simpl; cancel.
    destruct pp as [[[dhs'' vals''] ctxsz''] | ]; Intros.
    + subst. Exists d' pv1'; entailer!.
      rewrite sepcon_comm; rewrite distrib_orp_sepcon. apply orp_left; Intros.
      - rewrite if_true, if_false; trivial. entailer!.
      - rewrite memory_block_isptr; Intros. rewrite 2 if_false; trivial. 
        intros N; subst md'; contradiction.
    + subst; Exists d' pv1'. rewrite 2 if_true; trivial. entailer!. }
  Intros. rename H into FC0.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block; entailer!. }
  thaw FRAME1. do 7 forward. simpl. deadvars!.
  forward_call ((imdsh, Ews), buf, md, Int.unsigned ctxsz, idata).
  { rewrite Int.repr_unsigned. simpl; entailer!. }
  { simpl; cancel. }
  { simpl; intuition. }
  do 4 forward.
  Exists (Vint Int.one); entailer!. apply orp_right2; Exists buf; entailer!.
  destruct pp as [[[? ?] ?] | ];
  [ destruct PP as [? [? [? [? [? ?]]]]]; subst; rewrite if_false; trivial
  | destruct PP as [? [? ?]]; subst; rewrite if_true; trivial; entailer! ].
Time Qed. (*20s*)
(*
(*
Inductive copyEx_cases :=
  ictxNull: copyEx_cases
| inDigestNull: forall (ish:share) (md pv1 pv2 :val), copyEx_cases
| inDataNull: forall (ish:share) (d pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val), copyEx_cases
| equalDigests_outDataNull: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int), copyEx_cases
| equalDigests_outDataPtr: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (md':val), copyEx_cases
| outDigest_Null: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int), copyEx_cases
| distinctDigests: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (dsh':share) (vals' : reptype (Tstruct _env_md_st noattr))(ctxsz': int), copyEx_cases(*.
| indataPtr: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val)
                      (idsh:share) (idata:list val), copyEx_cases*).

Definition copyExPre (c:copyEx_cases) (ictx octx:val) : mpred :=
match c with 
  ictxNull => !!(ictx=nullval)&&emp
| inDigestNull ish md pv1 pv2 => !!(isptr ictx /\ readable_share ish)
                            && EVP_MD_CTX_NNnode ish (nullval, (md, (pv1, pv2))) ictx
| inDataNull ish d pv1 pv2 dsh vals osh d' md' pv1' =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ pv1=nullval /\ is_pointer_or_null pv2)
       && EVP_MD_CTX_NNnode ish (d, (nullval, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (d', (md', (pv1', nullval))) octx *
          if orb (Val.eq d' nullval) (Val.eq d d') 
          then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
          else EX dsh':_, EX vals':_, EX ctxsz': _,
               !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
               && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                  ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md')
| equalDigests_outDataNull ish d md pv1 pv2 dsh vals osh pv1' imdsh idata ctxsz =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (d, (nullval, (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md
| equalDigests_outDataPtr ish d md pv1 pv2 dsh vals osh pv1' imdsh idata ctxsz md' =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned /\
          isptr md')
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (d, (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
          memory_block Ews (Int.unsigned ctxsz) md'
| outDigest_Null ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (nullval, (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md

| distinctDigests ish d md pv1 pv2 dsh vals osh d' md' pv1' imdsh idata ctxsz dsh' vals' ctxsz' =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned /\
          d<>d' /\
          get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_NNnode dsh' vals' d' *
          EVP_MD_CTX_NNnode osh (d', (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
          ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md')
end.

Definition POST3 ictx octx ish d  pv2 (*dsh*) (vals:reptype (Tstruct _env_md_st noattr)) osh d' (*md' pv1' idsh idata*) rv:mpred :=
!!(rv=Vint Int.one) &&
match vals with (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) =>
(if orb (Val.eq d' nullval) (Val.eq d d')
 then
  EX ctxsz : int,
  !! (get_ctxsize (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) = Vint ctxsz /\ Int.eq ctxsz Int.zero = false) && emp
 else
  EX dsh' : share,
  (EX vals' : reptype (Tstruct _env_md_st noattr),
   (EX ctxsz' : int,
    !! (readable_share dsh' /\
        get_ctxsize vals' = Vint ctxsz' /\
        Int.eq ctxsz' Int.zero = false) &&
    data_at dsh' (Tstruct _env_md_st noattr) vals' d'))) * 
(EVP_MD_node
   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d) *
(data_at osh (Tstruct _env_md_ctx_st noattr)
   (d,
   (Vundef,
   (Vundef,
   force_val
     (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
        (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx) *
(data_at ish (Tstruct _env_md_ctx_st noattr)
   (d, (nullval, (nullval, pv2))) ictx)
end.

Definition POST4 ictx octx rv ish d md pv2 dsh vals osh imdsh idata ctxsz:mpred :=
(!!(rv=Vint Int.zero)
 && (data_at osh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (Vundef, Vundef))) octx *
     data_at dsh (Tstruct _env_md_st noattr) vals d *
     data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
     data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx))
||
( !!(rv=Vint Int.one)
  && (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
    data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
    data_at osh (Tstruct _env_md_ctx_st noattr) (d, (m, (Vundef, pv2))) octx *
    data_at dsh (Tstruct _env_md_st noattr) vals d *
    data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
    data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)).

Definition POST5 (ictx octx rv:val) (ish:share) (d md pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (md':val): mpred :=
!!(rv=Vint Int.one)
&& data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md' *
   data_at osh (Tstruct _env_md_ctx_st noattr) (d, (md', (Vundef, pv2))) octx *
   data_at dsh (Tstruct _env_md_st noattr) vals d *
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx.

Definition POST6 (ictx octx rv:val) (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int): mpred :=
(!!(rv=Vint Int.zero)
 && (data_at osh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (Vundef, Vundef))) octx *
     data_at dsh (Tstruct _env_md_st noattr) vals d *
     data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
     data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx))
||
!!(rv=Vint Int.one)
&& EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
   data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
   data_at osh (Tstruct _env_md_ctx_st noattr) (d, (m, (Vundef, pv2))) octx *
   data_at dsh (Tstruct _env_md_st noattr) vals d *
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx.

Definition POST7 (ictx octx rv:val) (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (dsh':share)(vals' : reptype (Tstruct _env_md_st noattr))(ctxsz':int): mpred :=
(!!(rv=Vint Int.zero)
 && (data_at osh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (Vundef, Vundef))) octx *
     data_at dsh (Tstruct _env_md_st noattr) vals d *
     EVP_MD_NNnode dsh' vals' d' *
     data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
     data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx))
||
!!(rv=Vint Int.one)
&& EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
   data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
   data_at osh (Tstruct _env_md_ctx_st noattr) (d, (m, (Vundef, pv2))) octx * 
   EVP_MD_NNnode dsh' vals' d' *
   data_at dsh (Tstruct _env_md_st noattr) vals d *
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx.

Definition copyExPost (c: copyEx_cases) (ictx octx:val) rv : mpred := 
match c with
   ictxNull => !!(rv=Vint Int.zero) && emp
| inDigestNull ish md pv1 pv2 => !!(rv=Vint Int.zero) && data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2))) ictx
| inDataNull ish d pv1 pv2 dsh vals osh d' md' pv1' => POST3 ictx octx ish d  pv2 (*dsh*) vals osh d' rv
| equalDigests_outDataNull ish d md pv1 pv2 dsh vals osh pv1' imdsh idata ctxsz => 
    POST4 ictx octx rv ish d md pv2 dsh vals osh imdsh idata ctxsz
| equalDigests_outDataPtr ish d md pv1 pv2 dsh vals osh pv1' imdsh idata ctxsz md' => 
    POST5 ictx octx rv ish d md pv2 dsh vals osh pv1' imdsh idata ctxsz md'
| outDigest_Null ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz  =>
    POST6 ictx octx rv ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz
| distinctDigests ish d md pv1 pv2 dsh vals osh d' md' pv1' imdsh idata ctxsz dsh' vals' ctxsz' =>
    POST7 ictx octx rv ish d md pv1 pv2 dsh vals osh d' md' pv1' imdsh idata ctxsz dsh' vals' ctxsz'
end.

Definition EVP_MD_CTX_copy_ex_SPEC := DECLARE _EVP_MD_CTX_copy_ex
  WITH gv:globals(*ep: val*), octx:val, ictx:val, case:copyEx_cases
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvars gv (*gvar ___stringlit_1 ep*); temp _out octx; temp _in ictx)
      SEP (ERRGV gv;(*ERR ep;*) copyExPre case ictx octx)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; (*ERR ep;*) copyExPost case ictx octx rv).

Inductive copy_cases :=
  cp_ictxNull: copy_cases
| cp_inDigestNull: forall (ish:share) (md pv1 pv2 :val), copy_cases
| cp_inDataNull: forall (ish:share) (d pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr)), copy_cases
| cp_default: forall (ish:share) (d md pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (imdsh:share) (idata:list int) (ctxsz: int), copy_cases.

Definition copyPre (c:copy_cases) (ictx octx:val) : mpred :=
match c with 
  cp_ictxNull => !!(ictx=nullval)&&emp
| cp_inDigestNull ish md pv1 pv2 => !!(isptr ictx /\ readable_share ish)
                            && EVP_MD_CTX_NNnode ish (nullval, (md, (pv1, pv2))) ictx
| cp_inDataNull ish d pv2 dsh vals =>
       !!(readable_share ish /\ readable_share dsh /\ is_pointer_or_null pv2 /\
          exists ctxsz, get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)
       && EVP_MD_CTX_NNnode ish (d, (nullval, (nullval, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d 
| cp_default ish d md pv2 dsh vals imdsh idata ctxsz =>
       !!(readable_share ish /\ readable_share dsh /\ 
          is_pointer_or_null pv2 /\ readable_share imdsh /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
       && EVP_MD_CTX_NNnode ish (d, (md, (nullval, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md
end.

Definition Gprog_copy_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_memcpy_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_malloc_SPEC; EVP_MD_CTX_cleanup_SPEC].

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
  { unfold ERRGV; cancel. }
  forward. Exists nullval. unfold ERRGV; entailer!. 
+ (*Case 2: indigestNull*)
  rename H into ISH.
  forward_if (
   PROP ( )
   LOCAL (gvars gv; temp _t'1 (Vint Int.one); temp _in ictx)
   SEP (ERRGV gv; data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2)))
          ictx)); [ subst; contradiction | forward; forward; entailer! | ]. 
  
  forward_if (PROP (False) LOCAL () SEP()); [ | inv H ].
  forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                gv ___stringlit_1, Vint (Int.repr 120)).
  { unfold ERRGV; cancel. }
  forward. Exists nullval. unfold ERRGV; entailer!. 
+ (*Case 3: indataNull *)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. subst.
  freeze [3;4;5] FR1.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'1 (Vint Int.zero); temp _out octx; temp _in ictx)
    SEP (FRZL FR1; ERRGV gv; data_at dsh (Tstruct _env_md_st noattr) vals d;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx)).
  { subst; contradiction. }
  { do 2 forward. entailer!. destruct d; try contradiction; trivial. }

  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _out octx; temp _in ictx)
    SEP (FRZL FR1; ERRGV gv; data_at dsh (Tstruct _env_md_st noattr) vals d;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx));
  [ congruence | forward; entailer! | do 2 forward ].

  forward_if (
    PROP ( )
    LOCAL (temp _pctx (Vint (Int.repr 0)); 
    gvars gv; temp _out octx; temp _in ictx)
    SEP (FRZL FR1; ERRGV gv; data_at dsh (Tstruct _env_md_st noattr) vals d;
    data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx));
  [ contradiction | forward; entailer! | thaw FR1; do 2 forward ].

  forward_if (
    PROP ( )
    LOCAL (temp _t'11 d; temp _t'10 d'; temp _pctx (Vint (Int.repr 0)); 
    gvars gv; temp _out octx; temp _in ictx)
    SEP (data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx;
         if (Val.eq d' nullval || Val.eq d d')%bool
         then EX ctxsz : int,
              !! (get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero = false) && emp
         else
    EX dsh' : share,
    (EX vals' : reptype (Tstruct digests._env_md_st noattr),
     (EX ctxsz' : int,
      !! (readable_share dsh' /\
          get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) &&
      data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
      (!! (md' = nullval) && emp || memory_block Ews (Int.unsigned ctxsz') md')));
   ERRGV gv; data_at dsh (Tstruct _env_md_st noattr) vals d;
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx)).



  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'1 (Vint Int.zero); (*temp _t'20 d; 
           temp _tmp_buf (Vint (Int.repr 0));*) temp _out octx; temp _in ictx)
    SEP (ERRGV gv; data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d;
         data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx;
         if orb (Val.eq d' nullval) (Val.eq d d')
         then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
         else EX dsh':_, EX vals':_, EX ctxsz': _,
               !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
               && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                 ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md'))).
  { subst; contradiction. }
  { freeze [0;3;4] FR1. forward. forward. thaw FR1. entailer!. destruct d; try contradiction; trivial. }
  forward_if (
    PROP ( )
    LOCAL (gvars gv; (*temp _tmp_buf (Vint (Int.repr 0));*)
           temp _out octx; temp _in ictx)
    SEP (ERRGV gv;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d;
         data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx;
         if orb (Val.eq d' nullval) (Val.eq d d') then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
         else EX dsh':_, EX vals':_, EX ctxsz': _,
              !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
              && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                 ((!!(md' = nullval)&& emp) || memory_block Ews (Int.unsigned ctxsz') md'))).
   { elim H; trivial. }
   { clear H. forward. entailer!. }
   freeze [4] FR1. do 2 forward. 

   forward_if (PROP ( )
     LOCAL ((*temp _t'16 nullval;*) temp _pctx (Vint (Int.repr 0)); gvars gv; temp _out octx; temp _in ictx)
     SEP (FRZL FR1; ERRGV gv;
          data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx;
          data_at dsh (Tstruct _env_md_st noattr) vals d;
          data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx)).
   { contradiction. }
   { forward. entailer!. }
   do 2 forward.
   thaw FR1.
Here -- maybe this case should not have the d'=null clause?
   forward_if (
     PROP ( )
     LOCAL (gvars gv; temp _out octx; temp _in ictx;
            temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0)))
     SEP (ERRGV gv;
          data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx;
          data_at dsh (Tstruct _env_md_st noattr) vals d; FRZL FR2;
          data_at osh (Tstruct _env_md_ctx_st noattr) (d', (if Val.eq d d' then nullval else md', (pv1', nullval))) octx)).
   { clear H. destruct d; try contradiction.
     apply denote_tc_test_eq_split.
     + destruct (Val.eq (Vptr b i) d'); subst.
       - (*apply sepcon_valid_pointer1.*)
         apply sepcon_valid_pointer2. entailer!.
       - thaw FR2. destruct (Val.eq d' nullval); subst; [ solve [apply valid_pointer_null] | simpl ]. 
         Intros dsh' vals' ctxsz'.
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer2. 
         apply sepcon_valid_pointer1. (* 
         apply sepcon_valid_pointer1. *) clear -H. entailer!.
     + (* apply sepcon_valid_pointer1.*)
       apply sepcon_valid_pointer2. entailer!. }
   { apply ptr_comp_Cne_t in H; trivial. thaw FR2.
     (* unfold typed_true, sem_cmp_pp in H. forward.*)
     destruct d; try contradiction. destruct d'; try contradiction.
     + (*d'=nullval*) 
       simpl in PNd'; subst. clear H.
       destruct_vals vals ISH.
       forward. thaw FR1. Intros.

 forward.  inv H. admit.
       destruct (Int.eq i0 Int.zero); simpl in H; inv H.
       destruct (eq_block b0 b); subst; simpl in H.
       - destruct (Ptrofs.eq_dec i0 i); subst; simpl in H. elim n; trivial.
         rewrite Ptrofs.eq_false in H; trivial; inv H.
       - inv H. }
   { unfold typed_true, sem_cmp_pp in H. 
     destruct (Val.eq d d'); subst; simpl in H.
     + destruct d'; try contradiction. simpl in H.
       rewrite if_true, Ptrofs.eq_true in H; trivial. inv H.
     + forward. entailer!. }
   
   (*Line 133: cleanup*)
   thaw FR1.
   assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.

   assert (exists auxvals:reptype (Tstruct _env_md_ctx_st noattr), auxvals=(d, (nullval, (nullval, pv2)))).
   { eexists; reflexivity. }
   destruct H as [auxvals AUXVALS].
   eapply semax_seq with (Q:=
     PROP ( )
     LOCAL (gvars gv; temp _out octx; temp _in ictx;
            temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0))) 
     SEP (ERRGV gv; EVP_MD_node vals d;
          data_at_ osh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) octx; 
          if orb (Val.eq d' nullval) (Val.eq d d')
          then EX ctxsz : int,
               !! (get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero = false) && emp
          else EX dsh' : share,
               EX vals' : reptype (Tstruct _env_md_st noattr),
               EX ctxsz' : int, !! (readable_share dsh' /\
                                    get_ctxsize vals' = Vint ctxsz' /\
                                    Int.eq ctxsz' Int.zero = false)
                  && data_at dsh' (Tstruct _env_md_st noattr) vals' d';
                     data_at ish (Tstruct _env_md_ctx_st noattr) auxvals ictx)).
   { destruct (Val.eq d' nullval); subst.
     { simpl; Intros ctxsz. rename H into ctxszH1. rename H0 into ctxszH2.  
       rewrite ! if_false. 2: destruct d; try contradiction; discriminate. 2: destruct d; try contradiction; discriminate.
       abbreviate_semax. (*VST 2.3 alpha: why is abbreviate_semax now needed?*)
       forward_call (octx, osh, md', pv1', 
         @inl unit (share * val * (reptype (Tstruct _env_md_st noattr))) tt).
       { unfold EVP_MD_CTX_NNnode. entailer!. }
       entailer!. Exists ctxsz. entailer!. apply orp_right2. Exists dsh; unfold EVP_MD_NNnode. entailer!.
     } 
     rewrite orb_false_l.
     destruct (Val.eq d d'); subst; simpl.
     - Intros ctxsz. rename H into ctxszH1. rename H0 into ctxszH2.  
       abbreviate_semax. (*VST 2.3 alpha: why is abbreviate_semax now needed?*)
       forward_call (octx, osh, nullval, pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh, d', vals)).
       { Exists ctxsz. 
         assert (FR: Frame = [ERRGV gv; data_at ish (Tstruct _env_md_ctx_st noattr) (d', (nullval, (nullval, pv2))) ictx]); subst Frame. reflexivity.
         clear FR. simpl. unfold EVP_MD_NNnode. entailer!. apply orp_right1; trivial. }
       Exists ctxsz; entailer. cancel. apply orp_right2. Exists dsh. trivial. 
     - Intros dsh' vals' ctxsz'.
       rename H into DSH'. rename H0 into ctxszH1'. rename H1 into ctxszH2'. 
       rewrite data_at_isptr with (p:=d'). Intros. 
       freeze [0;1;2] FR2.
       abbreviate_semax. (*VST 2.3 alpha: why is abbreviate_semax now needed?*)
       forward_call (octx, osh, md', pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh', d', vals')).
       { Exists ctxsz'.
         assert (FR: Frame = [FRZL FR2]) (*data_at dsh (Tstruct _env_md_st noattr) vals d; 
                   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx])*); subst Frame. reflexivity.
         clear FR. simpl. unfold EVP_MD_NNnode. entailer!. }
       unfold EVP_MD_node, EVP_MD_NNnode. entailer!. Exists dsh' vals' ctxsz'. thaw FR2.
       cancel. 
       rewrite distrib_orp_sepcon. apply orp_right2. Exists dsh. normalize. cancel.  }

  unfold MORE_COMMANDS, abbreviate; subst auxvals. forward.
  replace_SEP 2 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. (*replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).*)

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward. 
  freeze [3] FR1.
  destruct_vals vals ISH.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'3 nullval; temp _t'20 nullval; temp _t'23 d;
           temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (ERRGV gv; FRZL FR1; EVP_MD_node (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
         field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (Vundef, (Vundef, Vundef))) octx;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  deadvars!.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _out octx; temp _in ictx; 
           temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0)))
    SEP (ERRGV gv; FRZL FR1;
         EVP_MD_node (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
         field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (Vundef, (Vundef, Vundef))) octx;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx)).
   { elim H; trivial. }
   { clear H. forward; entailer!. }

  forward. 
  freeze [0;1;2] FR2.
  forward. freeze [0;1] FR3. forward. freeze [0;1] FR4.

  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'5 nullval; temp _t'12 pv2;
           temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
           temp _out octx; temp _in ictx)  SEP (FRZL FR4)). 
   { contradiction. }
   { clear H. forward. entailer!. }

  deadvars!.
  forward_if 
    (PROP ( ) LOCAL (gvars gv; temp _out octx; temp _in ictx) SEP (FRZL FR4)).
  {  elim H; trivial. }
  { clear H. forward. entailer!. }

  forward. Exists (Vint Int.one). entailer!. thaw FR4. thaw FR3. thaw FR2.
  cancel. unfold POST3. apply andp_right; [ apply prop_right; trivial | ].
  thaw FR1. simpl; cancel.
+ (*Case 4: equalDigests_outDataNull *)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. rename H2 into IMDSH.
  rename H3 into cxtszH1. rename H4 into ctxszH2. clear PNd PNmd.
  assert (ctxszH3: Int.eq ctxsz Int.zero=false).
  { remember (Int.eq ctxsz Int.zero) as q. destruct q; trivial.
    apply binop_lemmas2.int_eq_true in Heqq; subst. rewrite Int.unsigned_zero in *. omega. } 
  freeze [2;3;4] FR1.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'1 (Vint Int.zero); 
           temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).  
  { subst; contradiction. }
  { clear H. forward. destruct d; try contradiction. forward. entailer!. }

  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _tmp_buf (Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }

  thaw FR1. forward. forward.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _tmp_buf nullval;
           temp _out octx; temp _in ictx)
    SEP (ERRGV gv; 
         data_at osh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1', nullval))) octx;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { clear H. forward. forward. entailer!. }
  { destruct d; try contradiction. unfold sem_cmp_pp in H; simpl in H.
    rewrite if_true, Ptrofs.eq_true in H; trivial; inv H. }
   
  (*Line 133: cleanup*)
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.

  forward_call (octx, osh, nullval, pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh, d, vals)).
  { Exists ctxsz. 
    assert (FR: Frame = [ERRGV gv;
                         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
                         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx]); subst Frame. reflexivity.
    clear FR. simpl. unfold EVP_MD_NNnode; entailer!. apply orp_right1; trivial. }

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. (*replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).*)

  forward. 
  freeze [0;2] FR1.
  destruct_vals vals cxtszH1. 
  deadvars!.
  unfold EVP_MD_NNnode; Intros. 
  destruct d; simpl in Pd; try contradiction. 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'3 (Vint Int.one); temp _t'20 md; 
           temp _tmp_buf nullval; temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at dsh (Tstruct _env_md_st noattr)
          (type,
          (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))
          (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
  (*{ clear H.
    apply denote_tc_test_eq_split.
     + apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. omega. apply Int.unsigned_range. 
     + apply valid_pointer_null. }*)
  { simpl in *. clear H.
    forward. forward. forward. entailer!. rewrite ctxszH3; trivial. }
  { subst; contradiction. } 
  thaw FR1. 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; 
           temp _tmp_buf nullval; temp _out octx; temp _in ictx)
    SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                 (data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
                  field_at osh (Tstruct _env_md_ctx_st noattr) []
                    (Vptr b i, (m, (Vundef, Vundef))) octx);
         ERRGV gv;  
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
  2: solve [ inv H].
  { clear H H' Pd.
    forward_if (
      PROP ( )
      LOCAL (gvars gv; 
        temp _tmp_buf nullval; temp _out octx; temp _in ictx)
      SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                 (memory_block Ews (Int.unsigned ctxsz)  m *
                   field_at osh (Tstruct _env_md_ctx_st noattr) []
                    (Vptr b i, (m, (Vundef, Vundef))) octx);
           ERRGV gv;  
           data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
           data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
           data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
    { contradiction. }
    { clear H. forward. forward.
      forward_call (Int.unsigned ctxsz).
       + rewrite Int.repr_unsigned; simpl. apply prop_right; trivial.
       + Intros m. forward. forward.
         freeze [1;3;4;5] FR1. focus_SEP 1.
         apply semax_orp_SEPx.
         - Intros; subst m.
           forward_if (PROP (False) LOCAL () SEP ()). 
           * clear H H'.
             forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                gv ___stringlit_1, Vint (Int.repr 142)).
             { unfold ERRGV; cancel. } 
             forward. Exists nullval. thaw FR1; unfold ERRGV; entailer!.
             apply orp_right1. entailer!.
           * inv H. 
           * entailer!. (*intros  unfold overridePost. old_go_lower. clear H.
             destruct (EqDec_exitkind ek EK_normal). entailer!. trivial.*)
         - Intros. assert_PROP (isptr m) as Hm by entailer!.
           destruct m; try contradiction.
           forward_if (
              PROP ( )
              LOCAL (gvars gv; temp _t'17 (Vptr b0 i0); temp _t'2 (Vptr b0 i0);
                     temp _t'19 (Vint ctxsz); temp _t'18 (Vptr b i);
                     temp _t'3 (Vint Int.one); temp _t'20 md; 
                     temp _tmp_buf nullval; temp _out octx; temp _in ictx)
              SEP (ERRGV gv; memory_block Ews (Int.unsigned ctxsz)  (Vptr b0 i0); FRZL FR1)). (*
           { clear H0. apply denote_tc_test_eq_split; try apply valid_pointer_null.
             apply sepcon_valid_pointer1.  
             apply sepcon_valid_pointer1.  
             apply memory_block_valid_ptr. intuition. omega. }*)
           { elim H0; trivial. }
           { forward. entailer!.  }
           entailer!. thaw FR1. Exists  (Vptr b0 i0); entailer!. (*  unfold POSTCONDITION, abbreviate, overridePost; intros.
           destruct (EqDec_exitkind ek EK_normal). 
           * subst; old_go_lower. entailer!. thaw FR1. Exists  (Vptr b0 i0); entailer!.   
           * old_go_lower. clear H0. rewrite ! if_false; trivial. *)}
    Intros m. rename H into M. forward. forward. forward. forward.
    (*memcpy*)
    forward_call ((imdsh,Ews),m, md,Int.unsigned ctxsz, idata).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. split; trivial. apply Int.unsigned_range_2. }
    entailer!. Exists m. entailer!. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'5 nullval; temp _out octx; temp _in ictx)
    SEP (ERRGV gv;
         data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
           (Vptr b i, (m, (Vundef,
              force_val
               (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
                (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
     { contradiction. }
     { forward; entailer!. } 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _out octx; temp _in ictx)
    SEP (ERRGV gv; data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (Vptr b i, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)). 
     { elim H; trivial. }
     { forward; entailer!. }
  forward. Exists (Vint Int.one); entailer!.
  apply orp_right2. Exists m. entailer!.

+ (*Case 5: equalDigests_outDataPtr *)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. rename H2 into IMDSH.
  rename H3 into cxtszH1. rename H4 into ctxszH2. clear PNd PNmd.
  assert (ctxszH3: Int.eq ctxsz Int.zero=false).
  { remember (Int.eq ctxsz Int.zero) as q. destruct q; trivial.
    apply binop_lemmas2.int_eq_true in Heqq; subst. rewrite Int.unsigned_zero in *. omega. } 
  freeze [4] MD'.
  freeze [0;3;4;5] FR1.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'1 (Vint Int.zero); 
           temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).  
  { subst; contradiction. }
  { clear H. forward. destruct d; try contradiction. forward. entailer!.  }

  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _tmp_buf (Vint (Int.repr 0)); 
           temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }

  thaw FR1. forward. forward.
  forward_if 
  (PROP ( )
   LOCAL (gvars gv; temp _tmp_buf md'; temp _out octx; temp _in ictx)
   SEP (ERRGV gv; FRZL MD';
   data_at osh (Tstruct _env_md_ctx_st noattr)
     (d, (nullval, (pv1', nullval))) octx;
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz))
     (map Vint idata) md;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (md, (nullval, pv2))) ictx;
   data_at dsh (Tstruct _env_md_st noattr) vals d)). 
  { clear H. forward. forward. entailer!. }
  { destruct d; try contradiction. unfold sem_cmp_pp in H; simpl in H.
    rewrite if_true, Ptrofs.eq_true in H; trivial; inv H. }
   
  (*Line 133: cleanup*)
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.

  forward_call (octx, osh, nullval, pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh, d, vals)).
  { Exists ctxsz. 
    assert (FR: Frame = [ERRGV gv; FRZL MD'; 
                         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
                         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx]); subst Frame. reflexivity.
    clear FR. simpl. unfold EVP_MD_NNnode; entailer!. apply orp_right1; trivial. }

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. (*replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).*)

  forward. 
  freeze [0;3] FR1.
  destruct_vals vals cxtszH1.
  deadvars!.
  unfold EVP_MD_NNnode; Intros. 
  destruct d; simpl in Pd; try contradiction. 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'3 (Vint Int.one);
           temp _t'20 md; temp _tmp_buf md'; temp _out octx; temp _in ictx)
   SEP (ERRGV gv; FRZL FR1; 
        data_at dsh (Tstruct _env_md_st noattr)
          (type,
          (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))
          (Vptr b i);
       data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
       data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
(*  { clear H.
    apply denote_tc_test_eq_split.
     + apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. omega. apply Int.unsigned_range. 
     + apply valid_pointer_null. }*)
  { simpl in *; subst. clear H.
    forward. forward. forward. entailer!. rewrite ctxszH3; trivial. }
  { subst; contradiction. } 
  thaw FR1. 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _tmp_buf md'; temp _out octx; temp _in ictx)
    SEP (ERRGV gv; data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md';
         field_at osh (Tstruct _env_md_ctx_st noattr) []
                    (Vptr b i, (md', (Vundef, Vundef))) octx;
         data_at dsh (Tstruct _env_md_st noattr) (type,
           (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
  2: solve [inv H].
  { clear H H' Pd.  (* unfold POSTCONDITION, abbreviate; clear POSTCONDITION. *)thaw MD'.
    forward_if ( 
      PROP ( )
      LOCAL (gvars gv; temp _tmp_buf md'; temp _out octx; temp _in ictx)
      SEP (ERRGV gv; memory_block Ews (Int.unsigned ctxsz) md';
           field_at osh (Tstruct _env_md_ctx_st noattr) []
                    (Vptr b i, (md', (Vundef, Vundef))) octx;
           data_at dsh (Tstruct _env_md_st noattr) (type,
               (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
           data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
           data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
(*    { clear H.
      apply denote_tc_test_eq_split; [ | apply valid_pointer_null].
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer2. apply memory_block_valid_ptr. intuition. omega. }*)
    { clear H. forward. entailer!. }
    { subst; contradiction. }
    forward. forward. forward. forward.
    (*memcpy*)
    forward_call ((imdsh,Ews),md', md,Int.unsigned ctxsz, idata).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. split; trivial. apply Int.unsigned_range_2. }
    entailer!. }
  forward. forward. forward.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'5 nullval; temp _out octx; temp _in ictx)
    SEP (ERRGV gv; data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md';
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (Vptr b i, (md', (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
     { contradiction. }
     { forward; entailer!. } 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _out octx; temp _in ictx)
    SEP (ERRGV gv; data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md';
         field_at osh (Tstruct _env_md_ctx_st noattr) []
           (Vptr b i, (md', (Vundef,
              force_val
               (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
                (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)). 
     {  elim H; trivial. }
     { forward; entailer!. }
  forward. unfold POST5. Exists (Vint Int.one); entailer!.

+ (*Case 6: outDigest_Null*)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. rename H2 into IMDSH.
  rename H3 into cxtszH1. rename H4 into ctxszH2. clear PNd PNmd.
  assert (ctxszH3: Int.eq ctxsz Int.zero=false).
  { remember (Int.eq ctxsz Int.zero) as q. destruct q; trivial.
    apply binop_lemmas2.int_eq_true in Heqq; subst. rewrite Int.unsigned_zero in *. omega. }
  freeze [2;3] FR1.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'1 (Vint Int.zero); temp _tmp_buf (Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (ERRGV gv; FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).  
  { subst; contradiction. }
  { clear H. forward. destruct d; try contradiction. forward. entailer!. }

  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _tmp_buf (Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (ERRGV gv; FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }

  thaw FR1. forward. forward. freeze [0;1;2;3] FR1.
  forward_if (
     PROP ( )
     LOCAL (gvars gv; temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
     SEP (FRZL FR1; 
          data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { destruct d; try contradiction; inv H. }
  { clear H. forward. entailer!. }
   
  (*Line 133: cleanup*)
  thaw FR1. focus_SEP 1.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.
  forward_call (octx, osh, md', pv1', 
         @inl unit (share * val * (reptype (Tstruct _env_md_st noattr))) tt).
  { rewrite ! sepcon_assoc. apply sepcon_derives; [ unfold EVP_MD_CTX_NNnode; entailer! | cancel]. }

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. (*replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).*)

  forward.
  destruct_vals vals cxtszH1.
  deadvars!.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'3 (Vint Int.one); temp _tmp_buf (Vint (Int.repr 0)); 
          temp _out octx; temp _in ictx)
    SEP (ERRGV gv;
        field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (Vundef, (Vundef, Vundef))) octx;
        data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
        data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
        data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d)).
 (* { clear H. 
    apply denote_tc_test_eq_split; [ | apply valid_pointer_null]. 
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. omega. apply Int.unsigned_range. }*)
  { clear H.  
    forward. forward. forward. 
    entailer!. rewrite ctxszH3; trivial. }
  { subst; contradiction. } 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _tmp_buf nullval; temp _out octx; temp _in ictx)
    SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                 (data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
                  field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, Vundef))) octx);
         ERRGV gv; 
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d)).
  2: solve [inv H].
  { clear H H'. 
    forward_if (
      PROP ( )
      LOCAL (gvars gv; temp _tmp_buf nullval; temp _out octx; temp _in ictx)
      SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                   (memory_block Ews (Int.unsigned ctxsz)  m *
                    field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, Vundef))) octx);
           ERRGV gv; 
           data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
           data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
           data_at dsh (Tstruct _env_md_st noattr)
             (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d)).
    { contradiction. }
    { clear H. forward. forward.
      forward_call (Int.unsigned ctxsz).
      + rewrite Int.repr_unsigned; entailer!.
      + Intros m. forward. forward. freeze [2;3;4;5] FR1.
        focus_SEP 1.
        apply semax_orp_SEPx; Intros.
        - subst; simpl.
          forward_if (PROP (False) LOCAL () SEP ()); [ | inv H | ].
          * clear H. thaw FR1.
            forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                gv ___stringlit_1, Vint (Int.repr 142)).
            { unfold ERRGV; cancel. }
            forward. Exists nullval. unfold ERRGV; entailer!.
            apply orp_right1. entailer!.  
          * entailer!. (*intros. old_go_lower. clear H. unfold overridePost; simpl; entailer!. if_tac; entailer!. *)
        - rename H into M. 
          rewrite memory_block_isptr; Intros.
          forward_if (
            PROP ( )
            LOCAL (gvars gv; temp _tmp_buf (Vint (Int.repr 0)); 
                   temp _out octx; temp _in ictx)
            SEP (ERRGV gv; memory_block Ews (Int.unsigned ctxsz) m; FRZL FR1)).
          (** clear H.
            apply denote_tc_test_eq_split; [ | apply valid_pointer_null]. 
            apply sepcon_valid_pointer1.
            apply sepcon_valid_pointer1.
            apply memory_block_valid_ptr; intuition; omega. *)
          * destruct m; try contradiction; inv H.
          * clear H. forward. entailer!.  
          * entailer!. thaw FR1. Exists m; entailer!.  (*unfold POSTCONDITION, abbreviate, overridePost; intros.
            destruct (EqDec_exitkind ek EK_normal). 
            ++ subst; old_go_lower. entailer!. thaw FR1. Exists m; entailer!. cancel.
            ++ old_go_lower. clear H. rewrite ! if_false; trivial. *)}
    Intros m. rename H into M. forward. forward. forward. forward.
    (*memcpy*)
    forward_call ((imdsh,Ews),m, md,Int.unsigned ctxsz, idata).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel.  }
         { simpl; split; trivial. split; trivial. apply Int.unsigned_range_2. }
    entailer!. Exists m. entailer!. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'5 nullval; temp _out octx; temp _in ictx)
    SEP (ERRGV gv; data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (d, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)).
     { contradiction. }
     { forward; entailer!. } 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _out octx; temp _in ictx)
    SEP (ERRGV gv; data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
           (d, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)). 
     { elim H; trivial. }
     { forward; entailer!. }
  forward. Exists (Vint Int.one); entailer!. unfold POST6. normalize.
  apply orp_right2; Exists m. entailer!.

+ (*Case 7: distinctDigests*)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. rename H2 into IMDSH.
  rename H3 into cxtszH1. rename H4 into ctxszH2. 
  rename H5 into Hdd'. rename H6 into cxtszH1'. rename H7 into ctxszH2'. clear PNd PNmd PNd'.
  rewrite EVP_MD_NNnode_isptr'; Intros.
  assert (ctxszH3: Int.eq ctxsz Int.zero=false).
  { remember (Int.eq ctxsz Int.zero) as q. destruct q; trivial.
    apply binop_lemmas2.int_eq_true in Heqq; subst. rewrite Int.unsigned_zero in *. omega. }
  freeze [2;5] D'MD'. freeze [0;3;4] FR1.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'1 (Vint Int.zero);
           temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
    SEP (ERRGV gv; FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).  
  { subst; contradiction. }
  { clear H. forward. destruct d; try contradiction. forward. entailer!. }

  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _tmp_buf (Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (ERRGV gv; FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }

  thaw FR1. forward. forward. freeze [0;2;3;4] FR1.
  forward_if (
     PROP ( )
     LOCAL (gvars gv; temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
     SEP (FRZL FR1; FRZL D'MD';
          data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { clear H.
    apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply sepcon_valid_pointer2; entailer! ].
    apply sepcon_valid_pointer2. clear. thaw D'MD'.
    apply sepcon_valid_pointer1; unfold EVP_MD_NNnode. clear; entailer!. }
  { destruct d; destruct d'; try contradiction; unfold typed_true, sem_cmp_pp, Val.of_bool in H; simpl in H.
    rewrite if_false in H; simpl in H; try solve [inv H]. 
    intros N; subst; rewrite if_true in H; trivial; simpl in H.
    rewrite Ptrofs.eq_false in H; try solve [inv H]. }
  { clear H. forward. entailer!. }
   
  (*Line 133: cleanup*)
  thaw FR1. thaw D'MD'. freeze [0;2;3;6] FR1. 
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.
  forward_call (octx, osh, md', pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh', d', vals')).
  { Exists ctxsz'; unfold EVP_MD_CTX_NNnode. entailer!. } 
  thaw FR1.
  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. (* replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).*)

  forward.
  destruct_vals vals cxtszH1.
  deadvars!.
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'3 (Vint Int.one); temp _tmp_buf (Vint (Int.repr 0)); 
           temp _out octx; temp _in ictx)
    SEP (ERRGV gv;
         field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (Vundef, (Vundef, Vundef))) octx;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md; EVP_MD_NNnode dsh' vals' d';
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d)).
(*  { clear H. 
    apply denote_tc_test_eq_split; [ | apply valid_pointer_null]. 
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. omega. apply Int.unsigned_range. }*)
  { clear H.  
    forward. forward. forward. 
    entailer!. rewrite ctxszH3; trivial. }
  { subst; contradiction. } 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _tmp_buf nullval; temp _out octx; temp _in ictx)
    SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                 (data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
                  field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, Vundef))) octx);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         ERRGV gv; EVP_MD_NNnode dsh' vals' d';
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d)).
  2: solve [inv H].
  { clear H. 
    forward_if (
      PROP ( )
      LOCAL (gvars gv; temp _tmp_buf nullval; temp _out octx; temp _in ictx)
      SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                   (memory_block Ews (Int.unsigned ctxsz)  m *
                    field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, Vundef))) octx);
           data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
           ERRGV gv; EVP_MD_NNnode dsh' vals' d';
           data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
           data_at dsh (Tstruct _env_md_st noattr)
             (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d)).
    { contradiction. }
    { clear H H'. forward. forward.
      forward_call (Int.unsigned ctxsz).
      + rewrite Int.repr_unsigned; entailer!.
      + Intros m. forward. forward. freeze [2;3;4;5;6] FR1.
        focus_SEP 1.
        apply semax_orp_SEPx; Intros.
        - subst; simpl.
          forward_if (PROP (False) LOCAL () SEP ()); [ | inv H | ].
          * clear H H'.
            forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                gv ___stringlit_1, Vint (Int.repr 142)).
            { unfold ERRGV; cancel. }
            forward. Exists nullval. unfold ERRGV; entailer!.
            apply orp_right1; thaw FR1; entailer!.
          * entailer!. (* intros. old_go_lower. clear H. unfold overridePost; simpl; entailer!. if_tac; entailer!. *)
        - rename H into M. 
          rewrite memory_block_isptr; Intros.
          forward_if (
            PROP ( )
            LOCAL (gvars gv; temp _tmp_buf (Vint (Int.repr 0)); 
                   temp _out octx; temp _in ictx)
            SEP (ERRGV gv; memory_block Ews (Int.unsigned ctxsz) m; FRZL FR1)).
(*          * clear H.
            apply denote_tc_test_eq_split; [ | apply valid_pointer_null]. 
            apply sepcon_valid_pointer1. 
            apply sepcon_valid_pointer1.
            apply memory_block_valid_ptr; intuition; omega. *)
          * subst m; contradiction.
          * clear H. forward. entailer!.
          * entailer!. Exists m; thaw FR1; entailer!. (*unfold POSTCONDITION, abbreviate, overridePost; intros.
            destruct (EqDec_exitkind ek EK_normal). 
            ++ subst; old_go_lower. entailer!. thaw FR1. Exists m; entailer!. cancel.
            ++ old_go_lower. clear H. rewrite ! if_false; trivial.*) }
    Intros m. rename H into M. forward. forward. forward. forward.
    (*memcpy*)
    forward_call ((imdsh,Ews),m, md,Int.unsigned ctxsz, idata).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. split; trivial. apply Int.unsigned_range_2. }
    entailer!. Exists m. entailer!. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _t'5 nullval; temp _out octx; temp _in ictx)
    SEP (ERRGV gv; data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (d, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         EVP_MD_NNnode dsh' vals' d';
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)).
     { contradiction. }
     { forward; entailer!. } 
  forward_if (
    PROP ( )
    LOCAL (gvars gv; temp _out octx; temp _in ictx)
    SEP (ERRGV gv; data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (d, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         EVP_MD_NNnode dsh' vals' d';
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)). 
     {  elim H; trivial. }
     { forward; entailer!. }
  forward. Exists (Vint Int.one); entailer!. unfold POST7. normalize.
  apply orp_right2; Exists m. entailer!.
Time Qed. (*92s*) 
*)
*)
*)

(*Continue here
Parameter contentmodels (*bytes specdata*): list val ->  EVP_MD_CTX -> Prop.

Definition EVP_MD_data_rep (M:EVP_MD)  (C: EVP_MD_CTX) (p:val): mpred :=
  EX sh: share, EX bytes: list val, 
  !!(writable_share sh /\ contentmodels bytes C /\ 
     forall m, ctx_configured C = Some m -> m=M) && 
  data_at sh (tarray tuchar (EVP_MD_rec_ctx_size XX) bytes p.

Lemma EVP_MD_data_rep_isptrornull M C p: EVP_MD_data_rep M C p |-- !! is_pointer_or_null p.
Proof. unfold EVP_MD_data_rep. Intros sh bytes. entailer!. Qed.
Lemma EVP_MD_data_rep_isptrornull' M C p: EVP_MD_data_rep M C p = (!!(is_pointer_or_null p) && EVP_MD_data_rep M C p).
Proof. apply pred_ext; entailer. apply EVP_MD_data_rep_isptrornull. Qed.

Lemma EVP_MD_data_rep_validptr M C p: EVP_MD_data_rep M C p |-- valid_pointer p.
Proof. unfold EVP_MD_data_rep. Intros sh bytes. entailer. Qed. 

Definition EVP_MD_CTX_rep (M: EVP_MD) (C: EVP_MD_CTX) (vals:reptype (Tstruct _env_md_ctx_st noattr)) :=
match vals with (md, (mddata, _)) => (*TODO:pctx not yet modeled*)
EX r: EVP_MD_record, 
!!(get_md_record M = Some r)
&&
 (EVP_MD_rep r md * EVP_MD_data_rep M C mddata)
end.
(*
Definition EVP_MD_CTX_rep (C: EVP_MD_CTX) (p:val):mpred :=
  EX sh:_, EX vals :_,
  !!readable_share sh &&
  (matchEVP_MD_CTX C vals * data_at sh (Tstruct _env_md_ctx_st noattr) vals p).
*)
(*
Definition EVP_MD_CTX_rep' (C: EVP_MD_CTX) (d p:val):mpred :=
  EX sh:_, EX mddata :val, EX pctx:val*val,
  !!readable_share sh &&
  (EVP_MD_data_rep C mddata * data_at sh (Tstruct _env_md_ctx_st noattr) (d,(mddata,pctx)) p).
*)


(******************************************************************************)

(*Comment: digest.h does not say what happens if digest is not set (ie ctx->digest=null), or indeed
  if the context is not in the right state.
  In contrast, the DigestOperationAccessors are specified to crash in such a case.*)
Definition EVP_DigestUpdate_SPEC := DECLARE _EVP_DigestUpdate
  WITH ctx:val, data:_, len:Z, M: EVP_MD, olddata:list data, bytes:list data, d:val, x:val * (val * val), sh:share
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)), 
        _data OF (tptr tvoid), _len OF tuint ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx; temp _data data; temp _len (Vint (Int.repr len)))
      SEP (EVP_MD_CTX_rep M (EVP_MD_CTX_hashed M olddata) (d, x) ctx;
           data_at sh (tarray tuchar (Z.to_nat len) noattr) bytes data)
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (EVP_MD_CTX_rep M (EVP_MD_CTX_hashed M (olddata++bytes)) (d, x) ctx;
            data_at sh (tarray tuchar (Z.to_nat len) noattr) bytes data).
*)

(* Spec in digest.h: EVP_MD_CTX_cleanup frees any resources owned by |ctx| and resets it to a
                     freshly initialised state. It does not free |ctx| itself. It returns one. 
  Comment: spec doesn't say what happens if ctx==null (our preconditions uses requires NNode)
  Currently, we're not modeling/using pctx, so precondition here requires ctx->pctx==null and 
  ctx->pctx_ops==null*)
(*
Definition EVP_MD_CTX_cleanup_SPEC := 
  let n := sizeof (Tstruct _env_md_ctx_st noattr) 
  in DECLARE _EVP_MD_CTX_cleanup
   WITH ctx:val, C:EVP_MD_CTX, d: val, mdd:val
   PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
       PROP ()
       LOCAL (temp _ctx ctx)
       SEP (EVP_MD_CTX_NNnode C (d, (mdd,(nullval,nullval))) ctx; matchEVP_MD_CTX C (d,(mdd,(nullval,nullval))))
   POST [ tint ]
     EX sh:share,
       PROP (readable_share sh)
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) ctx;
            EVP_MD_rep (digest_of_ctx C) d).


*)