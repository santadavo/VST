Require Export VST.floyd.proofauto.
Require Import boringssl_fips_20180730.digests.
Require Import boringssl_fips_20180730.spec_mem. (*needed (only) for parameters WA and WORD*)
Require Export boringssl_fips_20180730.digest_model.

(*General lemmas, to be moved elsewhere*)
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

(**************************************)


Require Export sha.vst_lemmas. (*for definition of data_block. *)

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition EmptyGprog: funspecs:=nil.

Record MD_with_content :=
  { __EVP_MD : EVP_MD;
    __content : mddataTp __EVP_MD
  }.

Parameter rep: MD_with_content -> list byte -> Prop.

(*The generalization of sha's predicate sha256state_ to other digest functions*)
(*TDOD: replace by
  Definition MD_state (sh:share) (DC: MD_with_content):  val -> mpred :=
  match __EVP_MD DC with
    sha256_md => sha256state_ sh (__content DC)
  | _ => fun p => FF (*TODO: replace by suitable predicates for other digests*)
  end.*)

Definition MD_state (sh:share) (DC: MD_with_content) (v:val): mpred :=
  EX contents: list byte, 
  !!(Zlength contents = (ctx_size_of_MD (__EVP_MD DC)) /\
     rep DC contents) &&
  data_block sh contents v.

Lemma MD_state_memoryblock sh DC p:
      MD_state sh DC p |-- memory_block sh (ctx_size_of_MD (__EVP_MD DC)) p.
Proof. unfold MD_state, data_block; Intros c. rewrite H.
  eapply derives_trans. apply data_at_memory_block.
  specialize (Zlength_nonneg c); intros.
  simpl. rewrite Z.mul_1_l, Z.max_r; trivial; omega.
Qed.

(******* Access functions for reptype (Tstruct _env_md_ctx_st noattr) **)

Definition type_of_ctx (v:reptype (Tstruct _env_md_ctx_st noattr)) :=
  match v with
    (type, (mddata, pv)) => type
  end.
 
Definition mddata_of_ctx (v:reptype (Tstruct _env_md_ctx_st noattr)) :=
  match v with
    (type, (mddata, pv)) => mddata
  end.

Definition pv_of_ctx (v:reptype (Tstruct _env_md_ctx_st noattr)) :=
  match v with
    (type, (mddata, pv)) => pv
  end.

(******* Access functions for reptype (Tstruct _env_md_st noattr) **)

Definition get_type (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => type
  end.
Definition get_mdsize (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => mds
  end.
Definition get_iniptr (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => ini
  end.
Definition get_updptr (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => upd
  end.
Definition get_finptr (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => fin
  end.
Definition get_blsize (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => blsize
  end. 
Definition get_ctxsize (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => ctxsize
  end.


(*** Generalization of SHA256_{Init | Update | Final }_spec, incl wrapping in CTX*)

Definition UpdateSideconditions (DC:MD_with_content) (data:list byte) (len:Z) : Prop :=
  match __EVP_MD DC with
    sha256_md => len <= Zlength data /\ 0 <= len <= Int.max_unsigned
         (*TODO once we link to spec_sha.v: /\ s256a_len a + len * 8 < two_p 64)%Z*)
  | _ => False (*TODO: replace by suitable props for other digests*)
  end.

Definition UPD (DC: MD_with_content) (data:list byte) (len:Z) : MD_with_content:=
  let D := __EVP_MD DC in let cont := __content DC  in
  Build_MD_with_content D (EVP_MD_rec_update _ (EVPMD_record_of_EVPMD D) cont (sublist 0 len data)).

Definition update_spec (D:EVP_MD):funspec :=
  WITH DC:MD_with_content, ctx: val, sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       d: val, dsh:share, data: list byte, len:Z, mdsh:share
  PRE [ 1%positive OF (tptr (Tstruct _env_md_ctx_st noattr)), 
        2%positive OF tptr tvoid, 3%positive OF tuint]
       PROP (readable_share sh; readable_share dsh; writable_share mdsh;
             UpdateSideconditions DC data len; D = __EVP_MD DC)
       LOCAL (temp 1%positive ctx; temp 2%positive d; temp 3%positive (Vint (Int.repr len)) )
       SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
            data_block dsh data d;
            MD_state mdsh DC (mddata_of_ctx CTX))
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              data_block dsh data d;
              MD_state mdsh (UPD DC data len) (mddata_of_ctx CTX)).
(*
Definition postFin sh (n:Z) p: mpred := EX bytes:list byte, 
           !!(0 <= n) && (*data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vubyte Byte.zero)) p*)
                data_at sh (tarray tuchar n) (map Vubyte bytes) p.*)
Definition postFin sh D p: mpred := 
(*  EX c:_, MD_state sh (Build_MD_with_content D c) p.*)
  EX contents: list byte, 
  !!(Zlength contents = (ctx_size_of_MD D)(* /\
     rep DC contents*)) &&
  data_block sh contents p.

Lemma postFin_memory_block sh D p: postFin sh D p |-- memory_block sh (ctx_size_of_MD D) p.
Proof. unfold postFin. Intros bytes.
  eapply derives_trans. apply data_at_memory_block.
  simpl in *. rewrite Z.mul_1_l, Z.max_r, H; trivial.
  apply Zlength_nonneg.
Qed.
 
Lemma postFin_pTN sh D md: postFin sh D md |-- !!(is_pointer_or_null md).
Proof. eapply derives_trans. apply postFin_memory_block. entailer!. Qed.

Definition FinalSideconditions (DC: MD_with_content) (len:Z) : Prop :=
   len = md_size_of_MD (__EVP_MD DC).

Definition FIN (DC: MD_with_content):list data:=
  let D := __EVP_MD DC in let cont := __content DC
  in EVP_MD_rec_final _ (EVPMD_record_of_EVPMD D) cont.

Definition final_spec (D:EVP_MD): funspec :=
  WITH DC:MD_with_content, ctx: val, sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       out: val, osh:share, mdsh:share, len:Z
  PRE [ 1%positive OF tptr (Tstruct _env_md_ctx_st noattr),
        2%positive OF tptr tuchar]
       PROP (readable_share sh; writable_share osh; writable_share mdsh; D = __EVP_MD DC)
       LOCAL (temp 1%positive ctx; temp 2%positive out)
       SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
            MD_state mdsh DC (mddata_of_ctx CTX);
            memory_block osh len out)
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              postFin mdsh (__EVP_MD DC) (mddata_of_ctx CTX);
              data_block osh (FIN DC) out).
(*
Parameter preInit: share -> Z -> val -> mpred.
(*Parameter preInit_fresh: forall sh sz m, 
  memory_block Tsh sz m |--preInit sh sz m. *)(*Presumably, we'll only permit sh==Tsh because of this*)

Parameter preInit_fresh_EWS: forall sz m, 
  memory_block Ews sz m |--preInit Ews sz m.
*)

Definition preInit sh n p: mpred := 
  !!(0 <= n) && data_at_ sh (tarray tuchar n) p.
Lemma preInit_fresh_EWS sz m (H:0 <= sz < Ptrofs.modulus):
  memory_block Ews sz m |--preInit Ews sz m.
Proof. unfold preInit. entailer!. eapply memory_block_data_at__tarray_tuchar; trivial.
Qed.

Lemma postFin_preInit sh D m: postFin sh D m |-- preInit sh (ctx_size_of_MD D) m.
Proof. unfold postFin, preInit, MD_state. Intros c.
  simpl in *. unfold data_block. rewrite H; entailer!. Qed.

Definition INI (D: EVP_MD): MD_with_content :=
  let cont := EVP_MD_rec_init _ (EVPMD_record_of_EVPMD D)
  in Build_MD_with_content D cont.

Definition init_spec (D:EVP_MD):funspec :=
  WITH ctx: val, sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       dsh: share, dvals: reptype (Tstruct _env_md_st noattr), ctxsz:int, mdsh:share
  PRE [ 1%positive OF tptr (Tstruct _env_md_ctx_st noattr)]
          PROP (writable_share sh; readable_share dsh; get_ctxsize dvals = Vint ctxsz;
                4 <= Int.unsigned ctxsz <= Int.max_unsigned)
          LOCAL (temp 1%positive ctx)
          SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
               preInit mdsh (Int.unsigned ctxsz) (mddata_of_ctx CTX);
               data_at dsh (Tstruct _env_md_st noattr) dvals (type_of_ctx CTX))
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              MD_state mdsh (INI D) (mddata_of_ctx CTX);
              data_at dsh (Tstruct _env_md_st noattr) dvals (type_of_ctx CTX)).


(*** Predicate asserting correctness of adminstrative adata in an _env_md_st*)
(*Definition match_EVP_MD (D:EVP_MD) (vals: reptype (Tstruct _env_md_st noattr)):Prop :=
  let R := EVPMD_record_of_EVPMD D in
  match vals with
  ((type, (mdsize, (flags, (ini, (upd, (fin, (blocksize, ctxsize)))))))%type) =>
      type = Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type _ R))) /\
      mdsize = Vint (Int.repr (EVP_MD_rec_md_size _ R)) /\
      flags = Vint (Int.repr (EVP_MD_rec_flags _ R)) /\
      blocksize = Vint (Int.repr (EVP_MD_rec_block_size _ R )) /\
      ctxsize = Vint (Int.repr (EVP_MD_rec_ctx_size _ R))
(*** General representation predicate for _env_md_st*)
Definition EVP_MD_rep (D:EVP_MD) (p:val):mpred :=
  EX sh:_, EX vals :_,
  !!(readable_share sh /\ match_EVP_MD D vals) && 
  (data_at sh (Tstruct _env_md_st noattr) vals p).
  end.
*)

Definition match_EVP_MD (D:EVP_MD) (vals: reptype (Tstruct _env_md_st noattr)): mpred :=
  let R := EVPMD_record_of_EVPMD D in
  match vals with
    ((type, (mdsize, (flags, (ini, (upd, (fin, (blocksize, ctxsize)))))))%type) =>
  !! (type = Vint (Int.repr (NID_of_DigestNID (type_of_MD D))) /\
      mdsize = Vint (Int.repr (md_size_of_MD D)) /\
      flags = Vint (Int.repr (flags_of_MD D)) /\
      blocksize = Vint (Int.repr (block_size_of_MD D)) /\
      ctxsize = Vint (Int.repr (ctx_size_of_MD D)))
   && (func_ptr' (init_spec D) ini *
       func_ptr' (update_spec D) upd *
       func_ptr' (final_spec D) fin)
  end.

Definition EVP_MD_rep (D:EVP_MD) (p:val):mpred :=
  EX sh:_, EX vals :_,
  !!(readable_share sh /\ 4 <= (ctx_size_of_MD D) <= Int.max_unsigned - (WA + WORD) - 8) && match_EVP_MD D vals *
  (data_at sh (Tstruct _env_md_st noattr) vals p).

(**************** Lemmas about these constructions *********************)

Lemma EVP_MD_rep_isptr R p:  EVP_MD_rep R p |-- !!(isptr p).
Proof. unfold EVP_MD_rep. Intros sh vals. entailer!. Qed.

Lemma EVP_MD_rep_isptr' R p:  EVP_MD_rep R p = (!!(isptr p) && EVP_MD_rep R p).
Proof. apply pred_ext; entailer. apply EVP_MD_rep_isptr. Qed. 

Lemma EVP_MD_rep_validptr R p:  EVP_MD_rep R p |-- valid_pointer p.
Proof. unfold EVP_MD_rep. Intros sh vals. entailer!. Qed.

Lemma match_EVP_MD_getctxsize D dvals : match_EVP_MD D dvals |-- !!(get_ctxsize dvals = Vint (Int.repr (ctx_size_of_MD D))).
Proof. unfold match_EVP_MD. destruct dvals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. simpl in *. entailer!. Qed.

Lemma match_EVP_MD_getctxsize' D dvals : match_EVP_MD D dvals =
      (!!(get_ctxsize dvals = Vint (Int.repr (ctx_size_of_MD D))) && match_EVP_MD D dvals).
Proof. apply pred_ext; entailer; apply match_EVP_MD_getctxsize. Qed.