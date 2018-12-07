Require Export VST.floyd.proofauto.

Require Import boringssl_fips_20180730.digests.
Require Import boringssl_fips_20180730.spec_mem. (*needed (only) for parameters WA and WORD*)
Require Export boringssl_fips_20180730.digest_model.
Require Export sha.vst_lemmas. (*for definition of data_block. *)
Require Export boringssl_fips_20180730.vstlib.

(*Concrete states, generalizing the pair (t_struct_SHA256state_st * s256state*)
Variant type_with_content {cs} :=
  twc: forall (t:type), @reptype cs t -> type_with_content.
(*
Record type_with_content {cs} :=
  { __type: type;
    __values: @reptype cs __type
  }.*)

Definition __type {cs} (tc: @type_with_content cs): type := match tc with twc t v => t end.
Definition __values {cs} (tc: @type_with_content cs): @reptype cs (__type tc) := match tc with twc t v => v end.

(*Abstract states, generalzing s256abs*)
Record MD_with_content :=
  { __EVP_MD : EVP_MD;
    __content : mddataTp __EVP_MD
  }.

Parameter HashRelate: forall {cs}, MD_with_content -> @type_with_content cs -> Prop.
(*Parameter t_struct_SHA256state_st: type.
Parameter s256_relate: mddataTp sha256_md -> reptype t_struct_SHA256state_st -> Prop.
Definition HashRelate (DC:MD_with_content) (SWC: type_with_content):Prop.
Proof. destruct DC as [D c].
destruct D.
+ (*md4*) apply False.
+ (*md5*) apply False.
+ (*sha1*) apply False.
+ (*sha224*) apply False.
+ (*sha256*) destruct SWC as [T v]. 
             destruct (type_eq T t_struct_SHA256state_st).
                subst. simpl in *. apply (s256_relate c v).
                apply False.
+ (*sha384*) apply False.
+ (*sha512*) apply False.
+ (*md5_sha1*) apply False.
Defined.*)


Parameter ERR: val -> mpred. 
Definition ERRGV (gv: globals) : mpred :=
ERR (gv ___stringlit_1).

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition EmptyGprog: funspecs:=nil.

(*The generalization of sha's predicate sha256state_ to other digest functions*)
Definition MD_state (sh:share) (DC: MD_with_content) (v:val): mpred :=
  EX tc:type_with_content,
  !! (@sizeof cenv_cs (__type tc) = ctx_size_of_MD (__EVP_MD DC) /\ 
      ctx_size_of_MD (__EVP_MD DC) < Ptrofs.modulus /\ HashRelate DC tc) &&
  data_at sh (__type tc) (__values tc) v.

(*Definition MD_state (sh:share) (DC: MD_with_content) (v:val): mpred :=
  EX tc:type_with_content,
  !! (@sizeof cenv_cs (__type tc) = ctx_size_of_MD (__EVP_MD DC) /\ 
      ctx_size_of_MD (__EVP_MD DC) < Ptrofs.modulus /\ HashRelate DC tc) &&
  data_at sh (__type tc) (__values tc) v.*)

(*
Definition MD_state (sh:share) (DC: MD_with_content) (v:val): mpred :=
  EX contents: list byte, 
  !!(Zlength contents = (ctx_size_of_MD (__EVP_MD DC)) /\
     rep DC contents) &&
  data_block sh contents v.*)

Lemma MD_state_memoryblock sh DC p:
      MD_state sh DC p |-- memory_block sh (ctx_size_of_MD (__EVP_MD DC)) p.
Proof. unfold MD_state, data_block; Intros c; destruct c; Intros. rewrite <- H.
  apply data_at_memory_block.
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

(*Like MD_State, but without the HashRelate clause*)
Definition postFin {cs} sh D p: mpred := 
(*  EX contents: list byte, 
  !!(Zlength contents = (ctx_size_of_MD D)) &&
  data_block sh contents p.*)
  EX tc:type_with_content,
  !! (@sizeof cs (__type tc) = ctx_size_of_MD D /\ ctx_size_of_MD D < Ptrofs.modulus) &&
  data_at sh (__type tc) (__values tc) p.

Lemma MD_StateFIN: forall DC md, MD_state Ews DC md |-- postFin Ews (__EVP_MD DC) md.
Proof. intros. unfold postFin, MD_state. Intros c. Exists c. entailer!.
Qed.

Lemma postFin_memory_block sh D p: postFin sh D p |-- memory_block sh (ctx_size_of_MD D) p.
Proof. unfold postFin. Intros bytes.
  eapply derives_trans. apply data_at_memory_block.
  simpl in *. (*rewrite Z.mul_1_l, Z.max_r, H; trivial.
  apply Zlength_nonneg.*) rewrite <- H; trivial.
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
(*
Lemma postFin_preInit sh D m: postFin sh D m |-- preInit sh (ctx_size_of_MD D) m.
Proof. unfold postFin, preInit, MD_state. Intros c.
  simpl in *. unfold data_block. rewrite H; entailer!.
   Qed.*)
Lemma postFin_preInit sh D m: postFin sh D m |-- preInit sh (ctx_size_of_MD D) m.
Proof. unfold postFin, preInit, MD_state. Intros swc. destruct swc as [t v]. simpl in *.
  rewrite <- H in *; clear H. specialize (sizeof_pos t); intros. simpl in *.
  apply andp_right. apply prop_right; omega. 
  eapply derives_trans. apply data_at_memory_block.
  apply memory_block_data_at__tarray_tuchar; omega.
Qed.

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