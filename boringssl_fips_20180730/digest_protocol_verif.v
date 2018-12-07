Require Import VST.floyd.proofauto.
Require Import boringssl_fips_20180730.spec_mem.
Require Import boringssl_fips_20180730.digest.

Require Export boringssl_fips_20180730.digest_model.
Require Import boringssl_fips_20180730.spec_digest_base.
Require Import boringssl_fips_20180730.spec_digest.
Require Import boringssl_fips_20180730.digest_protocol_spec.
Require Import boringssl_fips_20180730.verif_digest.
Definition ConcGprog: funspecs := EVP_DigestInit_ex_SPEC :: EVP_DigestUpdate_SPEC :: Gprog_EVPMDCTX_1. (*and many more -- all specs from spec_digest*)

Module EVP_MD_CTX_Protocol <: EVP_MD_CTX_Protocol_TP.
Variant State :=
  Allocated: State
| Raw: State
| Empty: forall (D:EVP_MD) (d:val), State
| Hashed: forall (DC: MD_with_content) (d:val), State
| Full: forall (D: EVP_MD) (d:val), State.

Definition MDCTXAllocated p : mpred := 
  OPENSSL_malloc_token 16 p * data_at_ Ews (Tstruct _env_md_ctx_st noattr) p.

Definition MDCTXRaw p : mpred := 
  OPENSSL_malloc_token 16 p * CTX_NULL Ews p.

(*
Definition MD_proper D := sizeof (struct_of_MD D) = EVP_MD_rec_ctx_size D /\ 
                    0 < sizeof (struct_of_MD D) <= Int.max_unsigned.
*)
Definition MDCTXEmpty (D:EVP_MD) (d p:val): mpred :=
  EX md:val, (*!!(MD_proper D) &&*) 
        EVP_MD_CTX_NNnode Ews (d,(md,(nullval,nullval))) p *
        OPENSSL_malloc_token 16 p *
        MD_state Ews (INI D) md * 
        OPENSSL_malloc_token (ctx_size_of_MD D) md.

Definition MDCTXHashed (DC: MD_with_content) (d p:val): mpred :=
  EX md:val, (*!!(MD_proper D)  &&*) 
        EVP_MD_CTX_NNnode Ews (d,(md,(nullval,nullval))) p *
        OPENSSL_malloc_token 16 p *
        MD_state Ews DC md * 
        OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md.

Definition MDCTXFull D d p: mpred := EX md:val,
  EVP_MD_CTX_NNnode Ews (d,(md,(nullval,nullval))) p *
  OPENSSL_malloc_token 16 p *
  postFin Ews D md *
  OPENSSL_malloc_token (ctx_size_of_MD D) md.

Definition MDCTX (s: State): val -> mpred :=
  match s with 
  Allocated => MDCTXAllocated
| Raw => MDCTXRaw
| Empty D d => MDCTXEmpty D d
| Hashed DC d => MDCTXHashed DC d
| Full D d => MDCTXFull D d
  end.

Lemma RawAllocated: forall p, MDCTX Raw p |-- MDCTX Allocated p.
Proof. intros; simpl. unfold MDCTXRaw, MDCTXAllocated, CTX_NULL. cancel. Qed.

Lemma HashedFull: forall DC d p, MDCTX (Hashed DC d) p |-- MDCTX (Full (__EVP_MD DC) d) p.
Proof. intros; simpl. unfold MDCTXHashed, MDCTXFull, EVP_MD_CTX_NNnode.
  Intros md; Exists md. (* sep_apply (MD_StateFIN DC md). entailer!. *)
  destruct DC. simpl. unfold postFin, MD_state. Intros c. Exists c. entailer!. Qed.

Lemma Empty_HashedIni: forall D d p, MDCTX (Empty D d) p |-- MDCTX (Hashed (INI D) d) p.
Proof. intros; simpl. unfold MDCTXHashed, MDCTXEmpty. simpl; trivial. Qed.

Lemma EmptyFull: forall D d p, MDCTX (Empty D d) p |-- MDCTX (Full D d) p.
Proof. intros. sep_apply (Empty_HashedIni D d p). apply HashedFull. Qed.

Definition LEAK (c:State) :mpred :=
  match c with
  Allocated => emp
| Raw => emp
| Empty D d => EX md:_, MD_state Ews (INI D) md * OPENSSL_malloc_token (ctx_size_of_MD D) md
| Hashed DC d => EX md:_, MD_state Ews DC md * OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md
| Full D d => EX md:_, EX data:type_with_content, (*MD_state Ews (Build_MD_with_content D data) md*)
                                  (*data_block Ews data md *)
                                  data_at Ews (__type data) (__values data) md * 
                                  OPENSSL_malloc_token (ctx_size_of_MD D) md
  end.

Lemma AnyAllocated c p: MDCTX c p |-- MDCTX Allocated p * LEAK c.
Proof. unfold LEAK. destruct c; try cancel. apply  RawAllocated.
+ simpl. unfold MDCTXEmpty, MDCTXAllocated, EVP_MD_CTX_NNnode. Intros md. Exists md. cancel.
+ simpl. unfold MDCTXHashed, MDCTXAllocated, EVP_MD_CTX_NNnode. Intros md. Exists md. cancel.
+ simpl. unfold MDCTXFull, MDCTXAllocated, EVP_MD_CTX_NNnode. Intros md. Exists md. cancel.
  unfold postFin. Intros tc. Exists tc. trivial.
Qed.

Lemma Allocated_valid_ptr: forall p, MDCTX Allocated p |-- valid_pointer p.
Proof. intros; simpl. unfold MDCTXAllocated. apply sepcon_valid_pointer2.
  sep_apply (data_at__memory_block Ews (Tstruct _env_md_ctx_st noattr) p); Intros; simpl.
  sep_apply (memory_block_valid_ptr Ews 16 p); intuition. Qed.

Lemma Allocated_isptr: forall p, MDCTX Allocated p |-- !! isptr p.
Proof. intros; simpl. unfold MDCTXAllocated. entailer!. Qed.

Lemma Full_valid_ptr: forall D d p, MDCTX (Full D d) p |-- valid_pointer p.
Proof. intros; simpl. unfold MDCTXFull, EVP_MD_CTX_NNnode; Intros md.
  apply sepcon_valid_pointer1. do 2 apply sepcon_valid_pointer1. 
  sep_apply (data_at__memory_block Ews (Tstruct _env_md_ctx_st noattr) p); Intros; simpl.
  sep_apply (memory_block_valid_ptr Ews 16 p); intuition. Qed.

Lemma Full_isptr: forall D d p, MDCTX (Full D d) p |-- !! isptr p.
Proof. intros; simpl. unfold MDCTXFull, EVP_MD_CTX_NNnode; Intros md. entailer!. Qed.

Definition EVP_of (c: State): mpred :=
  match c with
  Allocated => FF
| Raw => emp
| Empty D d => EVP_MD_rep D d
| Hashed DC d => EVP_MD_rep (__EVP_MD DC) d
| Full D d => EVP_MD_rep D d
  end.

Definition EVP_MD_CTX_init_ASPEC := DECLARE _EVP_MD_CTX_init
   WITH ctx:val
   PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr) ]
       PROP () LOCAL (temp _ctx ctx) SEP (MDCTX Allocated ctx)
   POST [ tvoid ]
       PROP () LOCAL () SEP (MDCTX Raw ctx).

Lemma subsume_EVP_MD_CTX_init:
      subsume_funspec (snd EVP_MD_CTX_init_SPEC) (snd EVP_MD_CTX_init_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros ctx. Exists (ctx, Ews) (OPENSSL_malloc_token 16 ctx).
apply andp_right; auto.
+ old_go_lower; entailer.
+ apply prop_right. simplify_Delta; old_go_lower. entailer.
Qed.

Definition EVP_MD_CTX_copy_ASPEC := DECLARE _EVP_MD_CTX_copy
  WITH gv:globals, octx:val, ictx:val, c:State
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (c <> Allocated; c <> Raw)
      LOCAL (gvars gv; temp _out octx; temp _in ictx)
      SEP (MDCTX c ictx; EVP_of c; MDCTX Allocated octx; mm_inv gv; ERRGV gv)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (if Val.eq rv nullval then MDCTX Raw octx 
            else (!!(rv=Vint Int.one) && MDCTX c octx);
            ERRGV gv; mm_inv gv; MDCTX c ictx; EVP_of c).

Lemma subsume_EVP_MD_CTX_copy:
      subsume_funspec (snd EVP_MD_CTX_copy_SPEC) (snd EVP_MD_CTX_copy_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[gv octx] ictx] c]. specialize WA_WORD_nonneg; intros WAW.
destruct c; Intros.
+ (*Allocated*) congruence.
+ (*Raw*) congruence.
+ (*Empty*) clear H H0.
  replace_SEP 0 (MDCTXEmpty D d ictx) by entailer!.
  unfold MDCTXEmpty; Intros md.
  replace_SEP 5 (MDCTXAllocated octx) by entailer!.
  unfold MDCTXAllocated; Intros.
  unfold EVP_of, EVP_MD_rep; Intros dsh dvals. rename H into Rsh; rename H0 into SZ.
  rewrite data_at_isptr with (p:=d); Intros.
  rewrite match_EVP_MD_getctxsize'; Intros; rename H into CTSZ.
  unfold MD_state, data_block; Intros c. rename H into C. rename H0 into SZmod. rename H1 into HR.
  Exists (gv, octx, ictx, Ews, cp_default Ews d md nullval dsh dvals Ews c (Int.repr (ctx_size_of_MD D)))
         (OPENSSL_malloc_token 16 ictx * OPENSSL_malloc_token (ctx_size_of_MD D) md *
           match_EVP_MD D dvals * OPENSSL_malloc_token 16 octx).
  apply andp_right; auto.
  - old_go_lower. entailer!.
  - apply prop_right. simplify_Delta. Intros rv; Exists rv. old_go_lower.
    Exists dsh dvals.
    Intros; subst. entailer!. rewrite sepcon_comm, distrib_orp_sepcon.
    apply orp_left. 
    * Intros. subst. rewrite if_true by trivial.
      unfold MDCTXEmpty, MDCTXRaw, CTX_NULL, MD_state, EVP_MD_CTX_NNnode; cancel.
      Exists md c. rewrite C; simpl; entailer!.
    * Intros buf; subst. rewrite if_false by discriminate.
      unfold MDCTXEmpty, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode, match_EVP_MD.
      Exists buf md. entailer!. unfold MD_state.
      Exists c c. rewrite C; simpl; entailer!.
+ (*Hashed*) clear H H0.
  replace_SEP 0 (MDCTXHashed DC d ictx) by entailer!.
  unfold MDCTXHashed; Intros md.
  replace_SEP 5 (MDCTXAllocated octx) by entailer!.
  unfold MDCTXAllocated, CTX_NULL; Intros.
  unfold EVP_of, EVP_MD_rep; Intros dsh dvals. rename H into Rsh; rename H0 into SZ.
  rewrite data_at_isptr with (p:=d); Intros.
  rewrite match_EVP_MD_getctxsize'; Intros; rename H into CTSZ.
  unfold MD_state; Intros c; rename H into C. rename H0 into REP.
  Exists (gv, octx, ictx, Ews, cp_default Ews d md nullval dsh dvals Ews c (Int.repr (ctx_size_of_MD (__EVP_MD DC))))
         (OPENSSL_malloc_token 16 ictx * OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md *
           match_EVP_MD (__EVP_MD DC) dvals * OPENSSL_malloc_token 16 octx).
  apply andp_right; auto.
  - old_go_lower. entailer!.
  - apply prop_right. simplify_Delta. Intros rv; Exists rv. old_go_lower.
    Intros; subst. entailer!. rewrite sepcon_comm, distrib_orp_sepcon.
    apply orp_left. 
    * Intros. subst. rewrite if_true by trivial. Exists dsh dvals; entailer!.
      unfold MDCTXHashed, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode.
      Exists md. entailer!. unfold MD_state.
      Exists c. rewrite C; simpl; entailer!.
    * Intros buf; subst. rewrite if_false by discriminate. Exists dsh dvals; entailer!.
      unfold MDCTXHashed, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode.
      Exists buf md. entailer!. unfold MD_state.
      Exists c c. rewrite C; simpl; entailer!.
+ (*Full*) clear H H0.
  replace_SEP 0 (MDCTXFull D d ictx) by entailer!.
  unfold MDCTXFull; Intros md.
  replace_SEP 5 (MDCTXAllocated octx) by entailer!.
  unfold MDCTXAllocated, CTX_NULL; Intros.
  unfold EVP_of, EVP_MD_rep; Intros dsh dvals. rename H into Rsh; rename H0 into SZ.
  rewrite data_at_isptr with (p:=d); Intros.
  rewrite match_EVP_MD_getctxsize'; Intros; rename H into CTSZ.
  unfold MD_state, data_block; Intros.
  unfold postFin, MD_state. Intros finbytes. rename H into C(*; rename H0 into R*).
  Exists (gv, octx, ictx, Ews, cp_default Ews d md nullval dsh dvals Ews finbytes (Int.repr (ctx_size_of_MD D)))
         (OPENSSL_malloc_token 16 ictx * OPENSSL_malloc_token (ctx_size_of_MD D) md *
           match_EVP_MD D dvals * OPENSSL_malloc_token 16 octx).
  apply andp_right; auto.
  - old_go_lower. entailer!.
  - apply prop_right. simplify_Delta. Intros rv; Exists rv. old_go_lower.
    Intros; subst. entailer!. rewrite sepcon_comm, distrib_orp_sepcon.
    apply orp_left. 
    * Intros. subst. rewrite if_true by trivial. Exists dsh dvals; entailer!.
      unfold MDCTXFull, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode.
      Exists md. entailer!. unfold postFin.
      Exists finbytes. rewrite C; simpl; entailer!.
    * Intros buf; subst. rewrite if_false by discriminate. Exists dsh dvals; entailer!.
      unfold MDCTXFull, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode.
      Exists buf md. entailer!. unfold postFin.
      Exists finbytes finbytes. rewrite C; simpl; entailer!.
Time Qed. (*3.5s*)

Definition EVP_MD_CTX_copy_ex_ASPEC := DECLARE _EVP_MD_CTX_copy_ex
  WITH gv:globals, octx:val, ictx:val, c: State
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (c <> Allocated; c <> Raw)
      LOCAL (gvars gv; temp _out octx; temp _in ictx)
      SEP (MDCTX c ictx; EVP_of c; MDCTX Raw octx; mm_inv gv; ERRGV gv)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (if Val.eq rv nullval then MDCTX Raw octx 
            else (!!(rv=Vint Int.one) && MDCTX c octx);
            ERRGV gv; mm_inv gv; MDCTX c ictx; EVP_of c).

Lemma subsume_EVP_MD_CTX_copy_ex:
      subsume_funspec (snd EVP_MD_CTX_copy_ex_SPEC) (snd EVP_MD_CTX_copy_ex_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[gv octx] ictx] c]. specialize WA_WORD_nonneg; intros WAW.
destruct c; Intros.
+ (*Allocated*) congruence.
+ (*Raw*) congruence.
+ (*Empty*) clear H H0.
  replace_SEP 0 (MDCTXEmpty D d ictx) by entailer!.
  unfold MDCTXEmpty; Intros md.
  replace_SEP 5 (MDCTXRaw octx) by entailer!.
  unfold MDCTXRaw, CTX_NULL; Intros.
  unfold EVP_of, EVP_MD_rep; Intros dsh dvals. rename H into Rsh; rename H0 into SZ.
  rewrite data_at_isptr with (p:=d); Intros.
  rewrite match_EVP_MD_getctxsize'; Intros; rename H into CTSZ.
  unfold MD_state, data_block; Intros c. rename H into C. rename H0 into SZmod. rename H1 into HR.
  Exists (gv, octx, ictx, copyEx_other Ews d md nullval nullval dsh dvals Ews nullval nullval nullval
                           (Int.repr (ctx_size_of_MD D)) Ews c None)
          (match_EVP_MD D dvals * OPENSSL_malloc_token 16 ictx * 
           OPENSSL_malloc_token 16 octx * OPENSSL_malloc_token (ctx_size_of_MD D) md).
  apply andp_right; auto.
  - old_go_lower.
    rewrite if_false. 2: destruct d; try contradiction; discriminate.
    entailer!.
  - apply prop_right. simplify_Delta. Intros rv; Exists rv. old_go_lower.
    rewrite if_false. 2: destruct d; try contradiction; discriminate.
    Exists dsh dvals.
    Intros; subst. entailer!. rewrite sepcon_comm, distrib_orp_sepcon.
    apply orp_left. 
    * Intros. subst. rewrite if_true by trivial. cancel. 
      unfold MDCTXEmpty, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode, match_EVP_MD.
      Exists md. entailer!. unfold MD_state.
      Exists c. rewrite C; simpl; entailer!.
    * Intros buf; subst. rewrite if_false by discriminate.
      unfold MDCTXEmpty, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode, match_EVP_MD.
      Exists buf md. entailer!. unfold MD_state.
      Exists c c. rewrite C; simpl; entailer!.
+ (*Hashed*) clear H H0.
  replace_SEP 0 (MDCTXHashed DC d ictx) by entailer!.
  unfold MDCTXHashed; Intros md.
  replace_SEP 5 (MDCTXRaw octx) by entailer!.
  unfold MDCTXRaw, CTX_NULL; Intros.
  unfold EVP_of, EVP_MD_rep; Intros dsh dvals. rename H into Rsh; rename H0 into SZ.
  rewrite data_at_isptr with (p:=d); Intros.
  rewrite match_EVP_MD_getctxsize'; Intros; rename H into CTSZ.
  unfold MD_state, data_block; Intros c. rename H into C.
  Exists (gv, octx, ictx, copyEx_other Ews d md nullval nullval dsh dvals Ews nullval nullval nullval
                           (Int.repr (ctx_size_of_MD (__EVP_MD DC))) Ews c None)
          (match_EVP_MD (__EVP_MD DC) dvals * OPENSSL_malloc_token 16 ictx * 
           OPENSSL_malloc_token 16 octx * OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md).
  apply andp_right; auto.
  - old_go_lower.
    rewrite if_false. 2: destruct d; try contradiction; discriminate.
    entailer!.
  - apply prop_right. simplify_Delta. Intros rv; Exists rv. old_go_lower.
    rewrite if_false. 2: destruct d; try contradiction; discriminate.
    Exists dsh dvals.
    Intros; subst. entailer!. rewrite sepcon_comm, distrib_orp_sepcon.
    apply orp_left. 
    * Intros. subst. rewrite if_true by trivial. cancel.
      unfold MDCTXHashed, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode, match_EVP_MD.
      Exists md. entailer!. unfold MD_state.
      Exists c. rewrite C; simpl; entailer!.
    * Intros buf; subst. rewrite if_false by discriminate.
      unfold MDCTXHashed, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode, match_EVP_MD.
      Exists buf md. entailer!. unfold MD_state.
      Exists c c. rewrite C; simpl; entailer!.
+ (*Full*) clear H H0.
  replace_SEP 0 (MDCTXFull D d ictx) by entailer!.
  unfold MDCTXFull; Intros md.
  replace_SEP 5 (MDCTXRaw octx) by entailer!.
  unfold MDCTXRaw, CTX_NULL; Intros.
  unfold EVP_of, EVP_MD_rep; Intros dsh dvals. rename H into Rsh; rename H0 into SZ.
  rewrite data_at_isptr with (p:=d); Intros.
  rewrite match_EVP_MD_getctxsize'; Intros; rename H into CTSZ.
  unfold MD_state, data_block; Intros.
  unfold postFin, MD_state. Intros finbytes. rename H into C(*; rename H0 into R*).
  Exists (gv, octx, ictx, copyEx_other Ews d md nullval nullval dsh dvals Ews nullval nullval nullval
                           (Int.repr (ctx_size_of_MD D)) Ews finbytes None)
          (match_EVP_MD D dvals * OPENSSL_malloc_token 16 ictx * 
           OPENSSL_malloc_token 16 octx * OPENSSL_malloc_token (ctx_size_of_MD D) md).
  apply andp_right; auto.
  - old_go_lower.
    rewrite if_false. 2: destruct d; try contradiction; discriminate.
    (*rewrite H4; simpl.*) entailer!.
  - apply prop_right. simplify_Delta. Intros rv; Exists rv. old_go_lower.
    rewrite if_false. 2: destruct d; try contradiction; discriminate.
    Exists dsh dvals.
    Intros; subst. entailer!. rewrite sepcon_comm, distrib_orp_sepcon.
    apply orp_left. 
    * Intros. subst. rewrite if_true by trivial. cancel.
      unfold MDCTXFull, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode, match_EVP_MD.
      Exists md. entailer!. unfold postFin, MD_state. Exists finbytes.
      rewrite C; simpl; entailer!.
    * Intros buf; subst. rewrite if_false by discriminate.
      unfold MDCTXFull, MDCTXRaw, CTX_NULL, EVP_MD_CTX_NNnode, match_EVP_MD.
      Exists buf md. entailer!. unfold postFin, MD_state. Exists finbytes finbytes.
      rewrite C; simpl; entailer!. 
Time Qed. (*3.5s*)

Definition EVP_MD_CTX_newcreate_ASPEC :=
   WITH gv:globals
   PRE [ ]
       PROP (24 <= Int.max_unsigned - (WA + WORD))
       LOCAL (gvars gv)
       SEP (mm_inv gv)
   POST [ tptr (Tstruct _env_md_ctx_st noattr) ]
     EX ctx:val,
       PROP ()
       LOCAL (temp ret_temp ctx)
       SEP ((!!(ctx=nullval) && emp) || MDCTX Raw ctx; mm_inv gv).

Definition EVP_MD_CTX_create_ASPEC := DECLARE _EVP_MD_CTX_create EVP_MD_CTX_newcreate_ASPEC.
Definition EVP_MD_CTX_new_ASPEC := DECLARE _EVP_MD_CTX_new EVP_MD_CTX_newcreate_ASPEC.

Definition EVP_DigestUpdate_ASPEC := DECLARE _EVP_DigestUpdate
  WITH ctx: val, t:val, d: val, dsh:share, data: list byte, DC: MD_with_content, len:Z
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), _data OF tptr tvoid,  _len OF tuint ]
      PROP (readable_share dsh; UpdateSideconditions DC data len)
      LOCAL (temp _ctx ctx; temp _data d; temp _len (Vint (Int.repr len)) )
      SEP (MDCTX (Hashed DC t) ctx; data_block dsh data d; EVP_MD_rep (__EVP_MD DC) t)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTX (Hashed (UPD DC data len) t) ctx; data_block dsh data d; EVP_MD_rep (__EVP_MD DC) t).

Definition EVP_MD_CTX_freedestroy_ASPEC :=
  WITH gv:globals, ctx:val, c: State
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (c <> Allocated)
      LOCAL (gvars gv; temp _ctx ctx)
      SEP (MDCTX c ctx; mm_inv gv)
  POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mm_inv gv).

Definition EVP_MD_CTX_free_ASPEC := DECLARE _EVP_MD_CTX_free EVP_MD_CTX_freedestroy_ASPEC.
Definition EVP_MD_CTX_destroy_ASPEC := DECLARE _EVP_MD_CTX_destroy EVP_MD_CTX_freedestroy_ASPEC.

Definition EVP_MD_CTX_cleanupreset_ASPEC :=
  WITH gv:globals, ctx:val, c: State
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (c <> Allocated) LOCAL (gvars gv; temp _ctx ctx)
      SEP (MDCTX c ctx; EVP_of c; mm_inv gv)
  POST [ tint ]
       PROP () LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (MDCTX Raw ctx; EVP_of c; mm_inv gv).

Definition EVP_MD_CTX_cleanup_ASPEC := DECLARE _EVP_MD_CTX_cleanup EVP_MD_CTX_cleanupreset_ASPEC.

(*Note that this is the same spec as cleanup! Indeed the comment in the header file
  suggests that the precondition should be that of cleanup, whereas the fact that
  cleanup results in an initialized (not merely allocated) ctx means that doing
  init again does not change much*)
Definition EVP_MD_CTX_reset_ASPEC := DECLARE _EVP_MD_CTX_reset EVP_MD_CTX_cleanupreset_ASPEC.

Definition EVP_DigestFinal_ex_ASPEC := DECLARE _EVP_DigestFinal_ex
  WITH ctx: val, t:val, 
       out: val, osh:share, sz:val,
       DC:MD_with_content
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md_out OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share osh;
            0 <= ctx_size_of_MD (__EVP_MD DC) <= Int.max_unsigned)
      LOCAL (temp _ctx ctx; temp _md_out out; temp _size sz)
      SEP (MDCTX (Hashed DC t) ctx; EVP_MD_rep (__EVP_MD DC) t;
           if Val.eq sz nullval then emp else data_at_ Ews tuint sz;
           memory_block osh (md_size_of_MD (__EVP_MD DC)) out)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTX (Full (__EVP_MD DC) t) ctx; EVP_MD_rep (__EVP_MD DC) t;
            if Val.eq sz nullval then emp else data_at Ews tuint (Vint (Int.repr (md_size_of_MD (__EVP_MD DC)))) sz;
            data_block osh (FIN DC) out).

Definition EVP_DigestFinal_ASPEC := DECLARE _EVP_DigestFinal
  WITH gv: globals, ctx: val, t:val, 
       out: val, osh:share, sz:val,
       DC:MD_with_content
  PRE [_ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share osh;
            0 <= ctx_size_of_MD (__EVP_MD DC) <= Int.max_unsigned)
      LOCAL (gvars gv; temp _ctx ctx; temp _md out; temp _size sz )
      SEP (MDCTX (Hashed DC t) ctx; EVP_MD_rep (__EVP_MD DC) t;
           if Val.eq sz nullval then emp else data_at_ Ews tuint sz;
           memory_block osh (md_size_of_MD (__EVP_MD DC)) out; mm_inv gv)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTX Raw ctx;
            EVP_MD_rep (__EVP_MD DC) t;
            if Val.eq sz nullval then emp else data_at Ews tuint (Vint (Int.repr (md_size_of_MD (__EVP_MD DC)))) sz;
            data_block osh (FIN DC) out; mm_inv gv).

Definition EVP_DigestInitExPre T t c ctx :=
  match c with
| Allocated => FF
| Raw => MDCTX c ctx * EVP_MD_rep T t
| Empty D d => MDCTX c ctx * EVP_MD_rep T t * if Val.eq d t then !!(D=T) && emp else (!!(D<>T) && EVP_MD_rep D d)
| Hashed DC d => MDCTX c ctx * EVP_MD_rep T t * 
                 let D := __EVP_MD DC in
                 if Val.eq d t then !!(D=T) && emp else (!!(D<>T) && EVP_MD_rep D d)
| Full D d => MDCTX c ctx * EVP_MD_rep T t * if Val.eq d t then !!(D=T) && emp else (!!(D<>T) && EVP_MD_rep D d)
  end.

Definition EVP_DigestInitExPost T t c rv ctx :=
  match c with
  Allocated => FF
| Raw => if Val.eq rv nullval then MDCTX c ctx else
         !!(rv=Vint Int.one) && MDCTX (Empty T t) ctx
| Empty D d => if Val.eq rv nullval 
                 then !!(d<>t) && MDCTX c ctx * EVP_MD_rep D d
                 else (!!(rv=Vint Int.one) && MDCTX (Empty T t) ctx * if Val.eq d t then emp else EVP_MD_rep D d)
| Hashed DC d => if Val.eq rv nullval 
                 then !!(d<>t) && MDCTX c ctx * EVP_MD_rep (__EVP_MD DC) d
                 else (!!(rv=Vint Int.one) && MDCTX (Empty T t) ctx * if Val.eq d t then emp else EVP_MD_rep (__EVP_MD DC) d)
| Full D d => if Val.eq rv nullval 
                 then !!(d<>t) && MDCTX c ctx * EVP_MD_rep D d
                 else (!!(rv=Vint Int.one) && MDCTX (Empty T t) ctx * if Val.eq d t then emp else EVP_MD_rep D d)
  end.

(*Header file specifies that ictx must already be initialized, ie Allocated state is ruled out*)
Definition EVP_DigestInit_ex_ASPEC := DECLARE _EVP_DigestInit_ex
  WITH gv:globals, ctx:val, t:val, e:val, T: EVP_MD, c: State
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (4 <= ctx_size_of_MD T <= Int.max_unsigned - (WA + WORD) - 8; c <> Allocated)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (EVP_DigestInitExPre T t c ctx; ERRGV gv; mm_inv gv)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (EVP_DigestInitExPost T t c rv ctx;ERRGV gv; EVP_MD_rep T t; mm_inv gv).

(*
Definition EVP_DigestInit_ASPEC := DECLARE _EVP_DigestInit
  WITH gv:globals, ctx:val, t:val, T: EVP_MD, c: State
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr) ]
      PROP (4 <= ctx_size_of_MD T <= Int.max_unsigned - (WA + WORD) - 8)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx)
      SEP (MDCTX c ctx; EVP_MD_rep T t; ERRGV gv; mm_inv gv)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (if Val.eq rv nullval  then MDCTX Raw ctx
            else !!(rv=Vint Int.one) && MDCTX (Empty T t) ctx;
            LEAK c; ERRGV gv; EVP_MD_rep T t; mm_inv gv).*)
Definition EVP_DigestInit_ASPEC := DECLARE _EVP_DigestInit
  WITH gv:globals, ctx:val, t:val, T: EVP_MD
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr) ]
      PROP (4 <= ctx_size_of_MD T <= Int.max_unsigned - (WA + WORD) - 8)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx)
      SEP (MDCTX Allocated ctx; EVP_MD_rep T t; ERRGV gv; mm_inv gv)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (if Val.eq rv nullval then MDCTX Raw ctx
            else !!(rv=Vint Int.one) && MDCTX (Empty T t) ctx;
            ERRGV gv; EVP_MD_rep T t; mm_inv gv).

Lemma subsume_EVP_MD_CTX_cleanupreset:
      subsume_funspec EVP_MD_CTX_cleanupreset_SPEC EVP_MD_CTX_cleanupreset_ASPEC.
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[gv ctx] c]. destruct c.
+ (*Allocated*) Intros; congruence.
+ (*Raw*) Intros; clear H.
  Exists (gv, ctx, Ews, nullval, @None Z) (OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. unfold MDCTXRaw, CTX_NULL. entailer!.
    Exists nullval nullval. entailer!. 
  - apply prop_right. simplify_Delta. old_go_lower; unfold MDCTXRaw, CTX_NULL; entailer!.
+ (*Empty*) Intros; clear H.
  replace_SEP 0 (MDCTXEmpty D d ctx) by entailer!.
  unfold MDCTXEmpty; Intros md.
  Exists (gv, ctx, Ews, md, Some (ctx_size_of_MD D)) (EVP_MD_rep D d * OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. Exists d nullval. entailer!. apply MD_state_memoryblock.
  - apply prop_right. simplify_Delta. old_go_lower; unfold MDCTXRaw; entailer!.
+ (*Hashed*) Intros; clear H.
  replace_SEP 0 (MDCTXHashed DC d ctx) by entailer!.
  unfold MDCTXHashed; Intros md. destruct DC as [D data].
  Exists (gv, ctx, Ews, md, Some (ctx_size_of_MD D)) (EVP_MD_rep D d * OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. Exists d nullval. entailer!. apply MD_state_memoryblock.
  - apply prop_right. simplify_Delta. old_go_lower; unfold MDCTXRaw; entailer!.
+ (*Full*) Intros; clear H.
  replace_SEP 0 (MDCTXFull D d ctx) by entailer!.
  unfold MDCTXFull; Intros md.
  Exists (gv, ctx, Ews, md, Some (ctx_size_of_MD D)) (EVP_MD_rep D d * OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. Exists d nullval. entailer!. apply postFin_memory_block. (*apply MD_state_memoryblock.*)
  - apply prop_right. simplify_Delta. old_go_lower; unfold MDCTXRaw; entailer!.
Qed.

Lemma subsume_EVP_MD_CTX_newcreate:
      subsume_funspec EVP_MD_CTX_newcreate_SPEC EVP_MD_CTX_newcreate_ASPEC.
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros gv. Exists gv emp.
change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
apply andp_right; auto.
+ entailer!. 
+ apply prop_right. simplify_Delta. Intros ctx. Exists ctx. entailer.
Qed.

(*Identical proof to subsume_EVP_MD_CTX_new*)
Lemma subsume_EVP_MD_CTX_create:
      subsume_funspec (snd EVP_MD_CTX_create_SPEC) (snd EVP_MD_CTX_create_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros gv. Exists gv emp.
change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
apply andp_right; auto.
+ entailer!. 
+ apply prop_right. simplify_Delta. Intros ctx. Exists ctx. entailer.
Qed.

Lemma subsume_EVP_DigestUpdate:
      subsume_funspec (snd EVP_DigestUpdate_SPEC) (snd EVP_DigestUpdate_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[[[ctx t] d] dsh] data] DC] len]. 
rewrite EVP_MD_rep_isptr'; Intros. rename H into Rdsh. rename H0 into SC.
replace_SEP 0 (MDCTXHashed DC t ctx) by entailer!.
unfold MDCTXHashed, EVP_MD_CTX_NNnode; Intros md.
Exists (ctx, Ews, (t, (md, (nullval, nullval))), d, dsh, data, DC, len, Ews)
       (OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md * OPENSSL_malloc_token 16 ctx).
apply andp_right.
+ old_go_lower; entailer!.
+ apply prop_right. simplify_Delta. old_go_lower; entailer.
  unfold MDCTXHashed, EVP_MD_CTX_NNnode; simpl.
  Exists md. entailer!.
Qed.

Lemma subsume_EVP_MD_CTX_freedestroy:
      subsume_funspec EVP_MD_CTX_freedestroy_SPEC EVP_MD_CTX_freedestroy_ASPEC.
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[gv ctx] c]. destruct c.
+ (*Allocated*) Intros; congruence.
+ (*Raw*) Intros; clear H. 
  replace_SEP 0 (MDCTXRaw ctx) by entailer!.
  Exists (gv, ctx, nullval, nullval, nullval, @None Z) emp.
  change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
  apply andp_right; auto.
  - entailer!. apply orp_right2. unfold MDCTXRaw, CTX_NULL; entailer!.
  - entailer!.
+ (*Empty*) Intros; clear H.
  replace_SEP 0 (MDCTXEmpty D d ctx) by entailer!.
  unfold MDCTXEmpty. Intros md.
  Exists (gv, ctx, d, md, nullval, Some (ctx_size_of_MD D)) emp.
  change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
  apply andp_right; auto.
  - entailer!. apply orp_right2. entailer!. apply MD_state_memoryblock. 
  - apply prop_right. simplify_Delta. entailer!. 
+ (*Hashed*) Intros; clear H. 
  replace_SEP 0 (MDCTXHashed DC d ctx) by entailer!.
  unfold MDCTXHashed. Intros md.
  Exists (gv, ctx, d, md, nullval, Some (ctx_size_of_MD (__EVP_MD DC))) emp.
  change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
  apply andp_right; auto.
  - Time entailer!. simpl in *. apply orp_right2. entailer!. apply MD_state_memoryblock.
  - apply prop_right. simplify_Delta. entailer!. 
+ (*Full*) Intros; clear H. 
  replace_SEP 0 (MDCTXFull D d ctx) by entailer!.
  unfold MDCTXFull. Intros md.
  Exists (gv, ctx, d, md, nullval, Some (ctx_size_of_MD D)) emp.
  change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
  apply andp_right; auto. 
  - go_lower; simpl in *. cancel. apply andp_right. apply prop_right; intuition.
    cancel. apply orp_right2. cancel. apply postFin_memory_block.
  - apply prop_right. simplify_Delta. entailer!. 
Qed.

Lemma subsume_EVP_DigestFinal_ex:
      subsume_funspec (snd EVP_DigestFinal_ex_SPEC) (snd EVP_DigestFinal_ex_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[[ctx t] out] osh] sz] DC].
rewrite EVP_MD_rep_isptr'; Intros. rename H into Wosh. rename H0 into SZ.
replace_SEP 0 (MDCTXHashed DC t ctx) by entailer!.
unfold MDCTXHashed, EVP_MD_CTX_NNnode; Intros md.
Exists (ctx, Ews, (t, (md, (nullval, nullval))), out, osh, sz, DC, Ews)
       (OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md * OPENSSL_malloc_token 16 ctx).
apply andp_right.
+ old_go_lower; entailer!.
+ apply prop_right. simplify_Delta. old_go_lower. Time entailer!.
  Exists md. cancel. apply sepcon_derives; [unfold EVP_MD_CTX_NNnode; entailer! | apply derives_refl].
Qed.

Lemma subsume_EVP_DigestFinal:
      subsume_funspec (snd EVP_DigestFinal_SPEC) (snd EVP_DigestFinal_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[[[gv ctx] t] out] osh] sz] DC].
rewrite EVP_MD_rep_isptr'; Intros. rename H into Wosh. rename H0 into SZ.
replace_SEP 0 (MDCTXHashed DC t ctx) by entailer!.
unfold MDCTXHashed, EVP_MD_CTX_NNnode; Intros md.
Exists (gv, ctx, Ews, (t, (md, (nullval, nullval))), out, osh, sz, DC)
       (OPENSSL_malloc_token 16 ctx).
apply andp_right.
+ old_go_lower; entailer!.
+ apply prop_right. simplify_Delta. old_go_lower; entailer!.
  unfold MDCTXRaw; cancel. 
Qed.

Lemma subsume_EVP_DigestInit_ex:
      subsume_funspec (snd EVP_DigestInit_ex_SPEC) (snd EVP_DigestInit_ex_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[[gv ctx] t] e] T] c]. rewrite EVP_MD_rep_isptr'; Intros. rename H into SCT.
specialize WA_WORD_nonneg; intros WAW. 
destruct c; [ congruence | | | |]; clear H0.
+ (*Raw*)
  replace_SEP 0 (MDCTXRaw ctx * EVP_MD_rep T t) by entailer!.
  unfold MDCTXRaw.
  rewrite OPENSSL_malloc_token_compatible', EVP_MD_rep_isptr'; Intros.
  Exists (ctx, t, e, nullval, nullval, (nullval, nullval), T, gv, Ews, DIEC_NEQ None None)
         (OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. entailer!.
    unfold CTX_NULL; cancel.
  - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred.
    old_go_lower; entailer; cancel.
    rewrite sepcon_comm, distrib_orp_sepcon. apply orp_left.
    * Intros; subst. rewrite if_true; trivial. unfold MDCTXRaw, CTX_NULL; cancel.
    * Intros m; subst; rewrite if_false by discriminate.
      rewrite OPENSSL_malloc_token_compatible'; Intros.
      entailer!. unfold MDCTXEmpty, EVP_MD_CTX_NNnode.
      Exists m; entailer!.
+ (*Empty*)
  replace_SEP 0 (MDCTXEmpty D d ctx * EVP_MD_rep T t *
      (if Val.eq d t then !! (D = T) && emp else !! (D <> T) && EVP_MD_rep D d)) by entailer!.
  unfold MDCTXEmpty. Intros m.
  rewrite OPENSSL_malloc_token_compatible' with (v:=m), EVP_MD_rep_isptr' with (p:=t); Intros.
  rename H0 into SZD; rename H into MCm.
  destruct (Val.eq d t); Intros; subst.
  * (*d=t, D=T*)
    Exists (ctx, t, e, t, m, (nullval, nullval), T, gv, Ews, DIEC_EQ)
           (OPENSSL_malloc_token 16 ctx * mm_inv gv * OPENSSL_malloc_token (ctx_size_of_MD T) m).
    apply andp_right; auto.
    - old_go_lower. entailer. cancel. 
      eapply derives_trans. apply MD_state_memoryblock. simpl. apply preInit_fresh_EWS; rep_omega.
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred.
      old_go_lower; entailer!. rewrite if_false by discriminate. rewrite if_true by trivial.
      unfold MDCTXEmpty. Exists m. entailer!. 
      unfold EVP_MD_CTX_NNnode. entailer!.
  * (*d<>t, D<>T*)
    rewrite EVP_MD_rep_isptr' with (p:=d); Intros.
    unfold EVP_MD_rep at 2. Intros dsh dvals.
    unfold MD_state. Intros bytes. 
    Exists (ctx, t, e, d, m, (nullval, nullval), T, gv, Ews, DIEC_NEQ (Some (dsh,dvals)) 
            (Some (*(INI D)*)(D, bytes)))
           (OPENSSL_malloc_token 16 ctx * match_EVP_MD D dvals).
    apply andp_right; auto.
    - old_go_lower. entailer. cancel. unfold EVP_MD_NNnode. entailer!. 
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred.
      old_go_lower; simpl; entailer!. 
      rewrite sepcon_assoc. rewrite sepcon_comm, ! distrib_orp_sepcon. apply orp_left.
      { Intros; subst. rewrite if_true by trivial. 
        unfold MDCTXEmpty, EVP_MD_CTX_NNnode. Exists m; entailer. cancel.
        unfold EVP_MD_rep, EVP_MD_NNnode. Exists dsh dvals. entailer!.
         unfold MD_state. Exists bytes. rewrite H2; simpl; entailer!. }
      { Intros md; subst. rewrite if_false by discriminate.
        rewrite OPENSSL_malloc_token_compatible' with (v:=md).
        unfold MDCTXEmpty, EVP_MD_CTX_NNnode. Exists md; entailer. cancel.
        rewrite if_false by trivial.
        unfold EVP_MD_rep, EVP_MD_NNnode. Exists dsh dvals. entailer!.  }
+ (*Hashed*)
  replace_SEP 0 (MDCTXHashed DC d ctx * EVP_MD_rep T t *
      (if Val.eq d t then !! (__EVP_MD DC = T) && emp else !! (__EVP_MD DC <> T) && EVP_MD_rep (__EVP_MD DC) d)) by entailer!.
  unfold MDCTXHashed. Intros m.
  rewrite OPENSSL_malloc_token_compatible' with (v:=m), EVP_MD_rep_isptr' with (p:=t); Intros.
  rename H0 into SZD; rename H into MCm.
  destruct (Val.eq d t); Intros; subst.
  * (*d=t, D=T*)
    Exists (ctx, t, e, t, m, (nullval, nullval), __EVP_MD DC, gv, Ews, DIEC_EQ)
           (OPENSSL_malloc_token 16 ctx * mm_inv gv * OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) m).
    apply andp_right; auto.
    - old_go_lower. entailer. cancel.
      eapply derives_trans. apply MD_state_memoryblock. simpl. apply preInit_fresh_EWS; rep_omega.
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred.
      old_go_lower; entailer!. rewrite if_false by discriminate. rewrite if_true by trivial.
      unfold MDCTXEmpty. Exists m. entailer!. 
      unfold EVP_MD_CTX_NNnode. entailer!.
  * (*d<>t, D<>T*)
    rewrite EVP_MD_rep_isptr' with (p:=d); Intros.
    unfold EVP_MD_rep at 2. Intros dsh dvals.
    unfold MD_state; Intros bytes.
    Exists (ctx, t, e, d, m, (nullval, nullval), T, gv, Ews, 
            DIEC_NEQ (Some (dsh,dvals)) (Some (__EVP_MD DC,bytes)))
           (OPENSSL_malloc_token 16 ctx * match_EVP_MD (__EVP_MD DC) dvals).
    apply andp_right; auto.
    - old_go_lower. entailer. cancel. unfold EVP_MD_NNnode. entailer!.
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred.
      old_go_lower; simpl; entailer!. 
      rewrite sepcon_assoc. rewrite sepcon_comm, ! distrib_orp_sepcon. apply orp_left.
      { Intros; subst. rewrite if_true by trivial. 
        unfold MDCTXHashed, EVP_MD_CTX_NNnode. Exists m; entailer. cancel.
        unfold EVP_MD_rep, EVP_MD_NNnode. Exists dsh dvals. entailer!.
        unfold MD_state, data_block. Exists bytes. rewrite H2; simpl; entailer!. }
      { Intros md; subst. rewrite if_false by discriminate.
        rewrite OPENSSL_malloc_token_compatible' with (v:=md).
        unfold MDCTXEmpty, EVP_MD_CTX_NNnode. Exists md; entailer. cancel.
        rewrite if_false by trivial.
        unfold EVP_MD_rep, EVP_MD_NNnode. Exists dsh dvals. entailer!. }
+ (*Full*)
  replace_SEP 0 (MDCTXFull D d ctx * EVP_MD_rep T t *
      (if Val.eq d t then !! (D = T) && emp else !! (D <> T) && EVP_MD_rep D d)) by entailer!.
  unfold MDCTXFull. Intros m.
  rewrite OPENSSL_malloc_token_compatible' with (v:=m), EVP_MD_rep_isptr' with (p:=t); Intros.
  rename H0 into SZD; rename H into MCm.
  unfold postFin; Intros findata.
(*  rewrite (PF D m).*)
  destruct (Val.eq d t); Intros; subst.
  * (*d=t, D=T*)
    Exists (ctx, t, e, t, m, (nullval, nullval), T, gv, Ews, DIEC_EQ)
           (OPENSSL_malloc_token 16 ctx * mm_inv gv * OPENSSL_malloc_token (ctx_size_of_MD T) m).
    apply andp_right; auto.
    - old_go_lower. entailer. cancel. unfold preInit. rewrite <- H; entailer!.
       sep_apply (data_at_memory_block Ews (__type findata) (__values findata) m).
       rewrite memory_block_data_at__tarray_tuchar_eq; trivial. omega. 
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred.
      old_go_lower; entailer!. rewrite if_false by discriminate. rewrite if_true by trivial.
      unfold MDCTXEmpty. Exists m. entailer!. 
      unfold EVP_MD_CTX_NNnode. entailer!.
  * (*d<>t, D<>T*)
    rewrite EVP_MD_rep_isptr' with (p:=d); Intros.
    unfold EVP_MD_rep at 2. Intros dsh dvals.
    Exists (ctx, t, e, d, m, (nullval, nullval), T, gv, Ews, 
            DIEC_NEQ (Some (dsh,dvals)) (Some (D, findata) (*({| __EVP_MD := D; __content := findata |})*)))
           (OPENSSL_malloc_token 16 ctx * match_EVP_MD D dvals).
    apply andp_right; auto.
    - old_go_lower. entailer. cancel. unfold EVP_MD_NNnode. entailer!.
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred.
      old_go_lower; simpl; entailer!.
      rewrite sepcon_assoc. rewrite sepcon_comm, ! distrib_orp_sepcon. apply orp_left.
      { Intros; subst. rewrite if_true by trivial. 
        unfold MDCTXFull, EVP_MD_CTX_NNnode. Exists m; entailer. cancel.
        unfold EVP_MD_rep, EVP_MD_NNnode. Exists dsh dvals. entailer!.
        unfold postFin, data_block. Exists findata; rewrite H; simpl. entailer!. }
      { Intros md; subst. rewrite if_false by discriminate.
        rewrite OPENSSL_malloc_token_compatible' with (v:=md).
        unfold MDCTXEmpty, EVP_MD_CTX_NNnode. Exists md; entailer. cancel.
        rewrite if_false by trivial.
        unfold EVP_MD_rep, EVP_MD_NNnode. Exists dsh dvals. entailer!. }
Time Qed. (*22s*)

Lemma subsume_EVP_DigestInit:
      subsume_funspec (snd EVP_DigestInit_SPEC) (snd EVP_DigestInit_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[gv ctx] t] T]. rewrite EVP_MD_rep_isptr'; Intros. rename H into SCT.
  replace_SEP 0 (MDCTXAllocated ctx) by entailer!.
  unfold MDCTXAllocated; Intros.
  Exists (ctx, t, T, gv, Ews) (OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. entailer!.
  - apply prop_right. Intros rv. Exists rv. simplify_Delta. 
    old_go_lower. Intros; subst. apply andp_right. apply prop_right; intuition. cancel.
    unfold DIE_postMpred; simpl.
    rewrite sepcon_comm, distrib_orp_sepcon. apply orp_left.
    * Intros; subst. rewrite if_true by trivial. unfold MDCTXRaw, CTX_NULL. cancel.
    * Intros m; subst. rewrite if_false by discriminate.
      rewrite OPENSSL_malloc_token_compatible' with (v:=m); Intros. 
      apply andp_right. apply prop_right; trivial.
      Exists m. cancel.  unfold EVP_MD_CTX_NNnode. entailer!.
Qed. (*
Lemma subsume_EVP_DigestInit:
      subsume_funspec (snd EVP_DigestInit_SPEC) (snd EVP_DigestInit_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[gv ctx] t] T] c]. rewrite EVP_MD_rep_isptr'; Intros. rename H into SCT.
destruct c.
+ (*Allocated*)
  replace_SEP 0 (MDCTXAllocated ctx) by entailer!. 
  unfold MDCTXAllocated; Intros.
  Exists (ctx, t, T, gv, Ews) (OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. entailer!.
  - apply prop_right. Intros rv. Exists rv. simplify_Delta. 
    old_go_lower. Intros; subst. apply andp_right. apply prop_right; intuition. cancel.
    unfold DIE_postMpred; simpl.
    rewrite sepcon_comm, distrib_orp_sepcon. apply orp_left.
    * Intros; subst. rewrite if_true by trivial. unfold MDCTXRaw, CTX_NULL. cancel.
    * Intros m; subst. rewrite if_false by discriminate.
      rewrite OPENSSL_malloc_token_compatible' with (v:=m); Intros. 
      apply andp_right. apply prop_right; trivial.
      Exists m. cancel.  unfold EVP_MD_CTX_NNnode. entailer!.
+ (*Raw*) 
  replace_SEP 0 (MDCTXRaw ctx) by entailer!. 
  unfold MDCTXRaw, CTX_NULL; Intros.
  Exists (ctx, t, T, gv, Ews) (OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. entailer!.
  - apply prop_right. Intros rv. Exists rv. simplify_Delta.
    old_go_lower. entailer!.
    unfold DIE_postMpred; simpl. 
    rewrite sepcon_comm, distrib_orp_sepcon. apply orp_left.
    * Intros; subst. rewrite if_true by trivial. unfold MDCTXRaw, CTX_NULL. cancel.
    * Intros m; subst. rewrite if_false by discriminate. entailer!.
      rewrite OPENSSL_malloc_token_compatible' with (v:=m); Intros.
      Exists m. cancel. unfold EVP_MD_CTX_NNnode; entailer!.
+ (*Empty*) 
  replace_SEP 0 (MDCTXEmpty D d ctx) by entailer!. 
  unfold MDCTXEmpty; Intros md.
  Exists (ctx, t, T, gv, Ews) (OPENSSL_malloc_token 16 ctx * MD_state Ews (INI D) md * OPENSSL_malloc_token (ctx_size_of_MD D) md).
  apply andp_right; auto.
  - old_go_lower. Intros. cancel. subst. apply andp_right. apply prop_right; intuition. cancel.
  - apply prop_right. Intros rv. Exists rv. simplify_Delta.
    old_go_lower. entailer!. 
    Exists md. cancel. unfold DIE_postMpred; simpl.
    rewrite sepcon_comm, distrib_orp_sepcon. apply orp_left.
    * Intros; subst. rewrite if_true by trivial.
      unfold MDCTXRaw, CTX_NULL. entailer!.
    * Intros m; subst. rewrite if_false by discriminate. entailer!.
      rewrite OPENSSL_malloc_token_compatible' with (v:=m); Intros.
      Exists m. cancel. unfold EVP_MD_CTX_NNnode; entailer!.
+ (*Hashed*) 
  replace_SEP 0 (MDCTXHashed DC d ctx) by entailer!. 
  unfold MDCTXHashed; Intros md.
  Exists (ctx, t, T, gv, Ews) (OPENSSL_malloc_token 16 ctx * MD_state Ews DC md * OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md).
  apply andp_right; auto.
  - old_go_lower. Intros. apply andp_right. apply prop_right; intuition. cancel.
  - apply prop_right. Intros rv. Exists rv. simplify_Delta. 
    old_go_lower. simpl; Intros. apply andp_right. apply prop_right; intuition. 
    cancel. unfold DIE_postMpred. simpl.
    rewrite sepcon_comm, distrib_orp_sepcon. apply orp_left.
    * Intros; subst. rewrite if_true by trivial.
      Exists md; unfold MDCTXRaw, CTX_NULL. cancel.
    * Exists md. cancel. subst _id. Intros m; subst. rewrite if_false by discriminate.
      apply andp_right. apply prop_right; trivial.
      rewrite OPENSSL_malloc_token_compatible' with (v:=m); Intros.
      unfold MDCTXEmpty, EVP_MD_CTX_NNnode.
      Exists m. cancel. entailer!.
+ (*Full*) 
  replace_SEP 0 (MDCTXFull D d ctx) by entailer!. 
  unfold MDCTXFull; Intros md.
  unfold postFin; Intros findata.
  Exists (ctx, t, T, gv, Ews) 
         (OPENSSL_malloc_token 16 ctx * 
          data_at Ews (__type findata) (__values findata) md * 
          OPENSSL_malloc_token (ctx_size_of_MD D) md).
  apply andp_right; auto.
  - old_go_lower. Intros. apply andp_right. apply prop_right; intuition. cancel.
  - apply prop_right. Intros rv. Exists rv. simplify_Delta.
    old_go_lower; entailer; cancel. Exists md.
    entailer!. Exists findata. cancel. unfold DIE_postMpred. simpl. 
    rewrite sepcon_comm, distrib_orp_sepcon. apply orp_left.
    * Intros; subst. rewrite if_true by trivial. cancel.
      unfold MDCTXRaw, CTX_NULL. cancel. 
    * Intros m; subst. rewrite if_false by discriminate.
      rewrite OPENSSL_malloc_token_compatible' with (v:=m); Intros.
      apply andp_right. apply prop_right; intuition.
      Exists m. cancel. unfold EVP_MD_CTX_NNnode; entailer!.
Qed.*)

End EVP_MD_CTX_Protocol.
(*
(*TODO (discuss): we don't have a entailment converting configured (and hence hashed or finished) 
contexts into initialized (and hence allocated) contexts, fnullval: r two reasons:
a) it would leak the md memory region in the postcondition
b) configured requires d, md to me pointer_or_null. Initialized requires them to be null.
Thus, users are forced to use EVM_MD_CTX_cleanup to perform this conversion
*)
(*
Definition MDCTXHashed D (data:list Z) (d p:val): mpred :=
  EX md:val, EX v: reptype (struct_of_MD D),
       !!(MD_proper D /\ DigestRep (struct_of_MD D) v data)
       && EVP_MD_CTX_NNnode Tsh (d,(md,(nullval,nullval))) p *
             data_at Tsh (struct_of_MD D) v md.*)
(*Definition MDCTXHashed sh mdsh (DC: MD_with_content) (d p:val): mpred :=
  EX md:val, (*!!(MD_proper D) &&*) 
     !!(readable_share sh /\ writable_share mdsh) 
     && EVP_MD_CTX_NNnode sh (d,(md,(nullval,nullval))) p *
        OPENSSL_malloc_token 16 p *
        MD_state mdsh DC md * OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md.*)

Variant ConfHashedFinished D:=
  Configured: ConfHashedFinished D
| Hashed: (mddataTp D) -> ConfHashedFinished D
| Finished: (mddataTp D) -> ConfHashedFinished D.

Variant EVP_DigestInit_ex_case:=
  DIEx_CaseINI: EVP_DigestInit_ex_case (*ctx has been initialized but not been configured*)
| DIEx_CaseSameMD: EVP_DigestInit_ex_case (*ctx presently configured to same MD we want to initialize to*)
| DIEx_CaseDiffMD: forall (D:EVP_MD) (d:val) (p:ConfHashedFinished D), EVP_DigestInit_ex_case. (*ctx presently configured to MD D at d
            and these are different from what we want*)

Definition ConfHashedFinishedMpred D d p ctx :=
           match p with
           | Configured => MDCTXConfigured D d ctx
           | Hashed data => MDCTXHashed (Build_MD_with_content D data) d ctx
           | Finished data => MDCTXFinished (Build_MD_with_content D data) d ctx
           end.

Definition EVP_DigestInitExPre T t (c:EVP_DigestInit_ex_case) ctx :=
  match c with 
  DIEx_CaseINI => MDCTXInitialized ctx
| DIEx_CaseSameMD => MDCTXConfigured T t ctx || EX data:_, MDCTXFinished (Build_MD_with_content T data) t ctx
| DIEx_CaseDiffMD D d p => 
       !!(d<>t /\ D<>T) && ConfHashedFinishedMpred D d p ctx * EVP_MD_rep D d  
  end.

Definition EVP_DigestInitExPost T t (c:EVP_DigestInit_ex_case) rv ctx :=
  match c with 
  DIEx_CaseINI => (!!(rv= nullval) && MDCTXInitialized ctx)
               || (!!(rv= Vint Int.one) && MDCTXHashed (INI T) t ctx)
| DIEx_CaseSameMD => !!(rv= Vint Int.one) && MDCTXHashed (INI T) t ctx
| DIEx_CaseDiffMD D d p => 
       (!!(rv= nullval) && ConfHashedFinishedMpred D d p ctx * EVP_MD_rep D d)
    || (!!(rv= Vint Int.one) && MDCTXHashed (INI T) t ctx * EVP_MD_rep D d)
  end.

(*Header file specifies that ictx must already be initialized*)
Definition EVP_DigestInit_ex_ASPEC := DECLARE _EVP_DigestInit_ex
  WITH gv:globals, ctx:val, t:val, e:val, T: EVP_MD,
       c: EVP_DigestInit_ex_case
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (4 <= ctx_size_of_MD T <= Int.max_unsigned - (WA + WORD) - 8)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (EVP_DigestInitExPre T t c ctx; ERRGV gv; 
           EVP_MD_rep T t; mm_inv gv)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (EVP_DigestInitExPost T t c rv ctx; ERRGV gv; 
            EVP_MD_rep T t; mm_inv gv).

Lemma subsume_EVP_DigestInit_ex:
      subsume_funspec (snd EVP_DigestInit_ex_SPEC) (snd EVP_DigestInit_ex_ASPEC).
Proof. Admitted. (*
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[[gv ctx] t] e] T] c]. rewrite EVP_MD_rep_isptr'; Intros. destruct c.
+ (*Case INI, ie initialized*)
  replace_SEP 0 (MDCTXInitialized ctx). entailer!.
  Intros; rename H into SC.
  Exists (ctx, t, e, nullval, nullval, (nullval, nullval), T, gv, Ews, DIEC_NEQ None None)
         (OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. entailer!.
    unfold MDCTXInitialized, CTX_NULL; entailer!.
  - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred.
    old_go_lower; entailer; cancel.
    rewrite sepcon_comm, distrib_orp_sepcon. apply orp_left.
    * apply orp_right1. entailer!. unfold MDCTXInitialized, CTX_NULL; cancel.
    * Intros m; apply orp_right2. rewrite OPENSSL_malloc_token_compatible'; Intros.
      entailer!. unfold MDCTXHashed.
      Exists m. cancel.
      unfold EVP_MD_CTX_NNnode. entailer.
+ (*Case SameMD, ie configured/hashed or finished*)
  replace_SEP 0 (EX md : val,
 (EX data : mddataTp T,
  EVP_MD_CTX_NNnode Ews (t, (md, (nullval, nullval))) ctx *
  OPENSSL_malloc_token 16 ctx *
  (*MD_state Ews {| __EVP_MD := T; __content := data |} md **) memory_block Ews (ctx_size_of_MD T) md *
  OPENSSL_malloc_token (ctx_size_of_MD T) md)).
   (*MDCTXConfigured T t ctx || EX data:_, MDCTXFinished (Build_MD_with_content T data) t ctx). entailer!.*)
  { entailer!. simpl in *. apply orp_left.
    + unfold MDCTXConfigured. Intros md data. Exists md data. unfold EVP_MD_CTX_NNnode. entailer!. admit.
    + unfold MDCTXFinished. Intros data md. Exists md data. 
      rewrite OPENSSL_malloc_token_compatible' with (v:=md); Intros. entailer!. simpl. cancel. admit. }

  rename H into SZ. Intros m c.
    rewrite OPENSSL_malloc_token_compatible' with (v:=m); Intros. 
    Exists (ctx, t, e, t, m, (nullval, nullval), T, gv, Ews, DIEC_EQ)
           (OPENSSL_malloc_token 16 ctx * mm_inv gv * OPENSSL_malloc_token (ctx_size_of_MD T) m).
    apply andp_right; auto.
    - old_go_lower. entailer. cancel. Search preInit. admit. (* entailer.
      eapply derives_trans. apply MD_state_memoryblock. simpl. apply preInit_fresh_EWS.*)
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred.
      old_go_lower; entailer; cancel. 
      Exists m. cancel.
      unfold EVP_MD_CTX_NNnode. simpl. entailer!.
+ (*Case diffMD, ie configured or hashed*)
  replace_SEP 0 (!!(d<>t /\ D<>T) && ConfHashedFinishedMpred D d p ctx * EVP_MD_rep D d). entailer!.
  Intros. rename H into SZ. rename H0 into dt; rename H1 into DT.
  destruct p as [ | data | data].
  { (*Configured*)
    replace_SEP 0 (MDCTXConfigured D d ctx). entailer!.
    unfold MDCTXConfigured, EVP_MD_rep. Intros m c sh vals. rename H into Rsh.
    Exists (ctx, t, e, d, m, (nullval, nullval), T, gv, Ews, DIEC_NEQ (Some (sh,vals)) (Some {| __EVP_MD := D; __content := c |}))
           (OPENSSL_malloc_token 16 ctx * match_EVP_MD D vals).
    apply andp_right; auto.
    - old_go_lower. entailer!. unfold EVP_MD_NNnode. entailer!.
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. unfold DIE_postMpred. 
      old_go_lower; entailer.
      Exists x x0. entailer!.
      rewrite sepcon_comm. do 2 rewrite <- sepcon_assoc. rewrite sepcon_comm. 
      rewrite distrib_orp_sepcon. apply orp_left.
      * Intros; apply orp_right1; unfold MDCTXConfigured, EVP_MD_rep, EVP_MD_NNnode, EVP_MD_CTX_NNnode; entailer!.
        rewrite OPENSSL_malloc_token_compatible'; Intros.
        Exists sh m c vals. entailer!.
      * normalize. rewrite OPENSSL_malloc_token_compatible'; Intros. apply orp_right2. entailer!.
        unfold MDCTXHashed, EVP_MD_rep, EVP_MD_NNnode, EVP_MD_CTX_NNnode; entailer!.
        Exists sh x1 vals; simpl. entailer!. }
  { (*Hashed*) 
    replace_SEP 0 (MDCTXHashed {| __EVP_MD := D; __content := data |} d ctx). entailer!.
    unfold MDCTXHashed. Intros m. unfold EVP_MD_rep at 1. 
    Intros dsh dvals. rename H into Rdsh.
    Exists (ctx, t, e, d, m, (nullval, nullval), T, gv, Ews, DIEC_NEQ (Some(dsh,dvals)) (Some {| __EVP_MD := D; __content := data |}))
         (OPENSSL_malloc_token 16 ctx * match_EVP_MD D dvals).
    apply andp_right; auto.
    - old_go_lower. entailer!. unfold EVP_MD_NNnode. entailer!.
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. old_go_lower; entailer. cancel.
      unfold DIE_postMpred. simpl.
      rewrite sepcon_comm. do 3 rewrite <- sepcon_assoc. rewrite sepcon_comm.
      rewrite distrib_orp_sepcon. apply orp_left.
      * Intros; apply orp_right1. unfold MDCTXHashed, EVP_MD_NNnode.
        rewrite OPENSSL_malloc_token_compatible'; Intros. Exists m; entailer. simpl; cancel.
        entailer!.
        unfold EVP_MD_rep. Exists dsh dvals. entailer!.
      * normalize. rewrite OPENSSL_malloc_token_compatible'; Intros. apply orp_right2. entailer!.
        unfold MDCTXHashed, EVP_MD_rep, EVP_MD_NNnode, EVP_MD_CTX_NNnode; entailer!.
        Exists dsh x dvals; simpl. entailer!. }
  { (*Finished*) 
    replace_SEP 0 (MDCTXFinished {| __EVP_MD := D; __content := data |} d ctx). entailer!.
    unfold MDCTXFinished. Intros m. unfold EVP_MD_rep at 1. 
    Intros dsh dvals. rename H into Rdsh.
    Exists (ctx, t, e, d, m, (nullval, nullval), T, gv, Ews, DIEC_NEQ (Some(dsh,dvals)) (Some {| __EVP_MD := D; __content := data |}))
         (OPENSSL_malloc_token 16 ctx * match_EVP_MD D dvals).
    apply andp_right; auto.
    - old_go_lower. entailer!. unfold EVP_MD_NNnode. entailer!.
    - apply prop_right. Intros rv. Exists rv. simplify_Delta. old_go_lower; entailer. cancel.
      unfold DIE_postMpred. simpl.
      rewrite sepcon_comm. do 3 rewrite <- sepcon_assoc. rewrite sepcon_comm.
      rewrite distrib_orp_sepcon. apply orp_left.
      * Intros; apply orp_right1. unfold MDCTXHashed, EVP_MD_NNnode.
        rewrite OPENSSL_malloc_token_compatible'; Intros. Exists m; entailer. simpl; cancel.
        entailer!.
        unfold EVP_MD_rep. Exists dsh dvals. entailer!.
      * normalize. rewrite OPENSSL_malloc_token_compatible'; Intros. apply orp_right2. entailer!.
        unfold MDCTXHashed, EVP_MD_rep, EVP_MD_NNnode, EVP_MD_CTX_NNnode; entailer!.
        Exists dsh x dvals; simpl. entailer!. }
Time Qed. (*3.1s*)*)
(*
Variant EVP_DigestInit_case:=
  DI_CaseAlloc: EVP_DigestInit_case (*ctx has been allocated or initialized but not configured*)
| DI_CaseConf: forall D (d:val) (p:ConfOrHashed D), EVP_DigestInit_case. (*ctx has been configured*)

Definition EVP_DigestInitPre (c:EVP_DigestInit_case) ctx :=
  match c with 
  DI_CaseAlloc => MDCTXAllocated ctx
| DI_CaseConf D d p => ConfOrHashedMpred D d p ctx
  end.

Definition EVP_DigestInitPost T t (c:EVP_DigestInit_case) rv ctx :=
  match c with 
  DI_CaseAlloc => (!!(rv= nullval) && MDCTXInitialized ctx)
               || (!!(rv= Vint Int.one) && MDCTXHashed (INI T) t ctx)
| DI_CaseConf D d p => 
           (    (!!(rv= nullval) && MDCTXInitialized ctx)
             || (!!(rv= Vint Int.one) && MDCTXHashed (INI T) t ctx) )
           * EX md:_, EX data:_, 
             !!(match p with Configured => True | Hashed data' =>  data=data' end) &&
             MD_state Ews {| __EVP_MD := D; __content := data |} md * 
             OPENSSL_malloc_token (ctx_size_of_MD D) md  (*IS THIS A MEMORY LEAK?*)
  end.

Definition EVP_DigestInit_ASPEC := DECLARE _EVP_DigestInit
  WITH gv:globals, ctx:val, t:val, T: EVP_MD, c: EVP_DigestInit_case
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr) ]
      PROP (4 <= ctx_size_of_MD T <= Int.max_unsigned - (WA + WORD) - 8)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx)
      SEP (EVP_DigestInitPre c ctx; ERRGV gv; EVP_MD_rep T t; mm_inv gv)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (EVP_DigestInitPost T t c rv ctx; ERRGV gv; EVP_MD_rep T t; mm_inv gv).

Lemma subsume_EVP_DigestInit:
      subsume_funspec (snd EVP_DigestInit_SPEC) (snd EVP_DigestInit_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[gv ctx] t] T] c]. rewrite EVP_MD_rep_isptr'; Intros. rename H into SZ.
destruct c.
+ (*Alloc*)
  replace_SEP 0 (MDCTXAllocated ctx). entailer!.
  unfold MDCTXAllocated.
  Exists (ctx, t, T, gv, Ews) (OPENSSL_malloc_token 16 ctx).
  apply andp_right.
  * old_go_lower; entailer!.
  * apply prop_right. simplify_Delta. Intros rv; Exists rv. old_go_lower; entailer!.
    unfold DIE_postMpred; simpl.
    rewrite sepcon_comm, distrib_orp_sepcon; apply orp_left.
    - Intros; apply orp_right1. unfold MDCTXInitialized, CTX_NULL; entailer!.
    - Intros m; apply orp_right2. rewrite OPENSSL_malloc_token_compatible'; Intros.
      unfold MDCTXHashed. Exists m; simpl; entailer!.
+ (*Conf*) 
  replace_SEP 0 (ConfOrHashedMpred D d p ctx). entailer!.
  destruct p as [ | data].
  { (*Configured*)
    replace_SEP 0 (MDCTXConfigured D d ctx). entailer!. 
    unfold MDCTXConfigured, EVP_MD_CTX_NNnode; Intros md data.
    sep_apply (data_at_data_at_ Ews (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ctx).
    Exists (ctx, t, T, gv, Ews)
           (OPENSSL_malloc_token 16 ctx * MD_state Ews {| __EVP_MD := D; __content := data |} md * OPENSSL_malloc_token (ctx_size_of_MD D) md).
    apply andp_right.
    * old_go_lower; entailer!.
    * apply prop_right. simplify_Delta. Intros rv; Exists rv. old_go_lower; entailer. Exists md data. entailer!.
      unfold DIE_postMpred; simpl.
      rewrite sepcon_comm, distrib_orp_sepcon; apply orp_left.
      - Intros; subst. apply orp_right1. unfold MDCTXInitialized, CTX_NULL; entailer!.
      - Intros m; apply orp_right2. rewrite OPENSSL_malloc_token_compatible'; Intros; entailer!.
        unfold MDCTXHashed. Exists m; simpl; entailer!. }
  { (*Hashed*)
    replace_SEP 0 (MDCTXHashed {| __EVP_MD := D; __content := data |} d ctx). entailer!. 
    unfold MDCTXHashed, EVP_MD_CTX_NNnode; Intros md.
    sep_apply (data_at_data_at_ Ews (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ctx).
    Exists (ctx, t, T, gv, Ews)
           (OPENSSL_malloc_token 16 ctx * MD_state Ews {| __EVP_MD := D; __content := data |} md * OPENSSL_malloc_token (ctx_size_of_MD D) md).
    apply andp_right.
    * old_go_lower; entailer!.
    * apply prop_right. simplify_Delta. Intros rv; Exists rv. old_go_lower; entailer. Exists md data. entailer!.
      unfold DIE_postMpred; simpl.
      rewrite sepcon_comm, distrib_orp_sepcon; apply orp_left.
      - Intros; subst. apply orp_right1. unfold MDCTXInitialized, CTX_NULL; entailer!.
      - Intros m; apply orp_right2. rewrite OPENSSL_malloc_token_compatible'; Intros; entailer!.
        unfold MDCTXHashed. Exists m; simpl; entailer!. }
Qed.
*)
Definition EVP_DigestUpdate_ASPEC := DECLARE _EVP_DigestUpdate
  WITH ctx: val, t:val, d: val, dsh:share, data: list byte, DC: MD_with_content, len:Z
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), _data OF tptr tvoid,  _len OF tuint ]
      PROP (readable_share dsh; UpdateSideconditions DC data len)
      LOCAL (temp _ctx ctx; temp _data d; temp _len (Vint (Int.repr len)) )
      SEP (MDCTXHashed DC t ctx; data_block dsh data d; EVP_MD_rep (__EVP_MD DC) t)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTXHashed (UPD DC data len) t ctx; data_block dsh data d; EVP_MD_rep (__EVP_MD DC) t).

Lemma subsume_EVP_DigestUpdate:
      subsume_funspec (snd EVP_DigestUpdate_SPEC) (snd EVP_DigestUpdate_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[[[ctx t] d] dsh] data] DC] len]. 
rewrite EVP_MD_rep_isptr'; Intros. rename H into Rdsh. rename H0 into SC.
unfold MDCTXHashed, EVP_MD_CTX_NNnode; Intros md.
Exists (ctx, Ews, (t, (md, (nullval, nullval))), d, dsh, data, DC, len, Ews)
       (OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md * OPENSSL_malloc_token 16 ctx).
apply andp_right.
+ old_go_lower; entailer!.
+ apply prop_right. simplify_Delta. old_go_lower; entailer. Exists md. entailer!.
Qed.

Definition EVP_DigestFinal_ex_ASPEC := DECLARE _EVP_DigestFinal_ex
  WITH ctx: val, t:val, 
       out: val, osh:share, sz:val,
       DC:MD_with_content
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md_out OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share osh;
            0 <= ctx_size_of_MD (__EVP_MD DC) <= Int.max_unsigned)
      LOCAL (temp _ctx ctx; temp _md_out out; temp _size sz )
      SEP (MDCTXHashed DC t ctx; EVP_MD_rep (__EVP_MD DC) t;
           if Val.eq sz nullval then emp else data_at_ Ews tuint sz;
           memory_block osh (md_size_of_MD (__EVP_MD DC)) out)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTXFinished DC t ctx;
            EVP_MD_rep (__EVP_MD DC) t;
            if Val.eq sz nullval then emp else data_at Ews tuint (Vint (Int.repr (md_size_of_MD (__EVP_MD DC)))) sz;
            data_block osh (FIN DC) out).

Lemma subsume_EVP_DigestFinal_ex:
      subsume_funspec (snd EVP_DigestFinal_ex_SPEC) (snd EVP_DigestFinal_ex_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[[ctx t] out] osh] sz] DC].
rewrite EVP_MD_rep_isptr'; Intros. rename H into Wosh. rename H0 into SZ.
unfold MDCTXHashed, EVP_MD_CTX_NNnode; Intros md.
Exists (ctx, Ews, (t, (md, (nullval, nullval))), out, osh, sz, DC, Ews)
       (OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) md * OPENSSL_malloc_token 16 ctx).
apply andp_right.
+ old_go_lower; entailer!.
+ apply prop_right. simplify_Delta. old_go_lower; entailer!. Exists md; cancel.
Qed.

Definition EVP_DigestFinal_ASPEC := DECLARE _EVP_DigestFinal
  WITH gv: globals, ctx: val, t:val, 
       out: val, osh:share, sz:val,
       DC:MD_with_content
  PRE [_ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share osh;
            0 <= ctx_size_of_MD (__EVP_MD DC) <= Int.max_unsigned)
      LOCAL (gvars gv; temp _ctx ctx; temp _md out; temp _size sz )
      SEP (MDCTXHashed DC t ctx; EVP_MD_rep (__EVP_MD DC) t;
           if Val.eq sz nullval then emp else data_at_ Ews tuint sz;
           memory_block osh (md_size_of_MD (__EVP_MD DC)) out; mm_inv gv)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTXInitialized ctx;
            EVP_MD_rep (__EVP_MD DC) t;
            if Val.eq sz nullval then emp else data_at Ews tuint (Vint (Int.repr (md_size_of_MD (__EVP_MD DC)))) sz;
            data_block osh (FIN DC) out; mm_inv gv).

Lemma subsume_EVP_DigestFinal:
      subsume_funspec (snd EVP_DigestFinal_SPEC) (snd EVP_DigestFinal_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[[[[[gv ctx] t] out] osh] sz] DC].
rewrite EVP_MD_rep_isptr'; Intros. rename H into Wosh. rename H0 into SZ.
unfold MDCTXHashed, EVP_MD_CTX_NNnode; Intros md.
Exists (gv, ctx, Ews, (t, (md, (nullval, nullval))), out, osh, sz, DC)
       (OPENSSL_malloc_token 16 ctx).
apply andp_right.
+ old_go_lower; entailer!.
+ apply prop_right. simplify_Delta. old_go_lower; entailer!.
  unfold MDCTXInitialized; cancel.
Qed.

(*free can't be called on a merely allocated (but not yet initialized) CTX -- the md field is Vundef*)
Inductive EVP_MD_CTX_free_case :=
(*  FreeNull: EVP_MD_CTX_free_case TODO: should this be supported? If we're supporting it here, what about the other operations?*)
  FreeInitialized: EVP_MD_CTX_free_case
| FreeConfiguredOrFinished: forall (D:EVP_MD) (d:val), EVP_MD_CTX_free_case.

Definition EVP_MD_CTX_free_pre (c:EVP_MD_CTX_free_case) (ctx:val) : mpred :=
  match c with
(* | FreeNull: !!(ctx=nullval) && emp)*)
 | FreeInitialized => MDCTXInitialized ctx
 | FreeConfiguredOrFinished D d => 
      MDCTXConfigured D d ctx (*|| MDCTXFinished D d ctx*)
  end.

Definition EVP_MD_CTX_free_ASPEC := DECLARE _EVP_MD_CTX_free
  WITH gv:globals, ctx:val, c: EVP_MD_CTX_free_case
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvars gv; temp _ctx ctx)
      SEP (EVP_MD_CTX_free_pre c ctx; mm_inv gv)
  POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mm_inv gv).

Inductive EVP_MD_CTX_cleanup_case :=
  ClInitialized: EVP_MD_CTX_cleanup_case
| ClConfiguredOrFinished: forall (D:EVP_MD) (d:val), EVP_MD_CTX_cleanup_case.

Definition EVP_MD_CTX_cleanup_pre (c:EVP_MD_CTX_cleanup_case) (ctx:val) : mpred :=
  match c with
   ClInitialized => MDCTXInitialized ctx (*Note: can't use ALLOCATED here: the body's first instruction accesses ctx -> md_data*)
 | ClConfiguredOrFinished D d => 
      (MDCTXConfigured D d ctx (*|| MDCTXFinished D d ctx*)) * EVP_MD_rep D d
end.

Definition EVP_MD_CTX_cleanup_post (c:EVP_MD_CTX_cleanup_case) (ctx:val) : mpred :=
  match c with
   ClInitialized => MDCTXInitialized ctx
 | ClConfiguredOrFinished D d => MDCTXInitialized ctx * EVP_MD_rep D d
end.

Definition EVP_MD_CTX_cleanup_ASPEC := DECLARE _EVP_MD_CTX_cleanup
  WITH gv:globals, ctx:val, c:EVP_MD_CTX_cleanup_case
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP () LOCAL (gvars gv; temp _ctx ctx)
      SEP (EVP_MD_CTX_cleanup_pre c ctx; mm_inv gv)
  POST [ tint ]
       PROP () LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (EVP_MD_CTX_cleanup_post c ctx; mm_inv gv).

Definition EVP_MD_CTX_init_ASPEC := DECLARE _EVP_MD_CTX_init
   WITH ctx:val
   PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr) ]
       PROP () LOCAL (temp _ctx ctx) SEP (MDCTXAllocated ctx)
   POST [ tvoid ]
       PROP () LOCAL () SEP (MDCTXInitialized ctx).

(*Note that this is the same spec as cleanup! Indeed the comment in the header file
  suggests that the precondition should be that of lceanup, whereas the fact that
  cleanup results in an initialized (not merely allocated) ctx means that doing init again does not change much*)
Definition EVP_MD_CTX_reset_ASPEC := DECLARE _EVP_MD_CTX_reset
  WITH gv:globals, ctx:val, c: EVP_MD_CTX_cleanup_case
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvars gv; temp _ctx ctx)
      SEP (EVP_MD_CTX_cleanup_pre c ctx; mm_inv gv)
  POST [ tint]
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (EVP_MD_CTX_cleanup_post c ctx; mm_inv gv).

Lemma subsume_EVP_MD_CTX_cleanup:
      subsume_funspec (snd EVP_MD_CTX_cleanup_SPEC) (snd EVP_MD_CTX_cleanup_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[gv ctx] c]. destruct c.
+ (*Case ClInitialized*)
  Exists (gv, ctx, Ews, nullval, @None Z) (OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. unfold MDCTXInitialized, CTX_NULL. entailer!.
    Exists nullval nullval. entailer!. 
  - entailer!. unfold MDCTXInitialized, CTX_NULL. entailer!.
+ (*Case ClConfiguredOrFinished*)
  replace_SEP 0 (MDCTXConfigured D d ctx * EVP_MD_rep D d). 
  { entailer!. } 
  unfold MDCTXConfigured. Intros md data.
  Exists (gv, ctx, Ews, md, Some (ctx_size_of_MD D)) (EVP_MD_rep D d * OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. Exists d nullval. entailer!. apply MD_state_memoryblock.
  - apply prop_right. simplify_Delta. old_go_lower. entailer.
    unfold MDCTXInitialized. cancel.
Qed.

(*Indeed - same proof as for cleanup*)
Lemma subsume_EVP_MD_CTX_reset:
      subsume_funspec (snd EVP_MD_CTX_reset_SPEC) (snd EVP_MD_CTX_reset_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros [[gv ctx] c]. destruct c.
+ (*Case ClInitialized*)
  Exists (gv, ctx, Ews, nullval, @None Z) (OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. unfold MDCTXInitialized, CTX_NULL.
    Exists nullval nullval. entailer!.
  - entailer!. unfold MDCTXInitialized, CTX_NULL. entailer!.
+ (*Case ClConfiguredOrFinished*)
  replace_SEP 0 (MDCTXConfigured D d ctx * EVP_MD_rep D d). 
  { entailer!. } 
  unfold MDCTXConfigured. Intros md data.
  Exists (gv, ctx, Ews, md, Some (ctx_size_of_MD D)) (EVP_MD_rep D d * OPENSSL_malloc_token 16 ctx).
  apply andp_right; auto.
  - old_go_lower. Exists d nullval. entailer!. apply MD_state_memoryblock.
  - apply prop_right. simplify_Delta. old_go_lower. entailer.
    unfold MDCTXInitialized. cancel.
Qed.

Definition EVP_MD_CTX_newcreate_ASPEC :=
   WITH gv:globals
   PRE [ ]
       PROP (24 <= Int.max_unsigned - (WA + WORD))
       LOCAL (gvars gv)
       SEP (mm_inv gv)
   POST [ tptr (Tstruct _env_md_ctx_st noattr) ]
     EX ctx:val,
       PROP ()
       LOCAL (temp ret_temp ctx)
       SEP ((!!(ctx=nullval) && emp) || MDCTXInitialized ctx; mm_inv gv).

Definition EVP_MD_CTX_create_ASPEC := DECLARE _EVP_MD_CTX_create EVP_MD_CTX_newcreate_ASPEC.
Definition EVP_MD_CTX_new_ASPEC := DECLARE _EVP_MD_CTX_new EVP_MD_CTX_newcreate_ASPEC.

Lemma subsume_EVP_MD_CTX_init:
      subsume_funspec (snd EVP_MD_CTX_init_SPEC) (snd EVP_MD_CTX_init_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros ctx. Exists (ctx, Ews) (OPENSSL_malloc_token 16 ctx).
apply andp_right; auto.
+ old_go_lower; entailer.
+ apply prop_right. simplify_Delta; old_go_lower. entailer.
Qed.

Lemma subsume_EVP_MD_CTX_create:
      subsume_funspec (snd EVP_MD_CTX_create_SPEC) (snd EVP_MD_CTX_create_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros gv. Exists gv emp.
change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
apply andp_right; auto.
+ entailer!. 
+ apply prop_right. simplify_Delta. Intros ctx. Exists ctx. entailer.
Qed.

Lemma subsume_EVP_MD_CTX_new:
      subsume_funspec (snd EVP_MD_CTX_new_SPEC) (snd EVP_MD_CTX_new_ASPEC).
Proof.
apply NDsubsume_subsume.
{ split; reflexivity. }
split3; auto.
intros gv. Exists gv emp.
change (`emp) with (@emp (environ->mpred) _ _); rewrite !emp_sepcon.
apply andp_right; auto.
+ entailer!. 
+ apply prop_right. simplify_Delta. Intros ctx. Exists ctx. entailer.
Qed.

Lemma MDCTXAllocated_valid_ptr p: MDCTXAllocated p |-- valid_pointer p.
Proof. unfold MDCTXAllocated. apply sepcon_valid_pointer2.
  sep_apply (data_at__memory_block Ews (Tstruct _env_md_ctx_st noattr) p). Intros. simpl.
  sep_apply (memory_block_valid_ptr Ews 16 p).
  intuition. omega. trivial.
Qed.

Lemma MDCTXInitialized_valid_ptr p: MDCTXInitialized p |-- valid_pointer p.
Proof. eapply derives_trans. apply InitializedAllocated. apply MDCTXAllocated_valid_ptr. Qed.

Lemma MDCTXAllocated_isptr p: MDCTXAllocated p |-- !! isptr p.
Proof. intros. unfold MDCTXAllocated. entailer!. Qed.

Lemma MDCTXInitialized_isptr p: MDCTXInitialized p |-- !! isptr p.
Proof. eapply derives_trans. apply InitializedAllocated. apply MDCTXAllocated_isptr. Qed.

Lemma MDCTXAllocated_isptr' p: MDCTXAllocated p = (!!isptr p) && MDCTXAllocated p.
Proof. apply pred_ext; entailer. apply MDCTXAllocated_isptr. Qed.

Lemma MDCTXInitialized_isptr' p: MDCTXInitialized p = (!! isptr p) && MDCTXInitialized p.
Proof. apply pred_ext; entailer. apply MDCTXInitialized_isptr. Qed.

Lemma MDCTXConfigured_valid_ptr D d p: MDCTXConfigured D d p |-- valid_pointer p.
Proof. unfold MDCTXConfigured, EVP_MD_CTX_NNnode. Intros md data.
  apply sepcon_valid_pointer1; entailer!.
Qed.

Lemma MDCTXConfigured_isptr D d p: MDCTXConfigured D d p |-- !! isptr p.
Proof. unfold MDCTXConfigured, EVP_MD_CTX_NNnode. Intros md data. entailer!. Qed.

Lemma MDCTXFinished_valid_ptr D d p: MDCTXFinished D d p |-- valid_pointer p.
Proof. unfold MDCTXFinished, EVP_MD_CTX_NNnode. Intros md.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. entailer!. Qed.

Lemma MDCTXFinished_isptr D d p: MDCTXFinished D d p |-- !! isptr p.
Proof. unfold MDCTXFinished, EVP_MD_CTX_NNnode. Intros md. entailer!. Qed.

End EVP_MD_CTX_Protocol.*)
