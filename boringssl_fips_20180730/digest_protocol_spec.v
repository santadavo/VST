Require Import VST.floyd.proofauto.
Require Import boringssl_fips_20180730.spec_mem.
Require Import boringssl_fips_20180730.digest.

Require Export boringssl_fips_20180730.digest_model.
Require Import boringssl_fips_20180730.spec_digest_base.
Require Import boringssl_fips_20180730.spec_digest. (*should maybe be eliminated from here eventually*)

(*TODO: discuss/find out why some operations permit agument ctx to be null (free, copy_ex, 
albeit with raising error in the latter case) while others (eg cleanup, reset) don't. *)

Module Type EVP_MD_CTX_Protocol_TP.
Variant State :=
  Allocated: State
| Raw: State
| Empty: forall (D:EVP_MD) (d:val), State
| Hashed: forall (DC: MD_with_content) (d:val), State
| Full: forall (D: EVP_MD) (d:val), State.

Parameter MDCTX: State -> val -> mpred.

Axiom RawAllocated: forall p, MDCTX Raw p |-- MDCTX Allocated p.

Axiom Empty_HashedIni: forall D d p, MDCTX (Empty D d) p |-- MDCTX (Hashed (INI D) d) p.
Axiom HashedFull: forall DC d p, MDCTX (Hashed DC d) p |-- MDCTX (Full (__EVP_MD DC) d) p.

Lemma EmptyFull: forall D d p, MDCTX (Empty D d) p |-- MDCTX (Full D d) p.
Proof. intros. sep_apply (Empty_HashedIni D d p). apply HashedFull. Qed.

Axiom Allocated_valid_ptr: forall p, MDCTX Allocated p |-- valid_pointer p.
Axiom Allocated_isptr: forall p, MDCTX Allocated p |-- !! isptr p.

Axiom Full_valid_ptr: forall D d p, MDCTX (Full D d) p |-- valid_pointer p.
Axiom Full_isptr: forall D d p, MDCTX (Full D d) p |-- !! isptr p.

Definition EVP_MD_CTX_init_ASPEC := DECLARE _EVP_MD_CTX_init
   WITH ctx:val
   PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr) ]
       PROP () LOCAL (temp _ctx ctx) SEP (MDCTX Allocated ctx)
   POST [ tvoid ]
       PROP () LOCAL () SEP (MDCTX Raw ctx).

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

(*free/destroy can't be called on a merely allocated (but not yet initialized) CTX -- the md field is Vundef*)
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

Definition EVP_of (c: State): mpred :=
  match c with
  Allocated => FF
| Raw => emp
| Empty D d => EVP_MD_rep D d
| Hashed DC d => EVP_MD_rep (__EVP_MD DC) d
| Full D d => EVP_MD_rep D d
  end.

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
       SEP (if Val.eq rv nullval then MDCTX Raw ctx
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

(*The spec for EVP_Digest_SPEC  does not mention any concepts used
  in the definitions of the five MDCTX predicates. Thus, we
  omit its repetition here as the subsumption proof would be trivial anyway.
  Of course we should expose EVP_Digest_SPEC when we define the Gprog.*)

Axiom subsume_EVP_MD_CTX_newcreate:
      subsume_funspec EVP_MD_CTX_newcreate_SPEC EVP_MD_CTX_newcreate_ASPEC.

Axiom subsume_EVP_MD_CTX_cleanupreset:
      subsume_funspec EVP_MD_CTX_cleanupreset_SPEC EVP_MD_CTX_cleanupreset_ASPEC.

Axiom subsume_EVP_MD_CTX_freedestroy:
      subsume_funspec EVP_MD_CTX_freedestroy_SPEC EVP_MD_CTX_freedestroy_ASPEC.

Axiom subsume_EVP_MD_CTX_init:
      subsume_funspec (snd EVP_MD_CTX_init_SPEC) (snd EVP_MD_CTX_init_ASPEC).

Axiom subsume_EVP_DigestInit_ex:
      subsume_funspec (snd EVP_DigestInit_ex_SPEC) (snd EVP_DigestInit_ex_ASPEC).

Axiom subsume_EVP_DigestInit:
      subsume_funspec (snd EVP_DigestInit_SPEC) (snd EVP_DigestInit_ASPEC).

Axiom subsume_EVP_DigestUpdate:
      subsume_funspec (snd EVP_DigestUpdate_SPEC) (snd EVP_DigestUpdate_ASPEC).

Axiom subsume_EVP_DigestFinal_ex:
      subsume_funspec (snd EVP_DigestFinal_ex_SPEC) (snd EVP_DigestFinal_ex_ASPEC).

Axiom subsume_EVP_DigestFinal:
      subsume_funspec (snd EVP_DigestFinal_SPEC) (snd EVP_DigestFinal_ASPEC).

Axiom subsume_EVP_MD_CTX_copy_ex:
      subsume_funspec (snd EVP_MD_CTX_copy_ex_SPEC) (snd EVP_MD_CTX_copy_ex_ASPEC).

Axiom subsume_EVP_MD_CTX_copy:
      subsume_funspec (snd EVP_MD_CTX_copy_SPEC) (snd EVP_MD_CTX_copy_ASPEC).
Print funspecs.
(*The subsumes lemmas should be moved to the proof / instance of this module type - 
  in module types, we should only expose a Gprog that containing (only) the abtract specs*)

End EVP_MD_CTX_Protocol_TP.
