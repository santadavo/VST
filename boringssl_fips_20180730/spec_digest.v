Require Import boringssl_fips_20180730.spec_mem.
Require Import boringssl_fips_20180730.spec_digest_base.
Require Import boringssl_fips_20180730.digests.
Require Import boringssl_fips_20180730.digest.

Definition OPENSSL_PUT_ERROR_SPEC := DECLARE _ERR_put_error
  WITH a1:val, a2:val, a3:val, ep:val, a5:val
  PRE [ 1%positive OF tint, 
        2%positive OF tint, 3%positive OF tint, 
        4%positive OF (tptr tschar), 5%positive OF tuint ]
      PROP() 
      LOCAL (temp 1%positive a1; temp 2%positive a2; temp 3%positive a3; 
             temp 4%positive ep; temp 5%positive a5)
      SEP (ERR ep)
  POST [ tvoid ]
    PROP () LOCAL () SEP (ERR ep).

Definition EVP_MD_type_SPEC := DECLARE _EVP_MD_type
  WITH md:val, D:EVP_MD
  PRE [ _md OF (tptr (Tstruct _env_md_st noattr)) ]
      PROP ()
      LOCAL (temp _md md)
      SEP (EVP_MD_rep D md)
  POST [tint]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (NID_of_DigestNID (type_of_MD D)))))
       SEP (EVP_MD_rep D md).

Definition EVP_MD_flags_SPEC := DECLARE _EVP_MD_flags 
  WITH md:val, D:EVP_MD
  PRE [ _md OF (tptr (Tstruct _env_md_st noattr)) ]
      PROP ()
      LOCAL (temp _md md)
      SEP (EVP_MD_rep D md)
  POST [tuint]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (flags_of_MD D))))
       SEP (EVP_MD_rep D md).

Definition EVP_MD_size_SPEC := DECLARE _EVP_MD_size
  WITH md:val, D:EVP_MD
  PRE [ _md OF (tptr (Tstruct _env_md_st noattr)) ]
      PROP ()
      LOCAL (temp _md md)
      SEP (EVP_MD_rep D md)
  POST [tuint]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (md_size_of_MD D))))
       SEP (EVP_MD_rep D md).

Definition EVP_MD_block_size_SPEC := DECLARE _EVP_MD_block_size
  WITH md:val, D:EVP_MD
  PRE [ _md OF (tptr (Tstruct _env_md_st noattr)) ]
      PROP ()
      LOCAL (temp _md md)
      SEP (EVP_MD_rep D md)
  POST [tuint]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (block_size_of_MD D))))
       SEP (EVP_MD_rep D md).

Definition EVP_add_digest_SPEC := DECLARE _EVP_add_digest
  WITH v:val
  PRE [_digest OF tptr (Tstruct _env_md_st noattr)]
      PROP () LOCAL (temp _digest v) SEP ()
  POST [tint] PROP () LOCAL (temp ret_temp (Vint Int.one)) SEP ().

(*All uses of this mpred occurs in places where the variable pointing to
  the data structures has type EVP_MD_CTX - hence, we should not use the tarray - based definition*)
Definition CTX_NULL sh p: mpred := (*
  let n:= sizeof (Tstruct _env_md_ctx_st noattr) in
  data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) p*)
  data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) p.

Definition EVP_MD_CTX_init_SPEC := DECLARE _EVP_MD_CTX_init
   WITH ctx:val, sh:share(*, n:Z*)
   PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr) ]
       PROP (writable_share sh)
       LOCAL (temp _ctx ctx)
       SEP (data_at_ sh (Tstruct _env_md_ctx_st noattr) ctx)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (CTX_NULL sh ctx).

Definition EVP_MD_CTX_newcreate_SPEC :=
   WITH gv:globals
   PRE [ ]
       PROP (sizeof (Tstruct _env_md_ctx_st noattr) + 8 <= Int.max_unsigned - (WA + WORD))
       LOCAL (gvars gv)
       SEP (mm_inv gv)
   POST [ tptr (Tstruct _env_md_ctx_st noattr) ]
     EX ctx:val,
       PROP ((sizeof (Tstruct _env_md_ctx_st noattr)) = 16)
       LOCAL (temp ret_temp ctx)
       SEP ((!!(ctx=nullval) && emp) || (OPENSSL_malloc_token 16 ctx * CTX_NULL Ews ctx (*data_at_ Ews (tarray tuchar 16) ctx*));
            mm_inv gv).

Definition EVP_MD_CTX_new_SPEC := DECLARE _EVP_MD_CTX_new EVP_MD_CTX_newcreate_SPEC.

Definition EVP_MD_CTX_create_SPEC := DECLARE _EVP_MD_CTX_create EVP_MD_CTX_newcreate_SPEC.

(****** Specs of the four Digest Operation Accessors. *******)
(*nonnull node*)
Definition EVP_MD_CTX_NNnode (sh:share) (vals:val*(val*(val*val))) (p:val):mpred :=
  match vals with (d, (mddata, (pctx, pctxops))) =>
  !!(is_pointer_or_null d /\ is_pointer_or_null mddata) &&
  data_at sh (Tstruct _env_md_ctx_st noattr) (d,(mddata,(pctx, pctxops))) p
  end.
(*a possibly null node*)
Definition EVP_MD_CTX_node sh (vals:val*(val*(val*val))) (p:val):mpred :=
 (!!(p = nullval) && emp) || EVP_MD_CTX_NNnode sh vals p.

(*According to digest.h, EVP_MD_CTX_md may be invoked even if no digest has not been set, 
  returning null in this case. The other 3 functions are specified to crash in such a 
  situation - we hence strengthen the precondition to rule out these situations*)
Definition EVP_MD_CTX_md_SPEC := DECLARE _EVP_MD_CTX_md
  WITH ctx:val, sh:share, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_node sh (d, x) ctx)
  POST [ tptr (Tstruct _env_md_st noattr) ]
       PROP ()
       LOCAL (temp ret_temp (if Val.eq ctx nullval then nullval else d))
       SEP (EVP_MD_CTX_node sh (d, x) ctx).

Definition EVP_MD_CTX_size_SPEC := DECLARE _EVP_MD_CTX_size
  WITH ctx:val, sh:share, D:EVP_MD, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep D d)
  POST [ tuint ]
       PROP (readable_share sh)
       LOCAL (temp ret_temp (Vint (Int.repr (md_size_of_MD D))))
       SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep D d).

Definition EVP_MD_CTX_block_size_SPEC := DECLARE _EVP_MD_CTX_block_size
  WITH ctx:val, sh:share, D:EVP_MD, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep D d)
  POST [ tuint ]
       PROP (readable_share sh)
       LOCAL (temp ret_temp (Vint (Int.repr (block_size_of_MD D))))
       SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep D d).

Definition EVP_MD_CTX_type_SPEC := DECLARE _EVP_MD_CTX_type
  WITH ctx:val, sh:share, D:EVP_MD, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep D d)
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (NID_of_DigestNID (type_of_MD D)))))
       SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep D d).

(*Comment: digest.h does not say what happens if digest is not set (ie ctx->digest=null)
  or indeed if the context is not in the right state.
  In contrast, the DigestOperationAccessors are specified to crash in such a case.*)
Definition EVP_DigestUpdate_SPEC := DECLARE _EVP_DigestUpdate
  WITH ctx: val, sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       d: val, dsh:share, data: list byte, DC: MD_with_content, len:Z, mdsh:share
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), _data OF tptr tvoid,  _len OF tuint ]
      PROP (readable_share sh; readable_share dsh; writable_share mdsh;
            UpdateSideconditions DC data len)
      LOCAL (temp _ctx ctx; temp _data d; temp _len (Vint (Int.repr len)) )
      SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;        
           data_block dsh data d;
           MD_state mdsh DC (mddata_of_ctx CTX);
           EVP_MD_rep (__EVP_MD DC) (type_of_ctx CTX))
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
            data_block dsh data d;
            MD_state mdsh (UPD DC data len) (mddata_of_ctx CTX);
            EVP_MD_rep (__EVP_MD DC) (type_of_ctx CTX)).

Definition EVP_DigestFinal_ex_SPEC := DECLARE _EVP_DigestFinal_ex
  WITH ctx: val, sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       out: val, osh:share, sz:val,
       DC:MD_with_content, mdsh:share
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md_out OF tptr tuchar, _size OF tptr tuint]
      PROP (readable_share sh; writable_share osh; writable_share mdsh(*;
            0 <= ctx_size_of_MD (__EVP_MD DC) <= Int.max_unsigned*))
      LOCAL (temp _ctx ctx; temp _md_out out; temp _size sz )
      SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
            MD_state mdsh DC (mddata_of_ctx CTX);
            EVP_MD_rep (__EVP_MD DC) (type_of_ctx CTX); 
            if Val.eq sz nullval then emp else data_at_ Ews tuint sz;
            memory_block osh (md_size_of_MD (__EVP_MD DC)) out)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              postFin mdsh (__EVP_MD DC) (mddata_of_ctx CTX);
              EVP_MD_rep (__EVP_MD DC) (type_of_ctx CTX); 
              if Val.eq sz nullval then emp else data_at Ews tuint (Vint (Int.repr (md_size_of_MD (__EVP_MD DC)))) sz;
              data_block osh (FIN DC) out).

(*nonnull node*)
Definition EVP_MD_NNnode (sh:share) (vals:reptype (Tstruct _env_md_st noattr)) (p:val):mpred :=
  !!(readable_share sh) &&
  data_at sh (Tstruct _env_md_st noattr) vals p.

(*a possibly null node*)
Definition EVP_MD_node (vals:reptype (Tstruct _env_md_st noattr))(p:val):mpred :=
 (!!(p = nullval) && emp) || (EX sh:_, EVP_MD_NNnode sh vals p).

Definition EVP_Digest_SPEC := DECLARE _EVP_Digest
  WITH gv: globals, d:val, cnt:int, md:val, sz:val, t:val, e:val,
       D: EVP_MD,
       dsh:share, Data: list byte, osh:share
  PRE [_data OF tptr tvoid, _count OF tuint, _out_md OF (tptr tuchar),
        _out_size OF (tptr tuint), _type OF (tptr (Tstruct _env_md_st noattr)),
        _impl OF (tptr (Tstruct _engine_st noattr)) ]
      PROP ((*4 <= ctx_size_of_MD D <= Int.max_unsigned - (WA + WORD) - 8;*)
            readable_share dsh; writable_share osh; UpdateSideconditions (INI D) Data (Int.unsigned cnt))
      LOCAL (gvars gv; temp _data d; temp _count (Vint cnt);
             temp _out_md md; temp _out_size sz; temp _type t; temp _impl e)
      SEP (ERRGV gv; mm_inv gv; EVP_MD_rep D t; data_block dsh Data d;
            if Val.eq sz nullval then emp else data_at_ Ews tuint sz;
            memory_block osh (md_size_of_MD D) md)
  POST [tint] EX rv:int,
      PROP () LOCAL (temp ret_temp (Vint rv)) 
      SEP (ERRGV gv; mm_inv gv; EVP_MD_rep D t; data_block dsh Data d;
           (  (!!(rv=Int.zero) 
               && (memory_block osh (md_size_of_MD D) md *
                   if Val.eq sz nullval then emp 
                   else data_at_ Ews tuint sz))
           || (!!(rv=Int.one)
               && (data_block osh (FIN (UPD (INI D) Data (Int.unsigned cnt))) md *
                   if Val.eq sz nullval then emp 
                   else data_at Ews tuint (Vint (Int.repr (md_size_of_MD D))) sz)))).

Definition EVP_MD_CTX_cleanupreset_SPEC := 
  WITH gv: globals, ctx:val, sh:share, mdd:val, c: option Z
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (writable_share sh)
      LOCAL (gvars gv; temp _ctx ctx)
      SEP (EX d:val, EX pv1:val, EVP_MD_CTX_NNnode sh (d, (mdd, (pv1, nullval))) ctx; 
           (match c with 
              None => !!(mdd=nullval) && emp
            | Some sz => memory_block Ews sz mdd * OPENSSL_malloc_token sz mdd
            end); mm_inv gv)
  POST [ tint ]
       PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] ctx)
       LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (CTX_NULL sh ctx (*data_at_ sh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx*);
             mm_inv gv).
(*have strengthened at data_at_ to data_at list_repeat .. 0
Discuss white/blackbox abstract specs in the paper?*)

Definition EVP_MD_CTX_cleanup_SPEC := DECLARE _EVP_MD_CTX_cleanup EVP_MD_CTX_cleanupreset_SPEC.

Definition EVP_MD_CTX_reset_SPEC := DECLARE _EVP_MD_CTX_reset EVP_MD_CTX_cleanupreset_SPEC.

Variant copyEx_cases :=
  copyEx_ictxNull: copyEx_cases
| copyEx_indigestNull: forall (ish:share) (md pv1 pv2 :val), copyEx_cases
| copyEx_other: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val) (ctxsz:int) (imdsh:share) 
                      (idata: type_with_content (*list byte*))
                (pp: option (share * reptype (Tstruct _env_md_st noattr) * int)), copyEx_cases.

(*require that d'=null implies md'=null - otherwise, cleanup wouldn't know how much to free (sanity invariant)*)
Definition copyExPre (c:copyEx_cases) (ictx octx:val) gv : mpred :=
match c with 
  copyEx_ictxNull => !!(ictx=nullval)&&emp
| copyEx_indigestNull ish md pv1 pv2 => !!(readable_share ish)
                            && EVP_MD_CTX_NNnode ish (nullval, (md, (pv1, pv2))) ictx
| copyEx_other ish d md pv1 pv2 dsh vals osh d' md' pv1' ctxsz imdsh idata pp =>
       !!(isptr octx /\ readable_share ish /\
          readable_share dsh /\ writable_share osh /\ pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned - (WA + WORD) - 8 /\
          readable_share imdsh)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (d', (md', (pv1', nullval))) octx *
          (*data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vubyte idata) md *)
            data_at imdsh (__type idata) (__values idata) md * 
          mm_inv gv *
          if Val.eq d d' 
          then !! (pp=None)
               && OPENSSL_malloc_token (Int.unsigned ctxsz) md' * memory_block Ews (Int.unsigned ctxsz) md'
          else match pp with
          | None => !! (d'=nullval /\ md'=nullval) && emp
          | Some (dsh', vals', ctxsz') => 
               !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz'(*Int.lt Int.zero ctxsz = true *)(*/\ Int.eq ctxsz' Int.zero = false*)) 
               && (data_at dsh' (Tstruct _env_md_st noattr) vals' d') * 
                   (   (!!(md' = nullval)&& emp) 
                    || (OPENSSL_malloc_token (Int.unsigned ctxsz') md' * memory_block Ews (Int.unsigned ctxsz') md'))
          end 
end.

Definition copyExPost (c: copyEx_cases) (ictx octx:val) gv rv : mpred := 
match c with
  copyEx_ictxNull => !!(rv=Vint Int.zero) && emp
| copyEx_indigestNull ish md pv1 pv2 => !!(rv=Vint Int.zero) && data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2))) ictx
| copyEx_other ish d md pv1 pv2 dsh vals osh d' md' pv1' ctxsz imdsh idata pp =>
       (*data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vubyte idata) md * *)
       data_at imdsh (__type idata) (__values idata) md *      
       data_at dsh (Tstruct _env_md_st noattr) vals d * mm_inv gv *
       data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx *
       if Val.eq d d'
       then !!(rv=Vint Int.one)
            && OPENSSL_malloc_token (Int.unsigned ctxsz) md' *
(*               data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vubyte idata) md' **)
               data_at Ews (__type idata) (__values idata) md' *
               data_at osh (Tstruct _env_md_ctx_st noattr) (d, (md', (Vint (Int.repr 0), pv2))) octx
       else ( (!!(rv=Vint Int.zero)
                && match pp with
                   | Some (dsh', vals', ctxsz') => data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                                                (  (!! (md' = nullval) && emp)
                                                 || (OPENSSL_malloc_token (Int.unsigned ctxsz') md' * memory_block Ews (Int.unsigned ctxsz') md'))
                   | None => emp
                   end *
                   data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx)
             || (EX buf:val, !!(rv=Vint Int.one) &&
(*                    data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vubyte idata) buf **)
                    data_at Ews (__type idata) (__values idata) buf *
                    data_at osh (Tstruct _env_md_ctx_st noattr) (d, (buf, (Vint (Int.repr 0), pv2))) octx *
                    OPENSSL_malloc_token (Int.unsigned ctxsz) buf *
                    match pp with
                    | Some (dsh',vals',ctxsz') => data_at dsh' (Tstruct _env_md_st noattr) vals' d'
                    | None => emp
                    end) )
end.

Definition EVP_MD_CTX_copy_ex_SPEC := DECLARE _EVP_MD_CTX_copy_ex
  WITH gv:globals, octx:val, ictx:val, case:copyEx_cases
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvars gv; temp _out octx; temp _in ictx)
      SEP (ERRGV gv; copyExPre case ictx octx gv)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; copyExPost case ictx octx gv rv).

Inductive copy_cases :=
  cp_ictxNull: copy_cases
| cp_inDigestNull: forall (ish:share) (md pv1 pv2 :val), copy_cases
(*| cp_inDataNull: forall (ish:share) (d pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr)), copy_cases*)
| cp_default: forall (ish:share) (d md pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (imdsh:share) (idata:type_with_content(*list byte*)) (ctxsz: int), copy_cases.
Definition copyPre gv (c:copy_cases) (ictx octx:val): mpred :=
match c with 
  cp_ictxNull => !!(ictx=nullval)&&emp
| cp_inDigestNull ish md pv1 pv2 => !!(isptr ictx /\ readable_share ish)
                            && EVP_MD_CTX_NNnode ish (nullval, (md, (pv1, pv2))) ictx
(*| cp_inDataNull ish d pv2 dsh vals =>
       !!(readable_share ish /\ readable_share dsh /\ is_pointer_or_null pv2 /\
          exists ctxsz, get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)
       && EVP_MD_CTX_NNnode ish (d, (nullval, (nullval, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d *)
| cp_default ish d md pv2 dsh vals imdsh idata ctxsz =>
       !!(readable_share ish /\ readable_share dsh /\ 
          is_pointer_or_null pv2 /\ readable_share imdsh /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned - (WA + WORD) - 8)
       && EVP_MD_CTX_NNnode ish (d, (md, (nullval, nullval))) ictx * mm_inv gv *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          (*data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vubyte idata) md*)
          data_at imdsh (__type idata) (__values idata) md 
end.

Definition copyPost gv (c:copy_cases) (ictx octx rv:val) osh: mpred :=
match c with 
  cp_ictxNull => 
    !!(rv=nullval) 
    && CTX_NULL osh octx(*data_at osh (tarray tuchar 16) (list_repeat 16 (Vint Int.zero)) octx*)
| cp_inDigestNull ish md pv1 pv2 => 
    !!(rv=nullval) 
    && CTX_NULL osh octx (*data_at osh (tarray tuchar 16) (list_repeat 16 (Vint Int.zero)) octx*) *
    data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2))) ictx
(*| cp_inDataNull ish d pv2 dsh vals =>
    !!(rv=Vint Int.one) 
    && EVP_MD_node vals d *
       data_at osh (Tstruct _env_md_ctx_st noattr)
         (d, (Vundef, (Vundef, pv2))) octx *
       data_at ish (Tstruct _env_md_ctx_st noattr)
        (d, (nullval, (nullval, pv2))) ictx*)
| cp_default ish d md pv2 dsh vals imdsh idata ctxsz => 
   (*data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vubyte idata) md **)
   data_at imdsh (__type idata) (__values idata) md *
   data_at dsh (Tstruct _env_md_st noattr) vals d * mm_inv gv *
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx *
   ( (!! (rv = Vint Int.zero) &&
         data_at osh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) octx)
   || (EX buf : val, !! (rv = Vint Int.one) &&
       (*data_at Ews (tarray tuchar (Int.unsigned ctxsz)) (map Vubyte idata) buf **)
       data_at Ews (__type idata) (__values idata) buf *
       OPENSSL_malloc_token (Int.unsigned ctxsz) buf *
       data_at osh (Tstruct _env_md_ctx_st noattr) (d, (buf, (Vint (Int.repr 0), nullval))) octx) )
end.

(*since init is called, octx must not be null!*)
Definition EVP_MD_CTX_copy_SPEC := DECLARE _EVP_MD_CTX_copy
  WITH gv:globals, octx:val, ictx:val, osh:share, case:copy_cases
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (writable_share osh)
      LOCAL (gvars gv; temp _out octx; temp _in ictx)
      SEP (ERRGV gv; data_at_ osh (Tstruct _env_md_ctx_st noattr) octx; 
           copyPre gv case ictx octx)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; copyPost gv case ictx octx rv osh).

Definition EVP_MD_CTX_freedestroy_SPEC :=
  WITH gv:globals, ctx:val, d:val, md: val, pv1:val, c: option Z
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvars gv; temp _ctx ctx)
      SEP ((!!(ctx=nullval) && emp)
           || (EVP_MD_CTX_NNnode Ews (d, (md, (pv1, nullval))) ctx *
               match c with 
                 None => !!(md=nullval) && emp
               | Some sz => memory_block Ews sz md * OPENSSL_malloc_token sz md
               end * OPENSSL_malloc_token (sizeof (Tstruct _env_md_ctx_st noattr)) ctx);
           mm_inv gv)
  POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mm_inv gv).

Definition EVP_MD_CTX_free_SPEC := DECLARE _EVP_MD_CTX_free EVP_MD_CTX_freedestroy_SPEC.

Definition EVP_MD_CTX_destroy_SPEC := DECLARE _EVP_MD_CTX_destroy EVP_MD_CTX_freedestroy_SPEC.

Definition EVP_DigestFinal_SPEC := DECLARE _EVP_DigestFinal
  WITH gv:globals, ctx: val, sh:share,
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       out: val, osh:share, sz:val,
       DC: MD_with_content
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share sh; writable_share osh;
            (*0 <= ctx_size_of_MD (__EVP_MD DC) <= Int.max_unsigned;*)
            snd(snd(snd CTX))=nullval (*pv2*))
      LOCAL (gvars gv; temp _ctx ctx; temp _md out; temp _size sz )
      SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
            MD_state Ews DC (mddata_of_ctx CTX);
            EVP_MD_rep (__EVP_MD DC) (type_of_ctx CTX); 
            if Val.eq sz nullval then emp else data_at_ Ews tuint sz;
            memory_block osh (md_size_of_MD (__EVP_MD DC)) out; 
             OPENSSL_malloc_token (ctx_size_of_MD (__EVP_MD DC)) (mddata_of_ctx CTX); mm_inv gv)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (CTX_NULL sh ctx;
              EVP_MD_rep (__EVP_MD DC) (type_of_ctx CTX);
              if Val.eq sz nullval then emp else data_at Ews tuint (Vint (Int.repr ((md_size_of_MD (__EVP_MD DC))))) sz;
              data_block osh (FIN DC) out; mm_inv gv).
(*
Definition DIE_preMpred mdd (p: option (list val * EVP_MD)): mpred :=
    match p with
    | None => !!(mdd = nullval) && emp
    | Some (v, D) => (*!!(get_ctxsize dvals = Vint (Int.repr (ctx_size_of_MD DD)) /\ Int.ltu Int.zero sz = true) && *)
                     data_at Ews (tarray tuchar (ctx_size_of_MD D)) v mdd *
                     OPENSSL_malloc_token (ctx_size_of_MD D) mdd
    end.

Definition DIE_postMpred rv d t pv mdd ctx csh T (p: option (list val * EVP_MD)): mpred :=
   (!!(rv= nullval)
    && data_at csh (Tstruct _env_md_ctx_st noattr) (d,(mdd,pv)) ctx * 
       match p with
       | None => emp
       | Some (v, D) => data_at Ews (tarray tuchar (ctx_size_of_MD D)) v mdd *
                        OPENSSL_malloc_token (ctx_size_of_MD D) mdd
       end)
|| (EX m :_, !!(rv= Vint Int.one)
             && data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, pv)) ctx * 
                MD_state Ews (INI T) m *
                OPENSSL_malloc_token (ctx_size_of_MD T) m).

Variant DigestInitExCase :=
  DIEC_EQ
| DIEC_NEQ: option (share * reptype (Tstruct digests._env_md_st noattr)) -> 
            option (list val * EVP_MD) -> DigestInitExCase.*)

Definition DIE_preMpred mdd (p: (*option MD_with_content*) option (EVP_MD * type_with_content(*list byte*))): mpred :=
    match p with
    | None => !!(mdd = nullval) && emp
    | Some (D,v) => (*data_at Ews (tarray tuchar (ctx_size_of_MD D)) (map Vubyte v) mdd *)
                    (!!(sizeof (__type v) = ctx_size_of_MD D) && 
                    data_at Ews (__type v) (__values v) mdd) *
                    OPENSSL_malloc_token (ctx_size_of_MD D) mdd
    end.

Definition DIE_postMpred rv d t pv mdd ctx csh T (p: option (*MD_with_content*)(EVP_MD * type_with_content(*list byte*))): mpred :=
   (!!(rv= nullval)
    && data_at csh (Tstruct _env_md_ctx_st noattr) (d,(mdd,pv)) ctx * 
       match p with
       | None => emp
       | Some (D,v) => (*data_at Ews (tarray tuchar (ctx_size_of_MD D)) (map Vubyte v)  mdd *)
                    data_at Ews (__type v) (__values v) mdd  *
                    OPENSSL_malloc_token (ctx_size_of_MD D) mdd
       end)
|| (EX m :_, !!(rv= Vint Int.one)
             && data_at csh (Tstruct _env_md_ctx_st noattr) (t, (m, pv)) ctx * 
                MD_state Ews (INI T) m *
                OPENSSL_malloc_token (ctx_size_of_MD T) m).

Variant DigestInitExCase :=
  DIEC_EQ
| DIEC_NEQ: option (share * reptype (Tstruct digests._env_md_st noattr)) -> 
            option (*MD_with_content*)(EVP_MD * type_with_content(*list byte*)) -> DigestInitExCase.

Definition EVP_DigestInit_ex_SPEC := DECLARE _EVP_DigestInit_ex
  WITH ctx:val, t:val, e:val, d:val, mdd:val, pv: val * val, T: EVP_MD,
       gv:globals, csh:share, c: DigestInitExCase
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (writable_share csh)
      LOCAL (gvars gv; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERRGV gv; EVP_MD_CTX_NNnode csh (d,(mdd,pv)) ctx; 
           EVP_MD_rep T t;
           match c with 
           | DIEC_EQ => !!(d=t) && preInit Ews (ctx_size_of_MD T) mdd
           | DIEC_NEQ q p => !!(d <> t) 
                             && (DIE_preMpred mdd p * mm_inv gv *
                                 match q with 
                                 | None => !!(d=nullval) && emp
                                 | Some (dsh, dvals) => EVP_MD_NNnode dsh dvals d
                                 end)
           end)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; EVP_MD_rep T t;
            match c with
            | DIEC_EQ => !!(rv = Vint Int.one) && EVP_MD_CTX_NNnode csh (d,(mdd,pv)) ctx *
                         MD_state Ews (INI T) mdd
            | DIEC_NEQ q p => DIE_postMpred rv d t pv mdd ctx csh T p * mm_inv gv *
                              match q with 
                              | None => emp
                              | Some (dsh, dvals) => EVP_MD_NNnode dsh dvals d
                              end
            end).

Definition EVP_DigestInit_SPEC := DECLARE _EVP_DigestInit
  WITH ctx:val, t:val, T: EVP_MD, gv:globals, csh:share
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr) ]
      PROP (writable_share csh)
      LOCAL (gvars gv; temp _ctx ctx; temp _type t)
      SEP (data_at_ csh (Tstruct _env_md_ctx_st noattr) ctx; 
           ERRGV gv; EVP_MD_rep T t;mm_inv gv)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERRGV gv; EVP_MD_rep T t; mm_inv gv;
            DIE_postMpred rv nullval t (nullval, nullval) nullval ctx csh T None).
