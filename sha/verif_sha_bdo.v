Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Require Import sha.verif_sha_bdo4.
Require Import sha.verif_sha_bdo7.
Require Import sha.verif_sha_bdo8.
Local Open Scope logic.

Lemma body_sha256_block_data_order: semax_body Vprog Gtot f_sha256_block_data_order sha256_block_data_order_spec.
Proof.
start_function.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
unfold POSTCONDITION, abbreviate.
simpl_stackframe_of.
fixup_local_var; intro Xv.
remember (hash_blocks init_registers hashed) as regs eqn:Hregs.
assert (Lregs: length regs = 8%nat) 
  by (subst regs; apply length_hash_blocks; auto).
assert (Zregs: Zlength regs = 8%Z)
 by (rewrite Zlength_correct; rewrite Lregs; reflexivity).
forward data_old. (* data = in; *)
assert_PROP (isptr data); [  entailer | ].
 match goal with |- semax _ _ ?c _ =>
  eapply seq_assocN with (cs := sequenceN 8 c)
 end.
*

Ltac semax_frame Qframe Rframe :=
  eapply (semax_frame1 Qframe Rframe);
 [ | reflexivity| | auto 50 with closed ].

semax_frame
             [ lvar _X (tarray tuint 16) Xv ] 
             [`(data_at_ Tsh (tarray tuint 16) Xv);
                         `(data_block sh (intlist_to_Zlist b) data);
                         `(K_vector kv)].
eapply sha256_block_load8 with (ctx:=ctx); eassumption.
entailer!; eassumption.
*
abbreviate_semax.
eapply semax_seq'.
semax_frame 
      [ lvar _X (tarray tuint 16) Xv ]
      [`(field_at Tsh t_struct_SHA256state_st [StructField _h] (map Vint regs) ctx)].
replace Delta with Delta_loop1 by simplify_Delta.
    fold block_data_order_loop1.
    simple apply (sha256_block_data_order_loop1_proof _ sh b ctx data regs kv Xv); auto.
    apply Zlength_length in H; auto.
entailer!.
simpl; abbreviate_semax.
eapply semax_seq'.
semax_frame  (@nil (environ -> Prop))
        [`(field_at Tsh t_struct_SHA256state_st [StructField _h] (map Vint regs) ctx);
         `(data_block sh (intlist_to_Zlist b) data)].
 eapply sha256_block_data_order_loop2_proof; eassumption.
 entailer!.
abbreviate_semax.
subst MORE_COMMANDS; unfold abbreviate.
eapply seq_assocN with (cs := add_them_back).
semax_frame  [  lvar _X (tarray tuint 16) Xv ]
             [`(K_vector kv);
             `(data_at_ Tsh (tarray tuint LBLOCKz) Xv);
             `(data_block sh (intlist_to_Zlist b) data)].
  replace Delta with (initialized _i Delta_loop1) by simplify_Delta.
  simple apply (add_them_back_proof _ regs (Round regs (nthi b) 63) ctx); try assumption.
  apply length_Round; auto.
  entailer!. eassumption.
simpl; abbreviate_semax.
forward. (* return; *)
fold (hash_block  (hash_blocks init_registers hashed) b).
rewrite hash_blocks_last by auto.
rewrite (lvar_eval_lvar _ _ _ _ H4).
cancel.
Qed.










