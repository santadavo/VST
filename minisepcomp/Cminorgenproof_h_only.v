(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for Cminor generation. *)

Require Import Coq.Program.Equality FSets Permutation.
Require Import FSets FSetAVL Orders Mergesort.
Require Import Coqlib Maps minisepcomp.Ordered Errors Integers Floats.
Require Intv.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import minisepcomp.Csharpminor_memsem minisepcomp.Switch minisepcomp.Cminor_memsem minisepcomp.Cminorgen.

Open Local Scope error_monad_scope.

(*new: from Inlining*)
Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; xomega.
Qed.

Definition match_prog (p: Csharpminor_memsem.program) (tp: Cminor_memsem.program) :=
  match_program (fun cu f tf => transl_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof.
  intros. apply match_transform_partial_program; auto.
Qed.

Section TRANSLATION.

Variable prog: Csharpminor_memsem.program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge : Csharpminor_memsem.genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf_partial TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: Csharpminor_memsem.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSL).

Lemma functions_translated:
  forall (v: val) (f: Csharpminor_memsem.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial TRANSL).

Lemma sig_preserved_body:
  forall f tf cenv size,
  transl_funbody cenv size f = OK tf ->
  tf.(fn_sig) = Csharpminor_memsem.fn_sig f.
Proof.
  intros. unfold transl_funbody in H. monadInv H; reflexivity.
Qed.

Lemma sig_preserved:
  forall f tf,
  transl_fundef f = OK tf ->
  Cminor_memsem.funsig tf = Csharpminor_memsem.funsig f.
Proof.
  intros until tf; destruct f; simpl.
  unfold transl_function. destruct (build_compilenv f).
  case (zle z Int.max_unsigned); simpl bind; try congruence.
  intros. monadInv H. simpl. eapply sig_preserved_body; eauto.
  intro. inv H. reflexivity.
Qed.

(** * Derived properties of memory operations *)

Lemma load_freelist:
  forall fbl chunk m b ofs m',
  (forall b' lo hi, In (b', lo, hi) fbl -> b' <> b) ->
  Mem.free_list m fbl = Some m' ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction fbl; intros.
  simpl in H0. congruence.
  destruct a as [[b' lo] hi].
  generalize H0. simpl. case_eq (Mem.free m b' lo hi); try congruence.
  intros m1 FR1 FRL.
  transitivity (Mem.load chunk m1 b ofs).
  eapply IHfbl; eauto. intros. eapply H. eauto with coqlib.
  eapply Mem.load_free; eauto. left. apply sym_not_equal. eapply H. auto with coqlib.
Qed.

Lemma perm_freelist:
  forall fbl m m' b ofs k p,
  Mem.free_list m fbl = Some m' ->
  Mem.perm m' b ofs k p ->
  Mem.perm m b ofs k p.
Proof.
  induction fbl; simpl; intros until p.
  congruence.
  destruct a as [[b' lo] hi]. case_eq (Mem.free m b' lo hi); try congruence.
  intros. eauto with mem.
Qed.

Lemma nextblock_freelist:
  forall fbl m m',
  Mem.free_list m fbl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction fbl; intros until m'; simpl.
  congruence.
  destruct a as [[b lo] hi].
  case_eq (Mem.free m b lo hi); intros; try congruence.
  transitivity (Mem.nextblock m0). eauto. eapply Mem.nextblock_free; eauto.
Qed.

Lemma free_list_freeable:
  forall l m m',
  Mem.free_list m l = Some m' ->
  forall b lo hi,
  In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  revert H. destruct a as [[b' lo'] hi'].
  caseEq (Mem.free m b' lo' hi'); try congruence.
  intros m1 FREE1 FREE2.
  destruct H0. inv H.
  eauto with mem.
  red; intros. eapply Mem.perm_free_3; eauto. exploit IHl; eauto.
Qed.

Lemma nextblock_storev:
  forall chunk m addr v m',
  Mem.storev chunk m addr v = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold Mem.storev; intros. destruct addr; try discriminate.
  eapply Mem.nextblock_store; eauto.
Qed.

(** * Correspondence between C#minor's and Cminor's environments and memory states *)

(** In C#minor, every variable is stored in a separate memory block.
  In the corresponding Cminor code, these variables become sub-blocks
  of the stack data block.  We capture these changes in memory via a
  memory injection [f]:
  [f b = Some(b', ofs)] means that C#minor block [b] corresponds
  to a sub-block of Cminor block [b] at offset [ofs].

  A memory injection [f] defines a relation [Val.inject f] between
  values and a relation [Mem.inject f] between memory states.  These
  relations will be used intensively in our proof of simulation
  between C#minor and Cminor executions. *)

(** ** Matching between Cshaprminor's temporaries and Cminor's variables *)

Definition match_temps (f: meminj) (le: Csharpminor_memsem.temp_env) (te: env) : Prop :=
  forall id v, le!id = Some v -> exists v', te!(id) = Some v' /\ Val.inject f v v'.

Lemma match_temps_invariant:
  forall f f' le te,
  match_temps f le te ->
  inject_incr f f' ->
  match_temps f' le te.
Proof.
  intros; red; intros. destruct (H _ _ H1) as [v' [A B]]. exists v'; eauto.
Qed.

Lemma match_temps_assign:
  forall f le te id v tv,
  match_temps f le te ->
  Val.inject f v tv ->
  match_temps f (PTree.set id v le) (PTree.set id tv te).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  inv H1. exists tv; auto.
  eauto.
Qed.

(** ** Matching between C#minor's variable environment and Cminor's stack pointer *)

Inductive match_var (f: meminj) (sp: block): option (block * Z) -> option Z -> Prop :=
  | match_var_local: forall b sz ofs,
      Val.inject f (Vptr b Int.zero) (Vptr sp (Int.repr ofs)) ->
      match_var f sp (Some(b, sz)) (Some ofs)
  | match_var_global:
      match_var f sp None None.

(** Matching between a C#minor environment [e] and a Cminor
  stack pointer [sp]. The [lo] and [hi] parameters delimit the range
  of addresses for the blocks referenced from [te]. *)

Record match_env (f: meminj) (cenv: compilenv)
                 (e: Csharpminor_memsem.env) (sp: block)
                 (lo hi: block) : Prop :=
  mk_match_env {

(** C#minor local variables match sub-blocks of the Cminor stack data block. *)
    me_vars:
      forall id, match_var f sp (e!id) (cenv!id);

(** [lo, hi] is a proper interval. *)
    me_low_high:
      Ple lo hi;

(** Every block appearing in the C#minor environment [e] must be
  in the range [lo, hi]. *)
    me_bounded:
      forall id b sz, PTree.get id e = Some(b, sz) -> Ple lo b /\ Plt b hi;

(** All blocks mapped to sub-blocks of the Cminor stack data must be
    images of variables from the C#minor environment [e] *)
    me_inv:
      forall b delta,
      f b = Some(sp, delta) ->
      exists id, exists sz, PTree.get id e = Some(b, sz);

(** All C#minor blocks below [lo] (i.e. allocated before the blocks
  referenced from [e]) must map to blocks that are below [sp]
  (i.e. allocated before the stack data for the current Cminor function). *)
    me_incr:
      forall b tb delta,
      f b = Some(tb, delta) -> Plt b lo -> Plt tb sp
  }.

Ltac geninv x :=
  let H := fresh in (generalize x; intro H; inv H).

Lemma match_env_invariant:
  forall f1 cenv e sp lo hi f2,
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  (forall b delta, f2 b = Some(sp, delta) -> f1 b = Some(sp, delta)) ->
  (forall b, Plt b lo -> f2 b = f1 b) ->
  match_env f2 cenv e sp lo hi.
Proof.
  intros. destruct H. constructor; auto.
(* vars *)
  intros. geninv (me_vars0 id); econstructor; eauto.
(* bounded *)
  intros. eauto.
(* below *)
  intros. rewrite H2 in H; eauto.
Qed.

(** [match_env] and external calls *)

Remark inject_incr_separated_same:
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b, Mem.valid_block m1 b -> f2 b = f1 b.
Proof.
  intros. case_eq (f1 b).
  intros [b' delta] EQ. apply H; auto.
  intros EQ. case_eq (f2 b).
  intros [b'1 delta1] EQ1. exploit H0; eauto. intros [C D]. contradiction.
  auto.
Qed.

Remark inject_incr_separated_same':
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b b' delta,
  f2 b = Some(b', delta) -> Mem.valid_block m1' b' -> f1 b = Some(b', delta).
Proof.
  intros. case_eq (f1 b).
  intros [b'1 delta1] EQ. exploit H; eauto. congruence.
  intros. exploit H0; eauto. intros [C D]. contradiction.
Qed.

Lemma match_env_external_call:
  forall f1 cenv e sp lo hi f2 m1 m1',
  match_env f1 cenv e sp lo hi ->
  inject_incr f1 f2 ->
  inject_separated f1 f2 m1 m1' ->
  Ple hi (Mem.nextblock m1) -> Plt sp (Mem.nextblock m1') ->
  match_env f2 cenv e sp lo hi.
Proof.
  intros. apply match_env_invariant with f1; auto.
  intros. eapply inject_incr_separated_same'; eauto.
  intros. eapply inject_incr_separated_same; eauto. red. destruct H. xomega.
Qed.

(** [match_env] and allocations *)

Lemma match_env_alloc:
  forall f1 id cenv e sp lo m1 sz m2 b ofs f2,
  match_env f1 (PTree.remove id cenv) e sp lo (Mem.nextblock m1) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  match_env f2 cenv (PTree.set id (b, sz) e) sp lo (Mem.nextblock m2).
Proof.
  intros until f2; intros ME ALLOC CENV INCR SAME OTHER ENV.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  inv ME; constructor.
(* vars *)
  intros. rewrite PTree.gsspec. destruct (peq id0 id).
  (* the new var *)
  subst id0. rewrite CENV. constructor. econstructor. eauto.
  rewrite Int.add_commut; rewrite Int.add_zero; auto.
  (* old vars *)
  generalize (me_vars0 id0). rewrite PTree.gro; auto. intros M; inv M.
  constructor; eauto.
  constructor.
(* low-high *)
  rewrite NEXTBLOCK; xomega.
(* bounded *)
  intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inv H. rewrite NEXTBLOCK; xomega.
  exploit me_bounded0; eauto. rewrite NEXTBLOCK; xomega.
(* inv *)
  intros. destruct (eq_block b (Mem.nextblock m1)).
  subst b. rewrite SAME in H; inv H. exists id; exists sz. apply PTree.gss.
  rewrite OTHER in H; auto. exploit me_inv0; eauto.
  intros [id1 [sz1 EQ]]. exists id1; exists sz1. rewrite PTree.gso; auto. congruence.
(* incr *)
  intros. rewrite OTHER in H. eauto. unfold block in *; xomega.
Qed.

(** The sizes of blocks appearing in [e] are respected. *)

Definition match_bounds (e: Csharpminor_memsem.env) (m: mem) : Prop :=
  forall id b sz ofs p,
  PTree.get id e = Some(b, sz) -> Mem.perm m b ofs Max p -> 0 <= ofs < sz.

Lemma match_bounds_invariant:
  forall e m1 m2,
  match_bounds e m1 ->
  (forall id b sz ofs p,
   PTree.get id e = Some(b, sz) -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  match_bounds e m2.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

(** ** Permissions on the Cminor stack block *)

(** The parts of the Cminor stack data block that are not images of
    C#minor local variable blocks remain freeable at all times. *)

Inductive is_reachable_from_env (f: meminj) (e: Csharpminor_memsem.env) (sp: block) (ofs: Z) : Prop :=
  | is_reachable_intro: forall id b sz delta,
      e!id = Some(b, sz) ->
      f b = Some(sp, delta) ->
      delta <= ofs < delta + sz ->
      is_reachable_from_env f e sp ofs.

Definition padding_freeable (f: meminj) (e: Csharpminor_memsem.env) (tm: mem) (sp: block) (sz: Z) : Prop :=
  forall ofs,
  0 <= ofs < sz -> Mem.perm tm sp ofs Cur Freeable \/ is_reachable_from_env f e sp ofs.

Lemma padding_freeable_invariant:
  forall f1 e tm1 sp sz cenv lo hi f2 tm2,
  padding_freeable f1 e tm1 sp sz ->
  match_env f1 cenv e sp lo hi ->
  (forall ofs, Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, Plt b hi -> f2 b = f1 b) ->
  padding_freeable f2 e tm2 sp sz.
Proof.
  intros; red; intros.
  exploit H; eauto. intros [A | A].
  left; auto.
  right. inv A. exploit me_bounded; eauto. intros [D E].
  econstructor; eauto. rewrite H2; auto.
Qed.

(** Decidability of the [is_reachable_from_env] predicate. *)

Lemma is_reachable_from_env_dec:
  forall f e sp ofs, is_reachable_from_env f e sp ofs \/ ~is_reachable_from_env f e sp ofs.
Proof.
  intros.
  set (pred := fun id_b_sz : ident * (block * Z) =>
                 match id_b_sz with
                 | (id, (b, sz)) =>
                      match f b with
                           | None => false
                           | Some(sp', delta) =>
                               if eq_block sp sp'
                               then zle delta ofs && zlt ofs (delta + sz)
                               else false
                      end
                 end).
  destruct (List.existsb pred (PTree.elements e)) eqn:?.
  (* yes *)
  rewrite List.existsb_exists in Heqb.
  destruct Heqb as [[id [b sz]] [A B]].
  simpl in B. destruct (f b) as [[sp' delta] |] eqn:?; try discriminate.
  destruct (eq_block sp sp'); try discriminate.
  destruct (andb_prop _ _ B).
  left. apply is_reachable_intro with id b sz delta.
  apply PTree.elements_complete; auto.
  congruence.
  split; eapply proj_sumbool_true; eauto.
  (* no *)
  right; red; intro NE; inv NE.
  assert (existsb pred (PTree.elements e) = true).
  rewrite List.existsb_exists. exists (id, (b, sz)); split.
  apply PTree.elements_correct; auto.
  simpl. rewrite H0. rewrite dec_eq_true.
  unfold proj_sumbool. destruct H1. rewrite zle_true; auto. rewrite zlt_true; auto.
  congruence.
Qed.

(** * Correspondence between global environments *)

(** Global environments match if the memory injection [f] leaves unchanged
  the references to global symbols and functions. *)

Inductive match_globalenvs (f: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Remark inj_preserves_globals:
  forall f hi,
  match_globalenvs f hi ->
  meminj_preserves_globals ge f.
Proof.
  intros. inv H.
  split. intros. apply DOMAIN. eapply SYMBOLS. eauto.
  split. intros. apply DOMAIN. eapply VARINFOS. eauto.
  intros. symmetry. eapply IMAGE; eauto.
Qed.

(** * Invariant on abstract call stacks  *)

(** Call stacks represent abstractly the execution state of the current
  C#minor and Cminor functions, as well as the states of the
  calling functions.  A call stack is a list of frames, each frame
  collecting information on the current execution state of a C#minor
  function and its Cminor translation. *)

Inductive frame : Type :=
  Frame(cenv: compilenv)
       (tf: Cminor_memsem.function)
       (e: Csharpminor_memsem.env)
       (le: Csharpminor_memsem.temp_env)
       (te: Cminor_memsem.env)
       (sp: block)
       (lo hi: block).

Definition callstack : Type := list frame.

(** Matching of call stacks imply:
- matching of environments for each of the frames
- matching of the global environments
- separation conditions over the memory blocks allocated for C#minor local variables;
- separation conditions over the memory blocks allocated for Cminor stack data;
- freeable permissions on the parts of the Cminor stack data blocks
  that are not images of C#minor local variable blocks.
*)

(*CompComp adaptation: introduced L, TL, ensure that sp is local in TGT.
  Enforce that global blocks are not local, and expose hi (parameter h), so that 
  globals-not-local can be preserved in (new) Lemma match_callstack_sub below *)
Inductive match_callstack (L TL: block -> bool) (f: meminj) (m: mem) (tm: mem):
                          (*new parameter "h"*)block -> 
                           callstack -> block -> block -> Prop :=
  | mcs_nil:
      forall hi bound tbound
      (*new*) (Hhi: forall b (Hb: Plt b hi), L b = false /\ TL b = false)
      (*new*) (HiSrc: Ple hi (Mem.nextblock m))
      (*new*) (HiTgt: Ple hi (Mem.nextblock tm)),
      match_globalenvs f hi ->
      Ple hi bound -> Ple hi tbound ->
      match_callstack L TL f m tm hi nil bound tbound
  | mcs_cons:
      forall cenv tf e le te sp lo hi cs bound tbound h
        (BOUND: Ple hi bound)
        (TBOUND: Plt sp tbound)
        (MTMP: match_temps f le te)
        (MENV: match_env f cenv e sp lo hi)
        (BOUND: match_bounds e m)
        (PERM: padding_freeable f e tm sp tf.(fn_stackspace))
        (MCS: match_callstack L TL f m tm h cs lo sp)
        (Hsp: TL sp = true),
      match_callstack L TL f m tm h (Frame cenv tf e le te sp lo hi :: cs) bound tbound.

Lemma match_callstack_sub:
  forall L TL f m tm h cs bnd tbnd
  (MS: match_callstack L TL f m tm h cs bnd tbnd)
  K (HK: forall b, (L b = true -> K b = true) /\
                   (Plt b h -> K b = false))
  TK (HTK: forall b, (TL b = true -> TK b = true)/\
                     (Plt b h -> TK b = false)),
  match_callstack K TK f m tm h cs bnd tbnd.
Proof. induction 1; simpl; intros.
+ econstructor; try eassumption.
  intros b Hb; specialize (HK b); specialize (HTK b).
  destruct HK; destruct HTK. split; eauto.
+ econstructor; eauto. eapply HTK; trivial.
Qed.

(** [match_callstack] implies [match_globalenvs]. *)

(*CompComp adaptation: added assertion about globals blocks not being local, 
  expose additional knowledge about h*)
Lemma match_callstack_match_globalenvs:
  forall L TL hi f m tm cs bound tbound,
  match_callstack L TL f m tm hi cs bound tbound ->
  match_globalenvs f hi /\ Ple hi bound /\ Ple hi tbound /\ Ple hi (Mem.nextblock m) /\ Ple hi (Mem.nextblock tm) /\
  forall b (Hb: Plt b hi), L b = false /\ TL b = false.
Proof.
  induction 1; eauto. intuition. destruct IHmatch_callstack as [? [? [? [? [? ?]]]]].
  intuition. inv MENV. xomega. xomega. 
Qed.

(** Invariance properties for [match_callstack]. *)

Lemma match_callstack_invariant:
  forall L TL h f1 m1 tm1 f2 m2 tm2 cs bound tbound,
  match_callstack L TL f1 m1 tm1 h cs bound tbound ->
  forall (*NEW*) (VB: Ple (Mem.nextblock m1) (Mem.nextblock m2))
         (*NEW*) (TVB: Ple (Mem.nextblock tm1) (Mem.nextblock tm2)),
  inject_incr f1 f2 ->
  (forall b ofs p, Plt b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall sp ofs, Plt sp tbound -> Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, Plt b bound -> f2 b = f1 b) ->
  (forall b b' delta, f2 b = Some(b', delta) -> Plt b' tbound -> f1 b = Some(b', delta)) ->
  match_callstack L TL f2 m2 tm2 h cs bound tbound.
Proof.
  induction 1; intros.
+ (* base case *)
  econstructor; eauto; try xomega.
  inv H. constructor; intros; eauto.
  eapply IMAGE; eauto. eapply H6; eauto. xomega.
+ (* inductive case *)
  assert (Ple lo hi) by (eapply me_low_high; eauto).
  econstructor; eauto.
  eapply match_temps_invariant; eauto.
  eapply match_env_invariant; eauto.
    intros. apply H3. xomega.
  eapply match_bounds_invariant; eauto.
    intros. eapply H1; eauto.
    exploit me_bounded; eauto. xomega.
  eapply padding_freeable_invariant; eauto.
    intros. apply H3. xomega.
  eapply IHmatch_callstack; eauto.
    intros. eapply H1; eauto. xomega.
    intros. eapply H2; eauto. xomega.
    intros. eapply H3; eauto. xomega.
    intros. eapply H4; eauto. xomega.
Qed.

Lemma match_callstack_incr_bound:
  forall L TL h f m tm cs bound tbound bound' tbound',
  match_callstack L TL f m tm h cs bound tbound ->
  Ple bound bound' -> Ple tbound tbound' ->
  match_callstack L TL f m tm h cs bound' tbound'.
Proof.
  intros. inv H.
  econstructor; eauto. xomega. xomega.
  constructor; auto. xomega. xomega.
Qed.

(** Assigning a temporary variable. *)

Lemma match_callstack_set_temp:
  forall L TL h f cenv e le te sp lo hi cs bound tbound m tm tf id v tv,
  Val.inject f v tv ->
  match_callstack L TL f m tm h (Frame cenv tf e le te sp lo hi :: cs) bound tbound ->
  match_callstack L TL f m tm h (Frame cenv tf e (PTree.set id v le) (PTree.set id tv te) sp lo hi :: cs) bound tbound.
Proof.
  intros. inv H0. constructor; auto.
  eapply match_temps_assign; eauto.
Qed.

(** Preservation of [match_callstack] by freeing all blocks allocated
  for local variables at function entry (on the C#minor side)
  and simultaneously freeing the Cminor stack data block. *)

Lemma in_blocks_of_env:
  forall e id b sz,
  e!id = Some(b, sz) -> In (b, 0, sz) (blocks_of_env e).
Proof.
  unfold blocks_of_env; intros.
  change (b, 0, sz) with (block_of_binding (id, (b, sz))).
  apply List.in_map. apply PTree.elements_correct. auto.
Qed.

Lemma in_blocks_of_env_inv:
  forall b lo hi e,
  In (b, lo, hi) (blocks_of_env e) ->
  exists id, e!id = Some(b, hi) /\ lo = 0.
Proof.
  unfold blocks_of_env; intros.
  exploit list_in_map_inv; eauto. intros [[id [b' sz]] [A B]].
  unfold block_of_binding in A. inv A.
  exists id; intuition. apply PTree.elements_complete. auto.
Qed.

Lemma match_callstack_freelist:
  forall L TL h f cenv tf e le te sp lo hi cs m m' tm,
  Mem.inject f m tm ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  match_callstack L TL f m tm h (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  exists tm',
  Mem.free tm sp 0 tf.(fn_stackspace) = Some tm'
  /\ match_callstack L TL f m' tm' h cs (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f m' tm'.
Proof.
  intros until tm; intros INJ FREELIST MCS. inv MCS. inv MENV.
  assert ({tm' | Mem.free tm sp 0 (fn_stackspace tf) = Some tm'}).
  apply Mem.range_perm_free.
  red; intros.
  exploit PERM; eauto. intros [A | A].
  auto.
  inv A. assert (Mem.range_perm m b 0 sz Cur Freeable).
  eapply free_list_freeable; eauto. eapply in_blocks_of_env; eauto.
  replace ofs with ((ofs - delta) + delta) by omega.
  eapply Mem.perm_inject; eauto. apply H3. omega.
  destruct X as  [tm' FREE].
  exploit nextblock_freelist; eauto. intro NEXT.
  exploit Mem.nextblock_free; eauto. intro NEXT'.
  exists tm'. split. auto. split.
+ rewrite NEXT; rewrite NEXT'.
  apply match_callstack_incr_bound with lo sp; try omega.
  - apply match_callstack_invariant with f m tm; auto.
    rewrite NEXT; xomega. rewrite NEXT'; xomega.
    intros. eapply perm_freelist; eauto.
    intros. eapply Mem.perm_free_1; eauto. left; unfold block; xomega.
  - xomega. - xomega.
+ eapply Mem.free_inject; eauto.
  intros. exploit me_inv0; eauto. intros [id [sz A]].
  exists 0; exists sz; split.
  eapply in_blocks_of_env; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_max. eauto.
Qed.

Require Import sepcomp.mem_lemmas.
Require Import minisepcomp.mini_simulations. 

(** Preservation of [match_callstack] by external calls. *)
Lemma match_callstack_external_call_ext:
  forall L TL h f1 f2 m1 m2 m1' m2'
  (*NEW*) (VB: Ple (Mem.nextblock m1) (Mem.nextblock m2))
  (*New*) (GE2: Ple (Genv.genv_next tge) h)
  (*NEW*) (TVB: Ple (Mem.nextblock m1') (Mem.nextblock m2')),
  Mem.unchanged_on (fun b1 _ => L b1 = true /\ f1 b1 = None) m1 m2 ->
  Mem.unchanged_on (BuiltinEffects.o_o_reach f1 TL m1) m1' m2' ->
  mini_extern_incr f1 f2 L TL ->
(*  (forall b1 b2 delta, f1 b1 = None -> f2 b1 = Some (b2, delta) -> Plt b2 h -> Plt b1 h) ->*)
(*  inject_separated f1 f2 m1 m1' ->*)  globals_separate ge tge f1 f2 ->
  (forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  forall cs bound tbound,
  match_callstack L TL f1 m1 m1' h cs bound tbound ->
  (*new*)(forall b, Plt b h -> f2 b = f1 b) ->
  (*new*)(forall b b' delta, f2 b = Some(b', delta) -> Plt b' h -> f1 b = Some(b', delta)) ->
  Ple bound (Mem.nextblock m1) -> Ple tbound (Mem.nextblock m1') ->
  match_callstack L TL f2 m2 m2' h cs bound tbound.
Proof.
  intros until m2'.
  intros VB GE2 TVB UNMAPPED OUTOFREACH [INCR SEPARATED] GSEP MAXPERMS.
  induction 1; intros.
+ (* base case *)
  apply mcs_nil (*with hi*); auto; try xomega.
  inv H. constructor; auto.
  intros. case_eq (f1 b1).
  intros [b2' delta'] EQ. rewrite (INCR _ _ _ EQ) in H. inv H. eauto.
  intro EQ. rewrite (H3 _ _ _ H) in EQ. discriminate. xomega. 
     
+ (* inductive case *)
  constructor. - auto. - auto.
  - eapply match_temps_invariant; eauto.
  - eapply match_env_invariant; eauto.
    exploit match_callstack_match_globalenvs; eauto. intros [MG [A1 [A2 [A3 [A4 A5]]]]].
    (*red in SEPARATED.*) intros. destruct (f1 b) as [[b' delta']|] eqn:?.
    * exploit INCR; eauto. intros. rewrite H5 in H4; trivial. (* congruence.*)
    * rewrite H0 in H4. congruence. inv MENV. xomega. (* elim B. red. xomega.
      intros. assert (Ple lo hi) by (eapply me_low_high; eauto).
      destruct (f1 b) as [[b' delta']|] eqn:?.
      apply INCR; auto.
      destruct (f2 b) as [[b' delta']|] eqn:?; auto.
      exploit SEPARATED; eauto. intros [A B]. elim A. red. xomega.*)
  - eapply match_bounds_invariant; eauto.
    intros. eapply MAXPERMS; eauto. red. exploit me_bounded; eauto. xomega.
  - (* padding-freeable *)
    red; intros.
    destruct (is_reachable_from_env_dec f1 e sp ofs).
    inv H5. right. apply is_reachable_intro with id b sz delta; auto.
    exploit PERM; eauto. intros [A|A]; try contradiction.
    left. eapply Mem.perm_unchanged_on; eauto. 
    { split; trivial. intros. intros N. elim H5.
      exploit me_inv; eauto. intros [id [lv B]].
      exploit BOUND0; eauto. intros C.
      apply is_reachable_intro with id b1 lv delta; auto; omega. }
  - (* induction *)
    eapply IHmatch_callstack; eauto.
    intros; apply H0. inv MENV; xomega.
    intros. apply (H1 _ _ _ H4).  xomega.
    inv MENV; xomega. xomega.
  - trivial.
Qed. 
Lemma match_callstack_builtin:
  forall L TL h f1 f2 m1 m2 m1' m2'
  (*NEW*) (VB: Ple (Mem.nextblock m1) (Mem.nextblock m2))
  (*NEW*) (TVB: Ple (Mem.nextblock m1') (Mem.nextblock m2')),
  Mem.unchanged_on (loc_unmapped f1) m1 m2 ->
  Mem.unchanged_on (loc_out_of_reach f1 m1) m1' m2' ->
  inject_incr f1 f2 ->
  inject_separated f1 f2 m1 m1' ->
  (forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  forall cs bound tbound,
  match_callstack L TL f1 m1 m1' h cs bound tbound ->
  Ple bound (Mem.nextblock m1) -> Ple tbound (Mem.nextblock m1') ->
  match_callstack L TL f2 m2 m2' h cs bound tbound.
Proof.
  intros until m2'.
  intros VB TVB UNMAPPED OUTOFREACH INCR SEPARATED MAXPERMS.
  induction 1; intros.
+ (* base case *)
  apply mcs_nil (*with hi*); auto; try xomega.
  inv H. constructor; auto.
  intros. case_eq (f1 b1).
  intros [b2' delta'] EQ. rewrite (INCR _ _ _ EQ) in H. inv H. eauto.
  intro EQ. exploit SEPARATED; eauto. intros [A B]. elim B. red. xomega.
+ (* inductive case *)
  constructor. auto. auto.
  eapply match_temps_invariant; eauto.
  eapply match_env_invariant; eauto.
  red in SEPARATED. intros. destruct (f1 b) as [[b' delta']|] eqn:?.
  exploit INCR; eauto. congruence.
  exploit SEPARATED; eauto. intros [A B]. elim B. red. xomega.
  intros. assert (Ple lo hi) by (eapply me_low_high; eauto).
  destruct (f1 b) as [[b' delta']|] eqn:?.
  apply INCR; auto.
  destruct (f2 b) as [[b' delta']|] eqn:?; auto.
  exploit SEPARATED; eauto. intros [A B]. elim A. red. xomega.
  eapply match_bounds_invariant; eauto.
  intros. eapply MAXPERMS; eauto. red. exploit me_bounded; eauto. xomega.
  (* padding-freeable *)
  red; intros.
  destruct (is_reachable_from_env_dec f1 e sp ofs).
  inv H3. right. apply is_reachable_intro with id b sz delta; auto.
  exploit PERM; eauto. intros [A|A]; try contradiction.
  left. eapply Mem.perm_unchanged_on; eauto.
  red; intros; red; intros. elim H3.
  exploit me_inv; eauto. intros [id [lv B]].
  exploit BOUND0; eauto. intros C.
  apply is_reachable_intro with id b0 lv delta; auto; omega.
  eauto with mem.
  (* induction *)
  eapply IHmatch_callstack; eauto. inv MENV; xomega. xomega. trivial.
Qed.

(** [match_callstack] and allocations *)

Lemma match_callstack_alloc_right:
  forall L TL h f m tm cs tf tm' sp le te cenv,
  match_callstack L TL f m tm h cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  Mem.inject f m tm ->
  match_temps f le te ->
  (forall id, cenv!id = None) ->
  match_callstack L (fun b => TL b || (eq_block sp b)) f m tm' h
      (Frame cenv tf empty_env le te sp (Mem.nextblock m) (Mem.nextblock m) :: cs)
      (Mem.nextblock m) (Mem.nextblock tm').
Proof.
  intros.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  constructor.
  xomega.
  unfold block in *; xomega.
  auto.
  constructor; intros.
    rewrite H3. rewrite PTree.gempty. constructor.
    xomega.
    rewrite PTree.gempty in H4; discriminate.
    eelim Mem.fresh_block_alloc; eauto. eapply Mem.valid_block_inject_2; eauto.
    rewrite RES. change (Mem.valid_block tm tb). eapply Mem.valid_block_inject_2; eauto.
  red; intros. rewrite PTree.gempty in H4. discriminate.
  red; intros. left. eapply Mem.perm_alloc_2; eauto.
  + eapply match_callstack_invariant with (tm1 := tm); eauto; try xomega.
    exploit match_callstack_match_globalenvs; eauto. intros [MG [VB1 [VB2 [VB3 [VB4 HH]]]]].
    rewrite RES; auto. eapply match_callstack_sub; try eassumption. split; intros; trivial. apply HH; trivial.
    intros; split; intros Hb. rewrite Hb; trivial. destruct (HH _ Hb) as [Hl Ht]; rewrite Ht; simpl.
            subst. apply Mem.fresh_block_alloc in H0. destruct (eq_block (Mem.nextblock tm) b); trivial. subst. elim H0. unfold Mem.valid_block; xomega.
            rewrite NEXTBLOCK. xomega. 
    intros. eapply Mem.perm_alloc_1; eauto.
  + destruct (eq_block sp sp). apply orb_true_r. elim n; trivial.
Qed.

Lemma match_callstack_alloc_left:
  forall L TL h f1 m1 tm id cenv tf e le te sp lo cs sz m2 b f2 ofs,
  match_callstack L TL f1 m1 tm h
    (Frame (PTree.remove id cenv) tf e le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  match_callstack L TL f2 m2 tm h
    (Frame cenv tf (PTree.set id (b, sz) e) le te sp lo (Mem.nextblock m2) :: cs)
    (Mem.nextblock m2) (Mem.nextblock tm).
Proof.
  intros. inv H.
  exploit Mem.nextblock_alloc; eauto. intros NEXTBLOCK.
  exploit Mem.alloc_result; eauto. intros RES.
  assert (LO: Ple lo (Mem.nextblock m1)) by (eapply me_low_high; eauto).
  constructor.
  xomega.
  auto.
  eapply match_temps_invariant; eauto.
  eapply match_env_alloc; eauto.
  red; intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inversion H. subst b0 sz0 id0. eapply Mem.perm_alloc_3; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_alloc_4; eauto.
  exploit me_bounded; eauto. unfold block in *; xomega.
  red; intros. exploit PERM; eauto. intros [A|A]. auto. right.
  inv A. apply is_reachable_intro with id0 b0 sz0 delta; auto.
  rewrite PTree.gso. auto. congruence.
  eapply match_callstack_invariant with (m1 := m1); eauto; try xomega. rewrite NEXTBLOCK; xomega.
  intros. eapply Mem.perm_alloc_4; eauto.
  unfold block in *; xomega.
  intros. apply H4. unfold block in *; xomega.
  intros. destruct (eq_block b0 b).
  subst b0. rewrite H3 in H. inv H. xomegaContradiction.
  rewrite H4 in H; auto. trivial.
Qed.

(** * Correctness of stack allocation of local variables *)

(** This section shows the correctness of the translation of Csharpminor
  local variables as sub-blocks of the Cminor stack data.  This is the most difficult part of the proof. *)

Definition cenv_remove (cenv: compilenv) (vars: list (ident * Z)) : compilenv :=
  fold_right (fun id_lv ce => PTree.remove (fst id_lv) ce) cenv vars.

Remark cenv_remove_gso:
  forall id vars cenv,
  ~In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = PTree.get id cenv.
Proof.
  induction vars; simpl; intros.
  auto.
  rewrite PTree.gro. apply IHvars. intuition. intuition.
Qed.

Remark cenv_remove_gss:
  forall id vars cenv,
  In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = None.
Proof.
  induction vars; simpl; intros.
  contradiction.
  rewrite PTree.grspec. destruct (PTree.elt_eq id (fst a)). auto.
  destruct H. intuition. eauto.
Qed.

Definition cenv_compat (cenv: compilenv) (vars: list (ident * Z)) (tsz: Z) : Prop :=
  forall id sz,
  In (id, sz) vars ->
  exists ofs,
      PTree.get id cenv = Some ofs
   /\ Mem.inj_offset_aligned ofs sz
   /\ 0 <= ofs
   /\ ofs + Zmax 0 sz <= tsz.

Definition cenv_separated (cenv: compilenv) (vars: list (ident * Z)) : Prop :=
  forall id1 sz1 ofs1 id2 sz2 ofs2,
  In (id1, sz1) vars -> In (id2, sz2) vars ->
  PTree.get id1 cenv = Some ofs1 -> PTree.get id2 cenv = Some ofs2 ->
  id1 <> id2 ->
  ofs1 + sz1 <= ofs2 \/ ofs2 + sz2 <= ofs1.

Definition cenv_mem_separated (cenv: compilenv) (vars: list (ident * Z)) (f: meminj) (sp: block) (m: mem) : Prop :=
  forall id sz ofs b delta ofs' k p,
  In (id, sz) vars -> PTree.get id cenv = Some ofs ->
  f b = Some (sp, delta) ->
  Mem.perm m b ofs' k p ->
  ofs <= ofs' + delta < sz + ofs -> False.

Require Import sepcomp.mem_lemmas.
Require Import minisepcomp.mini_simulations.
Require Import minisepcomp.mini_simulations_lemmas.

(*CompComp adaptation: two new hypotheses, and two new conclusions.
  In the process, also correct the SrcLocal-set of the match_callstack conclusion, to be 
  (fun b : block => L b || freshblock m1 m2 b) rather than L*)
Lemma match_callstack_alloc_variables_rec:
  forall L TL h tm sp tf cenv le te lo cs
  (*new hypotheses: *)(GE1: Ple (Genv.genv_next ge) h) (GE2: Ple (Genv.genv_next tge) h),
  Mem.valid_block tm sp ->
  fn_stackspace tf <= Int.max_unsigned ->
  (forall ofs k p, Mem.perm tm sp ofs k p -> 0 <= ofs < fn_stackspace tf) ->
  (forall ofs k p, 0 <= ofs < fn_stackspace tf -> Mem.perm tm sp ofs k p) ->
  forall e1 m1 vars e2 m2,
  alloc_variables e1 m1 vars e2 m2 ->
  forall f1,
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace tf) ->
  cenv_separated cenv vars ->
  cenv_mem_separated cenv vars f1 sp m1 ->
  (forall id sz, In (id, sz) vars -> e1!id = None) ->
  match_callstack L TL f1 m1 tm h
    (Frame (cenv_remove cenv vars) tf e1 le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.inject f1 m1 tm ->
  exists f2,
    match_callstack (fun b : block => L b || freshblock m1 m2 b) TL f2 m2 tm h
      (Frame cenv tf e2 le te sp lo (Mem.nextblock m2) :: cs)
      (Mem.nextblock m2) (Mem.nextblock tm)
  /\ Mem.inject f2 m2 tm
  /\ (*new*) mini_intern_incr f1 f2 (fun b : block => L b || freshblock m1 m2 b) TL
  /\ (*new*) globals_separate ge tge f1 f2.
Proof.
  specialize mini_intern_incr_same_meminj; intros INC_SAME.
  specialize (globals_separate_same_meminj ge tge); intros GSEP_SAME.
  intros until cs; intros GE1 GE2 VALID REPRES STKSIZE STKPERMS.
  induction 1; intros f1 NOREPET COMPAT SEP1 SEP2 UNBOUND MCS MINJ.
  (* base case *)
+ simpl in MCS. exists f1; intuition.
  exploit match_callstack_match_globalenvs. eapply MCS. intros [_ [_ [_ [_ [_ ?]]]]]. 
  eapply match_callstack_sub; try eassumption.
  rewrite freshblock_irrefl'.
  intros; split; intros. rewrite H0; trivial. destruct (H _ H0) as [A _]; rewrite A; trivial.
  intros; split; intros; trivial. destruct (H _ H0); trivial.
+  (* inductive case *)
  simpl in NOREPET. inv NOREPET.
(* exploit Mem.alloc_result; eauto. intros RES.
  exploit Mem.nextblock_alloc; eauto. intros NB.*)
  exploit (COMPAT id sz). auto with coqlib. intros [ofs [CENV [ALIGNED [LOB HIB]]]].
  exploit Mem.alloc_left_mapped_inject.
    eexact MINJ.
    eexact H.
    eexact VALID.
    instantiate (1 := ofs). zify. omega.
    intros. exploit STKSIZE; eauto. omega.
    intros. apply STKPERMS. zify. omega.
    replace (sz - 0) with sz by omega. auto.
    intros. eapply SEP2. eauto with coqlib. eexact CENV. eauto. eauto. omega.
  intros [f2 [A [B [C D]]]].
  exploit (IHalloc_variables f2); eauto.
    red; intros. eapply COMPAT. auto with coqlib.
    red; intros. eapply SEP1; eauto with coqlib.
    red; intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b b1); intros P.
    subst b. rewrite C in H5; inv H5.
    exploit SEP1. eapply in_eq. eapply in_cons; eauto. eauto. eauto.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    omega.
    eapply SEP2. apply in_cons; eauto. eauto.
    rewrite D in H5; eauto. eauto. auto.
    intros. rewrite PTree.gso. eapply UNBOUND; eauto with coqlib.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    eapply match_callstack_alloc_left; eauto.
    rewrite cenv_remove_gso; auto.
    apply UNBOUND with sz; auto with coqlib.
  (*new*) intros [f3 [MSTK [MEMINJ [[INCA INCB] SEP]]]].
     exists f3. split.
     - exploit match_callstack_match_globalenvs. eapply MCS. intros [MG [VM [VTM [_ [_ ZZ]]]]].
       eapply match_callstack_sub; try eassumption.
       * intros bb; split; intros. destruct (L bb); simpl in *; trivial. 
            apply freshblockProp_char in H1. apply freshblockProp_char. destruct H1. split; trivial. intros MM. elim H2. eapply Mem.valid_block_alloc; eauto.
            destruct (ZZ _ H1) as [AA BB]; rewrite AA; simpl. apply freshblock_charF. left. unfold Mem.valid_block; xomega.
       * intros bb; split; intros; trivial. apply ZZ; trivial.
     - split; trivial. split.
     { split. eapply inject_incr_trans; eauto.
       intros. specialize (D b0). destruct (eq_block b0 b1); subst.
       + clear D. specialize (INCA _ _ _ C). rewrite INCA in J'. symmetry in J'; inv J'.
         assert (freshblock m m2 b1 = true).
         { apply freshblockProp_char. split. eapply Mem.valid_block_inject_1. apply INCA. apply MEMINJ. apply (Mem.fresh_block_alloc _ _ _ _ _ H). }
         rewrite H1. split. apply orb_true_r. inv MCS; trivial.
       + rewrite <- (D n) in J. destruct (INCB _ _ _ J J'). split; trivial.
         destruct (L b0); trivial; simpl in *.
         unfold freshblock in H1. unfold freshblock. apply andb_true_iff in H1. apply andb_true_iff.
         destruct H1. split; trivial. destruct (valid_block_dec m b0); simpl; trivial.
         apply (Mem.valid_block_alloc _ _ _ _ _ H) in v. destruct (valid_block_dec m1 b0); try contradiction. inv H5. }
     { red; intros. specialize (D b0). destruct (eq_block b0 b1); subst.
       + clear D. specialize (INCA _ _ _ C). rewrite INCA in J'. symmetry in J'; inv J'. 
         split.
         - destruct (Plt_Ple_dec b1 (Genv.genv_next ge)); simpl; trivial.
           elim (Mem.fresh_block_alloc _ _ _ _ _ H). 
           exploit match_callstack_match_globalenvs. eapply MCS. intros [MG [VM [VTM [_ [_ ZZ]]]]].
           unfold Mem.valid_block. xomega.
         - exploit match_callstack_match_globalenvs. eapply MCS. intros [MG [VM [VTM [_ [_ ZZ]]]]].
           destruct (Plt_Ple_dec sp (Genv.genv_next tge)); simpl; trivial.
           inv MCS. exploit (ZZ sp). xomega. intros [_ X]; congruence.
       + rewrite <- (D n) in J. destruct (INCB _ _ _ J J') as [AA BB].
         split.
         - destruct (Plt_Ple_dec b0 (Genv.genv_next ge)); simpl; trivial.
           exploit match_callstack_match_globalenvs. eapply MCS. intros [MG [VM [VTM [_ [_ ZZ]]]]].
           destruct (ZZ b0) as [KK JJ]. xomega. rewrite KK in AA; simpl in AA.
           apply freshblockProp_char in AA. destruct AA. elim H2; clear H2.
           eapply Mem.valid_block_alloc. eauto. unfold Mem.valid_block; xomega.
         - destruct (Plt_Ple_dec b2 (Genv.genv_next tge)); simpl; trivial.
           clear INCB. 
           exploit match_callstack_match_globalenvs. eapply MCS. intros [MG [VM [VTM [_ [_ ZZ]]]]].
           destruct (ZZ b2). xomega. congruence. }
Qed.

(*CompComp adaptation: two new hypotheses, and two new conclusions*)
Lemma match_callstack_alloc_variables:
  forall L TL h tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te
  (*new hypotheses: *)(GE1: Ple (Genv.genv_next ge) h) (GE2: Ple (Genv.genv_next tge) h),
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Int.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  Mem.inject f1 m1 tm1 ->
  match_callstack L TL f1 m1 tm1 h cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps f1 le te ->
  exists f2,
    match_callstack (fun b => L b || freshblock m1 m2 b) 
                    (fun b => TL b || freshblock tm1 tm2 b)
                    f2 m2 tm2 h (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject f2 m2 tm2
  /\ (*new*) mini_intern_incr f1 f2 (fun b : block => L b || freshblock m1 m2 b) (fun b => TL b || freshblock tm1 tm2 b)
  /\ (*new*) globals_separate ge tge f1 f2.
Proof.
  intros.
  eapply match_callstack_alloc_variables_rec; eauto.
  eapply Mem.valid_new_block; eauto.
  intros. eapply Mem.perm_alloc_3; eauto.
  intros. apply Mem.perm_implies with Freeable; auto with mem. eapply Mem.perm_alloc_2; eauto.
  (*instantiate (1 := f1).*) red; intros. eelim Mem.fresh_block_alloc; eauto.
  eapply Mem.valid_block_inject_2; eauto.
  intros. apply PTree.gempty.
  { rewrite (freshblock_alloc _ _ _ _ _ H).
    exploit match_callstack_match_globalenvs; eauto. intros [MG [HH1 [HH2 [HH33 HH]]]].
    eapply match_callstack_alloc_right; eauto.
    intros. destruct (In_dec peq id (map fst vars)).
    apply cenv_remove_gss; auto.
    rewrite cenv_remove_gso; auto.
    destruct (cenv!id) as [ofs|] eqn:?; auto. elim n; eauto. }
  eapply Mem.alloc_right_inject; eauto.
Qed.

(** Properties of the compilation environment produced by [build_compilenv] *)

Remark block_alignment_pos:
  forall sz, block_alignment sz > 0.
Proof.
  unfold block_alignment; intros.
  destruct (zlt sz 2). omega.
  destruct (zlt sz 4). omega.
  destruct (zlt sz 8); omega.
Qed.

Remark assign_variable_incr:
  forall id sz cenv stksz cenv' stksz',
  assign_variable (cenv, stksz) (id, sz) = (cenv', stksz') -> stksz <= stksz'.
Proof.
  simpl; intros. inv H.
  generalize (align_le stksz (block_alignment sz) (block_alignment_pos sz)).
  assert (0 <= Zmax 0 sz). apply Zmax_bound_l. omega.
  omega.
Qed.

Remark assign_variables_incr:
  forall vars cenv sz cenv' sz',
  assign_variables (cenv, sz) vars = (cenv', sz') -> sz <= sz'.
Proof.
  induction vars; intros until sz'.
  simpl; intros. inv H. omega.
Opaque assign_variable.
  destruct a as [id s]. simpl. intros.
  destruct (assign_variable (cenv, sz) (id, s)) as [cenv1 sz1] eqn:?.
  apply Zle_trans with sz1. eapply assign_variable_incr; eauto. eauto.
Transparent assign_variable.
Qed.

Remark inj_offset_aligned_block:
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) sz.
Proof.
  intros; red; intros.
  apply Zdivides_trans with (block_alignment sz).
  unfold align_chunk.  unfold block_alignment.
  generalize Zone_divide; intro.
  generalize Zdivide_refl; intro.
  assert (2 | 4). exists 2; auto.
  assert (2 | 8). exists 4; auto.
  assert (4 | 8). exists 2; auto.
  destruct (zlt sz 2).
  destruct chunk; simpl in *; auto; omegaContradiction.
  destruct (zlt sz 4).
  destruct chunk; simpl in *; auto; omegaContradiction.
  destruct (zlt sz 8).
  destruct chunk; simpl in *; auto; omegaContradiction.
  destruct chunk; simpl; auto.
  apply align_divides. apply block_alignment_pos.
Qed.

Remark inj_offset_aligned_block':
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) (Zmax 0 sz).
Proof.
  intros.
  replace (block_alignment sz) with (block_alignment (Zmax 0 sz)).
  apply inj_offset_aligned_block.
  rewrite Zmax_spec. destruct (zlt sz 0); auto.
  transitivity 1. reflexivity. unfold block_alignment. rewrite zlt_true. auto. omega.
Qed.

Lemma assign_variable_sound:
  forall cenv1 sz1 id sz cenv2 sz2 vars,
  assign_variable (cenv1, sz1) (id, sz) = (cenv2, sz2) ->
  ~In id (map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ (id, sz) :: nil) sz2
  /\ cenv_separated cenv2 (vars ++ (id, sz) :: nil).
Proof.
  unfold assign_variable; intros until vars; intros ASV NOREPET POS COMPAT SEP.
  inv ASV.
  assert (LE: sz1 <= align sz1 (block_alignment sz)). apply align_le. apply block_alignment_pos.
  assert (EITHER: forall id' sz',
             In (id', sz') (vars ++ (id, sz) :: nil) ->
             In (id', sz') vars /\ id' <> id \/ (id', sz') = (id, sz)).
    intros. rewrite in_app in H. destruct H.
    left; split; auto. red; intros; subst id'. elim NOREPET.
    change id with (fst (id, sz')). apply in_map; auto.
    simpl in H. destruct H. auto. contradiction.
  split; red; intros.
  apply EITHER in H. destruct H as [[P Q] | P].
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  exists ofs.
  split. rewrite PTree.gso; auto.
  split. auto. split. auto. zify; omega.
  inv P. exists (align sz1 (block_alignment sz)).
  split. apply PTree.gss.
  split. apply inj_offset_aligned_block.
  split. omega.
  omega.
  apply EITHER in H; apply EITHER in H0.
  destruct H as [[P Q] | P]; destruct H0 as [[R S] | R].
  rewrite PTree.gso in *; auto. eapply SEP; eauto.
  inv R. rewrite PTree.gso in H1; auto. rewrite PTree.gss in H2; inv H2.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  assert (ofs = ofs1) by congruence. subst ofs.
  left. zify; omega.
  inv P. rewrite PTree.gso in H2; auto. rewrite PTree.gss in H1; inv H1.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  assert (ofs = ofs2) by congruence. subst ofs.
  right. zify; omega.
  congruence.
Qed.

Lemma assign_variables_sound:
  forall vars' cenv1 sz1 cenv2 sz2 vars,
  assign_variables (cenv1, sz1) vars' = (cenv2, sz2) ->
  list_norepet (map fst vars' ++ map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ vars') sz2 /\ cenv_separated cenv2 (vars ++ vars').
Proof.
  induction vars'; simpl; intros.
  rewrite app_nil_r. inv H; auto.
  destruct a as [id sz].
  simpl in H0. inv H0. rewrite in_app in H6.
  rewrite list_norepet_app in H7. destruct H7 as [P [Q R]].
  destruct (assign_variable (cenv1, sz1) (id, sz)) as [cenv' sz'] eqn:?.
  exploit assign_variable_sound.
    eauto.
    instantiate (1 := vars). tauto.
    auto. auto. auto.
  intros [A B].
  exploit IHvars'.
    eauto.
    instantiate (1 := vars ++ ((id, sz) :: nil)).
    rewrite list_norepet_app. split. auto.
    split. rewrite map_app. apply list_norepet_append_commut. simpl. constructor; auto.
    rewrite map_app. simpl. red; intros. rewrite in_app in H4. destruct H4.
    eauto. simpl in H4. destruct H4. subst y. red; intros; subst x. tauto. tauto.
    generalize (assign_variable_incr _ _ _ _ _ _ Heqp). omega.
    auto. auto.
  rewrite app_ass. auto.
Qed.

Remark permutation_norepet:
  forall (A: Type) (l l': list A), Permutation l l' -> list_norepet l -> list_norepet l'.
Proof.
  induction 1; intros.
  constructor.
  inv H0. constructor; auto. red; intros; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.
  inv H. simpl in H2. inv H3. constructor. simpl; intuition. constructor. intuition. auto.
  eauto.
Qed.

Lemma build_compilenv_sound:
  forall f cenv sz,
  build_compilenv f = (cenv, sz) ->
  list_norepet (map fst (Csharpminor_memsem.fn_vars f)) ->
  cenv_compat cenv (Csharpminor_memsem.fn_vars f) sz /\ cenv_separated cenv (Csharpminor_memsem.fn_vars f).
Proof.
  unfold build_compilenv; intros.
  set (vars1 := Csharpminor_memsem.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  assert (cenv_compat cenv vars2 sz /\ cenv_separated cenv vars2).
    change vars2 with (nil ++ vars2).
    eapply assign_variables_sound.
    eexact H.
    simpl. rewrite app_nil_r. apply permutation_norepet with (map fst vars1); auto.
    apply Permutation_map. auto.
    omega.
    red; intros. contradiction.
    red; intros. contradiction.
  destruct H1 as [A B]. split.
  red; intros. apply A. apply Permutation_in with vars1; auto.
  red; intros. eapply B; eauto; apply Permutation_in with vars1; auto.
Qed.

Lemma assign_variables_domain:
  forall id vars cesz,
  (fst (assign_variables cesz vars))!id <> None ->
  (fst cesz)!id <> None \/ In id (map fst vars).
Proof.
  induction vars; simpl; intros.
  auto.
  exploit IHvars; eauto. unfold assign_variable. destruct a as [id1 sz1].
  destruct cesz as [cenv stksz]. simpl.
  rewrite PTree.gsspec. destruct (peq id id1). auto. tauto.
Qed.

Lemma build_compilenv_domain:
  forall f cenv sz id ofs,
  build_compilenv f = (cenv, sz) ->
  cenv!id = Some ofs -> In id (map fst (Csharpminor_memsem.fn_vars f)).
Proof.
  unfold build_compilenv; intros.
  set (vars1 := Csharpminor_memsem.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  generalize (assign_variables_domain id vars2 (PTree.empty Z, 0)).
  rewrite H. simpl. intros. destruct H1. congruence.
  rewrite PTree.gempty in H1. congruence.
  apply Permutation_in with (map fst vars2); auto.
  apply Permutation_map. apply Permutation_sym; auto.
Qed.

(** Initialization of C#minor temporaries and Cminor local variables. *)

Lemma create_undef_temps_val:
  forall id v temps, (create_undef_temps temps)!id = Some v -> In id temps /\ v = Vundef.
Proof.
  induction temps; simpl; intros.
  rewrite PTree.gempty in H. congruence.
  rewrite PTree.gsspec in H. destruct (peq id a).
  split. auto. congruence.
  exploit IHtemps; eauto. tauto.
Qed.

Fixpoint set_params' (vl: list val) (il: list ident) (te: Cminor_memsem.env) : Cminor_memsem.env :=
  match il, vl with
  | i1 :: is, v1 :: vs => set_params' vs is (PTree.set i1 v1 te)
  | i1 :: is, nil => set_params' nil is (PTree.set i1 Vundef te)
  | _, _ => te
  end.

Lemma bind_parameters_agree_rec:
  forall f vars vals tvals le1 le2 te,
  bind_parameters vars vals le1 = Some le2 ->
  Val.inject_list f vals tvals ->
  match_temps f le1 te ->
  match_temps f le2 (set_params' tvals vars te).
Proof.
Opaque PTree.set.
  induction vars; simpl; intros.
  destruct vals; try discriminate. inv H. auto.
  destruct vals; try discriminate. inv H0.
  simpl. eapply IHvars; eauto.
  red; intros. rewrite PTree.gsspec in *. destruct (peq id a).
  inv H0. exists v'; auto.
  apply H1; auto.
Qed.

Lemma set_params'_outside:
  forall id il vl te, ~In id il -> (set_params' vl il te)!id = te!id.
Proof.
  induction il; simpl; intros. auto.
  destruct vl; rewrite IHil.
  apply PTree.gso. intuition. intuition.
  apply PTree.gso. intuition. intuition.
Qed.

Lemma set_params'_inside:
  forall id il vl te1 te2,
  In id il ->
  (set_params' vl il te1)!id = (set_params' vl il te2)!id.
Proof.
  induction il; simpl; intros.
  contradiction.
  destruct vl; destruct (List.in_dec peq id il); auto;
  repeat rewrite set_params'_outside; auto;
  assert (a = id) by intuition; subst a; repeat rewrite PTree.gss; auto.
Qed.

Lemma set_params_set_params':
  forall il vl id,
  list_norepet il ->
  (set_params vl il)!id = (set_params' vl il (PTree.empty val))!id.
Proof.
  induction il; simpl; intros.
  auto.
  inv H. destruct vl.
  rewrite PTree.gsspec. destruct (peq id a).
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto.
  rewrite PTree.gsspec. destruct (peq id a).
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto.
Qed.

Lemma set_locals_outside:
  forall e id il,
  ~In id il -> (set_locals il e)!id = e!id.
Proof.
  induction il; simpl; intros.
  auto.
  rewrite PTree.gso. apply IHil. tauto. intuition.
Qed.

Lemma set_locals_inside:
  forall e id il,
  In id il -> (set_locals il e)!id = Some Vundef.
Proof.
  induction il; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss.
  rewrite PTree.gsspec. destruct (peq id a). auto. auto.
Qed.

Lemma set_locals_set_params':
  forall vars vals params id,
  list_norepet params ->
  list_disjoint params vars ->
  (set_locals vars (set_params vals params)) ! id =
  (set_params' vals params (set_locals vars (PTree.empty val))) ! id.
Proof.
  intros. destruct (in_dec peq id vars).
  assert (~In id params). apply list_disjoint_notin with vars; auto. apply list_disjoint_sym; auto.
  rewrite set_locals_inside; auto. rewrite set_params'_outside; auto. rewrite set_locals_inside; auto.
  rewrite set_locals_outside; auto. rewrite set_params_set_params'; auto.
  destruct (in_dec peq id params).
  apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto.
  rewrite set_locals_outside; auto.
Qed.

Lemma bind_parameters_agree:
  forall f params temps vals tvals le,
  bind_parameters params vals (create_undef_temps temps) = Some le ->
  Val.inject_list f vals tvals ->
  list_norepet params ->
  list_disjoint params temps ->
  match_temps f le (set_locals temps (set_params tvals params)).
Proof.
  intros; red; intros.
  exploit bind_parameters_agree_rec; eauto.
  instantiate (1 := set_locals temps (PTree.empty val)).
  red; intros. exploit create_undef_temps_val; eauto. intros [A B]. subst v0.
  exists Vundef; split. apply set_locals_inside; auto. auto.
  intros [v' [A B]]. exists v'; split; auto.
  rewrite <- A. apply set_locals_set_params'; auto.
Qed.

(** The main result in this section. *)

(*CompComp adaptation: new hypotheses, and two new conclusions*)
Theorem match_callstack_function_entry:
  forall L TL h fn cenv tf m e m' tm tm' sp f cs args targs le
  (*new hypotheses: *)(GE1: Ple (Genv.genv_next ge) h) (GE2: Ple (Genv.genv_next tge) h),
  build_compilenv fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Int.max_unsigned ->
  list_norepet (map fst (Csharpminor_memsem.fn_vars fn)) ->
  list_norepet (Csharpminor_memsem.fn_params fn) ->
  list_disjoint (Csharpminor_memsem.fn_params fn) (Csharpminor_memsem.fn_temps fn) ->
  alloc_variables Csharpminor_memsem.empty_env m (Csharpminor_memsem.fn_vars fn) e m' ->
  bind_parameters (Csharpminor_memsem.fn_params fn) args (create_undef_temps fn.(fn_temps)) = Some le ->
  Val.inject_list f args targs ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  match_callstack L TL f m tm h cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  let te := set_locals (Csharpminor_memsem.fn_temps fn) (set_params targs (Csharpminor_memsem.fn_params fn)) in
  exists f',
     match_callstack (fun b => L b || freshblock m m' b) 
                     (fun b => TL b || freshblock tm tm' b)
                     f' m' tm' h
                     (Frame cenv tf e le te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f' m' tm'
  /\ (*new*) mini_intern_incr f f' (fun b : block => L b || freshblock m m' b) 
                                   (fun b : block => TL b || freshblock tm tm' b)
  /\ (*new*) globals_separate ge tge f f'.
Proof.
  intros.
  exploit build_compilenv_sound; eauto. intros [C1 C2].
  eapply match_callstack_alloc_variables; eauto.
  intros. eapply build_compilenv_domain; eauto.
  eapply bind_parameters_agree; eauto.
Qed.

(** * Compatibility of evaluation functions with respect to memory injections. *)

Remark val_inject_val_of_bool:
  forall f b, Val.inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  intros; destruct b; constructor.
Qed.

Remark val_inject_val_of_optbool:
  forall f ob, Val.inject f (Val.of_optbool ob) (Val.of_optbool ob).
Proof.
  intros; destruct ob; simpl. destruct b; constructor. constructor.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists y, Some ?x = Some y /\ Val.inject _ _ _ ] =>
      exists x; split; [auto | try(econstructor; eauto)]
  | [ |- exists y, _ /\ Val.inject _ (Vint ?x) _ ] =>
      exists (Vint x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ Val.inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ Val.inject _ (Vlong ?x) _ ] =>
      exists (Vlong x); split; [eauto with evalexpr | constructor]
  | _ => idtac
  end.

(** Compatibility of [eval_unop] with respect to [Val.inject]. *)

Lemma eval_unop_compat:
  forall f op v1 tv1 v,
  eval_unop op v1 = Some v ->
  Val.inject f v1 tv1 ->
  exists tv,
     eval_unop op tv1 = Some tv
  /\ Val.inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_int f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_intu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_int f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_intu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_long f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_longu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_long f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_longu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
Qed.

(** Compatibility of [eval_binop] with respect to [Val.inject]. *)

Lemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  eval_binop op v1 v2 m = Some v ->
  Val.inject f v1 tv1 ->
  Val.inject f v2 tv2 ->
  Mem.inject f m tm ->
  exists tv,
     eval_binop op tv1 tv2 tm = Some tv
  /\ Val.inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; inv H1; TrivialExists.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  inv H; inv H0; inv H1; TrivialExists.
    apply Int.sub_add_l.
    simpl. destruct (eq_block b1 b0); auto.
    subst b1. rewrite H in H0; inv H0.
    rewrite dec_eq_true. rewrite Int.sub_shifted. auto.
  inv H; inv H0; inv H1; TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H; TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H. TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H; TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H. TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExists. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExists. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H; TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H. TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H; TrivialExists.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H. TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists.
  inv H; inv H0; inv H1; TrivialExists. simpl. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H; inv H0; inv H1; TrivialExists. simpl. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H; inv H0; inv H1; TrivialExists. simpl. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H; inv H0; inv H1; TrivialExists. apply val_inject_val_of_optbool.
(* cmpu *)
  inv H. econstructor; split; eauto.
  unfold Val.cmpu.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:E.
  replace (Val.cmpu_bool (Mem.valid_pointer tm) c tv1 tv2) with (Some b).
  destruct b; simpl; constructor.
  symmetry. eapply Val.cmpu_bool_inject; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  simpl; auto.
(* cmpf *)
  inv H; inv H0; inv H1; TrivialExists. apply val_inject_val_of_optbool.
(* cmpfs *)
  inv H; inv H0; inv H1; TrivialExists. apply val_inject_val_of_optbool.
(* cmpl *)
  unfold Val.cmpl in *. inv H0; inv H1; simpl in H; inv H.
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
(* cmplu *)
  unfold Val.cmplu in *. inv H0; inv H1; simpl in H; inv H.
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
Qed.

(** * Correctness of Cminor construction functions *)

(** Correctness of the variable accessor [var_addr] *)

Lemma var_addr_correct:
  forall L TL h cenv id f tf e le te sp lo hi m cs tm b,
  match_callstack L TL f m tm h (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  eval_var_addr ge e id b ->
  exists tv,
     eval_expr tge (Vptr sp Int.zero) te tm (var_addr cenv id) tv
  /\ Val.inject f (Vptr b Int.zero) tv.
Proof.
  unfold var_addr; intros.
  assert (match_var f sp e!id cenv!id).
    inv H. inv MENV. auto.
  inv H1; inv H0; try congruence.
+ (* local *)
  exists (Vptr sp (Int.repr ofs)); split.
  constructor. simpl. rewrite Int.add_zero_l; auto.
  congruence.
+ (* global *)
  exploit match_callstack_match_globalenvs; eauto. intros [MG [HH1 [HH2 [HH3 HH]]]]. inv MG.
  exists (Vptr b Int.zero); split.
  constructor. simpl. rewrite symbols_preserved. rewrite H2. auto.
  econstructor; eauto.
Qed.

(** * Semantic preservation for the translation *)

(** The proof of semantic preservation uses simulation diagrams of the
  following form:
<<
       e, m1, s ----------------- sp, te1, tm1, ts
          |                                |
         t|                                |t
          v                                v
       e, m2, out --------------- sp, te2, tm2, tout
>>
  where [ts] is the Cminor statement obtained by translating the
  C#minor statement [s].  The left vertical arrow is an execution
  of a C#minor statement.  The right vertical arrow is an execution
  of a Cminor statement.  The precondition (top vertical bar)
  includes a [mem_inject] relation between the memory states [m1] and [tm1],
  and a [match_callstack] relation for any callstack having
  [e], [te1], [sp] as top frame.  The postcondition (bottom vertical bar)
  is the existence of a memory injection [f2] that extends the injection
  [f1] we started with, preserves the [match_callstack] relation for
  the transformed callstack at the final state, and validates a
  [outcome_inject] relation between the outcomes [out] and [tout].
*)

(** ** Semantic preservation for expressions *)

Remark bool_of_val_inject:
  forall f v tv b,
  Val.bool_of_val v b -> Val.inject f v tv -> Val.bool_of_val tv b.
Proof.
  intros. inv H0; inv H; constructor; auto.
Qed.

Lemma transl_constant_correct:
  forall f sp cst v,
  Csharpminor_memsem.eval_constant cst = Some v ->
  exists tv,
     eval_constant tge sp (transl_constant cst) = Some tv
  /\ Val.inject f v tv.
Proof.
  destruct cst; simpl; intros; inv H.
  exists (Vint i); auto.
  exists (Vfloat f0); auto.
  exists (Vsingle f0); auto.
  exists (Vlong i); auto.
Qed.

Lemma transl_expr_correct:
  forall L TL h f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack L TL f m tm h
             (Frame cenv tf e le te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor_memsem.eval_expr ge e le m a v ->
  forall ta
    (TR: transl_expr cenv a = OK ta),
  exists tv,
     eval_expr tge (Vptr sp Int.zero) te tm ta tv
  /\ Val.inject f v tv.
Proof.
  induction 3; intros; simpl in TR; try (monadInv TR).
  (* Etempvar *)
  inv MATCH. exploit MTMP; eauto. intros [tv [A B]].
  exists tv; split. constructor; auto. auto.
  (* Eaddrof *)
  eapply var_addr_correct; eauto.
  (* Econst *)
  exploit transl_constant_correct; eauto. intros [tv [A B]].
  exists tv; split; eauto. constructor; eauto.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit eval_unop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split; auto. econstructor; eauto.
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 INJ2]].
  exploit eval_binop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. auto.
  (* Eload *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit Mem.loadv_inject; eauto. intros [tv [LOAD INJ]].
  exists tv; split. econstructor; eauto. auto.
Qed.

Lemma transl_exprlist_correct:
  forall L TL h f m tm cenv tf e le te sp lo hi cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack L TL f m tm h
             (Frame cenv tf e le te sp lo hi :: cs)
             (Mem.nextblock m) (Mem.nextblock tm)),
  forall a v,
  Csharpminor_memsem.eval_exprlist ge e le m a v ->
  forall ta
    (TR: transl_exprlist cenv a = OK ta),
  exists tv,
     eval_exprlist tge (Vptr sp Int.zero) te tm ta tv
  /\ Val.inject_list f v tv.
Proof.
  induction 3; intros; monadInv TR.
  exists (@nil val); split. constructor. constructor.
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit IHeval_exprlist; eauto. intros [tv2 [EVAL2 VINJ2]].
  exists (tv1 :: tv2); split. constructor; auto. constructor; auto.
Qed.

(** ** Semantic preservation for statements and functions *)

Inductive match_cont: Csharpminor_memsem.cont -> Cminor_memsem.cont -> compilenv -> exit_env -> callstack -> Prop :=
  | match_Kstop: forall cenv xenv,
      match_cont Csharpminor_memsem.Kstop Kstop cenv xenv nil
  | match_Kseq: forall s k ts tk cenv xenv cs,
      transl_stmt cenv xenv s = OK ts ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor_memsem.Kseq s k) (Kseq ts tk) cenv xenv cs
  | match_Kseq2: forall s1 s2 k ts1 tk cenv xenv cs,
      transl_stmt cenv xenv s1 = OK ts1 ->
      match_cont (Csharpminor_memsem.Kseq s2 k) tk cenv xenv cs ->
      match_cont (Csharpminor_memsem.Kseq (Csharpminor_memsem.Sseq s1 s2) k)
                 (Kseq ts1 tk) cenv xenv cs
  | match_Kblock: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor_memsem.Kblock k) (Kblock tk) cenv (true :: xenv) cs
  | match_Kblock2: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont k (Kblock tk) cenv (false :: xenv) cs
  | match_Kcall: forall optid fn e le k tfn sp te tk cenv xenv lo hi cs sz cenv',
      transl_funbody cenv sz fn = OK tfn ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor_memsem.Kcall optid fn e le k)
                 (Kcall optid tfn (Vptr sp Int.zero) te tk)
                 cenv' nil
                 (Frame cenv tfn e le te sp lo hi :: cs).

(*CompComp adaptation: state refactoring; added parameters L TL h, exposed (f:meminj)*)
Inductive match_states L TL h f: Csharpminor_memsem.state -> mem -> Cminor_memsem.state -> mem -> Prop :=
  | match_state:
      forall fn s k e le m tfn ts tk sp te tm cenv xenv lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s = OK ts)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack L TL f m tm h
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv xenv cs),
      match_states L TL h f (Csharpminor_memsem.State fn s k e le) m
                   (State tfn ts tk (Vptr sp Int.zero) te) tm
  | match_state_seq:
      forall fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s1 = OK ts1)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack L TL f m tm h
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont (Csharpminor_memsem.Kseq s2 k) tk cenv xenv cs),
      match_states L TL h f (Csharpminor_memsem.State fn (Csharpminor_memsem.Sseq s1 s2) k e le) m
                   (State tfn ts1 tk (Vptr sp Int.zero) te) tm
  | match_callstate:
      forall fd args k m tfd targs tk tm cs cenv
      (TR: transl_fundef fd = OK tfd)
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack L TL f m tm h cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (ISCC: Csharpminor_memsem.is_call_cont k)
      (ARGSINJ: Val.inject_list f args targs),
      match_states L TL h f (Csharpminor_memsem.Callstate fd args k) m
                   (Callstate tfd targs tk) tm
  | match_returnstate:
      forall v k m tv tk tm cs cenv
      (MINJ: Mem.inject f m tm)
      (MCS: match_callstack L TL f m tm h cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: Val.inject f v tv),
      match_states L TL h f (Csharpminor_memsem.Returnstate v k) m
                   (Returnstate tv tk) tm.

Remark val_inject_function_pointer:
  forall bound v fd f tv,
  Genv.find_funct ge v = Some fd ->
  match_globalenvs f bound ->
  Val.inject f v tv ->
  tv = v.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite Genv.find_funct_find_funct_ptr in H.
  assert (f b = Some(b, 0)). inv H0. apply DOMAIN. eapply FUNCTIONS; eauto.
  inv H1. rewrite H2 in H5; inv H5. reflexivity.
Qed.

Lemma match_call_cont:
  forall k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  match_cont (Csharpminor_memsem.call_cont k) (call_cont tk) cenv nil cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.effect_semantics.

(*CompComp adaptation: use effect-semantics, with EmptyEffect*)
Lemma match_is_call_cont:
  forall tfn te sp tm k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  Csharpminor_memsem.is_call_cont k ->
  exists tk',
    effstep_star CMin_effsem tge EmptyEffect (State tfn Sskip tk sp te) tm
               (State tfn Sskip tk' sp te) tm
    /\ is_call_cont tk'
    /\ match_cont k tk' cenv nil cs.
Proof.
  induction 1; simpl; intros; try contradiction.
  econstructor; split. apply effstep_star_zero. split. exact I. econstructor; eauto.
  exploit IHmatch_cont; eauto.
  intros [tk' [A B]]. exists tk'; split.
  eapply effstep_star_trans'. apply effstep_star_one; constructor. eassumption. reflexivity.
  auto.
  econstructor; split. apply effstep_star_zero. split. exact I. econstructor; eauto.
Qed.

(** Properties of [switch] compilation *)

Inductive lbl_stmt_tail: lbl_stmt -> nat -> lbl_stmt -> Prop :=
  | lstail_O: forall sl,
      lbl_stmt_tail sl O sl
  | lstail_S: forall c s sl n sl',
      lbl_stmt_tail sl n sl' ->
      lbl_stmt_tail (LScons c s sl) (S n) sl'.

Lemma switch_table_default:
  forall sl base,
  exists n,
     lbl_stmt_tail sl n (select_switch_default sl)
  /\ snd (switch_table sl base) = (n + base)%nat.
Proof.
  induction sl; simpl; intros.
- exists O; split. constructor. omega.
- destruct o.
  + destruct (IHsl (S base)) as (n & P & Q). exists (S n); split.
    constructor; auto.
    destruct (switch_table sl (S base)) as [tbl dfl]; simpl in *. omega.
  + exists O; split. constructor.
    destruct (switch_table sl (S base)) as [tbl dfl]; simpl in *. auto.
Qed.

Lemma switch_table_case:
  forall i sl base dfl,
  match select_switch_case i sl with
  | None =>
      switch_target i dfl (fst (switch_table sl base)) = dfl
  | Some sl' =>
      exists n,
         lbl_stmt_tail sl n sl'
      /\ switch_target i dfl (fst (switch_table sl base)) = (n + base)%nat
  end.
Proof.
  induction sl; simpl; intros.
- auto.
- destruct (switch_table sl (S base)) as [tbl1 dfl1] eqn:ST.
  destruct o; simpl.
  rewrite dec_eq_sym. destruct (zeq i z).
  exists O; split; auto. constructor.
  specialize (IHsl (S base) dfl). rewrite ST in IHsl. simpl in *.
  destruct (select_switch_case i sl).
  destruct IHsl as (x & P & Q). exists (S x); split. constructor; auto. omega.
  auto.
  specialize (IHsl (S base) dfl). rewrite ST in IHsl. simpl in *.
  destruct (select_switch_case i sl).
  destruct IHsl as (x & P & Q). exists (S x); split. constructor; auto. omega.
  auto.
Qed.

Lemma switch_table_select:
  forall i sl,
  lbl_stmt_tail sl
                (switch_target i (snd (switch_table sl O)) (fst (switch_table sl O)))
                (select_switch i sl).
Proof.
  unfold select_switch; intros.
  generalize (switch_table_case i sl O (snd (switch_table sl O))).
  destruct (select_switch_case i sl) as [sl'|].
  intros (n & P & Q). replace (n + O)%nat with n in Q by omega. congruence.
  intros E; rewrite E.
  destruct (switch_table_default sl O) as (n & P & Q).
  replace (n + O)%nat with n in Q by omega. congruence.
Qed.

Inductive transl_lblstmt_cont(cenv: compilenv) (xenv: exit_env): lbl_stmt -> cont -> cont -> Prop :=
  | tlsc_default: forall k,
      transl_lblstmt_cont cenv xenv LSnil k (Kblock (Kseq Sskip k))
  | tlsc_case: forall i s ls k ts k',
      transl_stmt cenv (switch_env (LScons i s ls) xenv) s = OK ts ->
      transl_lblstmt_cont cenv xenv ls k k' ->
      transl_lblstmt_cont cenv xenv (LScons i s ls) k (Kblock (Kseq ts k')).

(*CompComp adaptation: use effect-semantics, with EmptyEffect*)
Lemma switch_descent:
  forall cenv xenv k ls body s,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont cenv xenv ls k k'
  /\ (forall f sp e m,
      effstep_plus CMin_effsem tge EmptyEffect (State f s k sp e) m (State f body k' sp e) m).
Proof.
  induction ls; intros.
- monadInv H. econstructor; split.
  econstructor.
  intros. eapply effstep_plus_trans'; try eapply effstep_plus_one; constructor.
- monadInv H. exploit IHls; eauto. intros [k' [A B]].
  econstructor; split.
  econstructor; eauto.
  intros. eapply effstep_plus_star_trans'. eauto.
  eapply effstep_star_trans; eapply effstep_star_one; constructor.
  reflexivity.
Qed.

(*CompComp adaptation: use effect-semantics, with EmptyEffect*)
Lemma switch_ascent:
  forall f sp e m cenv xenv ls n ls',
  lbl_stmt_tail ls n ls' ->
  forall k k1,
  transl_lblstmt_cont cenv xenv ls k k1 ->
  exists k2,
  effstep_star CMin_effsem tge EmptyEffect (State f (Sexit n) k1 sp e) m
             (State f (Sexit O) k2 sp e) m
  /\ transl_lblstmt_cont cenv xenv ls' k k2.
Proof.
  induction 1; intros.
- exists k1; split; auto. apply effstep_star_zero.
- inv H0. exploit IHlbl_stmt_tail; eauto. intros (k2 & P & Q).
  exists k2; split; auto.
  eapply effstep_star_trans'. eapply effstep_star_one; econstructor.
  eapply effstep_star_trans'. eapply effstep_star_one; econstructor. eexact P.
  reflexivity. reflexivity.
Qed.

Lemma switch_match_cont:
  forall cenv xenv k cs tk ls tk',
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk' ->
  match_cont (Csharpminor_memsem.Kseq (seq_of_lbl_stmt ls) k) tk' cenv (false :: switch_env ls xenv) cs.
Proof.
  induction ls; intros; simpl.
  inv H0. apply match_Kblock2. econstructor; eauto.
  inv H0. apply match_Kblock2. eapply match_Kseq2. auto. eauto.
Qed.

(*CompComp adaptation: use effect-semantics, with EmptyEffect*)
Lemma switch_match_states:
  forall L TL h fn k e le m tfn ts tk sp te tm cenv xenv f lo hi cs sz ls body tk'
    (TRF: transl_funbody cenv sz fn = OK tfn)
    (TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts)
    (MINJ: Mem.inject f m tm)
    (MCS: match_callstack L TL f m tm h
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
    (MK: match_cont k tk cenv xenv cs)
    (TK: transl_lblstmt_cont cenv xenv ls tk tk'),
  exists S,
  effstep_plus CMin_effsem tge EmptyEffect (State tfn (Sexit O) tk' (Vptr sp Int.zero) te) tm S tm
  /\ match_states L TL h f (Csharpminor_memsem.State fn (seq_of_lbl_stmt ls) k e le) m S tm.
Proof.
  intros. inv TK.
- econstructor; split.
    eapply effstep_plus_trans'; try eapply effstep_plus_one; econstructor. 
  eapply match_state; eauto.
- econstructor; split. 
    eapply effstep_plus_trans'; try eapply effstep_plus_one; constructor. 
    simpl. eapply match_state_seq; eauto. simpl. eapply switch_match_cont; eauto.
Qed.

Lemma transl_lblstmt_suffix:
  forall cenv xenv ls n ls',
  lbl_stmt_tail ls n ls' ->
  forall body ts, transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  exists body', exists ts', transl_lblstmt cenv (switch_env ls' xenv) ls' body' = OK ts'.
Proof.
  induction 1; intros.
- exists body, ts; auto.
- monadInv H0. eauto.
Qed.

(** Commutation between [find_label] and compilation *)

Section FIND_LABEL.

Variable lbl: label.
Variable cenv: compilenv.
Variable cs: callstack.

Lemma transl_lblstmt_find_label_context:
  forall xenv ls body ts tk1 tk2 ts' tk',
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  transl_lblstmt_cont cenv xenv ls tk1 tk2 ->
  find_label lbl body tk2 = Some (ts', tk') ->
  find_label lbl ts tk1 = Some (ts', tk').
Proof.
  induction ls; intros.
- monadInv H. inv H0. simpl. rewrite H1. auto.
- monadInv H. inv H0. simpl in H6. eapply IHls; eauto.
  replace x with ts0 by congruence. simpl. rewrite H1. auto.
Qed.

Lemma transl_find_label:
  forall s k xenv ts tk,
  transl_stmt cenv xenv s = OK ts ->
  match_cont k tk cenv xenv cs ->
  match Csharpminor_memsem.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end

with transl_lblstmt_find_label:
  forall ls xenv body k ts tk tk1,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk1 ->
  find_label lbl body tk1 = None ->
  match Csharpminor_memsem.find_label_ls lbl ls k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end.
Proof.
  intros. destruct s; try (monadInv H); simpl; auto.
  (* seq *)
  exploit (transl_find_label s1). eauto. eapply match_Kseq. eexact EQ1. eauto.
  destruct (Csharpminor_memsem.find_label lbl s1 (Csharpminor_memsem.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto.
  (* ifthenelse *)
  exploit (transl_find_label s1). eauto. eauto.
  destruct (Csharpminor_memsem.find_label lbl s1 k) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto.
  (* loop *)
  apply transl_find_label with xenv. auto. econstructor; eauto. simpl. rewrite EQ; auto.
  (* block *)
  apply transl_find_label with (true :: xenv). auto. constructor; auto.
  (* switch *)
  simpl in H. destruct (switch_table l O) as [tbl dfl]. monadInv H.
  exploit switch_descent; eauto. intros [k' [A B]].
  eapply transl_lblstmt_find_label. eauto. eauto. eauto. reflexivity.
  (* return *)
  destruct o; monadInv H; auto.
  (* label *)
  destruct (ident_eq lbl l).
  exists x; exists tk; exists xenv; auto.
  apply transl_find_label with xenv; auto.

  intros. destruct ls; monadInv H; simpl.
  (* nil *)
  inv H1. rewrite H2. auto.
  (* cons *)
  inv H1. simpl in H7.
  exploit (transl_find_label s). eauto. eapply switch_match_cont; eauto.
  destruct (Csharpminor_memsem.find_label lbl s (Csharpminor_memsem.Kseq (seq_of_lbl_stmt ls) k)) as [[s' k''] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'; intuition.
  eapply transl_lblstmt_find_label_context; eauto.
  simpl. replace x with ts0 by congruence. rewrite H2. auto.
  intro. eapply transl_lblstmt_find_label. eauto. auto. eauto.
  simpl. replace x with ts0 by congruence. rewrite H2. auto.
Qed.

End FIND_LABEL.

Lemma transl_find_label_body:
  forall cenv xenv size f tf k tk cs lbl s' k',
  transl_funbody cenv size f = OK tf ->
  match_cont k tk cenv xenv cs ->
  Csharpminor_memsem.find_label lbl f.(Csharpminor_memsem.fn_body) (Csharpminor_memsem.call_cont k) = Some (s', k') ->
  exists ts', exists tk', exists xenv',
     find_label lbl tf.(fn_body) (call_cont tk) = Some(ts', tk')
  /\ transl_stmt cenv xenv' s' = OK ts'
  /\ match_cont k' tk' cenv xenv' cs.
Proof.
  intros. monadInv H. simpl.
  exploit transl_find_label. eexact EQ. eapply match_call_cont. eexact H0.
  instantiate (1 := lbl). rewrite H1. auto.
Qed.

(** The simulation diagram. *)

Fixpoint seq_left_depth (s: Csharpminor_memsem.stmt) : nat :=
  match s with
  | Csharpminor_memsem.Sseq s1 s2 => S (seq_left_depth s1)
  | _ => O
  end.

(*CompComp adaptation: removed memory (state refactoring)*)
Definition measure (S: Csharpminor_memsem.state) : nat :=
  match S with
  | Csharpminor_memsem.State fn s k e le => seq_left_depth s
  | _ => O
  end.

Require Import sepcomp.mem_lemmas.
Require Import minisepcomp.BuiltinEffects.

Definition match_ST L TL h j S1 m1 T1 tm1:= 
   (Ple (Genv.genv_next ge) h /\ Ple (Genv.genv_next tge) h) /\
   match_states L TL h j S1 m1 T1 tm1.

(*CompComp adaptation: state refactoring, removed trace, switched to effect-semantics, 
  exposed j in match_states*)
Lemma transl_step_correct:
  forall S1 m1 S2 m2 E, Csharpminor_memsem.estep ge E S1 m1 S2 m2 ->
  forall T1 tm1 L TL h j, match_ST L TL h j S1 m1 T1 tm1 ->
  exists j', globals_separate ge tge j j' /\ 
  ((exists T2 tm2, let TL' := (fun b => TL b || freshblock tm1 tm2 b) in
                   (exists TE, effstep_plus CMin_effsem tge TE T1 tm1 T2 tm2 /\
                     (forall (UHyp: forall b1 z, E b1 z = true -> (L b1 = true \/ j b1 <> None))
                             b2 ofs (Ub: TE b2 ofs = true),
                      TL b2 = true \/ 
                      (exists b1 delta, j b1 = Some(b2, delta) /\ E b1 (ofs-delta) = true))) /\ 
                  match_ST (fun b => L b || freshblock m1 m2 b) 
                               TL' 
                                h j' S2 m2 T2 tm2 /\
                  mini_intern_incr j j' (fun b => L b || freshblock m1 m2 b) TL')
  \/ ((measure S2 < measure S1 /\ match_ST (fun b => L b || freshblock m1 m2 b) 
                                              TL h j' S2 m2 T1 tm1)%nat
                              /\ mini_intern_incr j j' (fun b => L b || freshblock m1 m2 b) TL)).
Proof.
  specialize mini_intern_incr_same_meminj; intros INC_SAME.
  specialize (globals_separate_same_meminj ge tge); intros GSEP_SAME.
  induction 1; intros T1 tm1 L TL h j [[GE TGE] MSTATE]; inv MSTATE; try rewrite freshblock_irrefl', orb_false_r_ext.

- (* skip seq *)
  monadInv TR. exists j; split; trivial. left.  
  dependent induction MK. (*introduces spurious ge0 tge0, due to the presence of globals_separate ge tge j j' *)
  + eexists; econstructor; split.
    eexists; split. apply effstep_plus_one. constructor. discriminate. 
    rewrite freshblock_irrefl', orb_false_r_ext. intuition.
    split; eauto. econstructor; eauto.  
  + eexists;econstructor; split.
    eexists; split. apply effstep_plus_one. constructor. discriminate. 
    rewrite freshblock_irrefl', orb_false_r_ext. split; trivial. 
    split; eauto. eapply match_state_seq; eauto.
  + exploit IHMK; eauto. intros [T2 [tm2 [[TE [A HTE]] [B INC]]]].
    exists T2; eexists; split.
    eexists; split. eapply effstep_one_plus_plus. constructor. eauto. reflexivity.
                    simpl; intros. apply andb_true_iff in Ub; destruct Ub. apply HTE; trivial.     
    split; trivial. 
- (* skip block *)
  monadInv TR. exists j; split; trivial. left.
  dependent induction MK.
  + eexists; econstructor; split.
    eexists; split. apply effstep_plus_one. constructor. discriminate.
    rewrite freshblock_irrefl', orb_false_r_ext. split; trivial. 
    split; eauto. econstructor; eauto.
  + exploit IHMK; eauto. intros [T2 [tm2 [[TE [A HTE]] [B INC]]]].
    exists T2; eexists; split. eexists; split. eapply effstep_one_plus_plus. constructor. eauto. reflexivity.
               simpl; intros. apply andb_true_iff in Ub; destruct Ub. apply HTE; trivial.
    split; trivial. 
- (* skip call *)
  monadInv TR. exists j; split; trivial. left.
  exploit match_is_call_cont; eauto. intros [tk' [A [B C]]].
  exploit match_callstack_freelist; eauto. intros [tm' [P [Q R]]].
  eexists; econstructor; split.
  eexists; split. eapply effstep_star_plus_trans'. eexact A. apply effstep_plus_one. apply estep_skip_call. auto. eauto. reflexivity. 
                  simpl; intros Ub b z Eff. apply andb_true_iff in Eff; destruct Eff. apply FreeEffectD in H1. destruct H1 as [? [? ?]]; subst b.
                  inv MCS. left; trivial.
  erewrite (freshblock_free _ _ _ _ _ P), orb_false_r_ext. 
  erewrite (freshblock_free_list _ _ _ H0), orb_false_r_ext. split; trivial.
  split; eauto. econstructor; eauto.

- (* set *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  exists j; split; trivial. left; eexists; econstructor; split.
  eexists; split. apply effstep_plus_one. econstructor; eauto. discriminate.
  split; trivial. split; eauto. 
  econstructor; eauto. rewrite freshblock_irrefl',orb_false_r_ext.
  eapply match_callstack_set_temp; eauto.

- (* store *)
  monadInv TR.
  exploit transl_expr_correct. eauto. eauto. eexact H. eauto.
  intros [tv1 [EVAL1 VINJ1]].
  exploit transl_expr_correct. eauto. eauto. eexact H0. eauto.
  intros [tv2 [EVAL2 VINJ2]].
  exploit Mem.storev_mapped_inject; eauto. intros [tm' [STORE' MINJ']].
  destruct vaddr; inv H1. rename H3 into STORE. inv VINJ1. simpl in STORE'.
  exists j; split; trivial. left; eexists; econstructor; split.
  eexists; split. apply effstep_plus_one. econstructor; eauto.
    intros HH bb ofs EFF. 
      apply StoreEffectD in EFF. destruct EFF as [ii [VADDR' Hoff]]. inv VADDR'.
      remember (TL bb) as q; symmetry in Heqq; destruct q. left; trivial. right.
      eapply StoreEffect_propagate_inj; eassumption.
  repeat erewrite freshblock_store, orb_false_r_ext; eauto. split; trivial.
  split; eauto.
  econstructor; eauto.
    rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE).
    rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE').
    eapply match_callstack_invariant with j m tm1; eauto.
    rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE); xomega.
    rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE'); xomega.
    intros. eapply Mem.perm_store_2; eauto.
    intros. eapply Mem.perm_store_1; eauto.

- (* call *)
  simpl in H1. exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tvf [EVAL1 VINJ1]].
  assert (tvf = vf).
    exploit match_callstack_match_globalenvs; eauto. intros [bnd MG].
    eapply val_inject_function_pointer; eauto.
  subst tvf.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  exists j; split; trivial. left; eexists; econstructor; split.
  eexists; split. apply effstep_plus_one. eapply estep_call; eauto. apply sig_preserved; eauto.
                  discriminate.     
  rewrite freshblock_irrefl', orb_false_r_ext. split; trivial. split; eauto.
  econstructor; eauto.
  eapply match_Kcall with (cenv' := cenv); eauto.
  red; auto.

- (* builtin *)
  monadInv TR.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  exploit match_callstack_match_globalenvs; eauto. intros [hi' [MG [HH1 [HH2 [HH3 HH4]]]]].
  exploit external_call_mem_inject; eauto.
  eapply inj_preserves_globals; eauto.
  intros [f' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR SEPARATED]]]]]]]]].
  exists f'; split.
  { red; intros. destruct (SEPARATED _ _ _ J J') as [SEP1 SEP2].
    split.
    destruct (Plt_Ple_dec b1 (Genv.genv_next ge)); trivial. elim SEP1. unfold Mem.valid_block. xomega.
    destruct (Plt_Ple_dec b2 (Genv.genv_next tge)); trivial. elim SEP2. unfold Mem.valid_block. xomega. }
  left; eexists; econstructor; split.
  eexists; split. apply effstep_plus_one. econstructor; eauto.
     eapply external_call_symbols_preserved; eauto. apply senv_preserved.
     intros HH bb ofs EFF. right. eapply BuiltinEffects_propagate_injects; eassumption.
  assert (MCS': match_callstack 
                 (fun b : block => L b || freshblock m m' b)
                 (fun b : block => TL b || freshblock tm1 tm' b)
                 f' m' tm' h
                 (Frame cenv tfn e le te sp lo hi :: cs)
                 (Mem.nextblock m') (Mem.nextblock tm')).
  { eapply match_callstack_sub.
    + apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm1).
      eapply match_callstack_builtin; eauto.
      eapply external_call_nextblock; eassumption.
      eapply external_call_nextblock; eassumption.
     (* { eapply mem_unchanged_on_sub; eauto. intros. red. apply H1. }
      { eapply mem_unchanged_on_sub; eauto. intros. red; intros. apply H1; eauto. }*)
      intros. eapply external_call_max_perm; eauto.
      xomega. xomega.
      eapply external_call_nextblock; eauto.
      eapply external_call_nextblock; eauto.
    + intros bb; split; intros Hbb. rewrite Hbb; trivial. destruct (HH4 _ Hbb) as [A _]; rewrite A; simpl. apply freshblock_charF. left. unfold Mem.valid_block; xomega.
    + intros bb; split; intros Hbb. rewrite Hbb; trivial. destruct (HH4 _ Hbb) as [_ A]; rewrite A; simpl. apply freshblock_charF. left. unfold Mem.valid_block; xomega. }
  split.
  { split; eauto. econstructor; eauto.
Opaque PTree.set.
    unfold set_optvar. destruct optid; simpl.
    eapply match_callstack_set_temp; eauto.
    auto. }
   { split; trivial; intros. destruct (SEPARATED _ _ _ J J').
     assert (Fb: freshblock m m' b1 = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_1; eauto. }
     assert (Fb': freshblock tm1 tm' b2 = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_2; eauto. }
    rewrite Fb, Fb'. split; apply orb_true_r. }
- (* seq *)
  monadInv TR.
  exists j; split; trivial. left; eexists; econstructor; split.
  eexists; split. apply effstep_plus_one. constructor. discriminate.
  rewrite freshblock_irrefl', orb_false_r_ext. split; trivial.
  split; eauto. econstructor; eauto. econstructor; eauto.
- (* seq 2 *)
  exists j; split; trivial. right. split; trivial. split. auto. split; eauto. econstructor; eauto.

- (* ifthenelse *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  exists j; split; trivial. left; exists (State tfn (if b then x0 else x1) tk (Vptr sp Int.zero) te); eexists; split.
  eexists; split. apply effstep_plus_one. eapply estep_ifthenelse; eauto. eapply bool_of_val_inject; eauto. discriminate.
  rewrite freshblock_irrefl', orb_false_r_ext. split; trivial.
  split; eauto. econstructor; eauto. destruct b; auto.

- (* loop *)
  monadInv TR.
  exists j; split; trivial. left; eexists; econstructor; split.
  eexists; split. apply effstep_plus_one. constructor. discriminate.
  rewrite freshblock_irrefl', orb_false_r_ext. split; trivial.
  split; auto. econstructor; eauto.
  econstructor; eauto. simpl. rewrite EQ; auto.

- (* block *)
  monadInv TR.
  exists j; split; trivial. left; eexists; econstructor; split.
  eexists; split. apply effstep_plus_one. constructor. discriminate.
  rewrite freshblock_irrefl', orb_false_r_ext. split; trivial.
  split; auto. econstructor; eauto. econstructor; eauto.

- (* exit seq *)
  monadInv TR. exists j; split; trivial. left.
  dependent induction MK.
  + eexists; econstructor; split.
    eexists; split. apply effstep_plus_one. constructor. discriminate.
    rewrite freshblock_irrefl', orb_false_r_ext. split; trivial.
    split; auto. econstructor; eauto. simpl. auto.
  + exploit IHMK; eauto. intros [T2 [tm2 [[TE [A HTE]] B]]].
    exists T2; eexists; split. 
      eexists; split. eapply effstep_one_plus_plus. constructor. eauto. reflexivity.
                      simpl; intros. apply andb_true_iff in Ub; destruct Ub. eauto.
      eauto.
  + exploit IHMK; eauto. intros [T2 [tm2 [[TE [A HTE]] [B INC]]]].
    exists T2; eexists; split.
    eexists; split. eapply effstep_one_plus_plus. simpl. constructor. eauto. reflexivity.
             simpl; intros. apply andb_true_iff in Ub; destruct Ub. eauto.
    eauto.

- (* exit block 0 *)
  monadInv TR. exists j; split; trivial. left.
  dependent induction MK.
  + eexists; econstructor; split.
    eexists; split. apply effstep_plus_one. constructor. discriminate.
    rewrite freshblock_irrefl', orb_false_r_ext. split; trivial. split; eauto.
    econstructor; eauto.
  + exploit IHMK; eauto. intros [T2 [tm2 [[TE [A HTE]] [B INC]]]].
    exists T2; eexists; split; auto. simpl.
    eexists; split. eapply effstep_one_plus_plus. constructor. eauto. reflexivity.
             simpl; intros. apply andb_true_iff in Ub; destruct Ub. eauto.
    eauto. 

- (* exit block n+1 *)
  monadInv TR. exists j; split; trivial. left.
  dependent induction MK.
  + eexists; econstructor; split.
    eexists; simpl; split. apply effstep_plus_one. constructor. discriminate.
    rewrite freshblock_irrefl', orb_false_r_ext. split; trivial.
    split; auto. econstructor; eauto. auto.
  + exploit IHMK; eauto. intros [T2 [tm2 [[TE [A HTE]] [B INC]]]].
    exists T2; eexists; split.   
    eexists; split. eapply effstep_one_plus_plus. constructor. eauto. reflexivity.
             simpl; intros. apply andb_true_iff in Ub; destruct Ub. eauto.
    auto. 

- (* switch *)
  simpl in TR. destruct (switch_table cases O) as [tbl dfl] eqn:STBL. monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  assert (SA: switch_argument islong tv n).
  { inv H0; inv VINJ; constructor. }
  exploit switch_descent; eauto. intros [k1 [A B]].
  exploit switch_ascent; eauto. eapply (switch_table_select n).
  rewrite STBL; simpl. intros [k2 [C D]].
  exploit transl_lblstmt_suffix; eauto. eapply (switch_table_select n).
  simpl. intros [body' [ts' E]]. 
  exploit switch_match_states; eauto. intros [T2 [F G]].
  exists j; split; trivial. left; exists T2, tm1; split.
  + eexists; split.
    * eapply effstep_plus_star_trans. eapply B.
      eapply effstep_star_trans. apply effstep_star_one. econstructor; eauto.
      eapply effstep_star_trans. eexact C. eapply effstep_star_plus. eexact F.
    * simpl; discriminate. 
  + rewrite freshblock_irrefl', orb_false_r_ext. split; trivial. split; trivial.  auto.

- (* return none *)
  monadInv TR. exists j; split; trivial. left.
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  eexists; econstructor; split.
  eexists; split. apply effstep_plus_one. eapply estep_return_0. eauto. 
    intros Ub bb z EFF. apply FreeEffectD in EFF. destruct EFF as [SP' [VBsp'' BND]]; subst bb. inv MCS. left; trivial.
  erewrite freshblock_free_list, orb_false_r_ext; eauto.
  erewrite freshblock_free, orb_false_r_ext; eauto. split; trivial. split; auto.
  econstructor; eauto. eapply match_call_cont; eauto.

- (* return some *)
  monadInv TR. exists j; split; trivial. left.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  eexists; econstructor; split.
  eexists; split. apply effstep_plus_one. eapply estep_return_1. eauto. eauto.
    intros Ub bb z EFF. apply FreeEffectD in EFF. destruct EFF as [SP' [VBsp'' BND]]; subst bb. inv MCS. left; trivial.
  erewrite freshblock_free_list, orb_false_r_ext; eauto. split; trivial. split; auto.  
  erewrite freshblock_free, orb_false_r_ext; eauto.
  econstructor; eauto. eapply match_call_cont; eauto.

- (* label *)
  monadInv TR.
  exists j; split; trivial. left; econstructor; eexists; split.
  eexists; split. apply effstep_plus_one. constructor. discriminate. split; trivial. 
  rewrite freshblock_irrefl', orb_false_r_ext. split; auto. econstructor; eauto.

- (* goto *)
  monadInv TR.
  exploit transl_find_label_body; eauto.
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists j; split; trivial. left; econstructor; eexists; split.
  eexists; split. apply effstep_plus_one. apply estep_goto. eexact A. discriminate. split; trivial.
  rewrite freshblock_irrefl', orb_false_r_ext. split; auto. econstructor; eauto.

- (* internal call *)
  monadInv TR. generalize EQ; clear EQ; unfold transl_function.
  caseEq (build_compilenv f). intros ce sz BC.
  destruct (zle sz Int.max_unsigned); try congruence.
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  set (tf := mkfunction (Csharpminor_memsem.fn_sig f)
                        (Csharpminor_memsem.fn_params f)
                        (Csharpminor_memsem.fn_temps f)
                        sz
                        x0) in *.
  caseEq (Mem.alloc tm1 0 (fn_stackspace tf)). intros tm' sp ALLOC'.
  exploit match_callstack_function_entry; eauto. simpl; eauto. simpl; auto.
  intros [f2 [MCS2 [MINJ2 [INC SEP]]]].
  exists f2; split; trivial. 
  left; econstructor; eexists; split.
  + eexists; split. apply effstep_plus_one. constructor; simpl; eauto. discriminate.
  + split; trivial. split; eauto.
    econstructor. eexact TRBODY. eauto. eexact MINJ2. eexact MCS2.
    inv MK; simpl in ISCC; contradiction || econstructor; eauto.

- (* external call *)
  monadInv TR.
  exploit match_callstack_match_globalenvs; eauto. intros [hi [MG [HH1 [HH2 [HH3 HH4]]]]].
  exploit external_call_mem_inject; eauto.
  eapply inj_preserves_globals; eauto.
  intros [f' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR SEPARATED]]]]]]]]].
  exists f'; split.
  { red; intros. destruct (SEPARATED _ _ _ J J') as [SEP1 SEP2].
    split.
    destruct (Plt_Ple_dec b1 (Genv.genv_next ge)); trivial. elim SEP1. unfold Mem.valid_block. xomega.
    destruct (Plt_Ple_dec b2 (Genv.genv_next tge)); trivial. elim SEP2. unfold Mem.valid_block. xomega. }
  left; econstructor; eexists; split.
  { eexists; split. apply effstep_plus_one. econstructor. trivial.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    intros HH bb ofs EFF. right. eapply BuiltinEffects_propagate_injects; eassumption. }  
  split.
  { split; eauto.
    econstructor; eauto.
    eapply match_callstack_sub.
    + apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm1).
      eapply match_callstack_builtin; eauto.
      eapply external_call_nextblock; eauto.
      eapply external_call_nextblock; eauto.
      (*{ eapply mem_unchanged_on_sub; eauto. intros. red. apply H0. }
      { eapply mem_unchanged_on_sub; eauto. intros. red; intros. apply H0; eauto. }*)
      intros. eapply external_call_max_perm; eauto.
      xomega. xomega.
      eapply external_call_nextblock; eauto.
      eapply external_call_nextblock; eauto. 
    + intros bb; split; intros Hbb. rewrite Hbb; trivial. destruct (HH4 _ Hbb) as [A _]; rewrite A; simpl. apply freshblock_charF. left. unfold Mem.valid_block; xomega. 
    + intros bb; split; intros Hbb. rewrite Hbb; trivial. destruct (HH4 _ Hbb) as [_ A]; rewrite A; simpl. apply freshblock_charF. left. unfold Mem.valid_block; xomega. }
  { split; trivial; intros. destruct (SEPARATED _ _ _ J J').
     assert (Fb: freshblock m m' b1 = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_1; eauto. }
     assert (Fb': freshblock tm1 tm' b2 = true). { apply freshblockProp_char. split; trivial. eapply Mem.valid_block_inject_2; eauto. }
    rewrite Fb, Fb'. split; apply orb_true_r. }

- (* return *)
  inv MK. simpl. 
  exists j; split; trivial. left; econstructor; eexists; split.
  { eexists; split. apply effstep_plus_one. econstructor; eauto. discriminate. }
  { split; trivial. split; auto. rewrite freshblock_irrefl', orb_false_r_ext.
    unfold set_optvar. destruct optid; simpl; econstructor; eauto.
    eapply match_callstack_set_temp; eauto. }
Qed.
 
Lemma match_globalenvs_init:
  forall m,
  Genv.init_mem prog = Some m ->
  match_globalenvs (Mem.flat_inj (Mem.nextblock m)) (Mem.nextblock m).
Proof.
  intros. constructor.
  intros. unfold Mem.flat_inj. apply pred_dec_true; auto.
  intros. unfold Mem.flat_inj in H0.
  destruct (plt b1 (Mem.nextblock m)); congruence.
  intros. eapply Genv.find_symbol_not_fresh; eauto.
  intros. eapply Genv.find_funct_ptr_not_fresh; eauto.
  intros. eapply Genv.find_var_info_not_fresh; eauto.
Qed.

Lemma transl_initial_states:
  forall j S v tv vals tvals m tm bound, 
         match_globalenvs j bound ->
         CSharpMin_initial_core ge v vals = Some S ->
         Val.inject j v tv -> Val.inject_list j vals tvals ->
         Mem.inject j m tm -> Ple bound (Mem.nextblock m) -> Ple bound (Mem.nextblock tm) ->
  exists R, CMin_initial_core tge tv tvals = Some R /\
            match_states (fun b=> false) (fun b => false) bound j S m R tm.
Proof.
  intros. destruct v; try discriminate. simpl in H.
  simpl in *.
  destruct (Int.eq_dec i Int.zero); try discriminate.
  remember (Genv.find_funct_ptr ge b) as d; symmetry in Heqd; destruct d; try discriminate. subst i.
  exploit val_inject_function_pointer; eauto. rewrite Genv.find_funct_find_funct_ptr; eassumption.
  intros; subst. simpl in *. destruct (Int.eq_dec Int.zero Int.zero). 2: congruence. clear e H1.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]]. rewrite FIND. 
  destruct f; try discriminate.
  apply mem_lemmas.val_list_inject_forall_inject in H2. rewrite <- (mem_lemmas.Forall2_Zlength H2).
  exploit bind_inversion. apply TR. intros [trf [HTF OKx]]; inv OKx.
  destruct (zlt
      match
        match Zlength vals with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0
        | Z.neg y' => Z.neg y'~0
        end
      with
      | 0 => 0
      | Z.pos y' => Z.pos y'~0~0
      | Z.neg y' => Z.neg y'~0~0
      end Int.max_unsigned); inv H0.
  unfold transl_function in HTF. remember (build_compilenv f) as CENV. destruct CENV as [cenv stacksize].
    destruct (zle stacksize Int.max_unsigned); try discriminate.  
  eexists; split. reflexivity.
  econstructor; eauto.
  { instantiate (1:=nil). econstructor; eauto. }
  { instantiate (1:=cenv). constructor. }
  constructor.
  apply mem_lemmas.forall_inject_val_list_inject; trivial.
Qed.

(*
Lemma transl_initial_states:
  forall S, Csharpminor_memsem.initial_state prog S ->
  exists R, Cminor_memsem.initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  apply (Genv.init_mem_transf_partial TRANSL). eauto.
  simpl. fold tge. rewrite symbols_preserved.
  replace (prog_main tprog) with (prog_main prog). eexact H0.
  symmetry. unfold transl_program in TRANSL.
  eapply match_program_main; eauto. 
  eexact FIND.
  rewrite <- H2. apply sig_preserved; auto.
  eapply match_callstate with (f := Mem.flat_inj (Mem.nextblock m0)) (cs := @nil frame) (cenv := PTree.empty Z).
  auto.
  eapply Genv.initmem_inject; eauto.
  apply mcs_nil with (Mem.nextblock m0). apply match_globalenvs_init; auto. xomega. xomega.
  constructor. red; auto.
  constructor.
Qed.
*)

Lemma transl_final_states:
  forall L TL h j S m R tm r,
  match_states L TL h j S m R tm -> CSharpMin_halted S = Some r ->
  exists tr, CMin_halted R = Some tr /\ Mem.inject j m tm /\
               Val.inject j r tr.
Proof.
  intros. destruct S; inv H0. destruct k; inv H2. inv H. simpl.
  inv MK. exists tv; intuition. 
Qed.
(*
Lemma transl_final_states:
  forall S R r,
  match_states S R -> Csharpminor_memsem.final_state S r -> Cminor_memsem.final_state R r.
Proof.
  intros. inv H0. inv H. inv MK. inv RESINJ. constructor.
Qed.

Theorem transl_program_correct:
  forward_simulation (Csharpminor_memsem.semantics prog) (Cminor_memsem.semantics tprog).
Proof.
  eapply forward_simulation_star; eauto.
  apply senv_preserved.
  eexact transl_initial_states.
  eexact transl_final_states.
  eexact transl_step_correct.
Qed.
*)

Lemma transl_atExt_states:
  forall L TL h j S m R tm f sg args,
  match_states L TL h j S m R tm -> CSharpMin_at_external S = Some (f, sg, args) ->
  exists targs, CMin_at_external R = Some (f, sg, targs) /\ Mem.inject j m tm /\
               Val.inject_list j args targs /\ BuiltinEffects.observableEF f.
Proof.
  intros. destruct S; inv H0. destruct f0; inv H2. inv H. simpl. inv TR.
  destruct (BuiltinEffects.observableEF_dec e); inv H1.
  exists targs; intuition. 
Qed.
(*
Lemma transl_afterExt_states:
  forall L TL h j S m R tm f sg args,
  match_states L TL h j S m R tm -> CSharpMin_at_external S = Some (f, sg, args) ->
  exists targs, CMin_at_external R = Some (f, sg, targs) /\ Mem.inject j m tm /\
                Val.inject_list j args targs /\ BuiltinEffects.observableEF f /\
  forall m2 tm2 j2 ret tret
         (INC: inject_incr j j2)
         (SEP:inject_separated j j2 m tm)
         (MINJ2: Mem.inject j2 m2 tm2)
         (RetINJ: Val.inject j2 ret tret)
         (FwdSrc: Ple (Mem.nextblock m) (Mem.nextblock m2))
         (FwdTgt: Ple (Mem.nextblock tm) (Mem.nextblock tm2))
         (UnchSrc: Mem.unchanged_on (loc_unmapped j) m m2)
         (UnchTgt: Mem.unchanged_on (loc_out_of_reach j m) tm tm2)
         (PermSrc: forall b z p, Mem.valid_block m b -> Mem.perm m2 b z Max p -> Mem.perm m b z Max p),
  exists Q P,
    CSharpMin_after_external (Some ret) S = Some Q /\
    CMin_after_external (Some tret) R = Some P /\
    match_states L TL h j2 Q m2 P tm2.
Proof.
  intros. destruct S; inv H0. destruct f0; inv H2. inv H. simpl. inv TR.
  destruct (BuiltinEffects.observableEF_dec e); inv H1. 
  exists targs; intuition. 
  eexists; eexists; split. reflexivity. split. reflexivity.
  econstructor; try eassumption.
  eapply match_callstack_incr_bound; try eassumption.
  eapply match_callstack_external_call_ext; try eassumption; try xomega.
      { eapply mem_unchanged_on_sub; eauto. intros. red. apply H. }
      { eapply mem_unchanged_on_sub; eauto. intros. red; intros. apply H; eauto. }
Qed.*)

Lemma match_states_inject L1 L2 h j st1 m1 st2 m2 :
      match_states L1 L2 h j st1 m1 st2 m2 -> Mem.inject j m1 m2.
Proof. intros. inv H; trivial. Qed.

Lemma match_ST_inject L1 L2 h j st1 m1 st2 m2 :
      match_ST L1 L2 h j st1 m1 st2 m2 -> Mem.inject j m1 m2.
Proof. intros; destruct H; subst. eapply match_states_inject; eauto. Qed.

Definition match_sts:= fun cd j L1 st1 m1 L2 st2 m2 => cd=st1 /\ exists h, match_ST L1 L2 h j st1 m1 st2 m2 /\
   meminj_valid j L1 m1 L2 m2 /\ (forall b1 b2 d, j b1 = Some (b2, d) -> L1 b1 = L2 b2) /\
   mem_respects_readonly ge m1 /\ mem_respects_readonly tge m2.

Lemma corediagram: forall (st1 : Csharpminor_memsem.state) (m1 : mem) (st1' : Csharpminor_memsem.state) 
  (m1' : mem) (U1 : block -> Z -> bool),
effstep CSharpMin_effsem ge U1 st1 m1 st1' m1' ->
forall (st2 : state) (j : meminj) (m2 : mem) (L1 L2 : block -> bool),
match_sts st1 j L1 st1 m1 L2 st2 m2 ->
exists (st2' : state) (m2' : mem) (j' : meminj) (L1' L2' : block -> bool),
  mini_intern_incr j j' L1' L2' /\
  globals_separate ge tge j j' /\
  mini_locally_allocated L1 L2 m1 m2 L1' L2' m1' m2' /\
  match_sts st1' j' L1' st1' m1' L2' st2' m2' /\
  (exists U2 : block -> Z -> bool,
     (effstep_plus CMin_effsem tge U2 st2 m2 st2' m2' \/
      (measure st1' < measure st1)%nat /\ effstep_star CMin_effsem tge U2 st2 m2 st2' m2') /\
     ((forall (b1 : block) (z : Z), U1 b1 z = true -> L1 b1 = true \/ j b1 <> None) ->
      forall (b2 : block) (ofs : Z),
      U2 b2 ofs = true ->
      L2 b2 = true \/
      (exists (b1 : block) (delta : Z), j b1 = Some (b2, delta) /\ U1 b1 (ofs - delta) = true))).
Proof. intros. destruct H0 as [? [h [[GE MS] [VAL [WD MRR]]]]].
exploit transl_step_correct. apply H. split; eassumption. 
intros [j' [GSEP [LEFT | RIGHT]]].
+ destruct LEFT as [st2' [m2' [[U2 [TSTEPS HU]] [MS' INC]]]].
  exists st2', m2', j', (fun b : block => L1 b || freshblock m1 m1' b), (fun b : block => L2 b || freshblock m2 m2' b).
  intuition.
  { split; split; trivial. }
  { split; trivial. exploit match_states_inject; try apply MS. exploit match_ST_inject; try apply MS'. intros MINJ' MINJ.
    exists h; intuition. 
    + destruct VAL as [VAL1 [VAL2 VAL3]].
      split; [intros | split; intros].
      - apply orb_true_iff in H5. destruct H5. eapply effstep_fwd; eauto. apply freshblockProp_char in H5. apply H5.
      - apply orb_true_iff in H5. destruct H5. eapply effstep_plus_fwd; eauto. apply freshblockProp_char in H5. apply H5.
      - split. eapply Mem.valid_block_inject_1; eauto. eapply Mem.valid_block_inject_2; eauto. 
    + intros. remember (j b1) as q; symmetry in Heqq; destruct q.
      - destruct p. destruct INC as [INC SEP]. rewrite (INC _ _ _ Heqq) in H5. inv H5. rewrite (WD _ _ _ Heqq). destruct (L2 b2); simpl; trivial.
        assert (freshblock m2 m2' b2 = false).
        { apply freshblock_charF. left. eapply Mem.valid_block_inject_2; eauto. }
        rewrite H5. apply freshblock_charF. left. eapply Mem.valid_block_inject_1; eauto. 
      - destruct INC as [INC SEP]. destruct (SEP _ _ _ Heqq H5) as [AA BB]. rewrite AA, BB; split; trivial.
    + exploit semantics_lemmas.mem_step_readonly. eapply effstep_mem. apply H.
           intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto.
    + exploit semantics_lemmas.mem_step_readonly. eapply effstep_plus_mem; eauto.
           intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto. }
  exists U2; split. left; trivial. trivial.
+ destruct RIGHT as [[Meas MS'] IINC].
  exists st2, m2, j', (fun b : block => L1 b || freshblock m1 m1' b), L2.
  intuition.
  { split; trivial. rewrite freshblock_irrefl', orb_false_r_ext; trivial. }
  { split; trivial.  exploit match_states_inject; try apply MS. exploit match_ST_inject; try apply MS'. intros MINJ' MINJ.
    destruct IINC as [INC SEP]. exists h; intuition. 
    + destruct VAL as [VAL1 [VAL2 VAL3]]. 
      split; [intros | split; intros].
      - apply orb_true_iff in H5. destruct H5. eapply effstep_fwd; eauto. apply freshblockProp_char in H5. apply H5.
      - eauto. 
      - split. eapply Mem.valid_block_inject_1; eauto. eapply Mem.valid_block_inject_2; eauto.
    + intros. remember (j b1) as q; symmetry in Heqq; destruct q.
      - destruct p. rewrite (INC _ _ _ Heqq) in H5. inv H5. rewrite (WD _ _ _ Heqq). destruct (L2 b2); simpl; trivial.
        apply freshblock_charF. left. eapply Mem.valid_block_inject_1; eauto.
      - destruct (SEP _ _ _ Heqq H5) as [AA BB]. rewrite AA, BB; trivial.
    + exploit semantics_lemmas.mem_step_readonly. eapply effstep_mem. apply H.
        intros [Fwd RD]. eapply mem_respects_readonly_fwd; eauto. }
  exists EmptyEffect. split; [| discriminate]. right; split; trivial. apply effstep_star_zero.
Qed.

Definition SIM: Mini_simulation_inj.Mini_simulation_inject CSharpMin_effsem CMin_effsem ge tge.
eapply inj_simulation_plus_typed.
9: apply corediagram.
+ apply senv_preserved.
+ intros. destruct MS as [? [h [MS [VAL [WD MRR]]]]]; trivial.
+ intros. destruct MS as [? [h [MS [VAL [WD MRR]]]]]; eauto.
+ admit. (*genv properties - maybe these clauses are not quite right in mini_simulations.v ...*)
+ intros. admit. (* exploit transl_initial_states. is not quite right - maybe replce meminj_preserves_globals by match_globalenvs. Also: should the function pointers by injected or equal these days?*)
+ intros. destruct H as [? [h [MS [VAL [WD MRR]]]]]; subst.
  destruct c1; inv H0. destruct k; inv H1.
  destruct MS as [GE MS]. inv MS. inv MK. exists tv; intuition.
+ intros. destruct H as [? [h [MS [VAL [WD MRR]]]]]; subst.
  destruct c1; inv H0. destruct f; inv H1. 
  destruct MS as [GE MS]. inv MS. inv TR. simpl. 
  destruct (BuiltinEffects.observableEF_dec e0); inv H0. intuition.
  exists targs; intuition. eapply val_list_inject_forall_inject; eauto.
+ intros. destruct MatchMu as [? [h [MS [VAL [WD MRR]]]]]; subst.
  destruct st1; inv AtExtSrc. destruct f; inv H0. 
  destruct MS as [GE MS]. inv MS. inv TR. simpl in *. 
  destruct (BuiltinEffects.observableEF_dec e0); inv H1. inv AtExtTgt. 
  eexists; eexists; split. reflexivity. split. reflexivity. destruct GE as [GE1 GE2].
  split; trivial. exists h; split; [| split; [| split]]; trivial. 
  - split; auto. econstructor; eauto. (* destruct INC as [INC SEP].*)
    exploit match_callstack_match_globalenvs; eauto. intros [MG [A1 [A2 [A3 [A4 A5]]]]].
    eapply match_callstack_incr_bound; try eassumption.
    * eapply match_callstack_external_call_ext; try eassumption.
      apply forward_nextblock; trivial. apply forward_nextblock; trivial.
      intros. eapply FwdSrc; eauto.
      intros. remember (j b) as q. symmetry in Heqq; destruct q. destruct p. apply INC; trivial.
              remember (j' b) as w; symmetry in Heqw; destruct w; trivial. destruct p.
              destruct INC as [INC SEP]. destruct (GSep _ _ _ Heqq Heqw).x red in VAL. inv MG.  admit.
      intros. remember (j b) as q. symmetry in Heqq; destruct q. destruct p. rewrite <- H; symmetry. eapply INC. trivial. 
              destruct VAL. destruct INC as [INC SEP]. inv H. destruct (SEP _ _ _ Heqq Heqw). red in VAL. red in MV.
      xomega. econstructor; eauto. exists targs; intuition. eapply val_list_inject_forall_inject; eauto.*)
  - destruct INC as [INC SEP]. intros. remember (j b1) as q; destruct q; symmetry in Heqq.
    * destruct p. rewrite (INC _ _ _ Heqq) in H; inv H. eauto.
    * destruct (SEP _ _ _ Heqq H) as [AA BB]; rewrite AA, BB; trivial.
  - destruct MRR as [MRRSrc MRRTgt].
    split; eapply mem_respects_readonly_forward'; eassumption.  
Admitted.

End TRANSLATION. (*CompCert 2.7.1 has 2233 lines, and 
  Cminorgenproof_4_memsem has 2353 lines,
  Cminorgen_locset has 2426 lines, 
  Cminorgenproof_effects has 2433 lines,
  Cminorgenproof_meminjs has 2435 lines, so adding back-propagation of 
    effect sets to corediagram clause cost 45 lines*) 