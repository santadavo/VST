Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import msl.seplog.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext.
Require Import veric.res_predicates.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import sepcomp.structured_injections.
Require Import sepcomp.extspec.

Definition mem_lessdef m1 m2 :=
  (forall b ofs len v,
      Mem.loadbytes m1 b ofs len = Some v ->
      exists v',
        Mem.loadbytes m2 b ofs len = Some v' /\
        list_forall2 memval_lessdef v v'
  ) /\
  (forall b ofs k p,
      Mem.perm m1 b ofs k p ->
      Mem.perm m2 b ofs k p) /\
  (Mem.nextblock m1 <=
   Mem.nextblock m2)%positive.

Definition mem_lessalloc m1 m2 :=
  Mem.loadbytes m1 = Mem.loadbytes m2 /\
  Mem.perm m1 = Mem.perm m2 /\
  (Mem.nextblock m1 <= Mem.nextblock m2)%positive.

Definition mem_equiv m1 m2 :=
  Mem.loadbytes m1 = Mem.loadbytes m2 /\
  Mem.perm m1 = Mem.perm m2 /\
  Mem.nextblock m1 = Mem.nextblock m2.

Lemma same_perm_spec m1 m2 :
  Mem.perm m1 = Mem.perm m2 <->
  (forall k x, access_at m1 x k = access_at m2 x k).
Proof.
  split; intros E.
  - intros k (b, ofs).
    match type of E with ?f = ?g => assert (S : forall b z k p, f b z k p <-> g b z k p) end.
    { rewrite E; tauto. } clear E.
    spec S b ofs k. revert S.
    unfold access_at, Mem.perm. simpl.
    set (o1 := (Mem.mem_access _) !! b ofs k).
    set (o2 := (Mem.mem_access _) !! b ofs k). clearbody o1 o2. intros S.
    assert (S' : forall o, Mem.perm_order'' o1 o <-> Mem.perm_order'' o2 o).
    { intros [ o | ]. apply S. destruct o1 as [o1 | ], o2 as [o2 | ]; split; intro; constructor. }
    clear S.
    destruct (S' o1) as [A _]. spec A. apply perm_order_pp_refl.
    destruct (S' o2) as [_ B]. spec B. apply perm_order_pp_refl.
    destruct o1 as [[]|], o2 as [[]|]; auto; simpl in *.
    all: inv A; inv B; auto.
  - extensionality b ofs k. spec E k (b, ofs).
    unfold access_at in *.
    simpl in E.
    unfold Mem.perm in *.
    rewrite E.
    auto.
Qed.

Lemma same_loadbytes_spec m1 m2 :
  Mem.perm m1 = Mem.perm m2 ->  (* TODO change this to only need same Cur *)
  Mem.loadbytes m1 = Mem.loadbytes m2 <->
  (forall x, Mem.perm_order' (access_at m1 x Cur) Readable -> contents_at m1 x = contents_at m2 x).
Proof.
  intros P; split; intros E.
  - intros (b, ofs) R.
    Transparent Mem.loadbytes.
    unfold Mem.loadbytes in *.
    apply equal_f with (x := b) in E.
    apply equal_f with (x := ofs) in E.
    apply equal_f with (x := 1) in E.
    unfold access_at in *.
    if_tac [p1|np1] in E; if_tac in E; try discriminate.
    + simpl in E.
      unfold contents_at in *.
      simpl.
      congruence.
    + destruct np1.
      intros ofs1 r1.
      cut (ofs1 = ofs). intros <-. apply R.
      omega.
  - extensionality b ofs k.
    unfold Mem.loadbytes in *.
    if_tac [p1|np1]; if_tac [p2|np2].
    + destruct (zle 0 k).
      * clear p2.
        f_equal.
        rewrite <-(Coqlib.nat_of_Z_eq k) in p1. 2:omega.
        revert p1. generalize (nat_of_Z k); clear k l; intros n.
        revert ofs.
        induction n; auto; intros ofs p.
        simpl. f_equal.
        -- spec E (b, ofs).
           unfold contents_at in *.
           simpl in E.
           apply E.
           apply p.
           simpl.
           zify; omega.
        -- apply IHn.
           intros ofs' r'.
           apply p.
           zify. omega.
      * rewrite nat_of_Z_neg. auto. omega.
    + destruct np2.
      unfold Mem.range_perm in *.
      rewrite <-P.
      auto. 
    + destruct np1.
      unfold Mem.range_perm in *.
      rewrite P.
      auto.
    + auto.
Qed.

Definition mem_equiv' m1 m2 :=
  (forall x, Mem.perm_order' (access_at m1 x Cur) Readable -> contents_at m1 x = contents_at m2 x) /\
  Mem.perm m1 = Mem.perm m2 /\
  Mem.nextblock m1 = Mem.nextblock m2.

Definition mem_lessalloc' m1 m2 :=
  (forall x, Mem.perm_order' (access_at m1 x Cur) Readable -> contents_at m1 x = contents_at m2 x) /\
  Mem.perm m1 = Mem.perm m2 /\
  (Mem.nextblock m1 <= Mem.nextblock m2)%positive.

Lemma mem_equiv'_spec m1 m2 : mem_equiv m1 m2 <-> mem_equiv' m1 m2.
Proof.
  split; intros (? & ? & ?); repeat split; auto.
  rewrite <-same_loadbytes_spec; auto.
  rewrite same_loadbytes_spec; auto.
Qed.

Lemma mem_lessalloc'_spec m1 m2 : mem_lessalloc m1 m2 <-> mem_lessalloc' m1 m2.
Proof.
  split; intros (? & ? & ?); repeat split; auto.
  rewrite <-same_loadbytes_spec; auto.
  rewrite same_loadbytes_spec; auto.
Qed.

Lemma val_inject_antisym v1 v2 :
  val_inject inject_id v1 v2 ->
  val_inject inject_id v2 v1 ->
  v1 = v2.
Proof.
  destruct v1, v2; intros A B; auto.
  all: inversion A; subst; inversion B; try subst; try congruence.
  unfold inject_id in *.
  f_equal. congruence.
  replace delta with 0%Z by congruence.
  symmetry; apply Int.add_zero.
Qed.

Lemma memval_lessdef_antisym v1 v2 : memval_lessdef v1 v2 -> memval_lessdef v2 v1 -> v1 = v2.
Proof.
  destruct v1, v2; intros A B; auto.
  all: inversion A; subst; inversion B; subst; try congruence.
  f_equal. apply val_inject_antisym; auto.
Qed.

Lemma mem_lessdef_equiv m1 m2 : mem_lessdef m1 m2 -> mem_lessdef m2 m1 ->  mem_equiv m1 m2.
Proof.
  intros (L1 & P1 & N1) (L2 & P2 & N2); repeat split.
  - clear -L1 L2.
    extensionality b ofs z.
    match goal with |- ?a = ?b => destruct a as [v1|] eqn:E1; destruct b as [v2|] eqn:E2 end;
      try destruct (L1 _ _ _ _ E1) as (v2' & E1' & l1);
      try destruct (L2 _ _ _ _ E2) as (v1' & E2' & l2);
      try congruence.
    assert (v1' = v1) by congruence; assert (v2' = v2) by congruence; subst; f_equal.
    clear -l1 l2.
    revert v2 l1 l2; induction v1; intros v2 l1 l2; inversion l1; subst; auto.
    inversion l2; subst.
    f_equal; auto.
    apply memval_lessdef_antisym; auto.
  - repeat extensionality.
    apply prop_ext; split; auto.
  - zify.
    cut (Z.pos (Mem.nextblock m2) = Z.pos (Mem.nextblock m1)).
    congruence. omega.
Qed.

Lemma mem_equiv_refl m : mem_equiv m m.
Proof.
  split3; hnf; auto.
Qed.

Lemma mem_lessalloc_refl m : mem_lessalloc m m.
Proof.
  split3; auto. apply Ple_refl.
Qed.

Lemma mem_equiv_refl' m m' : m = m' -> mem_equiv m m'.
Proof.
  intros <-; apply mem_equiv_refl.
Qed.

Lemma mem_lessalloc_refl' m m' : m = m' -> mem_lessalloc m m'.
Proof.
  intros <-; apply mem_lessalloc_refl.
Qed.

Lemma mem_equiv_sym m1 m2 : mem_equiv m1 m2 -> mem_equiv m2 m1.
Proof.
  intros []; split; intuition.
Qed.

Lemma mem_equiv_trans m1 m2 m3 :
  mem_equiv m1 m2 ->
  mem_equiv m2 m3 ->
  mem_equiv m1 m3.
Proof.
  unfold mem_equiv in *.
  intros (-> & -> & ->) (-> & -> & ->); auto.
Qed.

Lemma mem_lessalloc_trans m1 m2 m3 :
  mem_lessalloc m1 m2 ->
  mem_lessalloc m2 m3 ->
  mem_lessalloc m1 m3.
Proof.
  unfold mem_lessalloc in *.
  intros (-> & -> & l) (-> & -> & l'); split; auto. split; auto.
  eapply Ple_trans; eauto.
Qed.

Lemma mem_equiv_lessalloc m1 m2 : mem_equiv m1 m2 -> mem_lessalloc m1 m2.
Proof.
  intros (L1 & P1 & N1); repeat split; auto.
  rewrite N1; auto. apply Ple_refl.
Qed.

Lemma mem_lessalloc_lessdef m1 m2 : mem_lessalloc m1 m2 -> mem_lessdef m1 m2.
Proof.
  intros (L1 & P1 & N1); repeat split.
  - rewrite L1; auto.
    intros b ofs len v H.
    exists v; intuition.
    clear.
    induction v; constructor; auto.
    apply memval_lessdef_refl.
  - rewrite P1; auto.
  - auto.
Qed.

Lemma mem_equiv_lessdef m1 m2 : mem_equiv m1 m2 -> mem_lessdef m1 m2.
Proof.
  intro H.
  apply mem_lessalloc_lessdef, mem_equiv_lessalloc, H.
Qed.

Lemma cl_step_mem_lessdef_sim {ge c m1 c' m1' m2} :
  mem_lessdef m1 m2 ->
  @cl_step ge c m1 c' m1' ->
  exists m2',
    mem_lessdef m1' m2' /\
    @cl_step ge c m2 c' m2'.
Admitted.

Lemma cl_step_mem_lessalloc_sim {ge c m1 c' m1' m2} :
  mem_lessalloc m1 m2 ->
  @cl_step ge c m1 c' m1' ->
  exists m2',
    mem_lessalloc m1' m2' /\
    @cl_step ge c m2 c' m2'.
(* we cannot use [cl_step_mem_lessdef_sim] directly because
[mem_lessalloc] does not imply [mem_lessdef] in both
directions. However, the proof must be simpler. *)
Proof.
Admitted.

Lemma cl_step_mem_equiv_sim {ge c m1 c' m1' m2} :
  mem_equiv m1 m2 ->
  @cl_step ge c m1 c' m1' ->
  exists m2',
    mem_equiv m1' m2' /\
    @cl_step ge c m2 c' m2'.
Proof.
  intros E S1.
  pose proof mem_equiv_lessdef _ _ E as L12.
  pose proof mem_equiv_lessdef _ _ (mem_equiv_sym _ _ E) as L21.
  destruct (cl_step_mem_lessdef_sim L12 S1) as (m2' & L12' & S2).
  destruct (cl_step_mem_lessdef_sim L21 S2) as (m1'' & L21' & S1').
  exists m2'; split; auto.
  apply mem_lessdef_equiv; auto.
  cut (m1'' = m1'). intros <-; auto.
  pose proof semax_lemmas.cl_corestep_fun' ge _ _ _ _ _ _ S1 S1'.
  congruence.
Qed.

Definition juicy_mem_equiv jm1 jm2 := mem_equiv (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Definition juicy_mem_lessdef jm1 jm2 := mem_lessdef (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Definition juicy_mem_lessalloc jm1 jm2 := mem_lessdef (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Lemma mem_equiv_juicy_mem_equiv jm1 m2 :
  mem_equiv (m_dry jm1) m2 ->
  exists jm2,
    m_dry jm2 = m2 /\
    juicy_mem_equiv jm1 jm2.
Proof.
  intros E.
  refine (ex_intro _ (mkJuicyMem m2 (m_phi jm1) _ _ _ _) _); repeat (split; auto).
  Unshelve.
  all: destruct jm1 as [m1 phi Con Acc Max All]; simpl in *.
  all: destruct E as (Load & Perm & Next).
    (* I'll admit this for now. It should take less time to prove once
    the new mem interface is there. *)
Admitted.

Lemma mem_lessdef_juicy_mem_lessdef jm1 m2 :
  mem_lessdef (m_dry jm1) m2 ->
  exists jm2,
    m_dry jm2 = m2 /\
    juicy_mem_lessdef jm1 jm2.
Proof.
  (* not sure about that one! [contents_cohere] should be ok, but
  [access_cohere] does not have a reason to be *)
Admitted.

Lemma mem_lessalloc_juicy_mem_lessdef jm1 m2 :
  mem_lessalloc (m_dry jm1) m2 ->
  exists jm2,
    m_dry jm2 = m2 /\
    juicy_mem_lessalloc jm1 jm2.
Proof.
  (* this one is fine, we need to prove that if two memories are
  mem_lessalloc then the difference of nextblock is only None's *)
Admitted.

Lemma juicy_step_mem_equiv_sim {ge c jm1 c' jm1' jm2} :
  juicy_mem_equiv jm1 jm2 ->
  corestep (juicy_core_sem cl_core_sem) ge c jm1 c' jm1' ->
  exists jm2',
    juicy_mem_equiv jm1' jm2' /\
    corestep (juicy_core_sem cl_core_sem) ge c jm2 c' jm2'.
Proof.
  intros [Ed Ew] [step [rd lev]].
  destruct (cl_step_mem_equiv_sim Ed step) as [m2' [Ed' Sd']].
  destruct (mem_equiv_juicy_mem_equiv jm1' m2' Ed') as (jm2', (<-, [Hd Hw])).
  exists jm2'.
  split; split; auto. split.
  - cut (Mem.nextblock (m_dry jm1) = Mem.nextblock (m_dry jm2)). congruence.
    apply Ed.
  - repeat rewrite level_juice_level_phi in *.
    congruence.
Qed.

Ltac sync D :=
  first
    [ split; [destruct D as [D _] | destruct D as [_ D]]
    | destruct D as [D|D]; [left|right]
    | let x := fresh in intro x; spec D x
    ].

Lemma juicy_step_mem_lessdef_sim {ge c jm1 c' jm1' jm2} :
  juicy_mem_lessdef jm1 jm2 ->
  corestep (juicy_core_sem cl_core_sem) ge c jm1 c' jm1' ->
  exists jm2',
    juicy_mem_lessdef jm1' jm2' /\
    corestep (juicy_core_sem cl_core_sem) ge c jm2 c' jm2'.
Proof.
  intros [Ed Ew] [step D].
  destruct (cl_step_mem_lessdef_sim Ed step) as [m2' [Ed' Sd']].
  destruct (mem_lessdef_juicy_mem_lessdef jm1' m2' Ed') as (jm2', (<-, [Hd Hw])).
  exists jm2'.
  split; split; auto.
  repeat rewrite level_juice_level_phi in *.
  
  repeat sync D.
  
  all: try rewrite <-Ew; try rewrite <-Hw; try assumption.
  
  - intros out. apply D.
    unfold mem_lessdef in *.
    zify.
    omega.
  
  - unfold mem_lessdef in *.
    zify.
    Fail omega. (* not true, maybe we can still resource_decay them somehow *)
Admitted.

Definition ext_spec_stable {M E Z} (R : M -> M -> Prop)
           (spec : external_specification M E Z) :=
  (forall e x b tl vl z m1 m2,
    R m1 m2 ->
    ext_spec_pre spec e x b tl vl z m1 ->
    ext_spec_pre spec e x b tl vl z m2) /\
  (forall e v m1 m2,
    R m1 m2 ->
    ext_spec_exit spec e v m1 ->
    ext_spec_exit spec e v m2).

Lemma jsafeN_mem_equiv {Z Jspec ge n z c jm1 jm2} :
  juicy_mem_equiv jm1 jm2 ->
  ext_spec_stable juicy_mem_equiv (JE_spec _ Jspec) ->
  @jsafeN Z Jspec ge n z c jm1 ->
  @jsafeN Z Jspec ge n z c jm2.
Proof.
  intros E [Spre Sexit] S1.
  revert jm2 E.
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 E.
  
  - constructor 1.
  
  - destruct (juicy_step_mem_equiv_sim E step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.
  
  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct E as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.
  
  - econstructor 4; eauto.
Qed.

Lemma jsafeN_mem_lessdef {Z Jspec ge n z c jm1 jm2} :
  juicy_mem_lessdef jm1 jm2 ->
  ext_spec_stable juicy_mem_lessdef (JE_spec _ Jspec) ->
  @jsafeN Z Jspec ge n z c jm1 ->
  @jsafeN Z Jspec ge n z c jm2.
Proof.
  intros L [Spre Sexit] S1.
  revert jm2 L.
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 L.
  
  - constructor 1.
  
  - destruct (juicy_step_mem_lessdef_sim L step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.
  
  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct L as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.
  
  - econstructor 4; eauto.
Qed.

Lemma mem_ext m1 m2 :
  Mem.mem_contents m1 = Mem.mem_contents m2 ->
  Mem.mem_access m1 = Mem.mem_access m2 ->
  Mem.nextblock m1 = Mem.nextblock m2 ->
  m1 = m2.
Proof.
  destruct m1, m2; simpl in *.
  intros <- <- <- .
  f_equal; apply proof_irr.
Qed.
