Require Import veric.rmaps.
Require Import progs.ghost.
Require Import mailbox.general_atomics.
Require Import mailbox.acq_rel_atomics.
Require Import progs.conclib.
Require Import mailbox.maps.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.kvnode_atomic_ra.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition load_acq_spec := DECLARE _load_acq load_acq_spec.
Definition store_rel_spec := DECLARE _store_rel store_rel_spec.

Definition surely_malloc_spec :=
 DECLARE _surely_malloc
   WITH n:Z
   PRE [ _n OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh n p * memory_block Tsh n p).

Definition tnode := Tstruct _node noattr.

Definition has_size : {x : Z | x = 8}.
Proof.
  eexists; eauto.
Qed.

Definition size := proj1_sig has_size.
Lemma size_def : size = 8.
Proof.
  apply (proj2_sig has_size).
Qed.

(* Lexicographic ordering doesn't lead to a PCM (it's not associative), so we keep a full log of values. *)

(* In this example, all the resources held in the protocols are snapshots, so the full and read interpretations
   are equal. *)

(* This is a bit messy to allow the mutually recursive protocol interpretations. *)
Definition data_T' version version_T s (v : Z) := EX ver : Z, !!(Z.even ver = true /\ log_latest s ver v) &&
  protocol_R version (ver - 1) Z.le (version_T, version_T).

Definition version_T_fun version locs g : (Z * Z -> mpred) -> (Z * Z -> mpred) :=
  fun R '(s, v) => !!(v = s) && EX L : _,
  !!(exists vs, Zlength vs = size /\ log_latest L (if Z.even v then v else v - 1) vs) &&
  fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef) (map_Znth i L 0) map_incl
    (data_T' version (fun s v => |>R (s, v)), data_T' version (fun s v => |>R (s, v)))) (upto (Z.to_nat size))) *
  ghost_snap L g.

Definition version_T' version locs g := HORec (version_T_fun version locs g).
Definition version_T version locs g s v := version_T' version locs g (s, v).

Definition data_T version locs g := data_T' version (|>version_T version locs g).

Lemma version_T'_eq version locs g : version_T' version locs g =
  version_T_fun version locs g (version_T' version locs g).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 (s, v).
  unfold version_T_fun.
  apply subp_andp; [apply subp_refl|].
  apply subp_exp; intro L.
  apply subp_sepcon; [|apply subp_refl].
  apply subp_andp; [apply subp_refl|].
  pose proof (fold_right_sepcon_nonexpansive
    (map (fun i => protocol_R (Znth i locs Vundef) (map_Znth i L 0) map_incl
      (data_T' version (fun s v => |>P1 (s, v)), data_T' version (fun s v => |>P1 (s, v)))) (upto (Z.to_nat size)))
    (map (fun i => protocol_R (Znth i locs Vundef) (map_Znth i L 0) map_incl
      (data_T' version (fun s v => |>P2 (s, v)), data_T' version (fun s v => |>P2 (s, v)))) (upto (Z.to_nat size)))) as H.
  rewrite fash_andp in H.
  eapply derives_trans; [eapply derives_trans, H; [|rewrite !Zlength_map; auto] | apply andp_left1; auto].
  apply allp_right; intro i.
  destruct (zlt i 0); [rewrite !Znth_underflow by auto; apply eqp_refl|].
  destruct (zlt i (Zlength (upto (Z.to_nat size))));
    [|rewrite !Znth_overflow by (rewrite Zlength_map; auto); apply eqp_refl].
  erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
  eapply derives_trans, protocol_piece_nonexpansive.
  apply allp_right; intro s1.
  apply allp_right; intro v1.
  unfold data_T'.
  eapply derives_trans, andp_right, derives_refl; auto.
  apply eqp_exp; intro ver.
  apply eqp_andp; [apply eqp_refl|].
  eapply derives_trans, protocol_piece_nonexpansive.
  apply allp_right; intro s2.
  apply allp_right; intro v2.
  apply allp_left with (s2, v2), andp_right; apply derives_refl.
Qed.

Lemma version_T_eq version locs g s v : version_T version locs g s v = !!(v = s) && EX L : _,
  !!(exists vs, Zlength vs = size /\ log_latest L (if Z.even v then v else v - 1) vs) &&
  fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef) (map_Znth i L 0) map_incl
    (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size))) * ghost_snap L g.
Proof.
  intros; unfold version_T.
  etransitivity; [rewrite version_T'_eq; reflexivity | auto].
Qed.

Lemma data_T_eq version locs g s v : data_T version locs g s v =
  EX ver : Z, !!(Z.even ver = true /\ log_latest s ver v) &&
    protocol_R version (ver - 1) Z.le (|>version_T version locs g, |>version_T version locs g).
Proof. auto. Qed.

(* up *)
Global Instance dup_protocol {state} (T : state -> Z -> mpred) (Ht : forall s v, duplicable (T s v)) :
  protocol T T.
Proof.
  split; auto.
Qed.

Existing Instance max_PCM.
Existing Instance max_order.
Existing Instance fmap_PCM.
Existing Instance fmap_order.

Lemma data_T_duplicable : forall version locs g s v, duplicable (data_T version locs g s v).
Proof.
  intros; rewrite data_T_eq.
  apply exp_duplicable; intro.
  apply prop_duplicable, protocol_R_duplicable.
Qed.

Instance data_prot version locs g : protocol (data_T version locs g) (data_T version locs g).
Proof.
  apply dup_protocol, data_T_duplicable.
Qed.

Lemma version_T_duplicable : forall version locs g s v, duplicable (version_T version locs g s v).
Proof.
  intros; rewrite version_T_eq.
  apply prop_duplicable, exp_duplicable; intro.
  apply sepcon_duplicable, ghost_snap_duplicable.
  apply prop_duplicable, sepcon_list_duplicable.
  rewrite Forall_map, Forall_forall; intros.
  apply protocol_R_duplicable.
Qed.

Instance version_prot version locs g : protocol (version_T version locs g) (version_T version locs g).
Proof.
  apply dup_protocol, version_T_duplicable.
Qed.

(* The collection of protocol assertions that describes a stable state of the node. *)
Definition node_state (sh : share) (L : Z -> option (list Z)) v version locs g :=
  !!(Z.even v = true /\ exists vs, Zlength vs = size /\ log_latest L v vs) &&
  protocol_piece sh version v Z.le (version_T version locs g, version_T version locs g) *
  fold_right sepcon emp (map (fun i => protocol_piece sh (Znth i locs Vundef) (map_Znth i L 0) map_incl
    (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size))) * ghost (sh, L) g.

Program Definition read_spec := DECLARE _read atomic_spec
  (ConstType (val * val * share * share * val * list val * val * (Z -> option (list Z)) * Z))
  empty_map [(_n, tptr tnode); (_out, tptr tint)] tvoid
  [fun _ '(n, out, sh, shi, version, locs, g, L0, v0) => temp _n n;
   fun _ '(n, out, sh, shi, version, locs, g, L0, v0) => temp _out out]
  (fun _ '(n, out, sh, shi, version, locs, g, L0, v0) => !!(readable_share sh /\
     writable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size) &&
   data_at sh tnode (version, locs) n * data_at_ shi (tarray tint size) out *
   node_state Share.bot L0 v0 version locs g)
  (fun _ '(n, out, sh, shi, version, locs, g, L0, v0) L => ghost (gsh1, L) g)
  (0, []) []
  (fun _ '(n, out, sh, shi, version, locs, g, L0, v0) L '(v, vals) =>
   !!(v0 <= v /\ Zlength vals = size /\ (v = v0 -> L0 v = Some vals)) &&
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) out *
   node_state Share.bot (singleton v vals) v version locs g)
  (fun _ '(n, out, sh, shi, version, locs, g, L0, v0) L '(v, vals) => !!(L v = Some vals) && ghost (gsh1, L) g)
  _ _ _ _ _ _.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.

Program Definition write_spec := DECLARE _write atomic_spec
  (ConstType (val * val * share * share * val * list val * list Z * val * (Z -> option (list Z)) * Z))
  (@empty_map Z (list Z)) [(_n, tptr tnode); (_in, tptr tint)] tvoid
  [fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) => temp _n n;
   fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) => temp _in input]
  (fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) => !!(readable_share sh /\
     readable_share shi /\ isptr version /\ Forall isptr locs /\ Zlength locs = size /\
     Forall repable_signed vals) &&
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state gsh2 L v0 version locs g)
  (fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) L' => ghost (gsh1, L') g)
  tt []
  (fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) _ _ =>
   data_at sh tnode (version, locs) n * data_at shi (tarray tint size) (map (fun x => vint x) vals) input *
   node_state gsh2 (map_upd L (v0 + 2) vals) (v0 + 2) version locs g)
  (fun _ '(n, input, sh, shi, version, locs, vals, g, L, v0) _ _ => ghost (gsh1, map_upd L (v0 + 2) vals) g)
  _ _ _ _ _ _.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.
Next Obligation.
Proof.
  intros ?? w; decompose [prod] w; auto.
Qed.

Definition make_node_spec := DECLARE _make_node
  WITH u : unit
  PRE [ ]
    PROP ()
    LOCAL ()
    SEP ()
  POST [ tptr tnode ]
   EX n : val, EX version : val, EX locs : list val, EX g : val,
    PROP (isptr version; Forall isptr locs; Zlength locs = size)
    LOCAL (temp ret_temp n)
    SEP (data_at Tsh tnode (version, locs) n; malloc_token Tsh (sizeof tnode) n;
         malloc_token Tsh (sizeof tint) version; fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) locs);
         node_state gsh2 (singleton 0 (repeat 0 (Z.to_nat size))) 0 version locs g;
         ghost (gsh1, singleton 0 (repeat 0 (Z.to_nat size))) g).

Definition writer_spec := DECLARE _writer
  WITH n : val, sh : share, v : Z, L : Z -> option (list Z), version : val, locs : list val, g : val
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; node_state gsh2 L v version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g))
  POST [ tptr tvoid ]
   EX L' : _,
    PROP (L' = map_upd_list L (map (fun i => (v + (2 * (i + 1)), repeat (i + 1) (Z.to_nat size)))%Z (upto 3)))
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state gsh2 L' (v + 6) version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g)).

(*Definition reader_spec := DECLARE _reader
  WITH n : val, sh : share, version : val, locs : list val, g : val, g' : val,
       lg : list val, lg' : list val, gh : val, gsh : share
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size; gsh <> Share.bot)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; ghost_hist gsh ([] : hist) gh;
         invariant (node_inv gh version locs g g' lg lg'))
  POST [ tptr tvoid ]
   EX h : hist,
    PROP (exists v vs, add_events [] [HRead v vs] h)
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; ghost_hist gsh h gh;
         invariant (node_inv gh version locs g g' lg lg')).*)

(* We can't keep an interleaved history of reads and writes, but we can know that each read got a value
   that was at some point in the history. *)
(*Program Definition reader_spec := DECLARE _reader atomic_spec
  (ConstType (val * share * val * list val * val * val * list val * list val * val * share))
  tt [(_n, tptr tvoid)] (tptr tvoid)
  [fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) => temp _n n]
  (fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) => !!(readable_share sh /\ isptr version /\
   Forall isptr locs /\ Zlength locs = size /\ gsh <> Share.bot) && data_at sh tnode (version, locs) n)
  (fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) _ => node_inv gh version locs g g' lg lg')
  (0, []) []
  (fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) _ _ => data_at sh tnode (version, locs) n)
  (fun _ '(n, sh, version, locs, g, g', lg, lg', gh, gsh) _ '(v1, vs1) =>
   EX v : Z, EX vs : list Z, node_state v vs version locs g g' lg lg' * EX hr : _,
     !!(apply_hist (0, repeat 0 (Z.to_nat size)) hr = Some (v, vs) /\ In (HWrite v1 vs1) hr) && ghost_ref hr gh)
  _ _ _ _ _ _. (* We could encapsulate this with another argument to node_inv, a known sublist of hr. *)*)

Definition reader_spec := DECLARE _reader
  WITH n : val, sh : share, v : Z, L : Z -> option (list Z), version : val, locs : list val, g : val
  PRE [ _n OF tptr tvoid ]
    PROP (readable_share sh; isptr version; Forall isptr locs; Zlength locs = size)
    LOCAL (temp _n n)
    SEP (data_at sh tnode (version, locs) n; node_state Share.bot L v version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g))
  POST [ tptr tvoid ]
   EX v' : Z, EX vs' : list Z,
    PROP (v <= v'; v' = v -> Z.even v = true /\ L v = Some vs')
    LOCAL ()
    SEP (data_at sh tnode (version, locs) n; node_state Share.bot (map_upd L v' vs') v' version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g)).

Definition Gprog : funspecs := ltac:(with_library prog [surely_malloc_spec; load_acq_spec; store_rel_spec;
  read_spec; write_spec; make_node_spec; writer_spec; reader_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
  - if_tac; entailer!.
  - forward_call tt.
    contradiction.
  - if_tac.
    + forward. subst p. discriminate.
    + Intros. forward. entailer!.
  - forward. Exists p; entailer!.
Qed.

Lemma land_1 : forall i, Z.land i 1 = i mod 2.
Proof.
  intros; apply Z.land_ones with (n := 1); omega.
Qed.

Definition list_max v l := fold_right Z.max v l.

Lemma list_max_app : forall v l1 l2, list_max v (l1 ++ l2) = list_max (list_max v l2) l1.
Proof.
  intros; apply fold_right_app.
Qed.

Lemma list_max_max : forall l v1 v2, Z.max v1 (list_max v2 l) = list_max (Z.max v1 v2) l.
Proof.
  induction l; auto; simpl; intros.
  rewrite Z.max_assoc, !IHl.
  rewrite Z.max_assoc, (Z.max_comm a); auto.
Qed.

Lemma list_max_spec : forall l v, v <= list_max v l /\ Forall (fun v' => v' <= list_max v l) l.
Proof.
  induction l; simpl; intros.
  - split; auto; omega.
  - rewrite list_max_max.
    destruct (IHl (Z.max a v)) as [H]; split; [|repeat constructor; auto].
    + etransitivity; eauto; apply Zle_max_r.
    + etransitivity; eauto; apply Zle_max_l.
Qed.

Lemma protocol_R_single : forall version locs l log g v v', log v = Some v' ->
  view_shift (protocol_R l log map_incl (data_T version locs g, data_T version locs g))
             (protocol_R l (singleton v v') map_incl (data_T version locs g, data_T version locs g)).
Proof.
  intros; apply protocol_R_forget.
  unfold singleton; intros ??; if_tac; [|discriminate].
  intro X; inv X; auto.
Qed.

Lemma node_state_snap : forall sh L v version locs g,
  view_shift (node_state sh L v version locs g)
             (node_state sh L v version locs g * node_state Share.bot L v version locs g).
Proof.
  intros; unfold node_state; view_shift_intros.
  rewrite !sepcon_assoc.
  etransitivity; [apply view_shift_sepcon1, make_protocol_R|].
  etransitivity; [apply view_shift_sepcon2|].
  - apply view_shift_sepcon, make_snap.
    apply view_shift_sepcon_list.
    { rewrite 2Zlength_map; reflexivity. }
    rewrite Zlength_map; intros.
    erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    apply make_protocol_R.
  - rewrite sepcon_map.
    apply derives_view_shift; entailer!.
Qed.

(* up *)
(* simple load_acq with read assertion *)
Definition load_acq_witness {state} l (s : state) st_ord T P Q := (l, s, st_ord, T, protocol_R l s st_ord T * P,
  fun _ : Z => FF, @nil Z, P, fun s' (v' : Z) => protocol_R l s' st_ord T * Q s' v').

(* simple load_acq with write assertion *)
Definition load_acq_W_witness {state} l (s : state) st_ord T P Q := (l, s, st_ord, T, protocol_W l s st_ord T * P,
  fun _ : Z => FF, @nil Z, protocol_W l s st_ord T * P,
  fun s' (v' : Z) => !!(s' = s) && protocol_W l s st_ord T * Q s' v').

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_atomic_function.
  destruct x as ((((((((n, out), sh), shi), version), locs), g), L0), v0); Intros.
  destruct H as (HP0 & HP & HQ).
  rewrite map_map in HP, HQ.
  assert (0 <= size) by (rewrite size_def; computable).
  unfold node_state; Intros.
  match goal with H : exists vs, _ |- _ => destruct H as [vs0 [? [HL0 ?]]] end.
  apply semax_pre with (P' := PROP () LOCAL (temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n; data_at_ shi (tarray tint size) out;
         EX v : Z, !!(v0 <= v) && protocol_R version v Z.le (version_T version locs g, version_T version locs g);
         EX ll : _, fold_right sepcon emp (map (fun i =>
           protocol_R (Znth i locs Vundef) (Znth i ll empty_map) map_incl (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size)));
         EX L' : _, ghost_snap (map_add L0 L') g;
         fold_right sepcon emp (map (fun p : Z => invariant (II p)) lI); P)).
  { unfold node_state; Intros.
    Exists v0 (map (fun i => map_Znth i L0 0) (upto (Z.to_nat size))) (@empty_map Z (list Z));
      rewrite map_add_empty; entailer!.
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite In_upto in *; erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega. }
  eapply semax_loop; [|forward; unfold loop2_ret_assert; apply drop_tc_environ].
  Intros v ll L'.
  repeat forward.
  forward_call_dep [Z : Type] (load_acq_witness version v Z.le
    (version_T version locs g, version_T version locs g) emp (version_T version locs g)).
  { simpl; cancel. }
  { simpl; split; intros; rewrite ?emp_sepcon, ?sepcon_emp; try reflexivity.
    rewrite sepcon_comm; reflexivity. }
  Intro x; rewrite version_T_eq; Intros L1; destruct x as (v1', v1); simpl in *; subst.
  gather_SEP 7 3; rewrite map_snap_join; Intros.
  gather_SEP 3 6; rewrite <- sepcon_map; eapply view_shift_sepcon_list with (l2 := map _ (upto (Z.to_nat size)));
    rewrite ?Zlength_map; auto; intros.
  { erewrite !Znth_map, !Znth_upto by (auto; rewrite ?Zlength_upto in *; omega).
    apply protocol_R_choose. }
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP (Z.even v1 = true) (LOCALx Q (SEPx R))) end.
  { eapply semax_pre; [|apply semax_continue].
    unfold POSTCONDITION, abbreviate, overridePost.
    destruct (eq_dec EK_continue EK_normal); [discriminate|].
    unfold loop1_ret_assert.
    go_lower.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_even in *.
    destruct (Z.even v1) eqn: Hodd; try contradiction.
    Exists v1 (map (fun i => map_Znth i L1 0) (upto (Z.to_nat size))) (map_add L' L1);
      rewrite map_add_assoc; entailer!.
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite In_upto in *; erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega. }
  { forward.
    entailer!.
    unfold Int.one in *; rewrite and_repr, land_1, Zmod_even in *.
    destruct (Z.even v1); auto; discriminate. }
  Intros.
  destruct (Z.even v1) eqn: Hv1; try discriminate.
  forward_for_simple_bound 8 (EX i : Z, EX vals : list Z, PROP (Zlength vals = i)
    LOCAL (temp _snap (vint v1); temp _ver version; temp _n n; temp _out out)
    SEP (@data_at CompSpecs sh tnode (version, locs) n;
         data_at shi (tarray tint size) (map (fun x => vint x) vals ++ repeat Vundef (Z.to_nat (size - i))) out;
         EX vers' : list Z, !!(Zlength vers' = i /\ Forall (fun v => Z.even v = true /\ v1 <= v) vers' /\
           forall j, 0 <= j < i -> forall v, map_Znth j L1 0 (Znth j vers' 0) = Some v -> v = Znth j vals 0) &&
           protocol_R version (list_max v1 (map (fun x => x - 1) vers')) Z.le (version_T version locs g, version_T version locs g) *
           fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef)
             (singleton (Znth i vers' 0) (Znth i vals 0)) map_incl (data_T version locs g, data_T version locs g)) (sublist 0 i (upto (Z.to_nat size))));
         fold_right sepcon emp (map (fun i => protocol_R (Znth i locs Vundef) (map_Znth i L1 0) map_incl
           (data_T version locs g, data_T version locs g)) (sublist i size (upto (Z.to_nat size)))); ghost_snap (map_add (map_add L0 L') L1) g;
         fold_right sepcon emp (map (fun p : Z => invariant (II p)) lI); P)).
  { Exists (@nil Z) (@nil Z).
    rewrite data_at__eq; unfold default_val; simpl data_at.
    rewrite repeat_list_repeat, Z.sub_0_r; entailer!.
    { intros; omega. }
    rewrite sublist_same by (auto; rewrite Zlength_upto, Z2Nat.id; auto); auto. }
  - Intros vers'.
    match goal with H : 0 <= i < _ |- _ => rewrite <- size_def in H end.
    forward.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    { rewrite <- size_def; apply prop_right; auto. }
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl.
    forward_call_dep [Z -> option Z : Type] (load_acq_witness (Znth i locs Vundef) (map_Znth i L1 0) map_incl
      (data_T version locs g, data_T version locs g)
      (protocol_R version (list_max v1 (map (fun x0 : Z => x0 - 1) vers')) Z.le
        (version_T version locs g, version_T version locs g))
      (fun s (v : Z) => EX v' : Z, !!(Z.even v' = true /\ log_latest s v' v) &&
        |>protocol_R version (list_max v1 (map (fun x => x - 1) (vers' ++ [v']))) Z.le (version_T version locs g, version_T version locs g))).
    { simpl; cancel. }
    { split; simpl; intros; rewrite !emp_sepcon; [reflexivity|].
      rewrite data_T_eq.
      view_shift_intro ver; view_shift_intros.
      
Axiom protocol_later : forall {state} sh l (s : state) ord Tread Tfull,
  protocol_piece sh l s ord (|>Tread, |>Tfull) |-- |>protocol_piece sh l s ord (Tread, Tfull).

      rewrite sepcon_comm, <- sepcon_assoc.
      etransitivity; [apply view_shift_sepcon1, view_shift_sepcon;
        apply derives_view_shift; [apply now_later | apply protocol_later]|].
      rewrite <- later_sepcon; setoid_rewrite protocol_R_join; [|simpl; eauto].
      apply derives_view_shift; Exists ver; entailer!.
      apply later_derives.
      rewrite map_app, list_max_app; simpl.
      rewrite Z.max_comm, list_max_max; auto. }
    Intros y v'; destruct y as (d, log'); simpl in *.
    focus_SEP 1; eapply protocol_R_single.
    { match goal with H : log_latest _ _ _ |- _ => destruct H; eauto end. }
    forward.
    go_lower; Exists (x ++ [d]) (vers' ++ [v']); rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    match goal with H : exists vs, _ /\ log_latest _ _ _ |- _ => destruct H as (vs1 & ? & HL1) end.
    rewrite <- size_def, upd_init, !map_app, <- app_assoc by (rewrite ?Zlength_map; omega).
    entailer!.
    { split.
      + rewrite Forall_app; repeat constructor; auto.
        eapply log_incl_latest; eauto.
        unfold map_Znth, map_add.
        destruct HL1 as [->]; simpl; eauto.
      + intros ??? Hv.
        destruct (eq_dec j (Zlength x)).
        * subst; rewrite app_Znth2 in Hv |- * by omega.
          replace (Zlength vers') with (Zlength x) in Hv; rewrite Zminus_diag, Znth_0_cons in Hv |- *.
          match goal with H : map_incl _ log' |- _ => pose proof (H _ _ Hv) as Heq end.
          match goal with H : log_latest log' _ _ |- _ => destruct H as [Hv']; rewrite Hv' in Heq end.
          inv Heq; auto.
        * rewrite app_Znth1 in Hv |- * by omega; match goal with H : forall j, _ |- _ => apply H; auto; omega end. }
    rewrite sublist_split with (mid := Zlength x)(hi := Zlength x + 1)
      by (rewrite ?Zlength_upto, ?Z2Nat.id; simpl; omega).
    erewrite sublist_len_1, Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; simpl; omega).
    rewrite map_app, sepcon_app; simpl.
    rewrite !app_Znth2 by omega.
    replace (Zlength vers') with (Zlength x); rewrite Zminus_diag, !Znth_0_cons; simpl; cancel.
    apply sepcon_list_derives; rewrite !Zlength_map; auto.
    intros ? Hi; erewrite !Znth_map by auto.
    rewrite Zlength_sublist in Hi by (rewrite ?Zlength_upto, ?Z2Nat.id; simpl; omega).
    rewrite !Znth_sublist, !Znth_upto by (rewrite ?Z2Nat.id; simpl; omega).
    rewrite !app_Znth1 by omega; auto.
  - Intros vals' vers'; rewrite <- size_def in *.
    rewrite Zminus_diag, app_nil_r, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto).
    forward_call_dep [Z : Type] (load_acq_witness version (list_max v1 (map (fun x => x - 1) vers')) Z.le
      (version_T version locs g, version_T version locs g) emp (fun s v : Z => !!(v = s) && emp)).
    { simpl; cancel. }
    { simpl; split; intros; rewrite ?emp_sepcon, ?sepcon_emp; [reflexivity|].
      rewrite version_T_eq; apply derives_view_shift; entailer!.
      (* Iris assumes that anything duplicable has empty footprint, and anyway doesn't care about throwing away
         resources. Should we make that assumption, or adjust the load rule? *)
      admit. }
    Intros x; destruct x as (v2', v2); simpl in *; subst.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (v2 <> v1) (LOCALx Q (SEPx R))) end.
    + subst.
      rewrite <- (map_map II).
      assert (forall j, 0 <= j < size -> Znth j vers' 0 = v1) as Hvers.
      { intros; match goal with H : Forall _ vers' |- _ => apply Forall_Znth with (i := j)(d := 0) in H;
          [destruct H as [Heven] | omega] end.
        destruct (list_max_spec (map (fun x => x - 1) vers') v1) as [_ Hmax].
        rewrite Forall_map in Hmax.
        apply Forall_Znth with (i := j)(d := 0) in Hmax; [simpl in Hmax | omega].
        destruct (eq_dec (Znth j vers' 0) v1); subst; auto.
        assert (Znth j vers' 0 = v1 + 1) as Heq by omega.
        rewrite Heq, Z.even_add in Heven; replace (Z.even v1) with true in Heven; discriminate. }
      match goal with H : exists vs, _ |- _ => destruct H as [? [? [HL1]]] end.
      assert (L1 v1 = Some vals') as Hvals'.
      { eapply map_Znth_eq.
        * intro; rewrite HL1; intro X; inv X; omega.
        * intro; subst; rewrite size_def in *; discriminate.
        * intros; unfold map_Znth in *; rewrite HL1; simpl.
          match goal with H : forall j, _ |- _ => apply f_equal, H; [omega|] end.
          rewrite Hvers, HL1 by omega; auto. }
      gather_SEP 6 8 7; rewrite <- !sepcon_assoc; apply invariants_view_shift with
        (Q0 := ghost_snap (singleton v1 vals') g * EX L : _, Q L (v1, vals')).
      { rewrite !map_map, !sepcon_assoc, (sepcon_comm P).
        etransitivity; [apply view_shift_sepcon2, HP|].
        view_shift_intro L2.
        etransitivity; [|apply derives_view_shift; Exists L2; apply derives_refl].
        rewrite (sepcon_comm (Q _ _)).
        etransitivity; [|apply view_shift_sepcon2, HQ]; simpl.
        rewrite <- sepcon_assoc, snap_master_join by auto.
        view_shift_intros; etransitivity; [apply view_shift_sepcon1, make_snap|].
        match goal with H : map_incl _ L2 |- _ => exploit (H v1 vals') end.
        { rewrite map_add_comm by auto.
          unfold map_add; rewrite Hvals'; auto. }
        rewrite sepcon_assoc; etransitivity;
          [apply view_shift_sepcon1, ghost_snap_forget with (v2 := singleton v1 vals'); auto|].
        { intros ??; unfold singleton; if_tac; intro X; inv X; auto. }
        apply derives_view_shift; entailer!. }
      Intros L2.
      forward.
      rewrite map_map; Exists (v1, vals') L2; unfold node_state, protocol_R, ghost_snap, share; entailer!.
      { split.
        * intro; subst; rewrite HL0; match goal with H : compatible _ _ |- _ => eapply f_equal, H; eauto end.
          unfold map_add; rewrite HL0; auto.
        * do 2 eexists; [|apply log_latest_singleton]; auto. }
      erewrite map_ext_in; eauto; intros; simpl.
      rewrite map_Znth_single, Hvers; auto.
      rewrite In_upto, Z2Nat.id in *; auto.
    + forward.
      entailer!.
    + intros; unfold overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      unfold POSTCONDITION, abbreviate, loop1_ret_assert.
      Intros; go_lower; Exists v2 (map (fun i => singleton (Znth i vers' 0) (Znth i vals' 0))
        (upto (Z.to_nat size))) (map_add L' L1); rewrite map_add_assoc; entailer!.
      { destruct (list_max_spec (map (fun x => x - 1) vers') v1); omega. }
      erewrite map_ext_in; eauto; intros; simpl.
      rewrite In_upto in *; erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; omega.
Admitted.

(* simple store_rel recovering write assertion *)
Definition store_rel_witness {state} l (v : Z) (s s'' : state) st_ord T P Q := (l, v, s, s'', st_ord, T,
  protocol_W l s st_ord T * P, fun _ : Z => FF, @nil Z, P, protocol_W l s'' st_ord T * Q).

(* Is there any use to allowing RA atomics to interact with invariants if they can't take or leave protocol
   assertions? Possibly. *)
(* Since the public view of the data structure has no data content (it's just the ghost state), there's no need
   for the backing-out linearization point reasoning (and in fact the linearization point can be anywhere,
   since all new write really guarantees is that no other data will be written at that version, plus maybe a
   certain eventual consistency). *)
Lemma body_write : semax_body Vprog Gprog f_write write_spec.
Proof.
  start_atomic_function.
  destruct x as (((((((((n, input), sh), shi), version), locs), vals), g), L), v0); Intros.
  destruct H as (HP0 & HP & HQ).
  forward.
  rewrite map_map in HP, HQ.
  unfold node_state; Intros.
  forward_call_dep [Z : Type] (load_acq_W_witness version v0 Z.le (version_T version locs g, version_T version locs g)
    emp (fun s v : Z => !!(v = s) && emp)).
  { simpl; unfold protocol_W; cancel. }
  { simpl; split; intros; rewrite !emp_sepcon, !sepcon_emp.
    { rewrite sepcon_comm; apply make_protocol_R. }
    rewrite sepcon_assoc; etransitivity;
      [apply view_shift_sepcon2; rewrite sepcon_comm; apply protocol_R_absorb; auto|].
    view_shift_intros; assert (s' = v0) by omega.
    apply derives_view_shift; rewrite version_T_eq; unfold protocol_W; entailer!.
    admit. (* as above *) }
  Intros x; destruct x as (?, v); simpl in *; subst.
  assert (repable_signed (v0 + 1)) by admit. (* version stays in range *)
  forward_call_dep [Z : Type] (store_rel_witness version (v0 + 1) v0 (v0 + 1) Z.le
    (version_T version locs g, version_T version locs g) emp emp).
  { simpl; cancel. }
  { split; auto; split; [|split; [|omega]]; intros; simpl; rewrite !sepcon_emp, ?emp_sepcon; [reflexivity|].
    rewrite !version_T_eq.
    apply derives_view_shift; Intros L1; Exists L1.
    subst; rewrite Z.even_add, Z.add_simpl_r, H in *; simpl; entailer!. }
  assert (0 <= size) by (rewrite size_def; computable).
  assert_PROP (Zlength (map (fun x => vint x) vals) = size) by entailer!.
  assert (Z.even (v0 + 2) = true) by (rewrite Z.even_add; replace (Z.even v0) with true; auto).
  rewrite <- seq_assoc.
  focus_SEP 4.
  match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
  forward_for_simple_bound 8 (EX i : Z, PROP () (LOCALx Q
    (SEPx (fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef)
             (map_Znth i (map_upd L (v0 + 2) vals) 0) map_incl (data_T version locs g, data_T version locs g))
             (sublist 0 i (upto (Z.to_nat size)))) ::
           fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef)
             (map_Znth i L 0) map_incl (data_T version locs g, data_T version locs g))
             (sublist i size (upto (Z.to_nat size)))) :: R)))) end.
  { rewrite sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto).
    replace (Z.even v0) with true; entailer!. }
  - (* loop body *)
    Intros; forward; rewrite <- size_def in *.
    { entailer!.
      apply Forall_Znth; [omega|].
      eapply Forall_impl; [|eauto]; auto. }
    forward.
    erewrite sublist_next with (i0 := i), Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl.
    rewrite Zlength_map in *.
    match goal with H : exists vs, _ |- _ => destruct H as [vs0 [? ?]] end.
    destruct (log_latest_upd (map_Znth i L 0) v0 (Znth i vs0 0) (v0 + 2) (Znth i vals 0)); auto; try omega.
    { apply map_Znth_log_latest; auto. }
    forward_call_dep [Z -> option Z : Type] (store_rel_witness (Znth i locs Vundef) (Znth i vals 0)
      (map_Znth i L 0) (map_upd (map_Znth i L 0) (v0 + 2) (Znth i vals 0)) map_incl (data_T version locs g, data_T version locs g)
      (protocol_W version (v0 + 1) Z.le (version_T version locs g, version_T version locs g))
      (protocol_W version (v0 + 1) Z.le (version_T version locs g, version_T version locs g))).
    { simpl; cancel. }
    { split; [apply Forall_Znth; auto; omega|].
      assert (0 <= i < Zlength (upto (Z.to_nat size))) by (rewrite Zlength_upto, Z2Nat.id; auto; omega).
      split; [|split; auto]; intros; simpl; rewrite ?emp_sepcon, ?sepcon_emp; [reflexivity|].
      rewrite !data_T_eq; view_shift_intro ver; view_shift_intros.
      rewrite sepcon_comm; etransitivity; [apply view_shift_sepcon1, make_protocol_R|].
      apply derives_view_shift; Exists (v0 + 2).
      rewrite <- Z.add_sub_assoc; simpl; unfold protocol_W; entailer!.

Axiom protocol_delay : forall {state} sh l (s : state) ord Tread Tfull,
  protocol_piece sh l s ord (Tread, Tfull) |-- protocol_piece sh l s ord (|>Tread, |>Tfull).

      eapply derives_trans; [apply sepcon_derives, derives_refl; apply protocol_delay|].
      simpl; unfold protocol_R; cancel.
      admit. (* as above *) }
    erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, Znth_upto, map_app, sepcon_app
      by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega); simpl fold_right.
    rewrite <- size_def, map_Znth_upd; entailer!.
  - rewrite <- size_def, sublist_nil, sublist_same by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega).
    assert (repable_signed (v0 + 2)) by admit.
    match goal with H : exists vs, _ |- _ => destruct H as [vs0 [? ?]] end.
    destruct (log_latest_upd L v0 vs0 (v0 + 2) vals); auto; try omega.
    forward_call_dep [Z : Type] (version, v0 + 2, v0 + 1, v0 + 2, Z.le, (version_T version locs g, version_T version locs g),
      P * protocol_W version (v0 + 1) Z.le (version_T version locs g, version_T version locs g) *
        fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef) (map_Znth i (map_upd L (v0 + 2) vals) 0)
          map_incl (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size))) * ghost (gsh2, L) g, II, lI,
      fold_right sepcon emp (map (fun i => protocol_W (Znth i locs Vundef) (map_Znth i (map_upd L (v0 + 2) vals) 0)
          map_incl (data_T version locs g, data_T version locs g)) (upto (Z.to_nat size))) * ghost (Tsh, L) g * R L,
      Q L tt * node_state gsh2 (map_upd L (v0 + 2) vals) (v0 + 2) version locs g).
    { fast_cancel. }
    { split; [auto | split; [| split; [|omega]]].
      + rewrite <- !sepcon_assoc, 2sepcon_assoc; etransitivity; [apply view_shift_sepcon1, HP|].
        view_shift_intro L1.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)), <- !sepcon_assoc.
        rewrite (sepcon_comm (ghost _ _)); setoid_rewrite ghost_var_share_join'; eauto.
        apply derives_view_shift; entailer!.
      + intros; simpl.
        rewrite !sepcon_assoc, (sepcon_comm (version_T _ _ _ (v0 + 2) _)).
        rewrite <- !sepcon_assoc, 4sepcon_assoc.
        etransitivity; [|apply view_shift_sepcon1, HQ].
        rewrite !version_T_eq; view_shift_intro L'; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right _ _ _)).
        rewrite <- !sepcon_assoc, <- sepcon_map.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, view_shift_sepcon_list|].
        { rewrite 2Zlength_map; reflexivity. }
        { rewrite Zlength_map; intros.
          erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
          etransitivity; [apply protocol_R_absorb; auto|].
          apply view_shift_prop; intro; apply make_protocol_R. }
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_snap _ _)).
        rewrite <- !sepcon_assoc, snap_master_join by apply Share.nontrivial; view_shift_intros.
        rewrite !sepcon_assoc; etransitivity.
        { apply view_shift_sepcon1; etransitivity.
          * apply master_update with (v' := map_upd L (v0 + 2) vals); auto.
          * apply make_snap. }
        fold (ghost_var Tsh (map_upd L (v0 + 2) vals) g).
        erewrite <- ghost_var_share_join by eauto.
        apply derives_view_shift; Exists (map_upd L (v0 + 2) vals).
        rewrite Zlength_map in *; rewrite sepcon_map.
        rewrite Z.even_add; replace (Z.even v0) with true; simpl.
        unfold ghost_var, node_state; entailer!.
        split; eauto. }
    forward.
    Exists tt L.
    rewrite Zlength_map in *; entailer!.
Admitted.

(* up *)
Lemma list_duplicate : forall Q lP, duplicable Q ->
  view_shift (fold_right sepcon emp lP * Q) (fold_right sepcon emp (map (sepcon Q) lP) * Q).
Proof.
  induction lP; simpl; intros; [reflexivity|].
  rewrite sepcon_assoc; etransitivity; [apply view_shift_sepcon2, IHlP; auto|].
  rewrite <- sepcon_assoc; etransitivity; [apply view_shift_sepcon2, H|].
  apply derives_view_shift; cancel.
Qed.

Lemma body_make_node : semax_body Vprog Gprog f_make_node make_node_spec.
Proof.
  start_function.
  forward_malloc tnode n.
  forward_malloc tint p.
  repeat forward.
  forward_for_simple_bound 8 (EX i : Z, EX ld : list val, PROP (Zlength ld = i; Forall isptr ld)
    LOCAL (temp _n n)
    SEP (malloc_token Tsh (sizeof tint) p; data_at Tsh tint (vint 0) p; malloc_token Tsh (sizeof tnode) n;
         @data_at CompSpecs Tsh tnode (p, ld ++ repeat Vundef (Z.to_nat (8 - i))) n;
         fold_right sepcon emp (map (data_at Tsh tint (vint 0)) ld);
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) ld))).
  { Exists (@nil val); entailer!; auto. }
  - forward_malloc tint d.
    rewrite data_at__isptr; Intros.
    repeat forward.
    Exists (x ++ [d]); rewrite upd_init, <- app_assoc, !Zlength_app, !Zlength_cons, !Zlength_nil by (auto; tauto).
    rewrite !map_app, !sepcon_app; simpl fold_right; entailer!.
    { rewrite Forall_app; repeat constructor; auto. }
    auto.
  - Intros ld.
    (* Initializing the mutually recursive protocols is hard. The best way is probably to say that version_T
       doesn't need the snapshots if it's at version 0. *)
    apply ghost_alloc with (g := (Tsh, singleton 0 (repeat 0 (Z.to_nat size))));
      [apply master_init | Intros g].
    apply make_snap; Intros.
    assert (exists vs, Zlength vs = size /\ log_latest (singleton 0 (repeat 0 (Z.to_nat size))) 0 vs).
    { do 2 eexists; [|apply log_latest_singleton].
      rewrite Zlength_repeat, Z2Nat.id; auto; rewrite size_def; computable. }
    gather_SEP 3 0; eapply view_shift_trans;
      [|apply (@make_protocol _ _ Z.le _ _ (version_prot p ld g) p 0 0); auto|].
    { rewrite version_T_eq; apply derives_view_shift.
      Exists (singleton 0 (repeat 0 (Z.to_nat size))); simpl; entailer!.
      admit. }
    apply make_protocol_R; Intros.
    focus_SEP 1; apply protocol_R_forget with (s1 := -1); [omega|].
    rewrite app_nil_r; gather_SEP 6 0; apply list_duplicate.
    { apply protocol_R_duplicable. }
    Intros; apply view_shift_sepcon_list with (l2 := map (fun l =>
      protocol_W l (singleton 0 0) map_incl (data_T p ld g, data_T p ld g)) ld); rewrite ?Zlength_map; auto.
    { intros.
      erewrite Znth_map, Znth_map', Znth_map with (d' := Vundef) by (rewrite ?Zlength_map; auto).
      rewrite sepcon_comm; etransitivity; [|apply make_protocol with (v := 0); auto; apply data_prot].
      rewrite data_T_eq.
      apply derives_view_shift; Exists 0; entailer!.
      { apply log_latest_singleton. }
      simpl; apply protocol_delay. }
    gather_SEP 2 1; apply protocol_R_absorb; auto; Intros.
    forward.
    fold (ghost_var Tsh (singleton 0 (repeat 0 (Z.to_nat size))) g);
      erewrite <- ghost_var_share_join by eauto.
    unfold node_state.
    rewrite <- size_def in *.
    Exists n p ld g; unfold protocol_W, ghost_var, share; simpl; entailer!.
    setoid_rewrite (list_Znth_eq Vundef ld) at 3.
    rewrite map_map, <- ZtoNat_Zlength; replace (Zlength ld) with size.
    erewrite map_ext_in; eauto; intros; simpl.
    rewrite map_Znth_single, Znth_repeat; auto.
Admitted.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  name data _data.
  start_function.
  rewrite data_at__eq; unfold default_val; simpl.
  repeat forward.
  forward_for_simple_bound 3 (EX i : Z, EX L' : _,
    PROP (L' = map_upd_list L (map (fun i => (v + 2 * (i + 1), repeat (i + 1) 8)%Z) (upto (Z.to_nat i))))
    LOCAL (lvar _data (tarray tint 8) data; temp _n n)
    SEP (data_at Tsh (tarray tint 8) (repeat (vint i) 8) data; @data_at CompSpecs sh tnode (version, locs) n;
         node_state gsh2 L' (v + 2 * i) version locs g;
         invariant (EX L : Z -> option (list Z), ghost (gsh1, L) g))).
  { Exists L; entailer!; auto. }
  - Intros.
    match goal with |-semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
    forward_for_simple_bound 8 (EX j : Z, PROP () (LOCALx Q
      (SEPx (data_at Tsh (tarray tint 8) (repeat (vint (i + 1)) (Z.to_nat j) ++
             repeat (vint i) (Z.to_nat (8 - j))) data :: R)))) end.
    { entailer!. }
    + forward.
      { entailer!.
        rewrite app_Znth2; rewrite Zlength_repeat, Z2Nat.id; try omega.
        rewrite Zminus_diag, Znth_repeat' by (rewrite Z2Nat.id; omega); auto. }
      rewrite app_Znth2; rewrite Zlength_repeat, Z2Nat.id; try omega.
      rewrite Zminus_diag, Znth_repeat' by (rewrite Z2Nat.id; omega).
      forward.
      rewrite add_repr, upd_init_const by auto; entailer!.
    + 
    (* change_compspecs runs forever here *)
Ltac lookup_spec_and_change_compspecs CS id ::=
 tryif apply f_equal_Some
 then
   (match goal with |- ?A = ?B =>
      let x := fresh "x" in set (x := A);
      let y := fresh "y" in set (y := B);
      hnf in x; subst x; subst y
   end;
   match goal with
   | |- ?fs = _ => check_canonical_funspec (id,fs);
      first [reflexivity |
      match goal with
       | |- mk_funspec _ _ ?t1 _ _ = mk_funspec _ _ ?t2 _ _ =>
         first [unify t1 t2
           | elimtype False; elimtype (Witness_type_of_forward_call_does_not_match_witness_type_of_funspec
      t2 t1)]
      end]
   end)
 else elimtype  (Cannot_find_function_spec_in_Delta id).

      forward_call (n, data, sh, Tsh, version, locs, repeat (i + 1) 8, g, x, v + 2 * i, emp,
        fun (_ : Z -> option (list Z)) (_ : unit) => emp, fun _ : Z -> option (list Z) => emp,
        fun _ : Z => EX L : Z -> option (list Z), ghost (gsh1, L) g, [0]).
      { entailer!.
        { apply Forall_repeat.
          split; [pose proof Int.min_signed_neg; omega|].
          transitivity 3; [omega | computable]. }
        rewrite size_def, Zminus_diag, app_nil_r, map_repeat; simpl; cancel. }
      { split; [|split].
        * admit.
        * simpl.
          admit.
        * intros _ _; simpl; rewrite !sepcon_emp.
          apply derives_view_shift; eapply derives_trans, now_later.
          Exists (map_upd x (v + 2 * i + 2) (repeat (i + 1) 8)); cancel. }
      Exists (map_upd x (v + 2 * i + 2) (repeat (i + 1) 8)).
      rewrite Z2Nat.inj_add, upto_app, map_app, map_upd_list_app by omega.
      change (upto 1) with [0]; simpl map_upd_list.
      rewrite Z2Nat.id, Z.add_0_r, Z.mul_add_distr_l, Z.add_assoc by omega.
      rewrite <- size_def; entailer!.
  - Intros L'; forward.
    Exists data (map_upd_list L (map (fun i => (v + 2 * (i + 1), repeat (i + 1) 8)) (upto (Z.to_nat 3))));
      rewrite size_def; simpl; entailer!.
Admitted.

(*Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  name data _data.
  start_function.
  forward_call (n, data, sh, Tsh, version, locs, g, g', lg, lg', ghost_hist gsh ([] : hist) gh,
    fun (_ : Z * list Z) '(v, vs) => EX h' : _, !!(add_events [] [HRead v vs] h') &&
      ghost_hist gsh h' gh,
    fun s => ghost_hist gsh ([] : hist) gh * EX hr : _, !!(apply_hist (0, repeat 0 (Z.to_nat size)) hr = Some s) &&
      ghost_ref hr gh,
    fun p => if eq_dec p 0 then node_inv gh version locs g g' lg lg' else FF, [0]).
  { entailer!.
    rewrite size_def, eq_dec_refl; simpl; cancel. }
  { split; [|split].
    * apply ghost_timeless.
    * simpl.
      admit. (* laters are messy *)
    * intros (v0, vs0) (v1, vs1); simpl.
      unfold node_inv.
      view_shift_intro hr; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_hist _ _ _)).
      rewrite <- sepcon_assoc.
      rewrite <- sepcon_assoc, sepcon_assoc.
      etransitivity; [apply view_shift_sepcon1, hist_add' with (e := HRead v1 vs1); auto|].
      apply derives_view_shift; Exists [(length hr, HRead v1 vs1)]; simpl; entailer!.
      { apply add_events_1 with (h := []), hist_incl_lt; auto. }
      eapply derives_trans, now_later.
      Exists v1 vs1 (hr ++ [HRead v1 vs1]); entailer!.
      rewrite apply_hist_app; replace (apply_hist _ _) with (Some (v0, vs0)); auto.
      (* At this point, the proof fails: the state recorded in the invariant may not match the state we read
         from. *)
Abort.*)

(*Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  name data _data.
  start_atomic_function.
  destruct x as (((((((((n, sh), version), locs), g), g'), lg), lg'), gh), gsh); Intros.
  destruct H as (HP0 & HP & HQ).
  rewrite map_map in HP, HQ.
  forward_call (n, data, sh, Tsh, version, locs, g, g', lg, lg', P,
    fun (_ : Z * list Z) '(v1, vs1) => Q tt (v1, vs1),
    fun s => EX hr : _, !!(apply_hist (0, repeat 0 (Z.to_nat size)) hr = Some s) && ghost_ref hr gh, II, lI).
  { simpl; rewrite <- size_def; entailer!. }
  { split; [|split].
    * auto.
    * simpl.
      admit. (* laters are messy *)
    * intros (v0, vs0) (v1, vs1); simpl.
      rewrite map_map; etransitivity; [|apply HQ]; simpl.
      (* This also fails: the history in the invariant may not have caught up with the value we read. *)
Abort.*)

(*Lemma node_state_forget : forall L v version locs g lg g' L' v' (HL' : map_incl L' L) (Hv : v' <= v)
  (Hv' : exists vs, Zlength vs = size /\ log_latest L' v' vs) (Heven : Z.even v' = true),
  view_shift (node_state Share.bot L v version locs g lg g')
             (node_state Share.bot L' v' version locs g lg g').
Proof.
  intros.
  unfold node_state.
  apply view_shift_sepcon, ghost_snap_forget; try (intros; eapply map_join_incl_compat); eauto.
  apply view_shift_sepcon.
  - view_shift_intros.
    etransitivity; [apply protocol_R_forget with (s1 := v'); auto|].
    { simpl; intros; subst.
      do 2 eexists; eauto; apply Z.max_le_compat_r; auto. }
    apply derives_view_shift; entailer!.
  - apply view_shift_sepcon_list; rewrite !Zlength_map; auto.
    intros; erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    unfold node_entry.
    apply protocol_R_forget.
    { intros; eapply map_join_incl_compat; eauto. }
    { transitivity (map_Znth i L 0); [|destruct (Z.even v); auto; subst; reflexivity].
      apply map_incl_Znth; auto. }
Qed.*)

(* up *)
Lemma map_add_single : forall {A B} {A_eq : EqDec A} (m : A -> option B) k v,
  map_add (singleton k v) m = map_upd m k v.
Proof.
  intros; extensionality; unfold map_add, singleton, map_upd; if_tac; auto.
Qed.

Lemma node_state_upd : forall L v v' vs' version locs g (Hv' : v <= v') (Hvs' : Zlength vs' = size)
  (Hcompat : v' = v -> L v' = Some vs'),
  node_state Share.bot (singleton v' vs') v' version locs g *
  node_state Share.bot L v version locs g |--
  node_state Share.bot (map_upd L v' vs') v' version locs g.
Proof.
  intros; unfold node_state; Intros.
  rewrite <- !sepcon_assoc, (sepcon_comm _ (protocol_piece _ _ _ _ _)).
  rewrite <- !sepcon_assoc, 3sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl; apply protocol_R_join'|].
  Intros v''.
  simpl in *; subst.
  rewrite Z.max_r by auto.
  do 2 (rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost _ _))).
  rewrite <- !sepcon_assoc; setoid_rewrite ghost_snap_join'.
  Intros L'.
  match goal with H : join _ _ _ |- _ => rewrite map_join_spec in H; destruct H as [Hcompat']; subst end.
  rewrite map_add_single.
  rewrite sepcon_assoc, <- sepcon_map.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_list_derives]|].
  { rewrite 2Zlength_map; reflexivity. }
  { rewrite Zlength_map; intros.
    erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
    eapply derives_trans; [apply protocol_R_join'|].
    Intros log'.
    match goal with H : join _ _ _ |- _ => rewrite map_join_spec in H; destruct H; subst end.
    rewrite <- map_Znth_add, map_add_single; apply derives_refl. }
  unfold ghost_snap, protocol_R; entailer!.
  destruct (eq_dec v' v).
  - subst; rewrite map_upd_triv; auto.
  - match goal with H : exists vs, _ |- _ => destruct H as [? [? HL]] end.
    eapply log_latest_upd with (v1' := v') in HL; [|omega].
    destruct HL; eauto.
Qed.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  name data _data.
  start_function.
  assert_PROP (Z.even v = true /\ exists vs, Zlength vs = size /\ log_latest L v vs) as Hv.
  { unfold node_state; entailer!. }
  destruct Hv as [Heven [? [? [HL ?]]]].
  focus_SEP 2; apply node_state_snap.
  forward_call (n, data, sh, Tsh, version, locs, g, L, v, emp,
    fun (L' : Z -> option (list Z)) (_ : Z * list Z) => emp,
    fun _ : Z -> option (list Z) => emp,
    fun _ : Z => EX L : Z -> option (list Z), ghost (gsh1, L) g, [0]).
  { rewrite <- size_def; simpl; entailer!. }
  { split; [|split].
    * admit.
    * admit.
    * intros L' (v1, vs1); simpl.
      view_shift_intro v'.
      rewrite !sepcon_emp; apply derives_view_shift.
      eapply derives_trans, now_later; Exists L'; entailer!. }
  Intro X; destruct X as ((v', vs'), L'); simpl; Intros.
  forward.
  Exists data v' vs'; rewrite size_def; entailer!.
  apply node_state_upd; auto.
Admitted.
