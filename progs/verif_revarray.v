Require Import VST.floyd.proofauto.
Require Import VST.progs.revarray.
Require Import VST.floyd.sublist.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition reverse_spec :=
 DECLARE _reverse
  WITH a0: val, sh : share, contents : list int, size: Z
  PRE [ _a OF (tptr tint), _n OF tint ]
          PROP (0 <= size <= Int.max_signed; writable_share sh)
          LOCAL (temp _a a0; temp _n (Vint (Int.repr size)))
          SEP (data_at sh (tarray tint size) (map Vint contents) a0)
  POST [ tvoid ]
     PROP() LOCAL()
     SEP(data_at sh (tarray tint size) (map Vint (rev contents)) a0).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [reverse_spec; main_spec]).

Definition flip_ends {A} lo hi (contents: list A) :=
  sublist 0 lo (rev contents)
  ++ sublist lo hi contents
  ++ sublist hi (Zlength contents) (rev contents).

Definition reverse_Inv a0 sh contents size :=
 (EX j:Z,
  (PROP  (0 <= j; j <= size-j)
   LOCAL  (temp _a a0; temp _lo (Vint (Int.repr j)); temp _hi (Vint (Int.repr (size-j))))
   SEP (data_at sh (tarray tint size) (flip_ends j (size-j) contents) a0)))%assert.


Lemma Zlength_flip_ends:
 forall A i j (al: list A),
 0 <= i  -> i<=j -> j <= Zlength al ->
 Zlength (flip_ends i j al) = Zlength al.
Proof.
intros.
unfold flip_ends.
autorewrite with sublist. omega.
Qed.
Hint Rewrite @Zlength_flip_ends using (autorewrite with sublist; omega) : sublist.

Lemma flip_fact_1: forall A size (contents: list A) j,
  Zlength contents = size ->
  0 <= j ->
  size - j - 1 <= j <= size - j ->
  flip_ends j (size - j) contents = rev contents.
Proof.
  intros.
  unfold flip_ends.
  rewrite <- (Zlen_le_1_rev (sublist j (size-j) contents))
      by (autorewrite with sublist; omega).
  rewrite !sublist_rev by (autorewrite with sublist; omega).
 rewrite <- !rev_app_distr, ?H.
 autorewrite with sublist; auto.
Qed.

Lemma flip_fact_3:
 forall A (al: list A) j size,
  size = Zlength al ->
  0 <= j < size - j - 1 ->
sublist 0 j (flip_ends j (size - j) al) ++
sublist (size - j - 1) (size - j) al ++
sublist (j + 1) size
  (sublist 0 (size - j - 1) (flip_ends j (size - j) al) ++
   sublist j (j + 1) (flip_ends j (size - j) al) ++
   sublist (size - j) size (flip_ends j (size - j) al)) =
flip_ends (j + 1) (size - (j + 1)) al.
Proof.
intros.
unfold flip_ends.
rewrite <- H.
autorewrite with sublist.
rewrite (sublist_split 0 j (j+1)) by (autorewrite with sublist; omega).
rewrite !app_ass.
f_equal. f_equal.
rewrite !sublist_rev, <- ?H by omega.
rewrite Zlen_le_1_rev by (autorewrite with sublist; omega).
f_equal; omega.
rewrite (sublist_app2 (size-j) size)
 by (autorewrite with sublist; omega).
autorewrite with sublist.
rewrite sublist_app'
 by (autorewrite with sublist; omega).
autorewrite with sublist.
f_equal.
f_equal; omega.
autorewrite with sublist.
  rewrite <- (Zlen_le_1_rev (sublist j (1+j) al))
      by (autorewrite with sublist; omega).
rewrite !sublist_rev, <- ?H by omega.
 rewrite <- !rev_app_distr, <- ?H.
 autorewrite with sublist.
 f_equal; f_equal; omega.
Qed.

Lemma flip_ends_map:
  forall A B (F: A -> B) lo hi (al: list A),
  flip_ends lo hi (map F al) = map F (flip_ends lo hi al).
Proof.
intros.
unfold flip_ends.
rewrite !map_app.
rewrite !map_sublist, !map_rev, Zlength_map.
auto.
Qed.

Lemma flip_fact_2:
  forall {A}{d: Inhabitant A} (al: list A) size j,
 Zlength al = size ->
  j < size - j - 1 ->
   0 <= j ->
  Znth (size - j - 1) al =
  Znth (size - j - 1) (flip_ends j (size - j) al).
Proof.
intros.
unfold flip_ends.
autorewrite with sublist. auto.
Qed.

Hint Rewrite @Znth_rev using Zlength_solve : Znth_solve.
Hint Rewrite Zlength_rev using Zlength_solve : Zlength.

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function.
repeat step.

assert_PROP (Zlength (map Vint contents) = size)
    as ZL by entailer!.
forward_while (reverse_Inv a0 sh (map Vint contents) size).
* (* Prove that current precondition implies loop invariant *)
repeat step.
apply data_at_data_at_cancel.
unfold flip_ends.
apply (Znth_eq_ext _ Inhabitant_val).
- Zlength_solve. (* why slow? *)
- autorewrite with Zlength. intros. Znth_solve.
  do 2 f_equal. omega.
* (* Prove that loop invariant implies typechecking condition *)
entailer!.
* (* Prove that loop body preserves invariant *)
(* unfold flip_ends. *) (* seems good to do this, but it makes step VERY slow *)
autorewrite with sublist in * |-.
forward.
progress_entailer.
autorewrite with sublist in * |-. { unfold flip_ends. Znth_solve. }
forward.
progress_entailer.
autorewrite with sublist in * |-. { unfold flip_ends. Znth_solve. }
forward.
forward.
forward.
autorewrite with norm.
forward.
autorewrite with norm.
Exists (j+1). (* put value here because entailer! did wrong unification *)
repeat info_step.
+ do 2 f_equal. omega.
+ apply data_at_data_at_cancel. unfold flip_ends.
  apply (Znth_eq_ext _ Inhabitant_val).
  Zlength_solve.
  autorewrite with Zlength.
  unfold upd_Znth. intros. list_form.
  Time Znth_solve. (* This takes quite a few minutes *)
  (* Finished transaction in 435.348 secs (433.171u,0.218s) (successful) *)
  - do 2 f_equal. omega.
  - do 2 f_equal. omega.
  - do 2 f_equal. omega.
  - do 2 f_equal. omega.
  - do 2 f_equal. omega.
* (* after the loop *)
forward. (* return; *)
apply data_at_data_at_cancel. unfold flip_ends.
autorewrite with Zlength in * |-.
apply (Znth_eq_ext _ Inhabitant_val).
Require Import Coq.Program.Tactics.
Ltac Zlength_solve ::= show_goal; autorewrite with Zlength; pose_Zlength_nonneg; omega.
Time Zlength_solve. (* example of slow rewrite *)
autorewrite with Zlength in *.
intros.
Znth_solve.
- do 2 f_equal. omega.
- do 2 f_equal. omega.
- do 2 f_equal. omega.
Time Qed.
(* Finished transaction in 53.902 secs (53.859u,0.s) (successful) *)

Definition four_contents := [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
name four _four.
start_function.

forward_call  (*  revarray(four,4); *)
  (gv _four, Ews, four_contents, 4).
   split; [computable | auto].
forward_call  (*  revarray(four,4); *)
    (gv _four,Ews, rev four_contents,4).
   split; [computable | auto].
rewrite rev_involutive.
forward. (* return s; *)
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_reverse.
semax_func_cons body_main.
Qed.
