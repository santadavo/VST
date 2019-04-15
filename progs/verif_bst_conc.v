Require Import VST.progs.conclib.
Require Import VST.progs.bst_conc.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.



Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.



Definition t_struct_tree := Tstruct _tree noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.

Section TREES.
Variable V : Type.
Variable default: V.

Definition key := Z.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> V -> tree -> tree.
 
Definition empty_tree : tree := E.
 
(*Inductive node_t : Type :=
 | En : node_t
 | NE : En -> key -> V -> En -> node_t.
 
Inductive general_node (X : Type) : Type :=
 | En : general_node X
 | N : X -> key -> V -> X -> general_node X.
 
Inductive tree_t: Type :=
  TR : general_node tree_t -> val -> tree_t.
  
Definition node : Type := general_node tree_t.

Definition empty_node : node := En tree_t.*)



Fixpoint lookup (x: key) (t : tree) : V :=
  match t with
  | E => default
  | T tl k v tr => if x <? k then lookup x tl
                         else if k <? x then lookup x tr
                         else v
  end.

(*Fixpoint insert (x: key) (v: V) (s: node) : node :=
 match s with
 | En => EX locka : val, EX lockb : val, 
          N tree_t (TR empty_node locka) x v (TR empty_node lockb) 
 | N (TR a la) y v' (TR b lb) => if  x <? y 
                        then N tree_t (TR (insert x v a) la) y v' (TR b lb)
                        else if y <? x
                        then N tree_t (TR a la) y v' (TR (insert x v b) lb)
                        else N tree_t (TR a la) x v (TR b lb)
 end.
*)

Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
 match s with
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
 end.



Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
 match bc with
 | E => a
 | T b y vy c => T (pushdown_left a b) y vy c
 end.

Fixpoint delete (x: key) (s: tree) : tree :=
 match s with
 | E => E
 | T a y v' b => if  x <? y then T (delete x a) y v' b
                        else if y <? x then T a y v' (delete x b)
                        else pushdown_left a b
 end.

End TREES.
Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments lookup {V} default x t.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.

Eval hnf in reptype (nested_field_type t_struct_tree_t [StructField _lock]).

(*Definition t_lock_pred' tl lsh p lock  := EX t : tree val, t_lock_pred tl lsh t p lock.

Definition t_lock_pred_uncurry (t: tree val) lsh (tl : (tree val -> (val * val) -> mpred)) := fun t '(p, lock) => 
  t_lock_pred tl t lsh p lock.

Definition t_lock_pred'' t lsh :=  HORec (t_lock_pred_uncurry t lsh).

Definition t_lock_pred''' t lsh p lock  := t_lock_pred'' t lsh (p,lock).


Definition ltree_final lsh p lock (t : tree val) :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at lsh t_struct_tree_t [StructField _lock] lock p *
   lock_inv lsh lock (t_lock_pred''' t lsh p lock)).
*)   

Fixpoint tree_rep (t: tree val) (p: val) : mpred := (*tree strored in p correctly, see struct tree, representation in memory*)
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    EX pa:val, EX pb:val,
    data_at Tsh t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) p *
    tree_rep a pa * tree_rep b pb
 end.


Definition ltree tl lsh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at lsh t_struct_tree_t [StructField _lock] lock p *
   lock_inv lsh lock (tl (p, lock))).


Fixpoint node_rep tl lsh (t: tree val) (tp: val) : mpred := (*tree strored in p correctly, see struct tree, representation in memory*)
 match t with
 | E => !!(tp=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) && EX pa:val, EX pb:val, EX locka : val, EX lockb : val,
    data_at Tsh t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) tp *
    ltree tl lsh pa locka * ltree tl lsh pb lockb
 end.
 
Definition t_lock_pred tl t lsh p lock :=
EX tp : val, (data_at Tsh (tptr t_struct_tree) tp p * node_rep tl lsh t tp *
  malloc_token Tsh (t_struct_tree_t) p *
 malloc_token Tsh (tlock) lock).


Definition t_lock_pred' tl lsh p lock  := 
      EX t : tree val, t_lock_pred tl t lsh p lock.

Definition t_lock_pred_uncurry lsh (tl : ((val * val) -> mpred)) := fun '(p, lock) => 
  t_lock_pred' tl lsh p lock.

Definition t_lock_pred'' lsh :=  HORec (t_lock_pred_uncurry lsh).

Definition t_lock_pred''' lsh p lock := t_lock_pred'' lsh (p,lock).


Definition ltree_final lsh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at lsh t_struct_tree_t [StructField _lock] lock p *
   lock_inv lsh lock (t_lock_pred''' lsh p lock)).



Theorem t_lock_pred_def : forall lsh p lock, 
  t_lock_pred''' lsh p lock = t_lock_pred' (t_lock_pred'' lsh) lsh p lock.
Proof.
Admitted.
   


Definition treebox_rep (t: tree val) (b: val) :=
 EX p: val, data_at Tsh (tptr t_struct_tree_t) p b.
 
 
Definition nodebox_rep (sh : share) (lock : val) (nb: val) :=
 EX np: val, data_at Tsh (tptr (t_struct_tree_t)) np nb * ltree_final sh np lock.
 



Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [ 1%positive OF tint]
     PROP (4 <= n <= Int.max_unsigned)
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP (malloc_compatible n v)
     LOCAL (temp ret_temp v)
     SEP (memory_block Tsh n v).

Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () LOCAL () SEP ().
    
    

Definition treebox_new_spec :=
 DECLARE _treebox_new
  WITH u : unit
  PRE  [  ]
       PROP() LOCAL() SEP ()
  POST [ tptr (tptr t_struct_tree) ]
    EX v:val,
    PROP()
    LOCAL(temp ret_temp v)
    SEP (data_at Tsh (tptr t_struct_tree) nullval v).

(*Definition insert_spec :=
 DECLARE _insert
  WITH b: val, x: Z, v: val, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint,
        _value OF (tptr Tvoid)   ]
    PROP( Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)); temp _value v)
    SEP (treebox_rep t b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (insert x v t) b).
*)  
    
(*maybe I should add the treebox_rep in the ltree definition *)
(*NEW*)
Definition insert_spec :=
  DECLARE _insert
  WITH sh : share, p : val, lock : val,
       b: val, x: Z, v: val, t: tree val
  PRE [  _t OF (tptr (tptr t_struct_tree_t)), _x OF tint,
        _value OF (tptr Tvoid)  ]
   PROP (readable_share sh; Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
   LOCAL (temp _t b; temp _x (Vint (Int.repr x)); temp _value v)
   SEP (nodebox_rep sh lock b)
  POST [ Tvoid ]
   PROP ()
   LOCAL ()
   SEP (nodebox_rep sh lock b).
(*Definition insert_spec prog := DECLARE (ext_link_prog prog "insert") insert_spec'.*)    

Definition lookup_spec :=
 DECLARE _lookup
  WITH b: val, x: Z, v: val, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint  ]
    PROP( Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (treebox_rep t b)
  POST [ tptr Tvoid ]
    PROP()
    LOCAL(temp ret_temp (lookup nullval x t))
    SEP (treebox_rep t b).

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH ta: tree val, x: Z, vx: val, tb: tree val, y: Z, vy: val, tc: tree val, b: val, l: val, pa: val, r: val
  PRE  [ __l OF (tptr (tptr (Tstruct _tree noattr))),
        _l OF (tptr (Tstruct _tree noattr)),
        _r OF (tptr (Tstruct _tree noattr))]
    PROP(Int.min_signed <= x <= Int.max_signed; is_pointer_or_null vx)
    LOCAL(temp __l b; temp _l l; temp _r r)
    SEP (data_at Tsh (tptr t_struct_tree) l b;
         data_at Tsh t_struct_tree (Vint (Int.repr x), (vx, (pa, r))) l;
         tree_rep ta pa;
         tree_rep (T tb y vy tc) r)
  POST [ Tvoid ] 
    EX pc: val,
    PROP(Int.min_signed <= y <= Int.max_signed; is_pointer_or_null vy)
    LOCAL()
    SEP (data_at Tsh (tptr t_struct_tree) r b;
         data_at Tsh t_struct_tree (Vint (Int.repr y), (vy, (l, pc))) r;
         tree_rep (T ta x vx tb) l;
         tree_rep tc pc).

Definition pushdown_left_spec :=
 DECLARE _pushdown_left
  WITH ta: tree val, x: Z, v: val, tb: tree val, b: val, p: val
  PRE  [ _t OF (tptr (tptr (Tstruct _tree noattr)))]
    PROP(Int.min_signed <= x <= Int.max_signed; tc_val (tptr Tvoid) v)
    LOCAL(temp _t b)
    SEP (data_at Tsh (tptr t_struct_tree) p b;
         field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr x)) p;
         field_at Tsh t_struct_tree [StructField _value] v p;
         treebox_rep ta (field_address t_struct_tree [StructField _left] p);
         treebox_rep tb (field_address t_struct_tree [StructField _right] p))
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (pushdown_left ta tb) b).

Definition delete_spec :=
 DECLARE _delete
  WITH b: val, x: Z, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP( Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (treebox_rep t b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (delete x t) b).

Definition tree_free_spec :=
 DECLARE _tree_free
  WITH t: tree val, p: val
  PRE  [ _p OF (tptr t_struct_tree) ]
       PROP() LOCAL(temp _p p) SEP (tree_rep t p)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (emp).

Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH t: tree val, b: val
  PRE  [ _b OF (tptr (tptr t_struct_tree)) ]
       PROP() LOCAL(temp _b b) SEP (treebox_rep t b)
  POST [ Tvoid ]
    PROP()
    LOCAL()
    SEP (emp).
    
    
Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.

(*no freelock_spec, spawn_spec, freelock2_spec, release2_spec*)
Definition Gprog : funspecs :=
    ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  (*
    acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;*)
    mallocN_spec; freeN_spec; treebox_new_spec;
    tree_free_spec; treebox_free_spec;
    insert_spec; lookup_spec;
    turn_left_spec; pushdown_left_spec; delete_spec
  ]).

Lemma tree_rep_saturate_local:
   forall tl lsh t p, node_rep tl lsh t p |-- !! is_pointer_or_null p.
Proof.
destruct t; simpl; intros.
entailer!.
Intros pa pb locka lockb. entailer!.
Qed.

Hint Resolve tree_rep_saturate_local: saturate_local.

Lemma tree_rep_valid_pointer:
  forall tl lsh t p, node_rep tl lsh t p |-- valid_pointer p.
Proof.
intros.
destruct t; simpl; normalize; auto with valid_pointer.
Qed.
Hint Resolve tree_rep_valid_pointer: valid_pointer.

(*Lemma treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree_t) [] b.
Proof.
intros.
unfold treebox_rep.
Intros p.
entailer!.
Qed.

Hint Resolve treebox_rep_saturate_local: saturate_local.

Definition insert_inv (b0: val) (t0: tree val) (x: Z) (v: val): environ -> mpred :=
  EX b: val, EX t: tree val,
  PROP()
  LOCAL(temp _t b; temp _x (Vint (Int.repr x));   temp _value v)
  SEP(treebox_rep t b;  (treebox_rep (insert x v t) b -* treebox_rep (insert x v t0) b0)). (* b0 which points to t0 which is the entire tree *)
*)
Definition insert_inv (b0: val) (t0: tree val) (x: Z) (v: val): environ -> mpred :=
  EX b: val, EX lock: val, EX lsh: share,
  PROP(readable_share lsh)
  LOCAL(temp _t b; temp _x (Vint (Int.repr x));   temp _value v)
  SEP(nodebox_rep lsh lock b).


Lemma ramify_PPQQ {A: Type} {NA: NatDed A} {SA: SepLog A} {CA: ClassicalSep A}: forall P Q,
  P |-- P * (Q -* Q).
Proof.
  intros. Check RAMIF_PLAIN.solve.
  apply RAMIF_PLAIN.solve with emp.
  + rewrite sepcon_emp. auto.
  + rewrite emp_sepcon. auto.
Qed.

Lemma tree_rep_nullval: forall tl t lsh,
  node_rep tl lsh t nullval |-- !! (t = E).
Proof.
  intros.
  destruct t; [entailer! |].
  simpl node_rep.
  Intros pa pb locka lockb. entailer!.
Qed.

Hint Resolve tree_rep_nullval: saturate_local.

(*Lemma treebox_rep_leaf: forall x p b (v: val),
  is_pointer_or_null v ->
  Int.min_signed <= x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr x), (v, (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- treebox_rep (T E x v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!.
Qed.

Lemma bst_left_entail: forall (t1 t1' t2: tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  node_rep t1 p1 * node_rep t2 p2
  |-- treebox_rep t1 (field_address t_struct_tree [StructField _left] p) *
       (treebox_rep t1'
         (field_address t_struct_tree [StructField _left] p) -*
        treebox_rep (T t1' k v t2) b).
        Print StructField.
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p). Check field_at_data_at.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.
  Check wand_sepcon_adjoint.
  rewrite <- wand_sepcon_adjoint.
  clear p1.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p1.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  cancel.
Qed.

Lemma bst_right_entail: forall (t1 t2 t2': tree val) k (v p1 p2 p b: val),
  Int.min_signed <= k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr k), (v, (p1, p2))) p *
  node_rep t1 p1 * node_rep t2 p2
  |-- treebox_rep t2 (field_address t_struct_tree [StructField _right] p) *
       (treebox_rep t2'
         (field_address t_struct_tree [StructField _right] p) -*
        treebox_rep (T t1 k v t2') b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  unfold treebox_rep at 1. Exists p2. cancel.

  rewrite <- wand_sepcon_adjoint.
  clear p2.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p2.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  cancel.
Qed.
*)
Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
  forall P Q R: A, P |-- Q -> P * (Q -* R) |-- R.
Proof.
  intros.
  eapply derives_trans; [| apply modus_ponens_wand].
  apply sepcon_derives; [| apply derives_refl].
  auto.
Qed.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply Z.ltb_lt; omega)
                          | rewrite if_falseb by (apply Z.ltb_ge; omega)].

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.  
  eapply semax_pre; [ 
    | apply (semax_loop _ (insert_inv b t x v) (insert_inv b t x v) )]. 
    (*P' = insert_inv b t x v *)
  * (* Precondition *)
    unfold insert_inv. 
    Exists b lock sh. entailer. 
  * (* Loop body *)
    unfold insert_inv.
    Intros b1 lock1 sh1.
    forward. (* Sskip *)
    unfold nodebox_rep at 1. Intros p1.
    forward. (* tgt=*t; *)
      unfold ltree_final. entailer!.
    unfold ltree_final. Intros.  
    (*assert_PROP
    (offset_val 4 p1 = field_address (tlock) [StructField _lock] p1).
      1: entailer!. rewrite field_address_offset.
         autorewrite with norm. unfold offset_val.*)
    forward. (* l=tgt->lock *)
      1: rewrite lock_inv_isptr. entailer!.
    forward_call(lock1, sh1, ltree_final sh1 p1 lock1). (* acquire(l) *)
      1: unfold ltree_final, data_at, field_at. lock_props. simpl. entailer!.
      rewrite lock_inv_isptr. entailer!. admit.
    2: unfold ltree_final. forward.
    forward_if.
    + (* then clause *)
      subst p1.
      Time forward_call (sizeof t_struct_tree).
        1: simpl. rep_omega.
      Intros p'. Check memory_block_data_at_.
      rewrite memory_block_data_at_ by auto.
      forward. (* p->key=x; *)
      simpl.
      forward. (* p->value=value; *)
      forward. (* p->left=NULL; *)
      forward. (* p->right=NULL; *)
      assert_PROP (t1= (@E _)).
        1: entailer!.
      subst t1. simpl tree_rep. Check prop_true_andp.
      rewrite prop_true_andp by auto.
      forward. (* *t = p; *)
      forward. (* return; *)
      Check modus_ponens_wand'.
      apply modus_ponens_wand'. 
      apply treebox_rep_leaf. auto. auto.
    + (* else clause *)
      destruct t1.
        { simpl tree_rep. normalize. (*???*)}
      simpl tree_rep.
      Intros pa pb. clear H1.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* t=&p->left *)
        unfold insert_inv.
        Exists (offset_val 8 p1) t1_1. (*why offset 8*)
        entailer!. simpl. Print simpl_compb.
        simpl_compb. 
        (* TODO: SIMPLY THIS LINE *)
        Print field_compatible. (*???*)
        replace (offset_val 8 p1)
          with (field_address t_struct_tree [StructField _left] p1)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        Check RAMIF_PLAIN.trans'.
        apply RAMIF_PLAIN.trans'.
        apply bst_left_entail. auto. auto.
      - (* Inner if, second branch:  k<x *)
        forward. (* t=&p->right *)
        unfold insert_inv.
        Exists (offset_val 12 p1) t1_2.
        entailer!. simpl.
        simpl_compb. simpl_compb. (*boolean comparison*)
        (* TODO: SIMPLY THIS LINE *)
        replace (offset_val 12 p1)
          with (field_address t_struct_tree [StructField _right] p1)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        apply RAMIF_PLAIN.trans'.
        apply bst_right_entail; auto.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x.  clear H H1 H3.
        forward. (* p->value=value *)
        forward. (* return *) simpl.
        (* TODO: SIMPLY THIS LINE *)
        simpl_compb.
        simpl_compb.
        apply modus_ponens_wand'.
        unfold treebox_rep. Exists p1.
        simpl tree_rep. Exists pa pb. entailer!.
  * (* After the loop *)
    forward.
    unfold loop2_ret_assert. apply andp_left2. normalize. 
Qed.





   
   