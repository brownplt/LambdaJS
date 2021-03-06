(* 
 * Mechanized LambdaJS
 *
 * Authors: 
 *   Arjun Guha <arjun@cs.brown.edu>
 *   Benjamin Lerner <blerner@cs.brown.edu>
 *)
Require Import Coq.Arith.EqNat.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.
Require Import SfLib.
Require Import ListExt.
Require Import Datatypes.
Set Implicit Arguments.

Module Make (Import Atom : ATOM) (Import String : STRING).

Module AtomEnv := Coq.FSets.FMapList.Make (Atom.Ordered).

Definition atom := Atom.atom. (* free variables *)
Definition loc := Atom.atom.
Definition string := String.string.

Parameter __proto__ : string.

Unset Elimination Schemes.
Inductive exp : Set :=
  | exp_fvar  : atom -> exp
  | exp_bvar  : nat -> exp (* bound variables as de Brujin indices *)
  | exp_abs   : exp -> exp
  | exp_app   : exp -> exp -> exp
  | exp_nat   : nat -> exp
  | exp_succ  : exp -> exp
  | exp_bool  : bool -> exp
  | exp_string : string -> exp
  | exp_undef : exp
  | exp_null  : exp
  | exp_not   : exp -> exp
  | exp_if    : exp -> exp -> exp -> exp
  | exp_err   : exp
  | exp_label : atom -> exp -> exp
  | exp_break : atom -> exp -> exp
  | exp_loc   : loc -> exp
  | exp_deref : exp -> exp
  | exp_ref   : exp -> exp
  | exp_set   : exp -> exp -> exp
  | exp_catch : exp -> exp -> exp (* 2nd exp is a binder *)
  | exp_throw : exp -> exp
  | exp_seq   : exp -> exp -> exp
  | exp_finally : exp -> exp -> exp
  | exp_obj   : list (string * exp) -> exp
  | exp_getfield : exp -> exp -> exp
  | exp_setfield : exp -> exp -> exp -> exp
  | exp_delfield : exp -> exp -> exp.

Definition fieldnames l := map (@fst string exp) l.
Definition values l := map (@snd string exp) l.
Definition map_values A (f : exp -> A) l := 
  map (fun kv => ((@fst string exp) kv, f ((@snd string exp) kv))) l.

(* locally closed : all de Brujin indices are bound *)
Inductive lc' : nat -> exp -> Prop :=
  | lc_fvar : forall n a, lc' n (exp_fvar a)
  | lc_bvar : forall k n, k < n -> lc' n (exp_bvar k)
  | lc_abs  : forall n e,
      lc' (S n) e -> lc' n (exp_abs e)
  | lc_app  : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_app e1 e2)
  | lc_nat  : forall n x, lc' n (exp_nat x)
  | lc_succ : forall n e, lc' n e -> lc' n (exp_succ e)
  | lc_bool : forall n b, lc' n (exp_bool b)
  | lc_string : forall n s, lc' n (exp_string s)
  | lc_undef : forall n, lc' n exp_undef
  | lc_null : forall n, lc' n exp_null
  | lc_not  : forall n e, lc' n e -> lc' n (exp_not e)
  | lc_if   : forall n e e1 e2, 
      lc' n e -> lc' n e1 -> lc' n e2 -> lc' n (exp_if e e1 e2)
  | lc_err   : forall n, lc' n exp_err
  | lc_label : forall n x e, lc' n e -> lc' n (exp_label x e)
  | lc_break : forall n x e, lc' n e -> lc' n (exp_break x e)
  | lc_loc   : forall n x, lc' n (exp_loc x)
  | lc_ref   : forall n e, lc' n e -> lc' n (exp_ref e)
  | lc_deref : forall n e, lc' n e -> lc' n (exp_deref e)
  | lc_set   : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_set e1 e2)
  | lc_catch : forall n e1 e2, 
      lc' n e1 -> lc' (S n) e2 -> lc' n (exp_catch e1 e2)
  | lc_throw : forall n e, lc' n e -> lc' n (exp_throw e)
  | lc_seq   : forall n e1 e2, lc' n e1 -> lc' n e2 -> lc' n (exp_seq e1 e2)
  | lc_finally : forall n e1 e2, 
    lc' n e1 ->
    lc' n e2 ->
    lc' n (exp_finally e1 e2)
  | lc_obj   : forall n l, NoDup (fieldnames l) -> Forall (lc' n) (values l) -> lc' n (exp_obj l)
  | lc_getfield : forall n o f, lc' n o -> lc' n f -> lc' n (exp_getfield o f)
  | lc_setfield : forall n o f e, lc' n o -> lc' n f -> lc' n e -> lc' n (exp_setfield o f e)
  | lc_delfield : forall n o f, lc' n o -> lc' n f -> lc' n (exp_delfield o f)
.

Definition lc := lc' 0.

Inductive val : exp -> Prop :=
  | val_abs  : forall e, lc (exp_abs e) -> val (exp_abs e)
  | val_nat  : forall n, val (exp_nat n)
  | val_fvar : forall a, val (exp_fvar a)
  | val_bool : forall b, val (exp_bool b)
  | val_string : forall s, val (exp_string s)
  | val_undef : val (exp_undef)
  | val_null : val (exp_null)
  | val_loc  : forall l, val (exp_loc l)
  | val_obj  : forall l, Forall val (values l)
                     -> NoDup (fieldnames l)
                     -> val (exp_obj l).

Set Elimination Schemes.

(* open_rec is the analogue of substitution for de Brujin indices.
  open_rec k u e replaces index k with u in e. *)
Fixpoint open_rec (k : nat) (u : exp) (e : exp) { struct e } := match e with
  | exp_fvar a    => e
  | exp_bvar n    => if beq_nat k n then u else e
  | exp_abs  e    => exp_abs (open_rec (S k) u e)
  | exp_app e1 e2 => exp_app (open_rec k u e1) (open_rec k u e2)
  | exp_nat n     => e
  | exp_succ e    => exp_succ (open_rec k u e)
  | exp_bool b     => e
  | exp_string s   => e
  | exp_undef      => e
  | exp_null       => e
  | exp_not e      => exp_not (open_rec k u e)
  | exp_if e e1 e2 => exp_if (open_rec k u e) (open_rec k u e1) (open_rec k u e2)
  | exp_err       => e
  | exp_label x e => exp_label x (open_rec k u e)
  | exp_break x e => exp_break x (open_rec k u e)
  | exp_loc _     => e
  | exp_deref e   => exp_deref (open_rec k u e)
  | exp_ref e     => exp_ref (open_rec k u e)
  | exp_set e1 e2 => exp_set (open_rec k u e1) (open_rec k u e2)
  | exp_catch e1 e2 => exp_catch (open_rec k u e1) (open_rec (S k) u e2)
  | exp_throw e     => exp_throw (open_rec k u e)
  | exp_seq e1 e2   => exp_seq (open_rec k u e1) (open_rec k u e2)
  | exp_finally e1 e2 => exp_finally (open_rec k u e1) (open_rec k u e2)
  | exp_obj l     => exp_obj (map_values (open_rec k u) l)
  | exp_getfield o f => exp_getfield (open_rec k u o) (open_rec k u f)
  | exp_setfield o f e => exp_setfield (open_rec k u o) (open_rec k u f) (open_rec k u e)
  | exp_delfield o f => exp_delfield (open_rec k u o) (open_rec k u f)
end.

Definition open e u := open_rec 0 u e.

Inductive stored_val : Set :=
  | val_with_proof : forall (v : exp), val v -> stored_val.

Definition sto := AtomEnv.t stored_val.

Inductive tag : Set :=
  | TagAbs  : tag
  | TagNat  : tag
  | TagVar  : tag
  | TagBool : tag
  | TagString : tag
  | TagUndef : tag
  | TagNull : tag
  | TagLoc  : tag
  | TagObj  : tag.

Inductive tagof : exp -> tag -> Prop :=
  | tag_abs  : forall e, tagof (exp_abs e) TagAbs
  | tag_nat  : forall n, tagof (exp_nat n) TagNat
  | tag_var  : forall x, tagof (exp_fvar x) TagVar
  | tag_bool : forall b, tagof (exp_bool b) TagBool
  | tag_string : forall s, tagof (exp_string s) TagString
  | tag_undef : tagof (exp_undef) TagUndef
  | tag_null : tagof (exp_null) TagNull
  | tag_loc  : forall l, tagof (exp_loc l) TagLoc
  | tag_obj  : forall l, tagof (exp_obj l) TagObj.


Inductive C : Set :=
  | C_hole    : C
  | C_app_1   : C -> exp -> C
  | C_app_2   : exp -> C -> C
  | C_succ    : C -> C
  | C_not     : C -> C
  | C_if      : C -> exp -> exp -> C
  | C_label   : atom -> C -> C
  | C_break   : atom -> C -> C
  | C_ref     : C -> C
  | C_deref   : C -> C
  | C_setref1 : C -> exp -> C
  | C_setref2 : exp -> C -> C
  | C_catch   : C -> exp -> C
  | C_throw   : C -> C
  | C_seq   : C -> exp -> C
  | C_finally  : C -> exp -> C
  | C_obj     : list (string * exp) -> string -> C -> list (string * exp) -> C
  | C_getfield1 : C -> exp -> C
  | C_getfield2 : exp -> C -> C
  | C_setfield1 : C -> exp -> exp -> C
  | C_setfield2 : exp -> C -> exp -> C
  | C_setfield3 : exp -> exp -> C -> C
  | C_delfield1 : C -> exp -> C
  | C_delfield2 : exp -> C -> C
.

Inductive E' : exp -> exp -> Prop :=
  | E'_app_1 : forall e1 e2,
      lc e1 ->
      lc e2 ->
      E' (exp_app e1 e2) e1
  | E'_app_2 : forall v1 e2,
      val v1 ->
      lc e2 ->
      E' (exp_app v1 e2) e2
  | E'_succ : forall e,
      lc e ->
      E' (exp_succ e) e
  | E'_not : forall e,
      lc e ->
      E' (exp_not e) e
  | E'_if : forall e1 e2 e3,
      lc e1 ->
      lc e2 ->
      lc e3 ->
      E' (exp_if e1 e2 e3) e1
  | E'_break : forall x e,
      lc e ->
      E' (exp_break x e) e
  | E'_ref : forall e,
      lc e ->
      E' (exp_ref e) e
  | E'_deref : forall e,
      lc e ->
      E' (exp_deref e) e
  | E'_setref_1 : forall e1 e2,
      lc e1 ->
      lc e2 ->
      E' (exp_set e1 e2) e1
  | E'_setref_2 : forall v1 e2,
      val v1 ->
      lc e2 ->
      E' (exp_set v1 e2) e2
  | E'_throw : forall e,
      lc e ->
      E' (exp_throw e) e
  | E'_seq_1 : forall e1 e2,
      lc e1 ->
      lc e2 ->
      E' (exp_seq e1 e2) e1
  | E'_seq_2 : forall v1 e2,
      val v1 ->
      lc e2 ->
      E' (exp_seq v1 e2) e2
  | E'_object : forall vs es k e,
       Forall val (values vs) ->
       lc (exp_obj (vs ++ (k, e) :: es)) ->
       E' (exp_obj (vs ++ (k, e) :: es)) e
  | E'_getfield_1 : forall e1 e2,
      lc e1 ->
      lc e2 ->
      E' (exp_getfield e1 e2) e1
  | C_getfield_2 : forall v1 e2,
      val v1 ->
      lc e2 ->
      E' (exp_getfield v1 e2) e2
  | E'_delfield_1 : forall e1 e2,
      lc e1 ->
      lc e2 ->
      E' (exp_delfield e1 e2) e1
  | C_delfield_2 : forall v1 e2,
      val v1 ->
      lc e2 ->
      E' (exp_delfield v1 e2) e2
  | E'_setfield_1 : forall e1 e2 e3,
      lc e1 ->
      lc e2 ->
      lc e3 ->
      E' (exp_setfield e1 e2 e3) e1
  | E'_setfield_2 : forall v1 e2 e3,
      val v1 ->
      lc e2 ->
      lc e3 ->
      E' (exp_setfield v1 e2 e3) e2
  | E'_setfield_3 : forall v1 v2 e3,
      val v1 ->
      val v2 ->
      lc e3 ->
      E' (exp_setfield v1 v2 e3) e3.

Inductive F : exp -> exp -> Prop :=
  | F_E' : forall e1 e2,
      E' e1 e2 ->
      F e1 e2
  | F_label : forall x e,
      lc e ->
      F (exp_label x e) e.

Inductive G : exp -> exp -> Prop :=
   | G_E' : forall e1 e2,
       E' e1 e2 ->
       G e1 e2
   | G_catch : forall e1 e2,
       lc e1 ->
       lc' 1 e2 ->
       G (exp_catch e1 e2) e1.

Inductive E : exp -> C -> exp -> Prop :=
  | E_hole : forall e,
      E e C_hole e
  | E_app_1 : forall C e1 e2 e',
      E e1 C e' ->
      E (exp_app e1 e2) (C_app_1 C e2) e'
  | E_app_2 : forall C v e e',
      val v ->
      E e C e' ->
      E (exp_app v e) (C_app_2 v C) e'
  | E_succ : forall C e e',
      E e C e' ->
      E (exp_succ e) (C_succ C) e'
  | E_not : forall C e e',
      E e C e' ->
      E (exp_not e) (C_not C) e'
  | E_if : forall C e e1 e2 e',
      E e C e' ->
      E (exp_if e e1 e2) (C_if C e1 e2) e'
  | E_break : forall x e C ae,
      E e C ae ->
      E (exp_break x e) (C_break x C) ae
  | E_label : forall x e C ae,
      E e C ae ->
      E (exp_label x e) (C_label x C) ae
  | E_ref : forall e C ae,
     E e C ae ->
     E (exp_ref e) (C_ref C) ae
  | E_deref : forall e C ae,
     E e C ae ->
     E (exp_deref e) (C_deref C) ae
  | E_set1 : forall e1 e2 C ae,
      E e1 C ae ->
      E (exp_set e1 e2) (C_setref1 C e2) ae
  | E_set2 : forall e1 e2 C ae,
      val e1 ->
      E e2 C ae ->
      E (exp_set e1 e2) (C_setref2 e1 C) ae
  | E_throw : forall e C ae,
      E e C ae ->
      E (exp_throw e) (C_throw C) ae
  | E_catch : forall e1 e2 C ae,
      E e1 C ae ->
      E (exp_catch e1 e2) (C_catch C e2) ae
  | E_seq : forall C e1 e2 ae,
      E e1 C ae ->
      E (exp_seq e1 e2) (C_seq C e2) ae
  | E_finally : forall C e1 e2 ae,
      E e1 C ae ->
      E (exp_finally e1 e2) (C_finally C e2) ae
  | E_obj  : forall vs es k e C e' (are_vals : Forall val (values vs)),
      E e C e' ->
      E (exp_obj (vs++(k,e)::es)) (C_obj vs k C es) e'
  | E_getfield1 : forall o f C ae,
      E o C ae ->
      E (exp_getfield o f) (C_getfield1 C f) ae
  | E_getfield2 : forall o f C ae,
      val o ->
      E f C ae ->
      E (exp_getfield o f) (C_getfield2 o C) ae
  | E_setfield1 : forall o f e C ae,
      E o C ae ->
      E (exp_setfield o f e) (C_setfield1 C f e) ae
  | E_setfield2 : forall o f e C ae,
      val o ->
      E f C ae ->
      E (exp_setfield o f e) (C_setfield2 o C e) ae
  | E_setfield3 : forall o f e C ae,
      val o -> val f ->
      E e C ae ->
      E (exp_setfield o f e) (C_setfield3 o f C) ae
  | E_delfield1 : forall o f C ae,
      E o C ae ->
      E (exp_delfield o f) (C_delfield1 C f) ae
  | E_delfield2 : forall o f C ae,
      val o ->
      E f C ae ->
      E (exp_delfield o f) (C_delfield2 o C) ae
.

Fixpoint plug (e : exp) (cxt : C) := match cxt with
  | C_hole => e
  | C_app_1 cxt e2 => exp_app (plug e cxt) e2
  | C_app_2 v cxt => exp_app v (plug e cxt)
  | C_succ cxt => exp_succ (plug e cxt)
  | C_not cxt => exp_not (plug e cxt)
  | C_if cxt e1 e2 => exp_if (plug e cxt) e1 e2
  | C_label x cxt => exp_label x (plug e cxt)
  | C_break x cxt => exp_break x (plug e cxt)
  | C_ref cxt => exp_ref (plug e cxt)
  | C_deref cxt => exp_deref (plug e cxt)
  | C_setref1 cxt e2 => exp_set (plug e cxt) e2
  | C_setref2 v1 cxt => exp_set v1 (plug e cxt)
  | C_catch cxt e2 => exp_catch (plug e cxt) e2
  | C_throw cxt    => exp_throw (plug e cxt)
  | C_seq cxt e2   => exp_seq (plug e cxt) e2
  | C_finally cxt e2 => exp_finally (plug e cxt) e2
  | C_obj vs k cxt es  => exp_obj (vs++(k,plug e cxt)::es)
  | C_getfield1 cxt f => exp_getfield (plug e cxt) f
  | C_getfield2 v cxt => exp_getfield v (plug e cxt)
  | C_setfield1 cxt f e' => exp_setfield (plug e cxt) f e'
  | C_setfield2 v cxt e' => exp_setfield v (plug e cxt) e'
  | C_setfield3 v f cxt => exp_setfield v f (plug e cxt)
  | C_delfield1 cxt f => exp_delfield (plug e cxt) f
  | C_delfield2 v cxt => exp_delfield v (plug e cxt)
end.

Fixpoint delta exp := match exp with
  | exp_succ (exp_nat n) => exp_nat (S n)
  | exp_not (exp_bool b) => exp_bool (negb b)
  | _                    => exp_err
end.

Inductive red :  exp -> exp -> Prop := 
  | red_succ : forall e, red (exp_succ e) (delta (exp_succ e))
  | red_not  : forall e, red (exp_not e) (delta (exp_not e))
  | red_if1  : forall e1 e2, red (exp_if (exp_bool true) e1 e2) e1
  | red_if2  : forall e1 e2, red (exp_if (exp_bool false) e1 e2) e2
  | red_app  : forall e v, 
      val v -> red (exp_app (exp_abs e) v) (open e v)
  | red_app_err : forall v1 v2,
      val v1 ->
      val v2 ->
      ~ tagof v1 TagAbs ->
      red (exp_app v1 v2) exp_err
  | red_if_err : forall v1 e2 e3,
      val v1 ->
      ~ tagof v1 TagBool ->
      red (exp_if v1 e2 e3) exp_err
  | red_label : forall x v,
      val v -> red (exp_label x v) v
  | red_break_bubble : forall x v e,
    G e (exp_break x v) ->
    red e (exp_break x v)
  | red_break_match : forall x v,
    red (exp_label x (exp_break x v)) v
  | red_break_mismatch : forall x y v,
    x <> y ->
    red (exp_label x (exp_break y v)) (exp_break y v)
  | red_set_err : forall v1 v2,
      val v1 ->
      val v2 ->
      ~ tagof v1 TagLoc ->
      red (exp_set v1 v2) exp_err
  | red_deref_err : forall v,
      val v ->
      ~ tagof v TagLoc ->
      red (exp_deref v) exp_err
  | red_err_bubble : forall e,
      F e exp_err ->
      red e exp_err
  | red_throw : forall v,
      val v ->
      red (exp_throw v) exp_err (* TODO: errors need carry values *)
  | red_catch_normal : forall v e,
      val v ->
      red (exp_catch v e) v
  | red_catch_catch : forall e,
      red (exp_catch exp_err e) (open e (exp_nat 0)) (* TODO: err vals *)
  | red_seq : forall e v,
      val v ->
      red (exp_seq v e) e
  | red_finally_normal : forall v e,
      val v ->
      red (exp_finally v e) (exp_seq e v)
  | red_finally_propagate_err : forall e ,
      red (exp_finally exp_err e) (exp_seq e exp_err)
  | red_finally_propagate_break : forall x v e,
      val v ->
      red (exp_finally (exp_break x v) e) (exp_seq e (exp_break x v))
  | red_getfield : forall l f,
      val (exp_obj l) ->
      In f (fieldnames l) ->
      red (exp_getfield (exp_obj l) (exp_string f)) (lookup_assoc l f exp_err string_eq_dec)
  | red_getfield_notfound : forall l f,
      val (exp_obj l) ->
      ~ In f (fieldnames l) -> ~ In __proto__ (fieldnames l) ->
      red (exp_getfield (exp_obj l) (exp_string f)) exp_undef
  | red_getfield_proto : forall l f,
      val (exp_obj l) ->
      ~ In f (fieldnames l) ->
      In __proto__ (fieldnames l) ->
      red (exp_getfield (exp_obj l) (exp_string f)) 
        (exp_getfield (exp_deref (exp_getfield (exp_obj l) (exp_string __proto__))) (exp_string f))
  | red_getfield_err_notobj : forall v f,
      val v -> ~ tagof v TagObj -> red (exp_getfield v f) exp_err
  | red_getfield_err_notstr : forall v f,
      val v -> val f -> ~ tagof f TagString -> red (exp_getfield v f) exp_err
  | red_setfield_update : forall l f v,
      val (exp_obj l) ->
      val v ->
      In f (fieldnames l) ->
      red (exp_setfield (exp_obj l) (exp_string f) v) (exp_obj (update_assoc l f v string_eq_dec))
  | red_setfield_add : forall l f v,
      val (exp_obj l) ->
      val v ->
      ~ In f (fieldnames l) ->
      red (exp_setfield (exp_obj l) (exp_string f) v) (exp_obj ((f,v)::l))
  | red_setfield_err_notobj : forall v f e,
      val v -> ~ tagof v TagObj -> red (exp_setfield v f e) exp_err
  | red_setfield_err_notstr : forall v f e,
      val v -> val f -> ~ tagof f TagString -> red (exp_setfield v f e) exp_err
  | red_delfield : forall l f,
      val (exp_obj l) ->
      In f (fieldnames l) ->
      red (exp_delfield (exp_obj l) (exp_string f)) 
        (exp_obj (remove_fst f l string_eq_dec))
  | red_delfield_notfound : forall l f,
      val (exp_obj l) ->
      ~ In f (fieldnames l) ->
      red (exp_delfield (exp_obj l) (exp_string f)) (exp_obj l)
  | red_delfield_err_notobj : forall v f,
      val v -> ~ tagof v TagObj -> red (exp_delfield v f) exp_err
  | red_delfield_err_notstr : forall v f,
      val v -> val f -> ~ tagof f TagString -> red (exp_delfield v f) exp_err
.

Inductive step : sto -> exp -> sto -> exp -> Prop :=
  | step_red : forall s e C ae e',
    lc e ->
    E e C ae ->
    red ae e' ->
    step s e s (plug e' C)
  | step_ref : forall C e v l s (pf : val v),
    lc e ->
    E e C (exp_ref v) ->
    ~ In l (map (@fst AtomEnv.key stored_val) (AtomEnv.elements s)) ->
    step s e (AtomEnv.add l (val_with_proof pf) s) (plug (exp_loc l) C)
  | step_deref : forall e s C l v (pf : val v),
    lc e ->
    E e C (exp_deref (exp_loc l)) ->
    AtomEnv.find l s = Some (val_with_proof pf) ->
    step s e s (plug v C)
  | step_deref_err : forall e s C l,
    lc e ->
    E e C (exp_deref (exp_loc l)) ->
    AtomEnv.find l s = None ->
    step s e s (plug exp_err C)
  | step_setref : forall s e C l v v_old (pf_v : val v) (pf_v_old : val v_old),
    lc e ->
    E e C (exp_set (exp_loc l) v) ->
    AtomEnv.find l s = Some (val_with_proof pf_v_old) ->
    step s e (AtomEnv.add l (val_with_proof pf_v) s) (plug (exp_loc l) C)
  | step_setref_err : forall s e C l v,
    lc e ->
    E e C (exp_set (exp_loc l) v) ->
    AtomEnv.find l s = None ->
    step s e s (plug exp_err C)
  | step_err : forall x v s,
      val v ->
      step s (exp_break x v) s exp_err
.

Definition progress := forall sto e, 
  lc e -> 
  val e \/ e = exp_err \/ (exists e', exists sto', step sto e sto' e').

Definition preservation := forall sto1 e1 sto2 e2, 
  lc e1 -> 
  step sto1 e1 sto2 e2 -> 
  lc e2.

Hint Constructors exp lc' val tagof tag stored_val C E' F G E red step.
Hint Unfold values fieldnames map_values open lc.

End Make.
