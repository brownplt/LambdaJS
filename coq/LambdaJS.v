(* 
 * An encoding of the untyped lambda calculus with numbers.
 *
 * Authors: 
 *   Arjun Guha <arjun@cs.brown.edu>
 *   Benjamin Lerner <blerner@cs.brown.edu>
 *)
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrderedType.
Require Import Coq.MSets.MSetList.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.
Require Import Omega.
Require Import SfLib.
Set Implicit Arguments.
Require Import ListExt.

Module Type ATOM.

  Parameter atom : Set.
  Declare Module Atom_as_OT : UsualOrderedType with Definition t := atom.
  Declare Module Ordered : Coq.Structures.OrderedType.OrderedType 
    with Definition t := atom.
  Module OrderedTypeFacts := Coq.Structures.OrderedType.OrderedTypeFacts (Ordered).
  Parameter atom_fresh_for_list : forall (xs : list atom), 
    exists x : atom, ~ List.In x xs.
  Parameter atom_eq_dec : forall a1 a2 : atom, {a1 = a2} + {~ a1 = a2}.
  Parameter atom_dec_eq : forall a1 a2 : atom, a1 = a2 \/ ~ a1 = a2.

End ATOM.

Module Type STRING.

 Parameter string : Set.
 Declare Module String_as_OT : UsualOrderedType with Definition t := string.
 Declare Module Ordered : Coq.Structures.OrderedType.OrderedType
   with Definition t := string.
 Module OrderedTypeFacts := Coq.Structures.OrderedType.OrderedTypeFacts (Ordered).
 Parameter string_eq_dec : forall s1 s2 : string, {s1 = s2} + {~ s1 = s2}.
 Parameter string_dec_eq : forall s1 s2 : string, s1 = s2 \/ ~ s1 = s2.

End STRING.

Module LC (Import Atom : ATOM) (Import String : STRING).

Module Atoms := Coq.MSets.MSetList.Make (Atom.Atom_as_OT).
Module AtomEnv := Coq.FSets.FMapList.Make (Atom.Ordered).

Definition atom := Atom.atom. (* free variables *)
Definition loc := Atom.atom.
Definition string := String.string.

Parameter __proto__ : string.


Section Definitions.
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
Set Elimination Schemes.

Definition exp_ind := fun (P : exp -> Prop)
  (rec_exp_fvar : forall a : atom, P (exp_fvar a))
  (rec_exp_bvar : forall n : nat, P (exp_bvar n))
  (rec_exp_abs : forall e : exp, P e -> P (exp_abs e))
  (rec_exp_app : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_app e e0))
  (rec_exp_nat : forall n : nat, P (exp_nat n))
  (rec_exp_succ : forall e : exp, P e -> P (exp_succ e))
  (rec_exp_bool : forall b : bool, P (exp_bool b))
  (rec_exp_string : forall s : string, P (exp_string s))
  (rec_exp_undef : P exp_undef)
  (rec_exp_null : P exp_null)
  (rec_exp_not : forall e : exp, P e -> P (exp_not e))
  (rec_exp_if : forall e : exp, P e -> forall e0 : exp, P e0 -> forall e1 : exp, P e1 -> P (exp_if e e0 e1))
  (rec_exp_err : P exp_err)
  (rec_exp_label : forall (a : atom) (e : exp), P e -> P (exp_label a e))
  (rec_exp_break : forall (a : atom) (e : exp), P e -> P (exp_break a e))
  (rec_exp_loc : forall l : loc, P (exp_loc l))
  (rec_exp_deref : forall e : exp, P e -> P (exp_deref e))
  (rec_exp_ref : forall e : exp, P e -> P (exp_ref e))
  (rec_exp_set : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_set e e0))
  (rec_exp_catch : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_catch e e0))
  (rec_exp_throw : forall e : exp, P e -> P (exp_throw e))
  (rec_exp_seq : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_seq e e0))
  (rec_exp_finally : forall e : exp, P e -> forall e0 : exp, P e0 -> P (exp_finally e e0))
  (rec_exp_obj : forall l : list (string * exp), Forall P (map (@snd string exp) l) -> P (exp_obj l))
  (rec_exp_getfield : forall o : exp, P o -> forall f : exp, P f -> P (exp_getfield o f))
  (rec_exp_setfield : forall o : exp, P o -> forall f, P f -> forall e, P e -> P (exp_setfield o f e))
  (rec_exp_delfield : forall o : exp, P o -> forall f : exp, P f -> P (exp_delfield o f))
  =>
fix exp_rec' (e : exp) {struct e} : P e :=
  match e as e0 return (P e0) with
  | exp_fvar a => rec_exp_fvar a
  | exp_bvar n => rec_exp_bvar n
  | exp_abs e0 => rec_exp_abs e0 (exp_rec' e0)
  | exp_app e0 e1 => rec_exp_app e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_nat n => rec_exp_nat n
  | exp_succ e0 => rec_exp_succ e0 (exp_rec' e0)
  | exp_bool b => rec_exp_bool b
  | exp_string s => rec_exp_string s
  | exp_undef => rec_exp_undef
  | exp_null => rec_exp_null
  | exp_not e0 => rec_exp_not e0 (exp_rec' e0)
  | exp_if e0 e1 e2 => rec_exp_if e0 (exp_rec' e0) e1 (exp_rec' e1) e2 (exp_rec' e2)
  | exp_err => rec_exp_err
  | exp_label a e0 => rec_exp_label a e0 (exp_rec' e0)
  | exp_break a e0 => rec_exp_break a e0 (exp_rec' e0)
  | exp_loc l => rec_exp_loc l
  | exp_deref e0 => rec_exp_deref e0 (exp_rec' e0)
  | exp_ref e0 => rec_exp_ref e0 (exp_rec' e0)
  | exp_set e0 e1 => rec_exp_set e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_catch e0 e1 => rec_exp_catch e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_throw e0 => rec_exp_throw e0 (exp_rec' e0)
  | exp_seq e0 e1 => rec_exp_seq e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_finally e0 e1 => rec_exp_finally e0 (exp_rec' e0) e1 (exp_rec' e1)
  | exp_obj l =>
    rec_exp_obj l ((fix forall_rec (ls : list (string * exp)) : Forall P (map (@snd string exp) ls) :=
      match ls with
        | nil => Forall_nil P
        | (_,tr)::rest => Forall_cons tr (exp_rec' tr) (forall_rec rest)
      end) l)
  | exp_getfield o f => rec_exp_getfield o (exp_rec' o) f (exp_rec' f)
  | exp_setfield o f e => rec_exp_setfield o (exp_rec' o) f (exp_rec' f) e (exp_rec' e)
  | exp_delfield o f => rec_exp_delfield o (exp_rec' o) f (exp_rec' f)
  end.
(* Definition exp_rec := fun (P : exp -> Set) => exp_rect (P := P). *)
(* Definition exp_ind := fun (P : exp -> Prop) => exp_rect (P := P). *)


Ltac destruct_and_solve' e := destruct e; [idtac | right; intro Neq; inversion Neq; contradiction].
Tactic Notation "solve" "by" "destruction" "1" tactic(t) constr(e) := destruct_and_solve' e; left; t; auto.
Tactic Notation "solve" "by" "destruction" "2" tactic(t) constr(e1) constr(e2) := 
  destruct_and_solve' e1; solve by destruction 1 (t) e2.
Tactic Notation "solve" "by" "destruction" "3" tactic(t) constr(e1) constr(e2) constr (e3) := 
  destruct_and_solve' e1; solve by destruction 2 (t) e2 e3.

Lemma exp_eq_dec : forall e1 e2 : exp, e1 = e2 \/ ~ e1 = e2.
Proof with eauto.
induction e1; induction e2; try solve [
  left; reflexivity | right; congruence
  | solve by destruction 1 subst (string_dec_eq s s0)
  | solve by destruction 1 subst (IHe1 e2)
  | solve by destruction 2 subst (IHe1_1 e2_1) (IHe1_2 e2_2)
  | solve by destruction 3 subst (IHe1_1 e2_1) (IHe1_2 e2_2) (IHe1_3 e2_3)
  | solve by destruction 1 subst (Atom.atom_dec_eq a a0)
  | solve by destruction 1 subst (Atom.atom_dec_eq l l0)
  | solve by destruction 2 subst (Atom.atom_dec_eq a a0) (IHe1 e2)  
  | solve by destruction 1 subst (eq_nat_dec n n0) 
  | solve by destruction 2 subst (IHe1 e2) (string_dec_eq f f0)
  | solve by destruction 3 subst (IHe1_1 e2_1) (IHe1_2 e2_2) (string_dec_eq f f0) ].
Case "exp_bool".
destruct b; destruct b0; try solve [left; reflexivity | right; congruence].
Case "exp_obj".
assert (l = l0 \/ l <> l0). 
  SCase "list proof".
  apply in_dec_dec_list. intros. rewrite Forall_forall in H. 
  remember a1 as a1'; destruct a1'. remember a2 as a2'; destruct a2'.
  assert (EqS := string_dec_eq s s0). inversion EqS; [auto | right; congruence].
  assert (e = e0 \/ e <> e0). apply H. apply in_split_r in H1. simpl in H1. 
  replace (map (snd (B:=exp)) l) with (snd (split l)). auto. symmetry; apply map_snd_snd_split.
  inversion H4; [left; subst; auto | right; congruence].
inversion H1; [left; subst; auto | right; congruence].
Qed.

Lemma str_exp_eq_dec : forall (a1 a2 : (string * exp)), a1 = a2 \/ a1 <> a2.
Proof with auto.
  destruct a1 as (a1s, a1e); destruct a2 as (a2s, a2e).
  assert (S := string_dec_eq a1s a2s). assert (E := exp_eq_dec a1e a2e).
  destruct S; destruct E; subst; solve [left; auto | right; congruence].
Qed.

Lemma str_exp_list_eq_dec : forall (l1 l2 : list (string * exp)), l1 = l2 \/ l1 <> l2.
Proof.
  induction l1. intros; destruct l2; solve [left; auto | right; congruence].
  intros. destruct l2. right; congruence.
  assert (E := str_exp_eq_dec a p). destruct E.
  destruct (IHl1 l2); subst; solve [left; auto | right; congruence].
  right; congruence.
Qed.

Definition fieldnames l := map (@fst string exp) l.
Definition values l := map (@snd string exp) l.
Definition map_values A (f : exp -> A) l := 
  map (fun kv => ((@fst string exp) kv, f ((@snd string exp) kv))) l.
Hint Unfold values fieldnames map_values.

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

Unset Elimination Schemes.
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
Set Elimination Schemes.

Definition lc'_ind := fun (P : nat -> exp -> Prop)
  (rec_lc_fvar : forall (n : nat) (a : atom), P n (exp_fvar a))
  (rec_lc_bvar : forall k n : nat, k < n -> P n (exp_bvar k))
  (rec_lc_abs : forall (n : nat) (e : exp),
        lc' (S n) e -> P (S n) e -> P n (exp_abs e))
  (rec_lc_app : forall (n : nat) (e1 e2 : exp),
        lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_app e1 e2))
  (rec_lc_nat : forall n x : nat, P n (exp_nat x))
  (rec_lc_succ : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_succ e))
  (rec_lc_bool : forall (n : nat) (b : bool), P n (exp_bool b))
  (rec_lc_string : forall (n : nat) (s : string), P n (exp_string s))
  (rec_lc_undef : forall n : nat, P n exp_undef)
  (rec_lc_null : forall n : nat, P n exp_null)
  (rec_lc_not : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_not e))
  (rec_lc_if : forall (n : nat) (e e1 e2 : exp),
        lc' n e ->
        P n e ->
        lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_if e e1 e2))
  (rec_lc_err : forall n : nat, P n exp_err)
  (rec_lc_label : forall (n : nat) (x : atom) (e : exp),
        lc' n e -> P n e -> P n (exp_label x e))
  (rec_lc_break : forall (n : nat) (x : atom) (e : exp),
         lc' n e -> P n e -> P n (exp_break x e))
  (rec_lc_loc : forall (n : nat) (x : loc), P n (exp_loc x))
  (rec_lc_ref : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_ref e))
  (rec_lc_deref : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_deref e))
  (rec_lc_set : forall (n : nat) (e1 e2 : exp),
         lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_set e1 e2))
  (rec_lc_catch : forall (n : nat) (e1 e2 : exp),
         lc' n e1 ->
         P n e1 -> lc' (S n) e2 -> P (S n) e2 -> P n (exp_catch e1 e2))
  (rec_lc_throw : forall (n : nat) (e : exp), lc' n e -> P n e -> P n (exp_throw e))
  (rec_lc_seq : forall (n : nat) (e1 e2 : exp),
         lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_seq e1 e2))
  (rec_lc_finally : forall (n : nat) (e1 e2 : exp),
         lc' n e1 -> P n e1 -> lc' n e2 -> P n e2 -> P n (exp_finally e1 e2))
  (rec_lc_obj : forall (n : nat) (l : list (string * exp)),
         NoDup (fieldnames l) -> Forall (P n) (map (@snd string exp) l) -> P n (exp_obj l)) 
  (rec_lc_getfield : forall (n : nat) o, P n o -> forall f, P n f -> P n (exp_getfield o f))
  (rec_lc_setfield : forall (n : nat) o, P n o -> forall f, P n f -> forall e, P n e -> P n (exp_setfield o f e))
  (rec_lc_delfield : forall (n : nat) o, P n o -> forall f, P n f -> P n (exp_delfield o f))
=>
fix lc'_ind' (n : nat) (e : exp) (l : lc' n e) {struct l} : P n e :=
  match l in (lc' n0 e0) return (P n0 e0) with
  | lc_fvar n0 a => rec_lc_fvar n0 a
  | lc_bvar k n0 l0 => rec_lc_bvar k n0 l0
  | lc_abs n0 e0 l0 => rec_lc_abs n0 e0 l0 (lc'_ind' (S n0) e0 l0)
  | lc_app n0 e1 e2 l0 l1 => rec_lc_app n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_nat n0 x => rec_lc_nat n0 x
  | lc_succ n0 e0 l0 => rec_lc_succ n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_bool n0 b => rec_lc_bool n0 b
  | lc_string n0 s => rec_lc_string n0 s
  | lc_undef n0 => rec_lc_undef n0
  | lc_null n0 => rec_lc_null n0
  | lc_not n0 e0 l0 => rec_lc_not n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_if n0 e0 e1 e2 l0 l1 l2 =>
      rec_lc_if  n0 e0 e1 e2 l0 (lc'_ind' n0 e0 l0) l1 (lc'_ind' n0 e1 l1) l2 (lc'_ind' n0 e2 l2)
  | lc_err n0 => rec_lc_err n0
  | lc_label n0 x e0 l0 => rec_lc_label n0 x e0 l0 (lc'_ind' n0 e0 l0)
  | lc_break n0 x e0 l0 => rec_lc_break n0 x e0 l0 (lc'_ind' n0 e0 l0)
  | lc_loc n0 x => rec_lc_loc n0 x
  | lc_ref n0 e0 l0 => rec_lc_ref n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_deref n0 e0 l0 => rec_lc_deref n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_set n0 e1 e2 l0 l1 => rec_lc_set n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_catch n0 e1 e2 l0 l1 =>
      rec_lc_catch n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' (S n0) e2 l1)
  | lc_throw n0 e0 l0 => rec_lc_throw n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_seq n0 e1 e2 l0 l1 => rec_lc_seq n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_finally n0 e1 e2 l0 l1 => rec_lc_finally n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_obj n0 l0 n1 pf_lc' => rec_lc_obj n0 l0 n1
      ((fix forall_lc_ind T (pf_lc : Forall (lc' n0) T) : Forall (P n0) T :=
        match pf_lc with
          | Forall_nil => Forall_nil (P n0)
          | Forall_cons t l' isVal rest => 
            Forall_cons (A:=exp) (P:=P n0) (l:=l') t (lc'_ind' n0 t isVal) (forall_lc_ind l' rest)
        end) (map (@snd string exp) l0) pf_lc')
  | lc_getfield n0 o f lc_o lc_f  => rec_lc_getfield n0 o (lc'_ind' n0 o lc_o) f (lc'_ind' n0 f lc_f)
  | lc_setfield n0 o f e lc_o lc_f lc_e => rec_lc_setfield n0 o (lc'_ind' n0 o lc_o) f (lc'_ind' n0 f lc_f) e (lc'_ind' n0 e lc_e)
  | lc_delfield n0 o f lc_o lc_f => rec_lc_delfield n0 o (lc'_ind' n0 o lc_o) f (lc'_ind' n0 f lc_f)
  end.

Definition lc := lc' 0.

Unset Elimination Schemes.
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

Definition val_ind := fun (P : exp -> Prop)
  (rec_val_abs : forall e : exp, lc (exp_abs e) -> P (exp_abs e))
  (rec_val_nat : forall n : nat, P (exp_nat n))
  (rec_val_fvar : forall a : atom, P (exp_fvar a))
  (rec_val_bool : forall b : bool, P (exp_bool b))
  (rec_val_string : forall s : string, P (exp_string s))
  (rec_val_undef : P exp_undef)
  (rec_val_null : P exp_null)
  (rec_val_loc : forall l : loc, P (exp_loc l))
  (rec_val_obj : forall l : list (string * exp), Forall P (map (@snd string exp) l) ->
        NoDup (fieldnames l) -> P (exp_obj l))
  (e : exp) (v : val e) =>
  fix val_ind' (e : exp) (v : val e) { struct v } : P e :=
  match v in (val e0) return (P e0) with
    | val_abs x x0 => rec_val_abs x x0
    | val_nat x => rec_val_nat x
    | val_fvar x => rec_val_fvar x
    | val_bool x => rec_val_bool x
    | val_string x => rec_val_string x
    | val_undef => rec_val_undef
    | val_null => rec_val_null
    | val_loc x => rec_val_loc x
    | val_obj x pf_vals x0 => rec_val_obj x
      ((fix forall_val_ind T (pf_vals : Forall val T) : Forall P T :=
        match pf_vals with
          | Forall_nil => Forall_nil P
          | Forall_cons t l' isVal rest => 
            Forall_cons (A:=exp) (P:=P) (l:=l') t (val_ind' t isVal) (forall_val_ind l' rest)
        end) (map (@snd string exp) x) pf_vals) x0
  end.


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

Hint Unfold open lc.
Hint Constructors lc'.

Lemma lc_val : forall v,
  val v -> lc' 0 v.
Proof with auto.
intros. induction v; try inversion H...
Case "exp_obj".
  constructor... subst... induction l; simpl... constructor.
  SCase "head".
  inversion H0. apply H5. subst. inversion H2. auto.  
  SCase "tail". 
  apply IHl. inversion H0... constructor. 
  inversion H2... inversion H2... inversion H3... inversion H2... inversion H3...
Qed.

Hint Resolve lc_val.

Lemma lc_ascend : forall k k' e, k' >= k -> lc' k e -> lc' k' e.
Proof with auto.
intros.
generalize dependent k'.
induction H0...
Case "lc_bvar".
  intros. apply lc_bvar. omega.
Case "lc_abs".
  intros. apply lc_abs. apply IHlc'. omega.
Case "lc_catch".
  intros. apply lc_catch... apply IHlc'2. omega.
Case "lc_obj".
  intros. apply lc_obj... unfold values.
  induction H0; constructor... 
Qed.
Hint Resolve lc_ascend.


Hint Constructors tagof tag.
Lemma decide_tagof : forall e t, tagof e t \/  ~ tagof e t.
Proof.
  intros.
  unfold not.
  destruct e; destruct t; try solve  [ auto | right; intros; inversion H ].
Qed.

Lemma dec_in : forall (l : list string) a, In a l \/ ~ In a l.
Proof with eauto.
induction l. intro; right; intro; inversion H.
intro. assert (dec := string_dec_eq a a0).
destruct dec; auto. inversion H.
 left; constructor...
 assert (H1 := IHl a0). inversion H1. left; right... 
 right. intro. apply H0. inversion H2... contradiction.
Qed.

Lemma dec_no_dup_strings : forall l : list string, NoDup l \/ ~ NoDup l. 
Proof with eauto.
induction l. left. constructor.
inversion IHl. assert (DecIn := dec_in l a).
inversion DecIn. right. intro. inversion H1. contradiction. left. constructor...
right. intro; inversion H0; contradiction.
Qed.

Ltac inverting_and_solve' e := 
  let D := fresh "D" in let Neq := fresh "Neq" in 
    assert (D := e); inversion D; [idtac | right; intro Neq; inversion Neq; contradiction].
Tactic Notation "solve" "by" "inverting" "1" tactic(t) constr(e) := inverting_and_solve' e; left; t; auto.
Tactic Notation "solve" "by" "inverting" "2" tactic(t) constr(e1) constr(e2) := 
  inverting_and_solve' e1; solve by inverting 1 (t) e2.
Tactic Notation "solve" "by" "inverting" "3" tactic(t) constr(e1) constr(e2) constr (e3) := 
  inverting_and_solve' e1; solve by inverting 2 (t) e2 e3.

Lemma decide_lc : forall e, forall n, lc' n e \/  ~ lc' n e.
Proof with eauto.
induction e; intro; try solve [ 
  left; auto
| solve by inverting 1 (constructor) (IHe n)
| solve by inverting 1 (constructor) (IHe (S n))
| solve by inverting 2 (constructor) (IHe1 n) (IHe2 n)
| solve by inverting 2 (constructor) (IHe1 n) (IHe2 (S n))
| solve by inverting 3 (constructor) (IHe1 n) (IHe2 n) (IHe3 n)
].
Case "exp_bvar".
  destruct (dec_le n0 n). 
  right. intro. inversion H0. omega.
  left. constructor. omega.
Case "exp_obj".
  assert (Forall (fun e => lc' n e \/ ~ lc' n e) (map (snd (B:=exp)) l)).
    induction H. constructor. apply Forall_cons. apply H. apply IHForall.
  apply forall_dec_dec_forall in H0. inversion H0. 
  SCase "Everything in l is locally closed".
    destruct (dec_no_dup_strings (fieldnames l)).
    SSCase "Field names are distinct". left. constructor. auto. unfold values... 
    SSCase "Field names are not distinct". right; intro; apply H2. inversion H3...
  SCase "Not everything in l is locally closed". right. intro. apply H1. inversion H2. apply H6.
Qed.


Lemma decide_val : forall e, val e \/ ~ val e.
Proof with eauto.
unfold not. intro. 
induction e; try solve [left; constructor | right; intro H; inversion H].
Case "exp_abs". 
induction IHe. left. constructor. constructor. apply lc_ascend with 0...
assert (lc' 1 e \/ ~ lc' 1 e). apply decide_lc.
inversion H0. left; constructor... right; intro. apply H1. inversion H2. inversion H4. auto.
Case "exp_obj".
apply (forall_dec_dec_forall val (l:=(map (@snd string exp) l))) in H.
inversion H. assert (H1 := dec_no_dup_strings (fieldnames l)).
inversion H1. left; constructor; unfold values; auto... right. intro. inversion H3. contradiction.
right. intro. inversion H1. contradiction.
Qed.


Inductive E : Set :=
  | E_hole    : E
  | E_app_1   : E -> exp -> E
  | E_app_2   : exp -> E -> E
  | E_succ    : E -> E
  | E_not     : E -> E
  | E_if      : E -> exp -> exp -> E
  | E_label   : atom -> E -> E
  | E_break   : atom -> E -> E
  | E_ref     : E -> E
  | E_deref   : E -> E
  | E_setref1 : E -> exp -> E
  | E_setref2 : exp -> E -> E
  | E_catch   : E -> exp -> E
  | E_throw   : E -> E
  | E_seq   : E -> exp -> E
  | E_finally  : E -> exp -> E
  | E_obj     : forall (vs : list (string * exp)) (es : list (string * exp)), 
                  (Forall val (values vs)) -> string -> E -> E
  | E_getfield1 : E -> exp -> E
  | E_getfield2 : exp -> E -> E
  | E_setfield1 : E -> exp -> exp -> E
  | E_setfield2 : exp -> E -> exp -> E
  | E_setfield3 : exp -> exp -> E -> E
  | E_delfield1 : E -> exp -> E
  | E_delfield2 : exp -> E -> E
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
  | E_getfield_2 : forall v1 e2,
      val v1 ->
      lc e2 ->
      E' (exp_getfield v1 e2) e2
  | E'_delfield_1 : forall e1 e2,
      lc e1 ->
      lc e2 ->
      E' (exp_delfield e1 e2) e1
  | E_delfield_2 : forall v1 e2,
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

Inductive ae : exp -> Prop :=
  | redex_app  : forall e1 e2, val e1 -> val e2 -> ae (exp_app e1 e2)
  | redex_succ : forall e, val e -> ae (exp_succ e)
  | redex_not  : forall e, val e -> ae (exp_not e)
  | redex_if   : forall e e1 e2, 
      val e -> lc e1 -> lc e2 -> ae (exp_if e e1 e2)
  | redex_label : forall x v, val v -> ae (exp_label x v)
   | redex_label_match_and_mismatch : forall x y v,
       val v ->
       ae (exp_label x (exp_break y v))
   | redex_break : forall x e v, 
     val v -> 
     G e (exp_break x v) ->
     ae e
  | redex_ref   : forall v, val v -> ae (exp_ref v)
  | redex_deref : forall v, val v -> ae (exp_deref v)
  | redex_set  : forall v1 v2, val v1 -> val v2 -> ae (exp_set v1 v2)
  | redex_uncatch : forall v e, val v -> lc' 1 e -> ae (exp_catch v e)
  | redex_catch : forall e, lc' 1 e -> ae (exp_catch exp_err e)
  | redex_throw : forall v, val v -> ae (exp_throw v)
  | redex_seq   : forall v e, val v -> lc e -> ae (exp_seq v e)
  | redex_finally : forall v e, val v -> lc e -> ae (exp_finally v e)
  | redex_finally_err : forall e , lc e -> ae (exp_finally exp_err e)
  | redex_finally_break : forall x v e, 
      val v -> 
      lc e -> 
       ae (exp_finally (exp_break x v) e)
  | redex_err_bubble : forall e,
      lc e ->
      F e exp_err ->
      ae e
  | redex_getfield : forall o f, val o -> val f -> ae (exp_getfield o f)
  | redex_setfield : forall o f e, val o -> val f -> val e -> ae (exp_setfield o f e)
  | redex_delfield : forall o f, val o -> val f -> ae (exp_delfield o f)
.

Inductive decompose : exp -> E -> exp -> Prop :=
  | cxt_hole : forall e,
      ae e ->
      decompose e E_hole e
  | cxt_app_1 : forall E e1 e2 e',
      decompose e1 E e' ->
      decompose (exp_app e1 e2) (E_app_1 E e2) e'
  | cxt_app_2 : forall E v e e',
      val v ->
      decompose e E e' ->
      decompose (exp_app v e) (E_app_2 v E) e'
  | cxt_succ : forall E e e',
      decompose e E e' ->
      decompose (exp_succ e) (E_succ E) e'
  | cxt_not : forall E e e',
      decompose e E e' ->
      decompose (exp_not e) (E_not E) e'
  | cxt_if : forall E e e1 e2 e',
      decompose e E e' ->
      decompose (exp_if e e1 e2) (E_if E e1 e2) e'
  | cxt_break : forall x e E ae,
      decompose e E ae ->
      decompose (exp_break x e) (E_break x E) ae
  | cxt_label : forall x e E ae,
      decompose e E ae ->
      decompose (exp_label x e) (E_label x E) ae
  | cxt_ref : forall e E ae,
     decompose e E ae ->
     decompose (exp_ref e) (E_ref E) ae
  | cxt_deref : forall e E ae,
     decompose e E ae ->
     decompose (exp_deref e) (E_deref E) ae
  | cxt_set1 : forall e1 e2 E ae,
      decompose e1 E ae ->
      decompose (exp_set e1 e2) (E_setref1 E e2) ae
  | cxt_set2 : forall e1 e2 E ae,
      val e1 ->
      decompose e2 E ae ->
      decompose (exp_set e1 e2) (E_setref2 e1 E) ae
  | cxt_throw : forall e E ae,
      decompose e E ae ->
      decompose (exp_throw e) (E_throw E) ae
  | cxt_catch : forall e1 e2 E ae,
      decompose e1 E ae ->
      decompose (exp_catch e1 e2) (E_catch E e2) ae
  | cxt_seq : forall E e1 e2 ae,
      decompose e1 E ae ->
      decompose (exp_seq e1 e2) (E_seq E e2) ae
  | cxt_finally : forall E e1 e2 ae,
      decompose e1 E ae ->
      decompose (exp_finally e1 e2) (E_finally E e2) ae
  | cxt_obj  : forall vs es k e E e' (are_vals : Forall val (values vs)),
      decompose e E e' ->
      decompose (exp_obj (vs++(k,e)::es)) (E_obj vs es are_vals k E) e'
  | cxt_getfield1 : forall o f E ae,
      decompose o E ae ->
      decompose (exp_getfield o f) (E_getfield1 E f) ae
  | cxt_getfield2 : forall o f E ae,
      val o ->
      decompose f E ae ->
      decompose (exp_getfield o f) (E_getfield2 o E) ae
  | cxt_setfield1 : forall o f e E ae,
      decompose o E ae ->
      decompose (exp_setfield o f e) (E_setfield1 E f e) ae
  | cxt_setfield2 : forall o f e E ae,
      val o ->
      decompose f E ae ->
      decompose (exp_setfield o f e) (E_setfield2 o E e) ae
  | cxt_setfield3 : forall o f e E ae,
      val o -> val f ->
      decompose e E ae ->
      decompose (exp_setfield o f e) (E_setfield3 o f E) ae
  | cxt_delfield1 : forall o f E ae,
      decompose o E ae ->
      decompose (exp_delfield o f) (E_delfield1 E f) ae
  | cxt_delfield2 : forall o f E ae,
      val o ->
      decompose f E ae ->
      decompose (exp_delfield o f) (E_delfield2 o E) ae
.

Fixpoint plug (e : exp) (cxt : E) := match cxt with
  | E_hole => e
  | E_app_1 cxt e2 => exp_app (plug e cxt) e2
  | E_app_2 v cxt => exp_app v (plug e cxt)
  | E_succ cxt => exp_succ (plug e cxt)
  | E_not cxt => exp_not (plug e cxt)
  | E_if cxt e1 e2 => exp_if (plug e cxt) e1 e2
  | E_label x cxt => exp_label x (plug e cxt)
  | E_break x cxt => exp_break x (plug e cxt)
  | E_ref cxt => exp_ref (plug e cxt)
  | E_deref cxt => exp_deref (plug e cxt)
  | E_setref1 cxt e2 => exp_set (plug e cxt) e2
  | E_setref2 v1 cxt => exp_set v1 (plug e cxt)
  | E_catch cxt e2 => exp_catch (plug e cxt) e2
  | E_throw cxt    => exp_throw (plug e cxt)
  | E_seq cxt e2   => exp_seq (plug e cxt) e2
  | E_finally cxt e2 => exp_finally (plug e cxt) e2
  | E_obj vs es _ k cxt => exp_obj (vs++(k,plug e cxt)::es)
  | E_getfield1 cxt f => exp_getfield (plug e cxt) f
  | E_getfield2 v cxt => exp_getfield v (plug e cxt)
  | E_setfield1 cxt f e' => exp_setfield (plug e cxt) f e'
  | E_setfield2 v cxt e' => exp_setfield v (plug e cxt) e'
  | E_setfield3 v f cxt => exp_setfield v f (plug e cxt)
  | E_delfield1 cxt f => exp_delfield (plug e cxt) f
  | E_delfield2 v cxt => exp_delfield v (plug e cxt)
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
  | step_red : forall s e E ae e',
    lc e ->
    decompose e E ae ->
    red ae e' ->
    step s e s (plug e' E)
  | step_ref : forall E e v l s (pf : val v),
    lc e ->
    decompose e E (exp_ref v) ->
    ~ In l (map (@fst AtomEnv.key stored_val) (AtomEnv.elements s)) ->
    step s e (AtomEnv.add l (val_with_proof pf) s) (plug (exp_loc l) E)
  | step_deref : forall e s E l v (pf : val v),
    lc e ->
    decompose e E (exp_deref (exp_loc l)) ->
    AtomEnv.find l s = Some (val_with_proof pf) ->
    step s e s (plug v E)
  | step_deref_err : forall e s E l,
    lc e ->
    decompose e E (exp_deref (exp_loc l)) ->
    AtomEnv.find l s = None ->
    step s e s (plug exp_err E)
  | step_setref : forall s e E l v v_old (pf_v : val v) (pf_v_old : val v_old),
    lc e ->
    decompose e E (exp_set (exp_loc l) v) ->
    AtomEnv.find l s = Some (val_with_proof pf_v_old) ->
    step s e (AtomEnv.add l (val_with_proof pf_v) s) (plug (exp_loc l) E)
  | step_setref_err : forall s e E l v,
    lc e ->
    decompose e E (exp_set (exp_loc l) v) ->
    AtomEnv.find l s = None ->
    step s e s (plug exp_err E)
  | step_err : forall x v s,
      val v ->
      step s (exp_break x v) s exp_err
.

End Definitions.

Tactic Notation "exp_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "exp_fvar"
    | Case_aux c "exp_bvar"
    | Case_aux c "exp_abs"
    | Case_aux c "exp_app"
    | Case_aux c "exp_nat"
    | Case_aux c "exp_succ"
    | Case_aux c "exp_bool"
    | Case_aux c "exp_string"
    | Case_aux c "exp_undef"
    | Case_aux c "exp_null"
    | Case_aux c "exp_not"
    | Case_aux c "exp_if"
    | Case_aux c "exp_err"
    | Case_aux c "exp_label"
    | Case_aux c "exp_break"
    | Case_aux c "exp_loc"
    | Case_aux c "exp_ref"
    | Case_aux c "exp_deref"
    | Case_aux c "exp_set"
    | Case_aux c "exp_catch"
    | Case_aux c "exp_throw"
    | Case_aux c "exp_seq"
    | Case_aux c "exp_finally"
    | Case_aux c "exp_obj"
    | Case_aux c "exp_getfield"
    | Case_aux c "exp_setfield"
    | Case_aux c "exp_delfield"
 ].
Tactic Notation "lc_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "lc_fvar"
    | Case_aux c "lc_bvar"
    | Case_aux c "lc_abs"
    | Case_aux c "lc_app"
    | Case_aux c "lc_nat"
    | Case_aux c "lc_succ"
    | Case_aux c "lc_bool"
    | Case_aux c "lc_string"
    | Case_aux c "lc_undef"
    | Case_aux c "lc_null"
    | Case_aux c "lc_not"
    | Case_aux c "lc_if"
    | Case_aux c "lc_err"
    | Case_aux c "lc_label"
    | Case_aux c "lc_break"
    | Case_aux c "lc_loc"
    | Case_aux c "lc_ref"
    | Case_aux c "lc_deref"
    | Case_aux c "lc_set"
    | Case_aux c "lc_catch"
    | Case_aux c "lc_throw"
    | Case_aux c "lc_seq"
    | Case_aux c "lc_finally"
    | Case_aux c "lc_obj" 
    | Case_aux c "lc_getfield"
    | Case_aux c "lc_setfield"
    | Case_aux c "lc_delfield"
].
Tactic Notation "val_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "val_abs"
    | Case_aux c "val_nat"
    | Case_aux c "val_fvar"
    | Case_aux c "val_bool"
    | Case_aux c "val_string"
    | Case_aux c "val_undef"
    | Case_aux c "val_null"
    | Case_aux c "val_loc"
    | Case_aux c "val_obj" ].
Tactic Notation "E_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "E_hole"
    | Case_aux c "E_app_1"
    | Case_aux c "E_app_2"
    | Case_aux c "E_succ"
    | Case_aux c "E_not"
    | Case_aux c "E_if"
    | Case_aux c "E_label"
    | Case_aux c "E_break"
    | Case_aux c "E_ref"
    | Case_aux c "E_deref"
    | Case_aux c "E_setref1"
    | Case_aux c "E_setref2"
    | Case_aux c "E_seq"
    | Case_aux c "E_finally"
    | Case_aux c "E_obj"
    | Case_aux c "E_getfield1"
    | Case_aux c "E_getfield2"
    | Case_aux c "E_setfield1"
    | Case_aux c "E_setfield2"
    | Case_aux c "E_setfield3"
    | Case_aux c "E_delfield1"
    | Case_aux c "E_delfield2"
 ].
Tactic Notation "redex_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "redex_app"
    | Case_aux c "redex_succ"
    | Case_aux c "redex_not"
    | Case_aux c "redex_if"
    | Case_aux c "redex_label"
    | Case_aux c "redex_break"
    | Case_aux c "redex_ref"
    | Case_aux c "redex_deref"
    | Case_aux c "redex_set"
    | Case_aux c "redex_uncatch"
    | Case_aux c "redex_catch"
    | Case_aux c "redex_throw"
    | Case_aux c "redex_seq"
    | Case_aux c "redex_finally" 
    | Case_aux c "redex_finally_err" 
    | Case_aux c "redex_err_bubble" 
    | Case_aux c "redex_getfield"
    | Case_aux c "redex_setfield"
    | Case_aux c "redex_delfield"
].
Tactic Notation "decompose_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "decompose_hole"
    | Case_aux c "decompose_app_1"
    | Case_aux c "decompose_app_2"
    | Case_aux c "decompose_succ"
    | Case_aux c "decompose_not"
    | Case_aux c "decompose_if"
    | Case_aux c "decompose_break"
    | Case_aux c "decompose_label"
    | Case_aux c "decompose_ref"
    | Case_aux c "decompose_deref"
    | Case_aux c "decompose_set1"
    | Case_aux c "decompose_set2" 
    | Case_aux c "decompose_throw"
    | Case_aux c "decompose_catch"
    | Case_aux c "decompose_seq"
    | Case_aux c "decompose_finally"
    | Case_aux c "decompose_obj"
    | Case_aux c "decompose_getfield1"
    | Case_aux c "decompose_getfield2"
    | Case_aux c "decompose_setfield1"
    | Case_aux c "decompose_setfield2"
    | Case_aux c "decompose_setfield3"
    | Case_aux c "decompose_delfield1" 
    | Case_aux c "decompose_delfield2" 
].
Tactic Notation "decompose1_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "decompose1_hole"
    | Case_aux c "decompose1_app_1"
    | Case_aux c "decompose1_app_2"
    | Case_aux c "decompose1_succ"
    | Case_aux c "decompose1_not"
    | Case_aux c "decompose1_if"
    | Case_aux c "decompose1_break"
    | Case_aux c "decompose1_ref"
    | Case_aux c "decompose1_deref"
    | Case_aux c "decompose1_set1"
    | Case_aux c "decompose1_set2"
    | Case_aux c "decompose1_throw"
    | Case_aux c "decompose1_seq"
    | Case_aux c "decompose1_obj" 
    | Case_aux c "decompose1_getfield1" 
    | Case_aux c "decompose1_getfield2" 
    | Case_aux c "decompose1_setfield1" 
    | Case_aux c "decompose1_setfield2" 
    | Case_aux c "decompose1_setfield3" 
    | Case_aux c "decompose1_delfield1" 
    | Case_aux c "decompose1_delfield2" 
].
Tactic Notation "red_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "red_succ"
    | Case_aux c "red_not"
    | Case_aux c "red_if1"
    | Case_aux c "red_if2"
    | Case_aux c "red_app"
    | Case_aux c "red_app_err"
    | Case_aux c "red_if_err"
    | Case_aux c "red_label"
    | Case_aux c "red_break_bubble"
    | Case_aux c "red_break_match"
    | Case_aux c "red_break_mismatch"
    | Case_aux c "red_set_err"
    | Case_aux c "red_deref_err"
    | Case_aux c "red_err_bubble"
    | Case_aux c "red_throw"
    | Case_aux c "red_catch_normal"
    | Case_aux c "red_catch_catch"
    | Case_aux c "red_seq"
    | Case_aux c "red_finally_normal"
    | Case_aux c "red_finally_propagate_err"
    | Case_aux c "red_finally_propagate_break" 
    | Case_aux c "red_getfield"
    | Case_aux c "red_getfield_notfound"
    | Case_aux c "red_getfield_proto"
    | Case_aux c "red_getfield_err_notobj"
    | Case_aux c "red_getfield_err_notstr"
    | Case_aux c "red_setfield_update"
    | Case_aux c "red_setfield_add"
    | Case_aux c "red_setfield_err_notobj"
    | Case_aux c "red_setfield_err_notstr"
    | Case_aux c "red_delfield"
    | Case_aux c "red_delfield_notfound"
    | Case_aux c "red_delfield_err_notobj"
    | Case_aux c "red_delfield_err_notstr"
].
Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "step_red"
  | Case_aux c "step_ref"
  | Case_aux c "step_deref"
  | Case_aux c "step_deref_err"
  | Case_aux c "step_setref"
  | Case_aux c "step_setref_err" ].

Hint Unfold values fieldnames map_values.
Hint Unfold open lc.
Hint Constructors lc'.
Hint Resolve lc_val.
Hint Resolve lc_ascend.
Hint Constructors tagof tag.
Hint Constructors decompose E val exp ae exp val ae red
                  step stored_val.

Lemma decompose_ae : forall e E e',
  decompose e E e' -> ae e'.
Proof with auto. intros. induction H... Qed.


Lemma val_injective : forall e1 e2, e1 = e2 -> (val e1 <-> val e2).
Proof with eauto. intros; subst... tauto. Qed.

Lemma plug_ok : forall e E e',
  decompose e E e' -> plug e' E = e.
Proof.
intros. Print decompose.
decompose_cases (induction H) Case; simpl; try (auto || rewrite -> IHdecompose; auto).
Qed.

Ltac destruct_decomp e := match goal with
  |  [ H : exists E : E, exists ae : exp, decompose e E ae |- _ ] =>
       destruct H as [E [ae H]]
  | _ => fail
end.



Lemma decompose_lc : forall E e ae,
  lc e ->
  decompose e E ae ->
  lc ae.
Proof. intros. decompose_cases (induction H0) Case; try solve [inversion H; eauto | auto].
Case "decompose_obj".
  apply IHdecompose. 
 apply Forall_in with (l := values (vs ++ (k, e) :: es)).
  unfold lc in H. inversion H.  auto.
  unfold values; rewrite map_app; simpl; apply in_middle.
Qed.

Inductive val' : exp -> Prop :=
  | val'_err : val' exp_err
  | val'_val : forall v, val v -> val' v
  | val'_break : forall x v, val v -> val' (exp_break x v)
.

Lemma lc_val' : forall v, val' v -> lc' 0 v.
Proof with auto. intros. inversion H... Qed.

Hint Constructors val' E' F G. 

Ltac clean_decomp := repeat match goal with
  | [ H1 : ?cond, IH : ?cond -> ?exp |- _ ] => let H := fresh "IH" in
    (assert exp as H by (apply IH; exact H1); clear IH)
  | [ IH : 0 = 0 -> ?exp |- _ ]
    => let H := fresh IH in
       (assert exp as H by (apply IH; reflexivity); clear IH)
  | [ IH : 1 = 0 -> _ |- _ ]
    => clear IH
end.

Ltac invert_val' := repeat match goal with
  | [ IH : val' ?e |- _ ]
    => (inversion IH; clear IH)
end.

Ltac solve_break_err H e :=
  let HV := fresh "HV" in 
  let HE := fresh "HE" in 
    destruct H as [HV | HE]; [idtac | destruct_decomp e; eauto 7];
    subst; eauto; inversion HV; clear HV; eauto; 
      [ right; exists E_hole; eapply ex_intro; apply cxt_hole; 
        try solve [apply redex_err_bubble; auto | constructor; auto]
      | subst
      | right; exists E_hole; eapply ex_intro; apply cxt_hole; 
        match goal with 
        | [ H: exp_break ?x ?v = _ |- _] => try solve [apply redex_break with x v; auto; constructor; auto| constructor; auto]
        end]. 

Lemma decomp : forall e,
  lc e -> val' e \/ 
          (exists E, exists ae, decompose e E ae).
Proof with eauto 7.
intros.
unfold lc in H.
remember 0.
remember H as LC. clear HeqLC.
move H after LC.
lc_cases (induction H) Case; intros; subst; clean_decomp; try solve [inversion LC; subst; repeat match goal with
|  [ H :  lc' 0 ?e -> val' ?e \/ _ ,
          (* should be  val ?e' \/ (exists (E : E) (ae : exp), decomposition ?e E ae), but coq8.4 chokes on it *)
     HLC : lc' 0 ?e
   |- _ ] => let H' := fresh in assert (H' := H HLC); clear H
| [ LC1 : lc' _ ?e1, H : val' ?e1 \/ _ |- val' (_ ?e1) \/ _ ] => solve_break_err H e1
| [ LC1 : lc' _ ?e1, H : val' ?e1 \/ _ |- val' (_ ?e1 _) \/ _ ] => solve_break_err H e1
| [ LC2 : lc' _ ?e2, H : val' ?e2 \/ _ |- val' (_ _ ?e2) \/ _ ] => solve_break_err H e2
| [ LC1 : lc' _ ?e1, H : val' ?e1 \/ _ |- val' (_ ?e1 _ _) \/ _ ] => solve_break_err H e1
| [ LC2 : lc' _ ?e2, H : val' ?e2 \/ _ |- val' (_ _ ?e2 _) \/ _ ] => solve_break_err H e2
| [ LC3 : lc' _ ?e3, H : val' ?e3 \/ _ |- val' (_ _ _ ?e3) \/ _ ] => solve_break_err H e3
end; eauto 7].
Case "lc_bvar".
  inversion H.
Case "lc_break".
  inversion IH. 
    inversion H0. right. exists E_hole. repeat eapply ex_intro. apply cxt_hole. apply redex_err_bubble... left...
    right. eapply ex_intro; eapply ex_intro; apply cxt_hole. eapply redex_break...
  destruct_decomp e. right; exists (E_break x E); exists ae; auto.
Case "lc_obj".
  assert (forall x : string * exp, In x l -> decidable (val (snd x))). intros; apply decide_val.
  assert (Split := (take_while l (fun kv => val (snd kv)) H1)).
  inversion Split. 
  SCase "Everything in (exp_obj l) is already a value".
    left. constructor. constructor... unfold values; rewrite map_snd_snd_split. apply forall_snd_comm...
  SCase "Something in (exp_obj l) is not yet a value".
    inversion_clear H2. inversion_clear H3. 
    inversion_clear H2. inversion_clear H3. inversion_clear H4.
    remember x1 as x1'; destruct x1'.
    assert (Forall val (values x)). unfold values; rewrite map_snd_snd_split; apply forall_snd_comm...
    assert (val' e \/ (exists E, exists ae, decompose e E ae)).   
      inversion LC. rewrite H2 in H0. rewrite map_snd_snd_split in H0. rewrite snd_split_comm in H0.
      simpl in H0. rewrite forall_app in H0. inversion_clear H0. inversion_clear H11.
      apply H0... rewrite Forall_forall in H9; apply H9. subst. unfold values. 
      rewrite map_snd_snd_split. rewrite snd_split_comm. simpl. apply in_middle. 
    inversion H6. 
      SSCase "e is a val'". invert_val'; subst.
        SSSCase "e is exp_err". right.
          exists E_hole. eapply ex_intro. apply cxt_hole. constructor. apply LC.
          constructor. constructor; auto.
        SSSCase "e is a val". contradiction. 
        SSSCase "e is a break".
          right.
          exists E_hole. eapply ex_intro. apply cxt_hole. 
          apply redex_break with (x := x2) (v := v). trivial.
          constructor. constructor. trivial. auto.
      SSCase "e is not a val'".
        inversion H7. inversion H8. right. exists (E_obj x x0 H4 s x2). exists x3. 
        rewrite H2. apply cxt_obj...
Qed.

Hint Resolve decompose_lc.
Hint Unfold not.

(* Invert tagof *)
Hint Extern 1 ( False ) => match goal with
  | [ H: tagof _ _ |- False]  => inversion H
end.

Lemma progress : forall sto e,
  lc e ->
  val e \/ e = exp_err \/ (exists e', exists sto', step sto e sto' e').
Proof with eauto.
intros.
remember H as HLC; clear HeqHLC.
apply decomp in H.
destruct H. destruct H...
right. right. exists exp_err. exists sto0. auto.
destruct_decomp e...
right. right.
assert (LC.ae ae). apply decompose_ae in H...


inversion H0; subst...
(* redex_cases (inversion H0) Case; subst... *)
Case "redex_app". val_cases (inversion H1) SCase; subst; eauto 6.
Case "redex_if". val_cases (inversion H1) SCase; subst; first [destruct b; eauto 6 | eauto 6]. 
Case "redex_label_break".
  assert ({ x = y } + { ~ x = y }). apply Atom.atom_eq_dec.
  destruct H2; subst...
Case "redex_ref".
assert (exists l : atom, 
          ~ In l (map (@fst AtomEnv.key stored_val) (AtomEnv.elements sto0))) 
    as [l HnotInL].
  apply Atom.atom_fresh_for_list.
exists (plug (exp_loc l) E).
exists (AtomEnv.add l (val_with_proof H1) sto0)...
Case "redex_deref".
val_cases (inversion H1) SCase; subst; try solve [ exists (plug exp_err E); eauto ].
  SCase "val_loc". remember (AtomEnv.find l sto0) as MaybeV.
  destruct MaybeV...
  destruct s...
Case "redex_set".
val_cases (inversion H1) SCase; subst; try solve [ exists (plug exp_err E); eauto ].
  SCase "val_loc". remember (AtomEnv.find l sto0) as MaybeV.
  destruct MaybeV...
  destruct s.
  exists (plug (exp_loc l) E).
  exists (AtomEnv.add l (val_with_proof H2) sto0)...
Case "redex_getfield".
  destruct (decide_tagof o TagObj).
  inversion H3. destruct (decide_tagof f TagString). inversion H5. destruct (dec_in (fieldnames l) s). 
    exists (plug (lookup_assoc l s exp_err string_eq_dec) E); exists sto0. subst; eapply step_red... 
    destruct (dec_in (fieldnames l) __proto__).
      exists (plug (exp_getfield (exp_deref (exp_getfield o (exp_string __proto__))) f) E); exists sto0. subst; eapply step_red...
      exists (plug exp_undef E); exists sto0. subst; eapply step_red...
    exists (plug exp_err E); exists sto0. subst; eapply step_red...
  exists (plug exp_err E); exists sto0; subst; eapply step_red...
Case "redex_setfield".
  destruct (decide_tagof o TagObj).
  inversion H4. destruct (decide_tagof f TagString). inversion H6. 
    destruct (dec_in (fieldnames l) s).
      exists (plug (exp_obj (update_assoc l s e0 string_eq_dec)) E); exists sto0. subst; eapply step_red...
      exists (plug (exp_obj ((s,e0)::l)) E); exists sto0. subst; eapply step_red...
    exists (plug exp_err E); exists sto0. subst; eapply step_red...
  exists (plug exp_err E); exists sto0; subst; eapply step_red...
Case "redex_delfield".
  destruct (decide_tagof o TagObj).
  inversion H3. destruct (decide_tagof f TagString). inversion H5.
    destruct (dec_in (fieldnames l) s). 
      exists (plug (exp_obj (remove_fst s l string_eq_dec)) E); exists sto0. subst; eapply step_red... 
      exists (plug o E); exists sto0. subst; eapply step_red...
    exists (plug exp_err E); exists sto0; subst; eapply step_red...
  exists (plug exp_err E); exists sto0; subst; eapply step_red...
Qed.

Ltac solve_lc_plug := match goal with
  | [ IHdecompose : lc' 0 ?e -> lc' 0 (plug ?e' ?E),
      H : lc' 0 ?e
      |- context [plug ?e' ?E] ]
    => (apply IHdecompose in H; auto)
end.

Lemma lc_plug : forall E ae e e',
  lc e ->
  lc e' ->
  decompose e E ae ->
  lc (plug e' E).
Proof with auto.
intros.
decompose_cases (induction H1) Case;
 first [ inversion H; subst; simpl; unfold lc in *; constructor ; try solve_lc_plug; auto | auto ]. 
Case "decompose_obj".
  SCase "Proving NoDup of fieldnames after plugging".
  unfold fieldnames in *. rewrite map_fst_fst_split. rewrite fst_split_comm. simpl.
  rewrite map_fst_fst_split in H3; rewrite fst_split_comm in H3; simpl in H3...
  SCase "Proving all are values after plugging".
  unfold values in *. rewrite map_snd_snd_split; rewrite snd_split_comm; simpl.
  rewrite map_snd_snd_split in H5; rewrite snd_split_comm in H5; simpl in H5...
  rewrite forall_app. rewrite forall_app in H5. inversion H5. split... inversion H4... 
Qed.

Hint Resolve lc_plug.

Lemma lc_active : forall e,
  ae e -> lc e.
Proof with eauto.
  intros.
  remember H.
  unfold lc.
  clear Heqa.
  inversion a; try solve [constructor; eauto using lc_val].

  subst. inversion H1; subst... inversion H2; subst...
  trivial.
Qed.

Hint Resolve lc_active.

Lemma lc_open : forall k e u,
  lc' (S k) e ->
  lc' 0 u ->
  lc' k (open_rec k u e).
Proof with auto.
intros.
generalize dependent k.
exp_cases (induction e) Case; intros; try solve [simpl; inversion H; subst;  eauto].
Case "exp_bvar".
  simpl. 
  assert (H1 := Coq.Arith.Compare_dec.lt_eq_lt_dec k n).
  destruct H1. destruct s.
  SCase "k < n".
    inversion H. subst. assert (beq_nat k n = false). rewrite -> beq_nat_false_iff. omega. rewrite -> H1. apply lc_ascend with (k := S k). omega. exact H.
  SCase "k = n". 
    rewrite <- beq_nat_true_iff in e.
    rewrite -> e.  apply lc_ascend with (k := 0) (k' := k)... omega.
  SCase "k > n". Check beq_nat.
    assert (beq_nat k n = false). rewrite -> beq_nat_false_iff... omega.
    rewrite -> H1...
Case "exp_obj".
  simpl. unfold map_values. apply forall_map_comm in H. constructor. 
  SCase "NoDup". 
    inversion H1. unfold fieldnames in *. rewrite map_fst_fst_split in *.
    rewrite fst_split_map_snd...
  SCase "values". 
    unfold values. apply forall_map_comm. apply forall_map_comm. simpl. 
    rewrite Forall_forall. rewrite Forall_forall in H.
    intros. apply H... inversion H1. rewrite Forall_forall in H6. apply H6. 
    destruct x as (s, e). subst. unfold values. rewrite map_snd_snd_split. apply in_split_r...
Qed.


Lemma lc_red : forall ae e,
  lc ae ->
  red ae e ->
  lc e.
Proof with auto.
intros.
red_cases (destruct H0) Case; try solve [auto | inversion H; auto].
Case "red_succ". simpl. exp_cases (destruct e) SCase; auto.
Case "red_not". simpl. exp_cases (destruct e) SCase; auto.
Case "red_app".
  unfold lc in *.
  inversion H; subst.
  unfold open.
  inversion H4; subst.
  apply lc_open. exact H3. exact H5.
Case "red_break_bubble".
  inversion H0; subst... inversion H1; subst...
  inversion H3; subst... 
  unfold values in H7.
  rewrite map_app in H7.
  rewrite forall_app in H7. 
  destruct H7.
  inversion H6.
  trivial.
Case "red_break_match".
  inversion H; inversion H2; subst...
Case "red_catch_catch".
  unfold lc in *.
  inversion H; subst.
  unfold open.
  apply lc_open...
Case "red_getfield".
  induction l. inversion H1.
  destruct a as (astr, aexp). simpl.
  destruct (string_eq_dec f astr). inversion H0. simpl in H3. inversion H3. apply lc_val...
  apply IHl. inversion H. inversion H5. simpl in *. inversion H8. inversion H10. subst.
  constructor...
  inversion H0. inversion H3. constructor... inversion H4...
  inversion H1. simpl in H2. symmetry in H2; contradiction. auto.
Case "red_setfield_update".
  induction l. inversion H2.
  destruct a as (astr, aexp). simpl.
  destruct (string_eq_dec f astr). inversion H. subst. inversion H7. simpl in H6. inversion H6. subst.
  constructor... constructor...
  constructor... simpl. 
  unfold fieldnames in *; rewrite <- update_fieldnames_eq. inversion H0. simpl in H5...
  constructor. inversion H. inversion H7; subst. simpl; simpl in H13; inversion H13...
  fold (map (@snd string exp) (update_assoc l f v string_eq_dec)); apply update_values_eq. inversion H0. inversion H4. rewrite Forall_forall in *; subst; intros. apply lc_val... apply lc_val...
Case "red_setfield_add".
  constructor. simpl. constructor... inversion H0... simpl. constructor... inversion H0...
  rewrite Forall_forall in H4; apply Forall_forall; intros; apply lc_val...
Case "red_delfield".
  unfold fieldnames in H1; rewrite map_fst_fst_split in H1; apply (in_split_fst f l) in H1. 
  inversion_clear H1; inversion_clear H2; inversion_clear H1. subst.  
  inversion_clear H; clear H2; inversion_clear H1; subst. unfold fieldnames in H; rewrite map_fst_fst_split in H.  
  rewrite fst_split_comm in H. assert (ND1 := NoDup_remove_1 (fst (split x)) (fst (split x0)) f H).
  assert (ND2 := NoDup_remove_2 (fst (split x)) (fst (split x0)) f H).
  assert (~ (In f (fst (split x)) \/ In f (fst (split x0)))).
  intro. apply (in_or_app (fst (split x)) (fst (split x0)) f) in H1. contradiction. 
  assert (~ In f (fst (split x))). intro; apply H1; left...
  assert (~ In f (fst (split x0))). intro; apply H1; right... clear ND2. clear H1.
  constructor. 
  rewrite remove_app_comm. unfold fieldnames. rewrite map_fst_fst_split. 
  rewrite fst_split_comm2. rewrite fst_split_comm2. simpl. destruct (string_eq_dec f f). simpl.
  rewrite (not_in_remove_eq f x string_eq_dec H3) in ND1. 
  rewrite (not_in_remove_eq f x0 string_eq_dec H4) in ND1...
  rewrite (not_in_remove_eq f x string_eq_dec H3) in H.
  rewrite (not_in_remove_eq f x0 string_eq_dec H4) in H...
  rewrite Forall_forall in H2. rewrite Forall_forall; intros. rewrite remove_app_comm in H1.
  unfold values in H1. rewrite map_snd_snd_split in H1.
  rewrite snd_split_comm2 in H1; rewrite snd_split_comm2 in H1.
  apply in_app_or in H1. inversion_clear H1. apply H2. unfold values. rewrite map_snd_snd_split.
  rewrite snd_split_comm. apply in_or_app. left. rewrite (not_in_remove_eq f x string_eq_dec H3)...
  apply in_app_or in H5. inversion_clear H5. simpl in H1. destruct (string_eq_dec f f). inversion H1. 
  unfold not in n. assert False. apply n... contradiction.
  apply H2. unfold values. rewrite map_snd_snd_split. rewrite snd_split_comm. apply in_or_app. right.
  right. rewrite (not_in_remove_eq f x0 string_eq_dec H4)...
Qed.

Lemma preservation : forall sto1 e1 sto2 e2,
  lc e1 ->
  step sto1 e1 sto2 e2 ->
  lc e2.
Proof with auto.
intros.
unfold lc in *.
destruct H0. (* step_cases (destruct H0) Case.  *)
Case "step_red".
  apply lc_red in H2... apply lc_plug with (ae := ae0) (e := e)...
  apply lc_active. apply decompose_ae with (e := e) (E := E0)...
Case "step_ref".
  apply lc_plug with (e := e) (ae := exp_ref v)...
Case "step_deref".
  apply lc_plug with (e := e) (ae := exp_deref (exp_loc l))...
Case "step_deref_err".
  apply lc_plug with (e := e) (ae := exp_deref (exp_loc l))...
Case "step_setref".
  apply lc_plug with (e := e) (ae := exp_set (exp_loc l) v)...
Case "step_setref_err".
  apply lc_plug with (e := e) (ae := exp_set (exp_loc l) v)...
Case "step_break".
  trivial.
Qed.

End LC.
