(* 
 * Mechanized LambdaJS
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
From Top Require Import SfLib.
From Top Require Import ListExt.
From Top Require Import Datatypes.
From Top Require LambdaJS_Defs.
Set Implicit Arguments.

Module LC (Import Atom : ATOM) (Import String : STRING).

Module Import Defs := LambdaJS_Defs.Make (Atom) (String).
From Top Require Import LambdaJS_Tactics.

Section Definitions.

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

Hint Constructors ae.

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
  rewrite map_snd_snd_split. auto.
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
  | @lc_bvar k n0 l0 => rec_lc_bvar k n0 l0
  | @lc_abs n0 e0 l0 => rec_lc_abs n0 e0 l0 (lc'_ind' (S n0) e0 l0)
  | @lc_app n0 e1 e2 l0 l1 => rec_lc_app n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | lc_nat n0 x => rec_lc_nat n0 x
  | @lc_succ n0 e0 l0 => rec_lc_succ n0 e0 l0 (lc'_ind' n0 e0 l0)
  | lc_bool n0 b => rec_lc_bool n0 b
  | lc_string n0 s => rec_lc_string n0 s
  | lc_undef n0 => rec_lc_undef n0
  | lc_null n0 => rec_lc_null n0
  | @lc_not n0 e0 l0 => rec_lc_not n0 e0 l0 (lc'_ind' n0 e0 l0)
  | @lc_if n0 e0 e1 e2 l0 l1 l2 =>
      rec_lc_if  n0 e0 e1 e2 l0 (lc'_ind' n0 e0 l0) l1 (lc'_ind' n0 e1 l1) l2 (lc'_ind' n0 e2 l2)
  | lc_err n0 => rec_lc_err n0
  | @lc_label n0 x e0 l0 => rec_lc_label n0 x e0 l0 (lc'_ind' n0 e0 l0)
  | @lc_break n0 x e0 l0 => rec_lc_break n0 x e0 l0 (lc'_ind' n0 e0 l0)
  | lc_loc n0 x => rec_lc_loc n0 x
  | @lc_ref n0 e0 l0 => rec_lc_ref n0 e0 l0 (lc'_ind' n0 e0 l0)
  | @lc_deref n0 e0 l0 => rec_lc_deref n0 e0 l0 (lc'_ind' n0 e0 l0)
  | @lc_set n0 e1 e2 l0 l1 => rec_lc_set n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | @lc_catch n0 e1 e2 l0 l1 =>
      rec_lc_catch n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' (S n0) e2 l1)
  | @lc_throw n0 e0 l0 => rec_lc_throw n0 e0 l0 (lc'_ind' n0 e0 l0)
  | @lc_seq n0 e1 e2 l0 l1 => rec_lc_seq n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | @lc_finally n0 e1 e2 l0 l1 => rec_lc_finally n0 e1 e2 l0 (lc'_ind' n0 e1 l0) l1 (lc'_ind' n0 e2 l1)
  | @lc_obj n0 l0 n1 pf_lc' => rec_lc_obj n0 l0 n1
      ((fix forall_lc_ind T (pf_lc : Forall (lc' n0) T) : Forall (P n0) T :=
        match pf_lc with
          | Forall_nil _ => Forall_nil (P n0)
          | @Forall_cons _ _ t l' isVal rest => 
            @Forall_cons (exp) (P n0) t (l') (lc'_ind' n0 t isVal) (forall_lc_ind l' rest)
        end) (map (@snd string exp) l0) pf_lc')
  | @lc_getfield n0 o f lc_o lc_f  => rec_lc_getfield n0 o (lc'_ind' n0 o lc_o) f (lc'_ind' n0 f lc_f)
  | @lc_setfield n0 o f e lc_o lc_f lc_e => rec_lc_setfield n0 o (lc'_ind' n0 o lc_o) f (lc'_ind' n0 f lc_f) e (lc'_ind' n0 e lc_e)
  | @lc_delfield n0 o f lc_o lc_f => rec_lc_delfield n0 o (lc'_ind' n0 o lc_o) f (lc'_ind' n0 f lc_f)
  end.

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
    | @val_abs x x0 => rec_val_abs x x0
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
          | @Forall_nil _ _ => Forall_nil P
          | @Forall_cons _ _ t l' isVal rest => 
            Forall_cons (A:=exp) (P:=P) (l:=l') t (val_ind' t isVal) (forall_val_ind l' rest)
        end) (map (@snd string exp) x) pf_vals) x0
  end.

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

End Definitions.

Hint Resolve lc_val.
Hint Resolve lc_ascend.

Lemma val_injective : forall e1 e2, e1 = e2 -> (val e1 <-> val e2).
Proof with eauto. intros; subst... tauto. Qed.

Lemma plug_ok : forall e C e',
  E e C e' -> plug e' C = e.
Proof.
intros.
E_cases (induction H) Case; simpl; try (auto || rewrite -> IHE; auto).
Qed.

Ltac destruct_decomp e := match goal with
  |  [ H : exists E : C, exists e' : exp, Defs.E e E e' /\ ae e' |- _ ] =>
     let E := fresh "E" in
     let e' := fresh "e" in
     let HE := fresh "HE" in
     let Hae := fresh "Hae" in
       destruct H as [E [e' [HE Hae]]]
  | _ => fail
end.

Lemma E_lc : forall C e ae,
  lc e ->
  E e C ae ->
  lc ae.
Proof. intros. E_cases (induction H0) Case; try solve [inversion H; eauto | auto].
Case "E_obj".
  apply IHE. 
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

Hint Constructors val' ae.

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
      [ right; exists C_hole; eapply ex_intro; split; (* apply E_hole;  *)
        try solve [apply redex_err_bubble; auto | constructor; auto]
      | subst
      | right; exists C_hole; eapply ex_intro; split; (* apply E_hole;  *)
        match goal with 
        | [ H: exp_break ?x ?v = _ |- _] => try solve [apply redex_break with x v; auto; constructor; auto| constructor; auto]
        end]. 

Lemma decomp : forall e,
  lc e -> val' e \/ 
          (exists C, exists e', E e C e' /\ ae e').
Proof with eauto 7.
intros.
unfold lc in H.
remember 0.
remember H as LC. clear HeqLC.
move H after LC.
lc_cases (induction H) Case; intros; subst; clean_decomp; inversion LC; subst; repeat match goal with
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
end; eauto 7. 
Case "lc_bvar".
  inversion H.
Case "lc_break".
  inversion IH. 
    inversion H0. right. exists C_hole. eapply ex_intro. split. apply E_hole. apply redex_err_bubble... left...
    subst.
    right. eapply ex_intro. eapply ex_intro. split. apply E_hole. eapply redex_break...
    destruct_decomp e. right. exists (C_break x E0). exists e0; auto.
Case "lc_obj".
  clear H2.
  assert (forall x : string * exp, In x l -> decidable (val (snd x))). intros; apply decide_val.
  assert (Split := (take_while l (fun kv => val (snd kv)) H1)).
  inversion Split. 
  SCase "Everything in (exp_obj l) is already a value".
    left. constructor. constructor... unfold values; rewrite map_snd_snd_split. apply forall_snd_comm...
  SCase "Something in (exp_obj l) is not yet a value".
    destruct H2 as [L1 [L2 [[k e] [Hsubst [Hvals' Hexps]]]]]. subst.
    assert (Forall val (values L1)) as Hvals.
      unfold values. rewrite map_snd_snd_split. apply forall_snd_comm. exact Hvals'.
    clear Hvals'.
    assert (lc e) as HLCe.
      inversion LC. subst.
      rewrite Forall_forall in H6. apply H6. unfold values. rewrite map_app. simpl. apply in_app_iff. right. apply in_eq.
    assert (val' e \/ (exists C, exists e', E e C e' /\ ae e')) as He.
      rewrite map_snd_snd_split in H0. rewrite snd_split_comm in H0. simpl in H0. rewrite forall_app in H0.
      destruct H0 as [H0 H0']. rewrite Forall_forall in H0'. apply H0'; auto with datatypes.
    solve_break_err He e'. (* gets us most of the way *)
      (* error *)
      subst. constructor...
      (* value *)
      contradiction.
      (* break *)
      subst. eapply redex_break. apply H2. constructor...
Qed.

Hint Resolve E_lc.
Hint Unfold not.

(* Invert tagof *)
Hint Extern 1 ( False ) => match goal with
  | [ H: tagof _ _ |- False]  => inversion H
end.

Lemma progress : Defs.progress.
Proof with eauto.
unfold Defs.progress.
intros.
remember H as HLC; clear HeqHLC.
apply decomp in H.
destruct H. destruct H...
right. right. exists exp_err. exists sto0. auto.
destruct_decomp e...
right. right.
inversion Hae; subst...
(* redex_cases (inversion H0) Case; subst... *)
Case "redex_app". val_cases (inversion H) SCase; subst; eauto 6.
Case "redex_if". val_cases (inversion H) SCase; subst; first [destruct b; eauto 6 | eauto 6]. 
Case "redex_label_break".
  assert ({ x = y } + { ~ x = y }). apply Atom.atom_eq_dec.
  destruct H0; subst...
Case "redex_ref".
assert (exists l : atom, 
          ~ In l (map (@fst AtomEnv.key stored_val) (AtomEnv.elements sto0))) 
    as [l HnotInL].
  apply Atom.atom_fresh_for_list.
exists (plug (exp_loc l) E0).
exists (AtomEnv.add l (val_with_proof H) sto0)...
Case "redex_deref".
val_cases (inversion H) SCase; subst; try solve [ exists (plug exp_err E0); eauto ].
  SCase "val_loc". remember (AtomEnv.find l sto0) as MaybeV.
  destruct MaybeV...
  destruct s...
Case "redex_set".
val_cases (inversion H) SCase; subst; try solve [ exists (plug exp_err E0); eauto ].
  SCase "val_loc". remember (AtomEnv.find l sto0) as MaybeV.
  destruct MaybeV...
  destruct s.
  exists (plug (exp_loc l) E0).
  exists (AtomEnv.add l (val_with_proof H0) sto0)...
Case "redex_getfield".
  destruct (decide_tagof o TagObj).
  inversion H1. destruct (decide_tagof f TagString). inversion H3. destruct (dec_in (fieldnames l) s). 
    exists (plug (lookup_assoc l s exp_err string_eq_dec) E0); exists sto0. subst; eapply step_red... 
    destruct (dec_in (fieldnames l) __proto__).
      exists (plug (exp_getfield (exp_deref (exp_getfield o (exp_string __proto__))) f) E0); exists sto0. subst; eapply step_red...
      exists (plug exp_undef E0); exists sto0. subst; eapply step_red...
    exists (plug exp_err E0); exists sto0. subst; eapply step_red...
  exists (plug exp_err E0); exists sto0; subst; eapply step_red...
Case "redex_setfield".
  destruct (decide_tagof o TagObj).
  inversion H2. destruct (decide_tagof f TagString). inversion H4. 
    destruct (dec_in (fieldnames l) s).
      exists (plug (exp_obj (update_assoc l s e1 string_eq_dec)) E0); exists sto0. subst; eapply step_red...
      exists (plug (exp_obj ((s,e1)::l)) E0); exists sto0. subst; eapply step_red...
    exists (plug exp_err E0); exists sto0. subst; eapply step_red...
  exists (plug exp_err E0); exists sto0; subst; eapply step_red...
Case "redex_delfield".
  destruct (decide_tagof o TagObj).
  inversion H1. destruct (decide_tagof f TagString). inversion H3.
    destruct (dec_in (fieldnames l) s). 
      exists (plug (exp_obj (remove_fst s l string_eq_dec)) E0); exists sto0. subst; eapply step_red... 
      exists (plug o E0); exists sto0. subst; eapply step_red...
    exists (plug exp_err E0); exists sto0; subst; eapply step_red...
  exists (plug exp_err E0); exists sto0; subst; eapply step_red...
Qed.

Ltac solve_lc_plug := match goal with
  | [ IHE : lc' 0 ?e -> lc' 0 (plug ?e' ?E),
      H : lc' 0 ?e
      |- context [plug ?e' ?E] ]
    => (apply IHE in H; auto)
end.

Lemma lc_plug : forall C ae e e',
  lc e ->
  lc e' ->
  E e C ae ->
  lc (plug e' C).
Proof with auto.
intros.
E_cases (induction H1) Case;
 first [ inversion H; subst; simpl; unfold lc in *; constructor ; try solve_lc_plug; auto | auto ]. 
Case "E_obj".
  SCase "Proving NoDup of fieldnames after plugging".
  unfold fieldnames in *. rewrite map_fst_fst_split. rewrite fst_split_comm. simpl.
  rewrite map_fst_fst_split in H3; rewrite fst_split_comm in H3; simpl in H3...
  SCase "Proving all are values after plugging".
  unfold values in *. rewrite map_snd_snd_split; rewrite snd_split_comm; simpl.
  rewrite map_snd_snd_split in H5; rewrite snd_split_comm in H5; simpl in H5...
  rewrite forall_app. rewrite forall_app in H5. inversion H5. split... inversion H4... 
Qed.

Hint Resolve lc_plug.

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
  SCase "k > n".
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

Lemma preservation : Defs.preservation.
Proof with auto.
unfold Defs.preservation.
intros.
unfold lc in *.
destruct H0. (* step_cases (destruct H0) Case.  *)
Case "step_red".
  apply lc_red in H2... apply lc_plug with (ae := ae0) (e := e)...
  apply E_lc with (C := C0) (e := e)...
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
