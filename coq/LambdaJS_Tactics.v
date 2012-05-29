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
Require Import SfLib.
Require Import ListExt.
Require Import Datatypes.
Require LambdaJS_Defs.
Set Implicit Arguments.

Ltac destruct_and_solve' e := destruct e; [idtac | right; intro Neq; inversion Neq; contradiction].
Tactic Notation "solve" "by" "destruction" "1" tactic(t) constr(e) := destruct_and_solve' e; left; t; auto.
Tactic Notation "solve" "by" "destruction" "2" tactic(t) constr(e1) constr(e2) := 
  destruct_and_solve' e1; solve by destruction 1 (t) e2.
Tactic Notation "solve" "by" "destruction" "3" tactic(t) constr(e1) constr(e2) constr (e3) := 
  destruct_and_solve' e1; solve by destruction 2 (t) e2 e3.

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

Tactic Notation "C_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "C_hole"
    | Case_aux c "C_app_1"
    | Case_aux c "C_app_2"
    | Case_aux c "C_succ"
    | Case_aux c "C_not"
    | Case_aux c "C_if"
    | Case_aux c "C_label"
    | Case_aux c "C_break"
    | Case_aux c "C_ref"
    | Case_aux c "C_deref"
    | Case_aux c "C_setref1"
    | Case_aux c "C_setref2"
    | Case_aux c "C_seq"
    | Case_aux c "C_finally"
    | Case_aux c "C_obj"
    | Case_aux c "C_getfield1"
    | Case_aux c "C_getfield2"
    | Case_aux c "C_setfield1"
    | Case_aux c "C_setfield2"
    | Case_aux c "C_setfield3"
    | Case_aux c "C_delfield1"
    | Case_aux c "C_delfield2"
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
