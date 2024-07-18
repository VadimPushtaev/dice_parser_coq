Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.FunctionalExtensionality.

Class Label
    (value_type : Type)
    (cmp : value_type -> value_type -> bool)
    (cmp_refl : forall x : value_type, cmp x x = true)
    (cmp_sym : forall x y : value_type, cmp x y = cmp y x)
    (cmp_trans : forall x y z : value_type, cmp x y = true -> cmp y z = true -> cmp x z = true)
    (comb : value_type -> value_type -> value_type)
    (comb_eq_left : forall x y: value_type, cmp (comb x y) x = true)
    (comb_eq_right : forall x y: value_type, cmp (comb x y) y = true)
  := {
    value : value_type
  }.

Section LabelProofs.

Context
  {value_type : Type}
  {cmp : value_type -> value_type -> bool}
  {cmp_refl : forall x : value_type, cmp x x = true}
  {cmp_sym : forall x y : value_type, cmp x y = cmp y x}
  {cmp_trans : forall x y z : value_type, cmp x y = true -> cmp y z = true -> cmp x z = true}
  {comb : value_type -> value_type -> value_type}
  (comb_eq_left : forall x y: value_type, cmp (comb x y) x = true)
  (comb_eq_right : forall x y: value_type, cmp (comb x y) y = true)
  {L1 : Label value_type cmp cmp_refl cmp_sym cmp_trans comb comb_eq_left comb_eq_right}
  {L2 : Label value_type cmp cmp_refl cmp_sym cmp_trans comb comb_eq_left comb_eq_right}.


(* Define the equivalence relation using cmp *)
Definition label_eqb : bool := cmp L1.(value) L2.(value).

(* Broken after this line ---- *)


(* Define the equivalence relation *)
Definition label_eq (x y : Label value_type) : Prop :=
  cmp x.(value) y.(value) = true.

(* Prove that label_eq is an equivalence relation *)

Instance label_eq_Reflexive : Reflexive label_eq.
Proof.
  unfold Reflexive, label_eq.
  intros x.
  apply cmp_refl.
Qed.

Instance label_eq_Symmetric : Symmetric label_eq.
Proof.
  unfold Symmetric, label_eq.
  intros.
  rewrite cmp_sym.
  apply H.

Qed.

Instance label_eq_Transitive : Transitive label_eq.
Proof.
  unfold Transitive, label_eq.
  intros x y z Hxy Hyz.
  eapply cmp_trans; eauto.
Qed.

Instance label_equiv : Equivalence label_eq :=
  { Equivalence_Reflexive := label_eq_Reflexive
  ; Equivalence_Symmetric := label_eq_Symmetric
  ; Equivalence_Transitive := label_eq_Transitive
  }.

(* Set up the label_eq notation and make it compatible with the rewrite tactic *)
Infix "=" := label_eq : label_scope.

(* Ensure that label_scope is the default scope for equality *)
Delimit Scope label_scope with label.
Bind Scope label_scope with Label.

(* Set up the rewrite rules *)
Instance label_eq_rewrite : Setoid Label :=
  { equiv := label_eq
  ; setoid_equiv := label_equiv
  }.

End LabelProofs.