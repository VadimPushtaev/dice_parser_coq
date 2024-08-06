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

Context
  {value_type : Type}
  {cmp : value_type -> value_type -> bool}
  {cmp_refl : forall x : value_type, cmp x x = true}
  {cmp_sym : forall x y : value_type, cmp x y = cmp y x}
  {cmp_trans : forall x y z : value_type, cmp x y = true -> cmp y z = true -> cmp x z = true}
  {comb : value_type -> value_type -> value_type}
  (comb_eq_left : forall x y: value_type, cmp (comb x y) x = true)
  (comb_eq_right : forall x y: value_type, cmp (comb x y) y = true).

(* Type alias for Label *)
Definition LabelT := Label value_type cmp cmp_refl cmp_sym cmp_trans comb comb_eq_left comb_eq_right.

(* Combine helper *)
Definition label_comb (x y : LabelT) : LabelT := 
  {| value := comb x.(value) y.(value) |}.

(* Define the equivalence relation using cmp *)
Definition label_eqb (x y : LabelT) : bool := cmp x.(value) y.(value).

(* Define the equivalence relation *)
Definition label_eq (x y : LabelT) : Prop :=
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
  rewrite (cmp_sym value value).
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

(* Ensure that label_scope is the default scope for equality *)
Delimit Scope label_scope with label.
Bind Scope label_scope with Label.

(* Set up the rewrite rules *)
Instance label_eq_rewrite : Setoid LabelT :=
  { equiv := label_eq
  ; setoid_equiv := label_equiv
  }.

Lemma label_eqb_after_comb_left:
  forall (x y : LabelT),
  label_eqb x (label_comb x y) = true.
Proof.
  intros.
  destruct x.
  destruct y.
  unfold label_comb.
  unfold label_eqb.
  simpl.
  rewrite cmp_sym.
  rewrite comb_eq_left.
  reflexivity.
Qed.