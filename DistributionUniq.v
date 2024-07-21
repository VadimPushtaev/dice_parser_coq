Require Import Arith.
Require Import QArith.
Require Import QArith.Qabs.
Require Import QArith.QArith_base.
Require Import DiceParser.Distribution.
Require Import DiceParser.NumberUtils.
Require Import DiceParser.Label.

Compute label_eq.

Context
  {value_type : Type}
  {cmp : value_type -> value_type -> bool}
  {cmp_refl : forall x : value_type, cmp x x = true}
  {cmp_sym : forall x y : value_type, cmp x y = cmp y x}
  {cmp_trans : forall x y z : value_type, cmp x y = true -> cmp y z = true -> cmp x z = true}
  {comb : value_type -> value_type -> value_type}
  (comb_eq_left : forall x y: value_type, cmp (comb x y) x = true)
  (comb_eq_right : forall x y: value_type, cmp (comb x y) y = true).

Definition LabelT := Label.LabelT.
Definition DisT := distribution (LT := LabelT).

Fixpoint distribution_has_label
    (d : DisT)
    (l : LabelT)
    : bool :=
  match d with
  | Single label part proof => (label_eqb l label)
  | Multi label part tail => (label_eqb l label) || (distribution_has_label tail l)
  end.

Fixpoint distribution_count_label
    (d : DisT)
    (l : LabelT)
    : nat :=
  match d with
  | Single label part proof => if label_eqb l label then 1 else 0
  | Multi label part tail =>
    (if label_eqb l label then 1 else 0) + (distribution_count_label tail l)
  end.

Fixpoint distribution_modify_label
    (d : DisT)
    (p : Q)
    (l : LabelT)
    : DisT :=
  match d with
  | Single label part proof =>
      if (label_eqb l label)
        then (Single (label_comb l label) ((Qabs part) + (Qabs p)) (sum_abs_ne_0 part p proof))
        else Multi l p (Single label part proof)
  | Multi label part tail =>
      if (label_eqb l label)
        then Multi (label_comb l label) ((Qabs part) + (Qabs p)) tail
        else Multi label part (distribution_modify_label tail p l)
  end.

Fixpoint distribution_uniq
    (d : DisT)
    : distribution :=
  match d with
  | Single label part proof => Single label part proof
  | Multi label part tail => (
      distribution_modify_label
      (distribution_uniq tail)
      part
      label
    )
  end.

Theorem distribution_modify_label_length_lower_bound:
  forall
    (d : DisT)
    (p : Q)
    (l : LabelT),
  (
    (distribution_size d) <=
    (distribution_size (distribution_modify_label d p l))
  )%nat.
Proof.
  intros.
  induction d.
  * simpl.
    destruct (label_eqb l label) eqn:E.
    + simpl. reflexivity.
    + simpl. apply Nat.le_succ_diag_r.
  * simpl.
    destruct (label_eqb l label) eqn:E.
    + simpl. apply le_n_S. reflexivity.
    + simpl. apply le_n_S. apply IHd.
Qed.

Theorem distribution_modify_label_length_upper_bound:
  forall
    (d : DisT)
    (p : Q)
    (l : LabelT),
  (
    (distribution_size (distribution_modify_label d p l)) <=
    (S (distribution_size d))
  )%nat.
Proof.
  intros.
  induction d.
  * simpl.
    destruct (label_eqb l label) eqn:E.
    + simpl. apply Nat.le_succ_diag_r.
    + simpl. reflexivity.
  * simpl.
    destruct (label_eqb l label) eqn:E.
    + simpl. apply le_n_S. apply Nat.le_succ_diag_r.
    + simpl. apply le_n_S. apply IHd.
Qed.

Theorem modify_ignores_head_without_matches:
  forall
    (d1 d2 : DisT)
    (p : Q)
    (l : LabelT),
  (distribution_has_label d1 l) = false ->
  (
    (distribution_modify_label (
      distribution_append (distribution_convert_to_app d1) d2
    ) p l) =
    (distribution_append
      (distribution_convert_to_app d1)
      (distribution_modify_label d2 p l)
    )
  ).
Proof.
  induction d1.
  * simpl.
    intros.
    rewrite H.
    reflexivity.
  * simpl.
    intros.
    apply orb_false_elim in H.
    destruct H as [X Y].
    rewrite X.
    rewrite IHd1. reflexivity.
    apply Y.
Qed.

Theorem modify_uses_head_with_matches:
  forall
    (d1 d2 : DisT)
    (p : Q)
    (l : LabelT),
  (distribution_has_label d1 l) = true ->
  (
    (distribution_modify_label (
      distribution_append (distribution_convert_to_app d1) d2
    ) p l) =
    (distribution_append
      (distribution_convert_to_app (distribution_modify_label d1 p l))
      d2
    )
  ).
Proof.
  induction d1.
  * simpl.
    intros.
    rewrite H.
    reflexivity.
  * intros.
    simpl in H.
    apply orb_prop in H.
    destruct H.
    + simpl.
      rewrite H.
      simpl.
      reflexivity.
    + simpl.
      rewrite IHd1. 2: apply H.
      destruct (label_eqb l label); simpl; reflexivity.
Qed.

Theorem distribution_uniq_length:
  forall
    (d : DisT)
    (l : LabelT),
  (
    (distribution_size (distribution_uniq d)) <=
    (distribution_size d)
  )%nat.
Proof.
  intros.
  induction d.
  * simpl.
    apply Nat.le_refl.
  * simpl.
    apply Nat.le_trans with (m := (S (
      distribution_size
       (distribution_uniq d)
    ))).
    + apply distribution_modify_label_length_upper_bound.
    + apply le_n_S.
      apply IHd.
Qed.

Theorem distribution_has_label_uniq_invariant:
  forall
    (d : DisT)
    (l : LabelT),
  (distribution_has_label d l = true) ->
  (distribution_has_label (
    distribution_uniq d
  ) l = true).
Proof.
Admitted.


Theorem distribution_has_label_vs_count_label:
  forall
    (d : DisT)
    (l : LabelT),
  (distribution_has_label d l = false) <->
  (distribution_count_label d l = O).
Proof.
  split.
  * induction d.
    + intros.
      simpl; simpl in H.
      rewrite H.
      reflexivity.
    + intros.
      simpl; simpl in H.
      apply orb_false_elim in H.
      destruct H as [H1 H2].
      rewrite H1.
      apply IHd.
      apply H2.
  * induction d.
    + intros.
      simpl; simpl in H.
      destruct (label_eqb l label) eqn:E.
      - discriminate H.
      - reflexivity.
    + intros.
      simpl; simpl in H.
      destruct (label_eqb l label) eqn:E.
      - discriminate H.
      - assert (distribution_has_label d l = false) as A.
        apply IHd.
        simpl in H; apply H.
        rewrite A; reflexivity.
Qed.
