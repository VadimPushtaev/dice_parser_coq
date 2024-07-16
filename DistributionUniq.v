Require Import Arith.
Require Import QArith.
Require Import QArith.Qabs.
Require Import QArith.QArith_base.
Require Import DiceParser.Distribution.
Require Import DiceParser.NumberUtils.


Definition LabelBinOpBool {LT : Type} := LT -> LT -> bool.

Fixpoint distribution_has_label
    {LT : Type}
    (d : distribution)
    (l : LT)
    (cmp : LabelBinOpBool)
    : bool :=
  match d with
  | Single label part proof => cmp l label
  | Multi label part tail => (cmp l label) || (distribution_has_label tail l cmp)
  end.

Fixpoint distribution_count_label
    {LT : Type}
    (d : distribution)
    (l : LT)
    (cmp : LabelBinOpBool)
    : nat :=
  match d with
  | Single label part proof => if cmp l label then 1 else 0
  | Multi label part tail =>
    (if cmp l label then 1 else 0) + (distribution_count_label tail l cmp)
  end.

Fixpoint distribution_modify_label
    {LT : Type}
    (d : distribution)
    (p : Q)
    (l : LT)
    (cmp : LabelBinOpBool)
    (comb : LabelBinOp)
    : distribution :=
  match d with
  | Single label part proof =>
      if (cmp l label)
        then (Single (comb l label) ((Qabs part) + (Qabs p)) (sum_abs_ne_0 part p proof))
        else Multi l p (Single label part proof)
  | Multi label part tail =>
      if (cmp l label)
        then Multi (comb l label) ((Qabs part) + (Qabs p)) tail
        else Multi label part (distribution_modify_label tail p l cmp comb)
  end.

Fixpoint distribution_uniq
    {LT : Type}
    (d : distribution)
    (cmp : LabelBinOpBool)
    (comb : LabelBinOp)
    : distribution :=
  match d with
  | Single label part proof => Single label part proof
  | Multi label part tail => (
      distribution_modify_label
      (LT := LT)
      (distribution_uniq tail cmp comb)
      part
      label
      cmp
      comb
    )
  end.

Theorem distribution_modify_label_length_lower_bound:
  forall
    {LT : Type}
    (d : distribution)
    (p : Q)
    (l : LT)
    (cmp : LabelBinOpBool)
    (comb : LabelBinOp),
  (
    (distribution_size d) <=
    (distribution_size (distribution_modify_label d p l cmp comb))
  )%nat.
Proof.
  intros.
  induction d.
  * simpl.
    destruct (cmp l label) eqn:E.
    + simpl. reflexivity.
    + simpl. apply Nat.le_succ_diag_r.
  * simpl.
    destruct (cmp l label) eqn:E.
    + simpl. apply le_n_S. reflexivity.
    + simpl. apply le_n_S. apply IHd.
Qed.

Theorem distribution_modify_label_length_upper_bound:
  forall
    {LT : Type}
    (d : distribution)
    (p : Q)
    (l : LT)
    (cmp : LabelBinOpBool)
    (comb : LabelBinOp),
  (
    (distribution_size (distribution_modify_label d p l cmp comb)) <=
    (S (distribution_size d))
  )%nat.
Proof.
  intros.
  induction d.
  * simpl.
    destruct (cmp l label) eqn:E.
    + simpl. apply Nat.le_succ_diag_r.
    + simpl. reflexivity.
  * simpl.
    destruct (cmp l label) eqn:E.
    + simpl. apply le_n_S. apply Nat.le_succ_diag_r.
    + simpl. apply le_n_S. apply IHd.
Qed.

Theorem modify_ignores_head_without_matches:
  forall
    {LT : Type}
    (d1 d2 : distribution)
    (p : Q)
    (l : LT)
    (cmp : LabelBinOpBool)
    (comb : LabelBinOp),
  (distribution_has_label d1 l cmp) = false ->
  (
    (distribution_modify_label (
      distribution_append (distribution_convert_to_app d1) d2
    ) p l cmp comb) =
    (distribution_append
      (distribution_convert_to_app d1)
      (distribution_modify_label d2 p l cmp comb)
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
    {LT : Type}
    (d1 d2 : distribution)
    (p : Q)
    (l : LT)
    (cmp : LabelBinOpBool)
    (comb : LabelBinOp),
  (distribution_has_label d1 l cmp) = true ->
  (
    (distribution_modify_label (
      distribution_append (distribution_convert_to_app d1) d2
    ) p l cmp comb) =
    (distribution_append
      (distribution_convert_to_app (distribution_modify_label d1 p l cmp comb))
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
      destruct (cmp l label); simpl; reflexivity.
Qed.

Theorem distribution_uniq_length:
  forall
    {LT : Type}
    (d : distribution)
    (l : LT)
    (cmp : LabelBinOpBool)
    (comb : LabelBinOp),
  (
    (distribution_size (distribution_uniq (LT:=LT) d cmp comb)) <=
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
       (distribution_uniq d cmp comb)
    ))).
    + apply distribution_modify_label_length_upper_bound.
    + apply le_n_S.
      apply IHd.
Qed.

Theorem distribution_has_label_uniq_invariant:
  forall
    {LT : Type}
    (d : distribution)
    (l : LT)
    (cmp : LabelBinOpBool)
    (comb : LabelBinOp),
  (distribution_has_label d l cmp = true) ->
  (distribution_has_label (
    distribution_uniq (LT:=LT) d cmp comb
  ) l cmp = true).
Proof.
  (* Doesn't work because of comb *)
  (* Needs to be reworked! *)
Admitted.


Theorem distribution_has_label_vs_count_label:
  forall
    {LT : Type}
    (d : distribution)
    (l : LT)
    (cmp : LabelBinOpBool),
  (distribution_has_label d l cmp = false) <->
  (distribution_count_label d l cmp = O).
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
      destruct (cmp l label) eqn:E.
      - discriminate H.
      - reflexivity.
    + intros.
      simpl; simpl in H.
      destruct (cmp l label) eqn:E.
      - discriminate H.
      - assert (distribution_has_label d l cmp = false) as A.
        apply IHd.
        simpl in H; apply H.
        rewrite A; reflexivity.
Qed.

Compute (
  let d := uniform_distribution 5 (fun n => n) in
  distribution_modify_label d (1000#1) 4%nat Nat.eqb (fun a b => a)
).