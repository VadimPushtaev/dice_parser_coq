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

Theorem distribution_modify_label_length:
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
      distribution_append (distribution_convert_to_app d1) d1
    ) p l cmp comb) =
    (distribution_append
      (distribution_convert_to_app d1) 
      (distribution_modify_label d2 p l cmp comb)
    )
  ).
Proof.
  intros.
  induction d1.
  * simpl.
    destruct (cmp l label) eqn:E.
    + admit. (* cmp l label CANNOT BE == true *)
    + admit.
Admitted.


Compute (
  let d := uniform_distribution 5 (fun n => n) in
  distribution_modify_label d (1000#1) 4%nat Nat.eqb (fun a b => a)
).