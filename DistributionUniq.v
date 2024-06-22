Require Import Arith.
Require Import QArith.
Require Import QArith.Qabs.
Require Import QArith.QArith_base.
Require Import DiceParser.Distribution.
Require Import DiceParser.NumberUtils.


Definition LabelBinOpBool {LT : Type} := LT -> LT -> bool.

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


Compute (
  let d := uniform_distribution 5 (fun n => n) in
  distribution_modify_label d (1000#1) 4%nat Nat.eqb (fun a b => a)
).