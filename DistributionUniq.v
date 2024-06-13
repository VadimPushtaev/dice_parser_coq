Require Import Arith.
Require Import QArith.
Require Import QArith.Qabs.
Require Import QArith.QArith_base.
Require Import DiceParser.Distribution.


Definition LabelBinOpBool {LT : Type} := LT -> LT -> bool.

Fixpoint distribution_uniq
    {LT : Type}
    (d : distribution)
    (cmp : LabelBinOpBool)
    (comb : LabelBinOp)
    : distribution :=
  match d with
  | Single label part => Single label part
  | Multi label part tail => 
    match tail with
    | Single label' part' =>
      if (cmp label label')
      then Single (comb label label') (((Z.pos part')#1) + part)
      else Multi label part (Single label' part')
    | Multi label' part' tail' => Multi label' part' tail'
    end
  end.
