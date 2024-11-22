Require Import DiceParser.Distribution.
Require Import DiceParser.Label.


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
