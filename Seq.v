Require Import List.
Import ListNotations.

Fixpoint make_desc_seq (from : nat) : list nat :=
  match from with
  | O => [1]
  | 1 => [1]
  | S n => from :: make_desc_seq n
  end.

Theorem desc_seq_descends:
  forall (n : nat),
  make_desc_seq (S (S n)) = ((S (S n)) :: (make_desc_seq (S n))).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
