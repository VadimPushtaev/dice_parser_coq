Require Import Arith.
Require Import QArith.
Require Import QArith.QArith_base.
Require Import List.
Import ListNotations.

Require Import DiceParser.Seq.

Inductive distribution : Type :=
  | Single (label : nat) (part : positive)
  | Multi (label : nat) (part : Q) (tail: distribution).


Fixpoint uniform_distribution (size : nat) : distribution :=
   match size with
   | O => Single 1 1
   | 1%nat => Single 1 1
   | S x => Multi size 1 (uniform_distribution x)
   end.

Fixpoint distribution_parts_sum (d : distribution) : Q :=
  match d with
  | Single (_) (part) => (Z.pos part)#1
  | Multi (_) (part) (tail) =>
    part + (distribution_parts_sum tail)
  end.

Fixpoint _distribution_to_probs (d : distribution) (sum : Q) : list Q :=
  match d with
  | Single (_) (part) => [((Z.pos part)#1) / sum]
  | Multi (_) (part) (tail) =>
    (part  / sum) :: (_distribution_to_probs tail sum)
  end.

Definition distribution_to_probs (d : distribution) : list Q :=
  _distribution_to_probs d (distribution_parts_sum d).

Compute (distribution_to_probs (uniform_distribution 5)).

Fixpoint distribution_to_labels (d : distribution): list nat :=
  match d with
  | Single (label) (_) => [label]
  | Multi (label) (_) (tail) =>
    label :: distribution_to_labels tail
  end.

Definition list_q_sum (lst : list Q) :=
  fold_right Qplus 0 lst.

Lemma q_sum_mult_1:
  forall (a b c : Q),
  a + b == c -> a + b * 1 == c.
Proof.
  intros.
  assert (b * 1 == b) as A.
    apply Qmult_1_r.
  rewrite A.
  apply H.
Qed.

Lemma q_plus_zero:
  forall (a b : Q),
  b == 0 -> a + b == a.
Proof.
  intros.

  unfold Qeq in H.
  rewrite Zmult_0_l in H.
  rewrite Zmult_1_r  in H.

  unfold Qplus.
  rewrite H.
  rewrite Zplus_0_r .

  unfold Qeq. simpl.
  rewrite <- Zmult_assoc.
  simpl.
  replace (Z.pos (Qden b * Qden a)) with (Z.pos (Qden a * Qden b)).
  reflexivity.
  rewrite Pos.mul_comm.
  reflexivity.
Qed.

Lemma q_minus_plus:
  forall (a b c: Q),
  a == c -> a - b + b == c.
Proof.
  intros.
  unfold Qminus.
  apply Qeq_trans with (y := a + (-b + b)).
  * apply Qeq_sym.
    apply Qplus_assoc with (x := a) (y :=- b) (z := b).
  * rewrite H.
    apply q_plus_zero.
    red; simpl; ring.
Qed.


Theorem distribution_to_probs_sum_eq_q:
  forall d : distribution,
  list_q_sum (distribution_to_probs d) == 1.
Proof.
  induction d.
  * simpl. rewrite Qplus_0_r.
    apply Qmult_inv_r.
    unfold "~". intros.
    unfold "==" in H.
    simpl in H.
    admit.
  * simpl.
    admit.
Admitted.

Theorem distribution_labels_and_probs_have_the_same_size:
  forall d : distribution,
  length (distribution_to_probs d) = length (distribution_to_labels d).
Proof.
  intros.
  induction d.
  * simpl. reflexivity.
  * simpl. apply eq_S.
    admit.
Admitted.

Lemma distribution_to_labels_uniform_distribution_head:
  forall (n : nat),
    (distribution_to_labels (uniform_distribution (S (S n)))) =
      ((S (S n)) :: (distribution_to_labels (uniform_distribution (S n)))).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem uniform_distribution_labels:
  forall (n : nat),
  (distribution_to_labels (uniform_distribution (S n))) = (make_desc_seq (S n)).
Proof.
  intros.
  induction n.
  * simpl.
    reflexivity.
  * rewrite desc_seq_descends.
    rewrite distribution_to_labels_uniform_distribution_head.
    rewrite IHn.
    reflexivity.
Qed.

(*
Compute (
  distribution_to_probs
  (distributions_mult (Single 7) (uniform_distribution 5) (fun x y => x * y)%nat)
).
Compute (
  distribution_to_labels
  (distributions_mult (Single 7) (uniform_distribution 5) (fun x y => x * y)%nat)
).

Compute (
  distribution_to_probs
  (distributions_mult (uniform_distribution 3) (uniform_distribution 3) (fun x y => x * y)%nat)
).
Compute (
  distribution_to_labels
  (distributions_mult (uniform_distribution 3) (uniform_distribution 3) (fun x y => x * y)%nat)
).
*)

Compute (distribution_to_probs (uniform_distribution 5)).
Compute (distribution_to_labels (uniform_distribution 5)).