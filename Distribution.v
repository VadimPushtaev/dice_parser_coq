Require Import Arith.
Require Import QArith.
Require Import QArith.QArith_base.
Require Import List.
Import ListNotations.

Require Import DiceParser.ZeroToOne.
Require Import DiceParser.Seq.

Inductive distribution : Type :=
  | Single (label : nat)
  | Multi (label : nat) (p_tail : ZeroToOne.ZTO) (tail: distribution).


Fixpoint uniform_distribution (size : nat) : distribution :=
   match size with
   | O => Single 1
   | 1%nat => Single 1
   | S x => Multi size
            (ZeroToOne.one_minus_zto (ZeroToOne.Fraction_1_div_x (Pos.of_nat size)))
            (uniform_distribution x)
   end.

(* this is broken, need to implement concat first *)
(*Fixpoint distribution_mult_single
    (l1 : nat)
    (d2 : distribution)
    (labels_func : nat -> nat -> nat)
    {struct d2}
    : distribution :=
  match d2 : distribution with
  | Single l2 =>
      Single (labels_func l1 l2)
  | Multi l2 p_tail2 tail2 =>
      Multi (labels_func l1 l2)
        p_tail2 (distribution_mult_single l1 tail2 labels_func)
  end.

Fixpoint distributions_mult
    (d1 d2 : distribution)
    (labels_func : nat -> nat -> nat)
    {struct d1}
    : distribution :=
  match d1, d2 with
  | Single l1, Single l2 =>
      Single (labels_func l1 l2)
  | Single l1, Multi l2 p_tail2 tail2 =>
      distribution_mult_single l1 d2 labels_func
  | Multi l1 p_tail1 tail1, Single l2 =>
      Multi (labels_func l1 l2)
        p_tail1 (distributions_mult tail1 d2 labels_func)
  | Multi l1 p_tail1 tail1, Multi l2 p_tail2 tail2 =>
      Multi (labels_func l1 l2)
          (zto_mult_zto p_tail1 p_tail2)
          (distributions_mult tail1 tail2 labels_func)
  end.*)

Fixpoint list_mult (m : Q) (l : list Q) : list Q :=
  match l with
  | nil => nil
  | cons head tail => head*m :: list_mult m tail
  end.

Lemma list_mult_head:
  forall (l : list Q) (head m: Q),
  (head * m) :: (list_mult m l) = (list_mult m (head::l)).
Proof.
  intros.
  destruct l.
  * simpl. reflexivity.
  * simpl. reflexivity.
Qed.

Lemma length_mult_does_not_change_length:
  forall (l : list Q) (head m: Q),
  (length l) = (length (list_mult m l)).
Proof.
  intros.
  induction l.
  * simpl. reflexivity.
  * simpl. apply eq_S. apply IHl.
Qed.


Fixpoint distribution_to_probs (d : distribution): list Q :=
  match d with
  | Single _ => [1]
  | Multi (_) (p_tail) (tail) =>
    (1 - p_tail.(ZeroToOne.q_val)) :: (
      list_mult
      p_tail.(ZeroToOne.q_val)
      (distribution_to_probs tail)
    )
  end.

Fixpoint distribution_to_labels (d : distribution): list nat :=
  match d with
  | Single label => [label]
  | Multi (label) (_) (tail) =>
    label :: distribution_to_labels tail
  end.

Definition list_q_sum (lst : list Q) :=
  fold_right Qplus 0 lst.

Lemma list_q_sum_with_list_mult:
  forall (l : list Q) (m: Q),
  list_q_sum (list_mult m l) == m * list_q_sum l.
Proof.
  intros.
  induction l.
  * simpl.
    apply Qeq_sym.
    apply Qmult_0_r.
  * simpl.
    rewrite IHl.
    assert ((m * (a + list_q_sum l)) == (m * a + m * list_q_sum l)) as A_disrt.
      apply Qmult_plus_distr_r .
    assert ((m * a) == (a * m)) as A_comm.
      apply Qmult_comm.

    rewrite A_disrt, A_comm.

    reflexivity.
Qed.

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
  intros.
  induction d as [|label head tail InH].
  * simpl. apply Qplus_0_r.
  * simpl.
    rewrite list_q_sum_with_list_mult.
    rewrite InH.
    apply q_sum_mult_1.
    apply q_minus_plus.
    reflexivity.
Qed.

Theorem distribution_labels_and_probs_have_the_same_size:
  forall d : distribution,
  length (distribution_to_probs d) = length (distribution_to_labels d).
Proof.
  intros.
  induction d.
  * simpl. reflexivity.
  * simpl. apply eq_S.
    rewrite <- length_mult_does_not_change_length with
      (m := (q_val p_tail))
      (l := (distribution_to_probs d)).
    apply IHd.
    exact 0. (* discard "Q" as a goal *)
Qed.

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