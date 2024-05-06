Require Import Arith.
Require Import QArith.
Require Import QArith.QArith_base.
Require Import List.
Import ListNotations.

Require Import DiceParser.ZeroToOne. 

Compute ZeroToOne.TT.

Inductive die : Type :=
  | D (sides : nat).


Inductive distribution : Type :=
  | Single (value : nat)
  | Multi (value : nat) (p_tail : ZeroToOne.ZTO) (tail: distribution).

Fixpoint list_mult (m : Q) (l : list Q)  : list Q :=
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
  induction d as [|value head tail InH].
  * simpl. apply Qplus_0_r.
  * simpl.
    rewrite list_q_sum_with_list_mult.
    rewrite InH.
    apply q_sum_mult_1.
    apply q_minus_plus.
    reflexivity.
Qed.
