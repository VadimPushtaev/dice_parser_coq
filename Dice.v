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
  | One100
  | Cons (p_tail : ZeroToOne.ZTO) (tail: distribution).



Fixpoint distribution_to_array_under_p (d : distribution) (p : ZeroToOne.ZTO): list Q :=
  match d with
  | One100 => [1]
  | Cons (p_tail) (tail) =>
    (1 - p.(ZeroToOne.q_val)) :: (
      map
      (fun x => x * p.(ZeroToOne.q_val))
      (distribution_to_array_under_p tail p_tail)
    )
  end.

Definition distribution_to_array (d : distribution): list Q :=
  distribution_to_array_under_p d (ZeroToOne.One).

Definition list_q_sum (lst : list Q) :=
  fold_right Qplus 0 lst.

Theorem distribution_sum_eq_q:
  forall d : distribution,
  list_q_sum (distribution_to_array d) == 1.
Proof.
  intros.
  unfold list_q_sum.
  induction d as [|head tail InH].
  * simpl. apply Qplus_0_r.
  * unfold distribution_to_array.
    unfold distribution_to_array in InH.
    admit.
Admitted.


Compute distribution_to_array(
  Cons (ZeroToOne.Half) (
  Cons (ZeroToOne.Half) (
  Cons (ZeroToOne.Half) (
  Cons (ZeroToOne.Half) (
  Cons (ZeroToOne.Half) (
    One100 )))))
).


