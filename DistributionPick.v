Require Import Arith.
Require Import QArith.
Require Import QArith.Qabs.
Require Import QArith.QArith_base.
Require Import List.
Import ListNotations.

Require Import DiceParser.Seq.
Require Import DiceParser.NumberUtils.
Require Import DiceParser.Distribution.
Require Import DiceParser.DistributionUtils.
Require Import DiceParser.Label.


Fixpoint _distribution_pick
    {LT : Type}
    (probs : list Q)
    (labels : list LT)
    (err : LT)
    (random : Q)
    : LT :=
  match probs with
  | [] => err
  | prob :: probs_tail =>
    match labels with
    | [] => err
    | label :: labels_tail =>
      if Qle_bool random prob && negb (Qeq_bool random prob)
        then label
        else _distribution_pick probs_tail labels_tail err (random - prob)
    end
   end.

Definition distribution_pick {LT : Type} (d : distribution) (err : LT) (random : Q) : LT :=
  _distribution_pick
    (distribution_to_probs d)
    (distribution_to_labels d)
    err
    random.


(* Probs, labels, pick! *)
Definition __d := (
  distributions_mult
    (Single 7%nat 1 Q_apart_0_1)
    (uniform_distribution 5 (fun n => n))
    (fun x y => x * y)%nat
).
Definition __probs := (distribution_to_probs __d).
Compute __probs.
Definition __labels := (distribution_to_labels __d).
Compute __labels.
Compute (distribution_pick __d 500%nat (59#100)%Q).