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

(*
_distribution_pick (_distribution_to_probs d (Qabs part + distribution_parts_sum d))
      (distribution_to_labels d) err (random - Qabs part / (Qabs part + distribution_parts_sum d))
_distribution_pick (_distribution_to_probs d (distribution_parts_sum d))
        (distribution_to_labels d) err random
*)

Lemma _distribution_pick_probs_plus:
  forall
    (d : DisT)
    (err : LabelT)
    (random : Q)
    (delta : Q),
    _distribution_pick (_distribution_to_probs d ((Qabs delta) + distribution_parts_sum d))
      (distribution_to_labels d) err (random - (Qabs delta) / ((Qabs delta) + distribution_parts_sum d))
    =
    _distribution_pick (_distribution_to_probs d (distribution_parts_sum d))
        (distribution_to_labels d) err random.
Proof.
  induction d.
  * intros.
    simpl.

    rewrite qle_bool_move_subtrahend_right.
    rewrite common_denominator_plus.
    rewrite Qplus_comm.
    rewrite x_div_x_eq_1.

    rewrite qeq_bool_move_subtrahend_right.
    rewrite common_denominator_plus.
    rewrite Qplus_comm.
    rewrite x_div_x_eq_1.
    rewrite x_div_x_eq_1.
    reflexivity.
    
    + unfold "~". intros.
      apply -> qabs_0 in H.
      apply proof in H.
      destruct H.
    + rewrite Qplus_comm.
      apply sum_abs_ne_0.
      apply proof.
    + rewrite Qplus_comm.
      apply sum_abs_ne_0.
      apply proof.
  * intros.
    admit. (* ? *)
Admitted.


Lemma distribution_pick_no_unkown_labels:
  forall
    (d : DisT)
    (err : LabelT)
    (random : Q)
    (result : LabelT),
  result = distribution_pick d err random ->
    (result = err) \/ (true = distribution_has_label d result).
Proof.
  unfold distribution_pick.
  * induction d.
    + intros.
      simpl; intros.
      unfold distribution_pick in H.
      simpl in H.
      destruct (Qle_bool random (Qabs part / Qabs part) && negb (Qeq_bool random (Qabs part / Qabs part))).
      ++ right. rewrite H. rewrite label_eqb_refl. reflexivity.
      ++ left. apply H.
    + simpl; intros.
      destruct (Qle_bool random (Qabs part / (Qabs part + distribution_parts_sum d)) &&
      negb (Qeq_bool random (Qabs part / (Qabs part + distribution_parts_sum d)))) eqn:E.
      ++ right. rewrite H. symmetry.
         rewrite label_eqb_refl.
         rewrite orb_true_l.
         reflexivity.
      ++ unfold distribution_to_probs in IHd.
         admit. (* Need to prove that next step is equal to prev one *)
Admitted.



Theorem distribution_pick_no_error:
  forall
    (d : DisT)
    (err : LabelT)
    (random : Q),
  false = distribution_has_label d err ->
  true = Qle_bool 0 random ->
  true = Qle_bool random 1 ->
  false = Qeq_bool random 1 ->
    err <> distribution_pick d err random.
Proof.
  induction d.
  *
    intros err random NoLabelH H0 H1 H1eq RH.
    simpl in NoLabelH.
    unfold distribution_pick in RH.
    simpl in RH.
    assert ((Qabs part / Qabs part) == 1) as A.
    + rewrite x_div_x_eq_1. reflexivity.
      rewrite qabs_0.
      apply proof.
    + rewrite A in RH.
      rewrite <- H1 in RH.
      rewrite <- H1eq in RH.
      simpl in RH.
      rewrite RH in NoLabelH.
      rewrite label_eqb_refl in NoLabelH.
      discriminate NoLabelH.
  * intros err random NoLabelH H0 H1 H1eq RH.
    simpl in NoLabelH.
    symmetry in NoLabelH.
    apply orb_false_iff in NoLabelH.
    destruct NoLabelH as [NL' NL''].
    symmetry in NL''.

    specialize (IHd err random).
    apply IHd in NL''.
    + rename NL'' into Goal.
      admit.
    + rewrite H0; reflexivity.
    + rewrite H1; reflexivity.
    + rewrite H1eq; reflexivity.

Admitted.


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