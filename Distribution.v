Require Import Arith.
Require Import QArith.
Require Import QArith.Qabs.
Require Import QArith.QArith_base.
Require Import List.
Import ListNotations.

Require Import DiceParser.Seq.
Require Import DiceParser.NumberUtils.

Definition LabelBinOp {LT : Type} := LT -> LT -> LT.
Definition LabelByNat {LT : Type} := nat -> LT.

Inductive distribution {LT : Type} : Type :=
  | Single (label : LT) (part : Q) (proof : ~ part == 0)
  | Multi (label : LT) (part : Q) (tail: distribution).

(* The same but without non-zero sum guarantees *)
Inductive distribution_tail {LT : Type} : Type :=
  | SingleT (label : LT) (part : Q)
  | MultiT (label : LT) (part : Q) (tail: distribution_tail).

(* Forget guarantees *)
Fixpoint distribution_to_tail
    {LT : Type} (d : distribution (LT := LT))
    : distribution_tail :=
  match d with
  | Single label part _ => SingleT label part
  | Multi label part tail => MultiT label part (distribution_to_tail tail)
  end.

Fixpoint distributions_concat
    {LT : Type} (a : distribution) (b : distribution_tail (LT := LT))
    : distribution :=
  match b with
  | SingleT label part => Multi label part a
  | MultiT label part tail => Multi label part (distributions_concat a tail)
  end.

Fixpoint _distribution_mult_single
    {LT : Type} (l : LT)
    (q : Q) (prf : ~ q == 0)
    (d : distribution) (comb : LabelBinOp)
    : distribution :=
  match d with
  | Single label part proof =>
      Single (comb l label) (q * part) (mult_ne_0 q part prf proof)
  | Multi label part tail => Multi (comb l label) (q * part) (
      _distribution_mult_single l q prf tail comb
    )
  end.

Fixpoint _distribution_mult_single_tail
    {LT : Type} (l : LT)
    (p : Q)
    (d : distribution)
    (comb : LabelBinOp)
    : distribution_tail :=
  match d with
  | Single label part _ => SingleT (comb l label) (p * part)
  | Multi label part tail => MultiT (comb l label) (p * part) (
      _distribution_mult_single_tail l p tail comb
    )
  end.

Fixpoint distributions_mult
    {LT : Type} (a b : distribution (LT := LT)) (comb : LabelBinOp)
    : distribution :=
  match a with
  | Single label part proof => _distribution_mult_single label part proof b comb
  | Multi label part tail => (
      distributions_concat
      (distributions_mult tail b comb)
      (_distribution_mult_single_tail label part b comb)
    )
  end.

Fixpoint uniform_distribution
    {LT : Type} (size : nat) (mapper : LabelByNat (LT := LT))
    : distribution :=
   match size with
   | O => Single (mapper 1%nat) 1 Q_apart_0_1
   | 1%nat => Single (mapper 1%nat) 1 Q_apart_0_1
   | S x => Multi (mapper size) 1 (uniform_distribution x mapper)
   end.

Fixpoint distribution_size {LT : Type} (d : distribution (LT := LT)) : nat :=
  match d with
  | Single _ _ _ => 1
  | Multi _ _ tail => 1 + (distribution_size tail)
  end.

Fixpoint distribution_parts_sum {LT : Type} (d : distribution (LT := LT)) : Q :=
  match d with
  | Single (_) (part) _ => Qabs part
  | Multi (_) (part) (tail) =>
    Qabs part + (distribution_parts_sum tail)
  end.

Fixpoint _distribution_to_probs {LT : Type} (d : distribution (LT := LT)) (sum : Q) : list Q :=
  match d with
  | Single (_) (part) _ => [Qabs part / sum]
  | Multi (_) (part) (tail) =>
    (Qabs part  / sum) :: (_distribution_to_probs tail sum)
  end.

Definition distribution_to_probs {LT : Type} (d : distribution (LT := LT)) : list Q :=
  _distribution_to_probs d (distribution_parts_sum d).

Fixpoint distribution_to_labels {LT : Type} (d : distribution): list LT :=
  match d with
  | Single (label) (_) _ => [label]
  | Multi (label) (_) (tail) =>
    label :: distribution_to_labels tail
  end.

Definition list_q_sum (lst : list Q) :=
  fold_right Qplus 0 lst.

Lemma list_q_sum_distribution_to_probs__sum_as_a_plus_b:
  forall {LT : Type} (d : distribution) (a b: Q),
  ~ b == 0 ->
    list_q_sum(_distribution_to_probs d (a + b)) ==
    (b / (a + b)) * list_q_sum(_distribution_to_probs (LT := LT) d b).
Proof.
  intros.
  induction d.
  * simpl.
    rewrite Qplus_0_r.
    rewrite Qplus_0_r.
    unfold Qdiv.
    rewrite Qmult_assoc.
    rewrite Q_shuffle_1234_1423.
    rewrite Qmult_inv_r.
    rewrite Qmult_1_l.
    rewrite Qmult_comm.
    reflexivity.
    apply H.
  * simpl.
    rewrite IHd.
    set (list := list_q_sum (_distribution_to_probs d b)).
    rewrite Qmult_plus_distr_r.
    apply Qplus_inj_r.
    unfold Qdiv.
    rewrite Qmult_assoc.
    rewrite Q_shuffle_1234_1423.
    rewrite Qmult_inv_r.
    rewrite Qmult_1_l.
    rewrite Qmult_comm.
    reflexivity.
    apply H.
Qed.

Theorem distribution_parts_sum_gt_0:
  forall {LT : Type} (d : distribution),
  0 < distribution_parts_sum (LT := LT) d.
Proof.
  induction d.
  * simpl.
    apply ge_0_and_ne_0_means_gt_0.
    + apply Qabs_nonneg.
    + unfold "~".
      intros.
      apply Qeq_sym in H.
      apply -> qabs_0 in H.
      apply proof in H.
      apply H.
  * simpl.
    apply zero_lt_sum.
    + apply Qabs_nonneg.
    + apply IHd.
Qed.

(* Broken below *)

Theorem distribution_to_probs_sum_gt_0:
  forall {LT : Type} (d : distribution),
  0 < list_q_sum (distribution_to_probs (LT := LT) d).
Proof.
  induction d.
  * simpl.
    rewrite (Qmult_inv_r (Qabs part)).
    reflexivity.
    unfold "~"; intros.
    apply -> qabs_0 in H.
    apply proof in H.
    apply H.
  * unfold distribution_to_probs.
    simpl.
    rewrite list_q_sum_distribution_to_probs__sum_as_a_plus_b.
    unfold distribution_to_probs in IHd.
    apply zero_lt_sum.
    + apply zero_le_div.
    +++ apply Qabs_nonneg.
    +++ apply zero_lt_sum.
        apply Qabs_nonneg.
        apply distribution_parts_sum_gt_0.
    + apply zero_lt_mult.
    +++ apply zero_lt_div.
        apply distribution_parts_sum_gt_0.
        apply zero_lt_sum.
        apply Qabs_nonneg.
        apply distribution_parts_sum_gt_0.
    +++ apply IHd.
    + apply gt_0_means_not_eq_0.
      apply distribution_parts_sum_gt_0.
Qed.

Theorem distribution_to_probs_sum_eq_1_or_0:
  forall {LT : Type} (d : distribution),
  list_q_sum (distribution_to_probs (LT := LT) d) == 1.
Proof.

  induction d.
  * simpl. rewrite Qplus_0_r.
    apply Qmult_inv_r.
    unfold "~". intros.
    apply -> qabs_0 in H.
    apply proof in H.
    apply H.
  * simpl.
    unfold distribution_to_probs in IHd.
    rewrite list_q_sum_distribution_to_probs__sum_as_a_plus_b.
    rewrite IHd.
    rewrite Qmult_1_r.
    simpl.
    rewrite common_denominator_sum.
    rewrite x_div_x_eq_1.
    + reflexivity.
    + apply gt_0_means_not_eq_0.
      apply zero_lt_sum.
    +++ apply Qabs_nonneg.
    +++ apply distribution_parts_sum_gt_0.
    + apply gt_0_means_not_eq_0.
      apply distribution_parts_sum_gt_0.
Qed.

Theorem distribution_labels_size:
  forall {LT : Type} (d : distribution),
  length (distribution_to_labels d) = distribution_size (LT := LT) d.
Proof.
  intros.
  induction d.
  * simpl. reflexivity.
  * simpl.
    apply eq_S.
    rewrite <- IHd.
    reflexivity.
Qed.

Lemma _distribution_to_probs_length_sum_invariant:
  forall {LT : Type} (d : distribution) (a b : Q),
    length (_distribution_to_probs d (a)) =
    length (_distribution_to_probs (LT := LT) d (b)).
Proof.
  induction d.
  * auto.
  * intros.
    simpl.
    apply eq_S.
    rewrite (IHd a b).
    reflexivity.
Qed.

Theorem distribution_probs_size:
  forall {LT : Type} (d : distribution),
  length (distribution_to_probs d) = distribution_size (LT := LT) d.
Proof.
  induction d.
  * simpl. reflexivity.
  * simpl.
    apply eq_S.
    rewrite <- IHd. clear IHd.
    unfold distribution_to_probs.
    apply _distribution_to_probs_length_sum_invariant.
Qed.

Theorem distribution_labels_and_probs_have_the_same_size:
  forall {LT : Type} (d : distribution),
  length (distribution_to_probs d) = length (distribution_to_labels (LT := LT) d).
Proof.
  intros.
  rewrite distribution_labels_size.
  rewrite distribution_probs_size.
  reflexivity.
Qed.

Lemma distribution_to_labels_uniform_distribution_head:
  forall (n : nat),
    (distribution_to_labels (uniform_distribution (S (S n)) (fun n => n))) =
      ((S (S n)) :: (distribution_to_labels (uniform_distribution (S n) (fun n => n)))).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem uniform_distribution_labels:
  forall (n : nat),
  (distribution_to_labels (uniform_distribution (S n) (fun n => n))) = (make_desc_seq (S n)).
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

Theorem distribution_size_concat_invariant:
  forall {LT : Type} (a b : distribution),
  ((distribution_size a) + (distribution_size b))%nat
    = distribution_size (LT := LT) (distributions_concat a (distribution_to_tail b)).
Proof.
  intros.
  induction b.
  * simpl.
    rewrite Nat.add_1_r.
    reflexivity.
  * simpl.
    rewrite <- IHb.
    rewrite Nat.add_succ_r.
    reflexivity.
Qed.

Theorem distributions_concat_parts_sum:
  forall {LT : Type} (a b : distribution),
  (distribution_parts_sum a) + (distribution_parts_sum b)
    == distribution_parts_sum (LT := LT) (distributions_concat a (distribution_to_tail b)).
Proof.
  intros.
  induction b.
  * simpl.
    rewrite Qplus_comm.
    reflexivity.
  * simpl.
    rewrite <- IHb.
    repeat (rewrite Qplus_assoc).
    apply <- Qplus_inj_r.
    rewrite Qplus_comm.
    reflexivity.
Qed.


Compute (
  distribution_to_probs
  (distributions_mult (Single 7%nat 1 Q_apart_0_1) (uniform_distribution 5 (fun n => n)) (fun x y => x * y)%nat)
).
Compute (
  distribution_to_labels
  (distributions_mult (Single 7%nat 1 Q_apart_0_1) (uniform_distribution 5 (fun n => n)) (fun x y => x * y)%nat)
).

Compute (
  distribution_to_probs
  (distributions_mult (uniform_distribution 3 (fun n => n)) (uniform_distribution 3 (fun n => n)) (fun x y => x * y)%nat)
).
Compute (
  distribution_to_labels
  (distributions_mult (uniform_distribution 3 (fun n => n)) (uniform_distribution 3 (fun n => n)) (fun x y => x * y)%nat)
).


Compute (distribution_to_probs (uniform_distribution 5 (fun n => n))).
Compute (distribution_to_labels (uniform_distribution 5 (fun n => n))).