Require Import Arith.
Require Import QArith.
Require Import QArith.Qabs.
Require Import QArith.QArith_base.
Require Import QArith.

Lemma ge_0_and_ne_0_means_gt_0:
  forall (a : Q),
  0 <= a -> ~ 0 == a -> 0 < a.
Proof.
  intros.
  apply Qlt_leneq.
  split.
  * apply H.
  * apply H0.
Qed.

Lemma gt_0_means_not_eq_0:
  forall (a : Q),
  a > 0 -> ~ a == 0.
Proof.
  intros.
  unfold "~".
  intros.
  rewrite H0 in H.
  discriminate H.
Qed.

Lemma eq_x_means_le_x:
  forall (a : Q),
  a == 0 -> a <= 0.
Proof.
  intros.
  rewrite H.
  unfold "<=".
  reflexivity.
Qed.

Lemma qabs_0:
  forall (a : Q),
  Qabs a == 0 <-> a == 0.
Proof.
  split.
  * intros H.
    destruct (Qlt_le_dec 0 a) as [Hgt | Hle].
    + (* Case a > 0 *)
      apply Qlt_le_weak in Hgt.
      apply Qabs_pos in Hgt.
      rewrite Hgt in H.
      apply H.
    + (* Case a <= 0 *)
      assert (a <= 0) as Hle_copy. apply Hle.
      apply Qabs_neg in Hle.
      rewrite Hle in H.
      apply eq_x_means_le_x in H.
      apply Qopp_le_compat in H.
      rewrite Qopp_involutive in H.
      unfold Qopp in H.
      simpl in H.
      apply Qle_antisym.
      apply Hle_copy.
      apply H.
  * intros.
    rewrite H.
    reflexivity.
Qed.

Lemma Q_shuffle_1234_1423:
  forall (a b c d : Q),
  a*b*c*d == a*d*b*c.
Proof.
  intros.
  repeat (rewrite <- Qmult_assoc).
  rewrite (Qmult_comm c d).
  rewrite (Qmult_assoc b d c).
  rewrite (Qmult_comm b d).
  rewrite (Qmult_assoc d b c).
  reflexivity.
Qed.

Lemma zero_lt_sum:
  forall (a b : Q),
  0 <= a -> 0 < b -> 0 < a + b.
Proof.
  intros.
  apply Qle_lt_trans with (y := a).
  apply H.
  rewrite <- Qplus_0_l at 1.
  setoid_replace (a + b) with (b + a).
  apply Qplus_lt_le_compat.
  apply H0.
  apply Qle_refl.
  apply Qplus_comm.
Qed.

Lemma zero_le_div:
  forall (a b : Q),
  0 <= a -> 0 < b -> 0 <= a / b.
Proof.
  intros.
  apply Qle_shift_div_l .
  * apply H0.
  * rewrite Qmult_0_l.
    apply H.
Qed.

Lemma zero_lt_div:
  forall (a b : Q),
  0 < a -> 0 < b -> 0 < a / b.
Proof.
  intros.
  apply Qlt_shift_div_l .
  * apply H0.
  * rewrite Qmult_0_l.
    apply H.
Qed.

Lemma zero_lt_mult:
  forall (a b : Q),
  0 < a -> 0 < b -> 0 < a * b.
Proof.
  intros.
  setoid_replace (a*b) with (a/(/b)).
  apply zero_lt_div.
  apply H.
  apply Qlt_shift_inv_l .
  apply H0.
  rewrite Qmult_0_l.
  reflexivity.

  unfold Qdiv.
  rewrite Qinv_involutive.
  reflexivity.
Qed.

Lemma common_denominator_sum:
  forall (a b c : Q),
  a/c + b/c == (a + b)/c.
Proof.
  intros.
  unfold Qdiv.
  rewrite Qmult_plus_distr_l.
  reflexivity.
Qed.

Lemma x_div_x_eq_1:
  forall (x : Q),
  ~ x == 0 -> x/x == 1.
Proof.
  intros.
  unfold Qdiv.
  rewrite Qmult_inv_r.
  reflexivity.
  apply H.
Qed.

Lemma mult_ne_0:
  forall
    (p1 p2 : Q)
    (proof1 : ~ p1 == 0)
    (proof2 : ~ p2 == 0),
  ~ (p1 * p2) == 0.
Proof.
  unfold "~".
  intros.
  apply Qmult_integral in H.
  destruct H.
  * apply proof1 in H.
    contradiction H.
  * apply proof2 in H.
    contradiction H.
Qed.
