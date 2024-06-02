Require Import Arith.
Require Import QArith.
Require Import QArith.Qabs.
Require Import QArith.QArith_base.

Lemma gt_0_means_not_eq_0:
  forall (a : Q),
  a > 0 -> ~ a == 0.
Proof.
Admitted.

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