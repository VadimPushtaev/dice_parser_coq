Require Import QArith.
Require Import QArith.QArith_base.


Definition is_between_zero_and_one (q : Q) : Prop :=
  0 <= q <= 1.

Lemma zero_is_between_zero_and_one :
  is_between_zero_and_one (0).
Proof.
  unfold is_between_zero_and_one.
  split.
  * (* 0 <= 1 *)
    unfold "<=".
    simpl.
    apply Z.le_refl.
  * (* 1 <= 1 *)
    unfold "<=".
    simpl.
    apply Z.le_0_1.
Qed.

Lemma one_div_x_is_between_zero_and_one (x : positive) :
  is_between_zero_and_one (1#x).
Proof.
  intros.
  unfold is_between_zero_and_one.
  split.
  * (* 0 <= 1/x *)
    unfold "<=".
    simpl.
    apply Z.le_0_1.
  * (* 1/2 <= 1 *)
    unfold "<=".
    simpl.
    induction x.
    + easy.
    + easy.
    + easy.
Qed.

Lemma pos_mult_is_pos :
  forall (x y : Z),
  (0 <= x -> 0 <= y -> 0 <= x * y)%Z.
Proof.
  intros.
  induction x.
  * simpl. reflexivity.
  * induction y; auto.
  * exfalso. auto.
Qed.

Lemma mult_is_between_zero_and_one
  (q1 q2 : Q)
  (proof1 : is_between_zero_and_one (q1))
  (proof2 : is_between_zero_and_one (q2))
  : is_between_zero_and_one (q1 * q2).
Proof.
  unfold is_between_zero_and_one in proof1, proof2.
  destruct proof1 as [P1_0 P1_1].
  destruct proof2 as [P2_0 P2_1].

  unfold "<=" in P1_0, P1_1, P2_0, P2_1.
  simpl in P1_0, P1_1, P2_0, P2_1.
  rewrite Z.mul_1_r in P1_0, P1_1, P2_0, P2_1.

  split.
  * unfold "<=".
    simpl.
    rewrite Z.mul_1_r.
    apply pos_mult_is_pos. apply P1_0. apply P2_0.
  * unfold "<=".
    simpl.
    rewrite Z.mul_1_r.
    rewrite Zpos_mult_morphism.
    induction (Qnum q1).
    + auto.
    + induction (Qnum q2).
      +++ auto.
      +++ admit.
      +++ exfalso. auto.
    + exfalso. auto.
Admitted.

Lemma one_minus_x_is_still_between_zero_and_one (q : Q) (proof : is_between_zero_and_one (q)) :
  is_between_zero_and_one (1 - q).
Proof.
  unfold is_between_zero_and_one in proof.
  destruct proof as [X Y].
  split.
  * apply -> Qle_minus_iff. apply Y.
  * apply <- Qle_minus_iff.
    assert ((q - 1) == (q + (-1))) as A1.
    1: {
      ring.
    }
    assert ((- (1 - q)) == (q - 1)) as A2.
    1: {
      ring.
    }
    assert ((1 + (-1)) == 0) as A3.
    1: {
      rewrite Qplus_opp_r .
      reflexivity.
    }

    rewrite A2.
    rewrite A1.
    rewrite Qplus_assoc.
    rewrite Qplus_comm with (x:=1) (y:=q).
    rewrite <- Qplus_assoc.
    rewrite A3.
    rewrite Qplus_0_r.
    apply X.
Qed.


Record ZTO : Type := {
  q_val : Q;
  q_bound : is_between_zero_and_one(q_val)  (* Proof that 0 <= q_val <= 1 *)
}.

Definition one_minus_zto (zto : ZTO) : ZTO := {|
  q_val := 1 - (q_val zto);
  q_bound := one_minus_x_is_still_between_zero_and_one (q_val zto) (q_bound zto)
|}.

Definition zto_mult_zto (z1 z2 : ZTO) : ZTO := {|
  q_val := (q_val z1) * (q_val z2);
  q_bound := mult_is_between_zero_and_one (q_val z1) (q_val z2) (q_bound z1) (q_bound z2)
|}.

Definition Zero : ZTO := {|
  q_val := 0;
  q_bound := zero_is_between_zero_and_one
|}.

Definition One : ZTO := {|
  q_val := 1;
  q_bound := (one_div_x_is_between_zero_and_one 1)
|}.

Definition Half: ZTO := {|
  q_val := (1#2);
  q_bound := (one_div_x_is_between_zero_and_one 2)
|}.

Definition Fraction_1_div_x (x : positive) := {|
  q_val := (1#x);
  q_bound := (one_div_x_is_between_zero_and_one x)
|}.