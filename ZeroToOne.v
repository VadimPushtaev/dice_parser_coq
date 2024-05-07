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