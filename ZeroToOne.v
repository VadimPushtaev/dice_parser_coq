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

Lemma one_is_between_zero_and_one :
  is_between_zero_and_one (1).
Proof.
  unfold is_between_zero_and_one.
  split.
  * (* 0 <= 1 *)
    unfold "<=".
    simpl.
    apply Z.le_0_1.
  * (* 1 <= 1 *)
    unfold "<=".
    simpl.
    apply Z.le_refl.
Qed.

Lemma half_is_between_zero_and_one :
  is_between_zero_and_one (1#2).
Proof.
  unfold is_between_zero_and_one.
  split.
  * (* 0 <= 1/2 *)
    unfold "<=".
    simpl.
    apply Z.le_0_1.
  * (* 1/2 <= 1 *)
    unfold "<=".
    simpl.
    apply Z.le_succ_diag_r.
Qed.

Record ZTO : Type := {
  q_val : Q;
  q_bound : is_between_zero_and_one(q_val)  (* Proof that 0 <= q_val <= 1 *)
}.


Definition Zero : ZTO := {|
  q_val := 0;
  q_bound := zero_is_between_zero_and_one
|}.

Definition One : ZTO := {|
  q_val := 1;
  q_bound := one_is_between_zero_and_one
|}.

Definition Half: ZTO:=  {|
  q_val := (1#2);
  q_bound := half_is_between_zero_and_one
|}.

