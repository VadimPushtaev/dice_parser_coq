Require Import Coq.Bool.Bool.


Lemma bool_neq_neg_bool:
  forall (a : bool),
  ~ a = negb a.
Proof.
  destruct a.
  * simpl.
    apply diff_true_false.
  * simpl.
    apply diff_false_true.
Qed.

Lemma bool_eq_contra:
  forall
    (a b c d : bool),
  (a = b -> c = d) ->
    (c = negb d -> a = negb b).
Proof.
  assert (true = true) as T. reflexivity.
  assert (false = false) as F. reflexivity.
  intros.
  destruct a; destruct b; try (
    try (
      apply H in T;
      rewrite T in H0
    );
    try (
      apply H in F;
      rewrite F in H0
    );
    apply bool_neq_neg_bool in H0;
    destruct H0
  );
  try (simpl; reflexivity).
Qed.