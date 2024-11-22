Require Import Arith.
Require Import QArith.
Require Import QArith.Qabs.
Require Import QArith.QArith_base.
Require Import DiceParser.Distribution.
Require Import DiceParser.DistributionUtils.
Require Import DiceParser.BoolUtils.
Require Import DiceParser.NumberUtils.
Require Import DiceParser.Label.

Compute label_eq.

Context
  {value_type : Type}
  {cmp : value_type -> value_type -> bool}
  {cmp_refl : forall x : value_type, cmp x x = true}
  {cmp_sym : forall x y : value_type, cmp x y = cmp y x}
  {cmp_trans : forall x y z : value_type, cmp x y = true -> cmp y z = true -> cmp x z = true}
  {comb : value_type -> value_type -> value_type}
  (comb_eq_left : forall x y: value_type, cmp (comb x y) x = true).

Fixpoint distribution_count_label
    (d : DisT)
    (l : LabelT)
    : nat :=
  match d with
  | Single label part proof => if label_eqb l label then 1 else 0
  | Multi label part tail =>
    (if label_eqb l label then 1 else 0) + (distribution_count_label tail l)
  end.

Fixpoint distribution_upsert_label
    (d : DisT)
    (p : Q)
    (l : LabelT)
    : DisT :=
  match d with
  | Single label part proof =>
      if (label_eqb l label)
        then (Single (label_comb l label) ((Qabs part) + (Qabs p)) (sum_abs_ne_0 part p proof))
        else Multi l p (Single label part proof)
  | Multi label part tail =>
      if (label_eqb l label)
        then Multi (label_comb l label) ((Qabs part) + (Qabs p)) tail
        else Multi label part (distribution_upsert_label tail p l)
  end.

Fixpoint distribution_uniq
    (d : DisT)
    : distribution :=
  match d with
  | Single label part proof => Single label part proof
  | Multi label part tail => (
      distribution_upsert_label
      (distribution_uniq tail)
      part
      label
    )
  end.

Theorem distribution_upsert_label_length_lower_bound:
  forall
    (d : DisT)
    (p : Q)
    (l : LabelT),
  (
    (distribution_size d) <=
    (distribution_size (distribution_upsert_label d p l))
  )%nat.
Proof.
  intros.
  induction d.
  * simpl.
    destruct (label_eqb l label) eqn:E.
    + simpl. reflexivity.
    + simpl. apply Nat.le_succ_diag_r.
  * simpl.
    destruct (label_eqb l label) eqn:E.
    + simpl. apply le_n_S. reflexivity.
    + simpl. apply le_n_S. apply IHd.
Qed.

Theorem distribution_upsert_label_length_upper_bound:
  forall
    (d : DisT)
    (p : Q)
    (l : LabelT),
  (
    (distribution_size (distribution_upsert_label d p l)) <=
    (S (distribution_size d))
  )%nat.
Proof.
  intros.
  induction d.
  * simpl.
    destruct (label_eqb l label) eqn:E.
    + simpl. apply Nat.le_succ_diag_r.
    + simpl. reflexivity.
  * simpl.
    destruct (label_eqb l label) eqn:E.
    + simpl. apply le_n_S. apply Nat.le_succ_diag_r.
    + simpl. apply le_n_S. apply IHd.
Qed.

Theorem upsert_ignores_head_without_matches:
  forall
    (d1 d2 : DisT)
    (p : Q)
    (l : LabelT),
  (distribution_has_label d1 l) = false ->
  (
    (distribution_upsert_label (
      distribution_append (distribution_convert_to_app d1) d2
    ) p l) =
    (distribution_append
      (distribution_convert_to_app d1)
      (distribution_upsert_label d2 p l)
    )
  ).
Proof.
  induction d1.
  * simpl.
    intros.
    rewrite H.
    reflexivity.
  * simpl.
    intros.
    apply orb_false_elim in H.
    destruct H as [X Y].
    rewrite X.
    rewrite IHd1. reflexivity.
    apply Y.
Qed.

Theorem upsert_uses_head_with_matches:
  forall
    (d1 d2 : DisT)
    (p : Q)
    (l : LabelT),
  (distribution_has_label d1 l) = true ->
  (
    (distribution_upsert_label (
      distribution_append (distribution_convert_to_app d1) d2
    ) p l) =
    (distribution_append
      (distribution_convert_to_app (distribution_upsert_label d1 p l))
      d2
    )
  ).
Proof.
  induction d1.
  * simpl.
    intros.
    rewrite H.
    reflexivity.
  * intros.
    simpl in H.
    apply orb_prop in H.
    destruct H.
    + simpl.
      rewrite H.
      simpl.
      reflexivity.
    + simpl.
      rewrite IHd1. 2: apply H.
      destruct (label_eqb l label); simpl; reflexivity.
Qed.

Theorem upsert_always_adds_label:
  forall
    (d : DisT)
    (l1 l2 : LabelT)
    (p : Q),
  label_eqb l1 l2 = true ->
    (distribution_has_label (distribution_upsert_label d p l1) l2) = true.
Proof.
  induction d.
  * intros.
    simpl.
    destruct (label_eqb l1 label).
    + simpl.
      apply label_eqb_trans with (y := l1).
      +++ rewrite label_eqb_sym.
          apply H.
      +++ apply label_eqb_after_comb_left.
          apply label_eqb_refl.
    + simpl.
      rewrite label_eqb_sym.
      rewrite H.
      rewrite orb_true_l.
      reflexivity.
  * intros.
    simpl.
    destruct (label_eqb l1 label) eqn:E.
    + simpl.
      apply orb_true_iff; left.
      apply label_eqb_trans with (y := l1).
      - rewrite label_eqb_sym.
        exact H.
      - apply label_eqb_after_comb_left.
        apply label_eqb_refl.
    + simpl.
      apply orb_true_iff; right.
      apply IHd.
      apply H.
Qed.

Theorem upsert_only_adds_provided_label_f:
  forall
    (d : DisT)
    (l1 l2 : LabelT)
    (p : Q),
  label_eqb l1 l2 = false ->
    distribution_has_label d l2 = false ->
    (distribution_has_label (distribution_upsert_label d p l1) l2) = false.
Proof.
  induction d.
  * intros.
    simpl.
    destruct (label_eqb l1 label) eqn:E.
    + simpl; simpl in H0.
      apply label_not_eqb_after_comb.
      +++ rewrite label_eqb_sym.
          apply H.
      +++ apply H0.
    + simpl; simpl in H0.
      apply orb_false_iff; split.
      +++ rewrite label_eqb_sym.
          apply H.
      +++ apply H0.
  * intros.
    simpl.
    destruct (label_eqb l1 label) eqn:E.
    + simpl; simpl in H0.
      apply orb_false_iff in H0; destruct H0.
      apply orb_false_iff; split.
      +++ apply label_not_eqb_after_comb.
        - rewrite label_eqb_sym.
          apply H.
        - apply H0.
      +++ apply H1.
    + simpl.
      simpl in H0; apply orb_false_iff in H0; destruct H0.
      apply orb_false_iff; split.
      +++ apply H0.
      +++ apply IHd.
        - apply H.
        - apply H1.
Qed.

Theorem upsert_only_adds_provided_label_t:
  forall
    (d : DisT)
    (l1 l2 : LabelT)
    (p : Q),
  label_eqb l1 l2 = false ->
    (distribution_has_label (distribution_upsert_label d p l1) l2) = true ->
    distribution_has_label d l2 = true.
Proof.
  intros d l1 l2 p H.
  replace true with (negb false).
  apply bool_eq_contra.
  * apply upsert_only_adds_provided_label_f.
    apply H.
  * simpl. reflexivity.
Qed.

Theorem upsert_never_removes_label_t:
  forall
    (d : DisT)
    (l1 l2 : LabelT)
    (p : Q),
  (distribution_has_label d l1) = true ->
    (distribution_has_label (distribution_upsert_label d p l2) l1) = true.
Proof.
  induction d.
  * intros.
    simpl.
    destruct (label_eqb l2 label) eqn:E.
    + simpl.
      simpl in H.
      apply label_eqb_trans with (y := l2).
      +++ apply label_eqb_trans with (y := label).
          apply H.
          rewrite label_eqb_sym.
          apply E.
      +++ apply label_eqb_after_comb_left.
          apply label_eqb_refl.
    + simpl.
      simpl in H.
      apply orb_true_iff; right.
      apply H.
  * intros.
    simpl.
    destruct (label_eqb l2 label) eqn:E.
    + simpl.
      simpl in H.
      apply orb_true_iff in H.
      destruct H.
      +++ apply orb_true_iff; left.
          apply label_eqb_trans with (y := l2).
          apply label_eqb_trans with (y := label).
          apply H.
          rewrite label_eqb_sym; apply E.
          apply label_eqb_after_comb_left.
          apply label_eqb_refl.
      +++ apply orb_true_iff; right.
          apply H.
    + simpl.
      simpl in H.
      apply orb_true_iff in H; destruct H.
      +++ apply orb_true_iff; left.
          apply H.
      +++ apply orb_true_iff; right.
          apply (IHd l1 l2 p) in H.
          apply H.
Qed.

Theorem upsert_never_removes_label_f:
  forall
    (d : DisT)
    (l1 l2 : LabelT)
    (p : Q),
  (distribution_has_label (distribution_upsert_label d p l2) l1) = false ->
    (distribution_has_label d l1) = false.
Proof.
  intros d l1 l2 p.
  replace false with (negb true).
  apply bool_eq_contra.
  * apply upsert_never_removes_label_t.
  * simpl. reflexivity.
Qed.

Theorem distribution_uniq_length:
  forall
    (d : DisT)
    (l : LabelT),
  (
    (distribution_size (distribution_uniq d)) <=
    (distribution_size d)
  )%nat.
Proof.
  intros.
  induction d.
  * simpl.
    apply Nat.le_refl.
  * simpl.
    apply Nat.le_trans with (m := (S (
      distribution_size
       (distribution_uniq d)
    ))).
    + apply distribution_upsert_label_length_upper_bound.
    + apply le_n_S.
      apply IHd.
Qed.

Theorem distribution_has_label_uniq_invariant:
  forall
    (d : DisT)
    (l : LabelT),
  (distribution_has_label d l = true) <->
  (distribution_has_label (
    distribution_uniq d
  ) l = true).
Proof.
  intros.
  split.
  ---
    induction d.
    * intros.
      simpl.
      simpl in H.
      apply H.
    * intros.
      simpl in H.
      apply orb_prop in H.
      destruct H.
      + simpl.
        rewrite upsert_always_adds_label; try reflexivity.
        rewrite label_eqb_sym.
        apply H.
      + apply IHd in H.
        simpl.
        apply upsert_never_removes_label_t.
        apply H.
  ---
    induction d.
    * intros.
      simpl.
      simpl in H.
      apply H.
    * intros.
      simpl.
      simpl in H.
      apply orb_true_iff.
      destruct (label_eqb l label) eqn:E.
      + left; reflexivity.
      + right.
        apply upsert_only_adds_provided_label_t in H.
        apply IHd in H.
        apply H.
        rewrite label_eqb_sym.
        apply E.
Qed.

Theorem distribution_no_label_uniq_invariant:
  forall
    (d : DisT)
    (l : LabelT),
  (distribution_has_label d l = false) <->
  (distribution_has_label (
    distribution_uniq d
  ) l = false).
Proof.
  intros.
  split.
  ---
    induction d.
    * intros.
      simpl.
      simpl in H.
      apply H.
    * intros.
      simpl.
      simpl in H.
      apply orb_false_iff in H.
      destruct H as [A B].
      apply upsert_only_adds_provided_label_f.
      + rewrite label_eqb_sym.
        apply A.
      + apply IHd.
        apply B.
  ---
    induction d.
    * intros.
      simpl.
      simpl in H.
      apply H.
    * intros.
      simpl.
      simpl in H.
      apply orb_false_iff.
      split.
      + destruct (label_eqb l label) eqn:E.
        +++ rewrite label_eqb_sym in E.
            apply upsert_always_adds_label with
              (d := (distribution_uniq d)) (p := part) in E.
            rewrite H in E.
            discriminate E.
        +++ reflexivity.
      + apply upsert_never_removes_label_f in H.
        apply IHd in H.
        apply H.
Qed.

(*
  All about
  distribution_count_label
*)

Theorem distribution_count_label__has_no_label:
  forall
    (d : DisT)
    (l : LabelT),
  (distribution_has_label d l = false) <->
  (distribution_count_label d l = O).
Proof.
  split.
  * induction d.
    + intros.
      simpl; simpl in H.
      rewrite H.
      reflexivity.
    + intros.
      simpl; simpl in H.
      apply orb_false_elim in H.
      destruct H as [H1 H2].
      rewrite H1.
      apply IHd.
      apply H2.
  * induction d.
    + intros.
      simpl; simpl in H.
      destruct (label_eqb l label) eqn:E.
      - discriminate H.
      - reflexivity.
    + intros.
      simpl; simpl in H.
      destruct (label_eqb l label) eqn:E.
      - discriminate H.
      - assert (distribution_has_label d l = false) as A.
        apply IHd.
        simpl in H; apply H.
        rewrite A; reflexivity.
Qed.

Theorem distribution_count_label__has_label:
  forall
    (d : DisT)
    (l : LabelT),
  (distribution_has_label d l = true) <->
  (distribution_count_label d l > O)%nat.
Proof.
  split.
  * intros.
    destruct (distribution_count_label d l) eqn:E.
    + apply <- distribution_count_label__has_no_label in E.
      rewrite E in H.
      discriminate H.
    + apply Arith_prebase.gt_Sn_O_stt.
  * intros.
    destruct (distribution_has_label d l) eqn:E.
    + reflexivity.
    + apply distribution_count_label__has_no_label in E.
      rewrite E in H.
      apply Arith_prebase.gt_irrefl_stt in H.
      destruct H.
Qed.

Theorem distribution_count_label__upsert_invariant:
  forall
    (d : DisT)
    (part : Q)
    (find_label upsert_label l2 : LabelT),
  label_eqb find_label upsert_label = false ->
    distribution_count_label d find_label =
      distribution_count_label (distribution_upsert_label d part upsert_label) find_label.
Proof.
  induction d.
  * intros.
    simpl.
    destruct (label_eqb find_label label) eqn:L.
    + pose proof (L) as L'.
      rewrite label_eqb_sym in L.
      apply label_eqb_trans_false with (z := upsert_label) in L.
      rewrite label_eqb_sym in L.
      rewrite L.
      simpl.
      rewrite H.
      rewrite L'.
      auto.
      apply H.
    + destruct (label_eqb upsert_label label) eqn:L2.
      - simpl.
        rewrite label_not_eqb_after_comb.
        reflexivity.
        apply H.
        apply L.
      - simpl.
        rewrite H, L.
        auto.
  * intros.
    simpl.
    destruct (label_eqb find_label label) eqn:L.
    + pose proof (L) as L'.
      rewrite label_eqb_sym in L.
      apply label_eqb_trans_false with (z := upsert_label) in L.
      rewrite label_eqb_sym in L.
      rewrite L.
      simpl.
      rewrite L'.
      simpl.
      apply eq_S.
      apply IHd.
      auto. auto. auto.
    + simpl.
      destruct (label_eqb upsert_label label) eqn:L2.
      - simpl.
        rewrite label_not_eqb_after_comb.
        auto. auto. auto.
      - simpl.
        rewrite L.
        simpl.
        apply IHd.
        auto. auto.
Qed.

(*
Theorem distribution_uniq_count_label__has_label:
  forall
    (d : DisT)
    (l : LabelT),
  (distribution_has_label (distribution_uniq d) l = true) <->
  (distribution_count_label (distribution_uniq d) l = 1)%nat.
Proof.
  split.
  * induction d.
    + intros.
      simpl; simpl in H.
      rewrite H.
      reflexivity.
    + intros.
      simpl.
      simpl in H.
      destruct (label_eqb label l) eqn:E.
      +++ admit.
      +++ apply upsert_only_adds_provided_label_t
            with (d := (distribution_uniq d)) (p := part) in E.
          - apply IHd in E.
            simpl in E.
*)