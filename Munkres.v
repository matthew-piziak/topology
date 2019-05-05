Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Powerset.
Require Import Setoid.

Section Chapter_1.
  Variable U : Type.

Theorem exercise_1_1_1: forall A B C : Ensemble U,
    Union U A (Intersection U B C) = (Intersection U (Union U A B) (Union U A C)).
Proof.
    intros A B C.
    apply Extensionality_Ensembles.
    split; red; intros x H'.
    elim H'; auto with sets.
    intros x0 H'0; elim H'0; auto with sets.
    elim H'.
    intros x0 H'0; elim H'0; auto with sets.
    intros x1 H'1 H'2; try exact H'2.
    generalize H'1.
    elim H'2; auto with sets.
Qed.

Theorem exercise_1_1_2: forall A B C : Ensemble U,
    Intersection U A (Union U B C) = (Union U (Intersection U A B) (Intersection U A C)).
Proof.
    intros A B C.
    apply Extensionality_Ensembles.
    split; red; intros x H'.
    elim H'.
    intros x0 H'0 H'1; generalize H'0.
    elim H'1; auto with sets.
    elim H'; intros x0 H'0; elim H'0; auto with sets.
Qed.

Theorem exercise_1_2_1: forall A B C : Ensemble U,
    Included U A B /\ Included U A C <-> Included U A (Intersection U B C).
Proof.
  intros.
  split.
  intros.
  destruct H.
  unfold Included.
  unfold Included in H.
  intros x HA.
  unfold In.
  split.
  unfold Included in H0.
  apply H.
  assumption.
  unfold Included in H0.
  apply H0.
  assumption.
  intros.
  split;
  unfold Included;
  unfold Included in H;
  intros x HA;
  destruct (H x HA);
  assumption.
Qed.

End Chapter_1.

Locate "_ * _".