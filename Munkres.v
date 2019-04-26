Require Export TopologicalSpaces.
Require Export InteriorsClosures.
From ZornsLemma Require Export EnsemblesSpec.

Section Chapter_1.
  Variable U : Type.

Theorem exercise_1_1_2: forall A B C : Ensemble U,
    Intersection A (Union B C) = (Union (Intersection A B) (Intersection A C)).
Proof.
    intros A B C.
    apply Extensionality_Ensembles.
    split; red; intros x H'.
    elim H'.
    intros x0 H'0 H'1; generalize H'0.
    elim H'1; auto with sets.
    elim H'; intros x0 H'0; elim H'0; auto with sets.
Qed.

Theorem exercise_1_1_1: forall A B C : Ensemble U,
    Union A (Intersection B C) = (Intersection (Union A B) (Union A C)).
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

End Chapter_1.