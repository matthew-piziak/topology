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

Theorem exercise_1_2_a_forward: forall A B C : Ensemble U,
    Included U A B /\ Included U A C -> Included U A (Union U B C).
Proof.
  intros.
  destruct H.
  unfold Included.
  intros.
  auto with sets.
Qed.

(* Lemma swap {X} (P: X -> Prop):  (exists x, ~ P x) -> ~ forall x, P x. *)
(* Proof. intros [x HPx] H. apply HPx, H. Qed. *)

(* Theorem exercise_1_2_a_backward: exists A B C : Ensemble U, *)
(*     ~ (Included U A (Union U B C) -> Included U A B /\ Included U A C). *)
(* Proof. *)
(*   unfold not. *)

(* Theorem exercise_1_2_b: forall A B C : Ensemble U, *)
(*     Included U A B \/ Included U A C <-> Included U A (Union U B C). *)
(* Proof. *)
(*   intros. *)
(*   split. *)
(*   - intros. *)
(*     destruct H. *)
(*     * unfold Included. *)
(*       unfold Included in H. *)
(*       intros. *)
(*       apply H in H0. *)
(*       unfold In. *)
(*       left. *)
(*       assumption. *)
(*     * unfold Included. *)
(*       unfold Included in H. *)
(*       intros. *)
(*       apply H in H0. *)
(*       unfold In. *)
(*       right. *)
(*       assumption. *)
(*   - intros. *)


Theorem exercise_1_2_c: forall A B C : Ensemble U,
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


Theorem exercise_1_2_g: forall A B C : Ensemble U,
    Intersection U A (Setminus U B C) = Setminus U (Intersection U A B) (Intersection U A C).
Proof.
  intros.
  apply Extensionality_Ensembles.
  split.
  - unfold Included.
    intros.
    unfold In.
    unfold In in H.
    unfold Setminus.
    split.
    + unfold In.
      inversion H.
      split.
      * assumption.
      * destruct H1.
        assumption.
    + destruct H.
      unfold In in H0.
      unfold Setminus in H0.
      unfold not.
      intros.
      unfold In in H1.
      destruct H1.
      destruct H0.
      contradiction.
  - unfold Included.
    intros.
    unfold In.
    split.
    + unfold In in H.
      unfold Setminus in H.
      destruct H.
      unfold In in H.
      destruct H.
      assumption.
    + unfold In.
      unfold Setminus.
      split.
      * unfold In in H.
        unfold Setminus in H.
        destruct H.
        unfold In in H.
        destruct H.
        assumption.
      * unfold not.
        intros.
        destruct H.
        unfold not in H1.
        apply H1.
        unfold In.
        split.
        unfold In in H.
        destruct H.
        assumption.
        assumption.
Qed.



(* Theorem exercise_1_2_j: forall A B C D : Ensemble U, *)
(*     Included U A C /\ Included U B D ->  *)

(* Theorem exercise 1_3_a: forall (A B A0 B0 : Ensemble U) (F : A -> B), *)
(*     Included U A0 A /\ Included U B0 B -> *)

End Chapter_1.
