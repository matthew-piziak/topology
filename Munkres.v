Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Powerset.
Require Export Coq.Sets.Powerset_facts.
Require Import Setoid.

Section Chapter_1.
  Variable U : Type.
  Variable V : Type.

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

Lemma singleton_1_0:
  ~ Singleton nat 1 0.
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma same_singletons_included:
  Included nat (Singleton nat 0) (Singleton nat 0).
Proof.
  intros.
  auto with sets.
Qed.

Lemma different_singletons_not_included:
  ~ Included nat (Singleton nat 0) (Singleton nat 1).
Proof.
  unfold not.
  intros.
  unfold Included in H.
  specialize (H 0).
  unfold In in H.
  apply singleton_1_0.
  apply H.
  apply In_singleton.
Qed.


Theorem exercise_1_2_a_backward: exists (A B C : Ensemble nat),
    ~ (Included nat A (Union nat B C) -> Included nat A B /\ Included nat A C).
Proof.
  unfold not.
  exists (Singleton nat 0).
  exists (Singleton nat 0).
  exists (Singleton nat 1).
  intros.
  destruct H.
  - auto with sets.
  - now apply different_singletons_not_included in H0.
Qed.

Theorem exercise_1_2_b_forward: forall A B C : Ensemble U,
    Included U A B \/ Included U A C -> Included U A (Union U B C).
Proof.
  intros.
  destruct H.
  - unfold Included.
    unfold Included in H.
    intros.
    unfold In.
    left.
    now apply H in H0.
  - unfold Included; unfold Included in H.
    intros.
    unfold In.
    right.
    now apply H in H0.
Qed.

Theorem exercise_1_2_b_backward: exists (A B C : Ensemble nat),
    ~ Included nat A (Union nat B C) -> Included nat A B \/ Included nat A C.
Proof.
  unfold not.
  exists (Union nat (Singleton nat 0) (Singleton nat 1)).
  exists (Singleton nat 0).
  exists (Singleton nat 1).
  intros.
  destruct H.
  auto with sets.
Qed.

Theorem exercise_1_2_c: forall (A B C : Ensemble U),
    Included U A B /\ Included U A C <-> Included U A (Intersection U B C).
Proof.
  intros.
  split.
  - intros.
    destruct H.
    unfold Included.
    unfold Included in H.
    unfold Included in H0.
    now split; try apply H; try apply H0.
  - intros.
    now split; unfold Included; unfold Included in H; intros; apply H in H0; destruct H0.
Qed.

Lemma empty_intersection:
  ~ (Intersection nat (Singleton nat 0) (Empty_set nat) 0).
Proof.
  unfold not.
  intros.
  destruct H.
  inversion H0.
Qed.

Lemma not_included:
  ~ (Included nat (Singleton nat 0) (Intersection nat (Singleton nat 0) (Empty_set nat))).
Proof.
  unfold not.
  intros.
  unfold Included in H.
  unfold In in H.
  specialize (H 0).
  apply empty_intersection.
  apply H.
  apply Singleton_intro.
  reflexivity.
Qed.

Lemma included_reflexive: forall (A : Ensemble nat) (x : nat),
    Included nat (Singleton nat x) (Singleton nat x).
Proof.
  auto with sets.
Qed.

Theorem exercise_1_2_d_forward: exists (A B C : Ensemble nat),
    ~ (Included nat A B \/ Included nat A C -> Included nat A (Intersection nat B C)).
Proof.
  unfold not.
  exists (Singleton nat 0).
  exists (Singleton nat 0).
  exists (Empty_set nat).
  intros.
  apply not_included.
  apply H.
  left.
  apply included_reflexive.
  apply (Singleton nat 0).
Qed.


(* Theorem exercise_1_2_d_backward: forall (A B C : Ensemble U), *)
(*     Included U A (Intersection U B C) -> Included U A B \/ Included U A C. *)
(* Proof. *)
(*   intros. *)
(*   unfold Included. *)
(*   unfold Included in H. *)
(*   unfold In in H. *)
(*   unfold In. *)

(* Theorem exercise_1_2_e : exists (A B : Ensemble nat), *)
(*     ~ (Setminus nat A (Setminus nat A B) = B). *)
(* Proof. *)
(*   exists (Union nat (Singleton nat 0) (Singleton nat 1)). *)
(*   exists (Union nat (Singleton nat 1) (Singleton nat 2)). *)

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
      now split; try destruct H1.
    + destruct H.
      unfold In in H0.
      unfold Setminus in H0.
      unfold not.
      intros.
      unfold In in H1.
      destruct H1.
      now destruct H0.
  - unfold Included.
    intros.
    unfold In.
    split.
    + unfold In in H.
      unfold Setminus in H.
      destruct H.
      unfold In in H.
      now destruct H.
    + unfold In.
      unfold Setminus.
      split.
      * unfold In in H.
        unfold Setminus in H.
        destruct H.
        unfold In in H.
        now destruct H.
      * unfold not.
        intros.
        destruct H.
        unfold not in H1.
        apply H1.
        unfold In.
        split.
        unfold In in H.
        now destruct H.
        assumption.
Qed.

Definition Cartesian (U V : Type) (A : Ensemble U) (B : Ensemble V) : Ensemble (U * V) :=
  fun x => In _ A (fst x) /\ In _ B (snd x).

Theorem exercise_1_1_2_j A B C D :
    Included U A C /\ Included V B D -> Included (U * V) (Cartesian _ _ A B) (Cartesian _ _ C D).
Proof.
intros [HU HV] [x y] [HA HB].
split.
- now apply HU.
- now apply HV.
Qed.

(* Theorem exercise_1_1_2_k: exists (A B C D: Ensemble nat), *)
(*     ~ (Included (nat * nat) (Cartesian _ _ A B) (Cartesian _ _ C D) *)
(*        -> Included nat A C /\ Included nat B D). *)
(* Proof. *)
(*   unfold not. *)
(*   exists (Singleton nat 0). *)
(*   exists (Empty_set nat). *)
(*   exists (Singleton nat 1). *)
(*   exists (Empty_set nat). *)
(*   intros. *)

End Chapter_1.