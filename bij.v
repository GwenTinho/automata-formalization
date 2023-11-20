Require Import Coq.Logic.ClassicalUniqueChoice.

Definition injective {A B : Type} (f : A -> B) :=
    forall x y : A, f x = f y -> x = y.

Definition surjective {A B : Type} (f : A -> B) :=
    forall y : B, exists x : A, f x = y.

Definition bijective {A B : Type} (f : A -> B) :=
    injective f /\ surjective f.

Lemma bijective_iff_unique_existence :
    forall (A B : Type) (f : A -> B), bijective f <-> forall y : B, exists! x : A, f x = y.
Proof.
  intros A B.
  split.
  - intros [Inj Surj] y.
    destruct (Surj y).
    exists x.
    split.
    + assumption.
    + intros.
      apply (Inj x x').
      rewrite H0.
      assumption.
  - intro H.
    split.
    + intros x y P.
      destruct (H (f y)).
      destruct H0 as [H0 H1].
      rewrite <- H0 in P.
      assert (G := H1 x).
      rewrite H0 in P.
      apply G in P.
      clear G.
      assert (G := H1 y).
      assert ( f y = f y).
      * reflexivity.
      * apply G in H2.
        rewrite H2 in P.
        symmetry.
        assumption.
    + intro.
      destruct (H y) as [x].
      exists x.
      destruct H0 as [H0 H1].
      assumption.
Qed.

Definition isomorphism_pair (A B : Type) (f : A -> B) (g : B -> A) := (forall x : A, g (f x) = x) /\ (forall y : B, f (g y) = y).

Definition isomorphism {A B : Type} (f : A -> B) :=
  exists g : B -> A,
  isomorphism_pair A B f g.

Lemma bijective_iff_iso : forall (A B : Type) (f : A -> B),
  isomorphism f <-> bijective f.
Proof.
  intros A B.
  split.
  - split.
    + destruct H as [g [H H0]].
      intros x y P.
      rewrite <- H with x.
      rewrite <- H with y.
      f_equal.
      assumption.
    + intro.
      destruct H as [g [H H0]].
      exists (g y).
      apply H0.
  - intro.
    assert (Bij := H).
    rewrite bijective_iff_unique_existence in H.
    destruct ((unique_choice B A (fun a => fun b => f b = a)) H) as [g FG].
    exists g.
    split.
    + intro.
      destruct (H (f x)) as [x' [F Unique]].
      assert (H0 := Unique (g (f x))).
      rewrite <- H0.
      * destruct Bij.
        apply H1.
        assumption.
      * rewrite FG.
        reflexivity.
    + intro.
      apply FG.
Qed.

Lemma isomorphism_pair_symmetric : forall (A B : Type) (f : A -> B) (g : B -> A),
  isomorphism_pair A B f g <-> isomorphism_pair B A g f.
Proof.
  intros.
  split.
  - intros [H K].
    split.
    + apply K.
    + apply H.
  - intros [H K].
    split.
    + apply K.
    + apply H.
Qed.


Definition identity (A : Type) (x : A) := x.

Lemma iden_is_iso : forall A : Type, isomorphism (identity A).
Proof.
  intro.
  exists (identity A).
  unfold identity.
  unfold isomorphism_pair.
  auto.
Qed.



Lemma iden_is_bijective : forall A : Type, bijective (identity A).
Proof.
  intro.
  assert (H := proj1 (bijective_iff_iso A A (identity A))).
  apply H.
  exact (iden_is_iso A).
Qed.

Lemma bij_as_adjunction : forall (A B : Type) (f : A -> B),
  bijective f <-> exists g : B -> A,
    forall (a : A) (b : B), f a = b <-> a = g b.
Proof.
  intros.
  split.
  - rewrite <- bijective_iff_iso.
    intros [g [C0 C1]].
    exists g.
    intros.
    split.
      + intro.
        rewrite <- H.
        symmetry.
        apply C0.
      + intro.
        rewrite H.
        apply C1.
  - intros [g H].
    split.
    + intros x y K.
      rewrite H in K.
      rewrite K.
      rewrite <- H in K.
      assert (f y = f y).
      {
        reflexivity.
      }
      rewrite H in H0.
      rewrite <- H0.
      reflexivity.
    + intro.
      exists (g y).
      assert (g y = g y).
      {
        reflexivity.
      }
      rewrite <- H in H0.
      assumption.
Qed.





















