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
    unfold bijective.
    intros.
    unfold injective, surjective in H.
    destruct H.
    assert (G := H0 y).
    destruct G.
    exists x.
    unfold unique.
    split.
    assumption.
    intros.
    clear H0.
    assert (G := H x x').
    symmetry in H2.
    rewrite H2 in H1.
    clear H2.
    apply G in H1.
    assumption.
    intro.
    unfold bijective.
    unfold surjective, injective.
    split.
    intros.
    assert (G := H (f y)).
    destruct G.
    unfold unique in H1.
    destruct H1.
    symmetry in H1.
    rewrite H1 in H0.
    assert (G := H2 x).
    rewrite <- H1 in H0.
    apply G in H0.
    clear G.
    assert (G := H2 y).
    assert ( f y = f y).
    reflexivity.
    apply G in H3.
    rewrite H0 in H3.
    assumption.
    intro.
    destruct (H y) as [x].
    exists x.
    unfold unique in H0.
    destruct H0.
    assumption.
Qed.

Definition isomorphism {A B : Type} (f : A -> B) :=
    exists g : B -> A,
    (forall x : A, g (f x) = x) /\ (forall y : B, f (g y) = y).

Lemma bijective_iff_iso : forall (A B : Type) (f : A -> B),
    isomorphism f <-> bijective f.
Proof.
    intros A B.
    split.
    unfold isomorphism.
    split.
    destruct H as [g H].
    destruct H.
    unfold injective.
    intros.
    assert (G := H x).
    rewrite H1 in G.
    rewrite (H y) in G.
    symmetry; assumption.
    unfold surjective.
    intro.
    destruct H as [g H].
    destruct H.
    assert (G := H0 y).
    exists (g y).
    assumption.
    intro.
    assert (G := (proj1 (bijective_iff_unique_existence A B f)) H).
    unfold isomorphism.
    assert (K := unique_choice B A (fun a => fun b => f b = a)).
    cut (forall x : B, exists! y : A, f y = x).
    intros.
    apply K in H0.
    destruct H0 as [g H0].
    exists g.
    split.
    intro.
    clear K.
    destruct (G (f x)) as [x' G'].
    unfold unique in G'.
    destruct G'.
    assert (H3 := H2 (g (f x))).
    rewrite (H0 (f x)) in H3.
    assert (f x = f x).
    reflexivity.
    apply H3 in H4.
    clear G H0.
    assert (N := proj1 H).
    unfold injective in N.
    apply (N x' x) in H1.
    rewrite H1 in H4.
    symmetry.
    assumption.
    intro.
    exact (H0 y).
    intro.
    destruct K.
    assumption.
    exists (x0 x).
    unfold unique.
    split.
    exact (H0 x).
    intros.
    assert (N := proj1 H).
    unfold injective in N.
    apply (N (x0 x) x').
    rewrite H1.
    exact (H0 x).
Qed.

Definition identity (A : Type) (x : A) := x.

Lemma iden_is_iso : forall A : Type, isomorphism (identity A).
Proof.
    intro.
    unfold isomorphism.
    exists (identity A).
    unfold identity.
    auto.
Qed.



Lemma iden_is_bijective : forall A : Type, bijective (identity A).
Proof.
    intro.
    assert (H := proj1 (bijective_iff_iso A A (identity A))).
    apply H.
    exact (iden_is_iso A).
Qed.




















