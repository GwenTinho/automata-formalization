Require Import Automata.bij.
Require Import Coq.Logic.FunctionalExtensionality.

Definition Inside{X} (x : X) := True.

Definition preImage{A B : Type} (f : A -> B) (s : B -> Prop) (x : A) := s (f x).

Definition Image{A B : Type} (f : A -> B) (s : A -> Prop) (y : B) := exists x, s x /\ f x = y.

Definition fiber{A B : Type} (f : A -> B) (y : B) (x : A) := f x = y.

Lemma surjective_iff_full_image : forall (A B : Type) (f : A -> B),
  surjective f <-> forall y : B, Image f Inside y.
Proof.
  intro.
  split.
  - intros.
    destruct (H y).
    exists x.
    split.
    + apply I.
    + assumption.
  - intros H y.
    destruct (H y) as [x [A B]].
    exists x.
    assumption.
Qed.

Section Composition.

Definition composition{X Y Z : Type} (f : X -> Y) (g : Y -> Z) := fun x => (g (f x)).

Notation "f ; g" := (composition f g) (at level 60).

Lemma comp_assoc : forall (X Y Z K : Type) (f : X -> Y) (g : Y -> Z) (h : Z -> K),
  (f ; g) ; h = f ; (g ; h).
Proof.
  reflexivity.
Qed.

Definition identity (A : Type) := fun x : A => x.

Lemma comp_r_unit : forall (X Y : Type) (f : X -> Y),
  f ; identity Y = f.
Proof.
  reflexivity.
Qed.


Lemma comp_l_unit : forall (X Y : Type) (f : X -> Y),
  identity X; f  = f.
Proof.
  reflexivity.
Qed.

Lemma factorizaation : forall (X Y : Set) (f : X -> Y),
  exists (ImF : Set) (epi : X -> ImF) (mono : ImF -> Y),
    f = epi ; mono /\ surjective epi /\ injective mono.
Proof.
  intros.
  exists {y : Y | Image f Inside y}.
  exists (fun x : X => sig (f x, Inside (f x)) ).

Admitted.

(*WANT TO DEFINE FACTORIZATION*)
