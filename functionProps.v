Require Import Automata.bij.

Parameters A B : Type.

Definition Inside{X} (x : X) := True.

Definition preImage (f : A -> B) (s : B -> Prop) (x : A) := s (f x).

Definition Image (f : A -> B) (s : A -> Prop) (y : B) := exists x, s x /\ f x = y.

Definition fiber (f : A -> B) (y : B) (x : A) := f x = y.

Lemma surjective_iff_full_image : forall (f : A -> B),
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

Parameters X Y Z H K: Type.

Definition composition (f : X -> Y) (g : Y -> Z) (x : X) := (g (f x)).

Notation "g . f" := (composition f g) (at level 60).

Lemma comp_assoc : forall (f : X -> Y) (g : Y -> Z) (h : Z -> K),
  (h . g) . f = h . (g . f).
Proof.

(*WANT TO DEFINE FACTORIZATION*)
