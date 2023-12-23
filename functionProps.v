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
    destruct (H y) as [x [K0 K1]].
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

Definition epi{X Y} (f : X -> Y) := forall Z (h g : Y -> Z), f ; g = f ; h -> g = h.

Definition mono{X Y} (f : X -> Y) := forall Z (h g : Z -> X), g ; f = h ; f -> g = h.

Lemma epi_iff_surjective : forall (X Y : Type) (f : X -> Y), epi f <-> surjective f.
Proof.
  intros.
  split.
  intro.
  rewrite surjective_iff_full_image.
  assert (f ; (fun y : Y => Image f Inside y) = f ; (fun y : Y => True)).
  apply functional_extensionality.
  intro.
  unfold composition.
  unfold Inside.
  unfold Image.
  admit. (*disgusting*)
  apply H in H0.
  intro.
  apply equal_f with (x := y) in H0.
  rewrite H0.
  apply I.
  intro.
  intros Z g h K.
  apply functional_extensionality.
  intro.
  rename x into y.
  destruct (H y).
  rewrite <- H0.
  unfold composition in K.
  apply equal_f with x in K.
  assumption.
Admitted.

Lemma mono_iff_injective : forall (X Y : Type) (f : X -> Y), mono f <-> injective f.
Proof.
  intros.
  split.
  - intros M x y H.
    assert (K := M unit (fun _ => x) (fun _ => y)).
    assert ((fun _ : unit => y); f = (fun _ : unit => x); f).
    f_equal.
    apply K.
    apply functional_extensionality.
    intro.
    unfold composition.
    rewrite H.
    reflexivity.
    apply K in H0.
    apply equal_f in H0.
    rewrite H0.
    reflexivity.
    exact tt.
  - intros I Z h g H.
    apply functional_extensionality.
    intro.
    apply I.
    apply equal_f with x in H.
    assumption.
Qed.



(*WANT TO DEFINE FACTORIZATION*)
