Parameters X : Set.

Definition relation (X : Set) := X -> X -> Prop.

Inductive close_preorder :   relation X -> X -> X -> Prop :=
| pstep (x y : X) (R : relation X) : R x y -> close_preorder R x y
| prefl (x : X) (R : relation X) : close_preorder R x x
| ptrans (x y z : X) (R : relation X): close_preorder R x y -> close_preorder R y z -> close_preorder R x z
.

Inductive close_equivalence : relation X -> X -> X -> Prop :=
| estep (x y : X) (R : relation X) : R x y -> close_equivalence R x y
| erefl (x : X) (R : relation X) : close_equivalence R x x
| esymm (x y : X) (R : relation X) : close_equivalence R x y -> close_equivalence R y x
| etrans (x y z : X) (R : relation X): close_equivalence R x y -> close_equivalence R y z -> close_equivalence R x z
.

Definition symmetric (R : relation X) := forall x y, R x y -> R y x.
Definition reflexive (R : relation X) := forall x, R x x.
Definition transitive (R : relation X) := forall x y z, R x y -> R y z -> R x z.
Definition preorder (R : relation X) := reflexive R /\ transitive R.
Definition equivalence (R : relation X) := reflexive R /\ symmetric R /\ transitive R.

Lemma close_preorder_correct : forall R : relation X,
    preorder (close_preorder R).
Proof.
    intros.
    split.
    intro.
    apply prefl.
    intros x y z H H'.
    apply ptrans with y; assumption.
Qed.

Lemma close_equivalence_correct : forall R : relation X,
    equivalence (close_equivalence R).
Proof.
    intros.
    split.
    intro.
    apply erefl.
    split.
    intros x y H.
    apply esymm.
    assumption.
    intros x y z H H'.
    apply etrans with y; assumption.
Qed.

Lemma close_preorder_sound : forall R : relation X,
    preorder R -> forall x y, R x y <-> close_preorder R x y.
Proof.
    intros.
    split.
    intro.
    apply pstep.
    assumption.
    intro.
    unfold preorder in H.
    destruct H.
    induction H0.
    assumption.
    apply H.
    apply H1 with y.
    apply IHclose_preorder1; assumption.
    apply IHclose_preorder2; assumption.
Qed.

Lemma close_equivalence_sound : forall R : relation X,
    equivalence R -> forall x y, R x y <-> close_equivalence R x y.
Proof.
    intros.
    split.
    intro.
    - apply estep. assumption.
    -   unfold equivalence in H.
        destruct H as [Refl [Symm Trans]].
        intro.
        induction H.
        + assumption.
        + apply Refl.
        +   apply Symm.
            apply IHclose_equivalence; assumption.
        + apply Trans with y.
            *   apply IHclose_equivalence1; assumption.
            *   apply IHclose_equivalence2; assumption.
Qed.

Definition subrelation (R1 R2 : relation X) := forall x y, R1 x y -> R2 x y.

Notation "R1 <= R2" := (subrelation R1 R2).

Lemma close_equivalence_minimal : forall P R: relation X,
    equivalence R -> P <= R -> close_preorder P <= R.
Proof.
    intros.
    intros x y K.
    unfold equivalence in H.
    destruct H as [Refl [Symm Trans]].
    induction K.
    -   apply H0.
        apply H.
    - apply Refl.
    -   apply Trans with y.
        apply IHK1; assumption.
        apply IHK2; assumption.
Qed.

(*TODO implement lemma for two preorders gives an equiv*)

