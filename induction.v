Require Import Nat.

(*want to show strong induction*)

Lemma strong_induction : forall (P : nat -> Prop),
  (forall m, (forall k : nat, k < m -> P k) -> P m) -> forall n, P n.
Proof.
    intros.
    induction n.
    - apply H.
      intros.
      inversion H0.
    - apply H.
      intro.
      induction k.
      intro.
      apply H.
      intros.
      inversion H1.
      intro.
Admitted.
