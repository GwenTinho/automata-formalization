Definition uniqueChoice := forall A B : Type,
forall R : A -> B -> Prop, (forall a, exists! b, R a b) -> exists f : A -> B, forall a, R a (f a).

Definition subrel{A B} (R' R : A -> B -> Prop) := forall a, forall b, R' a b -> R a b.

Lemma subrel_refl : forall (A B : Type) (R : A -> B -> Prop), subrel R R.
Proof.
  intros A B R a b P.
  assumption.
Qed.

Definition relChoice := forall A B : Type,
forall R : A -> B -> Prop, (forall a, exists b, R a b) -> exists R' : A -> B -> Prop, subrel R' R /\ forall a, exists! b, R' a b.

Definition LEM := forall P, P \/ ~P.

Definition funChoice := forall A B : Type,
forall R : A -> B -> Prop, (forall a, exists b, R a b) -> exists f : A -> B, forall a, R a (f a).

Lemma FC_gives_UC_RC : funChoice -> uniqueChoice /\ relChoice.
Proof.
  intro FC.
  split.
  - intros A B R H.
    apply FC.
    intro.
    destruct (H a) as [b [E U]].
    exists b.
    apply E.
  - intros A B R H.
    apply FC in H.
    destruct H as [f H].
    exists (fun a => fun b => b = (f a) /\ R a b).
    split.
    + intros a b [G T].
      assumption.
    + intro.
      exists (f a).
      split.
      * split.
        {
          reflexivity.
        }
        {
          apply H.
        }
      * intros b [G T].
        rewrite G.
        reflexivity.
Qed.



Definition Goof (P : Prop) (a : bool) (b : bool) :=
match a with
| true =>
  match b with
      | true => True
      | _ => P
  end
| false =>
  match b with
    | false => True
    | _ => P
  end
end.



Theorem Diaconescou : funChoice -> LEM.
Proof.
  intros FC P.
  assert (G := FC bool bool (Goof P)).
  assert (forall a : bool, exists b : bool, Goof P a b).
  - intro.
    destruct a.
    + exists true.
      apply I.
    + exists false.
      apply I.
  - apply G in H.
    destruct H as [f H].
    assert (a : bool).
    apply true.
    assert (M := H a).
    destruct (f a) eqn:F.
    destruct a eqn: A.
    simpl in M.
    assert (L := H false).
    simpl in L.
    destruct (f false) eqn:Q.
    (*LATOR*)



