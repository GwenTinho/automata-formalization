Parameters A B C : Set.

Axiom extensionality : forall (X Y : Set) (f g : X -> Y),
    (forall x : X, f x = g x) -> f = g.

Definition curry (f : A * B -> C) := fun x : A => fun y : B => f (x,y).

Definition uncurry (f : A -> B -> C) := fun p => f (fst p) (snd p).

Lemma curry_uncurry : forall (x : A) (y : B) (f : A -> B -> C), (curry (uncurry f)) x y = f x y.
Proof.
    intros.
    unfold curry, uncurry.
    simpl.
    reflexivity.
Qed.

Lemma uncurry_curry : forall (a : A) (b : B) (f : A * B -> C), (uncurry (curry f)) (a,b) = f (a,b).
Proof.
    intros.
    unfold curry, uncurry.
    reflexivity.
Qed.

Definition isomorphic (X Y : Set) :=
    exists (f : X -> Y) (g : Y -> X),
    (forall x, g (f x) = x) /\
    (forall y, f (g y) = y).


Theorem problem : isomorphic (A * B -> C) (A -> B -> C).
Proof.
    unfold isomorphic.
    exists curry.
    exists uncurry.
    split.
    intros.
    apply extensionality.
    intros [a b].
    apply uncurry_curry.
    intro.
    apply extensionality.
    intro.
    apply extensionality.
    intro.
    apply curry_uncurry.
Qed.

Theorem fobenius2 : forall (A : Set) (p : A -> Prop) (q : Prop),
    (exists x : A, q /\ p x) <-> (q /\ (exists x : A, p x)).
Proof.
    firstorder.
Qed.

Theorem fobenius : forall (A : Set) (p : A -> Prop) (q : Prop),
    (exists x : A, q /\ p x) <-> (q /\ (exists x : A, p x)).
Proof.
    intros.
    split.
    intros.
    destruct H.
    destruct H.
    split.
    assumption.
    exists x.
    assumption.
    intros.
    destruct H.
    destruct H0.
    exists x.
    split.
    assumption.
    assumption.
Qed.

Definition lem := forall p, p \/ ~p.

Definition dual_frobenius := forall (A : Type) (p : A -> Prop) (q : Prop),
    (forall x : A, q \/ p x) <-> (q \/ (forall x : A, p x)).

Theorem lem_to_dual_frobenius : lem -> dual_frobenius.
Proof.
    unfold lem, dual_frobenius.
    firstorder.
    destruct (H q).
    left; assumption.
    right.
    intro.
    destruct (H0 x).
    elim H1.
    assumption.
    assumption.
Qed.

Theorem lem_to_dual_frobenius_better : lem -> dual_frobenius.
Proof.
    unfold lem, dual_frobenius.
    firstorder.
    destruct (H q); firstorder.
Qed.

(*idea use the type with 1 element if p otherwise empty*)
Theorem dual_frobenius_to_lem : dual_frobenius -> lem.
Proof.
    unfold lem, dual_frobenius.
    intros.
    destruct (H {_ : unit | p} (fun _ => False) p).
    firstorder.
    assert (H0 := H0 tt).
    simpl in H0.
    assert (H2 := H2 tt).
    simpl in H2.
    firstorder.
Qed.




Theorem dual_frobenius_to_lem_2 : dual_frobenius -> lem.
Proof.
    unfold lem, dual_frobenius.
    intros.
    (*
    clear H1.
    rename H0 into G.
    *)
    destruct (H {_ : unit | p} (fun _ => False) p) as [G _].
    (*add an intermediate proof step*)
    cut (p \/ ({_ : unit | p} -> False)).
    intros [K1 | K2].
    left; assumption.
    right.
    intro.
    apply K2.
    (*idea think of set notation as exists*)
    exists tt.
    assumption.
    apply G.
    intros [u J].
    left.
    assumption.
Qed.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Fixpoint plus (n m : nat) : nat :=
match n with
| O => m
| S p => S (plus p m)
end.

Notation "a + b" := (plus a b).

Lemma zero_iden_l : forall m : nat, O + m = m.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.


Lemma zero_iden_r : forall m : nat, m + O = m.
Proof.
    intros.
    induction m.
    simpl.
    reflexivity.
    simpl.
    rewrite IHm.
    reflexivity.
Qed.


Lemma succ_add_l : forall n m : nat, S n + m = S (n + m).
Proof.
    intros.
    simpl.
    reflexivity.
Qed.


Lemma succ_add_r : forall n m : nat, n + S m = S (n + m).
Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma assoc_plus : forall x y z : nat, x + (y + z) = (x + y) + z.
Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    rewrite succ_add_l.
    rewrite IHx.
    simpl.
    reflexivity.
Qed.

Lemma commutes_plus : forall x y : nat, x + y = y + x.
Proof.
    intros.
    induction x.
    simpl.
    rewrite zero_iden_r.
    reflexivity.
    simpl.
    rewrite IHx.
    rewrite succ_add_r.
    reflexivity.
Qed.

Fixpoint mult (n m : nat) : nat :=
match n with
| O => O
| S p => m + mult p m
end.

Notation "a * b" := (mult a b).

Lemma zero_annil_l : forall n : nat, O * n = O.
Proof.
    intros.
    simpl.
    reflexivity.
Qed.

Lemma zero_annil_r : forall n : nat, n * O = O.
Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma succ_times_l : forall n m : nat, (S n) * m = n * m + m.
Proof.
    intros.
    simpl.
    rewrite commutes_plus.
    reflexivity.
Qed.

Lemma succ_times_r : forall n m : nat, n * (S m) = n + n * m.
Proof.
    intros.
    induction n.
    simpl.
    reflexivity.
    simpl.
    rewrite IHn.
    repeat rewrite assoc_plus.
    replace (n + m) with (m + n).
    reflexivity.
    rewrite commutes_plus.
    reflexivity.
Qed.

Lemma distributes_l : forall x y z : nat, x * (y + z) = x * y + x * z.
Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    simpl.
    rewrite IHx.
    repeat rewrite assoc_plus.
    replace (y + x * y + z) with (y + z + x * y).
    reflexivity.
    symmetry.
    rewrite commutes_plus.
    rewrite assoc_plus.
    replace (y + z) with (z + y).
    reflexivity.
    rewrite commutes_plus.
    reflexivity.
Qed.

Lemma commutes_mult : forall x y : nat, x * y = y * x.
Proof.
    intros.
    induction x.
    simpl.
    rewrite zero_annil_r.
    reflexivity.
    simpl.
    rewrite IHx.
    rewrite succ_times_r.
    reflexivity.
Qed.

Lemma distributes_r : forall x y z : nat, (y + z) * x = y * x+ z * x.
Proof.
    intros.
    rewrite commutes_mult.
    rewrite distributes_l.
    rewrite commutes_mult.
    replace (z * x) with (x * z).
    reflexivity.
    rewrite commutes_mult.
    reflexivity.
Qed.


Lemma assoc_mult : forall x y z : nat, x * (y * z) = (x * y) * z.
Proof.
    intros.
    induction x.
    simpl.
    reflexivity.
    simpl.
    rewrite IHx.
    symmetry.
    rewrite commutes_plus.
    rewrite distributes_r.
    rewrite commutes_plus.
    reflexivity.
Qed.


Definition le (n m : nat) := exists p, n + p = m.

Lemma le_refl : forall n, le n n.
Proof.
    intros.
    induction n.
    unfold le.
    exists O.
    simpl.
    reflexivity.
    destruct IHn as [p IHn'].
    unfold le.
    exists O.
    rewrite zero_iden_r.
    reflexivity.
Qed.



Lemma le_trans : forall n m p, le n m -> le m p -> le n p.
Proof.
    intros.
    destruct H as [k H].
    destruct H0 as [k0 H0].
    unfold le.
    exists (k + k0).
    rewrite assoc_plus.
    rewrite H.
    rewrite H0.
    reflexivity.
Qed.

Lemma injective_succ : forall x y : nat, S x = S y -> x = y.
Proof.
    intros.
    injection H as Hnm.
    apply Hnm.
Qed.

Lemma injectivity_sum : forall n m k : nat, n + m = n + k -> m = k.
Proof.
    intros.
    induction n.
    simpl in H.
    apply H.
    repeat rewrite succ_add_l in H.
    apply injective_succ in H.
    apply IHn in H.
    apply H.
Qed.

Lemma injectivity_zero : forall n m : nat, n + m = n -> m = O.
Proof.
    intros.
    induction n.
    simpl in H; apply H.
    rewrite succ_add_l in H.
    apply injective_succ in H.
    apply IHn in H.
    apply H.
Qed.

Lemma trans : forall p q r : Prop, (p -> q) -> (q -> r) -> (p -> r).
Proof.
    intros.
    apply H0.
    apply H.
    assumption.
Qed.


Lemma contrapositive : forall n m , (n -> m) -> ((~m) -> (~ n)).
Proof.
    intros.
    unfold not.
    intros.
    apply H0.
    apply H.
    assumption.
Qed.

Lemma negation_intro : forall n, ~ ((~ n) /\ n).
Proof.
    unfold not.
    intros.
    destruct H.
    apply H.
    assumption.
Qed.

Lemma sum_to_zero_w : forall n m : nat, n + m = O -> n = O.
Proof.
    intros.
    induction m.
    rewrite zero_iden_r in H.
    assumption.
    apply IHm.
    rewrite succ_add_r in H.
    discriminate H.
Qed.

Lemma sum_to_zero : forall n m : nat, n + m = O -> n = O /\ m = O.
Proof.
    intros.
    split.
    apply sum_to_zero_w with m.
    assumption.
    apply sum_to_zero_w with n.
    rewrite commutes_plus.
    assumption.
Qed.


Lemma le_antisym : forall n m, le n m -> le m n -> n = m.
Proof.
    intros.
    destruct H as [k H].
    destruct H0 as [k0 H0].
    symmetry in H.
    rewrite H in H0.
    rewrite <- assoc_plus in H0.
    apply injectivity_zero in H0.
    apply sum_to_zero in H0.
    destruct H0.
    rewrite H0 in H.
    rewrite zero_iden_r in H.
    symmetry.
    assumption.
Qed.


Inductive tree :=
| Empty : tree
| Node : tree -> tree -> tree.

Fixpoint size t :=
match t with
| Empty => O
| Node t1 t2 => S (size t1 + size t2)
end.

Fixpoint swap t :=
match t with
| Empty => Empty
| Node t1 t2 => Node (swap t2) (swap t1)
end.



Theorem swap_size : forall t : tree, size t = size (swap t).
Proof.
    intros.
    induction t.
    simpl.
    reflexivity.
    simpl.
    rewrite IHt1, IHt2.
    f_equal.
    rewrite commutes_plus.
    reflexivity.
Qed.



