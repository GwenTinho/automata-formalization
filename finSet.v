From Automata Require Import bij.
Import PeanoNat.


Definition interval (n : nat) := {x | x <= n}.

Definition finite (s : Set) := exists (n : nat) (f : s -> interval n), bijective f.

Lemma interval_is_finite : forall n : nat, finite (interval n).
Proof.
    intro.
    unfold finite.
    exists n.
    exists (identity (interval n)).
    exact (iden_is_bijective (interval n)).
Qed.

Definition lte_size (s t : Set) (p : finite s) (q : finite t) :=
  exists f : s -> t, injective f.

Lemma pigeonhole_baby
    :  forall m n : nat, m < n
    -> forall f : nat -> nat, (forall i, f i < m)
    -> exists i, i < n
    -> exists j, j < i /\ f i = f j.
Proof.
  intros.
  induction n.
  inversion H.
  exists (S m).
  intro.
  rewrite <- PeanoNat.Nat.succ_lt_mono in H1.
  apply IHn in H1.
  destruct H1.

Admitted.


(*(generalization of prev If S and T are sets,
and the cardinality of S is greater than the cardinality of T,
 then there is no injective function from S to T.*)
Lemma pigeonhole : forall (s t: Set),
  finite s ->
  finite t ->
  (exists f : s -> t, surjective f) ->
  (forall g : s -> t, not (bijective g)) ->
  (forall h : s -> t, not (injective h)).
Proof.

Admitted.


(*
found this too

Definition Full {A:Type} (l:list A) := forall a:A, In a l.
Definition Finite (A:Type) := exists (l:list A), Full l.
*)

(*another idea from herbelins automata formalization
Inductive Ensf : Set :=
  | empty : Ensf
  | add : Elt -> Ensf -> Ensf
with Elt : Set :=
  | natural : nat -> Elt
  | couple : Elt -> Elt -> Elt
  | up : Ensf -> Elt
  | word : Word -> Elt
with Word : Set :=
  | nil : Word
  | cons : Elt -> Word -> Word.
*)
