From Automata Require Import bij.
Import PeanoNat.
Require Import Coq.Logic.ClassicalUniqueChoice.

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

(*size is something we need*)
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
  intros.
  destruct H as [n [f H]].
  destruct H0 as [m [g H0]].
  intro.
  destruct H1 as [f1 H1].

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

(*other approach, define finite set as a list*)



(*GOAL CONVERSION ENSF to finset*)
