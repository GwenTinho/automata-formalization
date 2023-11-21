From Automata Require Import bij.
Import PeanoNat.
Require Import Coq.Logic.ClassicalUniqueChoice.
Require Import Coq.Lists.List.

(*IDEA 1*)

Inductive naive_interval : nat -> Set :=
| inil : naive_interval 0
| icons : forall (n : nat), naive_interval (S n) -> naive_interval n.

Definition naive_finite (s : Set) := exists (n : nat) (f : s -> naive_interval n), bijective f.

Definition naive_finite_op (s : Set) := exists (n : nat) (f : naive_interval n -> s), bijective f.

Lemma naive_finite_iff_naive_finite_op : forall s : Set, naive_finite s <-> naive_finite_op s.
Proof.
  intro.
  split.
  - intros [n [f H]].
    apply bijective_gives_inverse in H.
    destruct H as [g [Iso BijG]].
    exists n.
    exists g.
    assumption.
  - intros [n [g H]].
    apply bijective_gives_inverse in H.
    destruct H as [f [Iso BijF]].
    exists n.
    exists f.
    assumption.
Qed.


(*
IDEA 2
list of indicies
*)
Fixpoint interval (n : nat) :=
match n with
| O => nil
| S n => cons n (interval n)
end.

Fixpoint lmap{a b : Type} (f : a -> b) (l : list a) :=
match l with
| nil => nil
| cons h t => cons (f h) (lmap f t)
end.


Definition finite (s : Set) := exists (n : nat) (f : nat -> s),
  forall x : s, In x (lmap f (interval n)).


Lemma naive_finite_iff_finite : forall s : Set, finite s <-> naive_finite s.
Proof.
  intro.
  split.
  - intros [n [f H]].
    rewrite naive_finite_iff_naive_finite_op.
    exists n.
    induction n.
    +  exists (fun x =>
      match x with
      | inil => f 0
      | icons n t => f n
      end).
      split.
      * intros x y H0.
        destruct x.

Admitted.


Lemma interval_is_finite : forall n : nat, naive_finite (naive_interval n).
Proof.
    intro.
    unfold naive_finite.
    exists n.
    exists (identity (naive_interval n)).
    exact (iden_is_bijective (naive_interval n)).
Qed.

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
