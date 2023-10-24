From Automata Require Import bij.


Definition interval (n : nat) := {x | x < n}.

Definition finite (s : Set) := exists (n : nat) (f : s -> interval n), bijective f.

Lemma interval_is_finite : forall n : nat, finite (interval n).
Proof.
    intro.
    unfold finite.
    exists n.
    exists (identity (interval n)).
    exact (iden_is_bijective (interval n)).
Qed.



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
