Require Import Ensembles.
Require Import List.
Require Import Nat. 

Definition word char := list char.

Definition dlang char := word char -> Prop.

Inductive downset (n: nat) : Set := admit.

Check nat.

(*TODO*)
Definition incl {n : nat} (s : downset n) : nat := n. 

Check firstn.

Definition lastn{A} (n : nat) (l : list A) := firstn n (rev l).

Definition concat{char : Set} (L1 L2 : dlang char) : dlang char :=
  fun v =>
    
      exists i : (downset (length v + 1)), L1 (firstn (incl i) v) /\ L2 (lastn (incl i) v)
    
.

Lemma concP (L1 L2 : dlang char) {w : word char} :
  reflect ()
