Inductive word (char : Set) :=
  | Eps : word char
  | Concat : char -> word char -> word char.

Scheme Equality for word.

Parameter char : Set.

Notation "'Eps'" := (Eps _).

Notation "w1 ++ w2" := (Concat _ w1 w2) (at level 60, right associativity).

Fixpoint length (w : word char) : nat :=
  match w with
  | Eps => 0
  | a ++ w' => S (length w')
  end.


Fixpoint append (w1 w2: word char) : word char :=
  match w1 with
  | Eps => w2
  | a ++ w' => a ++ append w' w2
  end.


Fixpoint append_letter (w : word char) (a : char) :=
  match w with
  | Eps => a ++ Eps
  | x ++ w' => x ++ append_letter w' a
  end.

Notation "w1 ** w2" := (append w1 w2) (at level 60, right associativity).

Definition dlang char := word char -> Prop.

Fixpoint reverse (w : word char) :=
  match w with
  | Eps => Eps
  | a ++ w' => append_letter (reverse w') a
  end.

Lemma reverse_append_is_prepend_reverse : forall (w : word char) (a : char),
  reverse (append_letter w a) = a ++ (reverse w).
Proof.
  intros.
  induction w.
  unfold append_letter, reverse.
  unfold append.
  reflexivity.
  simpl.
  rewrite IHw.
  reflexivity.
Qed.



Lemma reverse_involution : forall w : word char,
  reverse (reverse w) = w.
Proof.
  intro.
  induction w.
  unfold reverse.
  reflexivity.
  simpl.
  rewrite (reverse_append_is_prepend_reverse (reverse w) c).
  rewrite IHw.
  reflexivity.
Qed.

Definition palindrome (a : char) := { w | exists (s : word char), w = s ** (a ++ Eps) ** (reverse s)}.



