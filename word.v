Require Import Automata.finSet.

Inductive word (char : Set) :=
  | Eps : word char
  | Concat : char -> word char -> word char.

Notation "'Eps'" := (Eps _).

Notation "w1 ++ w2" := (Concat _ w1 w2) (at level 60, right associativity).

Fixpoint length{char : Set} (w : word char) : nat :=
  match w with
  | Eps => 0
  | a ++ w' => S (length w')
  end.

Definition hd{char : Set} (w : word char) :=
match w with
| Eps => None
| a ++ _ => Some a
end.

Fixpoint last{char : Set} (w : word char) :=
match w with
| Eps => None
| a ++ Eps => Some a
| _ ++ t => last t
end.

Fixpoint prefix{char : Set} (w : word char) (n : nat) :=
match n with
| O => Eps
| S m =>
  match w with
  | Eps => Eps
  | a ++ w' => a ++ prefix w' m
  end
end.






Lemma length_one_implies_head : forall (char : Set) (w : word char),
length w > 0 -> ~ (hd w = None).
Proof.
  intros.

  induction w.
  simpl in H.
  unfold not.
  intro.
  easy.
  simpl.
  discriminate.
Qed.





Fixpoint append{char : Set} (w1 w2: word char) : word char :=
  match w1 with
  | Eps => w2
  | a ++ w' => a ++ append w' w2
  end.

Fixpoint exp{char : Set} (w : word char) (n : nat) :=
match n with
| O => Eps
| S m => append w (exp w m)
end.

Fixpoint exp_char{char : Set} (a : char) (n : nat) :=
match n with
| O => Eps
| S m => a ++ exp_char a m
end.


Fixpoint append_letter{char : Set} (w : word char) (a : char) :=
  match w with
  | Eps => a ++ Eps
  | x ++ w' => x ++ append_letter w' a
  end.

Notation "w1 ** w2" := (append w1 w2) (at level 60, right associativity).

Definition dlang char := word char -> Prop.

Fixpoint reverse{char : Set} (w : word char) :=
  match w with
  | Eps => Eps
  | a ++ w' => append_letter (reverse w') a
  end.

Fixpoint suffix{char : Set} (w : word char) (n : nat) :=
let r := reverse w in
match n with
| O => Eps
| S m =>
  match w with
  | Eps => Eps
  | a ++ w' => a ++ suffix w' m
  end
end.

Lemma reverse_append_is_prepend_reverse : forall (char : Set) (w : word char) (a : char),
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

Definition empty {char : Set} (w : word char) := length w = O.



Lemma reverse_involution : forall (char : Set) (w : word char),
  reverse (reverse w) = w.
Proof.
  intro.
  induction w.
  unfold reverse.
  reflexivity.
  simpl.
  rewrite (reverse_append_is_prepend_reverse char (reverse w) c).
  rewrite IHw.
  reflexivity.
Qed.


Fixpoint morphism {s d : Set} (h : s -> word d) (w : word s) :=
match w with
| Eps => Eps
| a ++ w' => h a ** morphism h w'
end.

Fixpoint alphabetic_morphism {s d : Set} (h : s -> d) (w : word s) :=
match w with
| Eps => Eps
| a ++ w' => h a ++ alphabetic_morphism h w'
end.


Lemma alphabetic_morphism_is_morphism : forall (s d : Set) (h : s -> d),
  exists h' : s -> word d, forall w : word s, morphism h' w = alphabetic_morphism h w.
Proof.
  intros.
  exists (fun a : s => (h a) ++ Eps).
  intro.
  induction w.
  simpl.
  reflexivity.
  simpl.
  rewrite IHw.
  simpl.
  reflexivity.
Qed.

