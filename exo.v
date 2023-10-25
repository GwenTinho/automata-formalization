Require Import Automata.word.

Definition palindrome{char : Set} (a : char) : dlang char := fun w => exists (s : word char), w = s ** (a ++ Eps) ** (reverse s).

Definition prefix{char : Set} (w w' : word char) := exists v : word char, (length v) > 0 /\ v ** w' = w.

Definition prefixless{char : Set} (L : dlang char) : Prop :=
  ~(exists w : word char, L w /\ (exists v, L v /\ prefix w v)).

Inductive ab :=
| a : ab
| b : ab.

Definition non_det_example (w : word ab) :=
  exists n : nat, n > O /\ (w = exp_char a n ** exp_char b n \/ w = exp_char a n ** exp_char b (2 * n)).

Inductive xyz :=
| x : xyz
| y : xyz
| z : xyz.

Definition non_det_example2 (w : word xyz) :=
  exists n : nat, n > O /\ w = exp_char x n ** exp_char y n ** exp_char z n.


