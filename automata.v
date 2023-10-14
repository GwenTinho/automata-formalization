Require Import Ensembles.
Require Import List.
Require Import Nat.
Import ListNotations.
Require Import Coq.Structures.Equalities.


Inductive word (char : Set) :=
  | Eps : word char
  | Concat : char -> word char -> word char.

Scheme Equality for word.


Notation "'Eps'" := (Eps _).

Notation "w1 ++ w2" := (Concat _ w1 w2) (at level 60, right associativity).

Fixpoint length {char : Set} (w : word char) : nat :=
  match w with
  | Eps => 0
  | a ++ w' => S (length w')
  end.

Fixpoint append {char : Set} (w1 w2: word char) : word char :=
  match w1 with
  | Eps => w2
  | a ++ w' => a ++ append w' w2
  end.

Definition eq_word char : forall x y : word char, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality.
  induction w.
  (*TODO*)
  admit.

Defined.


Definition dlang char := word char -> Prop.

Definition eq_dlang char : forall x y : dlang char, {x = y} + {x <> y}.
Proof.
  unfold dlang.
  intros.
  decide equality.
  admit.





(*Curried definition of the transition function*)


Record NFA := mkNFA {
  nstates : Set
  ; nalphabet : Set
  ; ntransition : nstates -> option nalphabet -> nstates -> Prop
  ; ninitial : nstates -> Prop
  ; nfinal : nstates -> Prop
}.



Record DFA := mkDFA {
  dstates : Set
  ; dalphabet : Set
  ; dtransition : dstates -> dalphabet -> dstates
  ; dinitial : dstates
  ; dfinal : dstates -> Prop
}.

Fixpoint DRecognizedWord (d : DFA) (w : word (dalphabet d))  : Prop :=
  let
    fix aux (w' : word (dalphabet d)) (q : dstates d) : Prop :=
      match w' with
      | Eps => dfinal d q
      |  a ++ w'' =>  aux w'' (dtransition d q a)
      end
    in
  aux w (dinitial d).

Fixpoint NRecognizedWord (n : NFA) (w : word (nalphabet n))  : Prop :=
  let
    fix aux (w' : word (nalphabet n)) (q : nstates n) : Prop :=
      match w' with
      | Eps => nfinal n q
      |  a ++ w'' => exists q': nstates n, ntransition n q (Some a) q' ->  aux w'' q'
      end
    in
  exists q0: nstates n, ninitial n q0 -> aux w q0.

Definition DRecognizedLanguage (d : DFA) : dlang (dalphabet d) :=
  DRecognizedWord d.

Definition NRecognizedLanguage (n : NFA) : dlang (nalphabet n) :=
  NRecognizedWord n.

Definition DFAtoNFA (d : DFA) : NFA :=
  {|
    nalphabet := dalphabet d;
    nstates := dstates d;
    ntransition := fun q a q' =>
      match a with
      | None => False
      | Some a => dtransition d q a = q'
      end;
    ninitial := fun q => q = dinitial d;
    nfinal := dfinal d
  |}.

Lemma rec_same_dfa_to_nfa :
  forall d : DFA, DRecognizedLanguage d = NRecognizedLanguage (DFAtoNFA d).
Proof.
  intros d.
  unfold DRecognizedLanguage, NRecognizedLanguage.
  unfold DRecognizedWord, NRecognizedWord.
  unfold DFAtoNFA.
  admit.



Record CFG := mkCFG
{
  nonterminals : Set;
  terminals : Set;
  production : nonterminals -> word (sum nonterminals terminals);
  start : nonterminals
}.

Definition CFGRecognizedWord (c : CFG) (w : word (terminals c)) :=
  admit.

Definition CFGRecognizedLanguage (c : CFG) : dlang (terminals c) :=
  CFGRecognizedWord c.

Definition inCNF (c : CFG) : Prop :=
  forall n : nonterminals c,
  length (production c n) <= 2.

Fixpoint CFGtoCNF (c : CFG) : CFG :=
  admit.

Lemma CFG_to_CNF_is_correct :
  forall c : CFG, inCNF (CFGtoCNF c).

Lemma rec_same_CFG_CNF :
  forall c : CFG,
  CFGRecognizedLanguage (CFGtoCNF c) = CFGRecognizedLanguage c.


Record PDA := mkPDA {
  pstates : Set
  ; palphabet : Set
  ; pstack : Set
  ; ptransition : pstates -> option palphabet -> option pstack -> pstates -> option pstack -> Prop
  ; pinitial : pstates -> Prop
  ; pfinal : pstates -> Prop
  ; pstackinitial : pstack
}.

Definition pconfiguration (p : PDA) := prod (pstates p) (word (pstack p)).

Definition possibleTransition {p : PDA} (c1 c2 : pconfiguration p) (a : option (palphabet p)) : Prop :=
  let (q1, g1) := c1 in
  let (q2, g2) := c2 in
    exists g' g'' : word (pstack p),
    exists z : pstack p,
    match g'' with
    | Eps => ptransition p q1 a (Some z) q2 None
    | s ++ g''' => ptransition p q1 a (Some z) q2 (Some s)
    end
    /\ g2 = append g' g''.

Definition finalConfig {p : PDA} (c : pconfiguration p) : Prop :=
  let (q, g) := c in
  pinitial p q.

Definition initialConfig {p : PDA} (c : pconfiguration p) : Prop :=
  let (q, g) := c in
  pfinal p q /\ g = pstackinitial p ++ Eps.

Fixpoint isExecution {p : PDA} (cs : list (pconfiguration p)) (letters : word (palphabet p)) : Prop :=
  match cs with
  | [] => True
  | [c] => True
  | c1 :: c2 :: rest =>
    match letters with
    | Eps => possibleTransition c1 c2 None
    | a ++ ls => possibleTransition c1 c2 (Some a) /\ isExecution (c2 :: rest) ls
    end
  end.


