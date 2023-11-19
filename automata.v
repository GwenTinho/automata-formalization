Require Import Ensembles.
Require Import Nat.
Require Import Coq.Structures.Equalities.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Automata.word.
Require Import Automata.finSet.
Require Import Coq.Logic.FunctionalExtensionality.
Require Setoid.

(*Curried definition of the transition function*)


Record NFA := mkNFA {
  nstates : Set
  ; nfinite : finite nstates
  ; nalphabet : Set
  ; nalphfinite : finite nalphabet
  ; ntransition : nstates -> option nalphabet -> nstates -> Prop
  ; ninitial : nstates -> Prop
  ; nfinal : nstates -> Prop
}.

Record SynchNFA := mkSynchNFA {
  snstates : Set
  ; snfinite : finite snstates
  ; snalphabet : Set
  ; snalphfinite : finite snalphabet
  ; sntransition : snstates -> snalphabet -> snstates -> Prop
  ; sninitial : snstates -> Prop
  ; snfinal : snstates -> Prop
}.


Record DFA := mkDFA {
  dstates : Set
  ; dfinite : finite dstates
  ; dalphabet : Set
  ; dalphfinite : finite dalphabet
  ; dtransition : dstates -> dalphabet -> dstates
  ; dinitial : dstates
  ; dfinal : dstates -> Prop
}.

Definition DRecognizedWord (d : DFA) (w : word (dalphabet d))  : Prop :=
  let
    fix aux (w' : word (dalphabet d)) (q : dstates d) : Prop :=
      match w' with
      | Eps => dfinal d q
      |  a ++ w'' =>  aux w'' (dtransition d q a)
      end
    in
  aux w (dinitial d).

Definition NRecognizedWord (n : NFA) (w : word (nalphabet n))  : Prop :=
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
    nalphfinite := dalphfinite d;
    nstates := dstates d;
    nfinite := dfinite d;
    ntransition := fun q a q' =>
      match a with
      | None => False
      | Some a => dtransition d q a = q'
      end;
    ninitial := fun q => q = dinitial d;
    nfinal := dfinal d
  |}.

Lemma dfa_if_initial_then_final : forall d : DFA,
 (exists q : dstates d, q = dinitial d -> dfinal d q) <-> dfinal d (dinitial d).
Proof.
  intro.
  split.
  intros [q H].
  (*we need decidability continue on finset ...*)
Admitted.

Lemma dfa_to_nfa_correct : forall d : DFA, NRecognizedLanguage (DFAtoNFA d) = DRecognizedLanguage d.
Proof.
  intro.
  unfold NRecognizedLanguage, DRecognizedLanguage.
  apply functional_extensionality.
  intro.
  induction x.
  unfold NRecognizedWord, DRecognizedWord.
  simpl.

Admitted.


(*determinization*)






