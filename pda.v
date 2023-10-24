Require Import Automata.bij.
Require Import Automata.finSet.
Require Import Automata.word.

Record PDA := mkPDA {
  pstates : Set
  ; palphabet : Set
  ; palphabet_finite : finite palphabet
  ; pstack : Set
  ; pstack_finite : finite pstack
  ; ptransition : pstates -> pstack -> option palphabet  -> pstates -> word pstack -> Prop
  ; pinitial : pstates -> Prop
  ; pfinal : pstates -> Prop
  ; pstackinitial : pstack
}.

Record DPDA := mkDPDA {
  pda : PDA;
  determinism :
    forall q : pstates pda,
    forall z : pstack pda,
    (
      exists! comb : prod (option (palphabet pda)) (prod (pstates pda) (word (pstack pda))),
      let (a, h) := comb in
      let (q',g) := h in
      ptransition pda q z a q' g
    )
}.

Record pconfiguration (p : PDA) := mkConfig {
  state : pstates p;
  content : word (pstack p)
}.




