Require Import Automata.bij.
Require Import Automata.finSet.
Require Import Automata.word.

Record PDA := mkPDA {
  pstates : Set
  ; palphabet : Set
  ; palphabet_finite : finite palphabet
  ; pstack : Set
  ; pstack_finite : finite pstack
  ; ptransition : pstates -> option pstack -> option palphabet  -> pstates -> word pstack -> Prop
  ; pinitial : pstates -> Prop
  ; pfinal : pstates -> Prop
  ; pstackinitial : pstack
}.

Record DPDA := mkDPDA {
  pda : PDA;
  determinism :
    forall q : pstates pda,
    forall z : option (pstack pda),
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

Definition initial_configuration{p : PDA} (c : pconfiguration p) :=
  pinitial p (state p c).

Definition final_configuration {p : PDA} (c : pconfiguration p) :=
  pfinal p (state p c).


Definition valid_transition_w {p : PDA} (c c' : pconfiguration p) (a : option (palphabet p)) :=
  let '(mkConfig _ state content) := c in
  let '(mkConfig _ state' content') := c' in
  exists m, ptransition p state (hd content)  a state' m /\ content' = suffix content' 1 ** m.

Record valid_transition {p : PDA} := mkTransition {
  tstart : pconfiguration p;
  tsymbol : option (palphabet p);
  tend : pconfiguration p;
  twittness : valid_transition_w tstart tend tsymbol
}.

Fixpoint valid_execution_w {p : PDA} (cs : word (pconfiguration p)) (letters : word (option (palphabet p))) :=
match cs with
| Eps => empty letters
| c ++ Eps => True
| c ++ c' ++ cs' =>
  match letters with
  | Eps => False
  | a ++ letters' => valid_execution_w cs' letters' /\ valid_transition_w c c' a
  end
end.

Record valid_execution (p : PDA) := mkExecution {
  econfigurations : word (pconfiguration p);
  eletters : word (option (palphabet p));
  ewittness : valid_execution_w econfigurations eletters
}.

Definition accepting_execution_w (p : PDA) (e : valid_execution p) :=
  let h := hd (econfigurations p e) in
  let b := last (econfigurations p e) in
  match h with
  | None => False
  | Some h => initial_configuration h /\
    match b with
    | None => False
    | Some b => final_configuration b
    end
  end.

Record accepting_execution (p : PDA) := mkAccExec {
  aexecution : valid_execution p;
  accepting : accepting_execution_w p aexecution
}.








