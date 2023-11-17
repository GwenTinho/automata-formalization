Record preorder{S : Set} := mkPreorder {
    prel : S -> S -> Prop;
    prefl : forall p : S, prel p p;
    ptrans : forall p q r: S, prel p q -> prel q r -> prel p r
}.

Record equivalence{S : Set} := mkEquivalence {
    erel : S -> S -> Prop;
    erefl : forall p : S, erel p p;
    esymm : forall p q : S, erel p q -> erel q p;
    etrans : forall p q r: S, erel p q -> erel q r -> erel p r
}.

Lemma preorder_induces_equiv : forall (S : Set) (p : preorder), exists e : equivalence,
    forall a b : S, erel e a b <-> prel p a b /\ prel p b a.
Proof.

