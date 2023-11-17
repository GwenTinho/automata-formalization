Require Import Automata.finSet.


Record monoid := mkMon {
    mset : Set;
    mmult : mset -> mset -> mset;
    miden : mset;
    massoc : forall a b c : mset, mmult (mmult a b) c = mmult a (mmult b c);
    munitl : forall a : mset, mmult a miden = a;
    munitr : forall a : mset, mmult miden a = a
}.

Notation "a * b" := (mmult _ a b).

Fixpoint pow {m : monoid} (x : mset m) (n : nat) :=
match n with
| 0 => miden m
| S n => x * pow x n
end.

Lemma iden_unique : forall m : monoid, forall e : mset m, (forall a : mset m,
    e * a = a /\ a = a * e) -> e = miden m.
Proof.
    intros.
    assert (G := H (miden m)).
    destruct G.
    rewrite <- (munitl m) with e.
    apply H0.
Qed.

Definition fin_mon (m : monoid) := finite (mset m).

Definition idempotent {m : monoid} (a : mset m) := a * a = a.

Lemma finiteHasIdem : forall (m : monoid) (x : mset m),
    fin_mon m -> exists k : nat, k > 0 /\ idempotent (pow x k).
Proof.
    intros.


