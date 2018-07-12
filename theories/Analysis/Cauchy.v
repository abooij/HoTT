Require Import
        HoTT.Basics
        HoTT.Types.Universe
        HoTT.Types.Sum
        HoTT.Spaces.Finite.

Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.implementations.assume_rationals
        HoTT.Classes.implementations.dedekind_reals.

Require Import
        HoTT.Analysis.Reals.

Section modulus.
  Context `{Funext} `{Univalence}.

  Context (xs : nat -> R).

  Definition cauchy_modulus :=
    { M : Q+ -> nat |
      forall epsilon, forall m n, M epsilon <= m -> M epsilon<= n ->
                        abs ((xs m) - (xs n)) < ' (' epsilon)
    }.

End modulus.

Section convergence.
  Context `{Funext} `{Univalence}.

  Context (xs : nat -> R).
  Context (l : R).

  Definition converges :=
    forall epsilon : Q+, hexists
                 (fun N : nat =>
                    forall n, N <= n ->
                         abs (xs n - l) < ' (' epsilon)
                 ).

End convergence.

Section dedekind_complete.
  Context `{Funext} `{Univalence}.

  Context {xs : nat -> R}.
  Context {xs_cauchy : cauchy_modulus xs}.

  Axiom limit : R.

  Axiom complete : converges xs limit.

End dedekind_complete.
