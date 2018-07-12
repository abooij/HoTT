Require Import
        HoTT.Basics
        HoTT.BoundedSearch
        HoTT.Types.Universe
        HoTT.Types.Sum
        HoTT.Spaces.Finite.

Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.interfaces.integers
        HoTT.Classes.implementations.assume_rationals
        HoTT.Classes.implementations.natpair_integers
        HoTT.Classes.implementations.dedekind_reals.

Require Import
        HoTT.Analysis.Cauchy
        HoTT.Analysis.Reals.

Module locator.

  (* Definition of a locator for a fixed real number. *)
  Definition locator (x : R) := forall q r : Q, q < r -> (L Q x q) + (U Q x r).

  Section gives.
    (* Basic theory of coproduct types. *)
    Context {A B : Type}.

    Definition gives_lower (z : A + B) : Type := (is_inl z).
    Definition gives_upper (z : A + B) : Type := (is_inr z).

    Check (fun z => BuildhProp (gives_lower z)).
    Check (fun z => BuildhProp (gives_upper z)).
    Global Instance gives_lower_dec {z} : Decidable (gives_lower z).
    Proof.
      destruct z; cbn; apply _.
    Defined.
    Global Instance gives_upper_dec {z} : Decidable (gives_upper z).
    Proof.
      destruct z; cbn; apply _.
    Defined.

    Definition gives_not_lower : forall (z : A + B) (na : ~ A), gives_upper z
      := is_inl_not_inr.
    Definition gives_not_upper : forall (z : A + B) (nb : ~ B), gives_lower z
      := is_inr_not_inl.

    Definition take_lower : forall (z : A + B), gives_lower z -> A := un_inl.
    Definition take_upper : forall (z : A + B), gives_upper z -> B := un_inr.

  End gives.

  Section rational.
    (* Rationals have locators: two constructions. *)
    Context (s : Q).

    Definition locator_first : locator (' s).
    Proof.
      intros q r ltqr.
      destruct (trichotomy _ q s) as [ltqs|[eqqs|ltsq]].
      - exact (inl ltqs).
      - rewrite eqqs in ltqr. exact (inr ltqr).
      - apply inr. simpl. transitivity q; assumption.
    Defined.

    Definition locator_second : locator (' s).
    Proof.
      intros q r ltqr.
      destruct (trichotomy _ s r) as [ltsr|[eqsr|ltrs]].
      - exact (inr ltsr).
      - rewrite <- eqsr in ltqr. exact (inl ltqr).
      - apply inl. simpl. transitivity r; assumption.
    Defined.

  End rational.

  Section approx.

    (* For any real number x, and any positive rational epsilon, there
    exists a rational q with q<x<q+epsilon *)

    Context (x : R)
            (epsilon : Q+).

    (* Axiom rat_arch_n : forall q r : Q, {n : nat | r < q + (' (' n)) * ' epsilon }. *)

    (* Section bounded. *)
    (*   Context (q r : Q) *)
    (*           (qltx : incR q < x) *)
    (*           (xltr : x < incR r). *)

    (*   Let n : nat := pr1 (rat_arch_n q r). *)

    (*   (* axiom: cast finite to natural *) *)

    (*   Let bla : forall k : Fin n, *)

    (* Axiom fin : forall k : Fin n, nat. *)

    (* Let generate_n (q r : Q) : (incR q < x) -> (x < incR r) -> . *)

    Axiom rational_epsilon_bound : hexists (fun q => ' q < x < ' (q + ' epsilon)).

  End approx.

  Section ops.
    (* If x and y are equipped with locators, then so are -x, x+y, etc. *)
    Context
      (x y : R)
      (f : locator x)
      (g : locator y).

    Definition minus : locator (- x).
    Proof.
      intros q r ltqr. compute.
      destruct (f (-r) (-q) (snd (rings.flip_lt_negate q r) ltqr)) as [ltnrx|ltxnq].
      - exact (inr ltnrx).
      - exact (inl ltxnq).
    Defined.

    Axiom plus : locator (x + y).

    Axiom times : locator (x * y).

    Context `{Univalence}.

    (* if x is apart from zero, then x^-1 has a locator *)
    Axiom divide : forall ineq, locator (rdrecip Q (x; ineq)).

    Axiom min : locator (x ⊓ y).

    Axiom max : locator (x ⊔ y).

  End ops.

  Section cauchy.
    (* Given a sequence of reals, all equipped with locators, and a
    Cauchy modulus, then we construct a locator for the limit.  *)
    Context `{Univalence}.

    Context (xs : nat -> R)
            {xs_cauchy : cauchy_modulus xs}
            (xs_locators : forall n, locator (xs n)).

    Axiom limits : locator (limit).

  End cauchy.

  Section lower_bounds.
    (* Given a real with a locator, we can find (integer) bounds. *)
    Context `{Univalence}.
    Context (x : R)
            (f : locator x).

    Let int := NatPair.Z nat.
    Definition cast_int_rat : Cast int Q := integers_to_ring int Q.
    Existing Instance cast_int_rat.

    Axiom ltkSk : forall k, cast_int_rat k < cast_int_rat (k+1).
    Let P (k : int) : Type := gives_lower (f ('k) ('(k+1)) (ltkSk k)).
    Definition P_prop {k} : IsHProp (P k).
    Proof.
      apply _.
    Qed.
    Axiom rat_floor : Q -> int.
    Axiom rat_floor_prop : forall q, ' (rat_floor q) <= q.
    Definition P_inhab : hexists (fun k => P k).
    Proof.
      assert (hqlt : hexists (fun q => L Q x q)).
      {
        unfold R, RD in *. refine (@bounded_l Q _ (L Q x) (U Q x) _).
        apply x.
      }
      strip_truncations.
      induction hqlt as [q lt].
      apply tr.
      set (k := (rat_floor q) - 1).
      exists k.
      assert (X : L Q x ('(k + 1))).
      {
        refine (snd (@rounded_l Q _ (L Q x) (U Q x) _ (' (k + 1))) _).
        - apply x.
        - apply tr; exists q; split.
          + unfold k. admit.
          + assumption.
      }
      assert (Y : not (U Q x ('(k+1)))) by refine (cut_disjoint Q _ _ X).
      apply gives_not_upper; assumption.
    Admitted.

    Axiom equiv_int_nat : int <~> nat.

    Definition lower_bound : {k : int | L Q x (' k)}.
    Proof.
      assert (path_int_nat : int = nat) by apply (path_universe equiv_int_nat).
      set (search := minimal_n).
      rewrite <- path_int_nat in search.
      destruct (search P _ _ P_inhab) as [k Pk].
      exists k.
      apply (take_lower _ Pk).
    Defined.

  End lower_bounds.

End locator.
