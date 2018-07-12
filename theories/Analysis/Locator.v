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
        HoTT.Analysis.Cauchy
        HoTT.Analysis.Reals.

Module locator.

  Definition locator (x : R) := forall q r : Q, q < r -> (L Q x q) + (U Q x r).

  Section gives.
    Context {A B : Type}.

    Definition gives_lower (z : A + B) : Type := (is_inl z).
    Definition gives_upper (z : A + B) : Type := (is_inr z).

    Check (fun z => BuildhProp (gives_lower z)).
    Check (fun z => BuildhProp (gives_upper z)).
    Check (fun z => dec (gives_lower z)).
    Check (fun z => dec (gives_upper z)).

    Definition gives_not_lower : forall (z : A + B) (na : ~ A), gives_upper z
      := is_inl_not_inr.
    Definition gives_not_upper : forall (z : A + B) (nb : ~ B), gives_lower z
      := is_inr_not_inl.

    Definition take_lower : forall (z : A + B), gives_lower z -> A := un_inl.
    Definition take_upper : forall (z : A + B), gives_upper z -> B := un_inr.

  End gives.

  Section rational.

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
    (* Proof. *)
    (*   intros q r ltqr. cbn. *)

    Axiom times : locator (x * y).

    Context `{Univalence}.

    (* Definition divide (ineq : x ≶ 0) : locator (rdrecip Q (x; ineq)). *)
    (* Proof. Admitted. *)

    (* if x is apart from zero, then x^-1 has a locator *)
    Axiom divide : forall ineq, locator (rdrecip Q (x; ineq)).

    Axiom min : locator (x ⊓ y).

    Axiom max : locator (x ⊔ y).

  End ops.

  Section cauchy.
    Context `{Univalence}.

    Context (xs : nat -> R)
            {xs_cauchy : cauchy_modulus xs}
            (xs_locators : forall n, locator (xs n)).

    Axiom limits : locator (limit).

  End cauchy.

End locator.
