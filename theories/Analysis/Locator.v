Require Import
        HoTT.Types.Sum.

Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.implementations.assume_rationals
        HoTT.Classes.implementations.dedekind_reals.

Module locator.

  (* todo automatically use Q *)
  Definition locator (x : RD Q) := forall q r : Q, q < r -> (L Q x q) + (U Q x r).

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

    Definition locator_first : locator (inc Q s).
    Proof.
      intros q r ltqr.
      destruct (trichotomy _ q s) as [ltqs|[eqqs|ltsq]].
      - exact (inl ltqs).
      - rewrite eqqs in ltqr. exact (inr ltqr).
      - apply inr. simpl. transitivity q; assumption.
    Defined.

    Definition locator_second : locator (inc Q s).
    Proof.
      intros q r ltqr.
      destruct (trichotomy _ s r) as [ltsr|[eqsr|ltrs]].
      - exact (inr ltsr).
      - rewrite <- eqsr in ltqr. exact (inl ltqr).
      - apply inl. simpl. transitivity r; assumption.
    Defined.

  End rational.

  Section ops.

    Context
      (x y : RD Q)
      (f : locator x)
      (g : locator y).

    Definition minus : locator (- x).
    Proof.
      intros q r ltqr. compute.
      destruct (f (-r) (-q) (snd (rings.flip_lt_negate q r) ltqr)) as [ltnrx|ltxnq].
      - exact (inr ltnrx).
      - exact (inl ltxnq).
    Defined.

  End ops.

End locator.
