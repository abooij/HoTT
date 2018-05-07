Require Import
        HoTT.Basics
        HoTT.Types.Universe
        HoTT.Types.Sigma
        HoTT.Basics.Decidable
        HoTT.Basics.Equivalences
        HoTT.Types.Sum
        HoTT.Types.Paths
        HoTT.Types.Record
        HoTT.Tactics
        HoTT.HIT.Truncations.
Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.interfaces.rationals
        HoTT.Classes.interfaces.orders
        HoTT.Classes.theory.rings
        HoTT.Classes.orders.semirings
        HoTT.Classes.theory.apartness
        HoTT.Classes.theory.rationals
        HoTT.Classes.orders.orders
        HoTT.Classes.tactics.ring_tac.

Section dedekind.
  Universe UU.
  Context `{Funext} `{Univalence}.
  Context (Q : Type@{UU}) `{Rationals@{UU UU UU UU UU UU UU UU UU UU} Q}.
  Context {Qtrivialapart : TrivialApart Q} {Qdec : DecidablePaths Q}.
  Context `{Trichotomy Q (<)}.
  (* TODO: Remove the following requirement as soon as the rationals are adequately developed. *)
  Context `{Meet Q} `{Join Q}.

  Section axioms.

    (* Let precut := and (Q -> hProp) (Q -> hProp). *)

    (* only parsing, at level declarations? *)
    (* Notation "q < x" := (fst (@id precut x) q) : mc_scope. *)
    (* Notation "x < r" := (snd (@id precut x) r) : mc_scope. *)

    Class IsCut (L U : Q -> hProp) :=
      BuildIsCut
        { bounded_l :> hexists (fun q => L q)
          ; bounded_u :> hexists (fun r => U r)
          ; rounded_l :> forall q, L q <-> hexists (fun q' => q < q' /\ L q')
          ; rounded_u :> forall r, U r <-> hexists (fun r' => U r' /\ r' < r)
          ; transitive :> forall q r, L q /\ U r -> q < r
          ; located :> forall q r, q < r -> hor (L q) (U r)}.

    Lemma issig_iscut (L U : Q -> hProp)
      : { _ : hexists (fun q => L q) |
          { _ : hexists (fun r => U r) |
            { _ : forall q, L q <-> hexists (fun q' => q < q' /\ L q') |
              { _ : forall r, U r <-> hexists (fun r' => U r' /\ r' < r) |
                { _ : forall q r, L q /\ U r -> q < r |
                  forall q r, q < r -> hor (L q) (U r)}}}}}
          <~> IsCut L U.
    Proof.
      issig (BuildIsCut L U)
            (@bounded_l L U)
            (@bounded_u L U)
            (@rounded_l L U)
            (@rounded_u L U)
            (@transitive L U)
            (@located L U).
    Defined.

    Instance ishprop_IsCut (L U : Q -> hProp) : IsHProp (IsCut L U).
    Proof.
      apply (trunc_equiv' _ (issig_iscut L U)).
    Qed.

    Definition RD : Type := { x : (Q -> hProp) /\ (Q -> hProp) | IsCut (fst x) (snd x) }.

    Instance ishset_RD : IsHSet RD.
    Proof.
      exact _.
    Qed.

  End axioms.

  Section ring.

    Axiom ltneg1 : forall s, s - 1 < s.
    Axiom lt1 : forall s, s < s + 1.
    Axiom ltinterp : forall s t, s < t -> s < (s+t)/2 < t.

    Definition inc (s : Q) : RD.
    Proof.
      exists (fun q => BuildhProp (q < s), fun r => BuildhProp (s < r)).
      split.
      - apply tr; exists (s - 1); simpl. exact (ltneg1 s).
      - apply tr; exists (s + 1); simpl. exact (lt1 s).
      - intros q; simpl. split.
        + intros ltq; apply tr. exists ((q + s)/2). exact (ltinterp q s ltq).
        + intro X. strip_truncations. destruct X as [q' [ltqq' ltq'0]]. transitivity q'; assumption.
      - intros r; simpl. split.
        + intros ltr; apply tr. exists ((s + r)/2). exact (ltinterp s r ltr).
        + intro X. strip_truncations. destruct X as [r' [lt0r' ltr'r]]. transitivity r'; assumption.
      - intros q r ltq0r. destruct ltq0r as [ltq0 lt0r]. simpl in *. transitivity s; assumption.
      - intros q r ltqr. simpl. apply tr. destruct (trichotomy (<) q s) as [ltq0|[eqq0|lt0q]].
        + apply inl. assumption.
        + rewrite <- eqq0; apply inr; assumption.
        + apply inr. transitivity q; assumption.
    Defined.

    Global Instance rd0 : Zero RD := inc 0.
    Global Instance rd1 : One RD := inc 1.

    Definition plus (x y : RD) : RD.
    Proof.
      destruct x as [[L U] iscut_x]; destruct y as [[K V] iscut_y].
      exists (fun q => hexists (fun s => L s /\ K (q - s)), fun r => hexists (fun t => U t /\ V (r - t))).
      admit.
    Admitted.

    Global Instance rdplus : Plus RD := plus.
    Eval compute in (rd0 + rd1).

    Global Instance rdplusassoc : Associative plus.
    Proof. Admitted.

    Global Instance rdpluscomm : Commutative plus.
    Proof. Admitted.

    Global Instance rdplusidl : LeftIdentity rdplus rd0.
    Proof. Admitted.

    Global Instance rdplusidr : RightIdentity rdplus rd0.
    Proof. Admitted.

    Definition minus (x : RD) : RD.
    Proof.
      destruct x as [[L U] iscut_x].
      exists (fun q => U (- q), fun r => L (- r)).
      admit.
    Admitted.
    Local Instance plus_assoc : Associative plus.
    Proof.
    Admitted.
    Local Instance plus_comm : Commutative plus.
    Proof.
    Admitted.

    Global Instance rdminus : Negate RD := minus.




    Global Instance rdplusinvl : LeftInverse rdplus rdminus rd0.
    Proof. Admitted.

    Global Instance rdplusinvr : RightInverse rdplus rdminus rd0.
    Proof. Admitted.

    Definition times (x y : RD) : RD.
    Proof.
      destruct x as [[L U] iscut_x]; destruct y as [[K V] iscut_y].
      exists ( fun q => hexists
                  (fun abcd =>
                     match abcd with
                       (a,(b,(c,d))) =>
                       L a /\ U b /\ K c /\ V d /\ q < ((a*c) ⊓ (a*d) ⊓ (b * c) ⊓ (b * d))
                     end
                  )
        , fun r => hexists
                  (fun abcd =>
                     match abcd with
                       (a,(b,(c,d))) =>
                       L a /\ U b /\ K c /\ V d /\ ((a*c) ⊔ (a*d) ⊔ (b * c) ⊔ (b * d)) < r
                     end)
        ).
      admit.
    Admitted.

    Global Instance rdtimes : Mult RD := times.

    Global Instance rdtimesassoc : Associative times.
    Proof. Admitted.

    Global Instance rdtimescomm : Commutative times.
    Proof. Admitted.

    Global Instance rdtimesidl : LeftIdentity rdtimes rd1.
    Proof. Admitted.

    Global Instance rdtimesidr : RightIdentity rdtimes rd1.
    Proof. Admitted.

    Global Instance rdplustimesdistr : LeftDistribute rdtimes rdplus.
    Proof. Admitted.

    Existing Instance ishset_RD.

    Global Instance rdring : Ring RD.
    Proof.
      repeat split; try exact _.
    Qed.

  End ring.

  Section order.

    Definition rd_lt (x y : RD) : hProp.
    Proof.
      destruct x as [[L U] iscut_x]; destruct y as [[K V] iscut_y].
      exact (hexists (fun s => U s /\ K s)).
    Defined.

    Global Instance rdlt : Lt RD := rd_lt.

    Definition rdltantisymm (x y : RD) : ~ x < y < x.
    Proof.
      intros [p q]; strip_truncations.
      destruct p as [s [us ks]]; destruct q as [t [ut kt]].
      assert (ltst : s < t) by exact (@transitive _ _ y.2 s t (ks , ut)).
      assert (ltts : t < s) by exact (@transitive _ _ x.2 t s (kt , us)).
      exact (lt_antisym _ _ (ltst , ltts)).
    Qed.

    Local Instance rdlttrans : Transitive (@lt RD _).
    Proof. Admitted.

    Local Instance rdltcotrans : CoTransitive (@lt RD _).
    Proof. Admitted.

    Local Instance rdltirrefl : Irreflexive (@lt RD _).
    Proof. Admitted.

    Local Instance rdltstrict : StrictOrder (@lt RD _).
    Proof.
      repeat split; exact _.
    Qed.

    Global Instance rdapart : Apart RD := fun x y => (x < y) \/ (y < x).

    Global Instance rdaparthprop : is_mere_relation RD rdapart.
    Proof.
      intros x y. apply hprop_allpath. intros [ltxy|ltyx] [ltxy'|ltyx'].
      1, 4: apply ap, path_ishprop.
      - destruct (@lt_antisym RD rdlt _ x y (ltxy , ltyx')).
      - destruct (@lt_antisym RD rdlt _ x y (ltxy' , ltyx)).
    Qed.

    Local Instance rdapartsymm : Symmetric apart.
    Proof. Admitted.

    Local Instance rdapartcotrans : CoTransitive apart.
    Proof. Admitted.

    Definition rdaparteq (x y : RD) : ~ x ≶ y <-> x = y.
    Proof. Admitted.

    Definition rdapartdisj (x y : RD) : x ≶ y <-> (x < y) \/ (y < x).
    Proof. Admitted.

    Definition le (x y : RD) : hProp.
    Proof.
      destruct x as [[L U] iscut_x]; destruct y as [[K V] iscut_y].
      exact (BuildhProp (forall q, L q -> K q)).
    Defined.

    Global Instance rdle : Le RD := le.

    Definition rdlelt (x y : RD) : x ≤ y <-> ~ y < x.
    Proof. Admitted.

    Definition rdleminus (x y : RD) : ~ y < x -> {z : RD | y = x + z}.
    Proof. Admitted.




(* StrictlyOrderPreserving (canonical_names.plus z) *)
(* StrictlyOrderReflecting (canonical_names.plus z) *)
(* StrongBinaryExtensionality mult *)
(* forall x y : RD, PropHolds (0 < x) -> PropHolds (0 < y) -> PropHolds (0 < x * y) *)

    Global Instance rdfssro : FullPseudoSemiRingOrder rdle rdlt.
    Proof.
      repeat split; try exact _.
      - apply rdaparteq.
      - apply rdaparteq.
      - apply rdltantisymm.
      - apply rdapartdisj.
      - apply rdapartdisj.
      - apply rdleminus.
      - admit.
      - admit.
      - admit.
      - admit.
      - apply rdlelt.
      - apply rdlelt.
    Admitted.

  End order.

  Section field.

    Global Instance rdrecip : Recip RD.
    Proof.
      intros [x nonzero].
      destruct (x) as [[L U] x_iscut].
      exists ( fun q => hexists
                  (fun r' => U r' /\ ((0 < r' /\ 1 < (q*r')%mc) \/ (r' < 0 /\ 1 < (q*r')%mc)))
        , fun r => hexists
                  (fun q' => L q' /\ ((0 < q' /\ 1 < (q'*r)%mc) \/ (q' < 0 /\ (q'*r)%mc < 1)))
        ).
    Admitted.

    Definition neq01 : 0 ≶ 1.
    Proof.
      assert (0 < 1).
      {
        apply tr; exists ((0+1)/2); simpl.
        refine (@Q_average_between _ _ Q _ _ _ _ _ _ _ _ _ _ _ _ _ 0 1 _).
        apply lt_0_1.
      }
      apply inl; assumption.
    Qed.

    Global Instance rdfield : Field RD.
    Proof.
      repeat split; try exact _; try apply rdfssro.
      - exact neq01.
      - intros [x nonzero].

  End field.

End dedekind.
