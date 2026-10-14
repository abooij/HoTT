(** * A model of the rationals

The files in [theories/Analysis] assume a type [Q] with [Rationals Q], [DecidablePaths Q], [TrivialApart Q], [Trichotomy (<)], [RoundUpStrict Q], enumerations [nat <~> Q] and [nat <~> Q * Qpos Q], and sometimes [PropHolds (1 ≶ 0)].  This file checks that these hypotheses are consistent by constructing one type satisfying all of them: the field of fractions [F Z] of the integers [Z := NatPair.Z nat], with the order given by the sign of [num q * den q].  At the end, some results of the analysis files are instantiated at this model. *)

From HoTT Require Import Basics Types.Bool Types.Sigma Types.Prod Types.Arrow
  Types.Forall Types.Empty Truncations.Core Misc.BoundedSearch Spaces.Nat.Core.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.naturals
  interfaces.integers
  interfaces.rationals
  interfaces.round
  interfaces.archimedean
  implementations.peano_naturals
  implementations.natpair_integers
  implementations.field_of_fractions
  theory.rings
  theory.fields
  theory.integers
  theory.rationals
  theory.apartness
  orders.orders
  orders.semirings
  orders.rings
  orders.integers
  orders.nat_int.

From HoTT.Analysis Require Import
  MetricSpace Locator LocatorDigits IntermediateValue BanachFixedPoint
  CauchyReals.

Local Set Universe Minimization ToSet.

Import NatPair.Instances.
Import Frac FracField.

Section enumerations.
  Local Open Scope nat_scope.
  Local Open Scope type_scope.

  (** ** Enumerations of countably infinite types *)

  Section least_witness.
    Context (P : nat -> Type) `{forall n, Decidable (P n)}.

    (** Either [P] has a least witness, or it has no witness below [N]. *)
    Local Definition least_witness_or_none (N : nat)
      : {n : nat & P n * forall m, P m -> n <= m}
        + (forall m, m < N -> ~ P m).
    Proof.
      induction N as [|N IH].
      - right; intros m l; destruct (not_lt_zero_r _ l).
      - destruct IH as [s | none].
        1: exact (inl s).
        destruct (dec (P N)) as [p | np].
        + left; exists N; split; only 1: exact p.
          intros m pm; apply geq_iff_not_lt.
          intros l; exact (none m l pm).
        + right; intros m l.
          destruct (equiv_leq_lt_or_eq (leq_pred' l)) as [l' | q].
          * exact (none m l').
          * destruct q^; exact np.
    Defined.

    Definition least_witness (n : nat) (p : P n)
      : {k : nat & P k * forall m, P m -> k <= m}.
    Proof.
      destruct (least_witness_or_none n.+1) as [s | none].
      - exact s.
      - destruct (none n _ p).
    Defined.

  End least_witness.

  Definition decidable_forall_lt (P : nat -> Type) `{forall n, Decidable (P n)}
    (N : nat)
    : Decidable (forall m, m < N -> P m).
  Proof.
    induction N as [|N IH].
    - left; intros m l; destruct (not_lt_zero_r _ l).
    - destruct IH as [h | nh].
      2: right; intros h; exact (nh (fun m l => h m _)).
      destruct (dec (P N)) as [p | np].
      + left; intros m l.
        destruct (equiv_leq_lt_or_eq (leq_pred' l)) as [l' | q].
        * exact (h m l').
        * destruct q^; exact p.
      + right; intros h'; exact (np (h' N _)).
  Defined.

  (** A decidable family of propositions on [nat] with arbitrarily large witnesses is enumerated in increasing order. *)
  Section enumerate_unbounded.
    Context `{Funext} (P : nat -> Type) `{forall n, IsHProp (P n)}
      `{forall n, Decidable (P n)}
      (unbounded : forall N, hexists (fun n => (N <= n) * P n)).

    Local Definition next (N : nat)
      : {n : nat & ((N <= n) * P n) * forall m, (N <= m) * P m -> n <= m}
      := let w := minimal_n _ _ (unbounded N) in least_witness _ w.1 w.2.

    Local Fixpoint enum (k : nat) : nat
      := match k with
         | 0 => (next 0).1
         | k.+1 => (next (enum k).+1).1
         end.

    Local Definition enum_p (k : nat) : P (enum k).
    Proof.
      destruct k; exact (snd (fst (next _).2)).
    Defined.

    Local Definition enum_lt_succ (k : nat) : enum k < enum k.+1
      := fst (fst (next _).2).

    Local Definition enum_lt (k l : nat) : k < l -> enum k < enum l.
    Proof.
      induction l as [|l IH].
      - intros c; destruct (not_lt_zero_r _ c).
      - intros c.
        destruct (equiv_leq_lt_or_eq (leq_pred' c)) as [c' | q].
        + exact (lt_trans (IH c') (enum_lt_succ l)).
        + destruct q; exact (enum_lt_succ k).
    Defined.

    Local Definition isinj_enum (k l : nat) : enum k = enum l -> k = l.
    Proof.
      intros q.
      destruct (Core.nat_trichotomy k l) as [[c | c] | c].
      - apply Empty_rec, (lt_irrefl (enum k)).
        exact (transport (fun n => enum k < n) q^ (enum_lt _ _ c)).
      - exact c.
      - apply Empty_rec, (lt_irrefl (enum k)).
        exact (transport (fun n => n < enum k) q^ (enum_lt _ _ c)).
    Defined.

    Local Definition enum_geq (k : nat) : k <= enum k.
    Proof.
      induction k as [|k IH].
      - exact (leq_zero_l _).
      - exact (lt_leq_lt_trans IH (enum_lt_succ k)).
    Defined.

    Local Definition enum_hits_below (k n : nat) (p : P n)
      : n <= enum k -> {j : nat & enum j = n}.
    Proof.
      induction k as [|k IH].
      - intros c; exists 0.
        exact (leq_antisym (snd (next 0).2 n (leq_zero_l _, p)) c).
      - intros c.
        destruct (leq_dichotomy n (enum k)) as [c' | c'].
        1: exact (IH c').
        exists k.+1.
        exact (leq_antisym (snd (next _).2 n (c', p)) c).
    Defined.

    Local Definition enum_hits (n : nat) (p : P n) : {j : nat & enum j = n}
      := enum_hits_below n n p (enum_geq n).

    Definition equiv_nat_sig_unbounded : nat <~> {n : nat & P n}.
    Proof.
      snapply equiv_adjointify.
      - exact (fun k => (enum k; enum_p k)).
      - exact (fun x => (enum_hits x.1 x.2).1).
      - intros x; apply path_sigma_hprop.
        exact (enum_hits x.1 x.2).2.
      - intros k; apply isinj_enum.
        exact (enum_hits _ _).2.
    Defined.

  End enumerate_unbounded.

  (** A type with decidable equality, a surjection from [nat] and, for every finite list of elements, an element not in the list, is equivalent to [nat]. *)
  Section enumerate_surjection.
    Context `{Funext} {A : Type} `{DecidablePaths A}
      (e : nat -> A) {es : IsSurjection e}
      (fresh : forall N, {a : A & forall m, m < N -> e m <> a}).

    (** The indices at which [e] takes a value it did not take before. *)
    Local Definition IsNew (n : nat) : Type := forall m, m < n -> e m <> e n.

    Local Instance ishprop_isnew (n : nat) : IsHProp (IsNew n).
    Proof.
      unfold IsNew; exact _.
    Defined.

    Local Instance decidable_isnew (n : nat) : Decidable (IsNew n)
      := decidable_forall_lt _ n.

    Local Definition least_preimage (a : A)
      : {n : nat & (e n = a) * IsNew n}.
    Proof.
      pose (w := minimal_n (fun n => e n = a) _
                   (@center (merely (hfiber e a)) (es a))).
      destruct (least_witness _ w.1 w.2) as [n [p min]].
      refine (n; (p, _)).
      intros m l q.
      exact (lt_irrefl _ (lt_leq_lt_trans (min m (q @ p)) l)).
    Defined.

    Local Definition isinj_e_isnew (n n' : nat) (u : IsNew n) (u' : IsNew n')
      : e n = e n' -> n = n'.
    Proof.
      intros q.
      destruct (Core.nat_trichotomy n n') as [[c | c] | c].
      - destruct (u' n c q).
      - exact c.
      - destruct (u n' c q^).
    Defined.

    Local Definition equiv_sig_isnew : {n : nat & IsNew n} <~> A.
    Proof.
      snapply equiv_adjointify.
      - exact (fun x => e x.1).
      - exact (fun a => ((least_preimage a).1; snd (least_preimage a).2)).
      - exact (fun a => fst (least_preimage a).2).
      - intros [n u]; apply path_sigma_hprop.
        exact (isinj_e_isnew _ _ (snd (least_preimage _).2) u
                 (fst (least_preimage _).2)).
    Defined.

    Local Definition isnew_unbounded (N : nat)
      : hexists (fun n => (N <= n) * IsNew n).
    Proof.
      apply tr.
      destruct (fresh N) as [a ha].
      exists (least_preimage a).1; split.
      2: exact (snd (least_preimage a).2).
      apply geq_iff_not_lt; intros l.
      exact (ha _ l (fst (least_preimage a).2)).
    Defined.

    Definition equiv_nat_surjection_fresh : nat <~> A
      := equiv_sig_isnew oE equiv_nat_sig_unbounded IsNew isnew_unbounded.

  End enumerate_surjection.

  (** *** Pairs of natural numbers *)

  (** A surjection [nat -> nat * nat], running through the diagonals [(d, 0), (d - 1, 1), ..., (0, d)]. *)
  Fixpoint nat_unpair (n : nat) : nat * nat
    := match n with
       | 0 => (0, 0)
       | n.+1 => match nat_unpair n with
                 | (0, b) => (b.+1, 0)
                 | (a.+1, b) => (a, b.+1)
                 end
       end.

  Local Definition nat_unpair_hits (a b : nat) : Type
    := {n : nat & nat_unpair n = (a, b)}.

  Local Definition nat_unpair_hits_step (a b : nat)
    : nat_unpair_hits a.+1 b -> nat_unpair_hits a b.+1.
  Proof.
    intros [n p]; exists n.+1; cbn; by rewrite p.
  Defined.

  Local Definition nat_unpair_hits_diag_step (b : nat)
    : nat_unpair_hits 0 b -> nat_unpair_hits b.+1 0.
  Proof.
    intros [n p]; exists n.+1; cbn; by rewrite p.
  Defined.

  Local Definition nat_unpair_hits_walk (k : nat)
    : forall a b, nat_unpair_hits (k + a) b -> nat_unpair_hits a (k + b).
  Proof.
    induction k as [|k IH].
    1: exact (fun a b h => h).
    intros a b h.
    change (nat_unpair_hits a (k + b).+1).
    rewrite <- nat_add_succ_r.
    exact (IH a b.+1 (nat_unpair_hits_step _ _ h)).
  Defined.

  Local Definition nat_unpair_hits_diag (d : nat) : nat_unpair_hits d 0.
  Proof.
    induction d as [|d IH].
    1: exact (0; idpath).
    rewrite <- (nat_add_zero_r d) in IH |- *.
    exact (nat_unpair_hits_diag_step _ (nat_unpair_hits_walk d 0 0 IH)).
  Defined.

  Definition nat_unpair_section (a b : nat)
    : {n : nat & nat_unpair n = (a, b)}.
  Proof.
    pose proof (nat_unpair_hits_walk b a 0 (nat_unpair_hits_diag (b + a))) as h.
    by rewrite nat_add_zero_r in h.
  Defined.

  (** A surjection onto a product from surjections onto its factors. *)
  Definition issurj_nat_pair {A B : Type} (eA : nat -> A) (eB : nat -> B)
    {esA : IsSurjection eA} {esB : IsSurjection eB}
    : IsSurjection
        (fun n => (eA (fst (nat_unpair n)), eB (snd (nat_unpair n)))).
  Proof.
    apply BuildIsSurjection.
    intros [a b].
    pose proof (@center (merely (hfiber eA a)) (esA a)) as ha.
    pose proof (@center (merely (hfiber eB b)) (esB b)) as hb.
    strip_truncations; apply tr.
    destruct ha as [i p], hb as [j q].
    exists (nat_unpair_section i j).1; cbn.
    rewrite (nat_unpair_section i j).2; cbn.
    by rewrite p, q.
  Defined.

End enumerations.

(** ** Rearranging sums and products *)

Section interchange.
  Context {R : Type} `{IsCRing R}.

  Local Definition plus_interchange (a b c d : R)
    : (a + b) + (c + d) = (a + c) + (b + d).
  Proof.
    rewrite <- !plus_assoc; apply ap.
    rewrite !plus_assoc; apply (ap (+ d)).
    apply plus_comm.
  Defined.

  Local Definition mult_interchange (a b c d : R)
    : (a * b) * (c * d) = (a * c) * (b * d).
  Proof.
    rewrite <- !mult_assoc; apply ap.
    rewrite !mult_assoc; apply (ap (.* d)).
    apply mult_comm.
  Defined.

End interchange.

Section model.
  Context `{Funext} `{Univalence}.

  (** ** The integers and their field of fractions *)

  Definition Z : Type@{Set} := NatPair.Z@{Set Set} nat.

  Local Notation Fr := (Frac Z).

  Definition Q : Type@{Set} := F Z.

  (** ** Positivity of fractions *)

  Definition frac_pos@{} (q : Fr) : Type@{Set} := 0 < num q * den q.

  Local Definition den_square_pos (q : Fr) : 0 < den q * den q.
  Proof.
    apply square_pos, trivial_apart, den_ne_0.
  Defined.

  Local Definition frac_pos_respect (q r : Fr)
    : equiv q r -> frac_pos q -> frac_pos r.
  Proof.
    unfold equiv, frac_pos; intros E p.
    apply (pos_mult_rev_l _ (den q * den q)).
    2: apply den_square_pos.
    assert (E' : num r * den r * (den q * den q)
                 = num q * den q * (den r * den r)).
    { lhs rapply mult_interchange.
      rewrite <- E, (mult_comm (den r) (den q)).
      apply mult_interchange. }
    rewrite E'.
    exact (pos_mult _ _ p (den_square_pos r)).
  Defined.

  Local Definition frac_pos_plus (q r : Fr)
    : frac_pos q -> frac_pos r -> frac_pos (pl _ q r).
  Proof.
    unfold frac_pos; cbn; intros p p'.
    rewrite plus_mult_distr_r, (mult_interchange (num q)).
    rewrite (mult_comm (den q) (den r)), (mult_interchange (num r)).
    apply pos_plus_compat; apply pos_mult; trivial; apply den_square_pos.
  Defined.

  Local Definition frac_pos_mult (q r : Fr)
    : frac_pos q -> frac_pos r -> frac_pos (ml _ q r).
  Proof.
    unfold frac_pos; cbn; intros p p'.
    rewrite mult_interchange.
    exact (pos_mult _ _ p p').
  Defined.

  Local Definition frac_pos_neg (q : Fr)
    : frac_pos (neg _ q) <-> num q * den q < 0.
  Proof.
    unfold frac_pos; cbn.
    rewrite <- negate_mult_distr_l.
    symmetry; apply flip_neg_negate.
  Defined.

  (** ** Positivity of rationals *)

  Local Instance decidable_frac_pos@{} (q : Fr) : Decidable (frac_pos q).
  Proof.
    unfold frac_pos; exact _.
  Defined.

  Local Definition frac_posb@{} (q : Fr) : Bool
    := if dec (frac_pos q) then true else false.

  Local Definition frac_posb_true (q : Fr)
    : frac_posb q = true <-> frac_pos q.
  Proof.
    unfold frac_posb; destruct (dec (frac_pos q)) as [p | np]; split.
    - exact (fun _ => p).
    - exact (fun _ => idpath).
    - intros c; destruct (false_ne_true c).
    - intros p; destruct (np p).
  Defined.

  Local Definition frac_posb_respect (q r : Fr)
    : equiv q r -> frac_posb q = frac_posb r.
  Proof.
    intros E; unfold frac_posb.
    destruct (dec (frac_pos q)) as [p | np],
      (dec (frac_pos r)) as [p' | np'].
    - reflexivity.
    - destruct (np' (frac_pos_respect q r E p)).
    - destruct (np (frac_pos_respect r q E^ p')).
    - reflexivity.
  Defined.

  Local Definition q_posb : Q -> Bool
    := @F_rec@{Set Set} _ _ _ _ Bool (hset_decpaths Bool) frac_posb
         frac_posb_respect.

  Definition QPos (x : Q) : Type@{Set} := q_posb x = true.

  Local Instance ishprop_qpos (x : Q) : IsHProp (QPos x) := _.

  Local Definition qpos_class (q : Fr) : QPos (' q) <-> frac_pos q
    := frac_posb_true q.

  Local Definition qpos_plus (x y : Q) : QPos x -> QPos y -> QPos (x + y).
  Proof.
    revert x y; srapply F_ind2; intros q r p p'.
    apply qpos_class, frac_pos_plus; apply qpos_class; assumption.
  Defined.

  Local Definition qpos_mult (x y : Q) : QPos x -> QPos y -> QPos (x * y).
  Proof.
    revert x y; srapply F_ind2; intros q r p p'.
    apply qpos_class, frac_pos_mult; apply qpos_class; assumption.
  Defined.

  Local Definition not_qpos_and_negate (x : Q) : QPos x -> ~ QPos (- x).
  Proof.
    revert x; srapply F_ind; intros q p p'.
    apply (qpos_class q) in p.
    apply (qpos_class (neg _ q)), frac_pos_neg in p'.
    exact (lt_antisym _ _ (p, p')).
  Defined.

  Local Definition not_qpos_0 : ~ QPos 0.
  Proof.
    intros p; apply (qpos_class 0) in p.
    change (0 < (0 : Z) * 1) in p.
    rewrite mult_0_l in p.
    exact (irreflexivity (<) _ p).
  Defined.

  Local Definition qpos_negate_not_qpos (x : Q)
    : ~ QPos x -> x <> 0 -> QPos (- x).
  Proof.
    revert x; srapply F_ind; intros q np nz.
    apply (qpos_class (neg _ q)), frac_pos_neg.
    destruct (trichotomy (<) (num q * den q) 0) as [c | [c | c]].
    - exact c.
    - apply zero_product in c; destruct c as [c | c].
      + apply Empty_rec, nz, (path (x:=q) (y:=0)).
        change (num q * 1 = (0 : Z) * den q).
        rewrite c, 2 mult_0_l; reflexivity.
      + destruct (den_ne_0 q c).
    - destruct (np (snd (qpos_class q) c)).
  Defined.

  Local Definition qpos_trichotomy (x : Q)
    : QPos x + (x = 0) + QPos (- x).
  Proof.
    destruct (dec (QPos x)) as [p | np].
    1: exact (inl (inl p)).
    destruct (dec (x = 0)) as [z | nz].
    1: exact (inl (inr z)).
    exact (inr (qpos_negate_not_qpos x np nz)).
  Defined.

  (** ** The order on the rationals *)

  #[export] Instance Q_apart : Apart@{Set Set} Q := fun x y => x <> y.

  #[export] Instance Q_trivial_apart : TrivialApart Q.
  Proof.
    split.
    - unfold apart, Q_apart; exact _.
    - intros x y; reflexivity.
  Defined.

  #[export] Instance Q_lt : Lt@{Set Set} Q := fun x y => QPos (y - x).

  #[export] Instance Q_le : Le@{Set Set} Q := fun x y => ~ (y < x).

  Local Definition minus_plus_minus (x y z : Q) : (z - y) + (y - x) = z - x.
  Proof.
    rewrite plus_assoc, <- (plus_assoc z), plus_negate_l, plus_0_r.
    reflexivity.
  Defined.

  Local Definition plus_minus_plus (x y z : Q) : (z + y) - (z + x) = y - x.
  Proof.
    rewrite negate_plus_distr, (plus_comm (-z)), plus_assoc.
    rewrite (plus_comm _ (-z)), !plus_assoc, plus_negate_l, plus_0_l.
    reflexivity.
  Defined.

  #[export] Instance Q_strict_order : StrictOrder Q_lt.
  Proof.
    split.
    - unfold lt, Q_lt; exact _.
    - intros x l.
      unfold lt, Q_lt in l; rewrite plus_negate_r in l.
      exact (not_qpos_0 l).
    - intros x y z l l'.
      unfold lt, Q_lt in *.
      rewrite <- (minus_plus_minus x y z).
      exact (qpos_plus _ _ l' l).
  Defined.

  #[export] Instance Q_trichotomy : Trichotomy Q_lt.
  Proof.
    intros x y.
    destruct (qpos_trichotomy (y - x)) as [[l | e] | l].
    - exact (inl l).
    - exact (inr (inl (fst (equal_by_zero_sum y x) e)^)).
    - right; right.
      unfold lt, Q_lt; rewrite negate_swap_r; exact l.
  Defined.

  Local Instance Q_isapart : IsApart Q := dec_strong_setoid.

  Local Instance Q_pseudo_order : PseudoOrder Q_lt
    := dec_strict_pseudo_order.

  #[export] Instance Q_full_pseudo_order : FullPseudoOrder Q_le Q_lt.
  Proof.
    split.
    - unfold le, Q_le; exact _.
    - exact _.
    - intros x y; reflexivity.
  Defined.

  #[export] Instance Q_full_pseudo_srorder
    : FullPseudoSemiRingOrder Q_le Q_lt.
  Proof.
    apply from_full_pseudo_ring_order.
    - intros z x y l.
      unfold lt, Q_lt; rewrite plus_minus_plus; exact l.
    - exact (dec_strong_binary_morphism (.*.)).
    - unfold PropHolds, lt, Q_lt; intros x y.
      rewrite !negate_0, !plus_0_r.
      apply qpos_mult.
  Defined.

  (** ** The map into a field of characteristic zero *)

  Section to_field.
    Universe j.
    Context (B : Type@{j}) `{IsField B} {Bchar : FieldCharacteristic B 0}.

    Local Notation nB := (naturals_to_semiring nat B).

    Local Definition z_to_field : Z -> B
      := NatPair.Z_rec@{Set Set j} nat (NatPair.PairT.to_ring@{Set j} nat B)
           (NatPair.PairT.to_ring_respects@{Set j} nat).

    Local Instance issemiringpreserving_z_to_field
      : IsSemiRingPreserving z_to_field.
    Proof.
      split; split; red.
      - change (@sg_op B _) with (@plus B _);
          change (@sg_op Z _) with (@plus Z _).
        srapply (NatPair.Z_ind2 nat).
        intros [pa na] [pb nb].
        change (nB (pa + pb) - nB (na + nb)
                = (nB pa - nB na) + (nB pb - nB nb)).
        rewrite !(preserves_plus (f:=nB)), negate_plus_distr.
        apply plus_interchange.
      - change (nB 0 - nB 0 = 0).
        apply plus_negate_r.
      - change (@sg_op B _) with (@mult B _);
          change (@sg_op Z _) with (@mult Z _).
        srapply (NatPair.Z_ind2 nat).
        intros [pa na] [pb nb].
        change (nB (pa * pb + na * nb) - nB (pa * nb + na * pb)
                = (nB pa - nB na) * (nB pb - nB nb)).
        rewrite !(preserves_plus (f:=nB)), !(preserves_mult (f:=nB)).
        rewrite plus_mult_distr_r, !plus_mult_distr_l.
        rewrite negate_mult_negate, <- negate_mult_distr_l,
          <- negate_mult_distr_r.
        rewrite (preserves_plus (f:=nB) (pa * nb)),
          !(preserves_mult (f:=nB)).
        rewrite (negate_plus_distr (nB pa * nB nb)), plus_interchange.
        apply ap, plus_comm.
      - change (nB 1 - nB 0 = 1).
        rewrite (preserves_1 (f:=nB)), (preserves_0 (f:=nB)), negate_0.
        apply plus_0_r.
    Defined.

    (** Every semiring map from [Z] agrees with [z_to_field]. *)
    Local Definition z_to_field_unique (g : Z -> B)
      `{!IsSemiRingPreserving g} (x : Z)
      : g x = z_to_field x.
    Proof.
      revert x; srapply (NatPair.Z_ind nat).
      intros [pa na].
      lhs napply (ap g (NatPair.Npair_splits nat pa na)).
      rewrite (preserves_plus (f:=g)), (preserves_negate (f:=g)).
      pose proof (compose_sr_morphism (cast nat Z) g
                    (NatPair.Z_of_N_morphism nat) _).
      exact (ap011 plus (toR_unique (g o cast nat Z) pa)^
               (ap negate (toR_unique (g o cast nat Z) na)^)).
    Defined.

    Local Definition nat_iter_to_field (n : nat)
      : nat_iter n (1 +) 0 = nB n.
    Proof.
      induction n as [|n IH].
      1: reflexivity.
      lhs napply (ap (1 +) IH).
      exact ((ap (+ nB n) (preserves_1 (f:=nB)))^
             @ (preserves_plus (f:=nB) 1%nat n)^).
    Defined.

    Local Definition nat_to_field_succ_apart (k : nat) : nB (S k) ≶ 0.
    Proof.
      rewrite <- nat_iter_to_field.
      apply (fst (Bchar (S k) (leq_succ (leq_zero_l k)))).
      intros m p; exact (neq_nat_zero_succ k p^).
    Defined.

    Local Definition nat_to_field_minus_succ_add (a k : nat)
      : nB a - nB ((S k) + a)%nat = - nB (S k).
    Proof.
      rewrite (preserves_plus (f:=nB)), negate_plus_distr.
      rewrite plus_comm, <- plus_assoc, plus_negate_l.
      apply plus_0_r.
    Defined.

    Local Definition nat_to_field_succ_add_minus (b k : nat)
      : nB ((S k) + b)%nat - nB b = nB (S k).
    Proof.
      rewrite (preserves_plus (f:=nB)), <- plus_assoc, plus_negate_r.
      apply plus_0_r.
    Defined.

    Local Definition z_to_field_apart (d : Z)
      : d <> 0 -> z_to_field d ≶ 0.
    Proof.
      revert d; srapply (NatPair.Z_ind nat).
      intros [a b] nz.
      change (nB a - nB b ≶ 0).
      assert (ne : a <> b).
      { intros p; apply nz, (NatPair.Z_path nat).
        exact (nat_add_zero_r a @ p). }
      destruct (fst neq_iff_lt_or_gt ne) as [l | l].
      - destruct (equiv_leq_add _ _ l) as [k q].
        destruct q; rewrite nat_add_succ_r.
        rewrite (nat_to_field_minus_succ_add a k).
        apply apart_negate, nat_to_field_succ_apart.
      - destruct (equiv_leq_add _ _ l) as [k q].
        destruct q; rewrite nat_add_succ_r.
        rewrite (nat_to_field_succ_add_minus b k).
        apply nat_to_field_succ_apart.
    Defined.

    (** ** Fractions in the field *)

    Local Definition div_mult_cancel (a : B) (b : ApartZero B)
      : (a // b) * b.1 = a.
    Proof.
      rewrite <- mult_assoc, (mult_comm (// b)), recip_inverse.
      apply mult_1_r.
    Defined.

    Local Definition div_unique (a t : B) (b : ApartZero B)
      : t * b.1 = a -> t = a // b.
    Proof.
      intros p; rewrite <- p, <- mult_assoc, recip_inverse.
      symmetry; apply mult_1_r.
    Defined.

    Local Definition den_to_field (q : Fr) : ApartZero B
      := (z_to_field (den q); z_to_field_apart _ (den_ne_0 q)).

    Local Definition frac_to_field (q : Fr) : B
      := z_to_field (num q) // den_to_field q.

    Definition q_to_field : Q -> B.
    Proof.
      srapply (F_rec frac_to_field).
      intros q r E.
      apply equal_quotients; cbn.
      rewrite <- !(preserves_mult (f:=z_to_field)).
      exact (ap z_to_field E).
    Defined.

    #[export] Instance issemiringpreserving_q_to_field
      : IsSemiRingPreserving q_to_field.
    Proof.
      split; split; red.
      - change (@sg_op B _) with (@plus B _);
          change (@sg_op Q _) with (@plus Q _).
        srapply F_ind2; intros q r; cbv beta.
        symmetry; apply div_unique.
        change ((frac_to_field q + frac_to_field r)
                  * z_to_field (den q * den r)
                = z_to_field (num q * den r + num r * den q)).
        rewrite (preserves_plus (f:=z_to_field) (num q * den r)).
        rewrite (preserves_mult (f:=z_to_field) (num q)).
        rewrite (preserves_mult (f:=z_to_field) (num r)).
        rewrite (preserves_mult (f:=z_to_field) (den q)).
        rewrite plus_mult_distr_r.
        apply ap011.
        + rewrite mult_assoc; apply (ap (.* _)), div_mult_cancel.
        + rewrite (mult_comm (z_to_field (den q))), mult_assoc.
          apply (ap (.* _)), div_mult_cancel.
      - apply field_div_0_l, (preserves_0 (f:=z_to_field)).
      - change (@sg_op B _) with (@mult B _);
          change (@sg_op Q _) with (@mult Q _).
        srapply F_ind2; intros q r; cbv beta.
        symmetry; apply div_unique.
        change ((frac_to_field q * frac_to_field r)
                  * z_to_field (den q * den r)
                = z_to_field (num q * num r)).
        rewrite !(preserves_mult (f:=z_to_field)), mult_interchange.
        apply ap011; apply div_mult_cancel.
      - apply field_div_diag; reflexivity.
    Defined.

    Definition q_to_field_unique (h : Q -> B) `{!IsSemiRingPreserving h}
      (x : Q)
      : q_to_field x = h x.
    Proof.
      revert x; srapply F_ind; intros q; cbv beta.
      symmetry; apply div_unique.
      change (h (cast Fr Q q) * z_to_field (den q) = z_to_field (num q)).
      pose (i := inject : Z -> Q).
      pose proof (compose_sr_morphism i h _ _).
      lhs exact (ap (h (' q) *.) (z_to_field_unique (h o i) (den q))^).
      rhs exact (z_to_field_unique (h o i) (num q))^.
      lhs_V exact (preserves_mult (f:=h) (' q) (i (den q))).
      apply (ap h), path.
      change (num q * den q * 1 = num q * (den q * 1)).
      rewrite !mult_1_r; reflexivity.
    Defined.

  End to_field.

  #[export] Instance Q_to_field : RationalsToField Q
    := fun B _ _ _ _ _ _ _ _ _ => q_to_field B.

  #[export] Instance Q_rationals : Rationals Q.
  Proof.
    split.
    - exact _.
    - exact _.
    - intros B; exact _.
    - intros B ? ? ? ? ? ? ? ? ? h ? x; exact (q_to_field_unique B h x).
  Defined.

  (** ** Further properties of the order *)

  #[export] Instance Q_lt_dec (x y : Q) : Decidable (x < y).
  Proof.
    unfold lt, Q_lt, QPos; exact _.
  Defined.

  #[export] Instance Q_le_dec (x y : Q) : Decidable (x ≤ y).
  Proof.
    unfold le, Q_le; exact _.
  Defined.

  #[export] Instance Q_1_apart_0 : PropHolds ((1 : Q) ≶ 0)
    := decfield_nontrivial Q.

  (** ** Rounding up *)

  Local Existing Instance nat_full.

  Local Notation nZ := (naturals_to_semiring nat Z).

  Local Definition z_round_up (z : Z) : {k : nat & z < nZ k}.
  Proof.
    destruct (nat_int_to_semiring z) as [m e].
    assert (le : z ≤ nZ m).
    { destruct e as [e | e].
      - rewrite e; reflexivity.
      - transitivity 0.
        + rewrite <- e.
          apply nonneg_plus_le_compat_r, to_semiring_nonneg.
        + apply to_semiring_nonneg. }
    exists (S m).
    apply (le_lt_trans _ _ _ le).
    refine (transport (fun t => nZ m < t)
              (preserves_plus (f:=nZ) 1%nat m
               @ ap (+ nZ m) (preserves_1 (f:=nZ)))^ _).
    apply pos_plus_lt_compat_l, lt_0_1.
  Defined.

  Local Definition nat_to_q_frac (k : nat)
    : naturals_to_semiring nat Q k = ' (Frac_inject _ (nZ k)).
  Proof.
    pose proof (compose_sr_morphism nZ (inject : Z -> Q) _ _).
    exact (toR_unique ((inject : Z -> Q) o nZ) k).
  Defined.

  #[export] Instance Q_round_up_strict : RoundUpStrict Q.
  Proof.
    intros a.
    apply (minimal_n (fun n => a < naturals_to_semiring nat Q n) _).
    revert a; srapply F_ind; intros q; cbv beta.
    destruct (z_round_up (num q * den q)) as [k l].
    apply tr; exists k.
    unfold lt, Q_lt; rewrite nat_to_q_frac.
    apply (qpos_class (pl _ (Frac_inject _ (nZ k)) (neg _ q))).
    unfold frac_pos.
    change (0 < (nZ k * den q + - num q * 1) * (1 * den q)).
    rewrite mult_1_l, mult_1_r, plus_mult_distr_r, <- mult_assoc,
      <- negate_mult_distr_l.
    apply (snd (flip_pos_minus _ _)).
    apply (lt_le_trans _ _ _ l).
    apply ge_1_mult_le_compat_r.
    - apply pos_ge_1, den_square_pos.
    - apply to_semiring_nonneg.
    - reflexivity.
  Defined.

  (** ** Enumerations *)

  Local Definition z_enum (n : nat) : Z
    := ' (NatPair.PairT.C (fst (nat_unpair n)) (snd (nat_unpair n))).

  Local Instance issurj_z_enum : IsSurjection z_enum.
  Proof.
    apply BuildIsSurjection.
    srapply (NatPair.Z_ind nat); intros [a b].
    apply tr; exists (nat_unpair_section a b).1.
    unfold z_enum; by rewrite (nat_unpair_section a b).2.
  Defined.

  Local Definition q_of_pair (nd : Z * Z) : Q.
  Proof.
    destruct (dec (snd nd = 0)) as [_ | nz].
    - exact 0.
    - exact (' (frac (fst nd) (snd nd) nz)).
  Defined.

  Local Definition q_enum (n : nat) : Q
    := q_of_pair (z_enum (fst (nat_unpair n)), z_enum (snd (nat_unpair n))).

  Local Instance issurj_q_enum : IsSurjection q_enum.
  Proof.
    apply BuildIsSurjection.
    srapply F_ind; intros [n d nz].
    pose proof (@center _ (issurj_nat_pair z_enum z_enum (n, d))) as h.
    strip_truncations; apply tr.
    destruct h as [k p]; exists k.
    unfold q_enum; rewrite p; unfold q_of_pair; cbn.
    destruct (dec (d = 0)) as [z | nz'].
    - destruct (nz z).
    - apply path; reflexivity.
  Defined.

  #[export] Instance Q_enumerable : Enumerable Q
    := {| enumerator := q_enum |}.

  (** The maximum of the first [N] values of a sequence. *)
  Local Fixpoint q_max_prefix (f : nat -> Q) (N : nat) : Q
    := match N with
       | O => 0
       | S N => if dec (q_max_prefix f N ≤ f N) then f N
                else q_max_prefix f N
       end.

  Local Definition q_max_prefix_le (f : nat -> Q) (N : nat)
    : forall m, (m < N)%nat -> f m ≤ q_max_prefix f N.
  Proof.
    induction N as [|N IH].
    1: intros m l; destruct (not_lt_zero_r _ l).
    intros m l.
    change (f m ≤ (if dec (q_max_prefix f N ≤ f N) then f N
                   else q_max_prefix f N)).
    destruct (dec (q_max_prefix f N ≤ f N)) as [c | c];
      destruct (equiv_leq_lt_or_eq (leq_pred' l)) as [l' | e].
    - exact (transitivity (IH m l') c).
    - destruct e; reflexivity.
    - exact (IH m l').
    - destruct e; apply lt_le, not_le_lt_flip, c.
  Defined.

  Local Definition q_fresh (f : nat -> Q) (N : nat)
    : {a : Q & forall m, (m < N)%nat -> f m <> a}.
  Proof.
    exists (q_max_prefix f N + 1).
    intros m l; apply lt_ne.
    apply (le_lt_trans _ _ _ (q_max_prefix_le f N m l)).
    apply pos_plus_lt_compat_r, lt_0_1.
  Defined.

  Definition equiv_nat_rationals : nat <~> Q
    := equiv_nat_surjection_fresh q_enum (q_fresh q_enum).

  #[export] Instance decidablepaths_qpos : DecidablePaths (Qpos Q).
  Proof.
    intros a b.
    destruct (dec (' a = ' b :> Q)) as [p | np].
    - exact (inl (pos_eq a b p)).
    - right; intros p; exact (np (ap pos p)).
  Defined.

  Local Instance decidablepaths_q_qpos : DecidablePaths (Q * Qpos Q).
  Proof.
    intros x y; exact (decidable_equiv' _ (equiv_path_prod x y) _).
  Defined.

  Local Definition q_qpos_enum (n : nat) : Q * Qpos Q
    := (enumerator Q (fst (nat_unpair n)),
        enumerator (Qpos Q) (snd (nat_unpair n))).

  Local Definition q_qpos_fresh (f : nat -> Q * Qpos Q) (N : nat)
    : {a : Q * Qpos Q & forall m, (m < N)%nat -> f m <> a}.
  Proof.
    exists ((q_fresh (fst o f) N).1, 1).
    intros m l p.
    exact ((q_fresh (fst o f) N).2 m l (ap fst p)).
  Defined.

  Definition equiv_nat_rationals_qpos : nat <~> Q * Qpos Q
    := equiv_nat_surjection_fresh q_qpos_enum
         (es := issurj_nat_pair _ _) (q_qpos_fresh q_qpos_enum).

End model.

(** * The analysis results at this model

All hypotheses on [Q] are found by typeclass search or given by the enumerations above; the ordered field [F] stays abstract. *)

Definition test_locator_times `{Funext} `{Univalence}
  (F : Type) `{OrderedField F} {Farch : ArchimedeanProperty Q F} (x y : F)
  := locator_times Q F equiv_nat_rationals (x:=x) (y:=y).

Definition test_exact_ivt `{Funext} `{Univalence}
  (F : Type) `{OrderedField F} {Farch : ArchimedeanProperty Q F}
  := exact_ivt Q F equiv_nat_rationals equiv_nat_rationals_qpos.

Definition test_merely_locator_iff_signed_digits `{Funext} `{Univalence}
  (F : Type) `{OrderedField F} {Farch : ArchimedeanProperty Q F}
  := merely_locator_iff_signed_digits Q F equiv_nat_rationals Z.

Definition test_banach_fixed_point `{Funext} `{Univalence}
  (F : Type) `{OrderedField F} {X : Type} (d : X -> X -> F)
  `{!IsPseudoMetric d}
  := banach_fixed_point Q d.

Definition test_rationals_to_cauchy_reals `{Funext} `{Univalence}
  : Q -> CauchyReals Q
  := rationals_to_cauchy_reals Q.

Definition test_rational_1_apart_0 `{Funext} `{Univalence}
  : PropHolds ((1 : Q) ≶ 0)
  := _.
