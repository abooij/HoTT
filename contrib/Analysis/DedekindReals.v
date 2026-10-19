(** * Dedekind reals *)

(** The Dedekind reals over a model [Q] of the rationals: pairs of a lower and an upper cut, predicates on [Q] that are inhabited, rounded, transitive and located.  We show that they form a set and an Archimedean ordered field, and that they are Cauchy complete, with the limit given by an explicit cut. *)

From HoTT Require Import Basics Spaces.Nat.Core Types.Sigma Types.Forall Types.Sum Types.Universe
  Truncations.Core Universes.HProp Universes.TruncType.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  theory.apartness
  theory.rings
  theory.dec_fields
  theory.rationals
  interfaces.naturals
  interfaces.round
  implementations.peano_naturals
  orders.naturals
  orders.orders
  orders.rings
  orders.dec_fields
  interfaces.archimedean
  interfaces.cauchy.
From HoTT.Analysis Require Import Locator.

Section dedekind.
  Context `{Funext} `{Univalence}.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    {Qroundup : RoundUpStrict Q}.

  Local Notation nQ := (naturals_to_semiring nat Q).

  (** ** Dedekind cuts *)

  (** The properties of a pair of predicates that make it a Dedekind cut: both are inhabited and rounded, every element of the lower cut is below every element of the upper cut, and every pair [q < r] has [q] in the lower cut or [r] in the upper cut.  We write [q < x] for [lower_cut x q] and [x < r] for [upper_cut x r] in comments. *)
  Record IsDedekindCut (lower upper : Q -> HProp) := {
    cut_lower_inhabited : hexists lower ;
    cut_upper_inhabited : hexists upper ;
    cut_lower_rounded : forall q, lower q <-> hexists (fun q' => prod (q < q') (lower q')) ;
    cut_upper_rounded : forall r, upper r <-> hexists (fun r' => prod (r' < r) (upper r')) ;
    cut_transitive : forall q r, lower q -> upper r -> q < r ;
    cut_located : forall q r, q < r -> hor (lower q) (upper r) }.

  Arguments cut_lower_inhabited {lower upper} _.
  Arguments cut_upper_inhabited {lower upper} _.
  Arguments cut_lower_rounded {lower upper} _ _.
  Arguments cut_upper_rounded {lower upper} _ _.
  Arguments cut_transitive {lower upper} _ _ _ _ _.
  Arguments cut_located {lower upper} _ _ _ _.

  Definition issig_isdedekindcut (lower upper : Q -> HProp)
    : _ <~> IsDedekindCut lower upper := ltac:(issig).

  #[export] Instance ishprop_isdedekindcut (lower upper : Q -> HProp) : IsHProp (IsDedekindCut lower upper).
  Proof.
    exact (istrunc_equiv_istrunc _ (issig_isdedekindcut lower upper)).
  Qed.

  (** A Dedekind real is a pair of a lower and an upper cut, with a proof that they form a Dedekind cut. *)
  Record DedekindReals := {
    lower_cut : Q -> HProp ;
    upper_cut : Q -> HProp ;
    isdedekindcut : IsDedekindCut lower_cut upper_cut }.

  Local Notation R := DedekindReals.

  (** Basic properties of the cuts. *)
  Section cut_lemmas.
    Context (x : R).

    Definition lower_cut_rounded := cut_lower_rounded (isdedekindcut x).
    Definition upper_cut_rounded := cut_upper_rounded (isdedekindcut x).

    Lemma lower_cut_lt (q q' : Q) : q < q' -> lower_cut x q' -> lower_cut x q.
    Proof.
      intros l p; apply (snd (lower_cut_rounded q)), tr; exact (q'; (l, p)).
    Qed.

    Lemma upper_cut_lt (r r' : Q) : r' < r -> upper_cut x r' -> upper_cut x r.
    Proof.
      intros l p; apply (snd (upper_cut_rounded r)), tr; exact (r'; (l, p)).
    Qed.

    Lemma lower_cut_le (q q' : Q) : q <= q' -> lower_cut x q' -> lower_cut x q.
    Proof.
      intros l p; destruct (le_equiv_lt q q' l) as [e|l'].
      - rewrite e; exact p.
      - exact (lower_cut_lt q q' l' p).
    Qed.

    Lemma upper_cut_le (r r' : Q) : r' <= r -> upper_cut x r' -> upper_cut x r.
    Proof.
      intros l p; destruct (le_equiv_lt r' r l) as [e|l'].
      - rewrite <- e; exact p.
      - exact (upper_cut_lt r r' l' p).
    Qed.

    Lemma cut_disjoint (q : Q) : lower_cut x q -> upper_cut x q -> Empty.
    Proof.
      intros p p'; exact (irreflexivity (<) q (cut_transitive (isdedekindcut x) q q p p')).
    Qed.
  End cut_lemmas.

  (** ** Paths between Dedekind reals *)

  Definition path_dedekindreals_cuts (x y : R)
    : lower_cut x = lower_cut y -> upper_cut x = upper_cut y -> x = y.
  Proof.
    destruct x as [lx ux c], y as [ly uy c']; cbn.
    intros p q; destruct p, q; exact (ap (Build_DedekindReals lx ux) (path_ishprop c c')).
  Defined.

  (** The type of Dedekind reals is a set. *)
  #[export] Instance ishset_dedekindreals : IsHSet R.
  Proof.
    apply (istrunc_equiv_istrunc {lower : Q -> HProp & {upper : Q -> HProp & IsDedekindCut lower upper}}).
    - make_equiv.
    - exact _.
  Qed.

  (** A Dedekind real is determined by its lower cut, and also by its upper cut, so inclusions of both cuts suffice. *)
  Lemma lower_cut_incl_rev (x y : R)
    (ll : forall q, lower_cut x q -> lower_cut y q) (uu : forall r, upper_cut x r -> upper_cut y r)
    (q : Q) : lower_cut y q -> lower_cut x q.
  Proof.
    intros p; apply (lower_cut_rounded y q) in p; strip_truncations; destruct p as [q' [l p]].
    assert (c := cut_located (isdedekindcut x) q q' l); strip_truncations; destruct c as [c|c].
    - exact c.
    - destruct (cut_disjoint y q' p (uu q' c)).
  Qed.

  Lemma upper_cut_incl_rev (x y : R)
    (ll : forall q, lower_cut x q -> lower_cut y q) (uu : forall r, upper_cut x r -> upper_cut y r)
    (r : Q) : upper_cut y r -> upper_cut x r.
  Proof.
    intros p; apply (upper_cut_rounded y r) in p; strip_truncations; destruct p as [r' [l p]].
    assert (c := cut_located (isdedekindcut x) r' r l); strip_truncations; destruct c as [c|c].
    - destruct (cut_disjoint y r' (ll r' c) p).
    - exact c.
  Qed.

  Definition path_dedekindreals (x y : R)
    (ll : forall q, lower_cut x q -> lower_cut y q) (uu : forall r, upper_cut x r -> upper_cut y r)
    : x = y.
  Proof.
    apply path_dedekindreals_cuts; apply path_forall; intros q; apply path_iff_hprop.
    - apply ll.
    - apply (lower_cut_incl_rev x y ll uu).
    - apply uu.
    - apply (upper_cut_incl_rev x y ll uu).
  Defined.

  (** ** Approximation *)

  Local Lemma pos_quarter_double (e : Qpos Q) : ' (e / 2 / 2) + ' (e / 2 / 2) < ' e.
  Proof.
    change (' (e / 2 / 2 + e / 2 / 2) < ' e); rewrite <- pos_split2.
    apply (transport (fun z => ' (e / 2) < ' z) (pos_split2 e)^).
    apply pos_plus_lt_compat_r, is_pos.
  Qed.

  Local Lemma plus_minus_cancel_l (a b : Q) : (a + b) - a = b.
  Proof.
    rewrite (plus_comm a), <- plus_assoc, plus_negate_r; apply plus_0_r.
  Qed.

  (** A Dedekind cut has a lower and an upper bound arbitrarily close to each other: walk up from a lower bound in steps of [e / 4], using locatedness at each step. *)
  Lemma cut_approximate (x : R) (e : Qpos Q)
    : merely {a : Q & {b : Q & prod (prod (lower_cut x a) (upper_cut x b)) (b - a < ' e)}}.
  Proof.
    assert (a0 := cut_lower_inhabited (isdedekindcut x)).
    assert (b0 := cut_upper_inhabited (isdedekindcut x)).
    strip_truncations; destruct a0 as [a0 la0], b0 as [b0 ub0].
    refine (Trunc_functor (-1) _ (located_close (Tr (-1)) (lower_cut x) (upper_cut x)
              (cut_located (isdedekindcut x)) (cut_transitive (isdedekindcut x))
              (' (e / 2 / 2)) (is_pos _) a0 b0 la0 ub0)).
    intros [a [la ub]]; exists a, (a + ' (e / 2 / 2) + ' (e / 2 / 2)); refine ((la, ub), _).
    rewrite <- (plus_assoc a), plus_minus_cancel_l; exact (pos_quarter_double e).
  Qed.

  (** ** Rationals *)

  Local Definition Qlt_hprop (q r : Q) : HProp := Build_HProp (q < r).

  (** The rational [q] has the lower cut [s < q] and the upper cut [q < s]. *)
  Lemma isdedekindcut_rational (q : Q)
    : IsDedekindCut (fun s => Qlt_hprop s q) (fun s => Qlt_hprop q s).
  Proof.
    split; cbn.
    - apply tr; exists (q - 1); exact (fst (pos_minus_lt_compat_r q 1) lt_0_1).
    - apply tr; exists (q + 1); exact (fst (pos_plus_lt_compat_r q 1) lt_0_1).
    - intros s; split.
      + intros l; apply tr; destruct (Q_dense s q l) as [s' ls]; exact (s'; ls).
      + intros l; strip_truncations; destruct l as [s' [l1 l2]]; exact (transitivity l1 l2).
    - intros s; split.
      + intros l; apply tr; destruct (Q_dense q s l) as [s' [l1 l2]]; exact (s'; (l2, l1)).
      + intros l; strip_truncations; destruct l as [s' [l1 l2]]; exact (transitivity l2 l1).
    - intros s t l1 l2; exact (transitivity l1 l2).
    - intros s t l; exact (cotransitive l q).
  Qed.

  Definition rational_dedekind (q : Q) : R
    := Build_DedekindReals _ _ (isdedekindcut_rational q).

  (** ** Order *)

  (** [x < y] when a rational lies between them, and [x <= y] when the lower cut of [x] is contained in that of [y]. *)
  #[local] Instance lt_dedekindreals : Lt R
    := fun x y => hexists (fun q => prod (upper_cut x q) (lower_cut y q)).

  #[local] Instance le_dedekindreals : Le R
    := fun x y => forall q, lower_cut x q -> lower_cut y q.

  #[local] Instance apart_dedekindreals : Apart R
    := fun x y => hor (x < y) (y < x).

  #[export] Instance ishprop_lt_dedekindreals : is_mere_relation R lt := _.
  #[export] Instance ishprop_le_dedekindreals : is_mere_relation R le := _.
  #[export] Instance ishprop_apart_dedekindreals : is_mere_relation R apart := _.

  Lemma lt_rational_dedekind_l (q : Q) (x : R) : rational_dedekind q < x <-> lower_cut x q.
  Proof.
    split.
    - intros l; strip_truncations; destruct l as [s [l p]]; exact (lower_cut_lt x q s l p).
    - intros p; apply (lower_cut_rounded x q) in p; strip_truncations.
      destruct p as [s [l p]]; exact (tr (s; (l, p))).
  Qed.

  Lemma lt_rational_dedekind_r (r : Q) (x : R) : x < rational_dedekind r <-> upper_cut x r.
  Proof.
    split.
    - intros l; strip_truncations; destruct l as [s [p l]]; exact (upper_cut_lt x r s l p).
    - intros p; apply (upper_cut_rounded x r) in p; strip_truncations.
      destruct p as [s [l p]]; exact (tr (s; (p, l))).
  Qed.

  Lemma le_iff_not_lt_dedekindreals (x y : R) : x <= y <-> ~ (y < x).
  Proof.
    split.
    - intros l l'; strip_truncations; destruct l' as [q [u p]].
      exact (cut_disjoint y q (l q p) u).
    - intros nl q p.
      apply (lower_cut_rounded x q) in p; strip_truncations; destruct p as [q' [l p]].
      assert (c := cut_located (isdedekindcut y) q q' l); strip_truncations.
      destruct c as [c|c]; [exact c|].
      destruct (nl (tr (q'; (c, p)))).
  Qed.


  (** ** The strict order *)

  Definition path_dedekindreals_lower (x y : R)
    (l : forall q, lower_cut x q -> lower_cut y q) (l' : forall q, lower_cut y q -> lower_cut x q)
    : x = y.
  Proof.
    apply (path_dedekindreals x y l).
    intros r u; apply (upper_cut_rounded x r) in u; strip_truncations; destruct u as [r' [lr u]].
    assert (c := cut_located (isdedekindcut y) r' r lr); strip_truncations.
    destruct c as [c|c]; [destruct (cut_disjoint x r' (l' r' c) u)|exact c].
  Defined.

  Lemma lt_dedekindreals_irrefl (x : R) : ~ (x < x).
  Proof.
    intros l; strip_truncations; destruct l as [q [u p]]; exact (cut_disjoint x q p u).
  Qed.

  Lemma lt_dedekindreals_antisym (x y : R) : ~ (prod (x < y) (y < x)).
  Proof.
    intros [l l']; strip_truncations; destruct l as [q [uq lq]], l' as [r [ur lr]].
    apply (irreflexivity (<) q), (transitivity (y:=r)).
    - exact (cut_transitive (isdedekindcut y) _ _ lq ur).
    - exact (cut_transitive (isdedekindcut x) _ _ lr uq).
  Qed.

  Lemma lt_dedekindreals_cotrans (x y : R) : x < y -> forall z, hor (x < z) (z < y).
  Proof.
    intros l z; strip_truncations; destruct l as [q [uq lq]].
    apply (upper_cut_rounded x q) in uq; strip_truncations; destruct uq as [q' [l uq']].
    assert (c := cut_located (isdedekindcut z) q' q l); strip_truncations.
    destruct c as [c|c]; apply tr; [left|right]; apply tr.
    - exact (q'; (uq', c)).
    - exact (q; (c, lq)).
  Qed.

  Lemma lt_dedekindreals_trans (x y z : R) : x < y -> y < z -> x < z.
  Proof.
    intros l l'; strip_truncations; destruct l as [q [uq lq]], l' as [r [ur lr]].
    apply tr; exists q; split; [exact uq|].
    exact (lower_cut_lt z q r (cut_transitive (isdedekindcut y) _ _ lq ur) lr).
  Qed.

  #[export] Instance isapart_dedekindreals : IsApart R.
  Proof.
    split.
    - exact _.
    - exact _.
    - intros x y a; strip_truncations; apply tr; destruct a as [a|a]; [right|left]; exact a.
    - intros x y a z; strip_truncations; destruct a as [a|a].
      + assert (c := lt_dedekindreals_cotrans x y a z); strip_truncations.
        apply tr; destruct c as [c|c]; [left|right]; apply tr; left; exact c.
      + assert (c := lt_dedekindreals_cotrans y x a z); strip_truncations.
        apply tr; destruct c as [c|c]; [right|left]; apply tr; right; exact c.
    - intros x y; split.
      + intros na; apply path_dedekindreals_lower.
        * apply (snd (le_iff_not_lt_dedekindreals x y)); intros l; exact (na (tr (inr l))).
        * apply (snd (le_iff_not_lt_dedekindreals y x)); intros l; exact (na (tr (inl l))).
      + intros [] a; strip_truncations; destruct a as [a|a]; exact (lt_dedekindreals_irrefl x a).
  Qed.

  #[export] Instance pseudoorder_dedekindreals : PseudoOrder (_ : Lt R).
  Proof.
    split.
    - exact _.
    - exact _.
    - exact lt_dedekindreals_antisym.
    - exact lt_dedekindreals_cotrans.
    - intros x y; split.
      + intros a; refine (Trunc_rec idmap a).
        apply ishprop_sum; [exact _|exact _|].
        intros l l'; exact (lt_dedekindreals_antisym x y (l, l')).
      + exact tr.
  Qed.

  #[export] Instance fullpseudoorder_dedekindreals : FullPseudoOrder (_ : Le R) (_ : Lt R).
  Proof.
    split.
    - exact _.
    - exact _.
    - exact le_iff_not_lt_dedekindreals.
  Qed.


  (** ** Cuts from located pairs of predicates *)

  (** Rounding is the only property of a Dedekind cut which is tedious to check for the operations below. We obtain it once and for all: if [BL] and [BU] are inhabited, every element of [BL] is below every element of [BU], and for [q < r] we merely have [BL q] or [BU r], then taking all rationals strictly below [BL] and strictly above [BU] gives a Dedekind cut. *)
  Section rounded.
    Context (BL BU : Q -> Type).

    Definition rounded_lower (q : Q) : HProp
      := Build_HProp (hexists (fun q' => prod (q < q') (BL q'))).
    Definition rounded_upper (r : Q) : HProp
      := Build_HProp (hexists (fun r' => prod (r' < r) (BU r'))).

    Lemma isdedekindcut_rounded (inhL : hexists BL) (inhU : hexists BU)
      (below : forall q r, BL q -> BU r -> q <= r) (loc : forall q r, q < r -> hor (BL q) (BU r))
      : IsDedekindCut rounded_lower rounded_upper.
    Proof.
      split.
      - strip_truncations; destruct inhL as [q l].
        exact (tr (q - 1; tr (q; (fst (pos_minus_lt_compat_r q 1) lt_0_1, l)))).
      - strip_truncations; destruct inhU as [r u].
        exact (tr (r + 1; tr (r; (fst (pos_plus_lt_compat_r r 1) lt_0_1, u)))).
      - intros q; split.
        + apply Trunc_functor; intros [q' [ltq l]].
          destruct (Q_dense q q' ltq) as [m [ltqm ltmq']].
          exact (m; (ltqm, tr (q'; (ltmq', l)))).
        + intros p; strip_truncations; destruct p as [m [ltqm p]].
          refine (Trunc_functor (-1) _ p); intros [q' [ltmq' l]].
          exact (q'; (transitivity ltqm ltmq', l)).
      - intros r; split.
        + apply Trunc_functor; intros [r' [ltr u]].
          destruct (Q_dense r' r ltr) as [m [ltr'm ltmr]].
          exact (m; (ltmr, tr (r'; (ltr'm, u)))).
        + intros p; strip_truncations; destruct p as [m [ltmr p]].
          refine (Trunc_functor (-1) _ p); intros [r' [ltr'm u]].
          exact (r'; (transitivity ltr'm ltmr, u)).
      - intros q r p p'; strip_truncations.
        destruct p as [q' [ltq l]], p' as [r' [ltr u]].
        exact (transitivity ltq (le_lt_trans _ _ _ (below _ _ l u) ltr)).
      - intros q r ltqr.
        destruct (Q_dense q r ltqr) as [q' [ltqq' ltq'r]].
        destruct (Q_dense q' r ltq'r) as [r' [ltq'r' ltr'r]].
        refine (Trunc_functor (-1) _ (loc q' r' ltq'r')); intros [l|u].
        + exact (inl (tr (q'; (ltqq', l)))).
        + exact (inr (tr (r'; (ltr'r, u)))).
    Qed.
  End rounded.

  (** ** Rational bounds *)

  (** Two lower bounds of a real have a common upper bound that is a lower bound, and dually. *)
  Lemma lower_cut_max (x : R) (a a' : Q) : lower_cut x a -> lower_cut x a'
    -> {c : Q & prod (lower_cut x c) (prod (a <= c) (a' <= c))}.
  Proof.
    intros la la'; destruct (le_or_lt a a') as [l|l].
    - exact (a'; (la', (l, reflexivity a'))).
    - exact (a; (la, (reflexivity a, lt_le _ _ l))).
  Qed.

  Lemma upper_cut_min (x : R) (b b' : Q) : upper_cut x b -> upper_cut x b'
    -> {c : Q & prod (upper_cut x c) (prod (c <= b) (c <= b'))}.
  Proof.
    intros ub ub'; destruct (le_or_lt b b') as [l|l].
    - exact (b; (ub, (reflexivity b, l))).
    - exact (b'; (ub', (lt_le _ _ l, reflexivity b'))).
  Qed.

  (** Rational bounds of a real. *)
  Record CutBounds (x : R) := {
    bound_lo : Q ;
    bound_hi : Q ;
    bound_lo_lower : lower_cut x bound_lo ;
    bound_hi_upper : upper_cut x bound_hi }.

  Arguments bound_lo {x} _.
  Arguments bound_hi {x} _.
  Arguments bound_lo_lower {x} _.
  Arguments bound_hi_upper {x} _.

  Definition in_bounds {x : R} (I : CutBounds x) (s : Q) : Type
    := prod (bound_lo I <= s) (s <= bound_hi I).

  Section bounds.
    Context {x : R}.

    Lemma merely_cutbounds : merely (CutBounds x).
    Proof.
      assert (a := cut_lower_inhabited (isdedekindcut x)).
      assert (b := cut_upper_inhabited (isdedekindcut x)); strip_truncations.
      exact (tr (Build_CutBounds x a.1 b.1 a.2 b.2)).
    Qed.

    Lemma bound_lo_lt_hi (I : CutBounds x) : bound_lo I < bound_hi I.
    Proof.
      exact (cut_transitive (isdedekindcut x) _ _ (bound_lo_lower I) (bound_hi_upper I)).
    Qed.

    Lemma in_bounds_lo (I : CutBounds x) : in_bounds I (bound_lo I).
    Proof.
      exact (reflexivity _, lt_le _ _ (bound_lo_lt_hi I)).
    Qed.

    Lemma in_bounds_hi (I : CutBounds x) : in_bounds I (bound_hi I).
    Proof.
      exact (lt_le _ _ (bound_lo_lt_hi I), reflexivity _).
    Qed.

    (** Two pairs of bounds can be refined to a pair inside both. *)
    Lemma cutbounds_intersect (I I' : CutBounds x)
      : {I'' : CutBounds x & forall s, in_bounds I'' s -> prod (in_bounds I s) (in_bounds I' s)}.
    Proof.
      destruct (lower_cut_max x _ _ (bound_lo_lower I) (bound_lo_lower I')) as [a [la [l1 l2]]].
      destruct (upper_cut_min x _ _ (bound_hi_upper I) (bound_hi_upper I')) as [b [ub [l3 l4]]].
      exists (Build_CutBounds x a b la ub); intros s [l5 l6]; cbn in l5, l6.
      split; split.
      - exact (transitivity l1 l5).
      - exact (transitivity l6 l3).
      - exact (transitivity l2 l5).
      - exact (transitivity l6 l4).
    Qed.

    (** There are bounds inside given ones which are less than [e] apart. *)
    Lemma merely_cutbounds_close (I : CutBounds x) (e : Qpos Q)
      : merely {J : CutBounds x & prod (forall s, in_bounds J s -> in_bounds I s)
                                    (bound_hi J - bound_lo J < ' e)}.
    Proof.
      refine (Trunc_functor (-1) _ (cut_approximate x e)); intros [a [b [[la ub] lab]]].
      destruct (cutbounds_intersect I (Build_CutBounds x a b la ub)) as [J HJ].
      exists J; split; [exact (fun s i => fst (HJ s i))|].
      refine (le_lt_trans _ _ _ _ lab).
      apply plus_le_compat.
      - exact (snd (snd (HJ _ (in_bounds_hi J)))).
      - apply (snd (flip_le_negate _ _)); exact (fst (snd (HJ _ (in_bounds_lo J)))).
    Qed.
  End bounds.

  (** Two points of an interval of width less than [D] are less than [D] apart. *)
  Local Lemma interval_close (a b s s' D : Q) : a <= s -> s <= b -> a <= s' -> s' <= b -> b - a < D
    -> prod (- D < s - s') (s - s' < D).
  Proof.
    intros l1 l2 l3 l4 lD; split.
    - apply flip_lt_negate_l; rewrite <- negate_swap_r.
      apply (le_lt_trans _ (b - a)); [|exact lD].
      apply plus_le_compat; [exact l4|exact (snd (flip_le_negate _ _) l1)].
    - apply (le_lt_trans _ (b - a)); [|exact lD].
      apply plus_le_compat; [exact l2|exact (snd (flip_le_negate _ _) l3)].
  Qed.

  (** ** Extending operations on the rationals *)

  (** Two rationals are [e]-close when their difference is less than [e] in absolute value. *)
  Local Notation close e s s' := (- ' e < s - s' < ' e).

  Local Lemma close_lt_l (e : Qpos Q) (u v : Q) : close e u v -> u - ' e < v.
  Proof.
    intros [_ h]; apply flip_lt_minus_l; rewrite plus_comm; exact (fst (flip_lt_minus_l _ _ _) h).
  Qed.

  Local Lemma close_lt_r (e : Qpos Q) (u v : Q) : close e u v -> v < u + ' e.
  Proof.
    intros [h _]; apply flip_lt_minus_l; rewrite plus_comm; exact (fst (flip_lt_minus_r _ _ _) h).
  Qed.

  (** A binary operation on the rationals is locally uniformly continuous if on every box it has a modulus of uniform continuity. *)
  Class IsLocallyUniform (f : Q -> Q -> Q)
    := locally_uniform : forall (a b c d : Q) (e : Qpos Q), hexists (fun w : Qpos Q =>
         forall s s' t t', a ≤ s ≤ b -> a ≤ s' ≤ b -> c ≤ t ≤ d -> c ≤ t' ≤ d
           -> close w s s' -> close w t t' -> close e (f s t) (f s' t')).

  Section extension.
    Context (f : Q -> Q -> Q) (x y : R).

    (** [f] is at least [q] on a box of rational bounds, and at most [r]. *)
    Definition BoxAbove (q : Q) : Type
      := hexists (fun I : CutBounds x => hexists (fun J : CutBounds y =>
           forall s t, in_bounds I s -> in_bounds J t -> q <= f s t)).
    Definition BoxBelow (r : Q) : Type
      := hexists (fun I : CutBounds x => hexists (fun J : CutBounds y =>
           forall s t, in_bounds I s -> in_bounds J t -> f s t <= r)).

    (** Two boxes intersect, since both contain [(x, y)]. *)
    Lemma boxabove_le_boxbelow (q r : Q) : BoxAbove q -> BoxBelow r -> q <= r.
    Proof.
      intros p p'; strip_truncations; destruct p as [I p], p' as [I' p']; strip_truncations.
      destruct p as [J p], p' as [J' p'].
      destruct (cutbounds_intersect I I') as [I'' HI], (cutbounds_intersect J J') as [J'' HJ].
      destruct (HI _ (in_bounds_lo I'')) as [i i'], (HJ _ (in_bounds_lo J'')) as [j j'].
      exact (transitivity (p _ _ i j) (p' _ _ i' j')).
    Qed.

    Context `{!IsLocallyUniform f}.

    (** Small boxes: on some box, all values of [f] are [e]-close. *)
    Lemma merely_box_close (e : Qpos Q)
      : merely {I : CutBounds x & {J : CutBounds y & forall s s' t t',
          in_bounds I s -> in_bounds I s' -> in_bounds J t -> in_bounds J t'
          -> close e (f s t) (f s' t')}}.
    Proof.
      assert (I0 := @merely_cutbounds x); assert (J0 := @merely_cutbounds y); strip_truncations.
      assert (w := locally_uniform (bound_lo I0) (bound_hi I0) (bound_lo J0) (bound_hi J0) e).
      strip_truncations; destruct w as [w fw].
      assert (I := merely_cutbounds_close I0 w); assert (J := merely_cutbounds_close J0 w).
      strip_truncations; destruct I as [I [HI wI]], J as [J [HJ wJ]].
      apply tr; exists I, J; intros s s' t t' is is' it it'.
      apply fw; try (apply HI; assumption); try (apply HJ; assumption).
      - exact (interval_close _ _ _ _ _ (fst is) (snd is) (fst is') (snd is') wI).
      - exact (interval_close _ _ _ _ _ (fst it) (snd it) (fst it') (snd it') wJ).
    Qed.

    Lemma merely_boxabove : hexists BoxAbove.
    Proof.
      assert (h := merely_box_close 1); strip_truncations; destruct h as [I [J h]].
      apply tr; exists (f (bound_lo I) (bound_lo J) - 1); apply tr; exists I; apply tr; exists J.
      intros s t is it; apply lt_le; unfold PropHolds.
      exact (close_lt_l _ _ _ (h _ _ _ _ (in_bounds_lo I) is (in_bounds_lo J) it)).
    Qed.

    Lemma merely_boxbelow : hexists BoxBelow.
    Proof.
      assert (h := merely_box_close 1); strip_truncations; destruct h as [I [J h]].
      apply tr; exists (f (bound_lo I) (bound_lo J) + 1); apply tr; exists I; apply tr; exists J.
      intros s t is it; apply lt_le; unfold PropHolds.
      exact (close_lt_r _ _ _ (h _ _ _ _ (in_bounds_lo I) is (in_bounds_lo J) it)).
    Qed.

    (** For locatedness, we take a box on which the values of [f] are closer than [(r - q) / 2], and compare the value at a corner with the midpoint of [q] and [r]. *)
    Lemma box_located (q r : Q) : q < r -> hor (BoxAbove q) (BoxBelow r).
    Proof.
      intros ltqr; set (e := Qpos_diff q r ltqr / 2).
      assert (h := merely_box_close e); strip_truncations; destruct h as [I [J h]].
      set (v := f (bound_lo I) (bound_lo J)).
      assert (p : q + ' e + ' e = r).
      { rewrite <- plus_assoc; change (q + ' (e + e) = r).
        rewrite <- (pos_split2 (Qpos_diff q r ltqr)); symmetry; apply plus_conjugate_alt. }
      destruct (le_or_lt (q + ' e) v) as [lev|ltv]; apply tr; [left|right];
        apply tr; exists I; apply tr; exists J; intros s t is it; apply lt_le; unfold PropHolds.
      - refine (le_lt_trans _ _ _ _ (close_lt_l _ _ _ (h _ _ _ _ (in_bounds_lo I) is (in_bounds_lo J) it))).
        apply flip_le_minus_l; rewrite negate_involutive; exact lev.
      - rewrite <- p.
        lhs' exact (close_lt_r _ _ _ (h _ _ _ _ (in_bounds_lo I) is (in_bounds_lo J) it)).
        apply (strictly_order_preserving (+ _)); exact ltv.
    Qed.
  End extension.

  (** The extension of [f] to the Dedekind reals: [q < f x y] when [f] is above a number greater than [q] on a box around [(x, y)], and dually. *)
  Definition extend (f : Q -> Q -> Q) `{!IsLocallyUniform f} (x y : R) : R
    := Build_DedekindReals _ _
         (isdedekindcut_rounded (BoxAbove f x y) (BoxBelow f x y)
            (merely_boxabove f x y) (merely_boxbelow f x y) (boxabove_le_boxbelow f x y)
            (box_located f x y)).

  Local Notation "[ q ]" := (rational_dedekind q).

  (** ** Closeness *)

  (** Two Dedekind reals [x] and [y] are [e]-close if [q + e < x] implies [q < y] and vice versa, that is, if [|x - y| ≤ e]. *)
  Definition dedekind_close (e : Qpos Q) (x y : R) : Type
    := forall q, prod (lower_cut x (q + ' e) -> lower_cut y q) (lower_cut y (q + ' e) -> lower_cut x q).

  #[export] Instance ishprop_dedekind_close (e : Qpos Q) (x y : R) : IsHProp (dedekind_close e x y)
    := _.

  Lemma dedekind_close_weaken (e d : Qpos Q) (x y : R) (le : ' e <= ' d)
    : dedekind_close e x y -> dedekind_close d x y.
  Proof.
    assert (l : forall (z : R) q, lower_cut z (q + ' d) -> lower_cut z (q + ' e)).
    { intros z q; apply lower_cut_le, (order_preserving (q +)), le. }
    intros c q; split; intros p; [apply (fst (c q))|apply (snd (c q))]; exact (l _ _ p).
  Qed.

  Lemma dedekind_close_triangle (e d : Qpos Q) (x y z : R)
    : dedekind_close e x y -> dedekind_close d y z -> dedekind_close (e + d) x z.
  Proof.
    intros c c' q; change (q + (' e + ' d)) with (q + ' (e + d)); split; intros l.
    - apply (fst (c' q)), (fst (c (q + ' d))).
      rewrite <- plus_assoc, (plus_comm (' d)); exact l.
    - apply (snd (c q)), (snd (c' (q + ' e))).
      rewrite <- plus_assoc; exact l.
  Qed.

  (** Reals which are [e]-close for all [e] are equal. *)
  Lemma path_dedekind_close (x y : R) (c : forall e, dedekind_close e x y) : x = y.
  Proof.
    assert (l : forall (u v : R), (forall e, dedekind_close e u v) -> forall q, lower_cut u q -> lower_cut v q).
    { clear x y c; intros u v c q p.
      apply (lower_cut_rounded u q) in p; strip_truncations; destruct p as [q' [ltqq' p]].
      apply (fst (c (Qpos_diff q q' ltqq') q)).
      exact (transport (lower_cut u) (plus_conjugate_alt q' q) p). }
    apply path_dedekindreals_lower; apply l; [exact c|].
    intros e q; exact (snd (c e q), fst (c e q)).
  Qed.

  (** Every real is arbitrarily close to a rational. *)
  Lemma merely_dedekind_close_rational (x : R) (e : Qpos Q)
    : merely {a : Q & dedekind_close e x [a]}.
  Proof.
    refine (Trunc_functor (-1) _ (cut_approximate x e)); intros [a [b [[la ub] lab]]].
    exists a; intros q; split; intros l.
    - change (q < a); apply (strictly_order_reflecting (+ ' e)).
      refine (transitivity (cut_transitive (isdedekindcut x) _ _ l ub) _).
      rewrite plus_comm; apply flip_lt_minus_l; exact lab.
    - change (q + ' e < a) in l.
      refine (lower_cut_lt x q a (transitivity _ l) la).
      exact (fst (pos_plus_lt_compat_r _ _) (is_pos e)).
  Qed.

  (** ** Continuity *)

  (** The minimum of two positive rationals. *)
  Local Definition qpos_min (e d : Qpos Q) : Qpos Q
    := match le_or_lt (' e) (' d) with inl _ => e | inr _ => d end.

  Local Lemma qpos_min_le_l (e d : Qpos Q) : ' (qpos_min e d) <= ' e.
  Proof.
    unfold qpos_min; destruct (le_or_lt (' e) (' d)) as [l|l]; [reflexivity|exact (lt_le _ _ l)].
  Qed.

  Local Lemma qpos_min_le_r (e d : Qpos Q) : ' (qpos_min e d) <= ' d.
  Proof.
    unfold qpos_min; destruct (le_or_lt (' e) (' d)) as [l|l]; [exact l|reflexivity].
  Qed.

  (** A function on the Dedekind reals is continuous if it is continuous at every point. *)
  Definition IsContinuous (F : R -> R)
    := forall x (e : Qpos Q), hexists (fun d : Qpos Q =>
         forall y, dedekind_close d x y -> dedekind_close e (F x) (F y)).

  Definition iscontinuous_idmap : IsContinuous idmap
    := fun x e => tr (e; fun y c => c).

  Lemma iscontinuous_const (z : R) : IsContinuous (fun _ => z).
  Proof.
    intros x e; apply tr; exists e; intros y _ q; split; apply lower_cut_lt, (fst (pos_plus_lt_compat_r _ _)), is_pos.
  Qed.

  (** Continuous functions which agree on the rationals are equal. *)
  Lemma eq_continuous_rationals (F G : R -> R) (cF : IsContinuous F) (cG : IsContinuous G)
    (h : forall a, F [a] = G [a]) (x : R)
    : F x = G x.
  Proof.
    apply path_dedekind_close; intros e.
    assert (d := cF x (e / 2)); assert (d' := cG x (e / 2)); strip_truncations.
    destruct d as [d close], d' as [d' close'].
    assert (a := merely_dedekind_close_rational x (qpos_min d d')); strip_truncations.
    destruct a as [a c].
    rewrite (pos_split2 e); apply (dedekind_close_triangle _ _ _ (F [a])).
    - exact (close _ (dedekind_close_weaken _ _ _ _ (qpos_min_le_l d d') c)).
    - rewrite h; intros q; split; intros l.
      + exact (snd (close' _ (dedekind_close_weaken _ _ _ _ (qpos_min_le_r d d') c) q) l).
      + exact (fst (close' _ (dedekind_close_weaken _ _ _ _ (qpos_min_le_r d d') c) q) l).
  Qed.

  (** Hence continuous functions of two or three arguments that agree on the rationals are equal. *)
  Lemma eq_continuous_rationals2 (F G : R -> R -> R)
    (cF1 : forall y, IsContinuous (fun x => F x y)) (cF2 : forall x, IsContinuous (F x))
    (cG1 : forall y, IsContinuous (fun x => G x y)) (cG2 : forall x, IsContinuous (G x))
    (h : forall a b, F [a] [b] = G [a] [b]) (x y : R)
    : F x y = G x y.
  Proof.
    revert x; apply (eq_continuous_rationals _ _ (cF1 y) (cG1 y)); intros a.
    revert y; apply (eq_continuous_rationals _ _ (cF2 [a]) (cG2 [a])); apply h.
  Qed.

  Lemma eq_continuous_rationals3 (F G : R -> R -> R -> R)
    (cF1 : forall y z, IsContinuous (fun x => F x y z))
    (cF2 : forall x z, IsContinuous (fun y => F x y z)) (cF3 : forall x y, IsContinuous (F x y))
    (cG1 : forall y z, IsContinuous (fun x => G x y z))
    (cG2 : forall x z, IsContinuous (fun y => G x y z)) (cG3 : forall x y, IsContinuous (G x y))
    (h : forall a b c, F [a] [b] [c] = G [a] [b] [c]) (x y z : R)
    : F x y z = G x y z.
  Proof.
    revert x; apply (eq_continuous_rationals _ _ (cF1 y z) (cG1 y z)); intros a.
    exact (eq_continuous_rationals2 (F [a]) (G [a]) (fun z => cF2 [a] z) (cF3 [a])
             (fun z => cG2 [a] z) (cG3 [a]) (h a) y z).
  Qed.

  (** ** Properties of extensions *)

  (** Arithmetic with halves and quarters of positive rationals. *)
  Local Lemma lt_minus_half_diff (q r : Q) (l : q < r) : q < r - ' (Qpos_diff q r l / 2).
  Proof.
    set (e := Qpos_diff q r l / 2).
    assert (p : r - ' e = q + ' e).
    { rewrite (plus_conjugate_alt r q); change (q + ' (Qpos_diff q r l) - ' e = q + ' e).
      rewrite (ap (cast (Qpos Q) Q) (pos_split2 (Qpos_diff q r l))).
      change (q + (' e + ' e) - ' e = q + ' e).
      rewrite <- plus_assoc, <- plus_assoc, plus_negate_r, plus_0_r; reflexivity. }
    rewrite p; exact (fst (pos_plus_lt_compat_r _ _) (is_pos e)).
  Qed.

  Local Lemma lt_minus_half (q q' : Q) (e : Qpos Q) : q + ' e < q' -> q < q' - ' (e / 2).
  Proof.
    intros l; apply flip_lt_minus_r.
    refine (transitivity _ l); apply (strictly_order_preserving (q +)).
    rewrite (ap (cast (Qpos Q) Q) (pos_split2 e)); change (' (e / 2) < ' (e / 2) + ' (e / 2)).
    exact (fst (pos_plus_lt_compat_r _ _) (is_pos _)).
  Qed.

  Local Lemma widen_lt (a b : Q) (d w : Qpos Q) (lab : b - a < ' d) (dw : ' d <= ' (w / 2 / 2))
    : b + ' d + ' d - (a - ' d) < ' w.
  Proof.
    assert (p : b + ' d + ' d - (a - ' d) = (b - a) + (' d + ' d + ' d)).
    { rewrite negate_plus_distr, negate_involutive, <- !plus_assoc; apply ap.
      rewrite (plus_comm (- a) (' d)), (plus_comm (- a)), !plus_assoc; reflexivity. }
    set (h := w / 2 / 2).
    assert (w4 : ' w = ' h + (' h + ' h + ' h)).
    { change (' w = ' (w / 2 / 2) + (' (w / 2 / 2) + ' (w / 2 / 2) + ' (w / 2 / 2))).
      rewrite <- (plus_assoc (' (w / 2 / 2))), (plus_assoc (' (w / 2 / 2)) (' (w / 2 / 2))).
      change (' w = ' (w / 2 / 2 + w / 2 / 2) + ' (w / 2 / 2 + w / 2 / 2)).
      rewrite <- (pos_split2 (w / 2)); change (' w = ' (w / 2 + w / 2)); rewrite <- (pos_split2 w).
      reflexivity. }
    rewrite p, w4.
    apply plus_lt_le_compat; [exact (lt_le_trans _ _ _ lab dw)|].
    repeat apply plus_le_compat; exact dw.
  Qed.

  (** Widening an interval inside [[lo0, hi0]] by [2 D] on each side stays inside [[lo0 - 1, hi0 + 2]] when [D ≤ 1]. *)
  Local Lemma widen_bounds (lo0 hi0 lo hi s : Q) (D : Qpos Q) (D1 : ' D ≤ 1)
    (l : lo0 ≤ lo ≤ hi0) (h : lo0 ≤ hi ≤ hi0)
    : lo - ' D ≤ s ≤ hi + ' D + ' D -> lo0 - 1 ≤ s ≤ hi0 + 1 + 1.
  Proof.
    intros [l' h']; split.
    - refine (transitivity _ l'); apply plus_le_compat; [exact (fst l)|].
      exact (snd (flip_le_negate _ _) D1).
    - refine (transitivity h' _); rewrite <- plus_assoc, <- (plus_assoc hi0).
      apply plus_le_compat; [exact (snd h)|exact (plus_le_compat _ _ _ _ D1 D1)].
  Qed.

  Local Lemma in_widened {x : R} (I : CutBounds x) (D : Qpos Q) (s : Q)
    : in_bounds I s -> bound_lo I - ' D ≤ s ≤ bound_hi I + ' D + ' D.
  Proof.
    intros [l h]; split.
    - refine (transitivity _ l); apply lt_le, (fst (pos_minus_lt_compat_r _ _) (is_pos D)).
    - refine (transitivity h _); rewrite <- plus_assoc; apply lt_le.
      exact (fst (pos_plus_lt_compat_r _ _) (pos_plus_compat _ _ (is_pos D) (is_pos D))).
  Qed.

  Lemma in_bounds_rational (q : Q) (I : CutBounds [q]) : in_bounds I q.
  Proof.
    exact (lt_le _ _ (bound_lo_lower I), lt_le _ _ (bound_hi_upper I)).
  Qed.

  (** Bounds of reals close to [x]. *)
  Lemma dedekind_close_lower (e : Qpos Q) (x y : R) (c : dedekind_close e x y) (q : Q)
    : lower_cut x q -> lower_cut y (q - ' e).
  Proof.
    intros l; apply (fst (c _)).
    rewrite <- plus_assoc, plus_negate_l, plus_0_r; exact l.
  Qed.

  Lemma dedekind_close_upper (e : Qpos Q) (x y : R) (c : dedekind_close e x y) (r : Q)
    : upper_cut x r -> merely (upper_cut y (r + ' e + ' e)).
  Proof.
    intros u; refine (Trunc_functor (-1) _ (cut_located (isdedekindcut y) (r + ' e) _
                                              (fst (pos_plus_lt_compat_r _ _) (is_pos e)))).
    intros [l|u']; [|exact u'].
    destruct (cut_disjoint x r (snd (c r) l) u).
  Qed.

  Section extension_properties.
    Context (f : Q -> Q -> Q) `{!IsLocallyUniform f}.
    Local Notation ext := (extend f).

    (** On the rationals, the extension of [f] is [f]. *)
    Lemma extend_rational (a b : Q) : ext [a] [b] = [f a b].
    Proof.
      apply path_dedekindreals_lower; intros q p.
      - strip_truncations; destruct p as [q' [ltq p]]; strip_truncations; destruct p as [I p].
        strip_truncations; destruct p as [J p].
        exact (lt_le_trans _ _ _ ltq (p a b (in_bounds_rational a I) (in_bounds_rational b J))).
      - change (q < f a b) in p; set (e := Qpos_diff q (f a b) p / 2).
        assert (h := merely_box_close f [a] [b] e); strip_truncations; destruct h as [I [J h]].
        apply tr; exists (f a b - ' e); split; [exact (lt_minus_half_diff q (f a b) p)|].
        apply tr; exists I; apply tr; exists J; intros s t is it; apply lt_le; unfold PropHolds.
        exact (close_lt_l _ _ _ (h _ _ _ _ (in_bounds_rational a I) is (in_bounds_rational b J) it)).
    Qed.

    (** The extension of a commutative operation is commutative. *)
    Lemma extend_comm (comm : forall s t, f s t = f t s) (x y : R) : ext x y = ext y x.
    Proof.
      assert (swap : forall u v q, BoxAbove f u v q -> BoxAbove f v u q).
      { intros u v q p; strip_truncations; destruct p as [I p]; strip_truncations.
        destruct p as [J p].
        apply tr; exists J; apply tr; exists I; intros s t js it; rewrite comm; exact (p t s it js). }
      apply path_dedekindreals_lower; intros q; apply Trunc_functor; intros [q' [ltq p]];
        exact (q'; (ltq, swap _ _ _ p)).
    Qed.

    (** If [f] varies by less than [e] on a rational box, then a lower bound on a box around [(u, v)] inside it gives a lower bound, up to [e], on every box around [(u', v')] inside it. *)
    Lemma boxabove_transfer (a b c d : Q) (e : Qpos Q)
      (osc : forall s s' t t', a ≤ s ≤ b -> a ≤ s' ≤ b -> c ≤ t ≤ d -> c ≤ t' ≤ d
                               -> close e (f s t) (f s' t'))
      {u v u' v' : R} (I : CutBounds u) (J : CutBounds v) (I' : CutBounds u') (J' : CutBounds v')
      (HI : forall s, in_bounds I s -> a ≤ s ≤ b) (HJ : forall t, in_bounds J t -> c ≤ t ≤ d)
      (HI' : forall s, in_bounds I' s -> a ≤ s ≤ b) (HJ' : forall t, in_bounds J' t -> c ≤ t ≤ d)
      (p : Q)
      : BoxAbove f u v p -> BoxAbove f u' v' (p - ' e).
    Proof.
      intros h; strip_truncations; destruct h as [I1 h]; strip_truncations; destruct h as [J1 h].
      destruct (cutbounds_intersect I I1) as [I2 HI2], (cutbounds_intersect J J1) as [J2 HJ2].
      destruct (HI2 _ (in_bounds_lo I2)) as [i i1], (HJ2 _ (in_bounds_lo J2)) as [j j1].
      apply tr; exists I'; apply tr; exists J'; intros s t is it.
      refine (lt_le _ _ (le_lt_trans _ _ _ (order_preserving (+ - ' e) _ _ (h _ _ i1 j1)) _)).
      exact (close_lt_l _ _ _ (osc _ _ _ _ (HI _ i) (HI' _ is) (HJ _ j) (HJ' _ it))).
    Qed.

    (** The extension of [f] is continuous: we take a box [I * J] around [(x, y)] so small that the values of [f] on the box [I' * J'] obtained by widening it by [2 d] on each side vary by less than [e / 2]. Then [I' * J'] contains a box around [(x', y')] for all [(x', y')] which are [d]-close to [(x, y)], and we can move lower bounds on boxes between [(x, y)] and [(x', y')]. *)
    Lemma extend_continuous (x y : R) (e : Qpos Q)
      : hexists (fun d : Qpos Q => forall x' y', dedekind_close d x x' -> dedekind_close d y y'
                                   -> dedekind_close e (ext x y) (ext x' y')).
    Proof.
      assert (I0 := @merely_cutbounds x); assert (J0 := @merely_cutbounds y); strip_truncations.
      set (a := bound_lo I0 - 1); set (b := bound_hi I0 + 1 + 1).
      set (c := bound_lo J0 - 1); set (d := bound_hi J0 + 1 + 1).
      assert (w := locally_uniform a b c d (e / 2)); strip_truncations; destruct w as [w fw].
      set (D := qpos_min (w / 2 / 2) 1).
      assert (I := merely_cutbounds_close I0 D); assert (J := merely_cutbounds_close J0 D).
      strip_truncations; destruct I as [I [HI wI]], J as [J [HJ wJ]].
      apply tr; exists D; intros x' y' cx cy.
      assert (ux := dedekind_close_upper _ _ _ cx _ (bound_hi_upper I)).
      assert (uy := dedekind_close_upper _ _ _ cy _ (bound_hi_upper J)); strip_truncations.
      set (I' := Build_CutBounds x' _ _ (dedekind_close_lower _ _ _ cx _ (bound_lo_lower I)) ux).
      set (J' := Build_CutBounds y' _ _ (dedekind_close_lower _ _ _ cy _ (bound_lo_lower J)) uy).
      (* The widened box. *)
      set (a' := bound_lo I - ' D); set (b' := bound_hi I + ' D + ' D).
      set (c' := bound_lo J - ' D); set (d' := bound_hi J + ' D + ' D).
      assert (osc : forall s s' t t', a' ≤ s ≤ b' -> a' ≤ s' ≤ b' -> c' ≤ t ≤ d' -> c' ≤ t' ≤ d'
                                     -> close (e / 2) (f s t) (f s' t')).
      { assert (inab : forall s, a' ≤ s ≤ b' -> a ≤ s ≤ b)
          by (intros s is; exact (widen_bounds _ _ _ _ _ _ (qpos_min_le_r (w / 2 / 2) 1) (HI _ (in_bounds_lo I))
                                    (HI _ (in_bounds_hi I)) is)).
        assert (incd : forall t, c' ≤ t ≤ d' -> c ≤ t ≤ d)
          by (intros t it; exact (widen_bounds _ _ _ _ _ _ (qpos_min_le_r (w / 2 / 2) 1) (HJ _ (in_bounds_lo J))
                                    (HJ _ (in_bounds_hi J)) it)).
        intros s s' t t' is is' it it'.
        apply fw; try (apply inab; assumption); try (apply incd; assumption).
        - exact (interval_close _ _ _ _ _ (fst is) (snd is) (fst is') (snd is')
                   (widen_lt _ _ _ _ wI (qpos_min_le_l _ _))).
        - exact (interval_close _ _ _ _ _ (fst it) (snd it) (fst it') (snd it')
                   (widen_lt _ _ _ _ wJ (qpos_min_le_l _ _))). }
      assert (inI : forall s, in_bounds I s -> a' ≤ s ≤ b') by exact (fun s => in_widened _ _ _).
      assert (inJ : forall t, in_bounds J t -> c' ≤ t ≤ d') by exact (fun t => in_widened _ _ _).
      intros q; split; intros l; strip_truncations; destruct l as [q' [ltq p]];
        apply tr; exists (q' - ' (e / 2)); (split; [exact (lt_minus_half q q' e ltq)|]).
      - exact (boxabove_transfer a' b' c' d' _ osc I J I' J' inI inJ (fun s i => i) (fun t i => i) q' p).
      - exact (boxabove_transfer a' b' c' d' _ osc I' J' I J (fun s i => i) (fun t i => i) inI inJ q' p).
    Qed.
  End extension_properties.

  (** Composites of extensions with continuous functions are continuous. *)
  Lemma iscontinuous_extend (f : Q -> Q -> Q) `{!IsLocallyUniform f} (F G : R -> R)
    (cF : IsContinuous F) (cG : IsContinuous G)
    : IsContinuous (fun x => extend f (F x) (G x)).
  Proof.
    intros x e; assert (d := extend_continuous f (F x) (G x) e); strip_truncations.
    destruct d as [d close].
    assert (dF := cF x d); assert (dG := cG x d); strip_truncations.
    destruct dF as [dF cF'], dG as [dG cG'].
    apply tr; exists (qpos_min dF dG); intros y c; apply close.
    - exact (cF' y (dedekind_close_weaken _ _ _ _ (qpos_min_le_l _ _) c)).
    - exact (cG' y (dedekind_close_weaken _ _ _ _ (qpos_min_le_r _ _) c)).
  Qed.

  Local Ltac continuity :=
    repeat first [ exact iscontinuous_idmap | exact (iscontinuous_const _)
                 | refine (iscontinuous_extend _ _ _ _ _) ].

  (** Hence identities between operations on the rationals hold for their extensions. *)
  Lemma extend_assoc (f : Q -> Q -> Q) `{!IsLocallyUniform f}
    (assoc : forall a b c, f a (f b c) = f (f a b) c) (x y z : R)
    : extend f x (extend f y z) = extend f (extend f x y) z.
  Proof.
    revert x y z; napply eq_continuous_rationals3; intros; try continuity.
    rewrite !extend_rational; apply ap, assoc.
  Qed.

  Lemma extend_distr (f g : Q -> Q -> Q) `{!IsLocallyUniform f} `{!IsLocallyUniform g}
    (distr : forall a b c, f a (g b c) = g (f a b) (f a c)) (x y z : R)
    : extend f x (extend g y z) = extend g (extend f x y) (extend f x z).
  Proof.
    revert x y z; napply eq_continuous_rationals3; intros; try continuity.
    rewrite !extend_rational; apply ap, distr.
  Qed.

  (** For an operation which is monotone in both arguments, the cuts of the extension are given by the cuts of the arguments. *)
  Section monotone.
    Context (f : Q -> Q -> Q) `{!IsLocallyUniform f}
      (mono : forall s s' t t', s <= s' -> t <= t' -> f s t <= f s' t').

    Lemma lower_extend_monotone (x y : R) (q : Q)
      : lower_cut (extend f x y) q
        <-> hexists (fun s => hexists (fun t => prod (prod (lower_cut x s) (lower_cut y t)) (q < f s t))).
    Proof.
      split; intros p.
      - strip_truncations; destruct p as [q' [ltq p]]; strip_truncations; destruct p as [I p].
        strip_truncations; destruct p as [J p].
        apply tr; exists (bound_lo I); apply tr; exists (bound_lo J).
        refine ((bound_lo_lower I, bound_lo_lower J), _).
        exact (lt_le_trans _ _ _ ltq (p _ _ (in_bounds_lo I) (in_bounds_lo J))).
      - assert (I := @merely_cutbounds x); assert (J := @merely_cutbounds y); strip_truncations.
        destruct p as [s p]; strip_truncations; destruct p as [t [[ls lt] ltq]].
        apply tr; exists (f s t); refine (ltq, _).
        apply tr; exists (Build_CutBounds x s _ ls (bound_hi_upper I)).
        apply tr; exists (Build_CutBounds y t _ lt (bound_hi_upper J)).
        intros s' t' [ls' _] [lt' _]; exact (mono _ _ _ _ ls' lt').
    Qed.

    Lemma upper_extend_monotone (x y : R) (r : Q)
      : upper_cut (extend f x y) r
        <-> hexists (fun s => hexists (fun t => prod (prod (upper_cut x s) (upper_cut y t)) (f s t < r))).
    Proof.
      split; intros p.
      - strip_truncations; destruct p as [r' [ltr p]]; strip_truncations; destruct p as [I p].
        strip_truncations; destruct p as [J p].
        apply tr; exists (bound_hi I); apply tr; exists (bound_hi J).
        refine ((bound_hi_upper I, bound_hi_upper J), _).
        exact (le_lt_trans _ _ _ (p _ _ (in_bounds_hi I) (in_bounds_hi J)) ltr).
      - assert (I := @merely_cutbounds x); assert (J := @merely_cutbounds y); strip_truncations.
        destruct p as [s p]; strip_truncations; destruct p as [t [[us ut] ltr]].
        apply tr; exists (f s t); refine (ltr, _).
        apply tr; exists (Build_CutBounds x _ s (bound_lo_lower I) us).
        apply tr; exists (Build_CutBounds y _ t (bound_lo_lower J) ut).
        intros s' t' [_ us'] [_ ut']; exact (mono _ _ _ _ us' ut').
    Qed.
  End monotone.

  (** ** The operations *)

  (** We extend addition, negation, multiplication, minimum and maximum. *)

  Local Lemma close_of_lt (e : Qpos Q) (u v : Q) : u - ' e < v -> v - ' e < u -> close e u v.
  Proof.
    intros l l'; split.
    - apply flip_lt_minus_r; rewrite plus_comm; exact l'.
    - apply flip_lt_minus_l; rewrite plus_comm; apply flip_lt_minus_l; exact l.
  Qed.

  Local Lemma close_plus (e d : Qpos Q) (s s' t t' : Q)
    : close e s s' -> close d t t' -> close (e + d) (s + t) (s' + t').
  Proof.
    intros [l1 l2] [l3 l4].
    assert (p : s + t - (s' + t') = (s - s') + (t - t')).
    { rewrite negate_plus_distr, <- !plus_assoc; apply ap.
      rewrite (plus_comm t), <- plus_assoc; apply ap, plus_comm. }
    change (' (e + d)) with (' e + ' d); rewrite p, negate_plus_distr.
    split; apply plus_lt_compat; assumption.
  Qed.

  Local Lemma close_negate (e : Qpos Q) (s s' : Q) : close e s s' -> close e (- s) (- s').
  Proof.
    intros [l1 l2]; rewrite <- negate_plus_distr; split.
    - exact (snd (flip_lt_negate _ _) l2).
    - apply flip_lt_negate_l; exact l1.
  Qed.

  (** The minimum and maximum of two rationals. *)
  Local Definition qmin (s t : Q) : Q := match le_or_lt s t with inl _ => s | inr _ => t end.
  Local Definition qmax (s t : Q) : Q := match le_or_lt s t with inl _ => t | inr _ => s end.

  Local Lemma qmin_le_l (s t : Q) : qmin s t <= s.
  Proof. unfold qmin; destruct (le_or_lt s t) as [l|l]; [reflexivity|exact (lt_le _ _ l)]. Qed.
  Local Lemma qmin_le_r (s t : Q) : qmin s t <= t.
  Proof. unfold qmin; destruct (le_or_lt s t) as [l|l]; [exact l|reflexivity]. Qed.
  Local Lemma le_qmax_l (s t : Q) : s <= qmax s t.
  Proof. unfold qmax; destruct (le_or_lt s t) as [l|l]; [exact l|reflexivity]. Qed.
  Local Lemma le_qmax_r (s t : Q) : t <= qmax s t.
  Proof. unfold qmax; destruct (le_or_lt s t) as [l|l]; [reflexivity|exact (lt_le _ _ l)]. Qed.

  (** Both are one of their arguments. *)
  Local Lemma qmin_cases (P : Q -> Type) (s t : Q) : P s -> P t -> P (qmin s t).
  Proof. unfold qmin; destruct (le_or_lt s t); trivial. Qed.
  Local Lemma qmax_cases (P : Q -> Type) (s t : Q) : P s -> P t -> P (qmax s t).
  Proof. unfold qmax; destruct (le_or_lt s t); trivial. Qed.

  Local Lemma qmin_monotone (s s' t t' : Q) : s <= s' -> t <= t' -> qmin s t <= qmin s' t'.
  Proof.
    intros l l'; apply (qmin_cases (fun m => qmin s t <= m)).
    - exact (transitivity (qmin_le_l s t) l).
    - exact (transitivity (qmin_le_r s t) l').
  Qed.

  Local Lemma qmax_monotone (s s' t t' : Q) : s <= s' -> t <= t' -> qmax s t <= qmax s' t'.
  Proof.
    intros l l'; apply (qmax_cases (fun m => m <= qmax s' t')).
    - exact (transitivity l (le_qmax_l s' t')).
    - exact (transitivity l' (le_qmax_r s' t')).
  Qed.

  Local Lemma close_symmetric (e : Qpos Q) (u v : Q) : close e u v -> close e v u.
  Proof.
    intros [l1 l2]; rewrite (negate_swap_r v u); split.
    - exact (snd (flip_lt_negate _ _) l2).
    - apply flip_lt_negate_l; exact l1.
  Qed.

  Local Lemma close_qmin (e : Qpos Q) (s s' t t' : Q)
    : close e s s' -> close e t t' -> close e (qmin s t) (qmin s' t').
  Proof.
    assert (h : forall s s' t t', close e s s' -> close e t t' -> qmin s t - ' e < qmin s' t').
    { clear s s' t t'; intros s s' t t' cs ct.
      apply (qmin_cases (fun m => qmin s t - ' e < m)).
      - exact (le_lt_trans _ _ _ (order_preserving (+ _) _ _ (qmin_le_l s t)) (close_lt_l _ _ _ cs)).
      - exact (le_lt_trans _ _ _ (order_preserving (+ _) _ _ (qmin_le_r s t)) (close_lt_l _ _ _ ct)). }
    intros cs ct; apply close_of_lt; [exact (h _ _ _ _ cs ct)|].
    exact (h _ _ _ _ (close_symmetric _ _ _ cs) (close_symmetric _ _ _ ct)).
  Qed.

  Local Lemma close_qmax (e : Qpos Q) (s s' t t' : Q)
    : close e s s' -> close e t t' -> close e (qmax s t) (qmax s' t').
  Proof.
    assert (h : forall s s' t t', close e s s' -> close e t t' -> qmax s t - ' e < qmax s' t').
    { clear s s' t t'; intros s s' t t' cs ct.
      apply (qmax_cases (fun m => m - ' e < qmax s' t')).
      - exact (lt_le_trans _ _ _ (close_lt_l _ _ _ cs) (le_qmax_l s' t')).
      - exact (lt_le_trans _ _ _ (close_lt_l _ _ _ ct) (le_qmax_r s' t')). }
    intros cs ct; apply close_of_lt; [exact (h _ _ _ _ cs ct)|].
    exact (h _ _ _ _ (close_symmetric _ _ _ cs) (close_symmetric _ _ _ ct)).
  Qed.

  (** A positive rational strictly bounding two given ones in absolute value. *)
  Local Lemma rational_bound (a b : Q) : {X : Q & prod (0 < X) (prod (- X < a) (b < X))}.
  Proof.
    destruct (round_up_strict Q b) as [m lm], (round_up_strict Q (- a)) as [n ln].
    pose proof (nat_to_semiring_nonneg (R:=Q) m) as Hm; pose proof (nat_to_semiring_nonneg (R:=Q) n) as Hn.
    assert (le1 : nQ m + nQ n <= nQ m + nQ n + 1) by exact (fst (nonneg_plus_le_compat_r _ _) le_0_1).
    exists (nQ m + nQ n + 1); refine (_, (_, _)).
    - refine (lt_le_trans _ 1 _ lt_0_1 _).
      exact (fst (nonneg_plus_le_compat_l _ _) (nonneg_plus_compat _ _ Hm Hn)).
    - apply flip_lt_negate_l; refine (lt_le_trans _ _ _ ln (transitivity _ le1)).
      exact (fst (nonneg_plus_le_compat_l _ _) Hm).
    - refine (lt_le_trans _ _ _ lm (transitivity _ le1)).
      exact (fst (nonneg_plus_le_compat_r _ _) Hn).
  Qed.

  (** A positive rational whose product with [S] is less than [e]. *)
  Local Lemma small_factor (e : Qpos Q) (S : Q) : 0 < S -> {D : Qpos Q & ' D * S < ' e}.
  Proof.
    intros Spos; pose (S' := mkQpos S Spos : Qpos Q).
    exists (e / S' / 2); cbn.
    rewrite <- (mult_assoc (' e)), (mult_comm (/ S)), <- !mult_assoc.
    rewrite (mult_comm (/ S)), dec_recip_inverse, mult_1_r; [|apply lt_ne_flip, Spos].
    change (' (e / 2) < ' e).
    apply (transport (fun z => ' (e / 2) < ' z) (pos_split2 e)^).
    apply pos_plus_lt_compat_r, is_pos.
  Qed.

  Local Lemma close_mult (a b c d : Q) (e : Qpos Q)
    : {w : Qpos Q & forall s s' t t', a ≤ s ≤ b -> a ≤ s' ≤ b -> c ≤ t ≤ d -> c ≤ t' ≤ d
                    -> close w s s' -> close w t t' -> close e (s * t) (s' * t')}.
  Proof.
    destruct (rational_bound a b) as [X [Xpos [lX lX']]], (rational_bound c d) as [W [Wpos [lW lW']]].
    destruct (small_factor e (X + W) (pos_plus_compat _ _ Xpos Wpos)) as [D lD].
    exists D; intros s s' t t' is is' it it' cs ct.
    assert (p : X * ' D + ' D * W = ' D * (X + W)) by (rewrite (mult_comm X), plus_mult_distr_l; reflexivity).
    destruct (mult_minus_mult_lt_bound s t s' t' X W (' D)
                (lt_le_trans _ _ _ lX (fst is), le_lt_trans _ _ _ (snd is) lX')
                (lt_le_trans _ _ _ lW (fst it'), le_lt_trans _ _ _ (snd it') lW') cs ct) as [lo hi].
    rewrite p in lo, hi; split.
    - exact (transitivity (snd (flip_lt_negate _ _) lD) lo).
    - exact (transitivity hi lD).
  Qed.

  #[export] Instance islocallyuniform_plus : IsLocallyUniform (+).
  Proof.
    intros a b c d e; apply tr; exists (e / 2); intros s s' t t' _ _ _ _ cs ct.
    rewrite (pos_split2 e); exact (close_plus _ _ _ _ _ _ cs ct).
  Qed.

  Local Definition negate_fst (s t : Q) : Q := - s.

  #[export] Instance islocallyuniform_negate_fst : IsLocallyUniform negate_fst
    := fun a b c d e => tr (e; fun s s' t t' _ _ _ _ cs _ => close_negate _ _ _ cs).

  #[export] Instance islocallyuniform_mult : IsLocallyUniform (.*.)
    := fun a b c d e => tr (close_mult a b c d e).

  #[export] Instance islocallyuniform_qmin : IsLocallyUniform qmin
    := fun a b c d e => tr (e; fun s s' t t' _ _ _ _ => close_qmin e s s' t t').

  #[export] Instance islocallyuniform_qmax : IsLocallyUniform qmax
    := fun a b c d e => tr (e; fun s s' t t' _ _ _ _ => close_qmax e s s' t t').

  #[local] Instance plus_dedekindreals : Plus R := extend (+).
  #[local] Instance negate_dedekindreals : Negate R := fun x => extend negate_fst x x.
  #[local] Instance zero_dedekindreals : Zero R := [0].
  #[local] Instance one_dedekindreals : One R := [1].
  #[local] Instance mult_dedekindreals : Mult R := extend (.*.).
  #[local] Instance meet_dedekindreals : Meet R := extend qmin.
  #[local] Instance join_dedekindreals : Join R := extend qmax.

  Lemma rational_dedekind_plus (q r : Q) : [q + r] = [q] + [r].
  Proof.
    exact (extend_rational _ q r)^.
  Qed.

  Lemma rational_dedekind_mult (q r : Q) : [q * r] = [q] * [r].
  Proof.
    exact (extend_rational _ q r)^.
  Qed.

  (** ** The ring laws *)

  (** They follow from those of the rationals, by continuity. *)
  #[export] Instance iscring_dedekindreals : IsCRing R.
  Proof.
    repeat split; try exact _; hnf.
    - exact (extend_assoc _ plus_assoc).
    - napply (eq_continuous_rationals (fun x => extend (+) 0 x) idmap); [continuity|continuity|].
      intros a; cbn beta; change (extend (+) [0] [a] = [a]).
      rewrite extend_rational; apply ap, plus_0_l.
    - napply (eq_continuous_rationals (fun x => extend (+) x 0) idmap); [continuity|continuity|].
      intros a; cbn beta; change (extend (+) [a] [0] = [a]).
      rewrite extend_rational; apply ap, plus_0_r.
    - napply (eq_continuous_rationals (fun x => extend (+) (extend negate_fst x x) x) (fun _ => 0));
        [continuity|continuity|].
      intros a; cbn beta; rewrite !extend_rational; exact (ap rational_dedekind (plus_negate_l a)).
    - napply (eq_continuous_rationals (fun x => extend (+) x (extend negate_fst x x)) (fun _ => 0));
        [continuity|continuity|].
      intros a; cbn beta; rewrite !extend_rational; exact (ap rational_dedekind (plus_negate_r a)).
    - exact (extend_comm _ plus_comm).
    - exact (extend_assoc _ mult_assoc).
    - napply (eq_continuous_rationals (fun x => extend (.*.) 1 x) idmap); [continuity|continuity|].
      intros a; cbn beta; change (extend (.*.) [1] [a] = [a]).
      rewrite extend_rational; apply ap, mult_1_l.
    - napply (eq_continuous_rationals (fun x => extend (.*.) x 1) idmap); [continuity|continuity|].
      intros a; cbn beta; change (extend (.*.) [a] [1] = [a]).
      rewrite extend_rational; apply ap, mult_1_r.
    - exact (extend_comm _ mult_comm).
    - exact (extend_distr _ _ plus_mult_distr_l).
  Qed.

  (** ** The cuts of the operations *)

  Lemma lower_plus (x y : R) (q : Q)
    : lower_cut (x + y) q
      <-> hexists (fun s => hexists (fun t => prod (prod (lower_cut x s) (lower_cut y t)) (q < s + t))).
  Proof.
    exact (lower_extend_monotone (+) (fun s s' t t' => plus_le_compat s s' t t') x y q).
  Qed.

  Lemma lower_negate (x : R) (q : Q) : lower_cut (- x) q <-> upper_cut x (- q).
  Proof.
    split; intros p.
    - strip_truncations; destruct p as [q' [ltq p]]; strip_truncations; destruct p as [I p].
      strip_truncations; destruct p as [J p].
      refine (upper_cut_le x _ _ _ (bound_hi_upper I)).
      apply lt_le, flip_lt_negate_r; refine (lt_le_trans _ _ _ ltq _).
      exact (p _ _ (in_bounds_hi I) (in_bounds_lo J)).
    - apply (upper_cut_rounded x) in p; strip_truncations; destruct p as [r' [ltr u]].
      assert (I := @merely_cutbounds x); strip_truncations.
      apply tr; exists (- r'); split; [exact (flip_lt_negate_r _ _ ltr)|].
      apply tr; exists (Build_CutBounds x _ r' (bound_lo_lower I) u); apply tr; exists I.
      intros s t [_ ls] _; exact (snd (flip_le_negate _ _) ls).
  Qed.

  Lemma lower_meet (x y : R) (q : Q)
    : lower_cut (meet x y) q <-> prod (lower_cut x q) (lower_cut y q).
  Proof.
    refine (iff_compose (lower_extend_monotone qmin qmin_monotone x y q) _); split.
    - intros p; strip_truncations; destruct p as [s p]; strip_truncations.
      destruct p as [t [[ls lt] ltq]]; split.
      + exact (lower_cut_lt x _ _ (lt_le_trans _ _ _ ltq (qmin_le_l s t)) ls).
      + exact (lower_cut_lt y _ _ (lt_le_trans _ _ _ ltq (qmin_le_r s t)) lt).
    - intros [lx ly].
      apply (lower_cut_rounded x) in lx; apply (lower_cut_rounded y) in ly; strip_truncations.
      destruct lx as [s [lts lx]], ly as [t [ltt ly]].
      exact (tr (s; tr (t; ((lx, ly), qmin_cases (fun m => q < m) s t lts ltt)))).
  Qed.

  Lemma lower_join (x y : R) (q : Q)
    : lower_cut (join x y) q <-> hor (lower_cut x q) (lower_cut y q).
  Proof.
    refine (iff_compose (lower_extend_monotone qmax qmax_monotone x y q) _); split.
    - intros p; strip_truncations; destruct p as [s p]; strip_truncations.
      destruct p as [t [[ls lt] ltq]]; revert ltq.
      apply (qmax_cases (fun m => q < m -> hor (lower_cut x q) (lower_cut y q))); intros l.
      + exact (tr (inl (lower_cut_lt x _ _ l ls))).
      + exact (tr (inr (lower_cut_lt y _ _ l lt))).
    - assert (a := cut_lower_inhabited (isdedekindcut x));
        assert (b := cut_lower_inhabited (isdedekindcut y)).
      intros p; strip_truncations; destruct a as [a la], b as [b lb]; destruct p as [p|p].
      + apply (lower_cut_rounded x) in p; strip_truncations; destruct p as [s [lts p]].
        exact (tr (s; tr (b; ((p, lb), lt_le_trans _ _ _ lts (le_qmax_l s b))))).
      + apply (lower_cut_rounded y) in p; strip_truncations; destruct p as [t [ltt p]].
        exact (tr (a; tr (t; ((la, p), lt_le_trans _ _ _ ltt (le_qmax_r a t))))).
  Qed.

  (** ** The lattice structure *)

  #[export] Instance partialorder_dedekindreals : PartialOrder (_ : Le R).
  Proof.
    split.
    - exact _.
    - exact _.
    - split.
      + intros x q p; exact p.
      + intros x y z l l' q p; exact (l' q (l q p)).
    - intros x y l l'; exact (path_dedekindreals_lower x y l l').
  Qed.

  #[export] Instance latticeorder_dedekindreals : LatticeOrder (_ : Le R).
  Proof.
    split; split.
    - exact _.
    - intros x y q p; exact (fst (fst (lower_meet x y q) p)).
    - intros x y q p; exact (snd (fst (lower_meet x y q) p)).
    - intros x y z l l' q p; exact (snd (lower_meet x y q) (l q p, l' q p)).
    - exact _.
    - intros x y q p; exact (snd (lower_join x y q) (tr (inl p))).
    - intros x y q p; exact (snd (lower_join x y q) (tr (inr p))).
    - intros x y z l l' q p; apply (lower_join x y q) in p; strip_truncations.
      destruct p as [p|p]; [exact (l q p)|exact (l' q p)].
  Qed.

  (** ** The order and the ring structure *)

  Lemma lt_dedekindreals_iff_lower_minus (x y : R) : x < y <-> lower_cut (y - x) 0.
  Proof.
    refine (iff_compose _ (iff_inverse (lower_plus y (- x) 0))); split.
    - intros l; strip_truncations; destruct l as [q [u p]].
      apply (upper_cut_rounded x) in u; strip_truncations; destruct u as [r [ltr u]].
      apply tr; exists q; apply tr; exists (- r); refine ((p, _), _).
      + apply lower_negate; rewrite negate_involutive; exact u.
      + exact (snd (flip_pos_minus _ _) ltr).
    - intros p; strip_truncations; destruct p as [s p]; strip_truncations.
      destruct p as [t [[ls lt] pos]].
      apply tr; exists s; refine (_, ls).
      refine (upper_cut_lt x _ _ _ (fst (lower_negate x t) lt)).
      rewrite <- (plus_0_l (- t)); exact (snd (flip_lt_minus_l _ _ _) pos).
  Qed.

  Local Lemma plus_minus_plus_dedekind (x y z : R) : (z + y) - (z + x) = y - x.
  Proof.
    rewrite negate_plus_distr, (plus_comm z y), <- plus_assoc, (plus_assoc z).
    rewrite plus_negate_r, plus_0_l; reflexivity.
  Qed.

  #[export] Instance strictlyorderpreserving_plus_dedekindreals (z : R)
    : StrictlyOrderPreserving (z +).
  Proof.
    intros x y l; apply lt_dedekindreals_iff_lower_minus.
    rewrite plus_minus_plus_dedekind; exact (fst (lt_dedekindreals_iff_lower_minus x y) l).
  Qed.

  Local Lemma lt_dedekindreals_minus_zero (a b : R) : a < b -> a - b < 0.
  Proof.
    intros l; rewrite <- (plus_negate_r b), (plus_comm a), (plus_comm b).
    exact (strictly_order_preserving (- b +) _ _ l).
  Qed.

  Local Lemma lt_dedekindreals_zero_minus (a b : R) : b < a -> 0 < a - b.
  Proof.
    intros l; rewrite <- (plus_negate_r b), (plus_comm a), (plus_comm b).
    exact (strictly_order_preserving (- b +) _ _ l).
  Qed.

  Local Lemma lt_dedekindreals_from_minus (a b c : R) : a - b < c - b -> a < c.
  Proof.
    intros l; assert (l' := strictly_order_preserving (b +) _ _ l).
    rewrite !(plus_comm b), <- !plus_assoc, !plus_negate_l, !plus_0_r in l'; exact l'.
  Qed.

  Lemma pos_mult_dedekindreals (x y : R) : 0 < x -> 0 < y -> 0 < x * y.
  Proof.
    intros lx ly.
    apply (fst (lt_rational_dedekind_l 0 x)), (lower_cut_rounded x) in lx.
    apply (fst (lt_rational_dedekind_l 0 y)), (lower_cut_rounded y) in ly.
    assert (b := cut_upper_inhabited (isdedekindcut x)).
    assert (d := cut_upper_inhabited (isdedekindcut y)); strip_truncations.
    destruct lx as [s [ls lx]], ly as [t [lt ly]], b as [b ub], d as [d ud].
    apply (snd (lt_rational_dedekind_l 0 _)), tr; exists (s * t); split; [exact (pos_mult _ _ ls lt)|].
    apply tr; exists (Build_CutBounds x s b lx ub); apply tr; exists (Build_CutBounds y t d ly ud).
    intros u v [lu _] [lv _]; cbn in lu, lv.
    exact (mult_le_compat _ _ _ _ (lt_le _ _ ls) (lt_le _ _ lt) lu lv).
  Qed.

  (** If [x * z] is apart from zero, then so is [z]: bounds of [z] cannot contain zero. *)
  Lemma mult_dedekindreals_apart_zero_r (x z : R) : x * z ≶ 0 -> z ≶ 0.
  Proof.
    assert (sign : forall (I : CutBounds x) (J : CutBounds z),
               ~ (prod (bound_lo J <= 0) (0 <= bound_hi J)) -> z ≶ 0).
    { intros I J n; destruct (le_or_lt (bound_lo J) 0) as [l|l].
      - destruct (le_or_lt 0 (bound_hi J)) as [l'|l']; [destruct (n (l, l'))|].
        apply tr, inl, (snd (lt_rational_dedekind_r 0 z)).
        exact (upper_cut_lt z _ _ l' (bound_hi_upper J)).
      - apply tr, inr, (snd (lt_rational_dedekind_l 0 z)).
        exact (lower_cut_lt z _ _ l (bound_lo_lower J)). }
    intros a; strip_truncations; destruct a as [a|a].
    - apply (fst (lt_rational_dedekind_r 0 _)) in a; strip_truncations.
      destruct a as [r [ltr a]]; strip_truncations; destruct a as [I a]; strip_truncations.
      destruct a as [J a].
      apply (sign I J); intros i0.
      apply (irreflexivity (<) (0 : Q)); refine (le_lt_trans _ _ _ _ ltr).
      exact (transport (fun w => w <= r) (mult_0_r _) (a _ _ (in_bounds_lo I) i0)).
    - apply (fst (lt_rational_dedekind_l 0 _)) in a; strip_truncations.
      destruct a as [q [ltq a]]; strip_truncations; destruct a as [I a]; strip_truncations.
      destruct a as [J a].
      apply (sign I J); intros i0.
      apply (irreflexivity (<) (0 : Q)); refine (lt_le_trans _ _ _ ltq _).
      exact (transport (fun w => q <= w) (mult_0_r _) (a _ _ (in_bounds_lo I) i0)).
  Qed.

  Local Lemma apart_dedekindreals_iff_minus_zero (a b : R) : a ≶ b <-> a - b ≶ 0.
  Proof.
    split; intros p; strip_truncations; apply tr; destruct p as [l|l].
    - left; exact (lt_dedekindreals_minus_zero a b l).
    - right; exact (lt_dedekindreals_zero_minus a b l).
    - left; apply (lt_dedekindreals_from_minus a b b); rewrite plus_negate_r; exact l.
    - right; apply (lt_dedekindreals_from_minus b b a); rewrite plus_negate_r; exact l.
  Qed.

  #[export] Instance strongbinaryextensionality_mult_dedekindreals
    : StrongBinaryExtensionality (A:=R) (.*.).
  Proof.
    intros x1 y1 x2 y2 a.
    assert (c := cotransitive a (x1 * y2)); strip_truncations; apply tr; destruct c as [c|c].
    - right; apply apart_dedekindreals_iff_minus_zero.
      apply (mult_dedekindreals_apart_zero_r x1).
      rewrite plus_mult_distr_l, <- negate_mult_distr_r.
      exact (fst (apart_dedekindreals_iff_minus_zero _ _) c).
    - left; apply apart_dedekindreals_iff_minus_zero.
      apply (mult_dedekindreals_apart_zero_r y2).
      rewrite plus_mult_distr_l, <- negate_mult_distr_r, !(mult_comm y2).
      exact (fst (apart_dedekindreals_iff_minus_zero _ _) c).
  Qed.

  #[export] Instance fullpseudosemiringorder_dedekindreals
    : FullPseudoSemiRingOrder (_ : Le R) (_ : Lt R).
  Proof.
    apply from_full_pseudo_ring_order.
    - exact _.
    - exact _.
    - exact pos_mult_dedekindreals.
  Qed.

  Local Lemma minus_minus_cancel (q s : Q) : q - (q - s) = s.
  Proof.
    rewrite negate_plus_distr, negate_involutive, plus_assoc, plus_negate_r; apply plus_0_l.
  Qed.

  (** ** The rationals as Dedekind reals *)

  Lemma rational_dedekind_lt (q r : Q) : q < r <-> [q] < [r].
  Proof.
    symmetry; exact (lt_rational_dedekind_l q [r]).
  Qed.

  #[export] Instance issemiringpreserving_rational_dedekind : IsSemiRingPreserving rational_dedekind.
  Proof.
    repeat split.
    - exact rational_dedekind_plus.
    - exact rational_dedekind_mult.
  Qed.

  (** Between two Dedekind reals lies a rational. *)
  Lemma dedekindreals_archimedean (x y : R) : x < y -> hexists (fun q => prod (x < [q]) ([q] < y)).
  Proof.
    intros l; strip_truncations; destruct l as [q [u p]]; apply tr; exists q; split.
    - exact (snd (lt_rational_dedekind_r q x) u).
    - exact (snd (lt_rational_dedekind_l q y) p).
  Qed.

  #[export] Instance lt_0_1_dedekindreals : PropHolds (0 < (1 : R)).
  Proof.
    exact (fst (rational_dedekind_lt 0 1) lt_0_1).
  Qed.

  #[export] Instance apart_1_0_dedekindreals : PropHolds ((1 : R) ≶ 0).
  Proof.
    exact (tr (inr lt_0_1_dedekindreals)).
  Qed.

  (** ** Reciprocals *)

  Local Lemma recip_mult_cancel (u b : Q) : 0 < b -> u / b * b = u.
  Proof.
    intros bpos; rewrite <- mult_assoc, (mult_comm (/ b)), dec_recip_inverse.
    - apply mult_1_r.
    - apply lt_ne_flip, bpos.
  Qed.

  Local Lemma pos_quotient (u b : Q) : 0 < u -> 0 < b -> 0 < u / b.
  Proof.
    intros upos bpos; apply pos_mult; [exact upos|apply pos_dec_recip_compat, bpos].
  Qed.

  (** A positive real has a positive rational upper bound. *)
  Local Lemma merely_pos_upper (x : R) : 0 < x -> merely {b : Q & prod (0 < b) (x < [b])}.
  Proof.
    intros xpos; generalize (cut_upper_inhabited (isdedekindcut x)).
    apply Trunc_functor; intros [b ub]; exists b.
    assert (lb := snd (lt_rational_dedekind_r b x) ub); split; [|exact lb].
    exact (snd (rational_dedekind_lt 0 b) (lt_dedekindreals_trans _ _ _ xpos lb)).
  Qed.

  (** For a positive real [x], we have [q < 1 / x] when [q * x < 1] and [1 / x < r] when [1 < r * x]. *)
  Section pos_recip.
    Context (x : R) `{xpos : !PropHolds (0 < x)}.

    Local Definition pos_recip_lower (q : Q) : HProp := Build_HProp ([q] * x < 1).
    Local Definition pos_recip_upper (r : Q) : HProp := Build_HProp (1 < [r] * x).

    Lemma isdedekindcut_pos_recip : IsDedekindCut pos_recip_lower pos_recip_upper.
    Proof.
      split.
      - apply tr; exists 0; change (0 * x < 1); rewrite mult_0_l; exact lt_0_1_dedekindreals.
      - apply (fst (lt_rational_dedekind_l 0 x)), (lower_cut_rounded x) in xpos.
        strip_truncations; destruct xpos as [s [spos ls]].
        apply tr; exists (1 / s); change (1 < [1 / s] * x).
        assert (PropHolds (0 < [1 / s]))
          by exact (fst (rational_dedekind_lt 0 _) (pos_quotient 1 s lt_0_1 spos)).
        refine (transport (fun w => w < _) _
                  (strictly_order_preserving ([1 / s] *.) [s] x (snd (lt_rational_dedekind_l s x) ls))).
        rewrite <- rational_dedekind_mult, recip_mult_cancel; [reflexivity|exact spos].
      - intros q; split.
        + intros l; change ([q] * x < 1) in l.
          assert (t := dedekindreals_archimedean _ _ l).
          assert (b := merely_pos_upper x xpos); strip_truncations.
          destruct t as [t [lt lt']], b as [b [bpos lb]].
          apply (rational_dedekind_lt t 1) in lt'.
          pose (d := (1 - t) / b).
          assert (dpos : 0 < d) by exact (pos_quotient _ _ (snd (flip_pos_minus _ _) lt') bpos).
          assert (PropHolds (0 < [d])) by exact (fst (rational_dedekind_lt 0 d) dpos).
          apply tr; exists (q + d); split.
          * exact (fst (pos_plus_lt_compat_r q d) dpos).
          * change ([q + d] * x < 1).
            rewrite rational_dedekind_plus, plus_mult_distr_r.
            apply (lt_le_trans _ ([t] + [d] * [b])).
            -- apply plus_lt_compat; [exact lt|].
               exact (strictly_order_preserving ([d] *.) x [b] lb).
            -- rewrite <- rational_dedekind_mult, <- rational_dedekind_plus.
               unfold d; rewrite recip_mult_cancel, <- plus_conjugate_alt; [reflexivity|exact bpos].
        + intros l; revert l; apply Trunc_rec; intros [q' [l p]]; change ([q'] * x < 1) in p.
          change ([q] * x < 1).
          rhs_V' exact p.
          exact (strictly_order_preserving (.* x) _ _ (fst (rational_dedekind_lt q q') l)).
      - intros r; split.
        + intros l; change (1 < [r] * x) in l.
          assert (t := dedekindreals_archimedean _ _ l).
          assert (b := merely_pos_upper x xpos); strip_truncations.
          destruct t as [t [lt lt']], b as [b [bpos lb]].
          apply (rational_dedekind_lt 1 t) in lt.
          pose (d := (t - 1) / b).
          assert (dpos : 0 < d) by exact (pos_quotient _ _ (snd (flip_pos_minus _ _) lt) bpos).
          assert (PropHolds (0 < [d])) by exact (fst (rational_dedekind_lt 0 d) dpos).
          apply tr; exists (r - d); split.
          * exact (fst (pos_minus_lt_compat_r r d) dpos).
          * change (1 < [r - d] * x).
            rewrite rational_dedekind_plus, preserves_negate, plus_mult_distr_r.
            apply (le_lt_trans _ ([t] - [d] * [b])).
            -- rewrite <- rational_dedekind_mult, <- preserves_negate, <- rational_dedekind_plus.
               unfold d; rewrite recip_mult_cancel, minus_minus_cancel; [reflexivity|exact bpos].
            -- apply plus_lt_compat; [exact lt'|].
               rewrite <- negate_mult_distr_l.
               apply (snd (flip_lt_negate _ _)).
               exact (strictly_order_preserving ([d] *.) x [b] lb).
        + intros l; revert l; apply Trunc_rec; intros [r' [l p]]; change (1 < [r'] * x) in p.
          change (1 < [r] * x).
          lhs' exact p.
          exact (strictly_order_preserving (.* x) _ _ (fst (rational_dedekind_lt r' r) l)).
      - intros q r l l'.
        apply (rational_dedekind_lt q r).
        apply (strictly_order_reflecting (.* x)).
        exact (transitivity l l').
      - intros q r l.
        exact (cotransitive (strictly_order_preserving (.* x) _ _ (fst (rational_dedekind_lt q r) l)) 1).
    Qed.

    Definition pos_recip_dedekind : R := Build_DedekindReals _ _ isdedekindcut_pos_recip.

    Local Notation y := pos_recip_dedekind.

    (** We show [x * y = 1] by approximating [y] closely enough. *)
    Lemma pos_recip_dedekind_inverse : x * y = 1.
    Proof.
      apply (fst (tight_apart _ _)); intros a.
      assert (b := merely_pos_upper x xpos); revert a; apply (Trunc_rec (n:=-1)); intros a.
      revert b; apply (Trunc_rec (n:=-1)); intros [b [bpos lb]]; destruct a as [l|l].
      - apply (Trunc_rec (n:=-1) (A:={t : Q & prod (x * y < [t]) ([t] < 1)})); [|exact (dedekindreals_archimedean _ _ l)].
        intros [t [lt lt']]; apply (rational_dedekind_lt t 1) in lt'.
        pose (e := mkQpos ((1 - t) / b) (pos_quotient _ _ (snd (flip_pos_minus _ _) lt') bpos)).
        assert (PropHolds (0 < [' e])) by exact (fst (rational_dedekind_lt 0 _) (is_pos e)).
        apply (Trunc_rec (n:=-1) (A:={q : Q & {r : Q & prod (prod (lower_cut y q) (upper_cut y r)) (r - q < ' e)}}));
          [|exact (cut_approximate y e)].
        intros [q [r [[lq ur] lqr]]]; change (1 < [r] * x) in ur.
        apply (irreflexivity (<) (1 : R)), (transitivity ur).
        rewrite (mult_comm [r]).
        apply (lt_le_trans _ (x * (y + [' e]))).
        + apply (strictly_order_preserving (x *.)).
          apply (lt_le_trans _ [q + ' e]).
          * apply rational_dedekind_lt; rewrite (plus_comm q).
            exact (fst (flip_lt_minus_l q r (' e)) lqr).
          * rewrite rational_dedekind_plus; apply lt_le.
            exact (strictly_order_preserving (+ [' e]) _ _ (snd (lt_rational_dedekind_l q y) lq)).
        + rewrite plus_mult_distr_l; apply lt_le.
          apply (lt_le_trans _ ([t] + [b] * [' e])).
          * apply plus_lt_compat; [exact lt|exact (strictly_order_preserving (.* [' e]) _ _ lb)].
          * rewrite <- rational_dedekind_mult, <- rational_dedekind_plus; cbn.
            rewrite mult_comm, recip_mult_cancel, <- plus_conjugate_alt; [reflexivity|exact bpos].
      - apply (Trunc_rec (n:=-1) (A:={t : Q & prod (1 < [t]) ([t] < x * y)})); [|exact (dedekindreals_archimedean _ _ l)].
        intros [t [lt lt']]; apply (rational_dedekind_lt 1 t) in lt.
        pose (e := mkQpos ((t - 1) / b) (pos_quotient _ _ (snd (flip_pos_minus _ _) lt) bpos)).
        assert (PropHolds (0 < [' e])) by exact (fst (rational_dedekind_lt 0 _) (is_pos e)).
        apply (Trunc_rec (n:=-1) (A:={q : Q & {r : Q & prod (prod (lower_cut y q) (upper_cut y r)) (r - q < ' e)}}));
          [|exact (cut_approximate y e)].
        intros [q [r [[lq ur] lqr]]]; change ([q] * x < 1) in lq.
        apply (irreflexivity (<) (1 : R)); rhs_V' exact lq.
        rewrite (mult_comm [q]).
        apply (le_lt_trans _ (x * (y - [' e]))).
        + rewrite plus_mult_distr_l, <- negate_mult_distr_r; apply lt_le.
          apply (le_lt_trans _ ([t] - [b] * [' e])).
          * rewrite <- rational_dedekind_mult, <- preserves_negate, <- rational_dedekind_plus; cbn.
            rewrite mult_comm, recip_mult_cancel, minus_minus_cancel; [reflexivity|exact bpos].
          * apply plus_lt_compat; [exact lt'|].
            apply (snd (flip_lt_negate _ _)).
            exact (strictly_order_preserving (.* [' e]) _ _ lb).
        + apply (strictly_order_preserving (x *.)), flip_lt_minus_l.
          apply (transitivity (snd (lt_rational_dedekind_r r y) ur)).
          rewrite <- rational_dedekind_plus; apply rational_dedekind_lt; rewrite (plus_comm q).
          exact (fst (flip_lt_minus_l q r (' e)) lqr).
    Qed.
  End pos_recip.

  Arguments pos_recip_dedekind x {xpos}.

  (** A real apart from zero has a positive square, so we can take [1 / x = x * (1 / (x * x))]. *)
  #[local] Instance recip_dedekindreals : Recip R
    := fun x => x.1 * @pos_recip_dedekind (x.1 * x.1) (square_pos x.1 x.2).

  #[export] Instance isfield_dedekindreals : IsField R.
  Proof.
    split.
    - exact _.
    - exact _.
    - exact _.
    - exact _.
    - exact _.
    - intros [x a]; cbn; unfold recip, recip_dedekindreals; cbn.
      rewrite mult_assoc; apply pos_recip_dedekind_inverse.
  Qed.

  #[export] Instance orderedfield_dedekindreals : OrderedField R.
  Proof.
    split; exact _.
  Qed.

End dedekind.

Arguments cut_lower_inhabited {Q _ lower upper} _.
Arguments cut_upper_inhabited {Q _ lower upper} _.
Arguments cut_lower_rounded {Q _ lower upper} _ _.
Arguments cut_upper_rounded {Q _ lower upper} _ _.
Arguments cut_transitive {Q _ lower upper} _ _ _ _ _.
Arguments cut_located {Q _ lower upper} _ _ _ _.

(** The operations on [DedekindReals Q] use the same operations on [Q], so as instances they would make the search for, say, [Lt ?A] loop by taking [?A] to be [DedekindReals ?A'] over and over.  We therefore only use them when the type is known to be the Dedekind reals. *)
#[export] Hint Extern 1 (Lt (DedekindReals _)) => exact (lt_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Le (DedekindReals _)) => exact (le_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Apart (DedekindReals _)) => exact (apart_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Plus (DedekindReals _)) => exact (plus_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Negate (DedekindReals _)) => exact (negate_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Zero (DedekindReals _)) => exact (zero_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (One (DedekindReals _)) => exact (one_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Join (DedekindReals _)) => exact (join_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Meet (DedekindReals _)) => exact (meet_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Mult (DedekindReals _)) => exact (mult_dedekindreals _) : typeclass_instances.
#[export] Hint Extern 1 (Recip (DedekindReals _)) => exact (recip_dedekindreals _) : typeclass_instances.

(** ** The Archimedean property and Cauchy completeness *)

(** We use a new section, so that the inclusion of the rationals into fields is not restricted to the universes used above: the Dedekind reals live in a universe above that of [Q]. *)
Section complete.
  Context `{Funext} `{Univalence}.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    {Qroundup : RoundUpStrict@{_ UQ _ UQ} Q}.

  Local Notation R := (DedekindReals Q (Qlt:=Qlt)).
  Local Notation "[ q ]" := (rational_dedekind Q q).

  (** The inclusion of the rationals into an ordered field is the unique semiring morphism, so on the Dedekind reals it is [rational_dedekind]. *)
  Lemma rationals_to_field_dedekindreals (q : Q) : rationals_to_field Q R q = [q].
  Proof.
    exact (rationals_initial (h:=rational_dedekind Q) q).
  Qed.

  #[export] Instance archimedean_dedekindreals : ArchimedeanProperty Q R.
  Proof.
    intros x y l; generalize (dedekindreals_archimedean Q x y l); apply Trunc_functor.
    intros [q lq]; exists q.
    exact (transport (fun z => prod (x < z) (z < y)) (rationals_initial (h:=rational_dedekind Q) q)^ lq).
  Qed.

  (** ** Cauchy completeness *)

  Section limit.
    Context (x : nat -> R) (M : Qpos Q -> nat) `{!CauchyModulus Q R x M}.

    (** Two terms beyond [M e] are [e]-close, so their cuts are too. *)
    Local Lemma modulus_cut_lt (e : Qpos Q) (m n : nat) (a b : Q)
      : (M e <= m)%nat -> (M e <= n)%nat -> lower_cut Q (x m) a -> upper_cut Q (x n) b -> a < b + ' e.
    Proof.
      intros lm ln la ub.
      assert (c := snd (cauchy_convergence Q R x e m n lm ln)).
      apply flip_lt_minus_l in c; unfold cast in c.
      rewrite (rationals_initial (h:=rational_dedekind Q)) in c.
      apply (snd (rational_dedekind_lt Q _ _)); rewrite plus_comm, (rational_dedekind_plus Q (Qroundup:=Qroundup)).
      lhs' exact (snd (lt_rational_dedekind_l Q a (x m)) la).
      lhs' exact c.
      exact (strictly_order_preserving ([' e] +) _ _ (snd (lt_rational_dedekind_r Q b (x n)) ub)).
    Qed.

    (** The limit: [q < l] when [q + e + d < x (M e)] for some [e] and [d], and dually. *)
    Local Definition limit_lower (q : Q) : HProp
      := Build_HProp (hexists (fun e : Qpos Q => hexists (fun d : Qpos Q =>
                       lower_cut Q (x (M e)) (q + ' e + ' d)))).
    Local Definition limit_upper (r : Q) : HProp
      := Build_HProp (hexists (fun e : Qpos Q => hexists (fun d : Qpos Q =>
                       upper_cut Q (x (M e)) (r - ' e - ' d)))).

    Local Lemma plus_minus_pos (q : Q) (e d : Qpos Q) : q - ' e - ' d + ' e + ' d = q.
    Proof.
      rewrite <- !plus_assoc, (plus_comm (' e) (' d)), (plus_assoc (- ' d)), plus_negate_l, plus_0_l.
      rewrite plus_negate_l; apply plus_0_r.
    Qed.

    Local Lemma plus_plus_minus (q : Q) (e d : Qpos Q) : q + ' e + ' d - ' e - ' d = q.
    Proof.
      rewrite <- !plus_assoc, (plus_assoc (' d) (- ' e)), (plus_comm (' d) (- ' e)).
      rewrite <- (plus_assoc (- ' e)), !plus_negate_r, plus_0_r, plus_negate_r; apply plus_0_r.
    Qed.

    Local Lemma plus_half_shift (q : Q) (e d : Qpos Q)
      : q + ' (d / 2) + ' e + ' (d / 2) = q + ' e + ' d.
    Proof.
      rhs exact (ap (fun z => q + ' e + ' z) (pos_split2 d)).
      change (q + ' (d / 2) + ' e + ' (d / 2) = q + ' e + (' (d / 2) + ' (d / 2))).
      rewrite <- (plus_assoc q (' (d / 2)) (' e)), (plus_comm (' (d / 2)) (' e)), plus_assoc.
      apply (plus_assoc _ (' (d / 2)) (' (d / 2)))^.
    Qed.

    Local Lemma minus_half_shift (r : Q) (e d : Qpos Q)
      : r - ' (d / 2) - ' e - ' (d / 2) = r - ' e - ' d.
    Proof.
      rhs exact (ap (fun z => r - ' e - ' z) (pos_split2 d)).
      change (r - ' (d / 2) - ' e - ' (d / 2) = r - ' e - (' (d / 2) + ' (d / 2))).
      rewrite negate_plus_distr.
      rewrite <- (plus_assoc r (- ' (d / 2)) (- ' e)), (plus_comm (- ' (d / 2)) (- ' e)), plus_assoc.
      apply (plus_assoc _ (- ' (d / 2)) (- ' (d / 2)))^.
    Qed.

    Local Lemma lt_plus_pos (q : Q) (e : Qpos Q) : q < q + ' e.
    Proof.
      exact (fst (pos_plus_lt_compat_r q (' e)) (is_pos e)).
    Qed.

    Local Lemma minus_pos_lt (q : Q) (e : Qpos Q) : q - ' e < q.
    Proof.
      exact (fst (pos_minus_lt_compat_r q (' e)) (is_pos e)).
    Qed.

    (** Two consequences of [modulus_cut_lt] that give transitivity of the limit cut. *)
    Local Lemma limit_transitive_aux (q s : Q) (e d : Qpos Q) : q + ' e + ' d < s + ' e -> q < s.
    Proof.
      intros l.
      rewrite <- (plus_assoc q), (plus_comm (' e)), plus_assoc in l.
      apply (strictly_order_reflecting (+ ' e)) in l.
      exact (transitivity (lt_plus_pos q d) l).
    Qed.

    Local Lemma limit_transitive_aux' (q r : Q) (e d e' d' : Qpos Q)
      : q + ' e + ' d < r - ' e' - ' d' + ' e' -> q < r.
    Proof.
      intros l.
      rewrite <- (plus_assoc (r - ' e')), (plus_comm (- ' d')), plus_assoc in l.
      rewrite <- (plus_assoc r), plus_negate_l, plus_0_r in l.
      lhs' exact (lt_plus_pos q e).
      lhs' exact (lt_plus_pos _ d).
      lhs' exact l.
      exact (minus_pos_lt r d').
    Qed.

    Local Lemma limit_located_aux (q r : Q) (e : Qpos Q)
      : ' e + ' e + ' e + ' e < r - q -> q + ' e + ' e < r - ' e - ' e.
    Proof.
      intros l.
      apply (snd (flip_lt_minus_r _ _ _)), (snd (flip_lt_minus_r _ _ _)).
      apply flip_lt_minus_r in l; rewrite plus_comm, !plus_assoc in l; exact l.
    Qed.

    Lemma isdedekindcut_limit : IsDedekindCut Q limit_lower limit_upper.
    Proof.
      split.
      - assert (a := cut_lower_inhabited (isdedekindcut Q (x (M 1)))); strip_truncations.
        destruct a as [a la]; apply tr; exists (a - ' 1 - ' 1); apply tr; exists 1; apply tr; exists 1.
        rewrite plus_minus_pos; exact la.
      - assert (b := cut_upper_inhabited (isdedekindcut Q (x (M 1)))); strip_truncations.
        destruct b as [b ub]; apply tr; exists (b + ' 1 + ' 1); apply tr; exists 1; apply tr; exists 1.
        rewrite plus_plus_minus; exact ub.
      - intros q; split.
        + intros p; strip_truncations; destruct p as [e p]; strip_truncations; destruct p as [d p].
          apply tr; exists (q + ' (d / 2)); split; [apply lt_plus_pos|].
          apply tr; exists e; apply tr; exists (d / 2).
          rewrite plus_half_shift; exact p.
        + intros p; strip_truncations; destruct p as [q' [l p]]; strip_truncations.
          destruct p as [e p]; strip_truncations; destruct p as [d p].
          apply tr; exists e; apply tr; exists d.
          refine (lower_cut_lt Q _ _ _ _ p).
          apply (strictly_order_preserving (+ ' d)), (strictly_order_preserving (+ ' e)), l.
      - intros r; split.
        + intros p; strip_truncations; destruct p as [e p]; strip_truncations; destruct p as [d p].
          apply tr; exists (r - ' (d / 2)); split; [apply minus_pos_lt|].
          apply tr; exists e; apply tr; exists (d / 2).
          rewrite minus_half_shift; exact p.
        + intros p; strip_truncations; destruct p as [r' [l p]]; strip_truncations.
          destruct p as [e p]; strip_truncations; destruct p as [d p].
          apply tr; exists e; apply tr; exists d.
          refine (upper_cut_lt Q _ _ _ _ p).
          apply (strictly_order_preserving (+ - ' d)), (strictly_order_preserving (+ - ' e)), l.
      - intros q r p p'; strip_truncations.
        destruct p as [e p], p' as [e' p']; strip_truncations.
        destruct p as [d p], p' as [d' p'].
        destruct (leq_dichotomy (M e) (M e')) as [lM|lM].
        + rhs_V' exact (minus_pos_lt r e').
          rhs_V' exact (minus_pos_lt _ d').
          exact (limit_transitive_aux q _ e d (modulus_cut_lt e _ _ _ _ (leq_refl _) lM p p')).
        + exact (limit_transitive_aux' q r e d e' d'
                   (modulus_cut_lt e' _ _ _ _ (leq_lt lM) (leq_refl _) p p')).
      - intros q r l.
        pose (k := Qpos_diff q r l); pose (e := k / 2 / 2 / 2).
        assert (le : ' e + ' e + ' e + ' e < r - q).
        { assert (h1 : ' e + ' e = ' (k / 2 / 2))
            by exact (ap (cast (Qpos Q) Q) (pos_split2 (k / 2 / 2)))^.
          assert (h2 : ' (k / 2 / 2) + ' (k / 2 / 2) = ' (k / 2))
            by exact (ap (cast (Qpos Q) Q) (pos_split2 (k / 2)))^.
          rewrite <- (plus_assoc (' e + ' e)), h1, h2.
          change (' (k / 2) < ' k).
          apply (transport (fun z => ' (k / 2) < ' z) (pos_split2 k)^), lt_plus_pos. }
        assert (c := cut_located (isdedekindcut Q (x (M e))) _ _ (limit_located_aux q r e le)).
        strip_truncations; destruct c as [c|c]; apply tr; [left|right];
          apply tr; exists e; apply tr; exists e; exact c.
    Qed.

    Definition limit_dedekind : R := Build_DedekindReals Q limit_lower limit_upper isdedekindcut_limit.

    Local Lemma rational_dedekind_minus (r h : Q) : [r - h] = [r] - [h].
    Proof.
      rewrite (rational_dedekind_plus Q (Qroundup:=Qroundup)); apply ap.
      exact (preserves_negate (f:=rational_dedekind Q) h).
    Qed.

    Local Lemma not_lt_flip_dedekind (a b : Q) : b < a -> ~ (a < b).
    Proof.
      intros l l'; exact (irreflexivity (<) a (transitivity l' l)).
    Qed.

    (** Beyond [M (e / 2)], the terms are at most [e / 2] above the limit. *)
    Local Lemma limit_minus_le (e : Qpos Q) (n : nat) : leq (M (e / 2)) n
      -> limit_dedekind - x n <= [' (e / 2)].
    Proof.
      intros ln; apply le_iff_not_lt_flip; intros l.
      apply flip_lt_minus_r in l.
      apply (Trunc_rec (n:=-1) (A:={r : Q & prod ([' (e / 2)] + x n < [r]) ([r] < limit_dedekind)}));
        [|exact (dedekindreals_archimedean Q _ _ l)].
      intros [r [lr lr']].
      apply (fst (lt_rational_dedekind_l Q r _)) in lr'.
      rewrite plus_comm in lr; apply flip_lt_minus_r in lr.
      rewrite <- rational_dedekind_minus in lr; apply (fst (lt_rational_dedekind_r Q _ _)) in lr.
      revert lr'; apply (Trunc_rec (n:=-1)); intros [e' p]; revert p.
      apply (Trunc_rec (n:=-1)); intros [d' p].
      destruct (leq_dichotomy (M (e / 2)) (M e')) as [lM|lM].
      - refine (not_lt_flip_dedekind _ _ _ (modulus_cut_lt (e / 2) _ _ _ _ lM ln p lr)).
        rewrite <- plus_assoc, plus_negate_l, plus_0_r.
        exact (transitivity (lt_plus_pos r e') (lt_plus_pos _ d')).
      - refine (not_lt_flip_dedekind _ _ _
                  (modulus_cut_lt e' _ _ _ _ (leq_refl _) (leq_trans (leq_lt lM) ln) p lr)).
        rhs_V' exact (lt_plus_pos _ d').
        apply (strictly_order_preserving (+ ' e')), minus_pos_lt.
    Qed.

    (** Beyond [M (e / 2)], the terms are at most [e / 2] below the limit. *)
    Local Lemma minus_limit_le (e : Qpos Q) (n : nat) : leq (M (e / 2)) n
      -> x n - limit_dedekind <= [' (e / 2)].
    Proof.
      intros ln; apply le_iff_not_lt_flip; intros l.
      apply flip_lt_minus_r in l.
      apply (Trunc_rec (n:=-1) (A:={r : Q & prod ([' (e / 2)] + limit_dedekind < [r]) ([r] < x n)}));
        [|exact (dedekindreals_archimedean Q _ _ l)].
      intros [r [lr lr']].
      apply (fst (lt_rational_dedekind_l Q r _)) in lr'.
      rewrite plus_comm in lr; apply flip_lt_minus_r in lr.
      rewrite <- rational_dedekind_minus in lr; apply (fst (lt_rational_dedekind_r Q _ _)) in lr.
      revert lr; apply (Trunc_rec (n:=-1)); intros [e' p]; revert p.
      apply (Trunc_rec (n:=-1)); intros [d' p].
      destruct (leq_dichotomy (M (e / 2)) (M e')) as [lM|lM].
      - refine (not_lt_flip_dedekind _ _ _ (modulus_cut_lt (e / 2) _ _ _ _ ln lM lr' p)).
        apply (lt_le_trans _ (r - ' (e / 2) + ' (e / 2))).
        + apply (strictly_order_preserving (+ ' (e / 2))).
          exact (transitivity (minus_pos_lt _ d') (minus_pos_lt _ e')).
        + rewrite <- plus_assoc, plus_negate_l, plus_0_r; apply reflexivity.
      - refine (not_lt_flip_dedekind _ _ _
                  (modulus_cut_lt e' _ _ _ _ (leq_trans (leq_lt lM) ln) (leq_refl _) lr' p)).
        apply (lt_le_trans _ (r - ' (e / 2) - ' e' + ' e')).
        + apply (strictly_order_preserving (+ ' e')), minus_pos_lt.
        + rewrite <- plus_assoc, plus_negate_l, plus_0_r; apply lt_le, minus_pos_lt.
    Qed.

    Lemma islimit_limit_dedekind : IsLimit Q R x limit_dedekind.
    Proof.
      intros e; apply tr; exists (M (e / 2)); intros n ln; unfold cast.
      rewrite (rationals_initial (h:=rational_dedekind Q)).
      assert (half : [' (e / 2)] < [' e]).
      { apply rational_dedekind_lt.
        apply (transport (fun z => ' (e / 2) < ' z) (pos_split2 e)^), lt_plus_pos. }
      split.
      - rewrite negate_swap_r; apply (snd (flip_lt_negate _ _)).
        exact (le_lt_trans _ _ _ (minus_limit_le e n ln) half).
      - exact (le_lt_trans _ _ _ (limit_minus_le e n ln) half).
    Qed.
  End limit.

  (** The Dedekind reals are Cauchy complete, with the limit given by [limit_dedekind]. *)
  #[export] Instance iscomplete_dedekindreals : IsComplete Q R.
  Proof.
    intros x M H'; exists (limit_dedekind x M); exact (islimit_limit_dedekind x M).
  Qed.
End complete.
