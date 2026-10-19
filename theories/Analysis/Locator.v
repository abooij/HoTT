From HoTT Require Import
  Basics DProp Misc.BoundedSearch ExcludedMiddle
  Modalities.ReflectiveSubuniverse Modalities.Identity
  Classes.interfaces.abstract_algebra
  Classes.interfaces.orders
  Classes.interfaces.rationals
  Classes.interfaces.cauchy
  Classes.interfaces.archimedean
  Classes.interfaces.round
  Classes.interfaces.naturals
  Classes.implementations.peano_naturals
  Classes.orders.archimedean
  Classes.orders.dec_fields
  Classes.orders.lattices
  Classes.theory.apartness
  Classes.theory.rationals
  Classes.orders.fields
  Classes.orders.rationals
  Classes.orders.naturals
  Classes.theory.fields
  Classes.theory.dec_fields.

Generalizable Variables A Ale Alt.

(** ** Located pairs of predicates *)

Section located.
  Context `{IsDecField A} `{Apart A} `{!FullPseudoSemiRingOrder (A:=A) Ale Alt}
    `{!RoundUpStrict A}.
  Local Notation nA := (naturals_to_semiring nat A).

  (** A pair [L], [U] of predicates on [A] is located when for [q < r] we can, in a reflective subuniverse [O], choose between [L q] and [U r]. For the identity modality [purely] this is a locator, see below, and for the propositional truncation it is the locatedness of a Dedekind cut. *)
  Context (O : ReflectiveSubuniverse) (L U : A -> Type)
    (loc : forall q r, q < r -> O (sum (L q) (U r))).

  (** Walking up from [L q0] in steps of [d], we either find [q] with [L q] and [U (q + d + d)], or stay in [L]. *)
  Definition located_walk (d : A) (dpos : 0 < d) (q0 : A) (Lq0 : L q0) (n : nat)
    : O (sum {q : A & prod (L q) (U (q + d + d))} (L (q0 + nA n * d))).
  Proof.
    induction n as [|n IH].
    - apply to; right.
      rewrite (preserves_0 (f:=nA)), mult_0_l, plus_0_r; exact Lq0.
    - revert IH; apply O_rec; intros [found|Lq]; [exact (to O _ (inl found))|].
      set (q := q0 + nA n * d).
      assert (step : q0 + nA (S n) * d = q + d).
      { unfold q; rewrite nat_to_semiring_succ, plus_mult_distr_r, mult_1_l.
        rewrite (plus_comm d), plus_assoc; reflexivity. }
      refine (O_functor O _ (loc (q + d) (q + d + d) (fst (pos_plus_lt_compat_r _ _) dpos))).
      intros [Lqd|Uqdd].
      + right; rewrite step; exact Lqd.
      + left; exact (q; (Lq, Uqdd)).
  Defined.

  (** If moreover [L] lies below [U], then from [L q0] and [U r0] we find [q] with [L q] and [U (q + d + d)]: the walk passes [r0] after finitely many steps. *)
  Definition located_close (trans : forall q r, L q -> U r -> q < r)
    (d : A) (dpos : 0 < d) (q0 r0 : A) (Lq0 : L q0) (Ur0 : U r0)
    : O {q : A & prod (L q) (U (q + d + d))}.
  Proof.
    assert (PropHolds (0 < d)) by exact dpos.
    destruct (round_up_strict A ((r0 - q0) / d)) as [n ltn].
    refine (O_functor O _ (located_walk d dpos q0 Lq0 n)).
    intros [found|Lq]; [exact found|].
    apply Empty_rec, (irreflexivity (<) r0).
    transitivity (q0 + nA n * d).
    - rewrite plus_comm; apply flip_lt_minus_l.
      rewrite <- (mult_1_r (r0 - q0)), <- (dec_recip_inverse d (lt_ne_flip _ _ dpos)),
        (mult_comm d), mult_assoc.
      apply (strictly_order_preserving (.* d)); exact ltn.
    - exact (trans _ _ Lq Ur0).
  Defined.
End located.

Local Open Scope type_scope.

Section locator.
  Context (Q : Type).
  Context `{Qrats : Rationals Q}.
  Context {Qdec_paths : DecidablePaths Q}.
  Context {Qtriv : TrivialApart Q}.
  Context `{!Trichotomy (<)}.
  Context (F : Type).
  Context `{Forderedfield : OrderedField F}.
  Context {Fabs : Abs F}.
  Context {Farchimedean : ArchimedeanProperty Q F}.
  Context {Fcomplete : IsComplete Q F}.
  Context {Qroundup : RoundUpStrict Q}.

  Context `{Funext} `{Univalence}.

  (* Assume we have enumerations of the rationals, and of pairs of ordered rationals. *)
  Context (Q_eq : nat <~> Q).
  Context (QQpos_eq : nat <~> Q * Qpos Q).

  Instance qinc : Cast Q F := rationals_to_field Q F.

  (* Definition of a locator for a fixed real number. *)
  Definition locator (x : F) := forall q r : Q, q < r -> (' q < x) + (x < ' r).

  (* Alternative definition; see equivalence below *)
  Record locator' (x : F) :=
    { locates_right : forall q r : Q, q < r -> DHProp
    ; locates_right_true : forall q r : Q, forall nu : q < r, locates_right q r nu -> ' q < x
    ; locates_right_false : forall q r : Q, forall nu : q < r, ~ locates_right q r nu -> x < ' r
    }.

  Arguments locates_right       [x] _ [q] [r] _.
  Arguments locates_right_true  [x] _ [q] [r] _.
  Arguments locates_right_false [x] _ [q] [r] _.

  Definition locates_left {x : F} (l : locator' x) {q r : Q} : q < r -> DHProp :=
    fun nu => Build_DHProp (Build_HProp (~ (locates_right l nu))) _.

  Section classical.
    Context `{ExcludedMiddle}.

    Lemma all_reals_locators (x : F) : locator x.
    Proof.
      intros q r ltqr.
      case (LEM (' q < x)).
      - exact _.
      - exact inl.
      - intros notlt.
        apply inr.
        assert (ltqr' : ' q < ' r)
          by auto.
        exact (nlt_lt_trans notlt ltqr').
    Qed.

  End classical.

  Section rational.
    Context (s : Q).

    Lemma locator_left : locator (' s).
    Proof.
      intros q r ltqr.
      destruct (trichotomy _ q s) as [ltqs|[eqqs|ltsq]].
      - apply inl. apply (strictly_order_preserving _); assumption.
      - rewrite eqqs in ltqr. apply inr, (strictly_order_preserving _); assumption.
      - apply inr, (strictly_order_preserving _), (transitivity ltsq ltqr); assumption.
    Qed.

    Definition locator_second : locator (' s).
    Proof.
      intros q r ltqr.
      destruct (trichotomy _ s r) as [ltsr|[eqsr|ltrs]].
      - apply inr, (strictly_order_preserving _); assumption.
      - rewrite <- eqsr in ltqr. apply inl, (strictly_order_preserving _); assumption.
      - apply inl, (strictly_order_preserving _), (transitivity ltqr ltrs).
    Qed.

  End rational.

  Section logic.

    Context {x : F}.

    Definition locator_locator' : locator x -> locator' x.
    Proof.
      intros l.
      refine (Build_locator' x (fun q r nu => Build_DHProp (Build_HProp (is_inl (l q r nu))) _) _ _).
      - intros q r nu. simpl. apply un_inl.
      - intros q r nu. simpl. destruct (l q r nu) as [ltqx|].
        + simpl; intros f; destruct (f tt).
        + intros ?; assumption.
    Defined.

    Definition locator'_locator : locator' x -> locator x.
    Proof.
      intros l' q r nu.
      destruct (dec (locates_right l' nu)) as [yes|no].
      - apply inl. exact (locates_right_true l' nu yes).
      - apply inr. exact (locates_right_false l' nu no).
    Defined.
  End logic.

  Section logic2.

    Context {x : F}.

    Coercion locator_locator' : locator >-> locator'.

    Definition locator_locator'_locator (l : locator x) : locator'_locator (locator_locator' l) = l.
    Proof.
      apply path_forall; intros q.
      apply path_forall; intros r.
      apply path_forall; intros nu.
      unfold locator'_locator, locator_locator'. simpl.
      destruct (l q r nu); auto.
    Qed.

    Local Definition locsig : _ <~> locator' x := ltac:(issig).

    Lemma locator'_locator_locator' (l' : locator' x)
      : locator_locator' (locator'_locator l') = l'.
    Proof.
      enough (p : locsig ^-1 (locator_locator' (locator'_locator l')) = locsig ^-1 l').
      - exact (equiv_inj (locsig ^-1) p).
      - unfold locsig; simpl.
        destruct l'; unfold locator'_locator, locator_locator'; simpl.
        apply path_sigma_hprop; simpl.
        apply path_forall; intro q;
          apply path_forall; intro r;
            apply path_arrow; intro nu.
        apply equiv_path_dhprop; simpl.
        rewrite (path_dec (locates_right0 q r nu)).
        destruct (dec (locates_right0 q r nu)); auto.
    Qed.

    Definition equiv_locator_locator' : locator x <~> locator' x
      := equiv_adjointify
           locator_locator'
           locator'_locator
           locator'_locator_locator'
           locator_locator'_locator.

    Lemma nltqx_locates_left {q r : Q} (l' : locator' x) (ltqr : q < r)
      : ~ (' q < x) -> locates_left l' ltqr.
    Proof.
      assert (f := locates_right_true l' ltqr).
      exact (not_contrapositive f).
    Qed.

    Lemma ltxq_locates_left {q r : Q} (l' : locator' x) (ltqr : q < r)
      : x < ' q -> locates_left l' ltqr.
    Proof.
      intros ltxq. apply nltqx_locates_left.
      apply lt_flip; assumption.
    Qed.

    Lemma nltxr_locates_right {q r : Q} (l' : locator' x) (ltqr : q < r)
      : ~ (x < ' r) -> locates_right l' ltqr.
    Proof.
      intros nltxr.
      apply stable.
      assert (f := locates_right_false l' ltqr).
      exact (not_contrapositive f nltxr).
    Qed.

    Lemma ltrx_locates_right {q r : Q} (l' : locator' x) (ltqr : q < r)
      : 'r < x -> locates_right l' ltqr.
    Proof.
      intros ltrx. apply nltxr_locates_right.
      apply lt_flip; assumption.
    Qed.

  End logic2.

  Local Definition ltQnegQ (q : Q) (eps : Qpos Q) : q - 'eps < q.
  Proof.
    apply (pos_minus_lt_compat_r q ('eps)), eps.
  Qed.
  
  Local Open Scope mc_scope.

  Local Definition ltQposQ (q : Q) (eps : Qpos Q) : q < q + 'eps.
  Proof.
    apply (pos_plus_lt_compat_r q ('eps)), eps.
  Qed.

  Section bounds.
    (* Given a real with a locator, we can find (integer) bounds. *)
    Context {x : F}
            (l : locator x).

    Local Definition ltN1 (q : Q) : q - 1 < q := ltQnegQ q 1.

    Local Definition P_lower (q : Q) : Type := locates_right l (ltN1 q).

    Definition P_lower_prop {k} : IsHProp (P_lower k).
    Proof.
      apply _.
    Qed.

    Local Definition ltxN1 : x - 1 < x := (fst (pos_minus_lt_compat_r x 1) lt_0_1).

    Local Definition P_lower_inhab : hexists (fun q => P_lower q).
    Proof.
      assert (hqlt : hexists (fun q => ' q < x)).
      {
        assert (hex := archimedean_property Q F (x-1) x ltxN1).
        refine (Trunc_rec _ hex); intros hex'.
        apply tr.
        destruct hex' as [q [ltx1q ltqx]]; exists q; assumption.
      }
      refine (Trunc_rec _ hqlt); intros hqlt'.
      induction hqlt' as [q lt].
      apply tr.
      exists q.
      unfold P_lower.
      apply ltrx_locates_right; assumption.
    Qed.

    Definition lower_bound : {q : Q | ' q < x}.
    Proof.
      assert (qP_lower : {q : Q | P_lower q})
        by exact (minimal_n_alt_type Q Q_eq P_lower _ P_lower_inhab).
      destruct qP_lower as [q Pq].
      exists (q - 1).
      unfold P_lower in Pq. simpl in *.
      exact (un_inl _ Pq).
    Qed.

    Local Definition lt1N (r : Q) : r < r + 1 := ltQposQ r 1.

    Local Definition P_upper (r : Q) : DHProp := locates_left l (lt1N r).

    Definition P_upper_prop {k} : IsHProp (P_upper k).
    Proof.
      apply _.
    Qed.

    Local Definition ltx1N : x < x + 1 := (fst (pos_plus_lt_compat_r x 1) lt_0_1).

    Local Definition P_upper_inhab : hexists (fun r => P_upper r).
    Proof.
      assert (hqlt : hexists (fun r => x < ' r)).
      {
        assert (hex := archimedean_property Q F x (x+1) ltx1N).
        refine (Trunc_rec _ hex); intros hex'.
        apply tr.
        destruct hex' as [r [ltxr ltrx1]]; exists r; assumption.
      }
      refine (Trunc_rec _ hqlt); intros hqlt'.
      induction hqlt' as [r lt].
      apply tr.
      exists r.
      unfold P_upper.
      apply ltxq_locates_left; assumption.
    Qed.

    Definition upper_bound : {r : Q | x < ' r}.
    Proof.
      assert (rP_upper : {r : Q | P_upper r})
        by exact (minimal_n_alt_type Q Q_eq P_upper _ P_upper_inhab).
      destruct rP_upper as [r Pr].
      exists (r + 1).
      unfold P_upper in Pr. simpl in *.
      destruct (l r (r + 1) (lt1N r)).
      - simpl in Pr. destruct (Pr tt).
      - assumption.
    Qed.

    (** Using the locator on a grid of step [epsilon / 2] between a lower and an upper bound, we find bounds which are [epsilon] apart. *)
    Definition tight_bound (epsilon : Qpos Q) : {u : Q | ' u < x < ' (u + ' epsilon)}.
    Proof.
      destruct lower_bound as [q ltqx], upper_bound as [r ltxr].
      destruct (located_close purely (fun q => ' q < x) (fun r => x < ' r) l
                  (fun q r ltqx ltxr => strictly_order_reflecting _ _ _ (transitivity ltqx ltxr))
                  (' (epsilon / 2)) (is_pos _) q r ltqx ltxr) as [u [ltux ltxu]].
      exists u; split; [exact ltux|].
      rewrite (pos_split2 epsilon); change (x < ' (u + (' (epsilon / 2) + ' (epsilon / 2)))).
      rewrite plus_assoc; exact ltxu.
    Defined.

  End bounds.

  (** ** Locators and rational approximations *)

  (** A real number has a locator exactly when it has rational approximations of any precision. *)
  Definition locator_approx {x : F} (l : locator x) (e : Qpos Q)
    : {p : Q | ' (p - ' e) < x < ' (p + ' e)}.
  Proof.
    destruct (tight_bound l e) as [u [ltux ltxu]].
    exists u; split; [|exact ltxu].
    rhs_V' exact ltux.
    apply (strictly_order_preserving _), ltQnegQ.
  Defined.

  (** A real number that has rational approximations of any precision has a locator. *)
  Definition locator_from_approx {z : F}
    (approx : forall e : Qpos Q, {p : Q | ' (p - ' e) < z < ' (p + ' e)})
    : locator z.
  Proof.
    intros q r ltqr.
    set (e := (Qpos_diff q r ltqr) / 2).
    assert (qeer : q + ' e + ' e = r).
    { assert (p : q + ' e = r - ' e)
        by (rewrite path_avg_split_diff_l, path_avg_split_diff_r; reflexivity).
      rewrite p, <- plus_assoc, plus_negate_l, plus_0_r; reflexivity. }
    destruct (approx e) as [p [ltpz ltzp]].
    destruct (trichotomy _ (q + ' e) p) as [ltqep|[eqqep|ltpqe]].
    - apply inl. rhs_V' exact ltpz.
      apply (strictly_order_preserving _), flip_lt_minus_r; assumption.
    - apply inl. rewrite <- eqqep, <- plus_assoc, plus_negate_r, plus_0_r in ltpz.
      exact ltpz.
    - apply inr. lhs' exact ltzp.
      rapply strictly_order_preserving.
      rewrite <- qeer.
      apply (strictly_order_preserving (+ ' e)); assumption.
  Defined.

  (** Splitting an interval in three. *)
  Local Lemma lt_trisect (q r : Q) (ltqr : q < r)
    : q + ' (Qpos_diff q r ltqr / 3) < r - ' (Qpos_diff q r ltqr / 3).
  Proof.
    set (d := Qpos_diff q r ltqr); set (e := d / 3).
    assert (p : r - ' e = q + ' e + ' e).
    { rewrite (plus_conjugate_alt r q); change (q + ' d - ' e = q + ' e + ' e).
      rewrite (ap (cast (Qpos Q) Q) (pos_split3 d)); change (q + (' e + ' e + ' e) - ' e = q + ' e + ' e).
      rewrite <- plus_assoc, <- (plus_assoc (' e + ' e)), plus_negate_r, plus_0_r, plus_assoc.
      reflexivity. }
    rewrite p; apply ltQposQ.
  Qed.

  (** A real number which is arbitrarily close to real numbers with locators has a locator: for [q < r], we use the locator of a real number within [(r - q) / 3]. *)
  Definition locator_close {z : F}
    (approx : forall e : Qpos Q, {y : F & prod (locator y) (y - ' (' e) < z < y + ' (' e))})
    : locator z.
  Proof.
    intros q r ltqr.
    set (e := Qpos_diff q r ltqr / 3).
    destruct (approx e) as [y [ly [lo hi]]].
    destruct (ly _ _ (lt_trisect q r ltqr)) as [lt|lt]; [left|right].
    - rewrite (preserves_plus (f:=cast Q F)) in lt.
      rhs_V' exact lo.
      exact (snd (flip_lt_minus_r _ _ _) lt).
    - rewrite (preserves_minus (f:=cast Q F)) in lt.
      lhs' exact hi.
      exact (fst (flip_lt_minus_r _ _ _) lt).
  Defined.

  (** Halves of a positive rational. *)
  Local Lemma qpos_halves (e : Qpos Q) : ' e = ' (e / 2) + ' (e / 2).
  Proof.
    exact (ap (cast (Qpos Q) Q) (pos_split2 e)).
  Qed.

  Local Lemma plus_swap_middle (a b c d : Q) : a + b + (c + d) = a + c + (b + d).
  Proof.
    rewrite <- !plus_assoc; apply ap.
    rewrite !plus_assoc; apply (ap (+ d)), plus_comm.
  Qed.


  Section arch_struct.

    Context {x y : F}
            (l : locator x)
            (m : locator y)
            (ltxy : x < y).

    Local Definition P (qeps' : Q * Qpos Q) : Type :=
      match qeps' with
      | (q' , eps') =>
        (prod
           (locates_left l (ltQnegQ q' eps'))
           (locates_right m (ltQposQ q' eps')))
      end.

    Local Definition P_isHProp qeps' : IsHProp (P qeps').
    Proof.
      destruct qeps' as [q eps'].
      exact istrunc_prod.
    Qed.

    Local Definition P_dec qeps' : Decidable (P qeps').
    Proof.
      destruct qeps' as [q eps'].
      unfold P.
      exact _.
    Qed.

    Local Definition P_inhab : hexists P.
    Proof.
      assert (hs := (archimedean_property Q F x y ltxy)).
      refine (Trunc_ind _ _ hs); intros [s [ltxs ltsy]].
      assert (ht := (archimedean_property Q F ('s) y ltsy)).
      refine (Trunc_ind _ _ ht); intros [t [ltst' ltty]].
      set (q := (t + s) / 2).
      assert (ltst : s < t).
      {
        Existing Instance full_pseudo_order_reflecting.
        exact (strictly_order_reflecting _ _ _ ltst').
      }
      set (epsilon := (Qpos_diff s t ltst) / 2).
      apply tr.
      exists (q, epsilon).
      unfold P; split.
      - apply ltxq_locates_left.
        assert (q - ' epsilon = s) as ->.
        {
          unfold q; cbn.
          rewrite <- path_avg_split_diff_l.
          rewrite <- (plus_assoc s ((t-s)/2) (-((t-s)/2))).
          rewrite plus_negate_r.
          rewrite plus_0_r.
          reflexivity.
        }
        assumption.
      - apply ltrx_locates_right.
        assert (q + ' epsilon = t) as ->.
        {
          unfold q; cbn.
          rewrite <- path_avg_split_diff_r.
          rewrite <- (plus_assoc t (-((t-s)/2)) ((t-s)/2)).
          rewrite plus_negate_l.
          rewrite plus_0_r.
          reflexivity.
        }
        assumption.
    Qed.

    Definition archimedean_structure : {q : Q | x < 'q < y}.
    Proof.
      assert (R : sig P).
      {
        apply minimal_n_alt_type.
        - exact QQpos_eq.
        - exact P_dec.
        - exact P_inhab.
      }
      unfold P in R.
      destruct R as [[q eps] [lleft mright]].
      exists q; split.
      - exact (locates_right_false l _ lleft).
      - exact (locates_right_true  m _ mright).
    Qed.

  End arch_struct.

  (** For reals [x] and [y] with locators and a rational [s], if [x < y] then we can choose between [x < s] and [s < y]. *)
  Definition locator_cotransitive_rational {x y : F} (l : locator x) (m : locator y) (s : Q)
    : x < y -> (x < ' s) + (' s < y).
  Proof.
    intros ltxy.
    destruct (archimedean_structure l m ltxy) as [q [ltxq ltqy]].
    destruct (trichotomy _ q s) as [ltqs|[eqqs|ltsq]].
    - apply inl; lhs' exact ltxq.
      rapply strictly_order_preserving; assumption.
    - apply inl; rewrite <- eqqs; assumption.
    - apply inr; rhs_V' exact ltqy.
      rapply strictly_order_preserving; assumption.
  Defined.

  (** Strong cotransitivity: for reals [x < y] with locators and a real [z] with a locator, we can choose between [x < z] and [z < y]. *)
  Definition locator_cotransitive {x y z : F} (l : locator x) (m : locator y) (n : locator z)
    : x < y -> (x < z) + (z < y).
  Proof.
    intros ltxy.
    destruct (archimedean_structure l m ltxy) as [q [ltxq ltqy]].
    destruct (archimedean_structure (locator_left q) m ltqy) as [r [ltqr ltry]].
    destruct (n q r (strictly_order_reflecting _ _ _ ltqr)) as [ltqz|ltzr].
    - exact (inl (transitivity ltxq ltqz)).
    - exact (inr (transitivity ltzr ltry)).
  Defined.

  Section unary_ops.

    Context {x : F}
            (l : locator x).

    Definition locator_minus : locator (-x).
    Proof.
      intros q r ltqr.
      assert (ltnrnq := snd (flip_lt_negate q r) ltqr : -r < -q).
      destruct (l _ _ ltnrnq) as [ltnrx|ltxnq].
      - apply inr. apply char_minus_left. rewrite <- preserves_negate. assumption.
      - apply inl. apply char_minus_right. rewrite <- preserves_negate. assumption.
    Qed.

    Section recip_pos.
      Context (xpos : 0 < x).

      Local Definition recip_nu := positive_apart_zero x xpos.

      Definition locator_recip_pos : locator (// (x ; recip_nu)).
      Proof.
        assert (recippos : 0 < // (x ; recip_nu))
          by apply pos_recip_compat.
        intros q r ltqr. destruct (trichotomy _ q 0) as [qneg|[qzero|qpos]].
        + apply inl. refine (transitivity _ _).
          * apply (strictly_order_preserving _). exact qneg.
          * rewrite preserves_0; assumption.
        + apply inl. rewrite qzero, preserves_0; assumption.
        + assert (qap0 : q ≶ 0)
            by exact (pseudo_order_lt_apart_flip _ _ qpos).
          assert (rap0 : r ≶ 0).
          {
            refine (pseudo_order_lt_apart_flip _ _ _).
            exact (transitivity qpos ltqr).
          }
          assert (ltrrrq : / r < / q)
            by (apply flip_lt_dec_recip; assumption).
          destruct (l (/r) (/q) ltrrrq) as [ltrrx|ltxrq].
          * apply inr.
            assert (rpos : 0 < r)
              by (transitivity q; assumption).
            assert (rpos' : 0 < ' r).
            {
              rewrite <- (@preserves_0 Q F _ _ _ _ _ _ _ _ _ _).
              apply strictly_order_preserving; try exact _; assumption.
            }
            rewrite (dec_recip_to_recip r (positive_apart_zero ('r) rpos')) in ltrrx.
            assert (ltxrr := flip_lt_recip_l x ('r) rpos' ltrrx).
            cbn in ltxrr.
            rewrite
              (recip_irrelevant
                 x
                 (positive_apart_zero
                    x
                    (transitivity (pos_recip_compat (' r) rpos') ltrrx)) recip_nu) in ltxrr.
            exact ltxrr.
          * apply inl.
            assert (qpos' : 0 < ' q).
            {
              rewrite <- (@preserves_0 Q F _ _ _ _ _ _ _ _ _ _).
              apply strictly_order_preserving; try exact _; assumption.
            }
            rewrite (dec_recip_to_recip q (positive_apart_zero ('q) qpos')) in ltxrq.
            assert (ltrqx := flip_lt_recip_r ('q) x qpos' xpos ltxrq).
            rewrite (recip_irrelevant x (positive_apart_zero x xpos) recip_nu) in ltrqx.
            exact ltrqx.
      Qed.
    End recip_pos.

  End unary_ops.

  Section recip_neg.
    Context {x : F}
            (l : locator x)
            (xneg : x < 0).

    Local Definition recip_neg_nu := negative_apart_zero x xneg.

    Definition locator_recip_neg : locator (// (x ; recip_neg_nu)).
    Proof.
      assert (negxpos : 0 < (-x))
        by (apply flip_neg_negate; assumption).
      assert (l' := locator_minus (locator_recip_pos (locator_minus l) negxpos)).
      rewrite (recip_negate (-x)) in l'.
      unfold negate_apart in l'.
      rewrite
        (recip_proper_alt
           (- - x)
           x
           (apart_negate (- x) (positive_apart_zero (- x) negxpos)) recip_neg_nu)
        in l'.
      - assumption.
      - apply negate_involutive.
    Qed.

  End recip_neg.

  Section unary_ops2.

    Context {x : F}
            (l : locator x)
            (nu : x ≶ 0).

    Definition locator_recip : locator (// (x ; nu)).
    Proof.
      destruct (fst (apart_iff_total_lt x 0) nu) as [xneg|xpos].
      - set (l' := locator_recip_neg l xneg).
        rewrite (recip_proper_alt x x (negative_apart_zero x xneg) nu) in l';
          try reflexivity; exact l'.
      - set (l' := locator_recip_pos l xpos).
        rewrite (recip_proper_alt x x (positive_apart_zero x xpos) nu) in l';
          try reflexivity; exact l'.
    Qed.

  End unary_ops2.

  Section binary_ops.

    Context {x y : F}
            (l : locator x)
            (m : locator y).

    (** Approximations of [x] and [y] up to [e / 2] give an approximation of [x + y] up to [e]. *)
    Definition locator_plus : locator (x + y).
    Proof.
      apply locator_from_approx; intros e.
      destruct (locator_approx l (e / 2)) as [p [ltpx ltxp]],
        (locator_approx m (e / 2)) as [p' [ltpy ltyp]].
      exists (p + p'); split.
      - rewrite qpos_halves, negate_plus_distr, plus_swap_middle, (preserves_plus (f:=cast Q F)).
        exact (plus_lt_compat _ _ _ _ ltpx ltpy).
      - rewrite qpos_halves, plus_swap_middle, (preserves_plus (f:=cast Q F)).
        exact (plus_lt_compat _ _ _ _ ltxp ltyp).
    Defined.

    Lemma locator_meet : locator (meet x y).
    Proof.
      intros q r ltqr.
      destruct (l q r ltqr, m q r ltqr) as [[ltqx|ltxr] [ltqy|ltyr]].
      - apply inl, meet_lt_l; assumption.
      - apply inr, meet_lt_r_r; assumption.
      - apply inr, meet_lt_r_l; assumption.
      - apply inr, meet_lt_r_r; assumption.
    Qed.

    Lemma locator_join : locator (join x y).
    Proof.
      intros q r ltqr.
      destruct (l q r ltqr, m q r ltqr) as [[ltqx|ltxr] [ltqy|ltyr]].
      - apply inl, join_lt_l_l; assumption.
      - apply inl, join_lt_l_l; assumption.
      - apply inl, join_lt_l_r; assumption.
      - apply inr, join_lt_r; assumption.
    Qed.

  End binary_ops.

  Section times.

    (** For positive rationals [Z] and [e], a rational [0 < d < 1] with [d (2 Z + 1) < e]: we take [d = e / (e + 2 Z + 1)]. *)
    Local Definition mult_precision (Z : Q) (Zpos : 0 < Z) (e : Qpos Q)
      : {d : Q & prod (prod (0 < d) (d < 1)) (d * (Z + Z + 1) < ' e)}.
    Proof.
      assert (Z1pos : 0 < Z + Z + 1).
      { apply pos_plus_compat; [apply pos_plus_compat; assumption|exact lt_0_1]. }
      set (K := ' e + (Z + Z + 1)).
      assert (Kpos : 0 < K) by (apply pos_plus_compat; [apply e|exact Z1pos]).
      set (d := ' e / K).
      assert (dpos : 0 < d)
        by (apply pos_mult; [apply e|apply pos_dec_recip_compat, Kpos]).
      assert (dK : d * K = ' e).
      { unfold d. rewrite <- (associativity (' e)), (commutativity (/ K)).
        rewrite dec_recip_inverse; [apply mult_1_r|].
        apply lt_ne_flip, Kpos. }
      exists d; refine ((dpos, _), _).
      - apply (strictly_order_reflecting (.* K)).
        rewrite dK, mult_1_l.
        exact (fst (pos_plus_lt_compat_r _ _) Z1pos).
      - rewrite <- dK. unfold K.
        rewrite (plus_mult_distr_l d (' e) (Z + Z + 1)), (commutativity (d * ' e)).
        apply (fst (pos_plus_lt_compat_r _ _)), pos_mult; [assumption|apply e].
    Defined.

    (** If [u < v < u + d], then [v] is within [d] of [u]. *)
    Local Lemma lt_bound_tight {u v d : F} (dpos : 0 < d) (ltuv : u < v) (ltvu : v < u + d)
      : - d < v - u < d.
    Proof.
      split.
      - rhs_V' exact (snd (flip_pos_minus _ _) ltuv).
        apply flip_pos_negate, dpos.
      - apply flip_lt_minus_l; rewrite (commutativity d); assumption.
    Qed.

    (** If moreover [- Z < v < Z] and [d < 1], then [- (Z + 1) < u < Z + 1]. *)
    Local Lemma lt_bound_tight_succ {u v d Z : F} (d1 : d < 1) (ltuv : u < v) (ltvu : v < u + d)
      (ltZv : - Z < v < Z)
      : - (Z + 1) < u < Z + 1.
    Proof.
      split.
      - rewrite negate_plus_distr.
        rhs_V' exact (snd (flip_lt_minus_l _ _ _) ltvu).
        apply plus_lt_compat; [apply ltZv|].
        apply (snd (flip_lt_negate _ _)); assumption.
      - refine (transitivity ltuv (transitivity (snd ltZv) _)).
        apply (fst (pos_plus_lt_compat_r _ _)), lt_0_1.
    Qed.

    Context {x y : F}
            (l : locator x)
            (m : locator y).

    (** If [x] and [y] have locators, then so does [x * y]. *)
    Definition locator_times : locator (x * y).
    Proof.
      (* The absolute values of [x] and [y], and hence their maximum, have locators. This gives a rational bound [Z]. *)
      destruct (upper_bound (locator_join (locator_join l (locator_minus l))
                                          (locator_join m (locator_minus m))))
        as [Z ltJZ].
      destruct (between_join_negate x y (' Z) ltJZ) as [ltZx ltZy].
      assert (Zpos : 0 < Z).
      { apply (strictly_order_reflecting qinc).
        rewrite preserves_0.
        exact (pos_between_negate _ _ ltZx). }
      apply locator_from_approx; intros e.
      (* We approximate [x] and [y] up to [d], so that [x y] is approximated up to [Z d + d (Z + 1) < e]. *)
      destruct (mult_precision Z Zpos e) as [d [[dpos ltd1] ltdZe]].
      destruct (tight_bound l (mkQpos d dpos)) as [a [ltax ltxa]].
      destruct (tight_bound m (mkQpos d dpos)) as [c [ltcy ltyc]].
      exists (a * c).
      rewrite (preserves_plus (f:=cast Q F)) in ltxa, ltyc.
      change (' (mkQpos d dpos)) with d in ltxa, ltyc.
      assert (dpos' : (0 : F) < ' d).
      { rewrite <- (preserves_0 (f:=cast Q F)); apply (strictly_order_preserving _), dpos. }
      assert (ltd1' : ' d < (1 : F)).
      { rewrite <- (preserves_1 (f:=cast Q F)); apply (strictly_order_preserving _), ltd1. }
      destruct (mult_minus_mult_lt_bound x y (' a) (' c) (' Z) (' Z + 1) (' d)
                  ltZx (lt_bound_tight_succ ltd1' ltcy ltyc ltZy)
                  (lt_bound_tight dpos' ltax ltxa) (lt_bound_tight dpos' ltcy ltyc))
        as [lo hi].
      assert (ltbound : ' Z * ' d + ' d * (' Z + 1) < ' (' e)).
      { assert (p : ' Z * ' d + ' d * (' Z + 1) = ' (d * (Z + Z + 1))).
        { rewrite (preserves_mult (f:=cast Q F)), 2!(preserves_plus (f:=cast Q F)),
            (preserves_1 (f:=cast Q F)).
          rewrite (commutativity (' Z) (' d)), <- plus_mult_distr_l, plus_assoc.
          reflexivity. }
        rewrite p; apply (strictly_order_preserving _), ltdZe. }
      rewrite (preserves_minus (f:=cast Q F) (a * c) (' e)),
        (preserves_plus (f:=cast Q F) (a * c) (' e)), (preserves_mult (f:=cast Q F) a c).
      split.
      - rewrite (commutativity (' a * ' c)).
        apply flip_lt_minus_r.
        exact (transitivity (snd (flip_lt_negate _ _) ltbound) lo).
      - rewrite (commutativity (' a * ' c)).
        apply flip_lt_minus_l.
        exact (transitivity hi ltbound).
    Defined.

  End times.

  Section limit.

    Context {xs : nat -> F}.
    Context {M} {M_ismod : CauchyModulus Q F xs M}.
    Context (ls : forall n, locator (xs n)).

    (** The limit is within [e] of [xs (M (e / 2))]. *)
    Lemma locator_limit {l} : IsLimit _ _ xs l -> locator l.
    Proof.
      intros islim; apply locator_close; intros e.
      exact (xs (M (e / 2)); (ls _, modulus_close_limit Q F xs islim e)).
    Qed.

  End limit.

End locator.
