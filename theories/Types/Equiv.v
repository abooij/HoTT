(* -*- mode: coq; mode: visual-line -*- *)

Require Import HoTT.Basics.
Require Import Types.Prod Types.Sigma Types.Forall Types.Arrow Types.Paths.

Local Open Scope path_scope.

(** * Equivalences *)

Section AssumeFunext.
  Context `{Funext}.

  (** We begin by showing that, assuming function extensionality, [IsEquiv f] is an hprop. *)
  Global Instance hprop_isequiv {A B} `(f : A -> B)
  : IsHProp (IsEquiv f).
  Proof.
    (** We will show that assuming [f] is an equivalence, [IsEquiv f] decomposes into a sigma of two contractible types. *)
    apply hprop_inhabited_contr; intros feq.
    nrefine (contr_equiv' _ (issig_isequiv f oE (equiv_sigma_assoc' _ _)^-1)).
    snrefine (contr_equiv' _ (equiv_contr_sigma' _ (f^-1 ; eisretr f))^-1); only 2: exact _.
    (** Each of these types is equivalent to a based homotopy space. *)
    - refine (contr_equiv' { g : B -> A & g == f^-1 } _).
      apply equiv_functor_sigma_id; intros g.
      apply equiv_functor_forall_id; intros b.
      apply equiv_moveR_equiv_M.
    - refine (contr_equiv' { s : f^-1 o f == idmap & eissect f == s } _).
      apply equiv_functor_sigma_id; intros s; cbn.
      apply equiv_functor_forall_id; intros a.
      refine (equiv_concat_l (eisadj f a) _ oE _).
      rapply equiv_ap.
  Qed.

  (** Thus, paths of equivalences are equivalent to paths of functions. *)
  Lemma equiv_path_equiv {A B : Type} (e1 e2 : A <~> B)
  : (e1 = e2 :> (A -> B)) <~> (e1 = e2 :> (A <~> B)).
  Proof.
    equiv_via ((issig_equiv A B) ^-1 e1 = (issig_equiv A B) ^-1 e2).
    2: symmetry; apply equiv_ap; refine _.
    exact (equiv_path_sigma_hprop ((issig_equiv A B)^-1 e1) ((issig_equiv A B)^-1 e2)).
  Defined.

  Definition path_equiv {A B : Type} {e1 e2 : A <~> B}
  : (e1 = e2 :> (A -> B)) -> (e1 = e2 :> (A <~> B))
    := equiv_path_equiv e1 e2.

  Global Instance isequiv_path_equiv {A B : Type} {e1 e2 : A <~> B}
  : IsEquiv (@path_equiv _ _ e1 e2)
    (* Coq can find this instance by itself, but it's slow. *)
    := equiv_isequiv (equiv_path_equiv e1 e2).

  (** This implies that types of equivalences inherit truncation.  Note that we only state the theorem for [n.+1]-truncatedness, since it is not true for contractibility: if [B] is contractible but [A] is not, then [A <~> B] is not contractible because it is not inhabited.

   Don't confuse this lemma with [trunc_equiv], which says that if [A] is truncated and [A] is equivalent to [B], then [B] is truncated.  It would be nice to find a better pair of names for them. *)
  Global Instance istrunc_equiv {n : trunc_index} {A B : Type} `{IsTrunc n.+1 B}
  : IsTrunc n.+1 (A <~> B).
  Proof.
    simpl. intros e1 e2.
    apply (trunc_equiv _ (equiv_path_equiv e1 e2)).
  Defined.

  (** In the contractible case, we have to assume that *both* types are contractible to get a contractible type of equivalences. *)
  Global Instance contr_equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : Contr (A <~> B).
  Proof.
    exists equiv_contr_contr.
    intros e. apply path_equiv, path_forall. intros ?; apply contr.
  Defined.

  (** The type of *automorphisms* of an hprop is always contractible *)
  Global Instance contr_aut_hprop A `{IsHProp A}
  : Contr (A <~> A).
  Proof.
    exists 1%equiv.
    intros e; apply path_equiv, path_forall. intros ?; apply path_ishprop.
  Defined.

  (** Equivalences are functorial under equivalences. *)
  Definition functor_equiv {A B C D} (h : A <~> C) (k : B <~> D)
  : (A <~> B) -> (C <~> D)
  := fun f => ((k oE f) oE h^-1).

  Global Instance isequiv_functor_equiv {A B C D} (h : A <~> C) (k : B <~> D)
  : IsEquiv (functor_equiv h k).
  Proof.
    refine (isequiv_adjointify _
              (functor_equiv (equiv_inverse h) (equiv_inverse k)) _ _).
    - intros f; apply path_equiv, path_arrow; intros x; simpl.
      exact (eisretr k _ @ ap f (eisretr h x)).
    - intros g; apply path_equiv, path_arrow; intros x; simpl.
      exact (eissect k _ @ ap g (eissect h x)).
  Defined.

  Definition equiv_functor_equiv {A B C D} (h : A <~> C) (k : B <~> D)
  : (A <~> B) <~> (C <~> D)
  := Build_Equiv _ _ (functor_equiv h k) _.

  (** Reversing equivalences is an equivalence *)
  Global Instance isequiv_equiv_inverse {A B}
  : IsEquiv (@equiv_inverse A B).
  Proof.
    refine (isequiv_adjointify _ equiv_inverse _ _);
      intros e; apply path_equiv; reflexivity.
  Defined.

  Definition equiv_equiv_inverse A B
  : (A <~> B) <~> (B <~> A)
    := Build_Equiv _ _ (@equiv_inverse A B) _.

End AssumeFunext.
