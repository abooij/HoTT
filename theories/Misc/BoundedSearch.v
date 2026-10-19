(** * Bounded Search *)

(** The main result of this file is [minimal_n], which say that if [P : nat -> Type] is a family such that each [P n] is decidable and [{n & P n}] is merely inhabited, then [{n & P n}] is inhabited.  Since [P n] is decidable, it is sufficient to prove [{n & merely (P n)}], and to do this, we prove the stronger claim that there is a *minimal* [n] satisfying [merely (P n)].  This stronger claim is a proposition, which is what makes the argument work.  Along the way, we also prove that [{ l : nat & (l <= n) * P l }] is decidable for each [n]. *)

Require Import Basics.Overture Basics.Decidable Basics.Trunc Basics.Tactics.
Require Import Types.Sigma Types.Prod.
Require Import Truncations.Core Modalities.ReflectiveSubuniverse.
Require Import Spaces.Nat.Core.

Section bounded_search.

  Context (P : nat -> Type) (P_dec : forall n, Decidable (P n)).
  
  (** We open [type_scope] again after [nat_scope] in order to use the product type notation. *)
  Local Open Scope nat_scope.
  Local Open Scope type_scope.
  
  Local Definition minimal (n : nat) : Type := forall m : nat, P m -> n <= m.

  (** If we assume [Funext], then [minimal n] is a proposition.  But to avoid needing [Funext], we propositionally truncate it. *)
  Local Definition min_n_Type : Type := { n : nat & merely (P n) * merely (minimal n) }.

  Local Instance ishpropmin_n : IsHProp min_n_Type.
  Proof.
    apply ishprop_sigma_disjoint.
    intros n n' [p m] [p' m'].
    strip_truncations.
    apply leq_antisym.
    - exact (m n' p').
    - exact (m' n p).
  Defined.

  Local Definition smaller (n : nat) := { l : nat & P l * minimal l * (l <= n) }.

  Local Definition smaller_S (n : nat) (k : smaller n) : smaller (S n).
  Proof.
    destruct k as [l [[p m] z]].
    exists l.
    repeat split.
    1,2: assumption.
    exact _.
  Defined.

  Local Definition bounded_search (n : nat) : smaller n + forall l : nat, (l <= n) -> not (P l).
  Proof.
    induction n as [|n IHn].
    - destruct (dec (P 0)) as [h|n].
      + left.
        exact (0; (h, fun _ _ => _, _)).
      + right.
        intros l lleq0.
        by rewrite (leq_antisym lleq0 _ : l = 0).
    - destruct IHn as [s|n0].
      + left; by apply smaller_S.
      + destruct (dec (P n.+1)) as [h|nP].
        * left.
          refine (n.+1; (h, _, _)).
          intros m pm.
          apply leq_iff_not_gt.
          unfold gt, lt; intro leq_Sm_Sn.
          apply leq_pred' in leq_Sm_Sn.
          destruct (n0 m leq_Sm_Sn pm).
        * right.
          by apply leq_ind_l.
  Defined.

  Local Definition n_to_min_n (n : nat) (Pn : P n) : min_n_Type.
  Proof.
    destruct (bounded_search n) as [[l [[Pl ml] _]] | none].
    - exact (l; (tr Pl, tr ml)).
    - destruct (none n (leq_refl n) Pn).
  Defined.

  Local Definition prop_n_to_min_n (P_inhab : hexists P) : min_n_Type.
  Proof.
    strip_truncations.
    exact (n_to_min_n (P_inhab.1) (P_inhab.2)).
  Defined.

  Definition minimal_n (P_inhab : hexists P) : { n : nat & P n }.
  Proof.
    destruct (prop_n_to_min_n P_inhab) as [n [p _]].
    exact (n; fst merely_inhabited_iff_inhabited_stable p).
  Defined.

  (** As a consequence of [bounded_search] we deduce that bounded existence is decidable.  See also [decidable_exists_bounded_nat] in Spaces/Lists/Theory.v for a similar result with different dependencies. *)
  Definition decidable_search (n : nat) : Decidable { l : nat & (l <= n) * P l }.
  Proof.
    destruct (bounded_search n) as [s | no_l].
    - destruct s as [l [[Pl min] l_leq_n]].
      exact (inl (l; (l_leq_n, Pl))).
    - right.
      intros [l [l_leq_n Pl]].
      exact (no_l l l_leq_n Pl).
  Defined.

End bounded_search.

Section bounded_search_alt_type.

  Context (X : Type)
          (e : nat -> X) {e_surj : IsSurjection e}
          (P : X -> Type)
          (P_dec : forall x, Decidable (P x))
          (P_inhab : hexists P).

  (** Bounded search works for every type with a surjection from the naturals, for instance a type equivalent to them: we search for an index whose image satisfies [P]. *)
  Definition minimal_n_alt_type : {x : X & P x}.
  Proof.
    assert (P'_inhab : hexists (P o e)).
    { strip_truncations; destruct P_inhab as [x p].
      refine (Trunc_functor (-1) _ (@center _ (e_surj x))).
      intros [n q]; exact (n; transport P q^ p). }
    destruct (minimal_n (P o e) (fun n => P_dec (e n)) P'_inhab) as [n p].
    exact (e n; p).
  Defined.

End bounded_search_alt_type.

(** ** Walks along the natural numbers in a reflective subuniverse *)

Section walk.
  Context (O : ReflectiveSubuniverse).

  Local Open Scope nat_scope.
  Local Open Scope type_scope.

  (** If at each step [k < n] we can, in [O], go from [L k] either on to [L (S k)] or stop with [U k], then a walk of [n] steps from [L 0] reaches, in [O], either a stop [L k * U k] at some [k < n], or [L n]. For the identity modality this is a search, and for the propositional truncation an induction proving a property step by step, without choosing at each step. *)
  Definition O_walk (L U : nat -> Type) (n : nat)
    (step : forall k, k < n -> L k -> O (L k.+1 + U k)) (L0 : L 0)
    : O ({k : nat & (k < n) * (L k * U k)} + L n).
  Proof.
    induction n as [|n IH]; [exact (to O _ (inr L0))|].
    refine (O_rec _ (IH (fun k lt => step k (leq_succ_r lt)))).
    intros [[k [lt LU]]|Ln].
    - exact (to O _ (inl (k; (leq_succ_r lt, LU)))).
    - refine (O_functor O _ (step n (leq_refl _) Ln)).
      intros [Ln'|Un]; [exact (inr Ln')|exact (inl (n; (leq_refl _, (Ln, Un))))].
  Defined.

  (** If moreover [L n] implies [U n], then the walk stops, in [O], at some [k <= n]. *)
  Definition O_walk_stop (L U : nat -> Type) (n : nat)
    (step : forall k, k < n -> L k -> O (L k.+1 + U k)) (L0 : L 0) (last : L n -> U n)
    : O {k : nat & (k <= n) * (L k * U k)}.
  Proof.
    refine (O_functor O _ (O_walk L U n step L0)).
    intros [[k [lt LU]]|Ln].
    - exact (k; (leq_lt lt, LU)).
    - exact (n; (leq_refl n, (Ln, last Ln))).
  Defined.
End walk.
