Require Import FunctionalExtensionality.
Require Import Lists.List.
Import ListNotations.
Require Import Reals.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Program.
From Equations Require Import Equations.
Require Import Equations.Prop.Tactics.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import Coquelicot.Coquelicot.
Require Import Coq.Sets.Multiset.

Require Import AD.tactics.
Require Import AD.types.
Require Import AD.maps.
Require Import AD.stlc.
Require Import AD.combinator.
Require Import AD.denotation.
Require Import AD.translation.

Local Open Scope program_scope.

Definition linear {A}
  : (⟦ snd (Dt A) ⟧ₛₜ -> ⟦ snd (Dt A) ⟧ₛₜ) -> Prop :=
  fun f =>
  (f (⟦target.t_O (snd (Dt A))⟧ₜₒ tt)
    = ⟦target.t_O (snd (Dt A))⟧ₜₒ tt) /\
  (forall a b, f (⟦target.t_plus (snd (Dt A))⟧ₜₒ (a, b))
    = ⟦target.t_plus (snd (Dt A))⟧ₜₒ (f a, f b)).

Definition second_linear {A}
  : (R * ⟦ snd (Dt A) ⟧ₛₜ -> R) -> Prop :=
  fun h =>
    (forall r, h (r, ⟦target.t_O (snd (Dt A))⟧ₜₒ tt) = 0) /\
    (forall r a b, h (r, ⟦target.t_plus (snd (Dt A))⟧ₜₒ (a, b))
      = h (r, a) + h (r, b))
.

Lemma seclin_lin : forall A (h : R * ⟦ snd (Dt A) ⟧ₛₜ -> R),
  second_linear h ->
    forall x f r,
    (exists y, h (x, f r) = y) /\ linear f.
Proof with (simpl in *; eauto).
  intros. split.
  { exists (h (x, f r))... }
  admit.
Admitted.

Lemma denote_plus_O_l : forall τ x,
  denote_plus τ (denote_O τ) x = x.
Proof with (simpl in *; eauto).
  intros.
  induction τ...
  { unfold vector_plus. induction n...
    { dependent destruction x... }
    { specialize IHn with (Vtail x).
      rewrite Vbuild_tail; rewrite Vbuild_head.
      rewrite Rplus_0_l. rewrite IHn.
      dependent destruction x... } }
  { rewrite Rplus_0_l... }
  { destruct x... }
  { fold denote_st.
    extensionality r.
    specialize IHτ2 with (x r)... }
  { rewrite IHτ1. rewrite IHτ2. destruct x... }
  { fold denote_st.
    destruct x...
    apply f_equal. extensionality x... }
Qed.

Lemma denote_plus_O_r : forall τ x,
  denote_plus τ x (denote_O τ) = x.
Proof with (simpl in *; eauto).
  intros.
  induction τ...
  { unfold vector_plus. induction n...
    { dependent destruction x... }
    { specialize IHn with (Vtail x).
      rewrite Vbuild_tail; rewrite Vbuild_head.
      rewrite Rplus_0_r. rewrite IHn.
      dependent destruction x... } }
  { rewrite Rplus_0_r... }
  { destruct x... }
  { fold denote_st.
    extensionality r.
    specialize IHτ2 with (x r)... }
  { rewrite IHτ1. rewrite IHτ2. destruct x... }
  { fold denote_st.
    destruct x...
    apply f_equal. extensionality x... }
  { rewrite app_nil_r... }
Qed.

Lemma denote_O_eq : forall A,
  denote_O A = ⟦ target.t_O A ⟧ₜₒ ().
Proof with (simpl in *; eauto).
  intros.
  induction A...
  { fold denote_st. extensionality x... }
  { rewrites. }
  { fold denote_st. apply f_equal... extensionality x... }
Qed.

Lemma denote_plus_eq : forall A a b,
  denote_plus A a b = ⟦ target.t_plus A ⟧ₜₒ (a, b).
Proof with (simpl in *; eauto).
  intros.
  induction A...
  { fold denote_st. extensionality x... }
  { rewrites. }
  { fold denote_st. apply f_equal... extensionality x... }
Qed.

Definition linear_f {τ σ} (f : ⟦ τ ⟧ₛₜ -> ⟦ σ ⟧ₛₜ) : Prop
  := f (denote_O _) = denote_O _ /\
    forall a b, f (denote_plus _ a b) = denote_plus _ (f a) (f b).

Lemma snd_Dcomb_linear :
  forall τ σ (c : comb τ σ),
    linear_f ⟦fst (Dcomb c)⟧ₜₒ /\
    linear_f ⟦snd (Dcomb c)⟧ₜₒ.
Proof with (simpl in *; eauto).
  induction c.
  { split; unfold linear_f... }
  { destruct IHc1 as [[eq11 eq12] [eq11' eq12']];
      destruct IHc2 as [[eq21 eq22] [eq21' eq22']].
    split.
    { split; rewrites. }
    { split...
      { rewrite eq11.
        rewrite <- eq11'.
        rewrite <- eq21'... }
      { intros.
        rewrite <- eq12'...
        rewrite <- eq22'...
        rewrite <- eq12... } } }
  { destruct IHc1 as [[eq11 eq12] [eq11' eq12']];
      destruct IHc2 as [[eq21 eq22] [eq21' eq22']].
    split.
    { split; rewrites. }
    { split...
      { rewrite <- eq21'. rewrite <- eq11'...  }
      { intros.
        rewrite <- eq12'...
        rewrite <- eq22'... } } }
  { split; unfold linear_f...
    { split...
      { rewrite <- denote_O_eq... }
      { intros. destruct a; destruct b...
        destruct u; destruct u0...
        repeat rewrite <- denote_O_eq.
        rewrite denote_plus_O_r... } } }
  { split; unfold linear_f...
    { split; intros; simpl; repeat rewrite <- denote_O_eq...
      { rewrite denote_plus_O_r... } } }
  { split; unfold linear_f...
    { split; intros; simpl; repeat rewrite <- denote_O_eq...
      { rewrite denote_plus_O_r... } } }
  { split; unfold linear_f...
    { split; intros; simpl; repeat rewrite <- denote_O_eq;
        repeat rewrite <- denote_plus_eq.
      { rewrite denote_plus_O_r... }
      { destruct a; destruct b...
        clear d d0.
        destruct p; destruct p0...
        repeat rewrite <- denote_plus_eq...
        induction A...
        (* True by associativity of plus
            (but not true for lists)
            TODO:
              possible solution: use multisets
                instead of lists as denotations of ⊗ *)
      all: admit. } } }
  { split; simpl; fold Dt.
    { split... intros.
    (* Note ev denotates to
        fun x => (fst x) (snd x)
      This goal is true if (fst x) can be proven to be linear.
      TODO:
        find some way to work out how to prove this *)
      admit. }
    { split...
      { apply injective_projections...
      (* This one is slightly weird in that the denotation of ⊗
          cannot contain values of ⟦O⟧.
          As will be apparent in the next section, the denotation
          chosen for ⊗ should be principled with respect to both
          O and plus.
          TODO:
            possible solution: Exclude O when defining equality on
              the denotations of ⊗ *)
        admit. }
      { intros.  apply injective_projections...
      (* Two weird goals:
        For the first:

          [(plus (snd (fst a)) (snd (fst b)), plus (snd a) (snd b))]
            = [(snd (fst a), snd a) ; (snd (fst b), snd b)]

        Using shorter variables, the behaviour expected of the denotations
          of ⊗ requires equality between:
        (plus a b, plus a' b') = (a, a') `union` (b, b')
          TODO: who knows, it seems like the `union` operation should
            itself be built such that this is true.
            This seems kind of weird as it would require
            a datastructure with a monoidal operation that is defined
            with the same semantics as plus, (so, union === ⟦plus⟧).
            Note: Might not be doable generically, because of this
              tight-coupling, so the ds would be specialized to
              functions/sums/products/reals.
              Due to the inclusion of functions, this might also not be do-able
              in Coq (no decidable equality).

        For the second:
          Something similar happens as when showing that the first projection
            of the macro applied to ev is linear.
          Namely that the function argument needs to be proven linear
          TODO: same as for the first projection *)
      all: admit. } } }
  { split; unfold linear_f; simpl; fold denote_st; fold Dt...
    { split.
      { extensionality x.
        apply injective_projections...
        { destruct IHc as [[eq11 eq12] _]...
        (* This seems a little weird.
            In trying to prove that (D c)_1 is linear, I get the goal
            that if c : comb (A × B) C then
              ⟦(D c)_1⟧ (⟦O⟧, x) = ⟦O⟧
            instead of the expected:
              ⟦(D c)_1⟧ (⟦O⟧, x) = x
            or something akin to that.
            Might be caused by trying to prove the wrong thing. *)
          admit. }
        { apply f_equal.
          extensionality y.
          destruct IHc as [_ [eq21 eq22]]...
        (* Approximately the same issue as above, but now with 2 additional
            variables instead of one.
            Goal: snd (⟦(D c)_2⟧ (⟦O⟧, x, y)) = ⟦O⟧ *)
          admit. } }
      { intros.
        extensionality x. apply injective_projections...
        (* Might be the same issue as above where we discussed the
            requirements of `union`, but now without the tupling
            So:
              ⟦(D c)_1⟧ (plus a b, x)
                = plus (⟦(D c)_1⟧ (a, x)) (⟦(D c)_1⟧ (b, x)) *)
      all: admit. } }
    { admit. } }
  { split; unfold linear_f...
    split...
    { rewrite Rplus_0_r... }
    { intros.
      rewrite 2 Rplus_assoc;
        rewrite (Rplus_comm (fst b)).
      rewrite Rplus_assoc;
        rewrite (Rplus_comm (snd b))... } }
  { split; unfold linear_f...
  (* Not true
      TODO: fix definition of linearity or wrong lemma *)
    admit. }
  { split; unfold linear_f...
  (* Should be true by associativity/commutativity of
      elementwise addition *)
    admit. }
  { split; unfold linear_f...
  (* Not true
      TODO: fix definition of linearity or wrong lemma *)
    admit. }
Admitted.