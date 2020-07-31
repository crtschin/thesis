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
Require Import AD.target.
Require Import AD.combinator.
Require Import AD.denotation.
Require Import AD.translation.

Local Open Scope program_scope.

Definition linear_f {τ σ} (f : ⟦ τ ⟧ₛₜ -> ⟦ σ ⟧ₛₜ) : Prop
  := f (⟦t_O _⟧ₜₒ tt) = ⟦t_O _⟧ₜₒ tt /\
    forall a b, f (⟦t_plus _⟧ₜₒ (a, b)) = ⟦t_plus _⟧ₜₒ (f a, f b).

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