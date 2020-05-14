(* Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Relations.
Require Import Logic.JMeq.
(* Require Import Reals. *)
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Coquelicot.Derive.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Equations.Equations.
Import EqNotations.

Require Import Definitions.
Require Import Macro.
Require Import Tactics.
Require Import Denotation.
Require Import Normalization.
(* Require Import Tangent. *)

Local Open Scope program_scope.
Local Open Scope R_scope.

(*
  Using a syntactic open logical relation adapted from
    On the Versatility of Open Logical Relations by Barthe, et al.
*)
Equations Rfixed τ {n} :
  tm (repeat Real n) τ -> tm (map Dt (repeat Real n)) (Dt τ) -> Prop :=
Rfixed Real t s :=
  ⟦ first _ s ⟧ₜₘ = ⟦ t ⟧ₜₘ /\
  (forall r, ⟦ second _ s ⟧ₜₘ = fun c => Derive (fun _ => ⟦ t ⟧ₜₘ c) r);
Rfixed (τ → σ) t s :=
  forall p q, Rfixed τ p q -> Rfixed σ (app _ _ _ t p) (app _ _ _ s q);
Rfixed (τ × σ) t s := True;
Rfixed (τ <+> σ) t s := True.

Equations Rsub Γ {n} :
  sub Γ (repeat Real n) -> sub (Dctx Γ) (repeat Real n) -> Prop :=
Rsub Γ γ δ := forall τ (x : τ ∈ Γ), Rfixed τ (γ τ x) (δ (Dt τ) (Dv x)).

Equations Rel Γ τ (n : nat) : tm Γ τ -> tm (Dctx Γ) (Dt τ) -> Prop :=
Rel Γ τ n t s := forall γ δ, @Rsub Γ n γ δ -> Rfixed τ (substitute γ t) (substitute δ s).

Inductive instantiation : forall {Γ Γ'} (n : nat), sub Γ Γ' -> Prop :=
  | inst_empty : forall n,
      @instantiation [] [] n id_sub
  | inst_const : forall Γ Γ' τ (t : tm Γ' τ) (s : sub Γ Γ') (n : nat),
      instantiation n s ->
      Rel Γ' τ n t (Dtm t) ->
      instantiation n (cons_sub t s).

Lemma step_preserves_Rfixed : forall {Γ τ n} (t t' : tm (repeat Real n) τ),
  Rfixed τ t (Dtm t) -> (t --> t') -> Rfixed τ t' (Dtm t').

Lemma step_preserves_Rel : forall {Γ τ n} (t t' : tm Γ τ),
  Rel Γ τ n t (Dtm t) -> (t --> t') -> Rel Γ τ n t' (Dtm t').
Proof with quick.
  intros Γ τ.
  generalize dependent Γ.
  dependent induction τ; quick; simp Rel in *...
  { apply (step_preserves_halting t t' H0)... }
  { split; destruct H...
    { eapply (step_preserves_halting t t')... }
    { pose proof (H1 s H2).
      eapply IHτ2...
      constructor... } }
  { destruct H. split.
    eapply (step_preserves_halting t t')...
    destruct H1 as [r [s H1]].
    destruct H1 as [Hst [Hvr [Hvs [Hr Hs]]]].
    exists r. exists s. splits...
    dependent destruction Hst.
    assert (value (tuple Γ r s))...
    apply value__normal in H1. contradiction H1...
    erewrite step_deterministic... }
  { destruct H as [Hh H].
    split... eapply (step_preserves_halting t t')...
    destruct H; destruct H as [x [Ht [Hv Hr]]].
    { left. exists x.
      splits...
      assert (value (@inl Γ τ1 τ2 x))...
      dependent destruction Ht.
      apply value__normal in H. contradiction H...
      erewrite step_deterministic... }
    { right. exists x.
      splits...
      assert (value (@inr Γ τ1 τ2 x))...
      dependent destruction Ht.
      apply value__normal in H. contradiction H...
      erewrite step_deterministic... } }
Qed.

Lemma fundamental :
  forall n Γ τ (t : tm Γ τ) (sb : sub Γ (repeat Real n)),
    instantiation n sb ->
    Rel (repeat Real n) τ n (substitute sb t) (Dtm (substitute sb t)).
Proof with quick.
  induction t...
  { (* Var *)
    induction v; dependent induction H...
    simp cons_sub. }
  { (* App *)
    specialize IHt1 with sb.
    specialize IHt2 with sb.
    simp Dtm Rel in *... fold Dt.
    specialize IHt1 with γ δ.
    simp Rfixed in IHt1. }
  { (* Abs *)
    simp Rel Rfixed...
    simp Rfixed... fold Dt.
    specialize IHt with (cons_sub p sb).
    simp Rel Rfixed in IHt...
    admit. }
  { (* Const *)
    admit. }
  { (* Add *)
    admit. }
  { (* Tuples *)
    admit. }
  { (* Projection 1 *)
    admit. }
  { (* Projection 2 *)
    admit. }
  { (* Case *)
    admit. }
  { (* Inl *)
    admit. }
  { (* Inl *)
    admit. }
Admitted.

Theorem semantic_correct_R :
  forall n,
  (* forall (f1 : R -> ⟦ repeat Real n ⟧ₜₓ),
  forall (f2 : R -> ⟦ Dctx (repeat Real n) ⟧ₜₓ), *)
  forall (t : tm (repeat Real n) Real),
  (* forall (f2 : R -> ⟦ Dctx (repeat Real n) ⟧ₜₓ), *)
    forall r, Derive ⟦ t ⟧ₜₘ r =
      ⟦ second (Dtm t) ⟧ₜₘ. *)