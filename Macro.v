Set Warnings "-notation-overridden,-parsing".

Require Import Lists.List.
Import ListNotations.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.
Require Import Reals.
Require Import Logic.JMeq.
Require Import Arith.PeanoNat.
Require Import Program.Equality.

Require Import Definitions.

Open Scope R_scope.

(* Functorial macro *)

Fixpoint Dt τ : ty :=
  match τ with
  | Real => Real × Real
  | t1 × t2 => Dt t1 × Dt t2
  | t1 → t2 => Dt t1 → Dt t2
  end.

Definition Dctx Γ : Ctx := map Dt Γ.

Fixpoint Dv {Γ τ} (v: τ ∈ Γ) : (Dt τ) ∈ (map Dt Γ) :=
  match v with
  | Top Γ τ => Top (map Dt Γ) (Dt τ)
  | Pop Γ τ σ t => Pop (map Dt Γ) (Dt τ) (Dt σ) (Dv t)
  end.

Program Fixpoint Dtm {Γ τ} (t : tm Γ τ) : tm (map Dt Γ) (Dt τ) :=
  match t with
  | var _ _ v => var (map Dt Γ) (Dt τ) (Dv v)
  | app _ _ _ t1 t2 => app _ _ _ (Dtm t1) (Dtm t2)
  | abs _ _ _ f => abs _ _ _ (Dtm f)

  | const _ r => tuple _ _ _ (const _ r) (const _ 0)
  | add _ t1 t2 =>
    let d1 := (Dtm t1) in
    let d2 := (Dtm t2) in
    tuple _ _ _
      (add _ (first _ _ _ d1) (first _ _ _ d2))
      (add _ (second _ _ _ d1) (second _ _ _ d2))

  | tuple _ _ _ t1 t2 => tuple _ _ _ (Dtm t1) (Dtm t2)
  | first _ _ _ p => first _ _ _ (Dtm p)
  | second _ _ _ p => second _ _ _ (Dtm p)
  end.

Lemma Dt_lift_var : forall Γ τ, τ ∈ Γ -> (Dt τ) ∈ (map Dt Γ).
Proof with eauto.
  intros Γ τ H. induction H; constructor. assumption.
Qed.

(* The D macro preserves types *)
Lemma D_type : forall Γ τ
  (t : tm Γ τ),
  has_type (Dtm t) = Dt τ.
Proof. trivial. Qed.

Lemma D_type_sub : forall Γ τ σ
  (t : tm (σ::Γ) τ)
  (s : tm Γ σ),
  has_type (Dtm (substitute (| s |) t)) =
    has_type (substitute (| Dtm s |) (Dtm t)).
Proof. trivial. Qed.

Lemma D_sub_lifted : forall Γ τ σ ρ
  (t : tm (ρ::σ::Γ) τ)
  (s : tm Γ σ),
  (forall r : tm (σ :: Γ) ρ,
     Dtm (substitute (| r |) t) = substitute (| Dtm r |) (Dtm t)) ->
  Dtm (substitute (substitute_lifted (| s |)) t) =
    substitute (substitute_lifted (| Dtm s |)) (Dtm t).
Proof with eauto.
  intros.
Admitted.

Theorem D_sub : forall Γ τ σ
  (t : tm (σ::Γ) τ)
  (s : tm Γ σ),
  Dtm (substitute (| s |) t) =
    substitute (| Dtm s |) (Dtm t).
Proof with eauto.
  dependent induction t...
  - dependent induction v...
  - assert (H: σ :: Γ = σ :: Γ). { reflexivity. }
    assert (H': t1 ~= t1). { reflexivity. }
    assert (H'': t2 ~= t2). { reflexivity. }
    pose proof (IHt1 Γ σ t1 H H') as H1.
    pose proof (IHt2 Γ σ t2 H H'') as H2.
    clear H H' H''.
    intros s. simpl.
    rewrite H1. rewrite H2.
    reflexivity.
  - assert (H: σ0 :: σ :: Γ = σ0 :: σ :: Γ). { reflexivity. }
    assert (H': t ~= t). { reflexivity. }
    pose proof (IHt (σ::Γ) σ0 t H H') as Ht.
    clear H H'.
    intros s. simpl. simpl (Dtm (abs (σ :: Γ) τ σ0 t)).
    assert (Hr :
      Dtm (substitute (substitute_lifted (| s |)) t) =
      substitute (substitute_lifted (| Dtm s |)) (Dtm t)).
    { apply D_sub_lifted... }
    rewrite Hr...
  - intros. simpl.
    assert (H: σ :: Γ = σ :: Γ). reflexivity.
    assert (H1: t1 ~= t1). reflexivity.
    assert (H2: t2 ~= t2). reflexivity.
    pose proof (IHt1 Γ σ t1 H H1) as Ht1. rewrite -> Ht1.
    pose proof (IHt2 Γ σ t2 H H2) as Ht2. rewrite -> Ht2...
  - intros. simpl.
    assert (H: σ :: Γ = σ :: Γ). reflexivity.
    assert (H1: t1 ~= t1). reflexivity.
    assert (H2: t2 ~= t2). reflexivity.
    pose proof (IHt1 Γ σ t1 H H1) as Ht1. rewrite -> Ht1.
    pose proof (IHt2 Γ σ t2 H H2) as Ht2. rewrite -> Ht2...
  - intros.
    assert (H: σ :: Γ = σ :: Γ). reflexivity.
    assert (H': t ~= t). reflexivity.
    pose proof (IHt Γ σ t H H') as Hr.
    simpl. rewrite Hr...
  - intros.
    assert (H: σ :: Γ = σ :: Γ). reflexivity.
    assert (H': t ~= t). reflexivity.
    pose proof (IHt Γ σ t H H') as Hr.
    simpl. rewrite Hr...
Qed.
