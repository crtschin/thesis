Set Warnings "-notation-overridden,-parsing".

Require Import Lists.List.
Import ListNotations.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.
Require Import Reals.
Require Import Logic.JMeq.
Require Import Arith.PeanoNat.
Require Import Program.Equality.

From Equations Require Import Equations.
From AD Require Import Definitions.
From AD Require Import Tactics.

Open Scope R_scope.

(* Functorial macro *)

Fixpoint Dt τ : ty :=
  match τ with
  | Real => Real × Real
  | t1 × t2 => Dt t1 × Dt t2
  | t1 → t2 => Dt t1 → Dt t2
  | t1 <+> t2 => Dt t1 <+> Dt t2
  end.

Definition Dctx Γ : Ctx := map Dt Γ.

Fixpoint Dv {Γ τ} (v: τ ∈ Γ) : (Dt τ) ∈ (map Dt Γ) :=
  match v with
  | Top Γ τ => Top (map Dt Γ) (Dt τ)
  | Pop Γ τ σ t => Pop (map Dt Γ) (Dt τ) (Dt σ) (Dv t)
  end.

Equations Dtm {Γ τ} (t : tm Γ τ) : tm (map Dt Γ) (Dt τ) :=
Dtm (Γ:=Γ) (τ:=τ) (var Γ τ v) := var _ _ (Dv v);
Dtm (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) := app _ _ _ (Dtm t1) (Dtm t2);
Dtm (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) := abs _ _ _ (Dtm f);
Dtm (Γ:=Γ) (τ:=τ) (const Γ r) := tuple _ (const _ r) (const _ 0);
Dtm (Γ:=Γ) (τ:=τ) (add Γ t1 t2) with Dtm t1 := {
  Dtm (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 with Dtm t2 := {
    Dtm (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 d2 :=
      tuple _
        (add _ (first _ d1) (first _ d2))
        (add _ (second _ d1) (second _ d2))
  }
};
Dtm (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) := tuple _ (Dtm t1) (Dtm t2);
Dtm (Γ:=Γ) (τ:=τ) (first Γ p) := first _ (Dtm p);
Dtm (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm p);
Dtm (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) := case _ (Dtm e) (Dtm c1) (Dtm c2);
Dtm (Γ:=Γ) (τ:=τ) (inl Γ e) := inl _ (Dtm e);
Dtm (Γ:=Γ) (τ:=τ) (inr Γ e) := inr _ (Dtm e).

Fixpoint Denv {Γ} (G : Env Γ) : Env (Dctx Γ) :=
  match G with
  | env_nil => env_nil
  | env_cons c G => env_cons (Dtm c) (Denv G)
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

Lemma D_sub : forall Γ τ σ
  (t : tm (σ::Γ) τ)
  (s : tm Γ σ),
  Dtm (substitute (| s |) t) =
    substitute (| Dtm s |) (Dtm t).
Proof with quick.
  dependent induction t...
  - dependent induction v...
  - assert (H: σ :: Γ ~= σ :: Γ). { reflexivity. }
    assert (H': t1 ~= t1). { reflexivity. }
    assert (H'': t2 ~= t2). { reflexivity. }
    pose proof (IHt1 Γ σ t1 H H') as H1.
    pose proof (IHt2 Γ σ t2 H H'') as H2.
    clear H H' H''.
    simp Dtm. rewrite H1. rewrite H2...
  - assert (H: σ0 :: σ :: Γ ~= σ0 :: σ :: Γ). { reflexivity. }
    assert (H': t ~= t). { reflexivity. }
    pose proof (IHt (σ::Γ) σ0 t H H') as Ht.
    clear H H' IHt.
    simp Dtm... fold (map Dt Γ).
    assert (Hr :
      Dtm (substitute (substitute_lifted (| s |)) t) =
      substitute (substitute_lifted (| Dtm s |)) (Dtm t)).
    { admit. }
    rewrite Hr...
  - intros. simpl.
    assert (H: σ :: Γ ~= σ :: Γ). reflexivity.
    assert (H1: t1 ~= t1). reflexivity.
    assert (H2: t2 ~= t2). reflexivity.
    simp Dtm.
    pose proof (IHt1 Γ σ t1 H H1) as Ht1. rewrite -> Ht1.
    pose proof (IHt2 Γ σ t2 H H2) as Ht2. rewrite -> Ht2...
  - intros. simpl.
    assert (H: σ :: Γ ~= σ :: Γ). reflexivity.
    assert (H1: t1 ~= t1). reflexivity.
    assert (H2: t2 ~= t2). reflexivity.
    simp Dtm.
    pose proof (IHt1 Γ σ t1 H H1) as Ht1. rewrite -> Ht1.
    pose proof (IHt2 Γ σ t2 H H2) as Ht2. rewrite -> Ht2...
  - intros.
    assert (H: σ :: Γ ~= σ :: Γ). reflexivity.
    assert (H': t ~= t). reflexivity.
    pose proof (IHt Γ σ t H H') as Hr.
    simpl. simp Dtm. rewrite Hr...
  - intros.
    assert (H: σ :: Γ ~= σ :: Γ). reflexivity.
    assert (H': t ~= t). reflexivity.
    pose proof (IHt Γ σ t H H') as Hr.
    simpl. simp Dtm. rewrite Hr...
  - intros. simpl.
    assert (H: σ :: Γ ~= σ :: Γ). { reflexivity. }
    assert (H': t1 ~= t1). { reflexivity. }
    assert (H'': t2 ~= t2). { reflexivity. }
    assert (H''': t3 ~= t3). { reflexivity. }
    pose proof (IHt1 Γ σ t1 H H').
    pose proof (IHt2 Γ σ t2 H H'').
    pose proof (IHt3 Γ σ t3 H H''').
    simp Dtm. rewrite H0; rewrite H1; rewrite H2...
  - intros. simpl.
    assert (H: σ :: Γ ~= σ :: Γ). reflexivity.
    assert (H': t ~= t). reflexivity.
    pose proof (IHt Γ σ t H H') as Hr.
    simp Dtm. rewrite Hr...
  - intros. simpl.
    assert (H: σ :: Γ ~= σ :: Γ). reflexivity.
    assert (H': t ~= t). reflexivity.
    pose proof (IHt Γ σ t H H') as Hr.
    simp Dtm. rewrite Hr...
Admitted.