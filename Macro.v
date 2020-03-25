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

Fixpoint Denv {Γ} (G : Env Γ): Env (Dctx Γ) :=
  match G with
  | env_nil => env_nil
  | env_cons t G => env_cons (Dtm t) (Denv G)
  end.

Lemma Dt_lift_var : forall Γ τ, τ ∈ Γ -> (Dt τ) ∈ (map Dt Γ).
Proof with eauto.
  intros Γ τ H. induction H; constructor. assumption.
Qed.

Lemma D_rename_lifted : forall Γ τ σ ρ (t : tm (ρ::Γ) τ),
  Dtm
  (rename (rename_lifted
    (fun (ρ : ty) (x : ρ ∈ Γ) => Pop Γ ρ σ x)) t) =
  rename (rename_lifted
    (fun (ρ : ty) (x : ρ ∈ map Dt Γ) => Pop (map Dt Γ) ρ (Dt σ) x)) (Dtm t).
Proof with quick.
Admitted.

Lemma D_rename Γ τ σ (t : tm Γ τ):
  Dtm (rename (fun (ρ : ty) (x : ρ ∈ Γ) => Pop Γ ρ σ x) t) =
  rename (fun (ρ : ty) (x : ρ ∈ map Dt Γ) => Pop (map Dt Γ) ρ (Dt σ) x) (Dtm t).
Proof with quick.
  induction t; simpl; simp Dtm; fold map Dt; rewrites.
  fold (map Dt).
  assert
    (Dtm (rename
      (rename_lifted (fun (ρ : ty) (x : ρ ∈ Γ) => Pop Γ ρ σ x)) t) =
    rename (rename_lifted
      (fun (ρ : ty) (x : ρ ∈ map Dt Γ) => Pop (map Dt Γ) ρ (Dt σ) x)) (Dtm t)).
  { admit. }
  rewrite H...
Admitted.

Lemma D_shift : forall Γ τ σ (t : tm Γ τ),
  Dtm (shift (σ:=σ) t) = shift (σ:=Dt σ) (Dtm t).
Proof with quick.
  intros. unfold shift...
  rewrite D_rename...
Admitted.

Lemma D_cons_sub: forall Γ τ σ (v: τ ∈ σ :: Γ) (s: tm Γ σ),
  Dtm ((| s |) τ v) = (| Dtm s |) (Dt τ) (Dv v).
Proof.
Admitted.

Lemma D_sub_lifted : forall Γ τ σ ρ (t : tm (ρ::σ::Γ) τ) (s: tm Γ σ),
Dtm (substitute (substitute_lifted (| s |)) t) =
  substitute (substitute_lifted (| Dtm s |)) (Dtm t).
Proof with quick.
  dependent induction t...
  - dependent induction v...
    simp Dtm.
    simp substitute_lifted.
    rewrite D_shift.
    simp substitute_lifted.
    unfold Dv.
    simp substitute_lifted.
Admitted.

Lemma D_sub : forall Γ τ σ
  (t : tm (σ::Γ) τ)
  (s : tm Γ σ),
  Dtm (substitute (| s |) t) =
    substitute (| Dtm s |) (Dtm t).
Proof with quick.
  dependent induction t...
  - dependent induction v...
  - simp Dtm. rewrites.
  - simp Dtm.
    rewrite D_sub_lifted...
  - simp Dtm.
    specialize IHt1 with Γ σ t1 s.
    specialize IHt2 with Γ σ t2 s. rewrites...
  - simp Dtm. rewrites...
  - simp Dtm. rewrites...
  - simp Dtm. rewrites...
  - simp Dtm. rewrites...
  - simp Dtm. rewrites...
  - simp Dtm. rewrites...
Admitted.