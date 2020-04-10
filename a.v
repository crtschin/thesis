Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Equations.Equations.

Definition Ctx x : Type := list x.
Definition KCtx := @Ctx unit.
Inductive Var {T : Type} : list T -> T -> Type :=
  | Top : forall Γ τ, Var (τ::Γ) τ
  | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ
.
Notation "x ∈ Γ" := (Var Γ x) (at level 75).

Inductive ty {Δ : KCtx}: Type :=
  | Real : ty
  | Prod : ty -> ty -> ty.
Fixpoint Dt {Δ : KCtx} (τ : @ty Δ) : @ty Δ :=
  match τ with
  | Real => Prod Real Real
  | Prod σ ρ => Prod (Dt σ) (Dt ρ)
  end.
Fixpoint denote_t (τ : @ty nil) : Set :=
  match τ with
  | Real => R
  | Prod τ1 τ2 => (denote_t τ1) * (denote_t τ2)
  end.
Equations S τ :
  (R -> denote_t τ) -> (R -> denote_t (Dt τ)) -> Prop :=
S Real f g :=
  (forall (x : R), ex_derive f x) /\
  (fun r => g r) =
    (fun r => (f r, Derive f r));
S (Prod σ ρ) f g :=
  exists f1 f2 g1 g2,
  exists (s1 : S σ f1 f2) (s2 : S ρ g1 g2),
    (f = fun r => (f1 r, g1 r)) /\
    (g = fun r => (f2 r, g2 r)).
