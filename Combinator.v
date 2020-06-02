Require Import Lists.List.
Import ListNotations.
Require Import Reals.
Require Import Coq.Program.Basics.
Require Import Equations.Equations.

Local Open Scope program_scope.

Inductive ty : Type :=
  | Real : ty
  | Unit : ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
.
Notation "'ℝ'" := (Real).
Notation "A × B" := (Prod A B) (left associativity, at level 89).
Notation "A → B" := (Arrow A B) (right associativity, at level 90).

Definition Ctx := list ty.

Inductive Var {T : Type} : list T -> T -> Type :=
  | Top : forall Γ τ, Var (τ::Γ) τ
  | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ
.
Derive Signature for Var.
Notation "x ∈ Γ" := (Var Γ x) (at level 75).

Inductive comb {Γ : Ctx} : ty -> Type :=
(* Category laws *)
  | id : forall {A}, comb (A → A)
  | seq : forall {A B C},
    comb (A → B) -> comb (B → C) -> comb (A → C)

  (* Monoidal *)
  | cross : forall {A B C D},
    comb (A → B) -> comb (C → D) -> comb ((A × C) → (B × D))

  (* Terminal *)
  | neg : forall {A},
    comb (A → Unit)

  (* Cartesian *)
  | exl : forall {A B},
    comb ((A × B) → A)
  | exr : forall {A B},
    comb ((A × B) → B)
  | dupl : forall {A},
    comb (A → (A × A))

  (* Closed *)
  | ev : forall {A B},
    comb (((A → B) × A) → B)
  | curry : forall {A B C},
    comb ((A × B) → C) -> comb (A → (B → C))
  | uncurry : forall {A B C},
    comb (A → (B → C)) -> comb ((A × B) → C)

  (* Const *)
  | cnst : forall {A},
    comb A -> comb (Unit → A)

  (* Numeric *)
  | cplus :
    comb ((ℝ × ℝ) → ℝ)
  | crval : forall (r : R), comb ℝ.

Notation "A ;; B" := (seq A B) (at level 40, left associativity).
Notation "<| A , B |>" := (dupl ;; cross A B) (at level 30).

Equations Ot {Γ : Ctx} (τ : ty): @comb Γ (Unit → τ) :=
  | ℝ => cnst (crval 0);
  | Unit => neg;
  | σ × ρ => <| (Ot σ), (Ot ρ) |>;
  | σ → ρ => curry (exl ;; (Ot ρ)).

Equations plust {Γ : Ctx} (τ : ty): @comb Γ (τ × τ → τ) :=
  | ℝ => cplus;
  | Unit => neg;
  | σ × ρ =>
    <|
      <|exl;;exl, exr;;exl|>;;plust σ,
      <|exl;;exr, exr;;exr|>;; plust ρ
    |>;
  | σ → ρ => curry (
    <|
      <|exl ;; exl, exr|> ;; ev,
      <|exl ;; exr, exr|> ;; ev
    |> ;; plust ρ).

Fixpoint Dt (τ : ty) : ty * ty :=
  match τ with
  | ℝ => (ℝ, ℝ)
  | Unit => (Unit, Unit)
  | σ × ρ =>
      ((fst (Dt σ)) × (fst (Dt ρ)), (snd (Dt σ)) × (snd (Dt ρ)))
  | σ → ρ =>
      (fst (Dt σ) → (fst (Dt ρ) × (snd (Dt ρ) → snd (Dt σ)))
        , fst (Dt σ) × snd (Dt ρ))
  end.

Equations? Dtm Γ τ (t : @comb Γ τ)
  : @comb Γ (fst (Dt τ)) :=
Dtm Γ τ t with t => {
  | @id Γ τ := _;
  | @seq Γ τ σ ρ t1 t2 := _;

  (* Monoidal *)
  | cross t1 t2 := _;

  (* Terminal *)
  | neg := _;

  (* Cartesian *)
  | exl := _;
  | exr := _;
  | dupl := _;

  (* Closed *)
  | ev := _;
  | curry t := _;
  | uncurry t := _;

  (* Const *)
  | cnst t := _;

  (* Numeric *)
  | cplus := _;
  | crval r := _
}.
