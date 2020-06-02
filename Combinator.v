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
  | id : forall {A},
    comb (A → A)
  | neg : forall {A},
    comb (A → Unit)
  | unit : comb Unit
  | diag : forall {A},
    comb (A → A × A)
  | first : forall {A B},
    comb (A × B → A)
  | second : forall {A B},
    comb (A × B → B)
  | ev : forall {A B},
    comb ((A → B) × A → B)
  | lam : forall {A B},
    comb (B → A → B × A)

  | plus :
    comb (ℝ × ℝ → ℝ)
  | rval : R -> comb ℝ

  | cnst : forall {A B},
    comb A -> comb (B → A)
  | curry : forall {A B C},
    comb (A × B → C) -> comb (A → B → C)
  | uncurry : forall {A B C},
    comb (A → B → C) -> comb (A × B → C)
  | seq : forall {A B C},
    comb (A → B) -> comb (B → C) -> comb (A → C)
  | bimap : forall {A B C D},
    comb (A → B) -> comb (C → D) -> comb (A × C → B × D)
.

Notation "A ;; B" := (seq A B) (at level 40, left associativity).
Notation "<| A , B |>" := (diag ;; bimap A B) (at level 40).

Equations Ot {Γ : Ctx} (τ : ty): @comb Γ (Unit → τ) :=
  | ℝ => cnst (rval 0);
  | Unit => neg;
  | σ × ρ => <| (Ot σ), (Ot ρ) |>;
  | σ → ρ => curry (first ;; (Ot ρ)).

Equations plust {Γ : Ctx} (τ : ty): @comb Γ (τ × τ → τ) :=
  | ℝ => plus;
  | Unit => neg;
  | σ × ρ => abs (tuple
    (app (plust σ) (tuple
      (fst' (fst' (var (Top _ _))))
      (fst' (snd' (var (Top _ _))))))
    (app (plust ρ) (tuple
      (snd' (fst' (var (Top _ _))))
      (snd' (snd' (var (Top _ _)))))));
  | σ → ρ =>
    abs (abs (app (plust ρ)
      (tuple
        (app (fst' (var (Pop _ _ _ (Top _ _)))) (var (Top _ _)))
        (app (snd' (var (Pop _ _ _ (Top _ _)))) (var (Top _ _))))
    )).

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
  | (@id Γ τ) => _;
  (* | id => _; *)
  | neg => _;
  | unit => _;
  | diag => _;
  | first => _;
  | second => _;
  | ev => _;
  | lam => _;
  | plus => _;
  | rval r => _;

  | cnst t => _;
  | curry t => _;
  | uncurry t => _;
  | seq f1 f2 => _;
  | bimap f1 f2 => _;

  | tuple t1 t2 => _;
  | fst' t => _;
  | snd' t => _;
  | abs t => _;
  | var v => _;
  | app t1 t2 => _
}.
