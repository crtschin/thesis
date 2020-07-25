Require Import Lists.List.
Import ListNotations.
Require Import Reals.
Require Import Coq.Program.Basics.
Require Import Equations.Equations.
Require Import CoLoR.Util.Vector.VecUtil.

Require Import AD.types.
Local Open Scope program_scope.

(* Target Language definition *)
Inductive target : s_ty -> s_ty -> Type :=
  (* Category laws *)
  | t_id : forall {A}, target A A
  | t_seq : forall {A B C},
    target A B -> target B C -> target A C

  (* Monoidal *)
  | t_cross : forall {A B C D},
    target A B -> target C D -> target (A s× C) (B s× D)

  (* Terminal *)
  | t_neg : forall {A},
    target A s_Unit

  (* Cartesian *)
  | t_exl : forall {A B},
    target (A s× B) A
  | t_exr : forall {A B},
    target (A s× B) B
  | t_dupl : forall {A},
    target A (A s× A)

  (* Closed *)
  | t_ev : forall {A B},
    target ((A s→ B) s× A) B
  | t_curry : forall {A B C},
    target (A s× B) C -> target A (B s→ C)

  (* Numeric *)
  | t_cplus : target (s_Real s× s_Real) s_Real
  | t_crval : forall (a : R), target s_Unit s_Real

  | t_cmplus : forall {n}, target (s_Reals n s× s_Reals n) (s_Reals n)
  | t_cmrval : forall {n} (a : vector R n), target s_Unit (s_Reals n)

  (* Linear *)
  | t_ev_l : forall {A B}, target ((A s⊸ B) s× A) B
  | t_curry_l : forall {A B C},
    target (A s× B) C -> target A (B s⊸ C)

  (* Maps *)
  | t_mempty : forall {τ σ},
    target s_Unit (τ s⊗ σ)
  | t_msingleton : forall {τ σ},
    target (τ s× σ) (τ s⊗ σ)
  | t_mplus : forall {τ σ},
    target ((τ s⊗ σ) s× (τ s⊗ σ)) (τ s⊗ σ)
  | t_mfold : forall {τ σ ρ},
    target (τ s⊗ σ s× (τ s× σ s→ ρ)) ρ
.
Derive Signature for target.

Notation "A ;; B" := (t_seq A B) (at level 40, left associativity).
Notation "⟨ A , B ⟩" := (t_dupl ;; t_cross A B) (at level 30).

(* Helpfull extras *)
Definition uncurry {A B C} : target A (B s→ C) -> target (A s× B) C :=
  fun c => t_cross c t_id ;; t_ev.
Definition assoc1 {A B C} : target ((A s× B) s× C) (A s× (B s× C)) :=
  ⟨t_exl;;t_exl, ⟨t_exl;;t_exr, t_exr⟩⟩.
Definition assoc2 {A B C} : target (A s× (B s× C)) ((A s× B) s× C) :=
  ⟨⟨t_exl, t_exr;;t_exl⟩, t_exr;;t_exr⟩.
Definition sym {A B} : target (A s× B) (B s× A) :=
  ⟨t_exr, t_exl⟩.

(* Monoidal/Derivative operation *)
Fixpoint t_O (τ : s_ty): target s_Unit τ :=
  match τ with
  | sℝ => t_crval 0%R
  | sℝ^n => t_cmrval (@Vbuild _ n (fun _ _ => 0%R))
  | s_Unit => t_neg
  | σ s× ρ => ⟨ (t_O σ), (t_O ρ) ⟩
  | σ s→ ρ => t_curry (t_exl ;; t_O ρ)
  | σ s⊸ ρ => t_curry_l (t_exl ;; t_O ρ)
  | σ s⊗ ρ => t_mempty
  end.

Fixpoint t_plus (τ : s_ty): target (τ s× τ) τ :=
  match τ with
  | sℝ => t_cplus
  | sℝ^n => t_cmplus
  | s_Unit => t_neg
  | σ s× ρ =>
    ⟨
      ⟨t_exl;;t_exl, t_exr;;t_exl⟩;; t_plus σ,
      ⟨t_exl;;t_exr, t_exr;;t_exr⟩;; t_plus ρ
    ⟩
  | σ s→ ρ =>
    t_curry (
      ⟨
        ⟨t_exl ;; t_exl, t_exr⟩ ;; t_ev,
        ⟨t_exl ;; t_exr, t_exr⟩ ;; t_ev
      ⟩ ;; t_plus ρ)
  | σ s⊸ ρ =>
    t_curry_l (
      ⟨
        ⟨t_exl ;; t_exl, t_exr⟩ ;; t_ev_l,
        ⟨t_exl ;; t_exr, t_exr⟩ ;; t_ev_l
      ⟩ ;; t_plus ρ)
  | σ s⊗ ρ => t_mplus
  end.
