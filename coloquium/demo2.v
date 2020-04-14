Require Import Equations.Equations.
Open Scope list_scope.

Inductive ty :=
  | bool : ty
  | arrow : ty -> ty -> ty.
Notation "A → B" := (arrow A B) (right associativity, at level 20).

Definition Ctx := list ty.

Section extrinsic.
  (* Extrinsic formulation *)
  Require Import PeanoNat.
  Inductive ext_tm : Type :=
    | ext_var : nat -> ext_tm
    | ext_app : ext_tm -> ext_tm -> ext_tm
    | ext_abs : ext_tm -> ext_tm.

  Definition lt_S_length : forall {A} {l : list A} {n a},
    S n < length (a::l) -> n < length l.
  Proof.
    intros. simpl in H.
    unfold lt in *.
    inversion H.
    - auto.
    - eapply Nat.le_trans.
      instantiate (1:=(S (S n))).
      all: auto.
  Defined.

  Equations elem {A} (n : nat) (l : list A) (pf : n < length l) : A :=
  elem O nil pf with pf := {};
  elem O (cons a l) _ := a;
  elem (S n) nil pf with pf := {};
  elem (S n) (cons a l) pf := elem n l (lt_S_length pf).

  Inductive has_type : ext_tm -> Ctx -> ty -> Prop :=
    | T_var : forall Γ n (pf : n < length Γ),
      has_type (ext_var n) Γ (elem n Γ pf)
    | T_app : forall Γ τ σ t1 t2,
      has_type t1 Γ (σ → τ) ->
      has_type t2 Γ σ ->
      has_type (ext_app t1 t2) Γ τ
    | T_abs : forall Γ τ σ t,
      has_type t (σ::Γ) τ ->
      has_type (ext_abs t) Γ (σ → τ).
End extrinsic.

Section intrinsic.
  (* Intrinsic strongly-typed formulation *)
  Inductive Var : Ctx -> ty -> Set :=
    | Top : forall Γ τ, Var (τ::Γ) τ
    | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ.
  Notation "x ∈ Γ" := (Var Γ x) (at level 75).

  Inductive tm : Ctx -> ty -> Set :=
    | var : forall Γ τ,
      τ ∈ Γ -> tm Γ τ
    | app : forall Γ τ σ,
      tm Γ (σ → τ) ->
      tm Γ σ ->
      tm Γ τ
    | abs : forall Γ τ σ,
      tm (σ::Γ) τ -> tm Γ (σ → τ).