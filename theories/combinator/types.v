Require Import PeanoNat.

Inductive s_ty : Type :=
  | s_Reals : nat -> s_ty
  | s_Real : s_ty
  | s_Unit : s_ty
  | s_Arrow : s_ty -> s_ty -> s_ty
  | s_Prod  : s_ty -> s_ty -> s_ty
  | s_LFunc  : s_ty -> s_ty -> s_ty
  | s_Map  : s_ty -> s_ty -> s_ty
.
Scheme Equality for s_ty.

Inductive ty : Type :=
  | Reals : nat -> ty
  | Real : ty
  | Unit : ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
.
Scheme Equality for ty.

Notation "'ℝ^' n" := (Reals n)  (left associativity, at level 24).
Notation "'ℝ'" := (Real).
Notation "A × B" := (Prod A B) (left associativity, at level 89).
Notation "A → B" := (Arrow A B) (right associativity, at level 90).

Notation "'sℝ^' n" := (s_Reals n)  (left associativity, at level 24).
Notation "'sℝ'" := (s_Real).
Notation "A s× B" := (s_Prod A B) (left associativity, at level 89).
Notation "A s→ B" := (s_Arrow A B) (right associativity, at level 90).
Notation "A s⊸ B" := (s_LFunc A B) (left associativity, at level 88).
Notation "A s⊗ B" := (s_Map A B) (left associativity, at level 88).
