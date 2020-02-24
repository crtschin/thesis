Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Arith_base.
Import EqNotations.

Require Import Definitions.
Require Import Macro.
Require Import Diffeology.

Local Open Scope nat_scope.
Local Open Scope R_scope.

(*
  Maps types in 'ty' to an underlying Type
  given a proof that that type is a diffeological space
*)
Fixpoint denote_t τ : DiffeoSp :=
  match τ with
  | Real => R_diffeology
  | Prod τ1 τ2 => denote_t τ1 *d* denote_t τ2
  | Arrow τ1 τ2 => denote_t τ1 -D> denote_t τ2
  end.

(* Example denote_t_ex :
  denote_t ((Real × Real × Real × Real) → (Real × Real)) =
    diff_smooth (denote_t (Real × Real × Real × Real)) (denote_t (Real × Real)).
Proof. trivial. Qed. *)

Fixpoint denote_ctx Γ : DiffeoSp :=
  match Γ with
  | [] => unit_diffeology
  | τ :: Γ' => denote_t τ *d* denote_ctx Γ'
  end.

Program Fixpoint denote_v {Γ τ} (v: τ ∈ Γ) : denote_ctx Γ -d> denote_t τ :=
  match v with
  | Top Γ τ => product_snd (denote_ctx Γ) (denote_t τ)
  | Pop Γ τ σ t =>
    denote_v t
  end.

Fixpoint denote_tm Γ τ (t : tm Γ τ) : denote_ctx Γ -> carrier (denote_t τ) :=
  match t with
  | var _ v => denote_v v
  end.

Definition diff_func :=
  forall T1 T2, T1 -> T2.

Inductive denote_tm
  : forall {Γ τ} (T : denote_tm τ DT), tm Γ τ -> diff_func -> Type :=
  | d_const : forall Γ r,
    denote_tm (const Γ r) (fun _ _ _ => r)
.

Theorem one : forall Γ τ (t : Γ τ),
  true = true.
Proof.