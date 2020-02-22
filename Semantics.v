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
  | Prod τ1 τ2 => product_diffeology (denote_t τ1) (denote_t τ2)
  | Arrow τ1 τ2 => functional_diffeology (denote_t τ1) (denote_t τ2)
  end.

Example denote_t_ex :
  carrier (denote_t ((Real × Real × Real × Real) → (Real × Real))) =
    ((R * R * R * R) -> (R * R)).
Proof. trivial. Qed.

Definition denote_ctx Γ : list DiffeoSp := map denote_t Γ.

Fixpoint denote_v {Γ τ} (v: τ ∈ Γ) : (denote_t τ) ∈ (denote_ctx Γ) :=
  match v with
  | Top Γ τ => Top (denote_ctx Γ) (denote_t τ)
  | Pop Γ τ σ t => Pop (denote_ctx Γ) (denote_t τ) (denote_t σ) (denote_v t)
  end.

Program Fixpoint denote_tm Γ τ (t : tm Γ τ) : carrier (denote_t τ) :=
  match t with
  | const r => (fun _ => r)
  | add t1 t2 => _

  | var σ v => _
  | app _ _ t1 t2 => _
  | abs _ _ f => _

  | tuple _ _ t1 t2 => _
  | fst _ _ p => _
  | snd _ _ p => _
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