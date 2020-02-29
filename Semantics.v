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

From AD Require Import Definitions.
From AD Require Import Macro.
From AD Require Import Diffeology.

Local Open Scope nat_scope.
Local Open Scope R_scope.

(*
  Maps types in 'ty' to an underlying Type
  given a proof that that type is a diffeological space
*)
Fixpoint denote_t τ : DiffeoSp :=
  match τ with
  | Real => R_diffeology
  | Prod τ1 τ2 => denote_t τ1 *** denote_t τ2
  | Arrow τ1 τ2 => denote_t τ1 -D> denote_t τ2
  end.

(* Example denote_t_ex :
  denote_t ((Real × Real × Real × Real) → (Real × Real)) =
    diff_smooth (denote_t (Real × Real × Real × Real)) (denote_t (Real × Real)).
Proof. trivial. Qed. *)

Fixpoint denote_ctx Γ : DiffeoSp :=
  match Γ with
  | [] => unit_diffeology
  | τ :: Γ' => denote_t τ *** denote_ctx Γ'
  end.

Fixpoint denote_v {Γ τ} (v: τ ∈ Γ) : denote_ctx Γ -d> denote_t τ :=
  match v with
  | Top Γ' τ' => product_first
  | Pop Γ' τ' σ x => diffeological_smooth_comp (denote_v x) product_second
  end.

Fixpoint denote_tm {Γ τ} (t : tm Γ τ)
    : denote_ctx Γ -d> denote_t τ :=
  match t with
  | var σ v => denote_v v

  | const r => constant_smooth (r : carrier R_diffeology)
  | add t1 t2 => denote_tm t1 + denote_tm t2

  | app σ ρ t1 t2 => diffeological_smooth_app (denote_tm t2) (denote_tm t1)
  | abs σ ρ f => curry (denote_tm f)

  | tuple σ ρ t1 t2 => (denote_tm t1, denote_tm t2)
  | first σ ρ t => fst (denote_tm t)
  | second σ ρ t => snd (denote_tm t)
  end.

Definition diff_func :=
  forall T1 T2, T1 -> T2.

Theorem one : forall Γ τ (t : Γ τ),
  true = true.
Proof.