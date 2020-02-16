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
Require Import Vectors.Vector.
Import EqNotations.

Require Import Definitions.
Require Import Macro.

Local Open Scope nat_scope.
Local Open Scope R_scope.

Definition R_space n := t R n.
Definition smooth_function n m := (R_space n -> R_space m) -> Prop.
(* Definition Diff := forall n m, R_space n -> R_space m. *)

Inductive Diff : Type :=
  | Df_R :
    Diff
  | Df_Prod :
    Diff -> Diff -> Diff
.

Inductive denote_t : ty -> Diff -> Type :=
  | dt_real : denote_t Real Df_R
  | dt_Prod : forall τ σ n m,
    denote_t τ n ->
    denote_t σ m ->
    denote_t (τ × σ) (Df_Prod n m)
  (* | D_Arrow : forall τ σ n m,
    denote_t τ n ->
    denote_t σ m ->
    denote_t (n + m) *)
.

Definition denote_tm
  : forall Γ τ, tm Γ τ -> Diff (denote_ctx Γ) (denote_t τ)
  := true.

Theorem one : forall Γ τ (t : Γ τ),
  true = true.
Proof.