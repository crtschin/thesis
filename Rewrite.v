Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Vector.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Reals.

Local Open Scope program_scope.

From Equations Require Import Equations.
From AD Require Import Tactics.
From AD Require Import Definitions.
From AD Require Import Normalization.
From AD Require Import Macro.
From AD Require Import Denotation.

Reserved Notation "t ~> s" (at level 30).
Inductive rwrt : forall {Γ τ}, tm Γ τ -> tm Γ τ -> Prop :=
  | RW_Id : forall Γ τ (t t': tm Γ τ),
    t ~> t'
  | RW_Mstep : forall Γ τ (t t': tm Γ τ),
    t -->* t' ->
    t ~> t'
  | RW_Abs : forall Γ τ σ (t t': tm (σ::Γ) τ),
    t ~> t' ->
    abs _ _ _ t ~> abs _ _ _ t'
  (* Tuple PE *)
  | RW_Tuple : forall Γ τ σ (t1 t1': tm Γ τ) (t2 t2': tm Γ σ),
    t1 ~> t1' ->
    t2 ~> t2' ->
    tuple _ t1 t2 ~> tuple _ t1' t2'
  | RW_First : forall Γ τ σ (t1: tm Γ τ) (t2: tm Γ σ),
    first _ (tuple _ t1 t2) ~> t1
where "t ~> s" := (rwrt t s).