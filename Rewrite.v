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
  | RW_Id : forall Γ τ (t: tm Γ τ),
    t ~> t
  (* Inherit normalization rules from stepping relation *)
  | RW_Mstep : forall Γ τ (t t': tm Γ τ),
    t -->* t' ->
    t ~> t'
  (* Function PE *)
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
  | RW_Second : forall Γ τ σ (t1: tm Γ τ) (t2: tm Γ σ),
    second _ (tuple _ t1 t2) ~> t2
  (* Ring addition *)
  | RW_add : forall Γ (t1 t1' t2 t2' : tm Γ ℝ),
    t1 ~> t1' ->
    t2 ~> t2' ->
    add _ t1 t2 ~> add _ t1' t2'
  | RW_add0L : forall Γ (t2 : tm Γ ℝ),
    add _ (rval _ 0) t2 ~> t2
  | RW_add0R : forall Γ (t1 : tm Γ ℝ),
    add _ t1 (rval _ 0) ~> t1
  | RW_add_R : forall Γ r,
    add Γ (rval Γ r) (rval Γ (-r)) ~> rval Γ 0
  | RW_add_L : forall Γ r,
    add Γ (rval Γ (-r)) (rval Γ r) ~> rval Γ 0
where "t ~> s" := (rwrt t s).

Lemma rewrite_soundness : forall τ (t t' : tm [] τ),
  t ~> t' -> ⟦ t ⟧ₜₘ = ⟦ t' ⟧ₜₘ.
Proof with quick.
  intros.
  dependent induction H...
  { apply soundness... }
  { extensionality ctx.
    simp denote_tm. fold denote_t.
    extensionality x.
    rewrites.
    admit. }
Admitted.
