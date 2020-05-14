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

(* Variable (Γ : list ty).
Variable (τ σ ρ : ty).
Variable (t1: tm Γ τ).
Variable (t2: tm (τ::Γ) σ).
Variable (t3: tm (σ::τ::Γ) ρ).
Check (letin t2 t3).
Check (letin (shift (letin t1 t2)) t3).
Check (letin t1 (letin t2 t3)). *)

Definition shift2 {Γ τ σ ρ} : tm (σ::Γ) τ -> tm (σ::ρ::Γ) τ.
Proof.
  intros t.
  pose proof (var (σ::Γ)) as f.
  epose proof shift as g.
  epose proof (substitute (fun τ v => var (σ::ρ::Γ) τ v)).
Admitted.

Reserved Notation "t ~> s" (at level 30).
Inductive rwrt : forall {Γ τ}, tm Γ τ -> tm Γ τ -> Prop :=
  | RW_Id : forall Γ τ (t: tm Γ τ),
    t ~> t
  (* Inherit normalization rules from stepping relation *)
  | RW_Mstep : forall τ (t t': tm [] τ),
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
  (* Lets *)
  | RW_LetDesugar : forall Γ τ σ (t1: tm (σ::Γ) τ) (t2: tm Γ σ),
    app _ _ _ (abs _ _ _ t1) t2 ~> letin t2 t1
  | RW_LetAssoc : forall Γ τ σ ρ
    (e0: tm Γ τ) (e1: tm (τ::Γ) σ) (e2: tm (σ::Γ) ρ),
    (* Original variant:
      let x :=               let y := e0 in
        let y := e0 in e1 ~> let x := e1 in
      in e2                  e2

      Presents a slight issue
      LHS: e2 does not have access to e0/y
      RHS: e2 does have access to e0/y but if it does
        correspond to LHS, then it does not 'use' it.
    *)
      letin (letin e0 e1) e2 ~>
        letin e0 (letin e1 (@shift (σ::Γ) ρ τ e2))
  (* Ring addition *)
  | RW_add : forall Γ (t1 t1' t2 t2' : tm Γ ℝ),
    t1 ~> t1' ->
    t2 ~> t2' ->
    add _ t1 t2 ~> add _ t1' t2'
  | RW_add0L : forall Γ (t2 t2': tm Γ ℝ),
    t2 ~> t2' ->
    add _ (rval _ 0) t2 ~> t2
  | RW_add0R : forall Γ (t1 t1': tm Γ ℝ),
    t1 ~> t1' ->
    add _ t1 (rval _ 0) ~> t1
  | RW_add_R : forall Γ r (t1 t2: tm Γ ℝ),
    t1 ~> rval Γ r ->
    t2 ~> rval Γ (-r) ->
    add Γ t1 t2 ~> rval Γ 0
  | RW_add_L : forall Γ r (t1 t2: tm Γ ℝ),
    t1 ~> rval Γ (-r) ->
    t2 ~> rval Γ r ->
    add Γ t1 t2 ~> rval Γ 0
where "t ~> s" := (rwrt t s).

Lemma rewrite_soundness : forall Γ τ (t t' : tm Γ τ),
  t ~> t' -> ⟦ t ⟧ₜₘ = ⟦ t' ⟧ₜₘ.
Proof with quick.
  intros.
  dependent induction H; quick;
    try solve [extensionality ctx; simp denote_tm; rewrites; trivial]...
  { apply soundness... }
  all: extensionality ctx; simp denote_tm; rewrites.
  (* { unfold letin.
    simp denote_tm.
    rewrite 2 denote_shift. simp denote_tm.
    admit. } *)
  { apply Rplus_0_l. }
  { rewrite Rplus_comm.
    apply Rplus_0_l. }
  { apply Rplus_opp_r. }
  { rewrite Rplus_comm.
    apply Rplus_opp_r. }
Admitted.
