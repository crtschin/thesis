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

Reserved Notation "t1 ⇓ t2" (at level 40).
Inductive eval : forall {Γ τ}, tm Γ τ -> tm Γ τ -> Prop :=
  (* Base STLC *)
  | EV_AppAbs : forall Γ τ σ t1 t1' t2 t2',
      t1 ⇓ (abs Γ τ σ t1') ->
      t2 ⇓ t2' ->
      (app Γ τ σ t1 t2) ⇓ (substitute (| t2' |) t1')

  (* Add *)
  | EV_Add : forall Γ t1 t1' t2 t2',
      t1 ⇓ (const Γ t1') ->
      t2 ⇓ (const Γ t2') ->
      add Γ t1 t2 ⇓ const Γ (Rdefinitions.Rplus t1' t2')

  (* Pairs *)
  | EV_Tuple1 : forall Γ τ σ t1 t1' t2 t2',
      t1 ⇓ t1' ->
      t2 ⇓ t2' ->
      (@tuple Γ τ σ t1 t2) ⇓ (@tuple Γ τ σ t1' t2')
  | EV_Fst : forall Γ τ σ t1 t1' t2',
        t1 ⇓ @tuple Γ τ σ t1' t2' ->
        (@first Γ τ σ t1) ⇓ t1'
  | EV_Snd : forall Γ τ σ t1' t2 t2',
        t2 ⇓ @tuple Γ τ σ t1' t2' ->
        (@second Γ τ σ t2) ⇓ t2'

  (* Sums *)
  | EV_CaseInl : forall Γ τ σ ρ t1 t2 t1' t2' e e',
      e ⇓ (inl Γ e') ->
      (t1 ⇓ t1') ->
      (t2 ⇓ t2') ->
      (@case Γ τ σ ρ e t1 t2) ⇓ (app Γ ρ τ t1' e')
  | EV_CaseInr : forall Γ τ σ ρ t1 t2 t1' t2' e e',
      e ⇓ (inr Γ e') ->
      (t1 ⇓ t1') ->
      (t2 ⇓ t2') ->
      (@case Γ τ σ ρ e t1 t2) ⇓ (app Γ ρ σ t2' e')

  | EV_Inl : forall Γ τ σ t1 t1',
        t1 ⇓ t1' ->
        (@inl Γ τ σ t1) ⇓ (@inl Γ τ σ t1')
  | EV_Inr : forall Γ τ σ t1 t1',
        t1 ⇓ t1' ->
        (@inr Γ τ σ t1) ⇓ (@inr Γ τ σ t1')
where "t  ⇓  v" := (eval t v).

Lemma natural_soundness : forall Γ τ (t1 : tm Γ τ) (t2 : tm Γ τ),
  t1 ⇓ t2 -> ⟦ t1 ⟧ₜₘ = ⟦ t2 ⟧ₜₘ.
Proof with quick.
  intros.
  induction H; simpl; extensionality ctx; rewrites.
  { rewrite <- denote_sub_commutes...
    unfold id_sub.
    unfold hd_sub. simp cons_sub.
    rewrite denote_sub_tl_cons...
    fold (@id_sub Γ). rewrite denote_sub_id_ctx... }
Qed.

(* Lemma D_natural : forall Γ τ (t1 : tm Γ τ) (t2 : tm Γ τ),
  t1 ⇓ t2 -> Dtm t1 ⇓ Dtm t2.
Proof with quick.
  intros.
  induction H; simpl; rewrites; simp Dtm in *; try (econstructor; quick).
  { fold Dt.
    (* TODO: Prove D_sub *)
    rewrite D_sub'.
    unfold Basics.compose.
    eassert ((fun (σ0 : ty) (x : σ0 ∈ σ :: Γ) => Dtm ((| t2' |) σ0 x))
      = (fun (σ0 : ty) (x : σ0 ∈ σ :: Γ) => ((| Dtm t2' |) (Dt σ0) (Dv x)))).
    { extensionality ρ.
      extensionality v.
      rewrite D_cons_sub... }
    rewrite H1. admit. }
  { constructor; eapply EV_Fst... }
  { assert (Rdefinitions.IZR BinNums.Z0 =
      Rdefinitions.Rplus Rdefinitions.R0 Rdefinitions.R0).
    { rewrite Rplus_0_r... }
    rewrite H1.
    eapply EV_Add; eapply EV_Snd... }
Admitted. *)
