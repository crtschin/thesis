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

Local Open Scope nat_scope.
Local Open Scope R_scope.

(*
  Goal: Write out the logical relation over types with the goal of having both
    the proof of differentiability and witness in one.

  Will piggyback on Coq's types
*)

Reserved Notation "⟦ T ⟧ₜ".
Fixpoint denote_t τ : Type :=
  match τ with
  | Real => R
  | τ1 × τ2 => ⟦τ1⟧ₜ * ⟦τ2⟧ₜ
  | τ1 → τ2 => ⟦τ1⟧ₜ -> ⟦τ2⟧ₜ
  end
where "⟦ T ⟧ₜ" := (denote_t T).

Reserved Notation "⟦ T ⟧ₜₓ".
Fixpoint denote_ctx (Γ : Ctx) : Type :=
  match Γ with
  | [] => unit
  | h :: t => ⟦h⟧ₜ * ⟦t⟧ₜₓ
  end
where "⟦ T ⟧ₜₓ" := (denote_ctx T).

Check snd.
Program Fixpoint denote_v {Γ τ} (v: τ ∈ Γ) : denote_ctx Γ -> denote_t τ  :=
  match v with
  | Top Γ' τ' => fun gamma => fst gamma
  | Pop Γ' τ' σ x => fun _ => ⟦ τ ⟧ₜ
  end.

Fixpoint denote_tm Γ τ (t : tm Γ τ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ :=
  match t with
  | const _ r         => (fun ctx => _)
  | add _ t1 t2       => (fun ctx => _)

  | var _ _ v         => (fun ctx => _)
  | app _ _ _ t1 t2   => (fun ctx => _)
  | abs _ _ _ f       => (fun ctx => _)

  | tuple _ _ _ t1 t2 => (fun ctx => _)
  | first _ _ _ p       => (fun ctx => _)
  | second _ _ _ p       => (fun ctx => _)
  end.

Record Gl := make_gl {
  X : ty;
  Y : ty;
  P : (R -> ⟦X⟧ₜ) -> (R -> ⟦Y⟧ₜ) -> Prop;
}.

(*
  Relation used by Gl giving a notion of
    differentiability between ⟦τ⟧ₜ and ⟦σ⟧ₜ
*)
Inductive diff : forall τ σ, (R -> ⟦τ⟧ₜ) -> (R -> ⟦σ⟧ₜ) -> Prop :=
  | diff_r : diff Real (Dt Real) id (fun r => (r, r))
  | diff_prod : forall τ σ f1 f2 g1 g2,
      diff τ (Dt τ) f1 g1 ->
      diff σ (Dt σ) f2 g2 ->
      diff (τ × σ) (Dt (τ × σ))
        (fun r => (f1 r, f2 r))
        (fun r => (g1 r, g2 r))
  | diff_arr : forall τ σ f1 g1,
      diff τ (Dt τ) f1 g1 ->
      diff (σ → τ) (Dt (σ → τ))
        (fun r => fun s => f1 r)
        (fun r => fun s => g1 r)
.

(* Inhabitants of Gl *)
Definition Gl_R : Gl :=
  make_gl Real (Dt Real) (diff Real (Dt Real))
.

Definition Gl_Prod τ σ : Gl :=
  make_gl (τ × σ) (Dt (τ × σ)) (diff (τ × σ) (Dt (τ × σ)))
.

Definition Gl_Arr τ σ : Gl :=
  make_gl (τ → σ) (Dt (τ → σ)) (diff (τ → σ) (Dt (τ → σ)))
.
