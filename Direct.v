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

Fixpoint denote_t τ : Type :=
  match τ with
  | Real => R
  | τ1 × τ2 => denote_t τ1 * denote_t τ2
  | τ1 → τ2 => denote_t τ1 -> denote_t τ2
  end.
Notation "⟦ t ⟧" := (denote_t t).

Record Gl := make_gl {
  X : ty;
  Y : ty;
  P : (R -> ⟦X⟧) -> (R -> ⟦Y⟧) -> Prop;
}.

Definition interpret τ : Gl :=
  make_gl τ (Dt τ) (fun f g => forall x, g x = (f x, denote f x)).
