Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Vectors.Fin.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.

Require Import CoLoR.Util.Vector.VecUtil.
Require Import Equations.Equations.
Require Import AD.Tactics.
Require Import AD.Definitions.
Require Import AD.Normalization.

Local Open Scope program_scope.

Inductive tm_f (Γ : Ctx) : ty -> Type :=
  (* Base STLC *)
  | inherit : forall τ,
    tm Γ τ -> tm_f Γ τ
.
