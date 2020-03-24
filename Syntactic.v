Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Arith_base.
Require Import Coquelicot.Derive.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Equations.Equations.
Import EqNotations.

Require Import AD.Definitions.
Require Import AD.Macro.
Require Import AD.Tactics.
Require Import AD.Normalization.
Require Import AD.Denotation.
(* Require Import AD.Tangent. *)

Local Open Scope program_scope.
Local Open Scope R_scope.
(*
Equations S τ : tm [] τ -> tm [] (Dt τ) -> Prop :=
S Real t s :=
  ⟦ first _ s ⟧ₜₘ = ⟦ t ⟧ₜₘ /\
  ⟦ second _ s ⟧ₜₘ = fun c => Derive (fun _ => ⟦ t ⟧ₜₘ c). *)