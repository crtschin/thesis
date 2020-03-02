Require Import Lists.List.
Import ListNotations.
Require Import Strings.String.
Require Import Logic.FunctionalExtensionality.
Require Import Reals.
Require Import Logic.JMeq.
Require Import Arith.PeanoNat.
Require Import Program.Equality.

From AD Require Import Definitions.

Definition sub Γ τ : Type := (Var Γ τ * tm Γ τ).

Fixpoint substitute {Γ Γ' τ v} (t : tm Γ τ) (s : sub Γ τ) : tm Γ τ :=
  match t with
  | var _ _ v => if fst s = v then snd s else v
  | app _ _ _ t1 t2 => app _ _ _ (substitute s t1) (substitute s t2)
  | abs _ _ _ f => abs _ _ _ (substitute (substitute_lifted s) f)

  | const _ r => const _ r
  | add _ t1 t2 => add _ (substitute s t1) (substitute s t2)

  | tuple _ t1 t2 => tuple  _ (substitute s t1) (substitute s t2)
  | first _ p => first _ (substitute s p)
  | second _ p => second _ (substitute s p)
  end.
