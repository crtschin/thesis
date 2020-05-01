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

  (* Bounded iteration *)
  | ifold : forall τ,
    tm_f Γ (Nat → τ → τ) -> tm_f Γ Nat -> tm_f Γ τ -> tm_f Γ τ
.

Lemma multistep_Ifold1 : forall Γ τ i (t t' : tm Γ τ) f,
  (t -->* t') ->
    ifold Γ τ f i t -->* ifold Γ τ f i t'.
Proof with quick.
  intros. induction H; econstructor... econstructor. assumption.
Qed.

Lemma multistep_Ifold2 : forall Γ τ i i' (t : tm Γ τ) f,
  value t ->
  (i -->* i') ->
    ifold Γ τ f i t -->* ifold Γ τ f i' t.
Proof with quick.
  intros. induction H0; econstructor... econstructor; assumption.
Qed.

Lemma multistep_Ifold3 : forall Γ τ i f' (t : tm Γ τ) f,
  value t ->
  value i ->
  (f -->* f') ->
    ifold Γ τ f i t -->* ifold Γ τ f' i t.
Proof with quick.
  intros. induction H1; econstructor... econstructor; assumption.
Qed.

(*
  Stepping for iteration

  | ST_Fold1 : forall Γ τ tf i (t t' : tm Γ τ),
    t --> t' ->
    ifold Γ τ tf i t --> ifold Γ τ tf i t'
  | ST_Fold2 : forall Γ τ tf i i' (t : tm Γ τ),
    value t ->
    i --> i' ->
    ifold Γ τ tf i t --> ifold Γ τ tf i' t
  | ST_Fold3 : forall Γ τ tf tf' i (t : tm Γ τ),
    value t ->
    value i ->
    tf --> tf' ->
    ifold Γ τ tf i t --> ifold Γ τ tf' i t
  | ST_FoldN0 : forall Γ τ f (t : tm Γ τ),
    ifold Γ τ (abs _ _ _ (abs _ _ _ f)) (nval _ 0) t --> t
  | ST_FoldNS : forall Γ τ f (t : tm Γ τ) n,
    ifold Γ τ (abs _ _ _ (abs _ _ _ f)) (nval _ (S n)) t -->
      ifold Γ τ (abs Γ (τ → τ) ℕ (abs (ℕ::Γ) τ τ
        (substitute
          (| var (τ::ℕ::Γ) ℕ (Pop _ _ _ (Top _ _));
              var (τ::ℕ::Γ) τ (Top _ _) |) (shift (shift f)))))
              (nval _ n) (substitute (| t ; nval _ 0 |) f)

*)
