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

From CoLoR Require Import Vector.VecUtil.
From Equations Require Import Equations.
From AD Require Import Definitions.
From AD Require Import Tactics.

Local Open Scope program_scope.
Local Open Scope R_scope.

(* Functorial macro *)

Fixpoint Dt τ : ty :=
  match τ with
  | Real => Real × Real
  | Nat => Nat
  | Array n t => Array n (Dt t)
  | t1 × t2 => Dt t1 × Dt t2
  | t1 → t2 => Dt t1 → Dt t2
  | t1 <+> t2 => Dt t1 <+> Dt t2
  end.

Definition Dctx Γ : Ctx := map Dt Γ.

Fixpoint Dv {Γ τ} (v: τ ∈ Γ) : (Dt τ) ∈ (map Dt Γ) :=
  match v with
  | Top Γ τ => Top (map Dt Γ) (Dt τ)
  | Pop Γ τ σ t => Pop (map Dt Γ) (Dt τ) (Dt σ) (Dv t)
  end.

Equations Dtm {Γ τ} : tm Γ τ -> tm (map Dt Γ) (Dt τ) :=
(* STLC *)
Dtm (Γ:=Γ) (τ:=τ) (var Γ τ v) := var _ _ (Dv v);
Dtm (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) := app _ _ _ (Dtm t1) (Dtm t2);
Dtm (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) := abs _ _ _ (Dtm f);
(* Arrays *)
(* Dtm (Γ:=Γ) (τ:=τ) (build_nil Γ τ) => build_nil _ _; *)
Dtm (Γ:=Γ) (τ:=τ) (build Γ τ n ta) =>
  build _ _ _ (Dtm ∘ ta);
Dtm (Γ:=Γ) (τ:=τ) (get Γ ti ta) => get _ ti (Dtm ta);
(* Nat *)
Dtm (Γ:=Γ) (τ:=τ) (nval Γ n) := (nval _ n);
(* Reals *)
Dtm (Γ:=Γ) (τ:=τ) (rval Γ r) := tuple _ (rval _ r) (rval _ 0);
Dtm (Γ:=Γ) (τ:=τ) (add Γ t1 t2) with Dtm t1 := {
  Dtm (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 with Dtm t2 := {
    Dtm (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 d2 :=
      tuple _
        (add _ (first _ d1) (first _ d2))
        (add _ (second _ d1) (second _ d2))
  }
};
(* Products *)
Dtm (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) := tuple _ (Dtm t1) (Dtm t2);
Dtm (Γ:=Γ) (τ:=τ) (first Γ p) := first _ (Dtm p);
Dtm (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm p);
(* Sums *)
Dtm (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) := case _ (Dtm e) (Dtm c1) (Dtm c2);
Dtm (Γ:=Γ) (τ:=τ) (inl Γ _ _ e) := inl _ _ _ (Dtm e);
Dtm (Γ:=Γ) (τ:=τ) (inr Γ _ _ e) := inr _ _ _ (Dtm e).

Definition Dsub (Γ Γ' : list ty) :=
  forall τ, Var Γ τ -> tm (Dctx Γ') (Dt τ).

Definition Dren (Γ Γ' : list ty) :=
  forall τ, Var Γ τ -> Var (Dctx Γ') (Dt τ).

Lemma Dt_lift_var : forall Γ τ, τ ∈ Γ -> (Dt τ) ∈ (map Dt Γ).
Proof with eauto.
  intros Γ τ H. induction H; constructor. assumption.
Qed.

Lemma D_cons_sub: forall Γ τ σ (v: τ ∈ σ :: Γ) (s: tm Γ σ),
  Dtm ((| s |) τ v) = (| Dtm s |) (Dt τ) (Dv v).
Proof with quick.
  dependent induction v...
Qed.
