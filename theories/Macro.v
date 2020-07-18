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
  | Bool => Bool
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
  | var Γ τ v := var _ _ (Dv v);
  | app Γ τ σ t1 t2 := app _ _ _ (Dtm t1) (Dtm t2);
  | abs Γ τ σ f := abs _ _ _ (Dtm f);
(* Bool *)
  | tru _ => tru _;
  | fls _ => fls _;
  | ifelse _ _ b t f => ifelse _ _ (Dtm b) (Dtm t) (Dtm f);
  | rlt _ t1 t2 => rlt _ (first _ (Dtm t1)) (first _ (Dtm t2));
(* Arrays *)
  | build Γ τ n ta => build _ _ _ (Dtm ∘ ta);
  | get Γ ti ta => get _ ti (Dtm ta);
(* Nat *)
  | nval Γ n := nval _ n;
  | nsucc _ t := nsucc _ (Dtm t);
  | nrec _ _ f i d => nrec _ _ (Dtm f) (Dtm i) (Dtm d);
(* Reals *)
  | rval Γ r := tuple _ (rval _ r) (rval _ 0);
  | (add Γ t1 t2) with Dtm t1 := {
    | d1 with Dtm t2 := {
      | d2 :=
      tuple _
        (add _ (first _ d1) (first _ d2))
        (add _ (second _ d1) (second _ d2))
  }
};
  | (mul Γ t1 t2) with Dtm t1 := {
    | d1 with Dtm t2 := {
      | d2 :=
      tuple _
        (mul _ (first _ d1) (first _ d2))
        (add _
          (mul _ (first _ d1) (second _ d2))
          (mul _ (first _ d2) (second _ d1)))
  }
};
(* Products *)
  | tuple Γ t1 t2 := tuple _ (Dtm t1) (Dtm t2);
  | first Γ p := first _ (Dtm p);
  | second Γ p := second _ (Dtm p);
(* Sums *)
  | case Γ e c1 c2 := case _ (Dtm e) (Dtm c1) (Dtm c2);
  | inl Γ _ _ e := inl _ _ _ (Dtm e);
  | inr Γ _ _ e := inr _ _ _ (Dtm e).

(* Equations Denv {Γ}: forall {τ}, Env τ Γ -> Env (Dt τ) (Dctx Γ) :=
Denv (τ:=τ) env_nil => env_nil (Dt τ);
Denv (τ:=τ) (env_cons Γ t G) => env_cons (Dt τ) (Dtm t) (Denv G). *)

Fixpoint Denv {Γ} (G : Env Γ): Env (Dctx Γ) :=
  match G with
  | env_nil => env_nil
  | env_cons _ _ t G => env_cons (Dtm t) (Denv G)
  end.

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
