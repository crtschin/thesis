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
(* STLC extra *)
Dtm (Γ:=Γ) (τ:=τ) (letn Γ τ σ t b) := letn _ _ _ (Dtm t) (Dtm b);
(* Arrays *)
Dtm (Γ:=Γ) (τ:=τ) (build_nil Γ τ) => build_nil _ _;
Dtm (Γ:=Γ) (τ:=τ) (build_cons Γ τ n t ta) =>
  build_cons _ _ _ (Dtm t) (Dtm ta);
Dtm (Γ:=Γ) (τ:=τ) (get Γ ti ta) => get _ ti (Dtm ta);
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

(* Equations Dsubstitute {Γ Γ' τ} (s : sub Γ Γ') (t : tm Γ τ)
    : tm (Dctx Γ') (Dt τ) :=
Dsubstitute (Γ:=Γ) (τ:=τ) s (var Γ τ v) := Dtm (s _ v);
Dsubstitute (Γ:=Γ) (τ:=τ) s (app Γ τ σ t1 t2) := app _ _ _ (Dsubstitute s t1) (Dsubstitute s t2);
Dsubstitute (Γ:=Γ) (τ:=τ) s (abs Γ τ σ f) := abs _ _ _ (Dsubstitute (substitute_lifted s) f);
Dsubstitute (Γ:=Γ) (τ:=τ) s (rval Γ r) := tuple _ (rval _ r) (rval _ 0);
Dsubstitute (Γ:=Γ) (τ:=τ) s (add Γ t1 t2) with Dsubstitute s t1 := {
  Dsubstitute (Γ:=Γ) (τ:=τ) s (add Γ t1 t2) d1 with Dsubstitute s t2 := {
    Dsubstitute (Γ:=Γ) (τ:=τ) s (add Γ t1 t2) d1 d2 :=
      tuple _
        (add _ (first _ d1) (first _ d2))
        (add _ (second _ d1) (second _ d2))
  }
};
Dsubstitute (Γ:=Γ) (τ:=τ) s (tuple Γ t1 t2) := tuple _ (Dsubstitute s t1) (Dsubstitute s t2);
Dsubstitute (Γ:=Γ) (τ:=τ) s (first Γ p) := first _ (Dsubstitute s p);
Dsubstitute (Γ:=Γ) (τ:=τ) s (second Γ p) := second _ (Dsubstitute s p);
Dsubstitute (Γ:=Γ) (τ:=τ) s (case Γ e c1 c2) := case _ (Dsubstitute s e) (Dsubstitute s c1) (Dsubstitute s c2);
Dsubstitute (Γ:=Γ) (τ:=τ) s (inl Γ _ _ e) := inl _ _ _ (Dsubstitute s e);
Dsubstitute (Γ:=Γ) (τ:=τ) s (inr Γ _ _ e) := inr _ _ _ (Dsubstitute s e). *)

(* Lemma D_rename_lifted : forall Γ Γ' τ σ
  (r : ren Γ Γ') (t : tm (σ::Γ) τ) ,
  Dtm (rename (rename_lifted r) t)
    = Drename (Drename_lifted (fun ρ => Dv ∘ r ρ)) t.
Proof with quick.
  dependent induction t; quick; simp Dtm;
    try solve [rewrites]...
  { dependent induction v... }
  { simp Drename.
    fold (map Dt).
    unfold compose.
    simp Drename_lifted Drename.
    assert (H: (Dtm (rename (rename_lifted (rename_lifted r)) t))
      = (Drename (Drename_lifted (Drename_lifted
           (fun (ρ : ty) (x : ρ ∈ Γ) => Dv (r ρ x)))) t)).
    { admit. }
    rewrite H... }
  { simp Drename.
    specialize IHt1 with Γ σ r t1.
    specialize IHt2 with Γ σ r t2. rewrites... }
Admitted.

Lemma D_shift : forall Γ Γ' τ σ (sb : sub Γ Γ') (t : tm Γ τ),
  Dtm (shift (σ:=σ) t) = Dshift (σ:=σ) t.
Proof with quick.
  intros.
  induction t; quick; simp Dtm;
    unfold shift in *; simpl; simp Dtm;
    unfold Dshift; simp Drename; quick;
    fold Dt (map Dt); try solve [rewrites]...
  { rewrite D_rename_lifted... }
Qed.

Lemma D_rename : forall Γ Γ' τ (t : tm Γ τ) (r : ren Γ Γ'),
  Dtm (rename r t) = Drename (fun σ => Dv ∘ r σ) t.
Proof with quick.
  induction t; quick;
    simp Drename Dtm; try solve [rewrites]...
  { fold (map Dt).
    rewrite D_rename_lifted... }
Qed. *)

(* Lemma D_sub_lifted : forall Γ Γ' τ σ
  (t : tm (σ::Γ) τ)
  (sb : sub Γ Γ'),
  Dtm (substitute (substitute_lifted sb) t) =
    Dsubstitute (substitute_lifted sb) t.
Proof with quick.
  dependent induction t; quick;
    simp Dtm Dsubstitute; try solve [rewrites].
  { fold (map Dt).
    pose proof (IHt (σ::Γ) σ0 t JMeq_refl JMeq_refl); clear IHt.
    assert (H': Dtm (substitute (substitute_lifted (substitute_lifted sb)) t)
      = Dsubstitute (substitute_lifted (substitute_lifted sb)) t).
    { remember (substitute_lifted sb).
      admit. }
    rewrite H'... }
  { simp Dtm.
    specialize IHt1 with Γ σ t1 sb.
    specialize IHt2 with Γ σ t2 sb. rewrites... }
Admitted.

Lemma D_sub : forall Γ Γ' τ
  (t : tm Γ τ)
  (sb : sub Γ Γ'),
  Dtm (substitute sb t) =
    Dsubstitute sb t.
Proof with quick.
  intros.
  unfold compose.
  induction t; simp Dsubstitute; quick; simp Dtm; rewrites.
  { fold (map Dt).
    rewrite D_sub_lifted... }
Admitted.


(* Suspicious *)
Definition Dsub' {Γ Γ'} : sub Γ Γ' -> sub (Dctx Γ) (Dctx Γ').
Admitted.

Lemma D_sub_lift' : forall Γ Γ' τ σ (t : tm (σ::Γ) τ)
  (sb : sub Γ Γ'),
  Dtm (substitute (substitute_lifted (τ:=σ) sb) t) =
    substitute (substitute_lifted (Dsub' sb)) (Dtm t).
Proof with quick.
Admitted.

Lemma D_sub_cons' : forall Γ Γ' τ σ
  (t : tm (σ::Γ) τ) (s : tm Γ' σ)
  (sb : sub Γ Γ'),
  Dtm (substitute (cons_sub s sb) t) =
    substitute (cons_sub (Dtm s) (Dsub' sb)) (Dtm t).
Proof with quick.
Admitted.

Lemma D_sub' : forall Γ Γ' τ σ
  (t : tm (σ::Γ) τ) (s : tm Γ' σ)
  (sb : sub Γ Γ'),
  Dtm (substitute (cons_sub s sb) t) =
    substitute (cons_sub (Dtm s) (Dsub' sb)) (Dtm t).
Proof with quick.
Admitted. *)
(*
Lemma D_sub_lifted : forall Γ τ σ ρ (t : tm (ρ::σ::Γ) τ) (s: tm Γ σ),
Dtm (substitute (substitute_lifted (| s |)) t) =
  substitute (substitute_lifted (| Dtm s |)) (Dtm t).
Proof with quick.
  dependent induction t...
  - dependent induction v...
    rewrite IHv...
Admitted.

Lemma D_sub : forall Γ τ σ
  (t : tm (σ::Γ) τ)
  (s : tm Γ σ),
  Dtm (substitute (| s |) t) =
    substitute (| Dtm s |) (Dtm t).
Proof with quick.
  dependent induction t;
    try solve [quick; simp Dtm; rewrites]...
  - dependent induction v...
  - simp Dtm. fold (map Dt).
    unfold id_sub...
    pose proof (IHt (σ::Γ) σ0 t JMeq_refl JMeq_refl).
    rewrite D_sub_lifted...
  - simp Dtm.
    specialize IHt1 with Γ σ t1 s.
    specialize IHt2 with Γ σ t2 s. rewrites...
Admitted. *)