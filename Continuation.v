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

From AD Require vect.
From Equations Require Import Equations.
From AD Require Import Definitions.
From AD Require Import Tactics.
From AD Require Import Denotation.

Local Open Scope program_scope.
Local Open Scope type_scope.

(* Continuation *)

Fixpoint Dt_c (n : nat) (σ : ty) : ty :=
  match σ with
  | Real => Real × (Real → Array n Real)
  | Array m τ => Array m (Dt_c n τ)
  | τ1 × τ2 => (Dt_c n τ1 × Dt_c n τ2)
  | τ1 → τ2 => (Dt_c n τ1 → Dt_c n τ2)
  | τ1 <+> τ2 => (Dt_c n τ1 <+> Dt_c n τ2)
  end.

Definition Dctx_c n Γ : Ctx := map (Dt_c n) Γ.

Fixpoint Dv_c n {Γ τ} (v: τ ∈ Γ) : (Dt_c n τ) ∈ (map (Dt_c n) Γ) :=
  match v with
  | Top Γ τ => Top (map (Dt_c n) Γ) (Dt_c n τ)
  | Pop Γ τ σ t =>
      Pop (map (Dt_c n) Γ) (Dt_c n τ) (Dt_c n σ) (Dv_c n t)
  end.

Equations Dtm_c n {Γ τ} : tm Γ τ -> tm (map (Dt_c n) Γ) (Dt_c n τ) :=
(* STLC *)
Dtm_c n (Γ:=Γ) (τ:=τ) (var Γ τ v) := var _ _ (Dv_c n v);
Dtm_c n (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) := app _ _ _ (Dtm_c n t1) (Dtm_c n t2);
Dtm_c n (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) := abs _ _ _ (Dtm_c n f);
(* Arrays *)
(* Dtm_c n (Γ:=Γ) (τ:=τ) (build_nil Γ τ) => build_nil _ _; *)
Dtm_c n (Γ:=Γ) (τ:=τ) (build Γ τ m ta) =>
  build _ _ _ (Dtm_c n ∘ ta);
Dtm_c n (Γ:=Γ) (τ:=τ) (get Γ ti ta) => get _ ti (Dtm_c n ta);
(* Reals *)
Dtm_c n (Γ:=Γ) (τ:=τ) (rval Γ r) :=
  tuple _ (rval _ r) (abs _ _ _ (build _ _ _ (const (rval _ 0))));
Dtm_c n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) with Dtm_c n t1 := {
  Dtm_c n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 with Dtm_c n t2 := {
    Dtm_c n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 d2 :=
      tuple _
        (add _ (first _ d1) (first _ d2))
        (abs _ _ _
          (array_add
            ((app _ _ _ (shift (second _ d1)) (var _ _ (Top _ _))))
            ((app _ _ _ (shift (second _ d2)) (var _ _ (Top _ _))))))
  }
};
(* Products *)
Dtm_c n (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) := tuple _ (Dtm_c n t1) (Dtm_c n t2);
Dtm_c n (Γ:=Γ) (τ:=τ) (first Γ p) := first _ (Dtm_c n p);
Dtm_c n (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm_c n p);
(* Sums *)
Dtm_c n (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) := case _ (Dtm_c n e) (Dtm_c n c1) (Dtm_c n c2);
Dtm_c n (Γ:=Γ) (τ:=τ) (inl Γ _ _ e) := inl _ _ _ (Dtm_c n e);
Dtm_c n (Γ:=Γ) (τ:=τ) (inr Γ _ _ e) := inr _ _ _ (Dtm_c n e).

(* Forward *)
Fixpoint Dt n τ : ty :=
  match τ with
  | Real => Real × Array n Real
  | Array m t => Array m (Dt n t)
  | t1 × t2 => Dt n t1 × Dt n t2
  | t1 → t2 => Dt n t1 → Dt n t2
  | t1 <+> t2 => Dt n t1 <+> Dt n t2
  end.

Definition Dctx n Γ : Ctx := map (Dt n) Γ.

Fixpoint Dv {n Γ τ} (v: τ ∈ Γ) : (Dt n τ) ∈ (Dctx n Γ) :=
  match v with
  | Top Γ τ => Top (map (Dt n) Γ) (Dt n τ)
  | Pop Γ τ σ t => Pop (map (Dt n) Γ) (Dt n τ) (Dt n σ) (Dv t)
  end.

Equations Dtm n {Γ τ} : tm Γ τ -> tm (map (Dt n) Γ) (Dt n τ) :=
(* STLC *)
Dtm n (Γ:=Γ) (τ:=τ) (var Γ τ v) := var _ _ (Dv v);
Dtm n (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) := app _ _ _ (Dtm n t1) (Dtm n t2);
Dtm n (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) := abs _ _ _ (Dtm n f);
(* Arrays *)
(* Dtm n (Γ:=Γ) (τ:=τ) (build_nil Γ τ) => build_nil _ _; *)
Dtm n (Γ:=Γ) (τ:=τ) (build Γ τ m ta) =>
  build _ _ _ (Dtm n ∘ ta);
Dtm n (Γ:=Γ) (τ:=τ) (get Γ ti ta) => get _ ti (Dtm n ta);
(* Reals *)
Dtm n (Γ:=Γ) (τ:=τ) (rval Γ r) :=
  tuple _ (rval _ r) (build _ _ _ (const (rval _ 0)));
Dtm n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) with Dtm n t1 := {
  Dtm n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 with Dtm n t2 := {
    Dtm n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 d2 :=
      tuple _
        (add _ (first _ d1) (first _ d2))
        (array_add (second _ d1) (second _ d2))
  }
};
(* Products *)
Dtm n (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) := tuple _ (Dtm n t1) (Dtm n t2);
Dtm n (Γ:=Γ) (τ:=τ) (first Γ p) := first _ (Dtm n p);
Dtm n (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm n p);
(* Sums *)
Dtm n (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) := case _ (Dtm n e) (Dtm n c1) (Dtm n c2);
Dtm n (Γ:=Γ) (τ:=τ) (inl Γ _ _ e) := inl _ _ _ (Dtm n e);
Dtm n (Γ:=Γ) (τ:=τ) (inr Γ _ _ e) := inr _ _ _ (Dtm n e).

(* Definition lam_ctx τ : Ctx -> Ctx. *)

Definition ren_c n m :
  ren (map (Dt n) (repeat Real m)) (map (Dt_c n) (repeat Real m)).
Proof with quick.
  unfold ren.
Admitted.

Definition ren_c' n m :
  ren (map (Dt_c n) (repeat Real m)) (map (Dt n) (repeat Real m)).
Proof with quick.
  unfold ren.
Admitted.

Lemma ren_ren' : forall Γ n m v,
  ren_c n m Γ (ren_c' n m Γ v) = v.
Proof with quick.
  intros.
Admitted.

Lemma ren'_ren : forall Γ n m v,
  ren_c' n m Γ (ren_c n m Γ v) = v.
Proof with quick.
  intros.
Admitted.

Lemma rename_ren'_ren :
  forall τ n m (t : tm (map (Dt n) (repeat Real m)) (Dt n τ)),
    rename (ren_c' n m) (rename (ren_c n m) t) = t.
Proof with quick.
  intros.
Admitted.

Lemma rename_ren_ren' :
  forall τ n m (t : tm (map (Dt_c n) (repeat Real m)) (Dt_c n τ)),
    rename (ren_c n m) (rename (ren_c' n m) t) = t.
Proof with quick.
  intros.
Admitted.

Definition lam_r {n m}
  (t : tm (map (Dt n) (repeat Real m)) (Dt n Real))
  : tm (map (Dt_c n) (repeat Real m)) (Dt_c n Real) :=
  tuple _ (first _ (rename (ren_c n m) t))
    (abs _ _ Real ((shift (σ:= Real) (second _ (rename (ren_c n m) t))))).

Equations lam {n m} τ
  {pf1: forall τ1 τ2, τ <> (τ1 → τ2)}
  {pf2: forall τ1 τ2, τ <> (τ1 <+> τ2)}
  {pf3: forall m τ', τ <> (Array m τ')}
  {pf4: forall τ1 τ2, τ <> (τ1 × τ2)}
  (t : tm (map (Dt n) (repeat Real m)) (Dt n τ))
  : tm (map (Dt_c n) (repeat Real m)) (Dt_c n τ) :=
lam Real z := lam_r z;
lam (τ1 × τ2) z
  with pf4 τ1 τ2 eq_refl := { };
  (* := tuple _ (lam τ1 (first _ z)) (lam τ2 (second _ z)); *)
lam (τ1 → τ2) z
  with pf1 τ1 τ2 eq_refl := { };
lam (Array m τ) z
  with pf3 m τ eq_refl := { };
lam (τ1 <+> τ2) z
  with pf2 τ1 τ2 eq_refl := { }.
  (* := case (Dctx n (repeat Real m)) z
    (abs _ (Dt_c n τ1 <+> Dt_c n τ2) (Dt_c n τ1)
      (inl _ _ _ (lam n τ1 (var _ _ (Top _ _)))))
    (abs _ (Dt_c n τ1 <+> Dt_c n τ2) (Dt_c n τ2)
      (inr _ _ _ (lam n τ2 (var _ _ (Top _ _))))). *)

(* Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted.
Next Obligation.
  Admitted. *)

Definition ev_r {n m}
  : tm (map (Dt_c n) (repeat Real m)) (Dt_c n Real) ->
    tm (map (Dt n) (repeat Real m)) (Dt n Real) :=
  fun z => tuple _
    (first _ (rename (ren_c' n m) z))
    (app _ _ _ (second _ (rename (ren_c' n m) z)) (rval _ 1)).

Lemma four :
  (* forall τ τ1 τ2, *)
  forall n m (t : tm (repeat Real m) Real),
  (* (τ <> (τ1 → τ2)) -> *)
  ⟦ev_r (lam_r (Dtm n t))⟧ₜₘ = ⟦Dtm n t⟧ₜₘ.
Proof with quick.
  intros. remember (Dtm n t) as t'.
  dependent induction t';
    unfold lam_r; unfold ev_r; quick.
  { extensionality ctx. simp denote_tm.
    apply injective_projections...
    { apply f_equal.
      rewrite ren'_ren... }
    { simp denote_tm. simp rename_lifted...
      apply f_equal.
      erewrite ren'_ren... } }
  { extensionality ctx. simp denote_tm.
    apply injective_projections...
    all: admit.
Admitted.