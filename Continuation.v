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
From AD Require Import Tactics.
From AD Require Import Simply.
From AD Require Direct.

Local Open Scope program_scope.
Local Open Scope type_scope.

(* Continuation *)

Fixpoint Dt_c (n : nat) (σ : ty) : ty :=
  match σ with
  | Real => Real × (Real → Array n Real)
  (* | Nat => Nat *)
  | Array m τ => Array m (Dt_c n τ)
  | τ1 × τ2 => (Dt_c n τ1 × Dt_c n τ2)
  | τ1 → τ2 => (Dt_c n τ1 → Dt_c n τ2)
  (* | τ1 <+> τ2 => (Dt_c n τ1 <+> Dt_c n τ2) *)
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
          (vector_add
            ((app _ _ _ (shift (second _ d1)) (var _ _ (Top _ _))))
            ((app _ _ _ (shift (second _ d2)) (var _ _ (Top _ _))))))
  }
};
(* Products *)
Dtm_c n (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) := tuple _ (Dtm_c n t1) (Dtm_c n t2);
Dtm_c n (Γ:=Γ) (τ:=τ) (first Γ p) := first _ (Dtm_c n p);
Dtm_c n (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm_c n p).

(* Forward *)
Fixpoint Dt τ : ty :=
  match τ with
  | Real => Real × Real
  (* | Nat => Nat *)
  | Array m t => Array m (Dt t)
  | t1 × t2 => Dt t1 × Dt t2
  | t1 → t2 => Dt t1 → Dt t2
  (* | t1 <+> t2 => Dt t1 <+> Dt t2 *)
  end.

Definition Dctx Γ : Ctx := map (Dt) Γ.

Fixpoint Dv {Γ τ} (v: τ ∈ Γ) : (Dt τ) ∈ (Dctx Γ) :=
  match v with
  | Top Γ τ => Top (map (Dt) Γ) (Dt τ)
  | Pop Γ τ σ t => Pop (map (Dt) Γ) (Dt τ) (Dt σ) (Dv t)
  end.

Equations Dtm {Γ τ} : tm Γ τ -> tm (map (Dt) Γ) (Dt τ) :=
(* STLC *)
Dtm (Γ:=Γ) (τ:=τ) (var Γ τ v) := var _ _ (Dv v);
Dtm (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) := app _ _ _ (Dtm t1) (Dtm t2);
Dtm (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) := abs _ _ _ (Dtm f);
(* Arrays *)
(* Dtm (Γ:=Γ) (τ:=τ) (build_nil Γ τ) => build_nil _ _; *)
Dtm (Γ:=Γ) (τ:=τ) (build Γ τ m ta) =>
  build _ _ _ (Dtm ∘ ta);
Dtm (Γ:=Γ) (τ:=τ) (get Γ ti ta) => get _ ti (Dtm ta);
(* Nat *)
(* Dtm (Γ:=Γ) (τ:=τ) (nval Γ m) := nval _ m;
Dtm (Γ:=Γ) (τ:=τ) (nsucc Γ m) := nsucc _ (Dtm m);
Dtm (Γ:=Γ) (τ:=τ) (nrec Γ τ tf ti t) :=
  nrec _ _ (Dtm tf) (Dtm ti) (Dtm t); *)
(* Reals *)
Dtm (Γ:=Γ) (τ:=τ) (rval Γ r) :=
  tuple _ (rval _ r) (rval _ 0);
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
Dtm (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm p).
(* Sums *)
(* Dtm (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) := case _ (Dtm e) (Dtm c1) (Dtm c2);
Dtm (Γ:=Γ) (τ:=τ) (inl Γ _ _ e) := inl _ _ _ (Dtm e);
Dtm (Γ:=Γ) (τ:=τ) (inr Γ _ _ e) := inr _ _ _ (Dtm e). *)

(* For some arguments (ctx = x_1, ..., x_n : ⟦ repeat ℝ n ⟧ₜₓ) *)

Lemma correctness :
  forall τ m n ctx1 ctx2
  (vector_hot [] m F1)
    (t : tm (repeat ℝ n) ℝ) (ctx : ⟦ repeat ℝ n ⟧ₜₓ),
  snd (⟦ Dtm t ⟧ₜₘ ctx1) = (snd (⟦ Dtm_c m t ⟧ₜₘ ctx2)) 1.






























(* Definition lam_ctx τ : Ctx -> Ctx. *)

(* Definition ren_c Γ n :
  ren (map (Dt) Γ) (map (Dt_c n) Γ).
Proof with quick.
  unfold ren. intros τ v.
  dependent induction v.
  dependent destruction τ.
Admitted.

Equations? ren_c Γ n :
  ren (map (Dt) Γ) (map (Dt_c n) Γ) :=
ren_c nil n τ v with v := { };
ren_c (τ::Γ) n τ v := _.
Abort.

Definition ren_c' Γ n :
  ren (map (Dt_c n) Γ) (map (Dt) Γ).
Proof with quick.
  unfold ren.
Admitted.

Equations? ren_c' Γ n :
  ren (map (Dt_c n) Γ) (map (Dt) Γ) :=
ren_c' nil n τ v with v := { };
ren_c' (τ::Γ) n τ v := _.
Abort.

Lemma ren_ren' :
  forall Γ (τ : ty) (n : nat) (v : τ ∈ map (Dt_c n) Γ),
    ren_c Γ n τ (ren_c' Γ n τ v) = v.
Proof with quick.
  intros.
Admitted.

Lemma ren'_ren :
  forall Γ (τ : ty) (n : nat) (v : τ ∈ map (Dt) Γ),
    ren_c' Γ n τ (ren_c Γ n τ v) = v.
Proof with quick.
  intros.
Admitted. *)

(*
Lemma rename_ren'_ren :
  forall τ n m (t : tm (map (Dt) (repeat Real m)) (Dt τ)),
    rename (ren_c' n m) (rename (ren_c n m) t) = t.
Proof with quick.
  intros.
Admitted.

Lemma rename_ren_ren' :
  forall τ n m (t : tm (map (Dt_c n) (repeat Real m)) (Dt_c n τ)),
    rename (ren_c n m) (rename (ren_c' n m) t) = t.
Proof with quick.
  intros.
Admitted. *)

(* Equations lam {Γ n} τ
  (t : tm (map (Dt) Γ) (Dt τ))
  : tm (map (Dt_c n) Γ) (Dt_c n τ) := {
lam ℝ t := tuple _
  (first _ (rename (ren_c Γ n) t))
  (abs _ _ Real ((shift (σ:=Real) (second _ (rename (ren_c Γ n) t)))));
lam (τ1 × τ2) t
  := tuple _ (lam τ1 (first _ t)) (lam τ2 (second _ t));
lam (τ1 → τ2) t
  := abs (map (Dt_c n) Γ) (Dt_c n τ2) (Dt_c n τ1)
    (lam (Γ:=τ1::Γ) _ (app _ _ _ (shift t)
      (ev _ (var _ _ (Dv_c n (Top Γ _))))));
lam (Array m τ) t := build _ _ m (fun i => lam _ (get _ i t)) }
where ev {Γ n} τ (t : tm (map (Dt_c n) Γ) (Dt_c n τ))
  : tm (map (Dt) Γ) (Dt τ) :=
ev ℝ t := tuple _
  (first _ (rename (ren_c' Γ n) t))
  (app _ _ _ (second _ (rename (ren_c' Γ n) t)) (rval _ 1));
ev (τ1 × τ2) t
  := tuple _ (ev τ1 (first _ t)) (ev τ2 (second _ t));
ev (τ1 → τ2) t
  := abs (map (Dt) Γ) (Dt τ2) (Dt τ1)
    (ev (Γ:=τ1::Γ) _ (app _ _ _ (shift t)
      (lam _ (var _ _ (Dv (Top Γ _))))));
ev (Array m τ) t := build _ _ m (fun i => ev _ (get _ i t)). *)

(* lam (τ1 <+> τ2) z
  :=
  (* Transform sums by splitting the sum into its cases *)
  case (Dctx (repeat Real m)) z
    (* Build up back a new sum with the continuation macro's
      type for the left case using inl with a recursive call
      to lam *)
    (abs (map (Dt) (repeat ℝ m))
      (Dt_c n τ1 <+> Dt_c n τ2) (Dt_c n τ1)
      (inl (Dt τ1 :: map (Dt) (repeat ℝ m)) (Dt_c n τ1) (Dt_c n τ2)
        (lam τ1
        (* TODO: Problem, each branch in the case takes a function,
          hence the abs term above. I need to do a recursive call of lam
          on the argument which I can't due to lam only accepting ℝ
          as context *)
          (var (Dt τ1 :: map (Dt) (repeat ℝ m)) _ (Top _ _)))))
    (* Same for right case. *)
    (abs (map (Dt) (repeat ℝ m))
      (Dt_c n τ1 <+> Dt_c n τ2) (Dt_c n τ2)
      (inr (τ2 :: map (Dt) (repeat ℝ m)) _ _
        (lam τ2 (var _ _ (Top _ _))))). *)

(* Lemma four :
  forall Γ τ n (t : tm Γ τ),
  ⟦ev τ (lam τ (Dtm n t))⟧ₜₘ = ⟦ Dtm n t ⟧ₜₘ.
Proof with quick.
  intros. remember (Dtm n t) as t'.
  induction τ; quick; extensionality ctx; simp denote_tm.
  { rewrite <- denote_ren_commutes. simp lam. simp denote_tm...
    rewrite denote_ren_commutes.
    unfold shift... simp denote_tm.
    rewrite <- app_ren_ren.
    rewrite <- denote_ren_commutes. admit. }
  { unfold compose.
    simp lam.
    simp ev. admit. }
  all: admit.
Admitted. *)