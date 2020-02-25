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
Require Import Coquelicot.Derive.
Import EqNotations.

Require Import Definitions.
Require Import Macro.

Local Open Scope nat_scope.
Local Open Scope R_scope.

(*
  Goal: Write out the logical relation over types with the goal of having both
    the proof of differentiability and witness in one.

  Will piggyback on Coq's types
*)

Reserved Notation "⟦ T ⟧ₜ".
Fixpoint denote_t τ : Type :=
  match τ with
  | Real => R
  | τ1 × τ2 => ⟦τ1⟧ₜ * ⟦τ2⟧ₜ
  | τ1 → τ2 => ⟦τ1⟧ₜ -> ⟦τ2⟧ₜ
  end
where "⟦ T ⟧ₜ" := (denote_t T).

Reserved Notation "⟦ T ⟧ₜₓ".
Fixpoint denote_ctx (Γ : Ctx) : Type :=
  match Γ with
  | [] => unit
  | h :: t => ⟦h⟧ₜ * ⟦t⟧ₜₓ
  end
where "⟦ T ⟧ₜₓ" := (denote_ctx T).

Check snd.
Program Fixpoint denote_v {Γ τ} (v: τ ∈ Γ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ  :=
  match v with
  | Top Γ' τ' => fun gamma => fst gamma
  | Pop Γ' τ' σ x => fun gamma => denote_v x (snd gamma)
  end.
Notation "⟦ v ⟧ᵥ" := (denote_v v).

Reserved Notation "⟦ t ⟧ₜₘ".
Program Fixpoint denote_tm {Γ τ} (t : tm Γ τ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ :=
  match t with
  | var σ v => fun ctx => denote_v v ctx
  | app σ ρ t1 t2 => fun ctx => (⟦t1⟧ₜₘ ctx) (⟦t2⟧ₜₘ ctx)
  | abs σ ρ f => fun ctx => fun x => ⟦ f ⟧ₜₘ (x, ctx)

  | const r => fun ctx => r
  | add t1 t2 => fun ctx => ⟦t1⟧ₜₘ ctx + ⟦t2⟧ₜₘ ctx

  | tuple σ ρ t1 t2 => fun ctx => (⟦t1⟧ₜₘ ctx, ⟦t2⟧ₜₘ ctx)
  | first σ ρ t => fun ctx => fst (⟦t⟧ₜₘ ctx)
  | second σ ρ t => fun ctx => snd (⟦t⟧ₜₘ ctx)
  end
where "⟦ t ⟧ₜₘ" := (denote_tm t).
(* Compute ((denote_tm (Dtm ex_plus) tt) (1, 1) (1, 1)). *)

(* Defined in section 5 *)
Record Gl := make_gl {
  glτ : ty;
  glσ : ty;
  GlP : (R -> ⟦glτ⟧ₜ) -> (R -> ⟦glσ⟧ₜ) -> Prop;
}.

(*
  Prop translation of S in the proof of theorem 1 as an
    inductive definition
*)
Inductive Sprop : forall τ, (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop :=
  | s_r : Sprop Real id (fun r => (r, r))
  | s_prod : forall τ σ f1 f2 g1 g2,
      Sprop τ f1 f2 ->
      Sprop σ g1 g2 ->
      Sprop (τ × σ) (fun r => (f1 r, g1 r)) (fun r => (f2 r, g2 r))
  | s_arr : forall τ σ f1 f2 g1 g2 (s1 : Sprop τ g1 g2),
      Sprop σ (fun x => f1 x (g1 x)) (fun x => f2 x (g2 x)) ->
      Sprop (τ → σ) (fun r => f1 r) (fun r => f2 r)
.

(*
Record S := make_s {
  Sτ : ty;
  SP : (R -> ⟦Sτ⟧ₜ) -> (R -> ⟦Dt Sτ⟧ₜ) -> Prop;
}.

Definition interpret τ : S :=
  match τ with
  | Real => make_s Real (Sprop Real)
  | τ1 × τ2 => make_s (τ1 × τ2) (Sprop (τ1 × τ2))
  | τ1 → τ2 => make_s (τ1 → τ2) (Sprop (τ1 → τ2))
  end.
*)

Fixpoint S τ : (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop := Sprop τ.

Fixpoint denote_sub {Γ Γ'}: sub Γ' Γ -> denote_ctx Γ -> denote_ctx Γ' :=
  match Γ' with
  | [] => fun s ctx => tt
  | h :: t => fun s ctx =>
      (denote_tm (hd_sub s) ctx, denote_sub (tl_sub s) ctx)
  end.

Fixpoint denote_ren {Γ Γ'}: ren Γ' Γ -> denote_ctx Γ -> denote_ctx Γ' :=
  match Γ' with
  | [] => fun r ctx => tt
  | h :: t => fun r ctx =>
      (denote_tm (hd_ren r) ctx, denote_ren (tl_ren r) ctx)
  end.

Lemma den_sub_comm_abs :
  forall Γ Γ' τ σ (t : tm (σ :: Γ) τ) (s : sub Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    (forall (Γ' : Ctx) (s : sub (σ :: Γ) Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
      ⟦ t ⟧ₜₘ (denote_sub s ctx) = ⟦ substitute s t ⟧ₜₘ ctx) ->
    ⟦ abs Γ τ σ t ⟧ₜₘ (denote_sub s ctx) =
      ⟦ substitute s (abs Γ τ σ t) ⟧ₜₘ ctx.
Proof.
Admitted.

Lemma den_sub_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (s : sub Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (denote_sub s ctx) = ⟦substitute s t ⟧ₜₘ ctx.
Proof with eauto.
  intros. generalize dependent Γ'.
  induction t...
  { simpl. induction v...
    intros. simpl. rewrite IHv... }
  { simpl. intros.
    rewrite IHt1. rewrite IHt2... }
  { intros. apply den_sub_comm_abs... }
  { simpl. intros. rewrite IHt1. rewrite IHt2... }
  { simpl. intros. rewrite IHt1. rewrite IHt2... }
  { simpl. intros. rewrite IHt... }
  { simpl. intros. rewrite IHt... }
Qed.

(*
  Plain words:
    Given a context Γ for which t is well-typed (Γ ⊢ t : τ) and every typing
    assignment in the context is in the relation S, applying the substitutions
    in the context to the term t is also in the relation S.
*)
Lemma fundamental_lemma_id_sub :
  forall Γ τ
    (t : tm Γ τ)
    (ctx : ⟦ Γ ⟧ₜₓ)
    (dctx : ⟦ Dctx Γ ⟧ₜₓ),
  S τ (fun _ => ⟦ t ⟧ₜₘ ctx)
    (fun _ => ⟦ Dtm t ⟧ₜₘ dctx) ->
  S τ (fun _ => ⟦ substitute id_sub t ⟧ₜₘ ctx)
    (fun _ => ⟦ Dtm (substitute id_sub t) ⟧ₜₘ dctx).
Proof with eauto.
  induction τ; simpl; intros; erewrite app_sub_id...
Qed.

Lemma fundamental_lemma :
  forall Γ Γ' τ s
    (t : tm Γ τ)
    (ctx : ⟦ Γ ⟧ₜₓ)
    (dctx : ⟦ Dctx Γ ⟧ₜₓ)
    (ctx' : ⟦ Γ' ⟧ₜₓ)
    (dctx' : ⟦ Dctx Γ' ⟧ₜₓ),
  S τ (fun _ => ⟦ t ⟧ₜₘ ctx)
    (fun _ => ⟦ Dtm t ⟧ₜₘ dctx) ->
  S τ (fun _ => ⟦ substitute s t ⟧ₜₘ ctx')
    (fun _ => ⟦ Dtm (substitute s t) ⟧ₜₘ dctx').
Proof with eauto.

Admitted.

Theorem semantic_correct :
  forall Γ τ (t : tm Γ τ)
    (F : denote_ctx (Dctx Γ))
    (fs : denote_ctx Γ),
  ⟦ Dtm t ⟧ₜₘ F =
    (⟦ t ⟧ₜₘ fs, Derive (⟦ t ⟧ₜₘ fs)).
Proof.
Admitted.
