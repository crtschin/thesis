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

Require Import AD.Definitions.
Require Import AD.Macro.

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
Compute ((denote_tm (Dtm ex_plus) tt) (1, 1) (0, 0)).

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
Inductive GlProp : forall τ σ, (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ σ ⟧ₜ) -> Prop :=
  | s_r : forall f,
      GlProp Real (Dt Real) f (fun r => (f r, Derive f r))
  | s_prod : forall τ σ f1 f2 g1 g2,
      GlProp τ (Dt τ) f1 f2 ->
      GlProp σ (Dt σ) g1 g2 ->
      GlProp (τ × σ) (Dt (τ × σ)) (fun r => (f1 r, g1 r)) (fun r => (f2 r, g2 r))
  | s_arr : forall τ σ f1 f2 g1 g2 (s1 : GlProp τ (Dt τ) g1 g2),
      GlProp σ (Dt σ) (fun x => f1 x (g1 x)) (fun x => f2 x (g2 x)) ->
      GlProp (τ → σ) (Dt (τ → σ))(fun r => f1 r) (fun r => f2 r)
.

Fixpoint S τ : (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop
  := GlProp τ (Dt τ).

Record St := make_s {
  carrier : ty;
  SP : (R -> ⟦carrier⟧ₜ) -> (R -> ⟦Dt carrier⟧ₜ) -> Prop;
}.

Definition interpret τ : St :=
  match τ with
  | Real => make_s Real (GlProp Real (Dt Real))
  | τ1 × τ2 => make_s (τ1 × τ2) (GlProp (τ1 × τ2) (Dt (τ1 × τ2)))
  | τ1 → τ2 => make_s (τ1 → τ2) (GlProp (τ1 → τ2) (Dt (τ1 → τ2)))
  end.

Fixpoint denote_sub {Γ Γ'}: sub Γ Γ' -> denote_ctx Γ' -> denote_ctx Γ :=
  match Γ with
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

Lemma denote_ren_elim : forall Γ Γ' τ
  (r : ren Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  denote_ren r ctx = denote_ren (tl_ren (rename_lifted r)) (x, ctx).
Proof with eauto.
    intros. unfold tl_ren. simpl.
  Admitted.

Lemma denote_ren_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (r : ren Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (denote_ren r ctx) = ⟦rename r t ⟧ₜₘ ctx.
Proof with eauto.
  intros. generalize dependent Γ'.
  induction t; intros...
  { simpl. induction v...
    intros. simpl. rewrite IHv... }
  { simpl. rewrite IHt1. rewrite IHt2... }
  { specialize IHt with (r:=rename_lifted r).
    simpl in IHt. rewrite -> rename_abs.
    simpl. apply functional_extensionality.
    intros. rewrite <- IHt. simpl.
    rewrite <- denote_ren_elim... }
  { simpl. rewrite IHt1. rewrite IHt2... }
  { simpl. rewrite IHt1. rewrite IHt2... }
  { simpl. rewrite IHt... }
  { simpl. rewrite IHt... }
Qed.

Lemma denote_sub_elim : forall Γ Γ' τ
  (s : sub Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  denote_sub s ctx = denote_sub (tl_sub (substitute_lifted s)) (x, ctx).
Proof with eauto.
  intros. unfold tl_sub. simpl.
Admitted.

Lemma denote_sub_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (s : sub Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (denote_sub s ctx) = ⟦substitute s t ⟧ₜₘ ctx.
Proof with eauto.
  intros. generalize dependent Γ'.
  induction t; intros...
  { simpl. induction v...
    intros. simpl. rewrite IHv... }
  { simpl. rewrite IHt1. rewrite IHt2... }
  { specialize IHt with (s:=substitute_lifted s).
    simpl in IHt. rewrite -> substitute_abs.
    simpl. apply functional_extensionality.
    intros. rewrite <- IHt. simpl.
    erewrite denote_sub_elim... }
  { simpl. rewrite IHt1. rewrite IHt2... }
  { simpl. rewrite IHt1. rewrite IHt2... }
  { simpl. rewrite IHt... }
  { simpl. rewrite IHt... }
Qed.

Definition Dsub {Γ Γ'} : sub Γ Γ' -> sub (Dctx Γ) (Dctx Γ').
  Admitted.

Lemma Dsub_step :
  forall Γ Γ' τ (t : tm Γ τ)
    (s : sub Γ Γ') (ctx : ⟦ Dctx Γ' ⟧ₜₓ),
  ⟦ Dtm (substitute s t) ⟧ₜₘ ctx
    = ⟦ substitute (Dsub s) (Dtm t) ⟧ₜₘ ctx.
Admitted.

Lemma D_denote_substitute : forall
  Γ Γ' τ (s: sub Γ Γ')
  (t: tm Γ τ) (dctx : ⟦ Dctx Γ' ⟧ₜₓ),
    ⟦ Dtm t ⟧ₜₘ (denote_sub (Dsub s) dctx) = ⟦ Dtm (substitute s t) ⟧ₜₘ dctx.
Proof.
Admitted.


(*
  Plain words:
    Given a context Γ for which t is well-typed (Γ ⊢ t : τ) and every typing
    assignment in the context is in the relation S, applying the substitutions
    in the context to the term t is also in the relation S.
*)
(* Lemma fundamental_lemma_closed :
  forall Γ τ
    env Γ -> *)

Lemma S_eq {τ f f'} (s : S τ f f') g g':
  f = g -> f' = g' ->
  S τ g g'.
Proof with eauto.
  intros. subst...
Qed.

Lemma fundamental_lemma :
  forall Γ Γ' τ s
    (t : tm Γ τ)
    (ctx : ⟦ Γ' ⟧ₜₓ)
    (dctx : ⟦ Dctx Γ' ⟧ₜₓ),
  S τ (fun _ => ⟦ t ⟧ₜₘ (denote_sub s ctx))
    (fun _ => ⟦ Dtm t ⟧ₜₘ (denote_sub (Dsub s) dctx)) ->
  S τ (fun _ => ⟦ substitute s t ⟧ₜₘ ctx)
    (fun _ => ⟦ Dtm (substitute s t) ⟧ₜₘ dctx).
Proof with eauto.
  induction τ; intros;
    try (apply (S_eq H); apply functional_extensionality; intros;
    apply denote_sub_commutes).
  { rewrite Dsub_step. admit. }
  { rewrite Dsub_step. admit. }
  { rewrite Dsub_step. admit. }
Admitted.

Theorem semantic_correct :
  forall Γ τ (t : tm Γ τ)
    (F : denote_ctx (Dctx Γ))
    (fs : denote_ctx Γ),
  ⟦ Dtm t ⟧ₜₘ F =
    (⟦ t ⟧ₜₘ fs, Derive (⟦ t ⟧ₜₘ fs)).
Proof.
Admitted.
