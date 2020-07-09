Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Vector.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import Reals.

Local Open Scope program_scope.

From Equations Require Import Equations.
From AD Require Import DepList.
From AD Require Import Tactics.
From AD Require Import Definitions.
From AD Require Import Natural.
From AD Require Import Macro.
From AD Require Import Denotation.

Equations shift_var {Γ : list ty} {τ σ ρ : ty}
  : τ ∈ σ :: Γ -> τ ∈ σ :: ρ :: Γ :=
shift_var (Top Γ τ) := Top (ρ::Γ) τ;
shift_var (Pop Γ τ σ v) := Pop (ρ::Γ) τ σ (Pop Γ τ ρ v).

Equations swap_var {Γ : list ty} {τ σ ρ : ty}
  : τ ∈ ρ :: σ :: Γ -> τ ∈ σ :: ρ :: Γ :=
swap_var (Top Γ τ) := Pop _ _ _ (Top _ _);
swap_var (Pop Γ τ σ v) := shift_var v.

Definition shift2 {Γ τ σ ρ} (t : tm (σ::Γ) τ) : tm (σ::ρ::Γ) τ
  := substitute (fun τ x => var (σ::ρ::Γ) τ (shift_var x)) t.

Definition swap {Γ τ σ ρ} (t : tm (ρ::σ::Γ) τ) : tm (σ::ρ::Γ) τ
  := substitute (fun τ x => var (σ::ρ::Γ) τ (swap_var x)) t.

Reserved Notation "t ~> s" (at level 30).
Inductive rwrt : forall {Γ τ}, tm Γ τ -> tm Γ τ -> Prop :=
  (* Inherit normalization rules from stepping relation *)
  | RW_Mstep : forall Γ τ (t t': tm Γ τ),
    t ⇓ t' ->
    t ~> t'
  (* Function PE *)
  | RW_Abs : forall Γ τ σ (t t': tm (σ::Γ) τ),
    t ~> t' ->
    abs _ _ _ t ~> abs _ _ _ t'
  (* Deforestation *)
  | RW_LpFusion : forall Γ τ n (i : Fin.t n) (f : Fin.t n -> tm Γ τ),
    get Γ i (build Γ τ n f) ~> f i
  (* Loop Fission *)
  | RW_LpFission : forall Γ τ σ ti
      (tf0 : tm Γ (ℕ → τ → τ)) (tf1 : tm Γ (ℕ → σ → σ))
      (z0 : tm Γ τ) (z1 : tm Γ σ),
    ifold (abs Γ (τ × σ → τ × σ) ℕ (abs (ℕ::Γ) (τ × σ) (τ × σ) (
      (tuple ((τ×σ)::ℕ::Γ)
        (app _ _ _
          (app _ _ _ (shift (shift tf0))
            (var _ _ (Pop _ _ _ (Top _ _))))
          (first _ (var _ _ (Top _ _))))
        (app _ _ _
          (app _ _ _ (shift (shift tf1))
            (var _ _ (Pop _ _ _ (Top _ _))))
          (second _ (var _ _ (Top _ _))))))))
      ti (tuple _ z0 z1) ~> tuple _ (ifold tf0 ti z0) (ifold tf1 ti z1)
  (* Lets *)
  | RW_LetDesugar : forall Γ τ σ (t1: tm (σ::Γ) τ) (t2: tm Γ σ),
    app _ _ _ (abs _ _ _ t1) t2 ~> letin t2 t1
  | RW_LetAssoc : forall Γ τ σ ρ
    (e0: tm Γ τ) (e1: tm (τ::Γ) σ) (e2: tm (σ::Γ) ρ),
      letin (letin e0 e1) e2 ~>
        letin e0 (letin e1 (shift2 e2))
  | RW_LetDupl : forall Γ τ σ
    (e0: tm Γ τ) (e1: tm (τ::Γ) σ),
    letin e0 (shift (letin e0 e1)) ~>
      letin e0 (letin (var _ _ (Top _ _)) (shift e1))
  | RW_LetDisj : forall Γ τ σ ρ
    (e0: tm Γ τ) (e1: tm Γ σ) (e2 : tm (τ::σ::Γ) ρ),
    letin e0 (letin (shift e1) (swap e2)) ~>
      letin e1 (letin (shift e0) e2)
  (* Ring operations *)
  | RW_add_comm : forall Γ (t1 t2 : tm Γ ℝ),
    add _ t1 t2 ~> add _ t2 t1
  | RW_add_0 : forall Γ (t2: tm Γ ℝ),
    add _ (rval _ 0) t2 ~> t2
  | RW_add_neg : forall Γ r,
    add Γ (rval Γ (-r)) (rval Γ r) ~> rval Γ 0
  | RW_mul_comm : forall Γ (t1 t2: tm Γ ℝ),
    mul _ t1 t2 ~> mul _ t2 t1
  | RW_mul_distr : forall Γ (t t1 t2: tm Γ ℝ),
    add Γ (mul Γ t t1) (mul Γ t t2) ~> mul Γ t (add Γ t1 t2)
  | RW_mul_0 : forall Γ (t2: tm Γ ℝ),
    mul _ (rval _ 0) t2 ~> rval _ 0
  | RW_mul_1 : forall Γ (t2: tm Γ ℝ),
    mul _ (rval _ 1) t2 ~> t2
where "t ~> s" := (rwrt t s).

Lemma denote_shift2 :
  forall Γ τ σ ρ (t : tm (σ::Γ) τ) (x : ⟦ σ ⟧ₜ) (y : ⟦ ρ ⟧ₜ) (ctx : ⟦ Γ ⟧ₜₓ),
  ⟦ t ⟧ₜₘ (x ::: ctx) = ⟦ shift2 t ⟧ₜₘ (x ::: y ::: ctx).
Proof with quick.
  intros.
  unfold shift2.
  rewrite <- denote_sub_commutes...
  unfold hd_sub, tl_sub. simp shift_var denote_tm...
  assert (H:
    (fun φ x => var (σ::ρ::Γ) φ (shift_var (Pop Γ φ σ x))) =
      tl_sub (tl_sub (id_sub (Γ:=σ::ρ::Γ)))).
  { extensionality φ. extensionality v. now simp shift_var. }
  rewrite_c H.
  rewrite 2 denote_sub_tl_simpl.
  rewrite denote_sub_id_ctx...
Qed.

Lemma denote_swap :
  forall Γ τ σ ρ ctx
    (e0: tm Γ τ) (e1: tm Γ σ) (e2 : tm (τ::σ::Γ) ρ),
  ⟦ swap e2 ⟧ₜₘ
    (⟦ shift e1 ⟧ₜₘ (⟦ e0 ⟧ₜₘ ctx ::: ctx) ::: ⟦ e0 ⟧ₜₘ ctx ::: ctx) =
  ⟦ e2 ⟧ₜₘ
    (⟦ shift e0 ⟧ₜₘ (⟦ e1 ⟧ₜₘ ctx ::: ctx) ::: ⟦ e1 ⟧ₜₘ ctx ::: ctx).
Proof with quick.
  intros. unfold swap.
  rewrite <- denote_sub_commutes...
  rewrite 2 denote_shift...
  unfold hd_sub, tl_sub.
  simp denote_tm swap_var shift_var...
  eassert (H': (fun ρ x =>
    var _ ρ (swap_var (Pop (σ :: Γ) ρ τ (Pop Γ ρ σ x))))
      = tl_sub (tl_sub id_sub)).
  { extensionality φ. extensionality v.
    now simp swap_var shift_var. }
  rewrite_c H'.
  rewrite 2 denote_sub_tl_simpl.
  rewrite denote_sub_id_ctx...
Qed.

Lemma rewrite_soundness : forall Γ τ (t t' : tm Γ τ),
  t ~> t' -> ⟦ t ⟧ₜₘ = ⟦ t' ⟧ₜₘ.
Proof with quick.
  intros.
  dependent induction H; quick;
    try solve [extensionality ctx; simp denote_tm; rewrites; trivial]...
  { apply natural_soundness... }
  all: extensionality ctx; simp denote_tm; rewrites.
  { apply denote_loop_fusion... }
  (* { unfold vector_map; unfold tm_compose.
    simp denote_tm; unfold compose.
    erewrite denote_array_eq... clear ctx.
    extensionality i; extensionality ctx.
    simp denote_tm; unfold compose.
    simp denote_v; repeat rewrite denote_shift...
    rewrite denote_loop_fusion... } *)
  { unfold ifold. simp denote_tm.
    induction (⟦ ti ⟧ₜₘ ctx)...
    rewrite_c IHd...
    rewrite 3 denote_shift...
    simp denote_tm...
    rewrite 4 denote_shift. simpl.
    simp denote_v. simpl.
    reflexivity. }
  { unfold letin.
    simp denote_tm.
    erewrite <- denote_shift2... }
  { unfold letin.
    simp denote_tm.
    erewrite 2 denote_shift... }
  { unfold letin.
    simp denote_tm.
    rewrite denote_swap... }
  { rewrite Rplus_comm... }
  { apply Rplus_0_l. }
  { apply Rplus_opp_l. }
  { rewrite Rmult_comm... }
  { rewrite Rmult_plus_distr_l... }
  { rewrite Rmult_0_l... }
  { rewrite Rmult_1_l... }
Qed.
