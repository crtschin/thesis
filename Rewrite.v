Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Vector.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Reals.

Local Open Scope program_scope.

From Equations Require Import Equations.
From AD Require Import Tactics.
From AD Require Import Definitions.
From AD Require Import Normalization.
From AD Require Import Macro.
From AD Require Import Denotation.

Equations shift_var {Γ : list ty} {τ σ ρ : ty}
  : τ ∈ σ :: Γ -> τ ∈ σ :: ρ :: Γ :=
shift_var (Top Γ τ) := Top (ρ::Γ) τ;
shift_var (Pop Γ τ σ v) := Pop (ρ::Γ) τ σ (Pop Γ τ ρ v).

Definition shift2 {Γ τ σ ρ} (t : tm (σ::Γ) τ) : tm (σ::ρ::Γ) τ
  := substitute (fun τ x => var (σ::ρ::Γ) τ (shift_var x)) t.

Reserved Notation "t ~> s" (at level 30).
Inductive rwrt : forall {Γ τ}, tm Γ τ -> tm Γ τ -> Prop :=
  | RW_Id : forall Γ τ (t: tm Γ τ),
    t ~> t
  (* Inherit normalization rules from stepping relation *)
  | RW_Mstep : forall Γ τ (t t': tm Γ τ),
    t -->* t' ->
    t ~> t'
  (* Function PE *)
  | RW_Abs : forall Γ τ σ (t t': tm (σ::Γ) τ),
    t ~> t' ->
    abs _ _ _ t ~> abs _ _ _ t'
  (* Tuple PE *)
  | RW_Tuple : forall Γ τ σ (t1 t1': tm Γ τ) (t2 t2': tm Γ σ),
    t1 ~> t1' ->
    t2 ~> t2' ->
    tuple _ t1 t2 ~> tuple _ t1' t2'
  | RW_First : forall Γ τ σ (t1: tm Γ τ) (t2: tm Γ σ),
    first _ (tuple _ t1 t2) ~> t1
  | RW_Second : forall Γ τ σ (t1: tm Γ τ) (t2: tm Γ σ),
    second _ (tuple _ t1 t2) ~> t2
  (* Loop Fusion *)
  | RW_BuildGet : forall Γ τ n (i : Fin.t n) (f : Fin.t n -> tm Γ τ),
    get Γ i (build Γ τ n f) ~> f i
  (* Loop Fission *)
  | RW_IFoldTuple :
    forall Γ τ σ ti
      (tf1 : tm Γ (ℕ → τ → τ)) (tf2 : tm Γ (ℕ → σ → σ))
      (z0 : tm Γ τ) (z1 : tm Γ σ),
    ifold (abs Γ (τ × σ → τ × σ) ℕ (abs (ℕ::Γ) (τ × σ) (τ × σ) (
      (tuple ((τ×σ)::ℕ::Γ)
        (app _ _ _
          (app _ _ _ (shift (shift tf1))
            (var _ _ (Pop _ _ _ (Top _ _))))
          (first _ (var _ _ (Top _ _))))
        (app _ _ _
          (app _ _ _ (shift (shift tf2))
            (var _ _ (Pop _ _ _ (Top _ _))))
          (second _ (var _ _ (Top _ _))))))))
      ti (tuple _ z0 z1) ~> tuple _ (ifold tf1 ti z0) (ifold tf2 ti z1)
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
  (* Ring addition *)
  | RW_add : forall Γ (t1 t1' t2 t2' : tm Γ ℝ),
    t1 ~> t1' ->
    t2 ~> t2' ->
    add _ t1 t2 ~> add _ t1' t2'
  | RW_add0L : forall Γ (t2 t2': tm Γ ℝ),
    t2 ~> t2' ->
    add _ (rval _ 0) t2 ~> t2
  | RW_add0R : forall Γ (t1 t1': tm Γ ℝ),
    t1 ~> t1' ->
    add _ t1 (rval _ 0) ~> t1
  | RW_add_R : forall Γ r (t1 t2: tm Γ ℝ),
    t1 ~> rval Γ r ->
    t2 ~> rval Γ (-r) ->
    add Γ t1 t2 ~> rval Γ 0
  | RW_add_L : forall Γ r (t1 t2: tm Γ ℝ),
    t1 ~> rval Γ (-r) ->
    t2 ~> rval Γ r ->
    add Γ t1 t2 ~> rval Γ 0
where "t ~> s" := (rwrt t s).

Lemma shift2_snd :
  forall Γ τ σ ρ (t : tm (σ::Γ) τ) (x : ⟦ σ ⟧ₜ) (y : ⟦ ρ ⟧ₜ) (ctx : ⟦ Γ ⟧ₜₓ),
  ⟦ t ⟧ₜₘ (x, ctx) = ⟦ shift2 t ⟧ₜₘ (x, (y, ctx)).
Proof with quick.
  intros.
  unfold shift2.
  rewrite <- denote_sub_commutes.
  simpl.
  unfold hd_sub. simp shift_var. simp denote_tm...
  unfold tl_sub.
  assert (H:
    (fun φ (x : φ ∈ Γ) =>
      var (σ :: ρ :: Γ) φ (shift_var (Pop Γ φ σ x))) =
    tl_sub (tl_sub (fun φ (x : φ ∈ σ :: ρ :: Γ) =>
      var (σ :: ρ :: Γ) φ x))).
  { extensionality φ. extensionality v. now simp shift_var. }
  rewrite_c H.
  assert (H: (fun (σ0 : ty) (x0 : σ0 ∈ σ :: ρ :: Γ) => var (σ :: ρ :: Γ) σ0 x0)
    = id_sub (Γ:=σ::ρ::Γ))...
  rewrite_c H.
  rewrite 2 denote_sub_tl_simpl.
  rewrite denote_sub_id_ctx...
Qed.

Lemma rewrite_soundness : forall Γ τ (t t' : tm Γ τ),
  t ~> t' -> ⟦ t ⟧ₜₘ = ⟦ t' ⟧ₜₘ.
Proof with quick.
  intros.
  dependent induction H; quick;
    try solve [extensionality ctx; simp denote_tm; rewrites; trivial]...
  { apply soundness... }
  all: extensionality ctx; simp denote_tm; rewrites.
  { unfold compose. induction i...
    { induction n... }
    { unfold shave_fin. rewrite IHi... } }
  { unfold ifold. simp denote_tm.
    induction (⟦ ti ⟧ₜₘ ctx)...
    rewrite_c IHd...
    rewrite 3 denote_shift...
    simp denote_tm...
    rewrite 4 denote_shift... }
  { unfold letin.
    simp denote_tm.
    erewrite <- shift2_snd... }
  { unfold letin.
    simp denote_tm.
    erewrite 2 denote_shift... }
  { apply Rplus_0_l. }
  { rewrite Rplus_comm.
    apply Rplus_0_l. }
  { apply Rplus_opp_r. }
  { rewrite Rplus_comm.
    apply Rplus_opp_r. }
Qed.
