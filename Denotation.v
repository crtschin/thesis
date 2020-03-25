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

Require Import AD.Definitions.
Require Import AD.Macro.
Require Import AD.Tactics.
Require Import AD.Normalization.

Local Open Scope program_scope.
Local Open Scope R_scope.

(* Notations:

  ⟦ τ ⟧ₜ := denote_t τ, Currently piggybacks off of Coq's types.
  ⟦ Γ ⟧ₜₓ := denote_ctx Γ, A product list of types ensured to exist
                          in the context Γ.
  ⟦ v ⟧ₜₓ := denote_v v, A projection of the product list denoted by the typing
                        context relevant to the variable referenced by v
  ⟦ t ⟧ₜₘ := denote_tm t, Gives a function f of t such that it has the correct
                          denoted type of τ given the denoted context of Γ.
*)

(*
  Goal: Write out the logical relation over types with the goal of having both
    the proof of differentiability and witness in one.

  Will piggyback on Coq's types
*)
Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t τ : Set :=
  match τ with
  | Real => R
  | τ1 × τ2 => ⟦τ1⟧ₜ * ⟦τ2⟧ₜ
  | τ1 → τ2 => ⟦τ1⟧ₜ -> ⟦τ2⟧ₜ
  | τ1 <+> τ2 => ⟦τ1⟧ₜ + ⟦τ2⟧ₜ
  end
where "⟦ τ ⟧ₜ" := (denote_t τ).

Reserved Notation "⟦ Γ ⟧ₜₓ".
Fixpoint denote_ctx (Γ : Ctx) : Type :=
  match Γ with
  | [] => unit
  | h :: t => ⟦h⟧ₜ * ⟦t⟧ₜₓ
  end
where "⟦ Γ ⟧ₜₓ" := (denote_ctx Γ).

Fixpoint denote_v {Γ τ} (v: τ ∈ Γ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ  :=
  match v with
  | Top Γ' τ' => fun gamma => fst gamma
  | Pop Γ' τ' σ x => fun gamma => denote_v x (snd gamma)
  end.
Notation "⟦ v ⟧ᵥ" := (denote_v v).

Reserved Notation "⟦ t ⟧ₜₘ".
Fixpoint denote_tm {Γ τ} (t : tm Γ τ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ :=
  match t with
  | var σ v => fun ctx => denote_v v ctx
  | app σ ρ t1 t2 => fun ctx => (⟦t1⟧ₜₘ ctx) (⟦t2⟧ₜₘ ctx)
  | abs σ ρ f => fun ctx => fun x => ⟦ f ⟧ₜₘ (x, ctx)

  | const r => fun ctx => r
  | add t1 t2 => fun ctx => ⟦t1⟧ₜₘ ctx + ⟦t2⟧ₜₘ ctx

  | tuple σ ρ t1 t2 => fun ctx => (⟦t1⟧ₜₘ ctx, ⟦t2⟧ₜₘ ctx)
  | first σ ρ t => fun ctx => fst (⟦t⟧ₜₘ ctx)
  | second σ ρ t => fun ctx => snd (⟦t⟧ₜₘ ctx)

  | case τ σ ρ e c1 c2 => fun ctx =>
    match (⟦e⟧ₜₘ ctx) with
    | Datatypes.inl x => (⟦c1⟧ₜₘ ctx) x
    | Datatypes.inr x => (⟦c2⟧ₜₘ ctx) x
    end
  | inl τ σ e => fun ctx => Datatypes.inl (⟦e⟧ₜₘ ctx)
  | inr τ σ e => fun ctx => Datatypes.inr (⟦e⟧ₜₘ ctx)
  end
where "⟦ t ⟧ₜₘ" := (denote_tm t).


Equations denote_env {Γ} (G : Env Γ): ⟦ Γ ⟧ₜₓ :=
denote_env env_nil => tt;
denote_env (env_cons t G') with denote_env G' => {
  denote_env (env_cons t G') X => (⟦ t ⟧ₜₘ X, X)
}.
Notation "⟦ s ⟧ₑ" := (denote_env s).

Fixpoint denote_sub {Γ Γ'}: sub Γ Γ' -> denote_ctx Γ' -> denote_ctx Γ :=
  match Γ with
  | [] => fun s ctx => tt
  | h :: t => fun s ctx =>
      (denote_tm (hd_sub s) ctx, denote_sub (tl_sub s) ctx)
  end.
Notation "⟦ s ⟧ₛ" := (denote_sub s).

Fixpoint denote_ren {Γ Γ'}: ren Γ Γ' -> denote_ctx Γ' -> denote_ctx Γ :=
  match Γ with
  | [] => fun r ctx => tt
  | h :: t => fun r ctx =>
      (denote_tm (hd_ren r) ctx, denote_ren (tl_ren r) ctx)
  end.
Notation "⟦ r ⟧ᵣ" := (denote_ren r).

(* Lemmas for renaming and substitution in the denotated context. *)
(* Many from Strongly Typed Terms in Coq by Nick Becton, et al. *)
Lemma denote_ren_tl_lift : forall Γ Γ' τ
  (r : ren Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  denote_ren r ctx = denote_ren (tl_ren (rename_lifted r)) (x, ctx).
Proof with eauto.
  induction Γ...
  intros. specialize IHΓ with (r:=tl_ren r).
  simpl. rewrite IHΓ with (x:=x)...
Qed.

Lemma denote_ren_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (r : ren Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (denote_ren r ctx) = ⟦ rename r t ⟧ₜₘ ctx.
Proof with quick.
  intros. generalize dependent Γ'.
  induction t; quick; rewrites...
  { induction v... rewrite IHv... }
  { specialize IHt with (r:=rename_lifted r).
    simpl in IHt. simp rename_lifted in IHt.
    apply functional_extensionality...
    rewrite <- IHt...
    rewrite <- denote_ren_tl_lift... }
Qed.

Lemma denote_ren_shift : forall Γ Γ' τ (r:ren Γ Γ'),
  denote_ren (fun _ v => Pop _ _ τ (r _ v)) =
    fun se => denote_ren r (snd se).
Proof with quick.
  induction Γ... extensionality ctx.
  apply injective_projections...
  unfold tl_ren. rewrite IHΓ...
Qed.

Lemma denote_ren_id : forall Γ,
  denote_ren (@id_ren Γ) = Datatypes.id.
Proof with quick.
  intros. extensionality x.
  dependent induction Γ... destruct x...
  destruct x...
  apply injective_projections...
  unfold tl_ren, id_ren in *...
  rewrite denote_ren_shift...
Qed.

Lemma denote_shift : forall Γ τ σ (t : tm Γ τ) ctx,
    ⟦ shift (σ:=σ) t ⟧ₜₘ ctx = ⟦ t ⟧ₜₘ (snd ctx).
Proof with eauto.
  unfold shift. intros.
  rewrite <- denote_ren_commutes...
  pose proof denote_ren_tl_lift as H.
  destruct ctx as [x ctx].
  specialize H with Γ Γ σ (fun t x => x) x ctx.
  unfold tl_ren in H.
  assert (H':
    (fun (σ0 : ty) (x : σ0 ∈ Γ) =>
       rename_lifted (fun (t : ty) (x0 : t ∈ Γ) => x0) σ0 (Pop Γ σ0 σ x)) =
    (fun (ρ : ty) (x0 : ρ ∈ Γ) => Pop Γ ρ σ x0)).
  { apply functional_extensionality_dep... }
  rewrite <- H'. rewrite <- H.
  fold (@id_ren Γ). rewrite denote_ren_commutes.
  rewrite app_ren_id...
Qed.

Lemma denote_sub_elim : forall Γ Γ' τ
  (s : sub Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  denote_sub s ctx = denote_sub (tl_sub (substitute_lifted s)) (x, ctx).
Proof with eauto.
  induction Γ; intros...
  intros. specialize IHΓ with (s := (tl_sub s)).
  simpl. rewrite IHΓ with (x := x).
  unfold hd_sub. unfold tl_sub. simp substitute_lifted.
  erewrite denote_shift...
Qed.

Lemma denote_sub_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (s : sub Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (denote_sub s ctx) = ⟦ substitute s t ⟧ₜₘ ctx.
Proof with quick.
  intros. generalize dependent Γ'.
  induction t; intros; rewrites...
  { simpl. induction v...
    intros. simpl. rewrite IHv... }
  { specialize IHt with (s:=substitute_lifted s)...
    apply functional_extensionality...
    rewrite <- IHt...
    erewrite denote_sub_elim... }
Qed.

Lemma denote_sub_id : forall Γ τ (t : tm Γ τ) (ctx : ⟦ Γ ⟧ₜₓ),
  ⟦ t ⟧ₜₘ (denote_sub id_sub ctx) = ⟦ t ⟧ₜₘ ctx.
Proof with quick.
  intros.
  rewrite denote_sub_commutes...
  rewrite app_sub_id...
Qed.

Lemma denote_sub_shift : forall Γ Γ' σ (s:sub Γ Γ'),
  denote_sub (fun _ v => shift (σ:=σ) (s _ v)) =
    fun ctx => denote_sub s (snd ctx).
Proof with quick.
  induction Γ... extensionality ctx.
  apply injective_projections...
  { unfold hd_sub. rewrite denote_shift... }
  { unfold tl_sub. rewrite IHΓ... }
Qed.

Lemma denote_sub_tl_simpl : forall Γ Γ' τ (ctx : ⟦ Γ' ⟧ₜₓ) (s : sub (τ::Γ) Γ'),
  ⟦ tl_sub s ⟧ₛ ctx = snd (⟦ s ⟧ₛ ctx).
Proof with quick.
  intros...
Qed.

Lemma denote_sub_id_ctx : forall Γ (ctx : ⟦Γ⟧ₜₓ),
  denote_sub id_sub ctx = ctx.
Proof with quick.
  induction Γ.
  { simpl denote_sub. destruct ctx... }
  { simpl denote_sub. destruct ctx...
    apply injective_projections...
    rewrite denote_sub_tl_simpl.
    (* eapply IHΓ. *)
    assert (⟦ @id_sub (a::Γ) ⟧ₛ (d, d0) = (d, d0)).
    { rewrites. admit. }
    rewrite H... }
Admitted.

Lemma denote_sub_tl_snd : forall Γ τ ctx,
  ⟦ tl_sub (Γ:=Γ) (τ:=τ) id_sub ⟧ₛ ctx = snd ctx.
Proof with quick.
  (* pose proof (tl_sub (Γ:=Γ) (τ:=τ) id_sub). *)
  induction Γ...
  { destruct ctx... destruct u... }
  { destruct ctx...
    destruct p... apply injective_projections...
    rewrite denote_sub_tl_simpl.
    rewrite denote_sub_tl_simpl.
    rewrite denote_sub_id_ctx... }
Admitted.

Lemma denote_sub_tl_cons : forall Γ τ (t : tm Γ τ) ctx,
  denote_sub (tl_sub (|t|)) ctx = ctx.
Proof with quick.
  intros.
  unfold id_sub.
  rewrite tl_cons_sub.
  fold (@id_sub Γ).
  rewrite denote_sub_id_ctx...
Admitted.

Theorem soundness : forall τ (t t' : tm [] τ),
  (t -->* t') -> ⟦t⟧ₜₘ = ⟦t'⟧ₜₘ.
Proof with quick.
  intros.
  induction H...
  rewrite <- IHmulti.
  dependent induction H;
    extensionality ctx; quick;
    try (erewrite IHstep; constructor)...
  { rewrite <- denote_sub_commutes...
    unfold hd_sub. simp cons_sub.
    destruct ctx... }
  { erewrite <- (IHstep t2 t2' t2')...
    constructor. }
Qed.

Lemma D_value : forall Γ τ (t : tm Γ τ),
  value t -> value (Dtm t).
Proof.
  intros. induction H; simp Dtm; constructor;
    try (constructor || assumption).
Qed.

Lemma D_step : forall Γ τ (t t' : tm Γ τ),
  (* value t' -> *)
  (t -->* t') -> Dtm t -->* Dtm t'.
Proof with quick.
  intros Γ τ t t' H.
  induction H... constructor.
  induction H.
  { simp Dtm. fold (map Dt) Dt.
    pose proof (D_value _ _ _ H).
    eapply multi_step.
    apply ST_AppAbs...
    eapply multi_trans...
    admit. }
  { simp Dtm. fold map Dt.
    specialize IHstep with t1'.
    eapply multi_trans...
    simp Dtm. fold map Dt.
    eapply multi_trans...
    apply multistep_App1.
    apply IHstep.
    all: constructor. }
  { simp Dtm. fold map Dt.
    specialize IHstep with t2'...
    eapply multi_trans...
    simp Dtm. fold map Dt.
    eapply multi_trans...
    apply multistep_App2.
    apply D_value in H...
    apply IHstep.
    all: constructor. }
  { simp Dtm. fold map Dt.
    eapply multi_trans...
    simp Dtm.
    eapply multi_trans.
    apply multistep_Tuple1.
    eapply multi_trans.
    apply multistep_Add1.
    apply multistep_FirstTuple...
    apply multistep_Add2...
    apply multistep_FirstTuple...
    eapply multi_trans.
    apply multistep_Tuple1.
    pose proof multistep_Add as H.
    specialize H with (map Dt Γ) v1 v2.
    pose proof (H v_real v_real)...
    eapply multi_trans.
    apply multistep_Tuple2...
    eapply multi_trans.
    apply multistep_Add1...
    apply multistep_SecondTuple...
    apply multistep_Add2...
    apply multistep_SecondTuple...
    eapply multi_trans.
    apply multistep_Tuple2...
    apply multistep_Add...
    rewrite Rplus_0_r.
    constructor. }
  { simp Dtm.
    specialize IHstep with t1'.
    eapply multi_trans...
    simp Dtm.
    eapply multi_trans...
    apply multistep_Tuple1.
    apply multistep_Add1.
    apply multistep_First.
    apply IHstep. constructor.
    constructor.
    eapply multi_trans...
    apply multistep_Tuple2.
    admit.
    apply multistep_Add1.
    apply multistep_Second.
    apply IHstep. constructor.
    constructor. constructor. }
    (* apply multistep_Add.
    apply multistep_First.
    apply IHstep. constructor.
    constructor.
    all: constructor. }

    apply multistep_App1.
    apply IHstep.
     } *)
  all: admit.
Admitted.


Theorem D_soundness : forall Γ τ (t t' : tm Γ τ),
  (Dtm t -->* Dtm t') -> ⟦Dtm t⟧ₜₘ = ⟦Dtm t'⟧ₜₘ.
Proof with quick.
  intros.
  induction H...
  rewrite <- IHmulti.
  dependent induction H;
    extensionality ctx;
    try (erewrite IHstep; constructor).
  { simp Dtm. fold map Dt. simpl.
    rewrite <- denote_sub_commutes...
    unfold hd_sub. simp cons_sub.
    rewrite denote_sub_tl_cons... }
  all: admit.
Admitted.
