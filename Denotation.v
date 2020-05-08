Require Import Lists.List.
Require Import Vectors.Fin.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Coquelicot.Derive.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Equations.Equations.
Import EqNotations.

Require Import CoLoR.Util.Vector.VecUtil.
Require Import AD.Definitions.
Require Import AD.Macro.
(* Require AD.DepList. *)
Require Import AD.Tactics.
Require Import AD.vect.

Local Open Scope program_scope.

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
*)

Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t τ : Set :=
  match τ with
  | Real => R
  | Nat => nat
  | Array n τ => vector ⟦ τ ⟧ₜ n
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

Fixpoint vector_nth {s : Set} {n}
  (i : Fin.t n) : vector s n -> s :=
  match i with
  | @F1 _    => fun ar => Vhead ar
  | @FS _ i' => fun ar => vector_nth i' (Vtail ar)
  end.

Fixpoint nat_to_fin n : Fin.t (S n) :=
  match n with
  | 0 => F1
  | S n' => F1
  end.

Definition shave_fin {A n} (f : Fin.t (S n) -> A) : Fin.t n -> A :=
  fun i => f (FS i).

Fixpoint loop_down {A} (n : nat) (f : A -> A) (a : A) :=
  match n with
  | 0 => a
  | S n => f (loop_down n f a)
  end.

Reserved Notation "⟦ t ⟧ₜₘ".
Equations denote_tm {Γ τ} (t : tm Γ τ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ by struct t := {
(* STLC *)
denote_tm (Γ:=Γ) (τ:=τ) (var Γ τ v) ctx := denote_v v ctx;
denote_tm (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) ctx := (⟦t1⟧ₜₘ ctx) (⟦t2⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) ctx := fun x => ⟦ f ⟧ₜₘ (x, ctx);
(* Arrays *)
denote_tm (Γ:=Γ) (τ:=τ) (build Γ τ n f) ctx :=
  denote_array n (denote_tm ∘ f) ctx;
denote_tm (Γ:=Γ) (τ:=τ) (get Γ i ta) ctx := vector_nth i (⟦ ta ⟧ₜₘ ctx);
(* Nat *)
denote_tm (Γ:=Γ) (τ:=τ) (nval Γ n) ctx := n;
denote_tm (Γ:=Γ) (τ:=τ) (nsucc Γ t) ctx := Datatypes.S (⟦t⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (nrec Γ τ tf ti ta) ctx :=
  loop_down (⟦ ti ⟧ₜₘ ctx) (⟦ tf ⟧ₜₘ ctx) (⟦ ta ⟧ₜₘ ctx);
(* Reals *)
denote_tm (Γ:=Γ) (τ:=τ) (rval Γ r) ctx := r;
denote_tm (Γ:=Γ) (τ:=τ) (add Γ t1 t2) ctx := ⟦t1⟧ₜₘ ctx + ⟦t2⟧ₜₘ ctx;
(* Products *)
denote_tm (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) ctx := (⟦t1⟧ₜₘ ctx, ⟦t2⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (first Γ t) ctx := fst (⟦t⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (second Γ t) ctx := snd (⟦t⟧ₜₘ ctx);
(* Sums *)
denote_tm (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) ctx with ⟦e⟧ₜₘ ctx := {
  denote_tm (case Γ e c1 c2) ctx (Datatypes.inl x) := (⟦c1⟧ₜₘ ctx) x;
  denote_tm (case Γ e c1 c2) ctx (Datatypes.inr x) := (⟦c2⟧ₜₘ ctx) x
};
denote_tm (Γ:=Γ) (τ:=τ) (inl Γ τ σ e) ctx := Datatypes.inl (⟦e⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (inr Γ σ τ e) ctx := Datatypes.inr (⟦e⟧ₜₘ ctx) }
where "⟦ t ⟧ₜₘ" := (denote_tm t)
(* Helper for arrays *)
where denote_array {Γ τ} n (f : Fin.t n -> ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ)
  : ⟦Γ⟧ₜₓ -> ⟦Array n τ⟧ₜ by struct n :=
denote_array 0 f ctx := Vnil;
denote_array (S n) f ctx := Vcons (f (nat_to_fin n) ctx)
  ((denote_array n (shave_fin f)) ctx).

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
(* Lemma denote_shave_env_snd : forall τ Γ (e : Env τ (τ::Γ)),
  snd ⟦ e ⟧ₑ = ⟦ shave_env e ⟧ₑ.
Proof with quick.
  dependent induction e.
  simp shave_env.
  simp denote_env...
Qed.

Lemma Ddenote_shave_env_snd : forall τ Γ (e : Env τ (τ::Γ)),
  snd ⟦ Denv e ⟧ₑ = ⟦ Denv (shave_env e) ⟧ₑ.
Proof with quick.
  dependent induction e.
  simp shave_env.
  simp denote_env...
Qed. *)

Lemma denote_ren_elim : forall Γ Γ' τ
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
  induction t; quick; try solve [simp denote_tm in *; rewrites]...
  { simp denote_tm in *; induction v; rewrites. }
  { simp denote_tm in *. specialize IHt with (r:=rename_lifted r).
    simpl in IHt. simp rename_lifted in IHt.
    apply functional_extensionality...
    rewrite <- IHt...
    rewrite <- denote_ren_elim... }
  { simp denote_tm in *. rewrites.
    unfold compose.
    induction n... rewrites.
    apply Vcons_eq.
    splits... }
  { simp denote_tm. rewrite IHt1.
    destruct (⟦ rename r t1 ⟧ₜₘ ctx);
      quick; rewrites. }
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
  pose proof denote_ren_elim as H.
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
  induction t; intros; simp denote_tm; rewrites...
  { simpl. induction v...
    intros. simpl. rewrite IHv... }
  { specialize IHt with (s:=substitute_lifted s)...
    apply functional_extensionality...
    simp denote_tm.
    rewrite <- IHt...
    erewrite denote_sub_elim... }
  { simp denote_tm.
    unfold compose.
    induction n... rewrites.
    apply Vcons_eq... }
  { simp denote_tm.
    destruct (⟦ substitute s t1 ⟧ₜₘ ctx);
      quick; rewrites. }
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

Lemma denote_sub_id_ctx : forall Γ (ctx : ⟦ Γ ⟧ₜₓ),
  ⟦ id_sub ⟧ₛ ctx = ctx.
Proof with quick.
  intros Γ...
  destruct Γ...
  { dependent destruction ctx... }
  { dependent destruction ctx...
    intros.
    unfold id_sub. unfold hd_sub. simp denote_tm...
    fold (id_sub (Γ:=t::Γ)).
    rewrite denote_sub_tl_simpl.
    eapply injective_projections...
    admit. }
Admitted.

Lemma denote_sub_tl_cons :
  forall Γ Γ' τ (t : tm Γ' τ) ctx (sb : sub Γ Γ'),
  denote_sub (tl_sub (cons_sub t sb)) ctx = denote_sub sb ctx.
Proof with quick.
  intros.
  unfold id_sub.
  rewrite tl_cons_sub.
  fold (@id_sub Γ)...
Qed.
