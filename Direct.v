Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Arith_base.
Require Import Coquelicot.Derive.
Import EqNotations.

Require Import AD.Definitions.
Require Import AD.Macro.
Require Import AD.Tactics.

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
  end
where "⟦ t ⟧ₜₘ" := (denote_tm t).

Definition constant {X} (x : X) {Y} {F : X -> Y -> X} := F x.
(* Compute ((denote_tm (Dtm ex_plus) tt) (id, constant 1) (id, constant 0)). *)

Fixpoint denote_env {Γ} (G : Env Γ) : ⟦ Γ ⟧ₜₓ :=
  match G with
  | env_nil => tt
  | env_cons Γ' τ c G' => (denote_closed c, denote_env G')
  end
with denote_closed {τ} (c : Closed τ) : ⟦ τ ⟧ₜ :=
  match c with
  | closure Γ'' τ' t G'' => denote_tm t (denote_env G'')
  | clapp τ' σ c1 c2 => (denote_closed c1) (denote_closed c2)
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

(* Lemmas for renaming and substitution in the denotated context. *)
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

Lemma denote_ren_pop_elim : forall Γ τ (ctx : ⟦ τ :: Γ ⟧ₜₓ),
  denote_ren (fun (ρ : ty) (y : ρ ∈ Γ) => Pop Γ ρ τ y) ctx = snd ctx.
Proof with eauto.
  induction Γ; simpl; intros...
  { induction ctx. simpl. induction b... }
  { induction ctx as [T G].
    apply injective_projections... simpl.
    unfold tl_ren... simpl.
    rewrite <- IHΓ. simpl. admit. }
Admitted.

Lemma denote_shift_elim : forall Γ τ σ (t : tm Γ τ) ctx x,
  ⟦ t ⟧ₜₘ ctx = ⟦ shift (σ:=σ) t ⟧ₜₘ (x, ctx).
Proof with eauto.
  induction t; intros; simpl...
  { rewrite IHt1 with (x:=x).
    rewrite IHt2 with (x:=x)... }
  { apply functional_extensionality. intros.
    rewrite <- denote_ren_commutes. simpl.
    rewrite <- denote_ren_elim. rewrite denote_ren_pop_elim... }
  { erewrite IHt1. erewrite IHt2... }
  { erewrite IHt1. erewrite IHt2... }
  { erewrite IHt... }
  { erewrite IHt... }
Qed.

Lemma denote_sub_elim : forall Γ Γ' τ
  (s : sub Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  denote_sub s ctx = denote_sub (tl_sub (substitute_lifted s)) (x, ctx).
Proof with eauto.
  induction Γ; intros...
  intros. specialize IHΓ with (s := (tl_sub s)).
  simpl. rewrite IHΓ with (x := x). simpl.
  unfold hd_sub. unfold tl_sub. simpl.
  erewrite denote_shift_elim...
Qed.

Lemma denote_sub_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (s : sub Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (denote_sub s ctx) = ⟦ substitute s t ⟧ₜₘ ctx.
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

(* Defined in section 5 *)
Record Gl := make_gl {
  glτ : ty;
  glσ : ty;
  GlP : (R -> ⟦glτ⟧ₜ) -> (R -> ⟦glσ⟧ₜ) -> Prop;
}.

(* Placeholder for derivatives on nD *)
Definition der {X Y} (f : X -> Y) x := f x.

Fixpoint S τ : (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop
  := match τ with
     | Real => fun f g =>
          (fun r => g r) = (fun r => (f r, Derive f r))
     | σ × ρ => fun f g =>
        forall f1 f2 g1 g2,
          S σ f1 f2 ->
          S ρ g1 g2 ->
            (f = fun r => (f1 r, g1 r)) /\
            (g = fun r => (f2 r, g2 r))
     | σ → ρ => fun f g =>
        forall f1 f2 g1 g2 (s1 : S σ g1 g2),
          S ρ (fun x => f1 x (g1 x)) (fun x => f2 x (g2 x)) ->
          f = f1 /\ g = f2
     end.

(* Program Fixpoint substitute_env {Γ Γ'} (s : sub Γ Γ') (E : Env Γ) : Env Γ' :=
  match E with
  | env_nil => env_nil
  | env_cons Γ'' τ c E' => env_cons Γ' τ
    (substitute_closed s c) (substitute_env s E')
  end
with substitute_closed {Γ Γ' τ} (s : sub Γ Γ') (c : Closed τ) : Closed τ :=
  match c with
  | closure Γ'' τ t E => closure Γ' τ (substitute s t) (substitute_env s E)
  | clapp τ σ cf c => clapp τ σ (substitute_closed s cf) (substitute_closed s c)
  end. *)

(*
  Plain words:
    Given a context Γ for which t is well-typed (Γ ⊢ t : τ) and every typing
    assignment in the context is in the relation S, applying the substitutions
    to the term t is also in the relation S.
*)
Lemma fundamental_lemma :
  forall Γ Γ' τ g
    (t : tm Γ τ) (sb : sub Γ Γ') (dsb : sub (Dctx Γ) (Dctx Γ')),
  Dtm (substitute sb t) = substitute dsb (Dtm t) ->
  (forall σ (s : tm Γ σ) f,
    S σ (⟦ s ⟧ₜₘ ∘ denote_env ∘ f) (⟦ Dtm s ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f)) ->
  S τ (⟦ substitute sb t ⟧ₜₘ ∘ denote_env ∘ g) (⟦ Dtm (substitute sb t) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ g).
Proof with quick.
  intros Γ Γ' τ g t sb dsb sbEq H.
  pose proof (H τ) as H'. clear H.
  dependent induction τ; unfold compose in *.
  { simpl in *. apply functional_extensionality.
    intros. rewrite sbEq.
    rewrite <- 2 denote_sub_commutes...
    dependent induction t...
    dependent induction v. simpl.
    admit. }
Admitted.

Lemma S_correct_R :
  forall Γ (t : tm Γ Real) f,
  S Real (fun r => (⟦ t ⟧ₜₘ (denote_env (f r))))
    (fun r => ⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r)))) ->
  (⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) =
  fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
    Derive (fun x => ⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof. quick. Qed.

Lemma S_correct_prod :
  forall Γ τ σ (t : tm Γ τ) (s : tm Γ σ) f,
  S (τ × σ) (⟦ tuple _ t s ⟧ₜₘ ∘ denote_env ∘ f)
    (⟦ Dtm (tuple _ t s) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) ->
  ⟦ Dtm (tuple _ t s) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f =
    fun r => (⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r))),
              (⟦ Dtm s ⟧ₜₘ (denote_env (Denv (f r))))).
Proof. quick. Qed.

Definition shave_env {Γ τ} (G : Env (τ::Γ)) : Env Γ.
  induction Γ. constructor.
  inversion G. assumption.
Defined.

Lemma shave_env_prod Γ τ (E : Env (τ :: Γ)) (c : Closed τ):
  denote_env E = (denote_closed c, denote_env (shave_env E)).
Proof with quick.
  dependent induction E.
  erewrite IHE. reflexivity.
  admit. admit.
Admitted.

Lemma shave_env_snd :
  forall Γ τ (f: R -> Env (τ :: Γ)) (x: R),
  (denote_env (shave_env (f x))) = (snd (denote_env (f x))).
Proof.
  admit.
Admitted.

Lemma well_typed_S :
  forall Γ τ (t : tm Γ τ) f,
    S τ (⟦ t ⟧ₜₘ ∘ denote_env ∘ f)
      (⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f).
Proof with quick.
  induction τ; unfold compose; simpl.
  { intros. apply functional_extensionality. intros.
    dependent induction t... dependent induction v...
    remember (f x). admit. }
  { intros. split; apply functional_extensionality...
    admit. }
  { intros. split; apply functional_extensionality...
    admit. }
Admitted.

Theorem semantic_correct_R :
  forall Γ (t : tm Γ Real) (f : R -> Env Γ),
  ⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f =
    fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
              Derive (fun x =>⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof with quick.
  intros.
  pose proof (well_typed_S Γ Real t).
  pose proof (S_correct_R Γ t)...
Qed.

(* Theorem semantic_correct_Prod :
  forall Γ τ σ (t : tm Γ (τ × σ)) (f : R -> Env Γ),
  ⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f =
    fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
              der (fun x =>⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof with quick.
  intros.
  pose proof (well_typed_S Γ (τ × σ) (tuple _ t s)).
  pose proof (S_correct_prod Γ (τ × σ))...
Qed. *)

Theorem semantic_correct_Prod :
  forall Γ τ σ (t : tm Γ τ) (s : tm Γ σ) (f : R -> Env Γ),
  ⟦ Dtm (tuple _ t s) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f =
    fun r => (⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r))),
              (⟦ Dtm s ⟧ₜₘ (denote_env (Denv (f r))))).
Proof with quick.
  intros.
  pose proof (well_typed_S Γ (τ × σ) (tuple _ t s)).
  pose proof (S_correct_prod Γ (τ × σ))...
Qed.
