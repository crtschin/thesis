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
Fixpoint denote_t τ : Type :=
  match τ with
  | Real => R -> R
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

  | const r => fun ctx => fun _ => r
  | add t1 t2 => fun ctx => fun r => ⟦t1⟧ₜₘ ctx r + ⟦t2⟧ₜₘ ctx r

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

(*
  Prop translation of S in the proof of theorem 1 as an
    inductive definition
*)
(* Inductive GlProp : forall τ σ, (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ σ ⟧ₜ) -> Prop :=
  | s_r : forall f,
      GlProp Real (Dt Real) f (fun r => (f r, Derive f r))
  | s_prod : forall τ σ f1 f2 g1 g2,
      GlProp τ (Dt τ) f1 f2 ->
      GlProp σ (Dt σ) g1 g2 ->
      GlProp (τ × σ) (Dt (τ × σ)) (fun r => (f1 r, g1 r)) (fun r => (f2 r, g2 r))
  | s_arr : forall τ σ f1 f2 g1 g2 (s1 : GlProp τ (Dt τ) g1 g2),
      GlProp σ (Dt σ) (fun x => f1 x (g1 x)) (fun x => f2 x (g2 x)) ->
      GlProp (τ → σ) (Dt (τ → σ))(fun r => f1 r) (fun r => f2 r)
. *)

Program Fixpoint S τ : (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop
  := match τ with
     | Real => fun f g =>
        forall r, g r = (f r, (Derive (f r)))
     | σ × ρ => fun f g =>
        forall f1 f2 g1 g2,
          S σ f1 f2 ->
          S ρ g1 g2 ->
            (fun r => (f1 r, g1 r)) = f /\
            (fun r => (f2 r, g2 r)) = g
     | σ → ρ => fun f g =>
        forall f1 f2 g1 g2 (s1 : S σ g1 g2),
          S ρ (fun x => f1 x (g1 x)) (fun x => f2 x (g2 x)) ->
          f = f1 /\ g = f2
     end.

(* Record St := make_s {
  carrier : ty;
  SP : (R -> ⟦carrier⟧ₜ) -> (R -> ⟦Dt carrier⟧ₜ) -> Prop;
}.

Definition interpret τ : St :=
  match τ with
  | Real => make_s Real (GlProp Real (Dt Real))
  | τ1 × τ2 => make_s (τ1 × τ2) (GlProp (τ1 × τ2) (Dt (τ1 × τ2)))
  | τ1 → τ2 => make_s (τ1 → τ2) (GlProp (τ1 → τ2) (Dt (τ1 → τ2)))
  end. *)

(*
  Plain words:
    Given a context Γ for which t is well-typed (Γ ⊢ t : τ) and every typing
    assignment in the context is in the relation S, applying the substitutions
    in the context to the term t is also in the relation S.
*)
Lemma fundamental_lemma :
  forall Γ Γ' τ g g'
    (t : tm Γ τ) (sb : sub Γ Γ'),
  (forall σ (s : tm Γ' σ) f f',
    S σ (⟦ s ⟧ₜₘ ∘ f) (⟦ Dtm s ⟧ₜₘ ∘ f')) ->
  S τ (⟦ substitute sb t ⟧ₜₘ  ∘ g) (⟦ Dtm (substitute sb t) ⟧ₜₘ ∘ g').
Proof with eauto.
  induction τ; intros.
  { specialize H with (σ:=Real)... }
  { specialize H with (σ:=τ1 → τ2)... }
  { specialize H with (σ:=τ1 × τ2)... }
Qed.

Theorem semantic_correct :
  forall Γ Γ' τ g g' (E : Env Γ)
    (t : tm Γ τ),
  exists g g', ⟦ Dtm t ⟧ₜₘ g =
    (⟦ t ⟧ₜₘ ∘ (denote_env), Derive (⟦ t ⟧ₜₘ ∘ (denote_env))).
Proof.
Admitted.
