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
Import EqNotations.

Require Import AD.Definitions.
Require Import AD.Macro.
Require Import AD.Tactics.
(* Require Import AD.Tangent. *)

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

Fixpoint denote_env' {Γ} (G : Env' Γ) : ⟦ Γ ⟧ₜₓ :=
  match G with
  | env'_nil => tt
  | env'_cons Γ' τ t G' => (denote_tm t tt, denote_env' G')
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
    ⟦ t ⟧ₜₘ (denote_ren r ctx) = ⟦ rename r t ⟧ₜₘ ctx.
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

Lemma denote_shift_elim : forall Γ τ σ (t : tm Γ τ) ctx (x : ⟦ σ ⟧ₜ),
    ⟦ t ⟧ₜₘ ctx = ⟦ shift t ⟧ₜₘ (x, ctx).
Proof with eauto.
  unfold shift. intros.
  rewrite <- denote_ren_commutes...
  pose proof denote_ren_elim.
  specialize H with Γ Γ σ (fun t x => x) x ctx.
  unfold tl_ren in H.
  simpl in H. rewrite <- H.
  fold (@id_ren Γ).
  rewrite denote_ren_commutes...
  rewrite app_ren_id...
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

(* Defined in section 5 *)
Record Gl τ σ := make_gl {
  Gl_P : (R -> ⟦τ⟧ₜ) -> (R -> ⟦σ⟧ₜ) -> Prop;
}.
(*
Fixpoint S τ : Gl τ (Dt τ)
  := make_gl τ (Dt τ)
    (match τ with
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
          f = f1 /\ g = f2 ->
          S ρ (fun x => f1 x (g1 x)) (fun x => f2 x (g2 x))
     end).
*)
Program Fixpoint S τ : (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop
  := match τ with
    | Real => fun (f : R -> R) (g : R -> R * R) =>
      (forall (x : R), ex_derive f x) /\
        (fun r => g r) = (fun r => (f r, Derive f r))
    | σ × ρ => fun f g =>
      exists f1 f2 g1 g2 (s1 : S σ f1 f2) (s2 : S ρ g1 g2),
        (f = fun r => (f1 r, g1 r)) /\
        (g = fun r => (f2 r, g2 r))
    | σ → ρ => fun f g =>
      (* In the proof sσ is opaque, I only have access to the resulting
        denotated functions g1 and g2 not the term g1 and g2 are created from.
      *)
      exists Γ h,
      forall (t : tm Γ σ),
      forall g1 g2 (sσ : S σ g1 g2),
        g1 = (⟦t⟧ₜₘ ∘ denote_env' ∘ h) ->
        g2 = (⟦Dtm t⟧ₜₘ ∘ denote_env' ∘ Denv' ∘ h) ->
        S ρ (fun x => f x (g1 x)) (fun x => g x (g2 x))
    end.

(*
Inductive instantiation :
  forall {Γ Γ'}, (⟦ Γ' ⟧ₜₓ -> ⟦ Γ ⟧ₜₓ) -> Prop :=
  | inst_empty : @instantiation [] [] (denote_sub id_sub)
  | inst_cons : forall {Γ Γ' τ} {sb : sub Γ Γ'} {g1 g2},
      instantiation (denote_sub sb) ->
      (S τ g1 g2) ->
      instantiation (denote_sub (substitute_lifted (τ:=τ) sb)).
*)

Inductive instantiation :
  forall {Γ Γ'}, sub Γ Γ' -> (R -> Env' Γ') -> Prop :=
  | inst_empty : forall {f}, @instantiation [] [] id_sub f
  | inst_cons : forall {Γ Γ' τ} {t : tm Γ' τ} {s : sub Γ Γ'} {f : R -> Env' Γ'},
      instantiation s f ->
      (S τ (⟦t⟧ₜₘ ∘ denote_env' ∘ f)
        (⟦Dtm t⟧ₜₘ ∘ denote_env' ∘ Denv' ∘ f)) ->
      instantiation (cons_sub t s) f.

Lemma S_cong : forall τ f1 f2 g1 g2,
  S τ f1 f2 -> g1 = f1 -> g2 = f2 -> S τ g1 g2.
Proof. intros; subst; assumption. Qed.

Lemma S_substitute_lifted :
  forall Γ Γ' τ σ (t : tm (σ::Γ) τ) (sb: sub Γ Γ') g g1 g2,
  S σ g1 g2 ->
  (exists (s : tm Γ' σ), S τ
    (⟦substitute (cons_sub s sb) t⟧ₜₘ ∘ denote_env' ∘ g)
    (⟦Dtm (substitute (cons_sub s sb) t) ⟧ₜₘ ∘ denote_env' ∘ Denv' ∘ g)) ->
  S τ
    (fun r => ⟦substitute (substitute_lifted (τ:=σ) sb) t⟧ₜₘ
      (g1 r, (denote_env' (g r))))
    (fun r => ⟦Dtm (substitute (substitute_lifted (τ:=σ) sb) t) ⟧ₜₘ
      (g2 r, (denote_env' (Denv' (g r))))).
Proof with quick.
  quick...
  destruct H0 as [s H'].
Admitted.

(*
  Plain words:
    Given a context Γ for which t is well-typed (Γ ⊢ t : τ) and every typing
    assignment in the context is in the relation S, applying the substitutions
    to the term t is also in the relation S.
*)
Lemma fundamental :
  forall Γ Γ' τ f
    (t : tm Γ τ) (sb : sub Γ Γ'),
  instantiation sb f ->
  S τ (⟦ substitute sb t ⟧ₜₘ ∘ denote_env' ∘ f)
    (⟦ Dtm (substitute sb t) ⟧ₜₘ ∘ denote_env' ∘ Denv' ∘ f).
Proof with quick.
  intros Γ Γ' τ g t sb H.
  generalize dependent Γ'.
  (* pose proof (H τ) as H'. clear H. *)
  dependent induction t; unfold compose in *.
  { (* Var *)
    intros.
    dependent induction H... inversion v.
    dependent destruction v; subst... }
  { (* App *)
    intros.
    specialize IHt1 with Γ' g sb; specialize IHt2 with Γ' g sb.
    pose proof (IHt1 H) as IHt1'; clear IHt1.
    pose proof (IHt2 H) as IHt2'; clear IHt2...
    destruct IHt1' as [Γ'' [h IHt1']].
    eapply IHt1'...
    admit.

    (* specialize IHt1' with
      (⟦ t ⟧ₜₘ ∘ denote_env' ∘ h)
      (⟦ Dtm t ⟧ₜₘ ∘ denote_env' ∘ Denv' ∘ h).
    apply IHt1'. *)
    (* admit. *)
    (* destruct IHt1' as [Γ'' IHt1']. *)
    (* eapply IHt1'...
    { apply functional_extensionality... unfold compose... }
    { unfold compose... }  *)
    }
  { (* Abs *)
    quick; subst.
    exists Γ'; exists g...
    apply S_substitute_lifted...
    exists t0.
    apply IHt.
    constructor; subst...

    (* exists (cons_sub t0 sb).
    pose proof (inst_cons H sσ).
    constructor... *)

    (* unfold compose...
    dependent induction H.
    { rewrite lift_sub_id.
      rewrite 1 app_sub_id.
      pose proof (IHt [] f (|t0|)).
      admit. }
    { admit. } *)

    (* eapply (IHt Γ' g (cons_sub t0 sb)).
    exists Γ'...
    pose proof (IHt Γ' g (cons_sub t0 sb)); subst.
    dependent induction H.
    { rewrite lift_sub_id.
      rewrite 1 app_sub_id.
      admit. }
    { admit. }
    apply H2.
    apply IHt. *)

    (* eapply S_cong; try apply IHt.
  2:apply functional_extensionality...
  2:rewrite <- 2 denote_sub_commutes.
  3:apply functional_extensionality...
    pose proof (inst_cons H sσ).
    dependent induction H.
    rewrite lift_sub_id...
    rewrite app_sub_id... *) }
  { (* Const *)
    quick. split.
    { intros. apply ex_derive_const. }
    apply functional_extensionality.
    intros. rewrite Derive_const... }
  { (* Add *)
    simpl in *. intros.
    pose proof (IHt1 Γ' g sb H) as [Hex1 H1]; clear IHt1.
    pose proof (IHt2 Γ' g sb H) as [Hex2 H2]; clear IHt2.
    split.
    { intros.
      specialize Hex1 with x.
      specialize Hex2 with x.
      apply (ex_derive_plus _ _ _ Hex1 Hex2). }
    { apply functional_extensionality...
      eapply equal_f in H1; rewrite H1.
      eapply equal_f in H2; rewrite H2.
      apply injective_projections...
      rewrite Derive_plus... } }
  { (* Tuples *)
    simpl. intros.
    pose proof (IHt1 Γ' g sb H) as H1'; clear IHt1.
    pose proof (IHt2 Γ' g sb H) as H2'; clear IHt2.
    exists (⟦ substitute sb t1 ⟧ₜₘ ∘ denote_env' ∘ g).
    exists (⟦ Dtm (substitute sb t1) ⟧ₜₘ ∘ denote_env' ∘ Denv' ∘ g).
    exists (⟦ substitute sb t2 ⟧ₜₘ ∘ denote_env' ∘ g).
    exists (⟦ Dtm (substitute sb t2) ⟧ₜₘ ∘ denote_env' ∘ Denv' ∘ g)... }
  { (* Projection 1 *)
    intros.
    specialize IHt with Γ' g sb.
    pose proof (IHt H) as IHt'; clear IHt.
    simpl in IHt'.
    destruct IHt' as [f1 [f2 [g1 [g2 [S1 [S2 [H1' H2']]]]]]]...
    eapply S_cong; try (apply S1);
    apply functional_extensionality_dep; intros;
    pose proof (equal_f H1') as H1; clear H1';
    pose proof (equal_f H2') as H2; clear H2'.
    rewrite H1...
    rewrite H2... }
  { (* Projection 2 *)
    intros.
    specialize IHt with Γ' g sb.
    pose proof (IHt H) as IHt'; clear IHt.
    simpl in IHt'.
    destruct IHt' as [f1 [f2 [g1 [g2 [S1 [S2 [H1' H2']]]]]]]...
    eapply S_cong; try (apply S2);
    apply functional_extensionality_dep; intros;
    pose proof (equal_f H1') as H1; clear H1';
    pose proof (equal_f H2') as H2; clear H2'.
    rewrite H1...
    rewrite H2... }
Admitted.

Lemma S_correct_R :
  forall Γ (t : tm Γ Real) f,
  S Real (fun r => (⟦ t ⟧ₜₘ (denote_env (f r))))
    (fun r => ⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r)))) ->
  (⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) =
  fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
    Derive (fun x => ⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof. intros. destruct H. quick. Qed.

Lemma S_correct_prod :
  forall Γ τ σ (t : tm Γ τ) (s : tm Γ σ) f,
  S (τ × σ) (⟦ tuple _ t s ⟧ₜₘ ∘ denote_env ∘ f)
    (⟦ Dtm (tuple _ t s) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) ->
  ⟦ Dtm (tuple _ t s) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f =
    fun r => (⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r))),
              (⟦ Dtm s ⟧ₜₘ (denote_env (Denv (f r))))).
Proof. quick. Qed.

Theorem semantic_correct_R :
  forall (t : tm [] Real) (f : R -> Env []),
  (fun r => ⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r)))) =
    fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
      Derive (fun (x : R) => ⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof with quick.
  intros.
  rewrite <- (app_sub_id [] Real t).
  apply S_correct_R.
  apply (fundamental _ _ _ _ t id_sub).
  constructor.
Qed.
