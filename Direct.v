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
Require Import AD.Denotation.
(* Require Import AD.Tangent. *)

Local Open Scope program_scope.
Local Open Scope R_scope.

(* Defined in section 5 *)
(* Record Gl τ σ := make_gl {
  Gl_P : (R -> ⟦τ⟧ₜ) -> (R -> ⟦σ⟧ₜ) -> Prop;
}. *)

(*
  Relation between
    denotation function of term
      (the function the term describes)
    denotation function of macro term
      (the derivative of the function the term describes)
*)
Equations S Γ τ : tm Γ τ -> (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop :=
S Γ Real t f g :=
  (forall h, ⟦ t ⟧ₜₘ ∘ denote_env ∘ h = f /\
    ⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ h = g)
  /\
  (forall (x : R), ex_derive f x) /\
  (fun r => g r) = (fun r => (f r, Derive f r));
S Γ (σ × ρ) t f g :=
  exists f1 f2 g1 g2 t1 t2,
  exists (s1 : S Γ σ t1 f1 f2) (s2 : S Γ ρ t2 g1 g2),
    t = tuple Γ t1 t2 /\
    (f = fun r => (f1 r, g1 r)) /\
    (g = fun r => (f2 r, g2 r));
S Γ (σ → ρ) t f g :=
  (* exists h, *)
  forall (s : tm Γ σ),
  forall g1 g2,
  forall (sσ : S Γ σ s g1 g2),
    (* value s -> *)
    (* g1 = (⟦s⟧ₜₘ ∘ denote_env ∘ h) -> *)
    (* g2 = (⟦Dtm s⟧ₜₘ ∘ denote_env ∘ Denv ∘ h) -> *)
    S Γ ρ (app Γ _ _ t s) (fun x => f x (g1 x)) (fun x => g x (g2 x));
S Γ (σ <+> ρ) t f g :=
  (exists g1 g2,
    forall (t : tm Γ σ),
    forall (s: S Γ σ t g1 g2),
      f = Datatypes.inl ∘ g1 /\
      g = Datatypes.inl ∘ g2) \/
  (exists g1 g2,
    forall (t : tm Γ ρ),
    forall (s: S Γ ρ t g1 g2),
      f = Datatypes.inr ∘ g1 /\
      g = Datatypes.inr ∘ g2).

(* Inductive instantiation :
  forall {Γ Γ'}, (⟦ Γ' ⟧ₜₓ -> ⟦ Γ ⟧ₜₓ) -> Prop :=
  | inst_empty : @instantiation [] [] Datatypes.id
  | inst_cons : forall {Γ Γ' τ} (sb: ⟦ Γ' ⟧ₜₓ -> ⟦ Γ ⟧ₜₓ) {g1 g2},
      instantiation sb ->
      (S τ g1 g2) ->
      instantiation (fun (ctx: ⟦ τ::Γ' ⟧ₜₓ) => (sb (snd ctx))). *)

Inductive instantiation :
  forall {Γ Γ'}, sub Γ Γ' -> (R -> Env Γ') -> Prop :=
  | inst_empty : forall {f}, @instantiation [] [] id_sub f
  | inst_cons :
      forall {Γ Γ' τ} {t : tm Γ' τ} {s : sub Γ Γ'} {f : R -> Env Γ'},
      instantiation s f ->
      value t ->
      (S Γ' τ t (⟦t⟧ₜₘ ∘ denote_env ∘ f)
        (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ f)) ->
      instantiation (cons_sub t s) f.

(* Equations instantiation Γ {Γ'} (f : R -> Env Γ') : sub Γ Γ' -> Prop :=
instantiation nil f s := True;
instantiation (τ :: Γ) f s :=
  exists g1 g2,
    S τ g1 g2 /\
      g1 = (⟦hd_sub s⟧ₜₘ ∘ denote_env ∘ f) /\
      g2 = (⟦Dtm (hd_sub s)⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) /\
      instantiation Γ f (tl_sub s). *)

Lemma S_cong : forall Γ τ t f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> S Γ τ t f1 f2 = S Γ τ t g1 g2.
Proof. intros. rewrites. Qed.

Lemma S_soundness : forall Γ τ (t t' : tm Γ τ) f f',
  (t -->* t') ->
    S Γ τ t f f' = S Γ τ t' f f'.
Proof with quick.
  intros.
  induction τ; simp S...
  all: admit.
  (* intros.
  pose proof (soundness _ _ t t' H) as Heq.
  pose proof (D_step _ _ t t' H) as H'.
  pose proof (soundness _ _ (Dtm t) (Dtm t') H') as Heq'.
  rewrite <- Heq. rewrite <- Heq'... *)
Admitted.

(*
Lemma S_substitute_lifted :
  forall Γ Γ' τ σ (t : tm (σ::Γ) τ) (sb: sub Γ Γ') g g1 g2,
  S σ g1 g2 ->
  (exists (s : tm Γ' σ), S τ
    (⟦substitute (cons_sub s sb) t⟧ₜₘ ∘ denote_env ∘ g)
    (⟦Dtm (substitute (cons_sub s sb) t) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ g)) ->
  S τ
    (fun r => ⟦substitute (substitute_lifted (τ:=σ) sb) t⟧ₜₘ
      (g1 r, (denote_env (g r))))
    (fun r => ⟦Dtm (substitute (substitute_lifted (τ:=σ) sb) t) ⟧ₜₘ
      (g2 r, (denote_env (Denv (g r))))).
Proof with quick.
Admitted. *)

(* Lemma S_exists : forall Γ τ g1 g2 (h : R -> Env Γ),
  S τ g1 g2 ->
    exists (t: tm Γ τ),
      g1 = (⟦t⟧ₜₘ ∘ denote_env ∘ h) /\
      g2 = (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h).
Proof.
  intros. induction τ.
  simp S in H.
  exists (const Γ 0). split.
Admitted. *)

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
  S Γ' τ (substitute sb t) (⟦ substitute sb t ⟧ₜₘ ∘ denote_env ∘ f)
    (⟦ Dtm (substitute sb t) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f).
Proof with quick.
  intros Γ Γ' τ g t sb H.
  generalize dependent Γ'.
  (* pose proof (H τ) as H'. clear H. *)
  dependent induction t; unfold compose in *.
  { (* Var *)
    (* Using Inductive Instantiation *)
    intros. induction H; dependent induction v...
    simp cons_sub.

    (* Using Equation Instantiation *)
    (* induction v; intros;
      simp instantiation in H;
      (* specialize H with g; *)
      destruct H as [g1 [g2 H]];
      destruct H as [H [Heq1 [Heq2 H']]]; subst.
    { unfold hd_sub in H... }
    { erewrite S_cong.
      simp instantiation in H.
      unfold tl_sub... unfold tl_sub... } *)
    }
  { (* App *)
    intros.
    specialize IHt1 with Γ' g sb; specialize IHt2 with Γ' g sb.
    pose proof (IHt1 H) as IHt1'; clear IHt1.
    pose proof (IHt2 H) as IHt2'; clear IHt2...
    simp S in IHt1'.
    (* admit. *)

    (* With terms in relation for functions *)
    (* specialize IHt1' with
      (substitute sb t2)
      (⟦ substitute sb t2 ⟧ₜₘ ∘ denote_env ∘ g)
      (⟦ Dtm (substitute sb t2) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ g)
      Γ' g... *)
    (* eapply IHt1'... *)

    (* With existentials for term in relation for functions *)
    (* pose proof (IHt1' IHt2') as [t IHt1]. clear IHt1'. *)
    (* With existentials for context in relation for functions *)
    (* pose proof (IHt1' IHt2') as [Γ0 [h IHt1]]. clear IHt1'.
    eapply IHt1... *)
    (* all: admit. *)
    }
  { (* Abs *)
    intros. simp S. intros; subst.
    simpl (substitute sb (abs Γ τ σ t)).
    simp Dtm. simpl.

    (* simp instantiation in H. *)
    (* With existentials for context in relation *)
    (* induction H.
    exists []; exists f... subst... *)
    specialize IHt with (σ::Γ')
      (fun r => env_cons s (f r)) (cons_sub s id_sub).

    (* exists (substitute (substitute_lifted sb) t). *)
    (* instantiate (1:=f). *)
    (* Show Existentials. *)
    (* pose proof (cons_sub t @id_sub []). *)
    (* instantiate (1:=id_sub). *)
    (* simp instantiation. *)
    (* exists (⟦ t0 ⟧ₜₘ ∘ denote_env ∘ h).
    exists (⟦ Dtm t0 ⟧ₜₘ ∘ denote_env ∘ Denv ∘ h).
    splits... *)
    (* instantiate (1:=cons_sub t0 sb). *)
    all: admit.

    (* Induction on context *)
    (* induction Γ'.
    { intros. induction Γ.
      simp S. simpl (substitute sb (abs [] τ σ t)).
      simp Dtm. intros. fold (map Dt). subst.
      eapply S_cong.
      apply IHt.
      instantiate (2:=g).
      pose proof (|t0|).
      instantiate (1:=(|t0|)).
      simp instantiation.
      intros.
      exists (⟦ t0 ⟧ₜₘ ∘ denote_env ∘ h).
      exists (⟦ Dtm t0 ⟧ₜₘ ∘ denote_env ∘ Denv ∘ h).
      splits...
      admit.
      (* apply IHt. simp instantiation.
      exists g1; exists g2; splits... *) }
    { intros. simp S. intros.
      simpl (substitute sb (abs _ τ σ t)).
      simp Dtm. fold (map Dt).  } *)
    }
  { (* Const *)
    quick. splits.
    { intros. apply ex_derive_const. }
    { apply functional_extensionality.
      intros. unfold compose. rewrite Derive_const... } }
  { (* Add *)
    simpl in *. intros.
    pose proof (IHt1 Γ' g sb H) as [[Heq1 Heq1'] [Hex1 H1]]; clear IHt1.
    pose proof (IHt2 Γ' g sb H) as [[Heq2 Heq2'] [Hex2 H2]]; clear IHt2.
    splits; intros.
    { unfold compose.
      extensionality x; simpl.
      admit. }
    { unfold compose.
      extensionality x; simpl.
      admit. }
    { specialize Hex1 with x.
      specialize Hex2 with x.
      apply (ex_derive_plus _ _ _ Hex1 Hex2). }
    { apply functional_extensionality...
      simp Dtm. simpl. unfold compose in *.
      eapply equal_f in H1; eapply equal_f in H2.
      rewrite H1; rewrite H2.
      apply injective_projections...
      rewrite Derive_plus... } }
  { (* Tuples *)
    simpl. intros.
    pose proof (IHt1 Γ' g sb H) as H1'; clear IHt1.
    pose proof (IHt2 Γ' g sb H) as H2'; clear IHt2.
    simp S.
    exists (⟦ substitute sb t1 ⟧ₜₘ ∘ denote_env ∘ g).
    exists (⟦ Dtm (substitute sb t1) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ g).
    exists (⟦ substitute sb t2 ⟧ₜₘ ∘ denote_env ∘ g).
    exists (⟦ Dtm (substitute sb t2) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ g)...
    exists (substitute sb t1).
    exists (substitute sb t2).
    exists H1'. exists H2'... }
  { (* Projection 1 *)
    intros. unfold compose in *.
    specialize IHt with Γ' g sb.
    pose proof (IHt H) as IHt'; clear IHt.
    simp S in IHt'.
    destruct IHt' as [f1 [f2 [g1 [g2 [t1 [t2 [H1 H2]]]]]]]...
    simp Dtm... destruct H2 as [H2 [Heq [Heq1 Heq2]]].
    erewrite S_cong.
  2:{ apply functional_extensionality_dep...
      eapply equal_f in Heq1.
      rewrite Heq1...  }
  2:{ apply functional_extensionality_dep...
      eapply equal_f in Heq2.
      rewrite Heq2... }
    rewrite Heq.
    erewrite S_soundness...
    eapply multistep_FirstTuple.
    all: admit. }
  { (* Projection 2 *)
    intros. unfold compose in *.
    specialize IHt with Γ' g sb.
    pose proof (IHt H) as IHt'; clear IHt.
    simp S in IHt'.
    destruct IHt' as [f1 [f2 [g1 [g2 [S1 [S2 [H1 H2]]]]]]]...
    simp Dtm... destruct H2 as [H2 [Heq [Heq1 Heq2]]].
    erewrite S_cong.
  2:{ apply functional_extensionality_dep...
      eapply equal_f in Heq1.
      rewrite Heq1...  }
  2:{ apply functional_extensionality_dep...
      eapply equal_f in Heq2.
      rewrite Heq2... }
      rewrite Heq.
    erewrite S_soundness...
    eapply multistep_SecondTuple.
    all: admit. }
  { (* Case *)
    intros.
    pose proof (IHt1 Γ' g sb H) as IH1; clear IHt1.
    simp S in IH1. simpl. simp Dtm. simpl.
    destruct IH1 as [[g1 [g2 H']]|[g1 [g2 H']]].
    all: admit.
    (* induction H.
    rewrite app_sub_id.
    simp Dtm.
    pose proof (IHt1 Γ' g sb H) as H1; clear IHt1.
    pose proof (IHt2 Γ' g sb H) as H2; clear IHt2.
    pose proof (IHt3 Γ' g sb H) as H3; clear IHt3.
    simpl (substitute sb (case Γ t1 t2 t3)).
    simp Dtm.
    simp S in H1. destruct H1 as [H1|H1].
    induction H... simpl. *)
    }
  { (* Inl *)
    intros. simp S. left...
    exists (⟦ substitute sb t ⟧ₜₘ ∘ denote_env ∘ g).
    exists (⟦ Dtm (substitute sb t) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ g).
    split; unfold compose; extensionality x... }
  { (* Inl *)
    intros. simp S. right...
    exists (⟦ substitute sb t ⟧ₜₘ ∘ denote_env ∘ g).
    exists (⟦ Dtm (substitute sb t) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ g).
    split; unfold compose; extensionality x... }
Admitted.

Lemma S_correct_R :
  forall Γ (t : tm Γ Real) f,
  S Γ Real t (fun r => (⟦ t ⟧ₜₘ (denote_env (f r))))
    (fun r => ⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r)))) ->
  (⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) =
  fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
    Derive (fun x => ⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof with quick.
  intros. simp S in H.
  unfold compose in *. extensionality x.
  destruct H.
  clear H.
  destruct H0.
  eapply equal_f in H0.
  rewrite H0...
Qed.

(* Lemma S_correct_prod :
  forall Γ τ σ (t : tm Γ τ) (s : tm Γ σ) f,
  S (τ × σ) (⟦ tuple _ t s ⟧ₜₘ ∘ denote_env ∘ f)
    (⟦ Dtm (tuple _ t s) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) ->
  ⟦ Dtm (tuple _ t s) ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f =
    fun r => (⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r))),
              (⟦ Dtm s ⟧ₜₘ (denote_env (Denv (f r))))).
Proof. quick. Qed. *)

Theorem semantic_correct_R :
  forall (t : tm [] Real) (f : R -> Env []),
  (fun r => ⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r)))) =
    fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
      Derive (fun (x : R) => ⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof with quick.
  intros.
  rewrite <- (app_sub_id [] Real t).
  apply S_correct_R.
  apply (fundamental [] [] Real f t id_sub).
  constructor.
Qed.
