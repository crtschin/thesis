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

Equations S (Γ : list ty) τ (g1 : R -> ⟦Γ⟧ₜₓ) (g2 : R -> ⟦Dctx Γ⟧ₜₓ) : (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop :=
S Γ Real h1 h2 f g :=
  (forall (x : R), ex_derive f x) /\
    (fun r => g r) = (fun r => (f r, Derive f r));
S Γ (σ × ρ) h1 h2 f g :=
  exists f1 f2 g1 g2 (s1 : S Γ σ h1 h2 f1 f2) (s2 : S Γ ρ h1 h2 g1 g2),
    (f = fun r => (f1 r, g1 r)) /\
    (g = fun r => (f2 r, g2 r));
S Γ (σ → ρ) h1 h2 f g :=
  forall (s : tm Γ σ),
  (* forall (b : tm (σ::Γ) ρ), *)
  (* forall (t : tm Γ (σ → ρ)), *)
  forall (sσ : S Γ σ h1 h2 (⟦ s ⟧ₜₘ ∘ h1) (⟦ Dtm s ⟧ₜₘ ∘ h2)),
    (* t = abs _ _ _ b -> *)
    (* value s -> *)
    (* (fun x => (⟦ substitute (|s|) b ⟧ₜₘ ∘ h1) x) = (fun x => f x ((⟦ s ⟧ₜₘ ∘ h1) x)) /\
    (fun x => (⟦ Dtm (substitute (|s|) b) ⟧ₜₘ ∘ h2) x) = (fun x => g x ((⟦ Dtm s ⟧ₜₘ ∘ h2) x)) -> *)
  (exists t, S Γ ρ h1 h2 (⟦ (app _ _ _ t s) ⟧ₜₘ ∘ h1)
    (⟦ Dtm (app _ _ _ t s) ⟧ₜₘ ∘ h2));
S Γ (σ <+> ρ) h1 h2 f g :=
  (forall g1 g2,
    (* forall (s: S Γ σ h1 h2 g1 g2), *)
      f = Datatypes.inl ∘ g1 /\
      g = Datatypes.inl ∘ g2) \/
  (forall g1 g2,
    (* forall (s: S Γ ρ h1 h2 g1 g2), *)
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
  forall {Γ Γ'}, sub Γ Γ' -> Prop :=
  | inst_empty : @instantiation [] [] id_sub
  | inst_cons :
      forall {Γ Γ' τ} {s : sub Γ Γ'},
      forall {t : tm Γ' τ},
      instantiation s ->
        value t ->
        (forall h1 h2, S Γ' τ h1 h2 (⟦ t ⟧ₜₘ ∘ h1) (⟦ Dtm t ⟧ₜₘ ∘ h2)) ->
        instantiation (cons_sub t s).

(* Equations instantiation Γ {Γ'} (f : R -> Env Γ') : sub Γ Γ' -> Prop :=
instantiation nil f s := True;
instantiation (τ :: Γ) f s :=
  exists g1 g2,
    S τ g1 g2 /\
      g1 = (⟦hd_sub s⟧ₜₘ ∘ denote_env ∘ f) /\
      g2 = (⟦Dtm (hd_sub s)⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) /\
      instantiation Γ f (tl_sub s). *)

Lemma S_cong : forall Γ τ h1 h2 f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> S Γ τ h1 h2 f1 f2 = S Γ τ h1 h2 g1 g2.
Proof. intros; rewrites. Qed.

(* Lemma S_soundness : forall Γ τ (t t' : tm Γ τ) f,
  (t -->* t') ->
    S τ (⟦ t ⟧ₜₘ ∘ denote_env ∘ f) (⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) ->
      S τ (⟦ t' ⟧ₜₘ ∘ denote_env ∘ f) (⟦ Dtm t' ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f).
Proof with quick.
  intros.
  pose proof (soundness _ _ t t' H) as Heq.
  pose proof (D_step _ _ t t' H) as H'.
  pose proof (soundness _ _ (Dtm t) (Dtm t') H') as Heq'.
  rewrite <- Heq. rewrite <- Heq'...
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

Lemma S_exists : forall Γ τ g1 g2 (h : R -> Env Γ),
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
  forall Γ Γ' τ
    (t : tm Γ τ) (sb : sub Γ Γ') h1 h2,
  instantiation sb ->
  (* instantiation Γ f sb -> *)
  S Γ' τ h1 h2 (⟦substitute sb t⟧ₜₘ ∘ h1) (⟦Dtm (substitute sb t)⟧ₜₘ ∘ h2).
Proof with quick.
  intros Γ Γ' τ t sb h1 h2 H.
  generalize dependent Γ'.
  (* pose proof (H τ) as H'. clear H. *)
  dependent induction t; unfold compose in *.
  { (* Var *)
    (* Using Inductive Instantiation *)
    intros. induction H; dependent induction v...
    simp cons_sub...

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
    specialize IHt1 with Γ' sb h1 h2; specialize IHt2 with Γ' sb h1 h2.
    pose proof (IHt1 H) as IHt1'; clear IHt1.
    pose proof (IHt2 H) as IHt2'; clear IHt2...
    simp S in IHt1'.
    pose proof (IHt1' _ IHt2').
    simp Dtm...

    (*
    (* With terms in relation for functions *)
    specialize IHt1' with Γ' h1 h2
      (* (⟦ substitute sb t2 ⟧ₜₘ ∘ h1)
      (⟦ Dtm (substitute sb t2) ⟧ₜₘ ∘ h2) *)
      (⟦ app Γ' τ σ (substitute sb t1) (substitute sb t2) ⟧ₜₘ ∘ h1)
      (⟦ Dtm (app Γ' τ σ (substitute sb t1) (substitute sb t2)) ⟧ₜₘ ∘ h2)
      (substitute sb t2).
    unfold compose in *.
    pose proof (IHt1' IHt2'); clear IHt1'.
    simp Dtm... *)

      (* (⟦ Dtm (substitute sb t2) ⟧ₜₘ ∘ h2)
      Γ' g
      (substitute sb t2)... *)

    (* With existentials for term in relation for functions *)
    (* pose proof (IHt1' IHt2') as [t IHt1]. clear IHt1'. *)
    (* With existentials for context in relation for functions *)
    (* pose proof (IHt1' IHt2') as [Γ0 [h IHt1]]. clear IHt1'.
    eapply IHt1... *)
    (* all: admit. *)
    }
  { (* Abs *)
    intros. simp S... subst. unfold compose...
    specialize IHt with Γ'
      (cons_sub s sb) h1 h2.
    exists (substitute sb (abs _ _ _ t))...
    (* exists Γ'. exists h1. exists h2. *)
    intros; subst. simp Dtm...
    (* rewrite D_sub. *)
    erewrite S_cong. apply IHt...
  2:{ extensionality x.
      erewrite <- 2 denote_sub_commutes...
      unfold hd_sub. simp cons_sub substitute_lifted...
      erewrite <- denote_sub_elim.
    }
    eapply IHt.

    destruct H0.
    simp Dtm in *; fold (map Dt) Dt in *; unfold compose in *.
    erewrite H0; erewrite H1... simp Dtm.
    simp Dtm in *; fold (map Dt) Dt in *; unfold compose in *...
    simpl.


    (* eapply IHt.
    erewrite S_cong.
    eapply IHt...
    instantiate (1:=cons_sub s sb)...
    constructor...
  2:{ extensionality x.
      eapply equal_f in H0.
      erewrite H0.
      erewrite <- 2 denote_sub_commutes...
      unfold hd_sub. simp cons_sub substitute_lifted...
      erewrite <- denote_sub_elim.
      erewrite denote_sub_tl_cons... }
  2:{ extensionality x.
      eapply equal_f in H1.
      erewrite H1...
      erewrite <- 2 denote_sub_commutes...
      unfold hd_sub. simp cons_sub substitute_lifted...
      erewrite <- denote_sub_elim.
      erewrite denote_sub_tl_cons... } *)

    (* simp instantiation in H. *)
    (* With existentials for context in relation *)
    (* induction H.
    exists []; exists f... subst... *)
    (* specialize IHt with (σ::[])
      (fun r => env_cons t0 (f r)) (cons_sub t0 id_sub). *)

    induction H.
    erewrite S_cong.
    (* exists (substitute (substitute_lifted sb) t). *)
    apply IHt.
    instantiate (1:=f).
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
    intros. simp S... split.
    { intros. apply ex_derive_const. }
    apply functional_extensionality.
    intros. simp Dtm... unfold compose. rewrite Derive_const... }
  { (* Add *)
    simp S in *. intros.
    pose proof (IHt1 Γ' sb h1 h2 H) as [Hex1 H1]; clear IHt1.
    pose proof (IHt2 Γ' sb h1 h2 H) as [Hex2 H2]; clear IHt2.
    split.
    { intros.
      specialize Hex1 with x.
      specialize Hex2 with x.
      apply (ex_derive_plus _ _ _ Hex1 Hex2). }
    { apply functional_extensionality...
      simp Dtm. simpl. unfold compose in *.
      eapply equal_f in H1; eapply equal_f in H2.
      rewrite H1; rewrite H2.
      apply injective_projections...
      rewrite Derive_plus... }
    }
  { (* Tuples *)
    simpl. intros.
    pose proof (IHt1 Γ' sb h1 h2 H) as H1'; clear IHt1.
    pose proof (IHt2 Γ' sb h1 h2 H) as H2'; clear IHt2.
    simp S.
    exists (⟦ substitute sb t1 ⟧ₜₘ ∘ h1).
    exists (⟦ Dtm (substitute sb t1) ⟧ₜₘ ∘ h2).
    exists (⟦ substitute sb t2 ⟧ₜₘ ∘ h1).
    exists (⟦ Dtm (substitute sb t2) ⟧ₜₘ ∘ h2)... }
  { (* Projection 1 *)
    intros. unfold compose in *.
    specialize IHt with Γ' sb h1 h2.
    pose proof (IHt H) as IHt'; clear IHt.
    simp S in IHt'.
    destruct IHt' as [f1 [f2 [g1 [g2 [S1 [S2 [H1 H2]]]]]]]...
    erewrite S_cong; try (apply S1);
    apply functional_extensionality_dep; intros;
    eapply equal_f in H1; eapply equal_f in H2.
    { rewrite H1... }
    { simp Dtm... rewrite H2... } }
  { (* Projection 2 *)
    intros. unfold compose in *.
    specialize IHt with Γ' sb h1 h2.
    pose proof (IHt H) as IHt'; clear IHt.
    simp S in IHt'.
    destruct IHt' as [f1 [f2 [g1 [g2 [S1 [S2 [H1 H2]]]]]]]...
    erewrite S_cong; try (apply S2);
    apply functional_extensionality_dep; intros;
    eapply equal_f in H1; eapply equal_f in H2.
    { rewrite H1... }
    { simp Dtm... rewrite H2... } }
  { (* Case *)
    intros.
    pose proof (IHt1 Γ' sb h1 h2 H) as IH1; clear IHt1.
    pose proof (IHt2 Γ' sb h1 h2 H) as IH2; clear IHt2.
    pose proof (IHt3 Γ' sb h1 h2 H) as IH3; clear IHt3.
    simp S in IH1. simpl. simp Dtm. simpl.
    fold denote_t Dt in *.
    destruct IH1 as [[Heq1 Heq2]|[Heq1 Heq2]].
    simp S in *.
    erewrite S_cong. apply IH2.
  2:{ extensionality x.
      eapply equal_f in Heq1.
      rewrite Heq1...
      unfold compose...
      admit. }
  2:{ extensionality x.
      eapply equal_f in Heq2.
      rewrite Heq2...
      unfold compose...
      admit. }
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
    fold denote_t Dt in *.
    exists (⟦ substitute sb t ⟧ₜₘ ∘ h1).
    exists (⟦ Dtm (substitute sb t) ⟧ₜₘ ∘ h2).
    split; unfold compose; extensionality x... }
  { (* Inl *)
    intros. simp S. right...
    fold denote_t Dt in *.
    exists (⟦ substitute sb t ⟧ₜₘ ∘ h1).
    exists (⟦ Dtm (substitute sb t) ⟧ₜₘ ∘ h2).
    split; unfold compose; extensionality x... }
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
  apply (fundamental [] [] Real f t id_sub).
  constructor.
Qed.
