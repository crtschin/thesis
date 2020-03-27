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
Require Import AD.Natural.
(* Require Import AD.Tangent. *)

Local Open Scope program_scope.
Local Open Scope R_scope.

(*
  Relation between
    denotation function of term
      (the function the term describes)
    denotation function of macro term
      (the derivative of the function the term describes)
*)
Equations S (Γ : list ty) (h : R -> Env Γ) τ :
  (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop :=
S Γ h Real f g :=
  (forall (x : R), ex_derive f x) /\
  (fun r => g r) =
    (fun r => (f r, Derive f r));
S Γ h (σ × ρ) f g :=
  exists f1 f2 g1 g2,
  exists (s1 : S Γ h σ f1 f2) (s2 : S Γ h ρ g1 g2),
    (f = fun r => (f1 r, g1 r)) /\
    (g = fun r => (f2 r, g2 r));
S Γ h (σ → ρ) f g :=
  (* exists h, *)
  forall (s : tm Γ σ),
  forall (sσ : S Γ h σ (⟦s⟧ₜₘ ∘ denote_env ∘ h)
            (⟦Dtm s⟧ₜₘ ∘ denote_env ∘ Denv ∘ h)),
    (* (fun x => h1 x) = (fun x => f x (g1 x)) /\
    (fun x => h2 x) = (fun x => g x (g2 x)); *)
    (* value s -> *)
    (* g1 = (⟦s⟧ₜₘ ∘ denote_env ∘ h) -> *)
    (* g2 = (⟦Dtm s⟧ₜₘ ∘ denote_env ∘ Denv ∘ h) -> *)
    S Γ h ρ (fun x => f x ((⟦s⟧ₜₘ ∘ denote_env ∘ h) x))
      (fun x => g x ((⟦Dtm s⟧ₜₘ ∘ denote_env ∘ Denv ∘ h) x));
S Γ h (σ <+> ρ) f g :=
  (exists (t : tm Γ σ),
    S Γ h σ (⟦t⟧ₜₘ ∘ denote_env ∘ h) (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h) /\
      f = Datatypes.inl ∘ (⟦t⟧ₜₘ ∘ denote_env ∘ h) /\
      g = Datatypes.inl ∘ (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h)) \/
  (exists (t : tm Γ ρ),
    S Γ h ρ (⟦t⟧ₜₘ ∘ denote_env ∘ h) (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h) /\
      f = Datatypes.inr ∘ (⟦t⟧ₜₘ ∘ denote_env ∘ h) /\
      g = Datatypes.inr ∘ (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h)).

(* Inductive instantiation :
  forall {Γ Γ'}, (⟦ Γ' ⟧ₜₓ -> ⟦ Γ ⟧ₜₓ) -> Prop :=
  | inst_empty : @instantiation [] [] Datatypes.id
  | inst_cons : forall {Γ Γ' τ} (sb: ⟦ Γ' ⟧ₜₓ -> ⟦ Γ ⟧ₜₓ) {g1 g2},
      instantiation sb ->
      (S τ g1 g2) ->
      instantiation (fun (ctx: ⟦ τ::Γ' ⟧ₜₓ) => (sb (snd ctx))). *)

Inductive instantiation :
  forall {Γ Γ'}, (R -> Env Γ') -> sub Γ Γ' -> Prop :=
  | inst_empty : forall h, @instantiation [] [] h id_sub
  | inst_cons :
        forall {Γ Γ' τ} {s : sub Γ Γ'},
        forall {t : tm Γ' τ} h,
      instantiation h s ->
        (* value t -> *)
        (S Γ' h τ (⟦ t ⟧ₜₘ ∘ denote_env ∘ h)
          (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h)) ->
        instantiation h (cons_sub t s).

(* Equations instantiation Γ {Γ'} (f : R -> Env Γ) : sub Γ Γ' -> Prop :=
instantiation nil f sb := True;
instantiation (τ :: Γ) f sb :=
    S Γ (shave_env ∘ f) τ
      (⟦hd_sub sb⟧ₜₘ ∘ denote_env ∘ shave_env ∘ f)
      (⟦Dtm (hd_sub sb)⟧ₜₘ ∘ denote_env ∘ Denv ∘ shave_env ∘ f) /\
    instantiation Γ (shave_env ∘ f) (tl_sub sb). *)

Lemma S_eq : forall Γ τ f1 f2 g1 g2 h,
  g1 = f1 -> g2 = f2 -> S Γ h τ f1 f2 = S Γ h τ g1 g2.
Proof. intros; rewrites. Qed.

Lemma S_soundness : forall Γ τ (t t' : tm Γ τ) h,
  (t ⇓ t') ->
    S Γ h τ (⟦t⟧ₜₘ ∘ denote_env ∘ h) (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h)
      = S Γ h τ (⟦t'⟧ₜₘ ∘ denote_env ∘ h) (⟦Dtm t'⟧ₜₘ ∘ denote_env ∘ Denv ∘ h).
Proof with quick.
  intros.
  pose proof (natural_soundness _ _ t t' H) as Heq.
  pose proof (natural_soundness _ _ (Dtm t) (Dtm t')
    (D_natural _ _ _ _ H)) as Heq'.
  rewrites.
Qed.

(*
  Plain words:
    Given a context Γ for which t is well-typed (Γ ⊢ t : τ) and every typing
    assignment in the context is in the relation S, applying the substitutions
    to the term t is also in the relation S.
*)
Lemma fundamental :
  forall Γ Γ' τ
    (t : tm Γ τ) (sb : sub Γ Γ') (h : R -> Env Γ'),
  instantiation h sb ->
  S Γ' h τ
    (⟦substitute sb t⟧ₜₘ ∘ denote_env ∘ h)
    (⟦Dtm (substitute sb t)⟧ₜₘ ∘ denote_env ∘ Denv ∘ h).
Proof with quick.
  intros Γ Γ' τ t sb h H.
  generalize dependent Γ'.
  (* pose proof (H τ) as H'. clear H. *)
  dependent induction t; unfold compose in *.
  { (* Var *)
    (* Using Inductive Instantiation *)
    intros. induction v; dependent induction H;
      quick; simp cons_sub.
    (* { dependent induction H... }
    { quick. dependent induction H...
      simp cons_sub. } *)

    (* Using Equation Instantiation *)
    (* induction v; intros;
      simp instantiation in H;
      (* specialize H with g; *)
      destruct H as [g1 [g2 H]];
      destruct H as [H [Heq1 [Heq2 H']]]; subst.
    { unfold hd_sub in H... }
    { erewrite S_eq.
      simp instantiation in H.
      unfold tl_sub... unfold tl_sub... } *)
    }
  { (* App *)
    intros.
    specialize IHt1 with Γ' sb h; specialize IHt2 with Γ' sb h.
    pose proof (IHt1 H) as IHt1'; clear IHt1.
    pose proof (IHt2 H) as IHt2'; clear IHt2...
    simp S in IHt1'.
    (* pose proof (IHt1' _ IHt2').
    simp Dtm... *)

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
    intros. simp S. intros.
    (* pose proof (H0 Γ' τ (app _ _ _ (substitute sb (abs Γ τ σ t)) s)
      (substitute (|s|) (substitute (substitute_lifted sb) t)) h). *)
    unfold compose in *.
    simpl. simp Dtm...
    specialize IHt with Γ' (cons_sub s sb) h.
    erewrite S_eq.
    eapply IHt. constructor...
    { extensionality x.
      rewrite <- 2 denote_sub_commutes...
      unfold hd_sub. simp cons_sub substitute_lifted...
      assert (H': denote_sub (tl_sub (cons_sub s sb)) = denote_sub sb).
      { quick. }
      erewrite H'; clear H'...
      assert (H': ⟦ sb ⟧ₛ ⟦ h x ⟧ₑ =
        ⟦ tl_sub (substitute_lifted sb) ⟧ₛ (⟦ s ⟧ₜₘ ⟦ h x ⟧ₑ, ⟦ h x ⟧ₑ)).
      { erewrite denote_sub_elim... }
      erewrite H'... }
    { extensionality x.
      (* TODO: Suspect *)
      erewrite D_sub_cons'.
      erewrite D_sub_lift'.
      rewrite <- 2 denote_sub_commutes...
      unfold hd_sub. simp cons_sub substitute_lifted...
      assert (H': denote_sub (tl_sub (cons_sub (Dtm s) (Dsub' sb)))
        = denote_sub (Dsub' sb)).
      { quick. }
      erewrite H'; clear H'...
      assert (H': (⟦ Dtm s ⟧ₜₘ ⟦ Denv (h x) ⟧ₑ, ⟦ Dsub' sb ⟧ₛ ⟦ Denv (h x) ⟧ₑ)
        = (⟦ Dtm s ⟧ₜₘ ⟦ Denv (h x) ⟧ₑ,
          ⟦ tl_sub (substitute_lifted (Dsub' sb)) ⟧ₛ
            (⟦ Dtm s ⟧ₜₘ ⟦ Denv (h x) ⟧ₑ, ⟦ Denv (h x) ⟧ₑ))).
      { apply injective_projections... erewrite denote_sub_elim... }
      (* rewrite <- H'. *)
      admit.
      }
    (* exists (substitute sb (abs _ _ _ t)). *)
    (* simpl (substitute sb (abs Γ τ σ t)). *)
    (* erewrite S_soundness. unfold compose in *.
    apply IHt.
    instantiate (1:=cons_sub s sb).
    constructor... *)
    (* instantiate (1:=cons_sub s sb). *)
    (* instantiate (1:=compose_sub_sub (| s |) (substitute_lifted sb)). *)
    }
  { (* Const *)
    quick. simp S... unfold compose.
    splits...
    { subst. apply ex_derive_const. }
    { apply functional_extensionality...
      simp Dtm...
      rewrite Derive_const... } }
  { (* Add *)
    simpl in *. intros.
    pose proof (IHt1 Γ' sb h H) as H1.
    pose proof (IHt2 Γ' sb h H) as H2.
    simp S in H1; simp S in H2.
    autorewrite with S...
    pose proof (H1) as [Heq1 Heq1']; clear H1.
    pose proof (H2) as [Heq2 Heq2']; clear H2.
    unfold compose in *.
    splits...
    { apply (ex_derive_plus _ _ _ (Heq1 x) (Heq2 x)). }
    { simp Dtm. simpl.
      extensionality x.
      eapply equal_f in Heq1'.
      eapply equal_f in Heq2'.
      rewrite Heq1'. rewrite Heq2'...
      rewrite Derive_plus... } }
  { (* Tuples *)
    intros... simp S.
    pose proof (IHt1 Γ' sb h H) as H1'; clear IHt1.
    pose proof (IHt2 Γ' sb h H) as H2'; clear IHt2.
    exists (⟦substitute sb t1⟧ₜₘ ∘ denote_env ∘ h);
      exists (⟦Dtm (substitute sb t1)⟧ₜₘ ∘ denote_env ∘ Denv ∘ h).
    exists (⟦substitute sb t2⟧ₜₘ ∘ denote_env ∘ h);
      exists (⟦Dtm (substitute sb t2)⟧ₜₘ ∘ denote_env ∘ Denv ∘ h).
    (* exists (substitute sb t1); exists (substitute sb t2). *)
    unfold compose.
    exists H1'; exists H2'... }
  { (* Projection 1 *)
    intros. unfold compose in *... simp Dtm... simpl.
    specialize IHt with Γ' sb h.
    simp S in IHt; pose proof (IHt H) as H'; clear IHt.
    destruct H' as [f1 [f2 [g1 [g2 [Hs1 [Hs2 [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x;
      eapply equal_f in Heq1; eapply equal_f in Heq2...
    rewrite Heq1...
    rewrite Heq2... }
  { (* Projection 2 *)
    intros. unfold compose in *... simp Dtm... simpl.
    specialize IHt with Γ' sb h.
    simp S in IHt; pose proof (IHt H) as H'; clear IHt.
    destruct H' as [f1 [f2 [g1 [g2 [Hs1 [Hs2 [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x;
      eapply equal_f in Heq1; eapply equal_f in Heq2...
    rewrite Heq1...
    rewrite Heq2... }
  { (* Case *)
    intros.
    pose proof (IHt1 Γ' sb h H) as IH1; clear IHt1.
    pose proof (IHt2 Γ' sb h H) as IH2; clear IHt2.
    pose proof (IHt3 Γ' sb h H) as IH3; clear IHt3.
    simp S in *. simpl. simp Dtm. simpl.
    destruct IH1 as [[t H']|[t H']].
    { destruct H' as [Hs [Heq1 Heq2]].
      erewrite S_eq. eapply IH2...
      { extensionality x. eapply equal_f in Heq1.
        rewrite Heq1... }
      { extensionality x. eapply equal_f in Heq2.
        rewrite Heq2... } }
    { destruct H' as [Hs [Heq1 Heq2]].
      erewrite S_eq. eapply IH3...
      { extensionality x. eapply equal_f in Heq1.
        rewrite Heq1... }
      { extensionality x. eapply equal_f in Heq2.
        rewrite Heq2... } } }
  { (* Inl *)
    intros... simp S... left... }
  { (* Inl *)
    intros. simp S. right... }
Admitted.

Lemma S_correct_R :
  forall Γ (t : tm Γ Real) f,
  S Γ f Real (fun r => (⟦ t ⟧ₜₘ (denote_env (f r))))
    (fun r => ⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r)))) ->
  (⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) =
  fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
    Derive (fun x => ⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof with quick.
  intros. simp S in H.
  unfold compose in *. extensionality x.
  destruct H.
  eapply equal_f in H0.
  rewrite H0...
Qed.

Theorem semantic_correct_R :
  forall (t : tm [] Real) (f : R -> Env []),
  (fun r => ⟦ Dtm t ⟧ₜₘ (denote_env (Denv (f r)))) =
    fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
      Derive (fun (x : R) => ⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof with quick.
  intros.
  rewrite <- (app_sub_id [] Real t).
  apply S_correct_R.
  apply (fundamental [] [] Real t id_sub).
  constructor.
Qed.
