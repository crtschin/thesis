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
  (exists g1 g2,
    (* forall (t : tm Γ σ), *)
    forall (s: S Γ h σ g1 g2),
      f = Datatypes.inl ∘ g1 /\
      g = Datatypes.inl ∘ g2) \/
  (exists g1 g2,
    (* forall (t : tm Γ ρ), *)
    forall (s: S Γ h ρ g1 g2),
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
        (* value t -> *)
        (forall (h : R -> Env Γ'), S Γ' h τ (⟦ t ⟧ₜₘ ∘ denote_env ∘ h)
          (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h)) ->
        instantiation (cons_sub t s).

(* Equations instantiation Γ {Γ'} (f : R -> Env Γ') : sub Γ Γ' -> Prop :=
instantiation nil f s := True;
instantiation (τ :: Γ) f s :=
  exists g1 g2,
    S τ g1 g2 /\
      g1 = (⟦hd_sub s⟧ₜₘ ∘ denote_env ∘ f) /\
      g2 = (⟦Dtm (hd_sub s)⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) /\
      instantiation Γ f (tl_sub s). *)

Lemma S_cong : forall Γ τ f1 f2 g1 g2 h,
  g1 = f1 -> g2 = f2 -> S Γ h τ f1 f2 = S Γ h τ g1 g2.
Proof. intros; rewrites. Qed.
(*
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
Admitted. *)

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

(* Lemma S_app : forall Γ τ σ t1 t2 h1 h1' h2 h2',
  S Γ σ t2 h2 h2' ->
    S Γ (σ → τ) t1 h1 h1' ->
    S Γ τ (app Γ τ σ t1 t2) (fun r => (h1 r) (h2 r)) (fun r => (h1' r) (h2' r)).
Proof with quick.
  intros...
  simp S in H0.
Admitted. *)


(*
  Plain words:
    Given a context Γ for which t is well-typed (Γ ⊢ t : τ) and every typing
    assignment in the context is in the relation S, applying the substitutions
    to the term t is also in the relation S.
*)
Lemma fundamental :
  forall Γ Γ' τ
    (t : tm Γ τ) (sb : sub Γ Γ') (h : R -> Env Γ'),
  instantiation sb ->
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
    intros. induction v; dependent induction H; quick; simp cons_sub.
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
    { erewrite S_cong.
      simp instantiation in H.
      unfold tl_sub... unfold tl_sub... } *)
    }
  { (* App *)
    intros...
    simp S in IHt1... simp Dtm...
    specialize IHt1 with Γ' sb h; specialize IHt2 with Γ' sb h.
    pose proof (IHt1 H); pose proof (IHt2 H).
    clear IHt1; clear IHt2.
    simp S in H0.
    (* unfold compose in *.
    apply H0. *)
    (* specialize H0 with (substitute sb t2).
    destruct H0 as [g1 [g2 H']].
    eapply H'. *)

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
    intros. simp S. intros; subst...
    simpl (substitute sb (abs Γ τ σ t)).
    simp Dtm...
    unfold compose in *.
    erewrite S_cong.
    specialize IHt with Γ' (cons_sub s sb) h.
    (* specialize IHt with (σ::Γ')
      (substitute_lifted sb) (fun r => env_cons s (h r)). *)
    eapply IHt. constructor...
    exists (⟦ s ⟧ₜₘ ∘ h1).
    exists (⟦ Dtm s ⟧ₜₘ ∘ h2).
    exists (⟦ substitute (cons_sub s sb) t ⟧ₜₘ ∘ h1).
    exists (⟦ Dtm (substitute (cons_sub s sb) t) ⟧ₜₘ ∘ h2)...
    splits...

    (* simp instantiation in H. *)
    (* With existentials for context in relation *)
    (* induction H.
    exists []; exists f... subst... *)

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
    pose proof (H1 h) as [Heq1 Heq1']; clear H1.
    pose proof (H2 h) as [Heq2 Heq2']; clear H2.
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
    erewrite S_cong; quick; extensionality x;
      eapply equal_f in Heq1; eapply equal_f in Heq2...
    rewrite Heq1...
    rewrite Heq2... }
  { (* Projection 2 *)

    intros. unfold compose in *... simp Dtm... simpl.
    specialize IHt with Γ' sb h.
    simp S in IHt; pose proof (IHt H) as H'; clear IHt.
    destruct H' as [f1 [f2 [g1 [g2 [Hs1 [Hs2 [Heq1 Heq2]]]]]]].
    erewrite S_cong; quick; extensionality x;
      eapply equal_f in Heq1; eapply equal_f in Heq2...
    rewrite Heq1...
    rewrite Heq2... }
  { (* Case *)
    intros.
    pose proof (IHt1 Γ' g sb H) as IH1; clear IHt1.
    simp S in IH1. simpl. simp Dtm. simpl.
    inversion IH1.
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
    intros... simp S... left...
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
