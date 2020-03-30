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
(* Require Import AD.Normalization. *)
Require Import AD.Denotation.
(* Require Import AD.Natural. *)
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
Equations S τ :
  (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop :=
S Real f g :=
  (forall (x : R), ex_derive f x) /\
  (fun r => g r) =
    (fun r => (f r, Derive f r));
S (σ × ρ) f g :=
  exists f1 f2 g1 g2,
  exists (s1 : S σ f1 f2) (s2 : S ρ g1 g2),
    (f = fun r => (f1 r, g1 r)) /\
    (g = fun r => (f2 r, g2 r));
S (σ → ρ) f g :=
  forall (g1 : R -> ⟦ σ ⟧ₜ)
    (g2 : R -> ⟦ Dt σ ⟧ₜ) (sσ : S σ g1 g2),
    S ρ (fun x => f x (g1 x))
      (fun x => g x (g2 x));
  (* forall (sσ : S σ (⟦s⟧ₜₘ ∘ denote_env ∘ h)
            (⟦Dtm s⟧ₜₘ ∘ denote_env ∘ Denv ∘ h)),
    S ρ (fun x => f x ((⟦s⟧ₜₘ ∘ denote_env ∘ h) x))
      (fun x => g x ((⟦Dtm s⟧ₜₘ ∘ denote_env ∘ Denv ∘ h) x)); *)
S (σ <+> ρ) f g :=
  (exists g1 g2,
    S σ g1 g2 /\
      f = Datatypes.inl ∘ g1 /\
      g = Datatypes.inl ∘ g2) \/
  (exists g1 g2,
    S ρ g1 g2 /\
      f = Datatypes.inr ∘ g1 /\
      g = Datatypes.inr ∘ g2).

Inductive instantiation : forall Γ,
    (R -> ⟦ Γ ⟧ₜₓ) -> (R -> ⟦ Dctx Γ ⟧ₜₓ) -> Prop :=
  | inst_empty :
      instantiation [] (Basics.const tt) (Basics.const tt)
  | inst_cons :
      forall Γ τ,
      forall g1 g2,
      forall (sb: R -> ⟦ Γ ⟧ₜₓ),
      forall (Dsb: R -> ⟦ Dctx Γ ⟧ₜₓ),
        instantiation Γ sb Dsb ->
        S τ g1 g2 ->
        instantiation (τ::Γ)
          (fun r => (g1 r, sb r)) (fun r => (g2 r, Dsb r)).

(* Inductive instantiation :
  forall {Γ Γ'}, (R -> Env Γ') -> sub Γ Γ' -> Prop :=
  | inst_empty : forall h, @instantiation [] [] h id_sub
  | inst_cons :
        forall {Γ Γ' τ} {s : sub Γ Γ'},
        forall {t : tm Γ' τ} h,
      instantiation h s ->
        (* value t -> *)
        (S Γ' h τ (⟦ t ⟧ₜₘ ∘ denote_env ∘ h)
          (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h)) ->
        instantiation h (cons_sub t s). *)

(* Equations instantiation Γ {Γ'} (f : R -> Env Γ) : sub Γ Γ' -> Prop :=
instantiation nil f sb := True;
instantiation (τ :: Γ) f sb :=
    S Γ (shave_env ∘ f) τ
      (⟦hd_sub sb⟧ₜₘ ∘ denote_env ∘ shave_env ∘ f)
      (⟦Dtm (hd_sub sb)⟧ₜₘ ∘ denote_env ∘ Denv ∘ shave_env ∘ f) /\
    instantiation Γ (shave_env ∘ f) (tl_sub sb). *)

Lemma inst_eq : forall Γ f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> instantiation Γ f1 f2 = instantiation Γ g1 g2.
Proof. intros; rewrites. Qed.

Lemma S_eq : forall τ f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> S τ f1 f2 = S τ g1 g2.
Proof. intros; rewrites. Qed.

(* Lemma S_soundness : forall Γ τ (t t' : tm Γ τ) h,
  (t ⇓ t') ->
    S Γ h τ (⟦t⟧ₜₘ ∘ denote_env ∘ h) (⟦Dtm t⟧ₜₘ ∘ denote_env ∘ Denv ∘ h)
      = S Γ h τ (⟦t'⟧ₜₘ ∘ denote_env ∘ h) (⟦Dtm t'⟧ₜₘ ∘ denote_env ∘ Denv ∘ h).
Proof with quick.
  intros.
  pose proof (natural_soundness _ _ t t' H) as Heq.
  (* pose proof (natural_soundness _ _ (Dtm t) (Dtm t')
    (D_natural _ _ _ _ H)) as Heq'. *)
  rewrites.
  admit.
Admitted. *)

(*
  Plain words:
    Given a context Γ for which t is well-typed (Γ ⊢ t : τ) and every typing
    assignment in the context is in the relation S, applying the substitutions
    to the term t is also in the relation S.
*)
Lemma fundamental :
  forall Γ τ,
  forall (t : tm Γ τ),
  forall (sb : R -> ⟦ Γ ⟧ₜₓ),
  forall (Dsb : R -> ⟦ Dctx Γ ⟧ₜₓ),
  (* forall (sb : ⟦ Γ' ⟧ₜₓ -> ⟦ Γ ⟧ₜₓ),
  forall (Dsb : ⟦ Dctx Γ' ⟧ₜₓ -> ⟦ Dctx Γ ⟧ₜₓ), *)
  (* forall (h : R -> Env Γ'), *)
  instantiation Γ sb Dsb ->
  S τ (⟦t⟧ₜₘ ∘ sb)
    (⟦Dtm t⟧ₜₘ ∘ Dsb).
Proof with quick.
  unfold compose.
  intros Γ τ t sb Dsb.
  (* pose proof (H τ) as H'. clear H. *)
  dependent induction t; unfold compose in *.
  { (* Var *)
    (* Using Inductive Instantiation *)
    intros. dependent induction v; dependent induction H;
      quick; simp cons_sub Dtm... }
  { (* App *)
    intros.
    specialize IHt1 with sb Dsb; specialize IHt2 with sb Dsb.
    pose proof (IHt1 H) as IHt1'; clear IHt1.
    pose proof (IHt2 H) as IHt2'; clear IHt2...
    simp S in IHt1'. }
  { (* Abs *)
    intros. simp S. intros.
    unfold compose in *.
    simpl. simp Dtm...
    specialize IHt with
      (fun r => (g1 r, sb r)) (fun r => (g2 r, Dsb r))...
    eapply IHt. constructor; assumption. }
  { (* Const *)
    quick. simp S... unfold compose.
    splits...
    { subst. apply ex_derive_const. }
    { apply functional_extensionality...
      simp Dtm...
      rewrite Derive_const... } }
  { (* Add *)
    simpl in *. intros.
    pose proof (IHt1 sb Dsb) as H1.
    pose proof (IHt2 sb Dsb) as H2.
    simp S in H1; simp S in H2.
    autorewrite with S...
    pose proof (H1 H) as [Heq1 Heq1']; clear H1.
    pose proof (H2 H) as [Heq2 Heq2']; clear H2.
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
    pose proof (IHt1 sb Dsb H) as H1'; clear IHt1.
    pose proof (IHt2 sb Dsb H) as H2'; clear IHt2.
    exists (⟦ t1 ⟧ₜₘ ∘ sb );
      exists (⟦ Dtm t1 ⟧ₜₘ ∘ Dsb).
    exists (⟦ t2 ⟧ₜₘ ∘ sb );
      exists (⟦ Dtm t2 ⟧ₜₘ ∘ Dsb).
    (* exists (substitute sb t1); exists (substitute sb t2). *)
    unfold compose.
    exists H1'; exists H2'... }
  { (* Projection 1 *)
    intros. unfold compose in *... simp Dtm... simpl.
    specialize IHt with sb Dsb.
    simp S in IHt; pose proof (IHt H) as H'; clear IHt.
    destruct H' as [f1 [f2 [g1 [g2 [Hs1 [Hs2 [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x...
    { eapply equal_f in Heq1. erewrite Heq1... }
    { eapply equal_f in Heq2. erewrite Heq2... } }
  { (* Projection 2 *)
    intros. unfold compose in *... simp Dtm... simpl.
    specialize IHt with sb Dsb.
    simp S in IHt; pose proof (IHt H) as H'; clear IHt.
    destruct H' as [f1 [f2 [g1 [g2 [Hs1 [Hs2 [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x...
    { eapply equal_f in Heq1. erewrite Heq1... }
    { eapply equal_f in Heq2. erewrite Heq2... } }
  { (* Case *)
    intros.
    pose proof (IHt1 sb Dsb H) as IH1; clear IHt1.
    pose proof (IHt2 sb Dsb H) as IH2; clear IHt2.
    pose proof (IHt3 sb Dsb H) as IH3; clear IHt3.
    simp S in *. simpl. simp Dtm. simpl.
    destruct IH1 as [[g1 [g2 H']]|[g1 [g2 H']]].
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
    intros... simp S... left...
    exists (⟦ t ⟧ₜₘ ∘ sb );
      exists (⟦ Dtm t ⟧ₜₘ ∘ Dsb)... }
  { (* Inl *)
    intros... simp S... right...
    exists (⟦ t ⟧ₜₘ ∘ sb );
      exists (⟦ Dtm t ⟧ₜₘ ∘ Dsb)... }
Qed.

Lemma S_correct_R :
  forall Γ (t : tm Γ Real) (f : R -> Env Γ),
  S Real (fun r => (⟦ t ⟧ₜₘ (denote_env (f r))))
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

Inductive reals : Ctx -> Prop :=
  | reals_empty : reals []
  | reals_cons : forall Γ, tm Γ Real -> reals Γ -> reals (Real::Γ).

Theorem semantic_correct_R :
  forall Γ,
  forall (t : tm Γ Real),
    reals Γ ->
    forall (f : R -> Env Γ),
    (⟦ Dtm t ⟧ₜₘ ∘ denote_env ∘ Denv ∘ f) =
      fun r => (⟦ t ⟧ₜₘ (denote_env (f r)),
      Derive (fun (x : R) => ⟦ t ⟧ₜₘ (denote_env (f x))) r).
Proof with quick.
  intros.
  (* eapply H'. *)
  (* unfold compose in *. *)
  generalize dependent t...
  eapply S_correct_R.
  eapply fundamental.
  induction H...
  { erewrite inst_eq.
  2:{ extensionality r; remember (f r);
        dependent destruction e; simp denote_env; reflexivity. }
  2:{ extensionality r; remember (f r);
        dependent destruction e; quick; simp denote_env; reflexivity. }
    fold (@Basics.const unit R tt); constructor. }
  { erewrite inst_eq.
  2:{ extensionality r. remember (f r).
        dependent destruction e. simp denote_env; reflexivity. }
    constructor... }
  (* generalize dependent f. *)
  induction H...
  { exists (Basics.const env_nil).
    apply S_correct_R.
    eapply fundamental...
    (* assert (f = Basics.const env_nil).
    { unfold Basics.const. extensionality x.
      remember (f x). dependent destruction e... } *)
    rewrites; unfold Basics.const in *...
    simp denote_env.
    fold (@Basics.const unit R tt); constructor. }
  {
    specialize IHreals with X as [f IH].
    exists (env_cons X ∘ f).
    apply S_correct_R. unfold compose.
    erewrite S_eq.
  2:{ extensionality r. simp denote_env. reflexivity. }
  2:{ extensionality r... simp denote_env. reflexivity. }
    eapply fundamental...
    constructor.
    all: admit. }
Admitted.
