Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Arith.PeanoNat.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Init.Datatypes.
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
Require Import AD.Denotation.

Local Open Scope program_scope.
Local Open Scope R_scope.

(*
  Using a logical relation on the denotational semantics adapted from:
    Correctness of Automatic Differentiation via
      Diffeologies and Categorical Gluing by Huot, Staton and Vakar.
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

Lemma inst_eq : forall Γ f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> instantiation Γ f1 f2 = instantiation Γ g1 g2.
Proof. intros; rewrites. Qed.

Lemma S_eq : forall τ f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> S τ f1 f2 = S τ g1 g2.
Proof. intros; rewrites. Qed.

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
  instantiation Γ sb Dsb ->
  S τ (fun x => ⟦t⟧ₜₘ (sb x))
    (fun x => ⟦Dtm (t)⟧ₜₘ (Dsb x)).
Proof with quick.
  unfold compose.
  intros Γ τ t sb Dsb.
  (* pose proof (H τ) as H'. clear H. *)
  induction t; unfold compose in *.
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
  forall Γ (t : tm Γ Real),
  forall (f1 : R -> ⟦ Γ ⟧ₜₓ),
  forall  (f2 : R -> ⟦ Dctx Γ ⟧ₜₓ),
  S Real (fun r => ⟦ t ⟧ₜₘ (f1 r))
    (fun r => ⟦ Dtm t ⟧ₜₘ (f2 r)) ->
  (forall x, ex_derive (fun x => ⟦ t ⟧ₜₘ (f1 x)) x) /\
  (⟦ Dtm t ⟧ₜₘ ∘ f2) =
  fun r => (⟦ t ⟧ₜₘ (f1 r),
    Derive (fun x => ⟦ t ⟧ₜₘ (f1 x)) r).
Proof with quick.
  intros. simp S in H.
Qed.

Equations gen (n : nat) : R -> ⟦ repeat Real n ⟧ₜₓ :=
gen O r := tt;
gen (Datatypes.S n) r := (r, gen n r).

Equations Dgen (n : nat) : R -> ⟦ Dctx (repeat Real n) ⟧ₜₓ :=
Dgen O r := tt;
Dgen (Datatypes.S n) r := ((r, 1), Dgen n r).

Equations D n
  (f : R -> ⟦ repeat Real n ⟧ₜₓ): R -> ⟦ map Dt (repeat Real n) ⟧ₜₓ :=
D 0 f r := f r;
D (Datatypes.S n) f r :=
  (((fst ∘ f) r, Derive (fst ∘ f) r), D n (snd ∘ f) r).

Equations hd_env {n} : Env (Real :: repeat Real n) -> tm (repeat Real n) Real :=
hd_env (env_cons t E') := t.

Equations tl_env {n} : Env (Real :: repeat Real n) -> Env (repeat Real n) :=
tl_env (env_cons t E) := E.

Equations DE n
  (f : R -> Env (repeat Real n)): R -> Env (map Dt (repeat Real n)) :=
DE 0 f r := f r;
DE (Datatypes.S n) f r :=
  (env_cons (Dtm ((hd_env ∘ f) r)) (DE n (tl_env ∘ f) r)).

Inductive differentiable : forall n, (R -> ⟦ repeat Real n ⟧ₜₓ) -> Prop :=
  | differentiable_0 : differentiable 0 (fun _ => tt)
  | differentiable_Sn :
    forall n,
    forall (f : R -> ⟦ repeat Real n ⟧ₜₓ),
    forall (g : R -> R),
      differentiable n f ->
      (forall x, ex_derive g x) ->
      differentiable (Datatypes.S n) (fun x => (g x, f x)).

Definition diff_eq : forall n f1 f2,
  f1 = f2 -> differentiable n f1 = differentiable n f2.
Proof. quick; rewrite H; trivial. Qed.

Lemma S_tm_derivable :
    forall n (t : R -> tm (repeat Real n) Real),
    forall (ctx : R -> Env (repeat Real n)),
  forall x, ex_derive (fun x => ⟦ t x ⟧ₜₘ ⟦ctx x⟧ₑ) x.
Proof.
  intros.
  (* apply S_correct_R. *)
  (* specialize H with (repeat Real n) t (denote_env ∘ ctx)
    (denote_env ∘ Denv ∘ ctx). *)
  (* eapply fundamental. *)
  admit.
Admitted.

Lemma S_denote_derivable :
  forall n,
  forall (f : R -> Env (repeat Real n)),
  differentiable n (denote_env ∘ f).
Proof with quick.
  intros.
  induction n.
  { assert (Heq: f = fun _ => env_nil).
    { extensionality x. remember (f x). dependent destruction e... }
    rewrite Heq; clear Heq.
    unfold compose.
    eapply differentiable_0. }
  { simpl in f.
    assert (Heq: f = fun r => env_cons (hd_env (f r)) (tl_env (f r))).
    { extensionality x. remember (f x). dependent destruction e... }
    rewrite Heq. clear Heq.
    unfold compose.
    (* rewrite Heq. *)
    erewrite diff_eq.
    instantiate
      (1:=fun r => (⟦(hd_env (f r))⟧ₜₘ ⟦(tl_env (f r))⟧ₑ, ⟦(tl_env (f r))⟧ₑ)).
    constructor.
    { eapply IHn. }
    (* pose proof S_tm_derivable. *)
    { apply (S_tm_derivable n (hd_env ∘ f) (tl_env ∘ f)). }
    { extensionality x... } }
Qed.

Theorem semantic_correct_R :
  forall n,
  forall (f : R -> ⟦ repeat Real n ⟧ₜₓ),
  forall (t : tm (repeat Real n) Real),
    differentiable n f ->
    (⟦ Dtm t ⟧ₜₘ ∘ D n f) =
      (fun r => (⟦ t ⟧ₜₘ (f r),
        Derive (fun (x : R) => ⟦ t ⟧ₜₘ (f x)) r)).
Proof with quick.
  intros...
  (* exists (gen n); exists (Dgen n). *)
  (* pose proof (S_denote_derivable n f). *)
  unfold compose.
  eapply S_correct_R.
  eapply fundamental.
  clear t.
  induction n...
  { erewrite inst_eq;
      try (extensionality r).
  2:{ remember (f r) as e. dependent destruction e.
      (* simpl. simp denote_env.  *)
      reflexivity. }
  2:{ simp D. remember (f r) as e. dependent destruction e.
      (* simpl. simp denote_env.  *)
      reflexivity. }
    fold (@Basics.const unit R tt); constructor. }
  { erewrite inst_eq;
      try (extensionality r).
  2:{ instantiate (1:=
        (* fun r => (⟦(hd_env (f r))⟧ₜₘ ⟦(tl_env (f r))⟧ₑ, ⟦(tl_env (f r))⟧ₑ)). *)
        fun r => (fst (f r), snd (f r))).
        apply injective_projections; quick; remember (f r);
          dependent elimination e... }
  2:{ simp D. unfold compose. reflexivity. }
    dependent destruction H.
    constructor...
    simp S. splits... }
Qed.
