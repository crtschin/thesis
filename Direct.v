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
Require Vectors.Fin.
Import EqNotations.
Require Import CoLoR.Util.Vector.VecUtil.

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
  (R -> ⟦ τ ⟧ₜ) -> (R -> ⟦ Dt τ ⟧ₜ) -> Prop := {
S Real f g :=
  (forall (x : R), ex_derive f x) /\
  (fun r => g r) =
    (fun r => (f r, Derive f r));
S (Array n τ) f g :=
  forall i,
  exists f1 g1,
    S τ f1 g1 /\
    (fun r => denote_idx i (f r)) = f1 /\
    (fun r => denote_idx i (g r)) = g1;
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
      g = Datatypes.inr ∘ g2) }.

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
  induction t; simp denote_tm in *; unfold compose in *.
  { (* Var *)
    intros; dependent induction v; dependent induction H;
      quick; simp denote_tm cons_sub Dtm...
    erewrite S_eq. eapply IHv...
    all: extensionality x... }
  { (* App *)
    intros.
    specialize IHt1 with sb Dsb; specialize IHt2 with sb Dsb.
    pose proof (IHt1 H) as IHt1'; clear IHt1.
    pose proof (IHt2 H) as IHt2'; clear IHt2...
    simp S in IHt1'.
    erewrite S_eq. eapply IHt1'...
    all: extensionality x; simp denote_tm Dtm... }
  { (* Abs *)
    intros. simp S Dtm...
    specialize IHt with
      (fun r => (g1 r, sb r)) (fun r => (g2 r, Dsb r))...
    eapply IHt. constructor; assumption. }
  { (* Build *)
    intros. simp S...
    induction n.
    { (* Induction on n, Base case = 0
        Contradiction due to indices running from 1..n *)
      inversion i. }
    { (* Induction on n, IHn case
        Give instances *)
      pose proof (IHn (shave_fin t)) as H'; clear IHn.
      simp Dtm denote_tm in *...
      (* Destruct index,
        Cons case handled by IHn *)
      dependent destruction i...
      clear H'.
      exists (fun r =>
        (denote_tm ∘ t) (nat_to_fin n) (sb r));
      exists (fun r =>
        (denote_tm ∘ (Dtm ∘ t)) (nat_to_fin n) (Dsb r))... } }
  { (* Get *)
    quick.
    pose proof (IHt sb Dsb H) as H'; clear IHt.
    simp S in *. simp SA in *.
    induction n...
    { (* Induction on n, Base case = 0
        Contradiction due to indices running from 1..n *)
      inversion t. }
    { (* Induction on n, IHn case
        Rewrite using logical relation *)
      simp Dtm.
      specialize H' with t.
      destruct H' as [f1 [g1 [Hs1 [Heq1 Heq2]]]].
      subst. erewrite S_eq... } }
  { (* Const *)
    intros. simp S.
    splits...
    { (* Rewrite using 'denotation of (rval r) = const r' *)
      assert (H': (fun x0 : R => ⟦ rval Γ r ⟧ₜₘ (sb x0)) = const r).
      { extensionality r'; simp denote_tm; unfold const... }
      rewrite H'.
      (* const is derivable *)
      apply ex_derive_const. }
    { extensionality x...
      simp Dtm denote_tm...
      (* Rewrite using 'denotation of (rval r) = const r' *)
      assert (H': (fun x0 : R => ⟦ rval Γ r ⟧ₜₘ (sb x0)) = const r).
      { extensionality r'; simp denote_tm; unfold const... }
      rewrite H'. apply injective_projections...
      unfold const.
      rewrite Derive_const... } }
  { (* Add *)
    simpl in *. intros.
    (* Specialize IH to give evidence that
      subterms are derivable/give derivative *)
    pose proof (IHt1 sb Dsb H) as H1.
    pose proof (IHt2 sb Dsb H) as H2.
    simp S in H1; simp S in H2.
    destruct H1 as [Heq1 Heq1'].
    destruct H2 as [Heq2 Heq2'].
    (* Prove addition of subterms is derivable
      and give derivative value *)
    autorewrite with S.
    splits...
    { (* Addition is derivable given subterms are derivable *)
      apply (ex_derive_plus _ _ _ (Heq1 x) (Heq2 x)). }
    { simp Dtm. simpl.
      extensionality x.
      eapply equal_f in Heq1'.
      eapply equal_f in Heq2'.
      simp denote_tm.
      apply injective_projections;
        rewrite Heq1'; rewrite Heq2'...
      (* Rewrite using definition of denote_tm *)
      assert
        (H': (fun x0 : R => ⟦ add Γ t1 t2 ⟧ₜₘ (sb x0)) =
          fun x0 : R => ⟦ t1 ⟧ₜₘ (sb x0) + ⟦ t2 ⟧ₜₘ (sb x0)).
      { extensionality r; simp denote_tm... }
      rewrite H'.
      (* Derivative is addition of derivative of subterms *)
      rewrite Derive_plus... } }
  { (* Tuples *)
    intros... simp S.
    (* Give instances using IHs *)
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
    intros. simp Dtm.
    specialize IHt with sb Dsb.
    simp S in IHt; pose proof (IHt H) as H'; clear IHt.
    destruct H' as [f1 [f2 [g1 [g2 [Hs1 [Hs2 [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x...
    { eapply equal_f in Heq1. simp denote_tm. erewrite Heq1... }
    { eapply equal_f in Heq2. simp denote_tm. erewrite Heq2... } }
  { (* Projection 2 *)
    intros. simp Dtm.
    specialize IHt with sb Dsb.
    simp S in IHt; pose proof (IHt H) as H'; clear IHt.
    destruct H' as [f1 [f2 [g1 [g2 [Hs1 [Hs2 [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x...
    { eapply equal_f in Heq1. simp denote_tm. erewrite Heq1... }
    { eapply equal_f in Heq2. simp denote_tm. erewrite Heq2... } }
  { (* Case *)
    intros.
    pose proof (IHt1 sb Dsb H) as IH1; clear IHt1.
    pose proof (IHt2 sb Dsb H) as IH2; clear IHt2.
    pose proof (IHt3 sb Dsb H) as IH3; clear IHt3.
    simp S in *. simpl. simp Dtm. simpl.
    (* Either term denotates to inl or inr *)
    destruct IH1 as [[g1 [g2 H']]|[g1 [g2 H']]].
    { (* Scrutinee is inl *)
      destruct H' as [Hs [Heq1 Heq2]].
      erewrite S_eq. eapply IH2...
      { extensionality x. eapply equal_f in Heq1.
        simp denote_tm. rewrite Heq1... }
      { extensionality x. eapply equal_f in Heq2.
        simp denote_tm. rewrite Heq2... } }
    { (* Scrutinee is inr *)
      destruct H' as [Hs [Heq1 Heq2]].
      erewrite S_eq. eapply IH3...
      { extensionality x. eapply equal_f in Heq1.
        simp denote_tm. rewrite Heq1... }
      { extensionality x. eapply equal_f in Heq2.
        simp denote_tm. rewrite Heq2... } } }
  { (* Inl *)
    intros. simp S. left...
    exists (⟦ t ⟧ₜₘ ∘ sb );
      exists (⟦ Dtm t ⟧ₜₘ ∘ Dsb)... }
  { (* Inl *)
    intros. simp S. right...
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

Equations D n
  (f : R -> ⟦ repeat Real n ⟧ₜₓ): R -> ⟦ map Dt (repeat Real n) ⟧ₜₓ :=
D 0 f r := f r;
D (Datatypes.S n) f r :=
  (((fst ∘ f) r, Derive (fst ∘ f) r), D n (snd ∘ f) r).

Inductive differentiable : forall n, (R -> ⟦ repeat Real n ⟧ₜₓ) -> Prop :=
  | differentiable_0 : differentiable 0 (fun _ => tt)
  | differentiable_Sn :
    forall n (f : R -> ⟦ repeat Real n ⟧ₜₓ),
    forall (g : R -> R),
      differentiable n f ->
      (forall x, ex_derive g x) ->
      differentiable (Datatypes.S n) (fun x => (g x, f x)).

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
  unfold compose.
  eapply S_correct_R.
  eapply fundamental.
  clear t.
  (* Prove every term in the context is in the relation
    by induction on number of real terms in context *)
  induction n...
  { (* N = 0
      Prove f : R -> ⟦ repeat Real 0 ⟧ₜₓ is equal to 'const tt' *)
    erewrite inst_eq;
      try (extensionality r).
  2:{ remember (f r) as e. dependent destruction e.
      reflexivity. }
  2:{ simp D. remember (f r) as e. dependent destruction e.
      reflexivity. }
    fold (@Basics.const unit R tt); constructor. }
  { (* N = n + 1  *)
    erewrite inst_eq;
      try (extensionality r).
  2:{ instantiate (1 := fun r => (fst (f r), snd (f r))).
      apply injective_projections; easy. }
  2:{ simp D. reflexivity. }
    dependent destruction H.
    constructor...
    simp S. splits... }
Qed.
