Require Import Arith.PeanoNat.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coquelicot.Derive.
Require Import Coquelicot.Hierarchy.
Require Import Equations.Equations.
Require Import Init.Datatypes.
Require Import Lists.List.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.JMeq.
Require Import Reals.
Require Import micromega.Lia.
Require Vectors.Fin.
Import ListNotations.

Require Import AD.DepList.
Require Import AD.Tactics.
Require Import AD.Definitions.
Require Import AD.Macro.
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
  (* When (τ := ℝ), we need to prove that the function of which we track the
      derivative, f, is both derivable and that g contains exactly that
      derivative
  *)
  (forall (x : R), ex_derive f x) /\
    g = (fun r => (f r, Derive f r));
S Nat f g :=
  (* When (τ := ℕ), we do not need to keep track of the derivative,
      as the tangent space at each related point is 0-dimensional and
      any related functions will also be constant.
  *)
  f = g /\ (exists n, f = fun _ => n);

(* For composed constructs, the relation needs to be preserved by the
    underlying subcomponents.

    Carefull consideration needs to be taken w.r.t. which variables
    are universally or existentially quantified. The general idea
    being that the subterms need to be 'given' as witnesses or
    instances for the complete term to be constructed, hence the
    variables denotating these subterms are defined existentially.
*)
S (Array n τ) f g :=
  forall i,
  exists f1 g1,
    S τ f1 g1 /\
    (fun r => vector_nth i (f r)) = f1 /\
    (fun r => vector_nth i (g r)) = g1;
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

(* Helper definition to ensure that the context is only built
    from terms whose denotation are in the relation
*)
Inductive instantiation : forall Γ,
    (R -> ⟦ Γ ⟧ₜₓ) -> (R -> ⟦ Dctx Γ ⟧ₜₓ) -> Prop :=
  | inst_empty :
      instantiation [] (Basics.const HNil) (Basics.const HNil)
  | inst_cons :
      forall Γ τ,
      forall g1 g2,
      forall (sb: R -> ⟦ Γ ⟧ₜₓ),
      forall (Dsb: R -> ⟦ Dctx Γ ⟧ₜₓ),
        instantiation Γ sb Dsb ->
        S τ g1 g2 ->
        instantiation (τ::Γ)
          (fun r => (g1 r ::: sb r)) (fun r => (g2 r ::: Dsb r)).

Example derivative_id :
  (⟦ Dtm ex_id_real ⟧ₜₘ HNil) (3, 1) = (3, 1).
Proof with quick.
  unfold ex_id_real.
  simp Dtm...
Qed.

Example derivative_plus :
  ⟦ Dtm (@ex_plus []) ⟧ₜₘ HNil (7, 1) (13, 0) = (7 + 13, 1 + 0).
Proof with quick.
  unfold ex_plus.
  simp Dtm...
Qed.

(* Derivative of (y + x * x) *)
Example derivative_square_plus :
  ⟦ Dtm (@ex_square_plus []) ⟧ₜₘ HNil (7, 1) (13, 0)
    = (7 + 13 * 13, 1 + (13 * 0 + 13 * 0)).
Proof with quick.
  unfold ex_square_plus.
  simp Dtm...
Qed.

(* Very useful helper definitions for rewriting the relations,
    as the denotations we're working on are functions *)
Lemma inst_eq : forall Γ f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> instantiation Γ f1 f2 = instantiation Γ g1 g2.
Proof. intros; rewrites. Qed.

Lemma S_eq : forall τ f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> S τ f1 f2 = S τ g1 g2.
Proof. intros; rewrites. Qed.

(*
  This is the generalization of the fundamental property of the
  logical relation given also referred to as the substitution lemma.

  Considering we are working in the denotational domain and omit
  syntactic constructions as much as possible, we formulate
  substitutions as context supplying function in both the original
  and macro contexts, resp
    `R -> ⟦ Γ ⟧ₜₓ`
    `R -> ⟦ Dctx Γ ⟧ₜₓ`
  The idea is then to build up these denotated substitutions using
  the `instantiation` relation above which intuitively ensures that
  any term being supplied by the function for the context, which
  would have the denotation `R -> ⟦ τ ⟧ₜ` for some type τ, is also
  valid w.r.t. the logical relation.
*)
Lemma S_subst :
  forall Γ τ,
  forall (t : tm Γ τ),
  forall (sb : R -> ⟦ Γ ⟧ₜₓ),
  forall (Dsb : R -> ⟦ Dctx Γ ⟧ₜₓ),
  instantiation Γ sb Dsb ->
  S τ (fun x => ⟦t⟧ₜₘ (sb x))
    (fun x => ⟦Dtm t⟧ₜₘ (Dsb x)).
Proof with quick.
  intros Γ τ t sb Dsb.
  induction t; simp denote_tm in *.
  { (* Var *)
    intros.
    (* Using induction on the type being referenced by
        the variable in the context. Destructing the
        instantiation term should indicate that the relation
        is preserved by the context *)
    induction v; dependent destruction H.
    { (* v := Top, we already know that the relation is preserved by
          every term in the context. *)
      erewrite S_eq.
    2,3: extensionality x.
    2,3: simp Dtm denote_tm...
    2,3: simp denote_v...
      assumption. }
    { (* v := Pop, proven by the induction hypothesis obtained from
          the variable. *)
      simp Dtm.
      erewrite S_eq. eapply IHv...
      all: extensionality x.
      all: simp Dtm denote_tm...
      all: simp denote_v.
      all: reflexivity. } }
  { (* App *)
    intros.
    pose proof (IHt1 sb Dsb H) as IHt1.
    pose proof (IHt2 sb Dsb H) as IHt2.
    (* The relation is preserved by function terms,
        so we apply the corresponding induction hypothesis. *)
    simp S in IHt1.
    erewrite S_eq. eapply IHt1...
    (* The leftover equalities are proven by simple rewriting. *)
    all: extensionality x.
    all: simp Dtm; fold Dt.
    all: simp denote_tm.
    all: now simp denote_tm Dtm. }
  { (* Abs *)
    intros. simp S...
    (* specialize IHt with
      (fun r => (g1 r ::: sb r)) (fun r => (g2 r ::: Dsb r))... *)
    erewrite S_eq.
  2,3: extensionality x.
  2,3: simp Dtm denote_tm; reflexivity.
    eapply IHt. constructor... }
  { (* Build *)
    intros. simp S...
    induction n.
    { (* Induction on n, Base case = 0
        Contradiction due to indices running from 1..n *)
      inversion i. }
    { (* Induction on n, IHn case
        Give instances *)
      pose proof (IHn (shave_fin t)) as IHn.
      simp Dtm denote_tm in *...
      (* Case analysis on index,
        (+1) case is automatically handled by IHn *)
      dependent destruction i...
      clear IHn.
      (* For the 1 case,
        Give the correct terms which should correspond to the
          denotation of the `head` of the build term
          `build Γ τ (Datatypes.S n) t` *)
      exists (fun r =>
        ⟦ t (nat_to_fin n) ⟧ₜₘ (sb r)).
      exists (fun r =>
        ⟦ Dtm (t (nat_to_fin n)) ⟧ₜₘ (Dsb r))... } }
  { (* Get
        Proven by logical relation where (τ:=Array n τ) *)
    intros H.
    pose proof (IHt sb Dsb H) as IHt. simp S in *.
    specialize IHt with t.
    destruct IHt as [f1 [g1 [Hs1 [Heq1 Heq2]]]]; subst.
    erewrite S_eq... }
  { (* Const *)
    (* For ℝ cases, prove that there exists a derivative and give
        that derivative *)
    intros. simp S.
    (* Setup rewrite rule using 'denotation of (rval r) = const r' *)
    assert (H': forall r,
      (fun x : R => ⟦ rval Γ r ⟧ₜₘ (sb x)) = const r).
    { intros; extensionality r'; simp denote_tm; unfold const... }
    splits...
    { rewrite_c H'.
      (* const is derivable *)
      apply ex_derive_const. }
    { extensionality x...
      simp Dtm denote_tm...
      rewrite_c H'. apply injective_projections...
      (* Derivative of const is 0 *)
      unfold const.
      rewrite Derive_const... } }
  { (* Add *)
    intros.
    (* Specialize IH to give evidence that
      subterms are derivable/give derivative *)
    destruct (IHt1 sb Dsb H) as [Heq1 Heq1'].
    destruct (IHt2 sb Dsb H) as [Heq2 Heq2'].
    clear IHt1 IHt2.
    (* Prove addition of subterms is derivable
      and give derivative value *)
    simp S.
    splits...
    { (* Addition is derivable given subterms are derivable *)
      apply (ex_derive_plus _ _ _ (Heq1 x) (Heq2 x)). }
    { simp Dtm.
      extensionality x.
      eapply equal_f in Heq1'.
      eapply equal_f in Heq2'.
      simp denote_tm.
      apply injective_projections;
        rewrite_c Heq1'; rewrite_c Heq2'...
      (* Derivative is addition of derivative of subterms *)
      symmetry.
      apply (Derive_plus _ _ x (Heq1 x) (Heq2 x)). } }
  { (* Mul
      Same as addition *)
    intros H.
    destruct (IHt1 sb Dsb H) as [IHex1 IHdiv1].
    destruct (IHt2 sb Dsb H) as [IHex2 IHdiv2].
    clear IHt1 IHt2.
    erewrite S_eq.
  2,3: extensionality x.
  2,3: simp Dtm...
  2,3: simp denote_tm.
  2,3: reflexivity.
    simp S. split...
    { apply (ex_derive_mult _ _ _ (IHex1 x) (IHex2 x)). }
    { extensionality x.
      simp Dtm denote_tm.
      rewrite (equal_f IHdiv1); clear IHdiv1.
      rewrite (equal_f IHdiv2); clear IHdiv2...
      apply injective_projections...
      { eassert (H': (fun r : R => ⟦ mul Γ t1 t2 ⟧ₜₘ (sb r)) = _).
        { extensionality r. now simp denote_tm. }
        rewrite_c H'.
        rewrite Derive_mult...
        eassert (H':
          Derive (fun x0 : R => ⟦ t1 ⟧ₜₘ (sb x0)) x * ⟦ t2 ⟧ₜₘ (sb x) = _) by now rewrite Rmult_comm.
        rewrite_c H'.
        rewrite Rplus_comm... } } }
  { (* Nsucc
        Terms with type ℕ don't carry a derivative, so prove
        `t` and `Dtm t` are equal and they denotate to some
        constant function which gives n. *)
    intros H. simp S.
    pose proof (IHt sb Dsb H) as IHt.
    simp S in IHt. destruct IHt as [IHeq IHex].
    split.
    { (* `t = Dtm t` proven by IH *)
      extensionality x. simp Dtm denote_tm.
      pose proof (equal_f IHeq)... }
    { (* Give the denotation of these terms. *)
      destruct IHex as [n IHex].
      exists (Datatypes.S n).
      extensionality x. simp denote_tm.
      rewrite (equal_f IHex)... } }
  { (* Nval *)
    intros H. simp S. splits.
    exists n. extensionality x. simp denote_tm... }
  { (* Bounded iteration *)
    intros.
    pose proof (IHt1 sb Dsb H) as IHt1.
    pose proof (IHt2 sb Dsb H) as IHt2.
    pose proof (IHt3 sb Dsb H) as IHt3.
    simp S in IHt2.
    destruct IHt2 as [IHt2eq IHt2case].
    (* ℕ terms are not differentiated, so applying the
        macro does not add a tangent term and the denotations
        of the term and the macro applied variant are equal.
      Rewrite using this fact. *)
    pose proof (equal_f IHt2eq) as IHt2'...
    erewrite S_eq.
  2:{ extensionality x. simp Dtm denote_tm.
      reflexivity. }
  2:{ extensionality x. simp Dtm denote_tm.
      rewrite <- IHt2'. reflexivity. }
    clear IHt2' IHt2eq.
    (* Case analysis on the denotation of the ℕ term *)
    destruct IHt2case as [n IHt2case].
    destruct n.
    { (* 0 case:
        Proven by the induction hypothesis
          resulting from the base term *)
      pose proof (equal_f IHt2case) as IHt20'...
      erewrite S_eq.
    2:{ extensionality x. rewrite IHt20'...
        reflexivity. }
    2:{ extensionality x. rewrite IHt20'...
        reflexivity. }
      assumption. }
    { (* (n+1) case:
        Proven by the induction hypothesis
          resulting from the function term
        Need to rewrite the number term as its
          denotation and do straightforward induction *)
      pose proof (equal_f IHt2case) as IHt2S'...
      erewrite S_eq.
    2:{ extensionality x. rewrite IHt2S'...
        reflexivity. }
    2:{ extensionality x. rewrite IHt2S'...
        reflexivity. }
      simp S in IHt1.
      eapply IHt1. clear IHt2S' IHt2case.
      induction n... } }
  { (* Tuples
        Give denotational instances of subterms using IHs *)
    intros...
    erewrite S_eq.
  2,3: extensionality x.
  2,3: simp Dtm.
  2,3: simp denote_tm.
  2,3: reflexivity.
    simp S.
    pose proof (IHt1 sb Dsb H) as IHt1.
    pose proof (IHt2 sb Dsb H) as IHt2.
    exists (⟦ t1 ⟧ₜₘ ∘ sb );
      exists (⟦ Dtm t1 ⟧ₜₘ ∘ Dsb).
    exists (⟦ t2 ⟧ₜₘ ∘ sb );
      exists (⟦ Dtm t2 ⟧ₜₘ ∘ Dsb).
    unfold compose.
    exists IHt1; exists IHt2... }
  { (* Projection 1
        Simply deconstruct the denotation of the tuple and use the
        correct subterm to find the first projection *)
    intros. simp Dtm.
    specialize IHt with sb Dsb.
    simp S in IHt; pose proof (IHt H) as H'; clear IHt.
    destruct H' as [f1 [f2 [g1 [g2 [Hs1 [_ [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x...
    { simp denote_tm. erewrite (equal_f Heq1)... }
    { simp denote_tm. erewrite (equal_f Heq2)... } }
  { (* Projection 2
        Idem *)
    intros. simp Dtm.
    specialize IHt with sb Dsb.
    simp S in IHt; pose proof (IHt H) as H'; clear IHt.
    destruct H' as [f1 [f2 [g1 [g2 [_ [Hs2 [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x...
    { simp denote_tm. erewrite (equal_f Heq1)... }
    { simp denote_tm. erewrite (equal_f Heq2)... } }
  { (* Case *)
    intros.
    pose proof (IHt1 sb Dsb H) as IHt1.
    pose proof (IHt2 sb Dsb H) as IHt2.
    pose proof (IHt3 sb Dsb H) as IHt3.
    simp S in *. simp Dtm.
    (* Either term denotates to inl or inr *)
    destruct IHt1 as [[g1 [g2 H']]|[g1 [g2 H']]].
    { (* Scrutinee is inl *)
      clear IHt3.
      destruct H' as [Hs [Heq1 Heq2]].
      erewrite S_eq...
      { extensionality x. eapply equal_f in Heq1.
        simp denote_tm. now rewrite Heq1. }
      { extensionality x. eapply equal_f in Heq2.
        simp denote_tm. now rewrite Heq2. } }
    { (* Scrutinee is inr *)
      clear IHt2.
      destruct H' as [Hs [Heq1 Heq2]].
      erewrite S_eq...
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

(* Very simple lemma which states that terms of type ℝ whose denotation are in
    the relation is both derivable and applying the macro to the term results
    in the derivative
*)
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
  (f : R -> hlist denote_t (repeat Real n))
  : R -> hlist denote_t (map Dt (repeat Real n)) :=
D 0 f r := f r;
D (Datatypes.S n) f r :=
  @denote_ctx_cons (map Dt (repeat Real n)) (Dt ℝ)
    ((denote_ctx_hd ∘ f) r, Derive (denote_ctx_hd ∘ f) r)
    (D n (denote_ctx_tl ∘ f) r).

(*  Helper inductive definition asserting that every parameter supplied to the
      typing context is derivable.
*)
Inductive differentiable : forall n, (R -> ⟦ repeat Real n ⟧ₜₓ) -> Prop :=
  | differentiable_0 : differentiable 0 (fun _ => HNil)
  | differentiable_Sn :
    forall n (f : R -> ⟦ repeat Real n ⟧ₜₓ),
    forall (g : R -> R),
      differentiable n f ->
      (forall x, ex_derive g x) ->
      differentiable (Datatypes.S n) (fun x =>
        @denote_ctx_cons (repeat ℝ n) ℝ (g x) (f x)).

(* The fundamental property of the logical relation given above.
    Simply states that syntacticly well-typed terms are
    semantically well-typed (so, in the relation).
    Note the restriction that the only free variables allowed
    are of type ℝ, the arguments which the function denotation
    of the term takes *)
Lemma fundamental_property :
  forall τ n,
  forall (t : tm (repeat ℝ n) τ),
  forall (f : R -> ⟦ repeat ℝ n ⟧ₜₓ),
  differentiable n f ->
  S τ (fun x => ⟦t⟧ₜₘ (f x))
    (fun x => ⟦Dtm t⟧ₜₘ (D n f x)).
Proof with quick.
  intros. apply S_subst. clear t.
  (* Need to prove that the typing context is only built out of
      terms which are valid w.r.t the logical relation.
      This is true because the context is limited to terms
      of type ℝ and we only consider differentiable functions
      enforced by the `differentiable` relation defined above *)
  induction n...
  { (* N = 0
      Prove f : R -> ⟦ repeat Real 0 ⟧ₜₓ is equal to 'const tt'
      Rewrite it as such *)
    erewrite inst_eq;
      try (extensionality r; simp D; remember (f r) as e;
        dependent destruction e; reflexivity).
    fold (@Basics.const unit R tt). constructor. }
  { (* N = n + 1  *)
    erewrite inst_eq;
      try (extensionality r).
  2:{ instantiate (1 := fun r =>
        denote_ctx_cons (denote_ctx_hd (f r)) (denote_ctx_tl (f r)))...
      remember (f r) as e. dependent destruction e.
      now apply denote_ctx_eq. }
  2:{ simp D. reflexivity. }
    constructor.
    { apply IHn. dependent destruction H. simpl. apply H. }
    { unfold compose.
      simp S. split.
      { dependent destruction H... }
      { reflexivity. } } }
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
  eapply S_correct_R.
  (* Fundamental lemma proves that the ℝ term is in the relation
      given each of the terms in the context are in the relation. *)
  eapply fundamental_property...
Qed.
