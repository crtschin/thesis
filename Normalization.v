Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Vector.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Reals.

From Equations Require Import Equations.
From AD Require Import Tactics.
From AD Require Import Definitions.

(*
  Strong Normalization

  Will follow about the same line as the normalization proof in software
    foundations vol.2
  Also used as a reference is:
    Proofs And Types by Jean-Yves Girard.
*)
Inductive value : forall {Γ τ}, tm Γ τ -> Prop :=
  | v_real : forall {Γ r},
    value (const Γ r)
  | v_tuple : forall Γ τ σ (t1 : tm Γ τ) (t2 : tm Γ σ),
    value t1 ->
    value t2 ->
    value (tuple Γ t1 t2)
  | v_abs : forall Γ τ σ b,
    value (abs Γ τ σ b)
  | v_inl : forall Γ τ σ t,
    value t ->
    value (@inl Γ τ σ t)
  | v_inr : forall Γ τ σ t,
    value t ->
    value (@inr Γ τ σ t)
.
Hint Constructors value : ad.

Reserved Notation "t1 --> t2" (at level 40).
Inductive step : forall {Γ τ}, tm Γ τ -> tm Γ τ -> Prop :=
  (* Base STLC *)
  | ST_AppAbs : forall Γ τ σ t1' v2,
    value v2 ->
      (app Γ τ σ (abs Γ τ σ t1') v2) --> (substitute (| v2 |) t1')
  | ST_App1 : forall Γ τ σ t1 t1' t2,
      t1 --> t1' ->
        (app Γ τ σ t1 t2) --> (app Γ τ σ t1' t2)
  | ST_App2 : forall Γ τ σ (v1 : tm Γ (σ → τ)) t2 t2',
      value v1 ->
      t2 --> t2' ->
        (app Γ τ σ v1 t2) --> (app Γ τ σ v1 t2')

  (* Add *)
  | ST_Add : forall Γ v1 v2,
      (add Γ (const Γ v1) (const Γ v2)) --> const Γ (Rdefinitions.Rplus v1 v2)
  | ST_Add1 : forall Γ t1 t1' t2,
      t1 --> t1' ->
      (add Γ t1 t2) --> (add Γ t1' t2)
  | ST_Add2 : forall Γ v1 t2 t2',
    value v1 ->
      t2 --> t2' ->
      (add Γ v1 t2) --> (add Γ v1 t2')

  (* Pairs *)
  | ST_Tuple1 : forall Γ τ σ t1 t1' t2,
      t1 --> t1' ->
      (@tuple Γ τ σ t1 t2) --> (@tuple Γ τ σ t1' t2)
  | ST_Tuple2 : forall Γ τ σ t2 t2' v1,
      value v1 ->
      t2 --> t2' ->
      (@tuple Γ τ σ v1 t2) --> (@tuple Γ τ σ v1 t2')
  | ST_Fst : forall Γ τ σ t1 t1',
        t1 --> t1' ->
        (@first Γ τ σ t1) --> (@first Γ τ σ t1')
  | ST_FstTuple : forall Γ τ σ v1 v2,
        value v1 ->
        value v2 ->
      (@first Γ τ σ (@tuple Γ τ σ v1 v2)) --> v1
  | ST_Snd : forall Γ τ σ t1 t1',
        t1 --> t1' ->
        (@second Γ τ σ t1) --> (@second Γ τ σ t1')
  | ST_SndTuple : forall Γ τ σ v1 v2,
        value v1 ->
        value v2 ->
      (@second Γ τ σ (@tuple Γ τ σ v1 v2)) --> v2

  (* Sums *)
  | ST_Case : forall Γ τ σ ρ e e' t1 t2,
      e --> e' ->
      (@case Γ τ σ ρ e t1 t2) --> (@case Γ τ σ ρ e' t1 t2)
  | ST_Case1 : forall Γ τ σ ρ (t2 : tm Γ (σ → ρ))
        (t1 t1' : tm Γ (τ → ρ)) (e e' : tm Γ (τ <+> σ)),
      (* (@inl Γ τ σ e --> @inl Γ τ σ e') -> *)
      (* (@inl Γ τ σ e --> @inl Γ τ σ e') -> *)
      value e ->
      (t1 --> t1') ->
      (@case Γ τ σ ρ e t1 t2) --> (@case Γ τ σ ρ e t1' t2)
  | ST_Case2 : forall Γ τ σ ρ (t2 t2' : tm Γ (σ → ρ))
        (t1 : tm Γ (τ → ρ)) (e e' : tm Γ (τ <+> σ)),
      (* (@inr Γ τ σ e --> @inr Γ τ σ e') -> *)
      (* value e' -> *)
      (* (@inr Γ τ σ e --> @inr Γ τ σ e') -> *)
      value e ->
      value t1 ->
      (t2 --> t2') ->
      (@case Γ τ σ ρ e t1 t2) --> (@case Γ τ σ ρ e t1 t2')
  | ST_CaseInl : forall Γ τ σ ρ t2 t1' (e : tm Γ τ),
      value e ->
      value t1' ->
      value t2 ->
      (@case Γ τ σ ρ (inl Γ e) t1' t2) --> (app Γ ρ τ t1' e)
  | ST_CaseInr : forall Γ τ σ ρ t1 t2' (e : tm Γ σ),
      value e ->
      value t1 ->
      value t2' ->
      (@case Γ τ σ ρ (inr Γ e) t1 t2') --> (app Γ ρ σ t2' e)

  | ST_Inl : forall Γ τ σ t1 t1',
        t1 --> t1' ->
        (@inl Γ τ σ t1) --> (@inl Γ τ σ t1')
  | ST_Inr : forall Γ τ σ t1 t1',
        t1 --> t1' ->
        (@inr Γ τ σ t1) --> (@inr Γ τ σ t1')

where "t  -->  v" := (step t v).

(* From software foundations vol.2 *)
Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (Rel : relation X) : relation X :=
  | multi_refl : forall {x : X}, multi Rel x x
  | multi_step : forall {x y z : X},
      Rel x y ->
      multi Rel y z ->
      multi Rel x z.
Definition multistep {Γ τ} := multi (@step Γ τ).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Definition normal_form {X : Type} (Rel : relation X) (t : X) : Prop :=
  ~ exists t', Rel t t'.
Theorem multi_R : forall (X : Type) (Rel : relation X) (x y : X),
  Rel x y -> (multi Rel) x y.
Proof with quick. intros. econstructor... econstructor... Qed.
Theorem multi_trans : forall {X : Type} {Rel : relation X} {x y z : X},
  multi Rel x y -> multi Rel y z -> multi Rel x z.
Proof with quick. intros. induction H... apply multi_step with y... Qed.
Notation step_normal_form := (normal_form step).
Definition deterministic {X : Type} (Rel : relation X) :=
  forall x y1 y2 : X, Rel x y1 -> Rel x y2 -> y1 = y2.
Definition halts {Γ τ} (t:tm Γ τ) : Prop := exists t', t -->* t' /\  value t'.

Lemma value__normal : forall Γ τ (t : tm Γ τ), value t -> step_normal_form t.
Proof with quick.
  intros Γ τ.
  induction τ;
    intros t Hv [t' Hstep];
    dependent destruction Hstep; dependent destruction Hv; subst.
  - apply (IHτ1 t1) in Hv1; apply Hv1...
  - apply (IHτ2 t2) in Hv2; apply Hv2...
  - apply (IHτ1 t1) in Hv; apply Hv...
  - apply (IHτ2 t1) in Hv; apply Hv...
Qed.

Lemma app_congr : forall Γ τ σ t1 t2 t1' t2',
  t1 = t1' -> t2 = t2' -> app Γ τ σ t1 t2 = app Γ τ σ t1' t2'.
Proof. intros; subst; auto. Qed.

Ltac value_contradiction H :=
  (apply value__normal in H; contradiction H; quick).

Lemma step_deterministic : forall Γ τ,
  deterministic (@step Γ τ).
Proof with quick.
  unfold deterministic.
  intros Γ τ t t' t'' H1 H2.
  generalize dependent t''.
  dependent induction H1;
    intros t'' H2; dependent destruction H2;
      try erewrite IHstep...
  { dependent induction H;
    dependent destruction H2... }
  { value_contradiction H. }
  { dependent induction H1... }
  { value_contradiction H. }
  { value_contradiction H0. }
  { value_contradiction H. }
  { assert (H': value (const Γ v1)). constructor.
    value_contradiction H'. }
  { assert (H': value (const Γ v2)). constructor.
    value_contradiction H'. }
  { assert (H': value (const Γ v1)). constructor.
    value_contradiction H'. }
  { value_contradiction H. }
  { assert (H': value (const Γ v2)). constructor.
    value_contradiction H'. }
  { value_contradiction H. }
  { value_contradiction H. }
  { value_contradiction H. }
  { dependent destruction H1.
    value_contradiction H.
    value_contradiction H2. }
  { dependent destruction H2...
    value_contradiction H.
    value_contradiction H0. }
  { dependent destruction H1...
    value_contradiction H.
    value_contradiction H2. }
  { dependent destruction H2...
    value_contradiction H.
    value_contradiction H0. }
  { value_contradiction H. }
  { value_contradiction H. }
  { assert (value (@inl Γ τ σ e0)). constructor...
    value_contradiction H3. }
  { assert (value (@inr Γ τ σ e0)). constructor...
    value_contradiction H3. }
  { value_contradiction H. }
  { value_contradiction H2. }
  { value_contradiction H2. }
  { value_contradiction H2. }
  { value_contradiction H. }
  { value_contradiction H0. }
  { value_contradiction H4. }
  { value_contradiction H4. }
  { assert (value (@inl Γ τ σ e)). constructor...
    value_contradiction H3. }
  { value_contradiction H0. }
  { value_contradiction H1. }
  { assert (value (@inr Γ τ σ e)). constructor...
    value_contradiction H3. }
  { value_contradiction H0. }
  { value_contradiction H1. }
Qed.

(** A trivial fact: *)
Lemma value_halts : forall Γ τ (v : tm Γ τ), value v -> halts v.
Proof.
  intros Γ τ v H. unfold halts.
  exists v. split.
  apply multi_refl.
  assumption.
Qed.

Equations Rel {Γ} τ (t : tm Γ τ): Prop :=
Rel Real t := halts t;
Rel (τ1 × τ2) t := halts t /\ (exists (r : tm Γ τ1) (s : tm Γ τ2),
  t -->* tuple Γ r s /\
  value r /\
  value s /\
  Rel τ1 r /\ Rel τ2 s);
Rel (τ1 → τ2) t := halts t /\
  (forall (s : tm Γ τ1), Rel τ1 s -> Rel τ2 (app Γ τ2 τ1 t s));
Rel (τ1 <+> τ2) t := halts t /\
  ((exists (r : tm Γ τ1),
    t -->* @inl Γ τ1 τ2 r /\ value r /\ Rel τ1 r) \/
  (exists (s : tm Γ τ2),
    t -->* @inr Γ τ1 τ2 s /\ value s /\ Rel τ2 s)).

(* Program Fixpoint Rel {Γ} τ (t : tm Γ τ): Prop :=
  halts t /\
  (match τ with
   | Real => True
   | τ1 × τ2 =>
      (exists (r : tm Γ τ1) (s : tm Γ τ2),
        t -->* tuple Γ r s /\
        value r /\
        value s /\
        Rel τ1 r /\ Rel τ2 s)
   | τ1 → τ2 =>
      (forall (s : tm Γ τ1), Rel τ1 s -> Rel τ2 (app Γ τ2 τ1 t s))
   | τ1 <+> τ2 =>
      ((exists (r : tm Γ τ1),
        t -->* @inl Γ τ1 τ2 r /\ value r /\ Rel τ1 r) \/
      (exists (s : tm Γ τ2),
        t -->* @inr Γ τ1 τ2 s /\ value s /\ Rel τ2 s))
   end). *)

Lemma R_halts : forall {Γ τ} {t : tm Γ τ}, Rel τ t -> halts t.
Proof.
  intros.
  dependent elimination τ; simp Rel in H;
    inversion H; assumption.
Qed.

Lemma step_preserves_halting :
  forall {Γ τ} (t t' : tm Γ τ), (t --> t') -> (halts t <-> halts t').
Proof.
 intros Γ τ t t' ST. unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  inversion STM; subst.
   exfalso.  apply value__normal in V. unfold normal_form in V. apply V. exists t'. auto.
   rewrite (step_deterministic Γ τ t t' y ST H). exists t''. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; quick.
  econstructor; eassumption.
Qed.

Lemma multistep_preserves_halting :
  forall {Γ τ} (t t' : tm Γ τ), (t -->* t') -> (halts t <-> halts t').
Proof with quick.
  intros Γ τ t t' ST.
  split.
  - induction ST...
    apply (step_preserves_halting _ _ H) in H0.
    apply IHST in H0...
  - induction ST...
    apply IHST in H0...
    apply (step_preserves_halting _ _ H) in H0...
Qed.

Lemma step_preserves_R :
  forall {Γ τ} (t t' : tm Γ τ), Rel τ t -> (t --> t') -> Rel τ t'.
Proof with quick.
  intros Γ τ.
  generalize dependent Γ.
  dependent induction τ; simp Rel in *...
  { apply (step_preserves_halting t t' H0)... }
  { split; destruct H...
    { eapply (step_preserves_halting t t')... }
    { pose proof (H1 s H2).
      eapply IHτ2...
      constructor... } }
  { destruct H. split.
    eapply (step_preserves_halting t t')...
    destruct H1 as [r [s H1]].
    destruct H1 as [Hst [Hvr [Hvs [Hr Hs]]]].
    exists r. exists s. splits...
    dependent destruction Hst.
    assert (value (tuple Γ r s))...
    apply value__normal in H1. contradiction H1...
    erewrite step_deterministic... }
  { destruct H as [Hh H].
    split... eapply (step_preserves_halting t t')...
    destruct H; destruct H as [x [Ht [Hv Hr]]].
    { left. exists x.
      splits...
      assert (value (@inl Γ τ1 τ2 x))...
      dependent destruction Ht.
      apply value__normal in H. contradiction H...
      erewrite step_deterministic... }
    { right. exists x.
      splits...
      assert (value (@inr Γ τ1 τ2 x))...
      dependent destruction Ht.
      apply value__normal in H. contradiction H...
      erewrite step_deterministic... } }
Qed.

Lemma multistep_preserves_R :
  forall {Γ τ} (t t' : tm Γ τ), Rel τ t -> (t -->* t') -> Rel τ t'.
Proof with quick.
  intros Γ τ t t' H Hst.
  dependent induction Hst...
  apply IHHst. eapply step_preserves_R...
Qed.

Lemma step_preserves_R' :
  forall {Γ τ} (t t' : tm Γ τ), Rel τ t' -> (t --> t') -> Rel τ t.
Proof with quick.
  intros Γ τ.
  generalize dependent Γ.
  dependent induction τ...
  { simp Rel in *.
    rewrite step_preserves_halting... }
  { simp Rel in *.
    split; destruct H as [Hh Ht]...
    rewrite step_preserves_halting...
    eapply IHτ2... constructor... }
  { split; destruct H as [Hh Ht]...
    rewrite step_preserves_halting...
    destruct Ht as [r [s Ht]].
    destruct Ht as [Hst [Hvr [Hvs [Hr Hs]]]].
    exists r. exists s.
    splits... econstructor... }
  { split; destruct H as [Hh Ht]...
    rewrite step_preserves_halting...
    destruct Ht as [Ht | Ht];
      destruct Ht as [x [Ht [Hv Hr]]].
    { left. exists x.
      splits...
      econstructor... }
    { right. exists x. splits...
      econstructor... } }
Qed.

Lemma multistep_preserves_R' :
  forall {Γ τ} (t t' : tm Γ τ), Rel τ t' -> (t -->* t') -> Rel τ t.
Proof with quick.
  intros Γ τ t t' H Hst.
  dependent induction Hst...
  apply IHHst in H. eapply step_preserves_R'...
Qed.

Inductive instantiation : forall {Γ Γ'}, sub Γ Γ' -> Prop :=
  | inst_empty : @instantiation [] [] id_sub
  | inst_const : forall Γ Γ' τ (t : tm Γ' τ) (s : sub Γ Γ'),
      value t -> Rel τ t ->
      instantiation s ->
      instantiation (cons_sub t s).

Lemma step__multistep : forall {Γ τ} {t t' : tm Γ τ},
  t --> t' -> t -->* t'.
Proof with quick.
  intros. repeat econstructor...
Qed.

Lemma multistep_AppAbs : forall Γ τ σ (f : tm (σ::Γ) τ) (t t' : tm Γ σ),
  value t' -> t -->* t' -> (app _ _ _ (abs _ _ _ f) t) -->* substitute (|t'|) f.
Proof with quick.
  intros. induction H0.
  - econstructor; econstructor...
  - eapply multi_step. eapply ST_App2...
    apply IHmulti...
Qed.

Lemma multistep_App1 : forall Γ τ σ (t t' : tm Γ (σ → τ)) (b : tm Γ σ),
  (t -->* t') -> (app _ _ _ t b) -->* (app _ _ _ t' b).
Proof with quick.
  intros. induction H.
  - constructor.
  - eapply multi_step. apply ST_App1... assumption.
Qed.

Lemma multistep_App2 : forall Γ τ σ (v : tm Γ (σ → τ)) (t t' : tm Γ σ),
  value v -> (t -->* t') -> (app _ _ _ v t) -->* (app _ _ _ v t').
Proof with quick.
  intros. induction H0.
  - constructor.
  - eapply multi_step. apply ST_App2... assumption.
Qed.

Lemma multistep_Add1 : forall Γ (t t' : tm Γ Real) (t1 : tm Γ Real),
  (t -->* t') -> (add Γ t t1) -->* (add Γ t' t1).
Proof with quick.
  intros. induction H.
  - constructor.
  - eapply multi_step. apply ST_Add1... assumption.
Qed.

Lemma multistep_Add2 : forall Γ (t t' : tm Γ Real) (v : tm Γ Real),
  value v -> (t -->* t') -> (add Γ v t) -->* (add Γ v t').
Proof with quick.
  intros. induction H0.
  - constructor.
  - eapply multi_step. apply ST_Add2... assumption.
Qed.

Lemma multistep_Add : forall Γ r1 r2,
  value (const Γ r1) -> value (const Γ r2) ->
  (add Γ (const Γ r1) (const Γ r2)) -->* (const Γ (Rdefinitions.Rplus r1 r2)).
Proof with quick.
  intros. econstructor.
  all: constructor.
Qed.

Lemma multistep_Tuple1 : forall Γ τ σ (t t' : tm Γ τ) (t1 : tm Γ σ),
  (t -->* t') -> (tuple Γ t t1) -->* (tuple Γ t' t1).
Proof with quick.
  intros. induction H.
  - constructor.
  - eapply multi_step. apply ST_Tuple1... assumption.
Qed.

Lemma multistep_Tuple2 : forall Γ τ σ (t t' : tm Γ σ) (v : tm Γ τ),
  value v -> (t -->* t') -> (tuple Γ v t) -->* (tuple Γ v t').
Proof with quick.
  intros. induction H0.
  - constructor.
  - eapply multi_step. apply ST_Tuple2... assumption.
Qed.

Lemma multistep_First : forall Γ τ σ (t t' : tm Γ (τ × σ)),
  (t -->* t') -> (first Γ t) -->* (first Γ t').
Proof with quick.
  intros. induction H.
  - constructor.
  - eapply multi_step. apply ST_Fst... assumption.
Qed.

Lemma multistep_FirstTuple : forall Γ τ σ (t1 : tm Γ τ) (t2 : tm Γ σ),
  value t1 -> value t2 -> (first Γ (tuple Γ t1 t2)) -->* t1.
Proof with quick.
  intros. econstructor.
  apply ST_FstTuple... constructor.
Qed.

Lemma multistep_Second : forall Γ τ σ (t t' : tm Γ (τ × σ)),
  (t -->* t') -> (second Γ t) -->* (second Γ t').
Proof with quick.
  intros. induction H.
  - constructor.
  - eapply multi_step. apply ST_Snd... assumption.
Qed.

Lemma multistep_SecondTuple : forall Γ τ σ (t1 : tm Γ τ) (t2 : tm Γ σ),
  value t1 -> value t2 -> (second Γ (tuple Γ t1 t2)) -->* t2.
Proof with quick.
  intros. econstructor.
  apply ST_SndTuple... constructor.
Qed.

Lemma multistep_Case : forall Γ τ σ ρ e e' c1 c2,
  (e -->* e') -> (@case Γ τ σ ρ e c1 c2) -->* (@case Γ τ σ ρ e' c1 c2).
Proof with quick.
  intros. induction H.
  - constructor.
  - eapply multi_step. apply ST_Case... assumption.
Qed.

Lemma multistep_Case1 : forall Γ τ σ ρ e c1 c1' c2,
  value e -> (c1 -->* c1') -> (@case Γ τ σ ρ e c1 c2) -->* (@case Γ τ σ ρ e c1' c2).
Proof with quick.
  intros. induction H0.
  - constructor.
  - eapply multi_step. apply ST_Case1... assumption.
Qed.

Lemma multistep_Case2 : forall Γ τ σ ρ e c1 c2 c2',
  value e -> value c1 -> (c2 -->* c2') -> (@case Γ τ σ ρ e c1 c2) -->* (@case Γ τ σ ρ e c1 c2').
Proof with quick.
  intros. induction H1.
  - constructor.
  - eapply multi_step. apply ST_Case2... assumption.
Qed.

Lemma multistep_CaseInl : forall Γ τ σ ρ e c1 c2,
  value e -> value c1 -> value c2 ->
    (@case Γ τ σ ρ (inl Γ e) c1 c2) -->* (@app Γ ρ τ c1 e).
Proof with quick.
  intros. econstructor...
  - apply ST_CaseInl...
  - constructor.
Qed.

Lemma multistep_CaseInr : forall Γ τ σ ρ e c1 c2,
  value e -> value c1 -> value c2 ->
    (@case Γ τ σ ρ (inr Γ e) c1 c2) -->* (@app Γ ρ σ c2 e).
Proof with quick.
  intros. econstructor...
  - apply ST_CaseInr...
  - constructor.
Qed.

Lemma multistep_Inl : forall Γ τ σ e e',
  (e -->* e') ->
    (@inl Γ τ σ e) -->* (@inl Γ τ σ e').
Proof with quick.
  intros. induction H...
  - constructor.
  - econstructor. apply ST_Inl... assumption.
Qed.

Lemma multistep_Inr : forall Γ τ σ e e',
  (e -->* e') ->
    (@inr Γ τ σ e) -->* (@inr Γ τ σ e').
Proof with quick.
  intros. induction H...
  - constructor.
  - econstructor. apply ST_Inr... assumption.
Qed.

Lemma subst_R :
  forall {Γ Γ' τ} (t : tm Γ τ) (s : sub Γ Γ'),
    instantiation s ->
    Rel τ (substitute s t).
Proof with quick.
  intros Γ Γ' τ t s.
  generalize dependent Γ.
  generalize dependent Γ'.
  dependent induction t; simpl; intros sb H.
  { (* Variables *)
    dependent induction H.
    { inversion v. }
    { dependent induction v; simp cons_sub... } }
  { (* App *)
    pose proof (IHt1 sb H).
    pose proof (IHt2 sb H).
    simp Rel in H0. destruct H0 as [Hh H']... }
  { (* Abs *)
    simp Rel. split.
    { apply value_halts. constructor. }
    { simpl. intros s Hrs.
      pose proof (R_halts Hrs) as [s' [Hst Hs']].
      pose proof (multistep_preserves_R s s' Hrs Hst) as Hrs'.
      pose proof (IHt (cons_sub s' sb)) as H'.
      eapply multistep_preserves_R'.
      apply H'.
      { constructor... }
      { eapply multi_trans.
        eapply multistep_AppAbs...
        rewrite <- app_sub_sub.
        assert
          (H'': (compose_sub_sub (| s' |) (substitute_lifted sb))
            = cons_sub s' sb).
        { unfold compose_sub_sub.
          repeat (apply functional_extensionality_dep; intros).
          dependent destruction x0...
          simp substitute_lifted cons_sub.
          erewrite subst_shift_refl... }
        rewrite H''. constructor. } } }
  { (* Const *)
    simp Rel. apply value_halts... }
  { (* Add *)
    intros.
    pose proof (IHt1 sb H) as P1; clear IHt1.
    pose proof (IHt2 sb H) as P2; clear IHt2.
    pose proof P1 as P1'; pose proof P2 as P2'.
    simp Rel in P1'; simp Rel in P2'.
    inversion P1 as [t1' [Hst1 Hv1]].
    inversion P2 as [t2' [Hst2 Hv2]].
    pose proof (multistep_preserves_R _ _ P1 Hst1).
    pose proof (multistep_preserves_R _ _ P2 Hst2).
    assert (add Γ' (substitute sb t1) (substitute sb t2)
      -->* add Γ' t1' t2').
    { eapply multi_trans.
      { eapply multistep_Add1... }
      { eapply multistep_Add2... } }
    dependent destruction Hv1.
    dependent destruction Hv2.
    pose proof (multistep_Add Γ0 r r0 v_real v_real).
    eapply multistep_preserves_R'.
    2: eassumption.
    eapply multistep_preserves_R'.
    2: eassumption.
    simp Rel.
    unfold halts in *.
    exists (const Γ0 (Rdefinitions.RbaseSymbolsImpl.Rplus r r0)).
    splits...
    econstructor. }
  { (* Tuple *)
    intros.
    pose proof (IHt1 sb H) as H1; clear IHt1.
    pose proof (IHt2 sb H) as H2; clear IHt2.
    pose proof (R_halts H1) as [t1' [Hst1 Hv1]].
    pose proof (R_halts H2) as [t2' [Hst2 Hv2]].
    pose proof (multistep_preserves_R _ _ H1 Hst1).
    pose proof (multistep_preserves_R _ _ H2 Hst2).
    assert (tuple Γ' (substitute sb t1) (substitute sb t2) -->* tuple Γ' t1' t2').
    { eapply multi_trans.
      { apply multistep_Tuple1... }
      { apply multistep_Tuple2... } }
    simp Rel. split.
    { unfold halts.
      exists (tuple Γ' t1' t2')... }
    { intros. exists t1'. exists t2'.
      splits... } }
  { (* First *)
    intros. simpl.
    pose proof (IHt sb H) as H'.
    pose proof (R_halts H'); destruct H0 as [t' [Hst Hvt]].
    apply value_halts in Hvt.
    pose proof H' as [Hh He].
    destruct He as [Hr [Hs [Hsst [Hvr [Hvs [Hrr Hrs]]]]]].
    pose proof (multistep_preserves_R _ _ H' Hsst).
    assert (Hst''': first Γ' (substitute sb t) -->* Hr).
    { eapply multi_trans.
      { apply multistep_First. apply Hsst. }
      { econstructor. apply ST_FstTuple... constructor. } }
    eapply multistep_preserves_R'.
    2: apply Hst'''.
    induction τ... }
  { (* Second *)
    intros. simpl.
    pose proof (IHt sb H) as H'.
    pose proof (R_halts H') as [t' [Hst Hvt]].
    apply value_halts in Hvt.
    pose proof H' as [Hh He].
    destruct He as [Hr [Hs [Hsst [Hvr [Hvs [Hrr Hrs]]]]]].
    pose proof (multistep_preserves_R _ _ H' Hsst).
    assert (Hst''': second Γ' (substitute sb t) -->* Hs).
    { eapply multi_trans.
      { apply multistep_Second. apply Hsst. }
      { econstructor. apply ST_SndTuple... constructor. } }
    eapply multistep_preserves_R'.
    2: apply Hst'''.
    induction τ... }
  { (* Case *)
    intros. simpl.
    pose proof (IHt1 sb H) as IHt1'; clear IHt1.
    pose proof (IHt2 sb H) as IHt2'; clear IHt2.
    pose proof (IHt3 sb H) as IHt3'; clear IHt3.
    (* pose proof (R_halts H0) as [e' [Hste Hve]]. *)
    pose proof (R_halts IHt2') as [t2' [Hst2 Hv2]].
    pose proof (R_halts IHt3') as [t3' [Hst3 Hv3]].
    (* pose proof (multistep_preserves_R _ _ H0 Hste). *)
    pose proof (multistep_preserves_R _ _ IHt2' Hst2) as H2'.
    pose proof (multistep_preserves_R _ _ IHt3' Hst3) as H3'.
    (* dependent induction Hve; clear IHHve. *)
    simpl in IHt1'. simp Rel in *.
    destruct IHt1' as [Hh IHt1']; destruct IHt1' as [IHt1'|IHt1'];
      destruct IHt1' as [x [Hstep [Hv Hr]]].
    { eapply multistep_preserves_R'.
    2:{ apply multistep_Case... }
      eapply multistep_preserves_R'.
    2:{ apply multistep_Case1... }
      eapply multistep_preserves_R'.
    2:{ apply multistep_Case2... }
      eapply multistep_preserves_R'.
    2:{ apply multistep_CaseInl... }
      destruct H2' as [Hh2 Hs2]... }
    { eapply multistep_preserves_R'.
    2:{ apply multistep_Case... }
      eapply multistep_preserves_R'.
    2:{ apply multistep_Case1... }
      eapply multistep_preserves_R'.
    2:{ apply multistep_Case2... }
      eapply multistep_preserves_R'.
    2:{ apply multistep_CaseInr... }
      destruct H3' as [Hh3 Hs3]... } }
  { (* Inl *)
    intros.
    pose proof (IHt sb H) as H'.
    apply R_halts in H'.
    destruct H' as [t' [Hst Hv]].
    split...
    { econstructor.
      split... apply multistep_Inl... }
    { left. exists t'.
      splits...
      apply multistep_Inl...
      eapply multistep_preserves_R... } }
  { (* Inr *)
    intros.
    pose proof (IHt sb H) as H'.
    apply R_halts in H'.
    destruct H' as [t' [Hst Hv]].
    split...
    { econstructor.
      split... apply multistep_Inr... }
    { right. exists t'.
      splits...
      apply multistep_Inr...
      eapply multistep_preserves_R... } }
Qed.

Theorem normalization :
  forall τ (t : tm [] τ), halts t.
Proof.
  intros.
  rewrite <- (app_sub_id [] τ t).
  eapply (R_halts).
  eapply (subst_R t id_sub); quick.
  constructor.
Qed.
