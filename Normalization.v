Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Vector.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.

From AD Require Import Definitions.
From AD Require Import Tactics.

(*
  Evaluation (unfinished)
    Will follow about the same line as the normalization proof in software foundations vol.2
  Also used as a reference is:
    Proofs And Types by Jean-Yves Girard.
*)
Inductive value : forall {Γ τ}, tm Γ τ -> Prop :=
  | v_real : forall Γ r,
    value (const Γ r)
  | v_tuple : forall Γ τ σ (t1 : tm Γ τ) (t2 : tm Γ σ),
    value t1 ->
    value t2 ->
    value (tuple Γ t1 t2)
  | v_abs : forall Γ τ σ b,
    value (abs Γ τ σ b)
.
Hint Constructors value.

Reserved Notation "t1 --> t2" (at level 40).
Inductive step : forall {Γ τ}, tm Γ τ -> tm Γ τ -> Prop :=
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
where "t  -->  v" := (step t v).

(* From software foundations vol.2 *)
Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall {x : X}, multi R x x
  | multi_step : forall {x y z : X},
      R x y ->
      multi R y z ->
      multi R x z.
Definition multistep {Γ τ} := multi (@step Γ τ).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.
(* Inductive neutral : forall {Γ τ} (t : tm Γ τ), Prop :=
  | neutral_var : forall Γ τ v, neutral (var Γ τ v)
  | neutral_first : forall Γ τ σ (t : tm Γ (τ × σ)), neutral (first Γ t)
  | neutral_second : forall Γ τ σ (t : tm Γ (τ × σ)), neutral (second Γ t)
  | neutral_app : forall Γ τ σ (t1 : tm Γ (σ → τ)) (t2 : tm Γ σ), neutral (app Γ τ σ t1 t2)
. *)
Notation step_normal_form := (normal_form step).

Lemma value__normal : forall Γ τ (t : tm Γ τ), value t -> step_normal_form t.
Proof with eauto.
  intros Γ τ.
  induction τ;
    intros t Hv [t' Hstep];
    dependent destruction Hstep; dependent destruction Hv; subst.
  - apply (IHτ1 t1) in Hv1.
    unfold normal_form in Hv1.
    apply Hv1. exists t1'...
  - apply (IHτ2 t2) in Hv2.
    unfold normal_form in Hv2.
    apply Hv2. exists t2'...
Qed.

Lemma app_congr : forall Γ τ σ t1 t2 t1' t2',
  t1 = t1' -> t2 = t2' -> app Γ τ σ t1 t2 = app Γ τ σ t1' t2'.
Proof. intros. subst. auto. Qed.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Lemma step_deterministic : forall Γ τ,
  deterministic (@step Γ τ).
Proof with quick.
  unfold deterministic.
  intros Γ τ t t' t'' H1 H2.
  generalize dependent t''.
  dependent induction H1;
    intros t'' H2; dependent destruction H2.
  { dependent destruction H... }
  { dependent induction H;
    dependent destruction H2... }
  { apply value__normal in H. contradiction H. exists t2'... }
  { dependent induction H1... }
  { rewrite (IHstep t1'0 H2)... }
  { apply value__normal in H. contradiction H. exists t1'... }
  { apply value__normal in H0. contradiction H0. exists t2'... }
  { apply value__normal in H. contradiction H. exists t1'... }
  { rewrite (IHstep t2'0 H2)... }
  { rewrite (IHstep t1'0 H2)... }
  { apply value__normal in H. contradiction H. exists t1'... }
  { apply value__normal in H. contradiction H. exists t1'... }
  { rewrite (IHstep t2'0 H2)... }
  { rewrite (IHstep t1'0 H2)... }
  { apply value__normal in H. contradiction H. exists t1'... }
  { apply value__normal in H. contradiction H. exists t1'... }
  { rewrite (IHstep t2'0 H2)... }
  { rewrite (IHstep t1'0 H2)... }
  { dependent destruction H1...
    apply value__normal in H. contradiction H. exists t1'0...
    apply value__normal in H2. contradiction H2. exists t2'... }
  { dependent destruction H2...
    apply value__normal in H. contradiction H. exists t1'0...
    apply value__normal in H0. contradiction H0. exists t2'... }
  { reflexivity. }
  { rewrite (IHstep t1'0 H2)... }
  { dependent destruction H1...
    apply value__normal in H. contradiction H. exists t1'0...
    apply value__normal in H2. contradiction H2. exists t2'... }
  { dependent destruction H2...
    apply value__normal in H. contradiction H. exists t1'0...
    apply value__normal in H0. contradiction H0. exists t2'... }
  { reflexivity. }
Qed.

Definition halts {Γ τ} (t:tm Γ τ) : Prop := exists t', t -->* t' /\  value t'.

(** A trivial fact: *)

Lemma value_halts : forall Γ τ (v : tm Γ τ), value v -> halts v.
Proof.
  intros Γ τ v H. unfold halts.
  exists v. split.
  apply multi_refl.
  assumption.
Qed.

(* What would be preservation if it was needed *)
Theorem preservation : forall Γ τ (t : tm Γ τ) t' ,
  t --> t' ->
  (Γ ⊢ t ∷ τ) = (Γ ⊢ t' ∷ τ).
Proof. reflexivity. Qed.

(*
Fixpoint R (T:ty) (t:tm) {struct T} : Prop :=
  has_type empty t T /\ halts t /\
  (match T with
   | Bool  => True
   | Arrow T1 T2 => (forall s, R T1 s -> R T2 (app t s))
   | Prod T1 T2 =>
        (exists r s, t -->* pair r s /\
          value r /\
          value s /\
          R T1 r /\ R T2 s)
   end).
*)
Program Fixpoint R τ {Γ} (t : tm Γ τ): Prop :=
  halts t /\
  (match τ with
   | Real => True
   | τ1 × τ2 =>
      (forall (r : tm Γ τ1) (s : tm Γ τ2),
        t -->* tuple Γ r s /\
        value r /\
        value s /\
        R τ1 r /\ R τ2 s)
   | τ1 → τ2 =>
      (forall (s : tm Γ τ1), R τ1 s -> R τ2 (app Γ τ2 τ1 t s))
   end).

Lemma R_halts : forall {Γ τ} {t : tm Γ τ}, R τ t -> halts t.
Proof.
  intros.
  dependent destruction τ;
    unfold R in H; inversion H; assumption.
Qed.

Lemma step_preserves_halting :
  forall {Γ τ} (t t' : tm Γ τ), (t --> t') -> (halts t <-> halts t').
Proof.
 intros Γ τ t t' ST.  unfold halts.
 split.
 - (* -> *)
  intros [t'' [STM V]].
  inversion STM; subst.
   exfalso.  apply value__normal in V. unfold normal_form in V. apply V. exists t'. auto.
   rewrite (step_deterministic Γ τ t t' y ST H). exists t''. split; assumption.
 - (* <- *)
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
  econstructor; eassumption.
Qed.

Lemma step_preserves_R :
  forall {Γ τ} (t t' : tm Γ τ), R τ t -> (t --> t') -> R τ t'.
Proof with quick.
  intros Γ τ.
  generalize dependent Γ.
  dependent induction τ.
  { split... destruct H.
    apply (step_preserves_halting t t' H0)... }
  { quick. split; destruct H.
    apply (step_preserves_halting t t' H0)...
    intros. pose proof (H1 s H2).
    apply (IHτ2 Γ (app Γ τ2 τ1 t s) (app Γ τ2 τ1 t' s))...
    constructor... }
  { quick. destruct H. split.
    apply (step_preserves_halting t t' H0)...
    intros r s.
    destruct (H1 r s) as [Hst [Hvr [Hvs [Hr Hs]]]].
    clear H1. splits...
    dependent destruction Hst.
    assert (value (tuple Γ r s))...
    apply value__normal in H1. contradiction H1. exists t'...
    rewrite (step_deterministic Γ (τ1 × τ2) t t' y H0 H1).
    apply Hst. }
Qed.

Lemma multistep_preserves_R :
  forall {Γ τ} (t t' : tm Γ τ), R τ t -> (t -->* t') -> R τ t'.
Proof with quick.
  intros Γ τ t t' H Hst.
  dependent induction Hst...
  apply IHHst. eapply step_preserves_R...
Qed.

Lemma step_preserves_R' :
  forall {Γ τ} (t t' : tm Γ τ), R τ t' -> (t --> t') -> R τ t.
Proof with quick.
  intros Γ τ.
  generalize dependent Γ.
  dependent induction τ...
  { split... destruct H as [Hh Ht]. clear Ht.
    rewrite step_preserves_halting... }
  { split; destruct H as [Hh Ht]...
    rewrite step_preserves_halting...
    eapply IHτ2... constructor... }
  { split; destruct H as [Hh Ht]...
    rewrite step_preserves_halting...
    specialize Ht with r s.
    destruct Ht as [Hst [Hvr [Hvs [Hr Hs]]]].
    splits... econstructor... }
Qed.

Lemma multistep_preserves_R' :
  forall {Γ τ} (t t' : tm Γ τ), R τ t' -> (t -->* t') -> R τ t.
Proof with quick.
  intros Γ τ t t' H Hst.
  dependent induction Hst...
  apply IHHst in H. eapply step_preserves_R'...
Qed.

Lemma subst_R :
  forall {Γ Γ' τ} (t : tm Γ τ) (s : sub Γ Γ') (e : Env Γ),
    (forall σ (v : Var Γ σ), R σ (s σ v)) ->
    R τ (substitute s t).
Proof with quick.
  intros Γ Γ' τ t s E.
  (* remember (substitute s t) as t''. *)
  generalize dependent Γ.
  generalize dependent Γ'.
  dependent induction t.
  { (* Variables *)
    intros. simpl. apply H. }
  { (* App *)
    intros. simpl.
    pose proof (IHt1 s E H).
    pose proof (IHt2 s E H).
    simpl in H0. destruct H0 as [Hh H']... }
  { (* Abs *)
    intros sb E H. split.
    { apply value_halts. constructor. }
    { simpl. intros s Hrs.
      pose proof (R_halts Hrs) as [s' [Hst Hs']].
      pose proof (multistep_preserves_R s s') as H'.
      pose proof (H' Hrs Hst) as H''. clear H'.
      eapply multistep_preserves_R'...
      admit. } }
  { (* Const *)
    intros... split... apply value_halts... }
  { (* Add *)
    intros.
    pose proof (IHt1 s E H). clear IHt1.
    pose proof (IHt2 s E H). clear IHt2.
    inversion H0. clear H3.
    inversion H1. clear H4.
    unfold halts in *.
    destruct H2 as [t1' [Hst1 Hv1]]. destruct H3 as [t2' [Hst2 Hv2]].
    simpl (substitute s (add Γ t1 t2)).
    pose proof (multistep_preserves_R _ _ H0 Hst1).
    pose proof (multistep_preserves_R _ _ H1 Hst2).
    eapply multistep_preserves_R'.
    assert (R Real (add Γ' t1' t2')).
    { admit. }
    apply H4.
    econstructor. apply ST_Add1. admit.
    econstructor. apply ST_Add2. apply Hv1. admit.
    econstructor. }
  { intros.
    pose proof (IHt1 s E H). clear IHt1.
    pose proof (IHt2 s E H). clear IHt2.
    simpl (substitute s (tuple Γ t1 t2)).
    eapply multistep_preserves_R'.
    { admit. }
    { admit. } }
  { intros. pose proof (IHt s E H).
    simpl. apply H0. admit. }
  { intros. pose proof (IHt s E H).
    simpl. apply H0. admit. }
Admitted.

Theorem normalization :
  forall Γ τ (t : tm Γ τ) (e : Env Γ), halts t.
Proof.
  intros.
  rewrite <- (app_sub_id Γ τ t).
  eapply (R_halts).
  eapply (subst_R t id_sub); eauto.
Qed.
