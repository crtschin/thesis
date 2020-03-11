Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Vector.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Reals.

From AD Require Import Definitions.
From AD Require Import Tactics.

(*
  Strong Normalization

  Will follow about the same line as the normalization proof in software
    foundations vol.2
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
  | ST_Add : forall Γ v1 v2,
      (add Γ (const Γ v1) (const Γ v2)) --> const Γ (Rplus v1 v2)
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
Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
  R x y -> (multi R) x y.
Proof with quick. intros. econstructor... econstructor... Qed.
Theorem multi_trans : forall {X : Type} {R : relation X} {x y z : X},
  multi R x y -> multi R y z -> multi R x z.
Proof with quick. intros. induction H... apply multi_step with y... Qed.
Notation step_normal_form := (normal_form step).
Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

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
  { reflexivity. }
  { assert (H': value (const Γ v1)). constructor.
    apply value__normal in H'. contradiction H'. exists t1'... }
  { assert (H': value (const Γ v2)). constructor.
    apply value__normal in H'. contradiction H'. exists t2'... }
  { assert (H': value (const Γ v1)). constructor.
    apply value__normal in H'. contradiction H'. exists t1'... }
  { rewrite (IHstep t1'0 H2)... }
  { apply value__normal in H. contradiction H. exists t1'... }
  { assert (H': value (const Γ v2)). constructor.
    apply value__normal in H'. contradiction H'. exists t2'... }
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

Program Fixpoint R τ {Γ} (t : tm Γ τ): Prop :=
  halts t /\
  (match τ with
   | Real => True
   | τ1 × τ2 =>
      (exists (r : tm Γ τ1) (s : tm Γ τ2),
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
    destruct H1 as [r [s H1]].
    destruct H1 as [Hst [Hvr [Hvs [Hr Hs]]]].
    exists r. exists s. splits...
    dependent destruction Hst.
    assert (value (tuple Γ r s))...
    apply value__normal in H1. contradiction H1. exists t'...
    rewrite (step_deterministic Γ (τ1 × τ2) t t' y H1 H0).
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
    destruct Ht as [r [s Ht]].
    destruct Ht as [Hst [Hvr [Hvs [Hr Hs]]]].
    exists r. exists s.
    splits... econstructor... }
Qed.

Lemma multistep_preserves_R' :
  forall {Γ τ} (t t' : tm Γ τ), R τ t' -> (t -->* t') -> R τ t.
Proof with quick.
  intros Γ τ t t' H Hst.
  dependent induction Hst...
  apply IHHst in H. eapply step_preserves_R'...
Qed.

Inductive instantiation : forall {Γ Γ'}, sub Γ Γ' -> Prop :=
  | inst_empty : @instantiation [] [] id_sub
  | inst_const : forall Γ Γ' τ (t : tm Γ' τ) (s : sub Γ Γ'),
      value t -> R τ t ->
      instantiation s ->
      instantiation (cons_sub t s).

Lemma subst_compose_cons :
  forall Γ Γ' τ (t : tm Γ' τ) (s : sub Γ Γ'),
    compose_sub_sub (|t|) (substitute_lifted s) =
      (cons_sub t s).
Proof with quick.
  intros.
  unfold compose_sub_sub.
  eta_expand.
Admitted.

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

Lemma multistep_Add : forall Γ t1 t2,
  value t1 -> value t2 ->
  exists t', (add Γ t1 t2) -->* (const Γ t').
Proof with quick.
  intros.
  dependent destruction H.
  dependent destruction H0.
  exists (r + r0). repeat econstructor.
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

Lemma multistep_Second : forall Γ τ σ (t t' : tm Γ (τ × σ)),
  (t -->* t') -> (second Γ t) -->* (second Γ t').
Proof with quick.
  intros. induction H.
  - constructor.
  - eapply multi_step. apply ST_Snd... assumption.
Qed.

(* Definition shave_var {X Γ τ σ} (v : @Var X (σ::Γ) τ): @Var X Γ τ.
Proof with quick.
  induction (σ::Γ). inversion v.
  inversion v... subst. apply IHl.
Admitted.

Lemma multistep_subst : forall Γ Γ' τ σ (t : tm (σ::Γ) τ)
  (sb : sub Γ Γ') (s' : tm Γ' σ),
    value s' ->
      (substitute
        (compose_sub_sub (| s' |) (substitute_lifted sb)) t) -->*
      (substitute
        (fun (σ0 : ty) (v : σ0 ∈ σ :: Γ) => sb σ0 (shave_var v)) t).
Admitted. *)

(* Lemma subst_cons_sub_compose : forall Γ Γ' τ (s : tm Γ τ) (sb : sub Γ Γ'),
  compose_sub_sub (| s |) sb =
    cons_sub s sb.
Admitted. *)

Lemma subst_R :
  forall {Γ Γ' τ} (t : tm Γ τ) (s : sub Γ Γ'),
    instantiation s ->
    (* (forall σ (v : Var Γ σ), R σ (s σ v)) -> *)
    R τ (substitute s t).
Proof with quick.
  intros Γ Γ' τ t s.
  generalize dependent Γ.
  generalize dependent Γ'.
  dependent induction t.
  { (* Variables *)
    intros. simpl.
    dependent induction H.
    { inversion v. }
    { dependent induction v... } }
  { (* App *)
    intros. simpl.
    pose proof (IHt1 s H).
    pose proof (IHt2 s H).
    simpl in H0. destruct H0 as [Hh H']... }
  { (* Abs *)
    intros sb H. split.
    { apply value_halts. constructor. }
    { simpl. intros s Hrs.
      pose proof (R_halts Hrs) as [s' [Hst Hs']].
      pose proof (multistep_preserves_R s s' Hrs Hst) as Hrs'.
      pose proof (IHt (compose_sub_sub (|s'|)
        (substitute_lifted sb))) as H'.
      simpl in H'.
      eapply multistep_preserves_R'.
      apply H'.
      { rewrite -> subst_compose_cons. constructor... }
      { eapply multi_trans.
        eapply multistep_AppAbs...
        rewrite <- app_sub_sub. constructor. } } }
  { (* Const *)
    intros... split... apply value_halts... }
  { (* Add *)
    intros.
    pose proof (IHt1 s H) as P1; clear IHt1.
    pose proof (IHt2 s H) as P2; clear IHt2.
    inversion P1 as [P1' P1'']; clear P1''.
    inversion P2 as [P2' P2'']; clear P2''.
    unfold halts in *.
    destruct P1' as [t1' [Hst1 Hv1]]. destruct P2' as [t2' [Hst2 Hv2]].
    simpl (substitute s (add Γ t1 t2)).
    pose proof (multistep_preserves_R _ _ P1 Hst1).
    pose proof (multistep_preserves_R _ _ P2 Hst2).
    assert (add Γ' (substitute s t1) (substitute s t2)
      -->* add Γ' t1' t2').
    { eapply multi_trans.
      { eapply multistep_Add1... }
      { eapply multistep_Add2... } }
    pose proof (multistep_Add _ _ _ Hv1 Hv2).
    destruct H3.
    pose proof (multi_trans H2 H3).
    eapply multistep_preserves_R'.
    2: eassumption.
    simpl. splits...
    unfold halts in *. exists (const Γ' x). splits...
    econstructor. }
  { (* Tuple *)
    intros.
    pose proof (IHt1 s H) as H1; clear IHt1.
    pose proof (IHt2 s H) as H2; clear IHt2.
    pose proof (R_halts H1) as H1'; destruct H1' as [t1' [Hst1 Hv1]].
    pose proof (R_halts H2) as H2'; destruct H2' as [t2' [Hst2 Hv2]].
    pose proof (multistep_preserves_R _ _ H1 Hst1).
    pose proof (multistep_preserves_R _ _ H2 Hst2).
    simpl (substitute s (tuple Γ t1 t2)).
    assert (tuple Γ' (substitute s t1) (substitute s t2) -->* tuple Γ' t1' t2').
    { eapply multi_trans.
      { apply multistep_Tuple1... }
      { apply multistep_Tuple2... } }
    unfold R. fold R. split.
    { unfold halts.
      exists (tuple Γ' t1' t2')... }
    { intros. exists t1'. exists t2'.
      splits... } }
  { (* First *)
    intros. simpl.
    pose proof (IHt s H) as H'.
    pose proof (R_halts H'); destruct H0 as [t' [Hst Hvt]].
    apply value_halts in Hvt.
    pose proof H' as H''.
    simpl in H'. destruct H' as [Hh He].
    destruct He as [Hr [Hs [Hsst [Hvr [Hvs [Hrr Hrs]]]]]].
    pose proof (multistep_preserves_R _ _ H'' Hsst).
    assert (Hst''': first Γ' (substitute s t) -->* Hr).
    { eapply multi_trans.
      { apply multistep_First. apply Hsst. }
      { econstructor. apply ST_FstTuple... constructor. } }
    eapply multistep_preserves_R'.
    2: apply Hst'''.
    induction τ... }
  { (* Second *)
    intros. simpl.
    pose proof (IHt s H) as H'.
    pose proof (R_halts H'); destruct H0 as [t' [Hst Hvt]].
    apply value_halts in Hvt.
    pose proof H' as H''.
    simpl in H'. destruct H' as [Hh He].
    destruct He as [Hr [Hs [Hsst [Hvr [Hvs [Hrr Hrs]]]]]].
    pose proof (multistep_preserves_R _ _ H'' Hsst).
    assert (Hst''': second Γ' (substitute s t) -->* Hs).
    { eapply multi_trans.
      { apply multistep_Second. apply Hsst. }
      { econstructor. apply ST_SndTuple... constructor. } }
    eapply multistep_preserves_R'.
    2: apply Hst'''.
    induction τ... }
Admitted.

Theorem normalization :
  forall τ (t : tm [] τ), halts t.
Proof.
  intros.
  rewrite <- (app_sub_id [] τ t).
  eapply (R_halts).
  eapply (subst_R t id_sub); eauto.
  constructor.
Qed.
