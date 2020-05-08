Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Vector.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Coq.micromega.Lia.
Require Reals.

From Equations Require Import Equations.
From AD Require Import Tactics.
From AD Require Import Definitions.
From AD Require Import Denotation.

Local Open Scope program_scope.

(*
  Strong Normalization

  Will follow about the same line as the normalization proof in software
    foundations vol.2
  Also used as a reference is:
    Proofs And Types by Jean-Yves Girard.
*)
Inductive value : forall {Γ τ}, tm Γ τ -> Prop :=
  | v_real : forall {Γ r},
    value (rval Γ r)
  | v_nval : forall {Γ n},
    value (nval Γ n)
  (* | v_nat0 : forall {Γ},
    value (nval0 Γ)
  | v_natS : forall {Γ n},
    value n ->
    value (nvalS Γ n) *)
  | v_build : forall {Γ τ n f},
    value (build Γ τ n f)
  | v_tuple : forall Γ τ σ (t1 : tm Γ τ) (t2 : tm Γ σ),
    value t1 ->
    value t2 ->
    value (tuple Γ t1 t2)
  | v_abs : forall Γ τ σ b,
    value (abs Γ τ σ b)
  | v_inl : forall Γ τ σ t,
    value t ->
    value (inl Γ τ σ t)
  | v_inr : forall Γ τ σ t,
    value t ->
    value (inr Γ τ σ t)
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

  (* Arrays *)
  | ST_Get : forall Γ τ n (t t' : tm Γ (Array n τ)) (ti : Fin.t n),
    t --> t' ->
    get Γ ti t --> get Γ ti t'
  | ST_GetBuild : forall Γ τ n i (f : Fin.t n -> tm Γ τ),
    get Γ i (build Γ τ n f) --> f i

  (* | ST_Fold1 : forall Γ τ tf i (t t' : tm Γ τ),
    t --> t' ->
    ifold Γ τ tf i t --> ifold Γ τ tf i t'
  | ST_Fold2 : forall Γ τ tf i i' (t : tm Γ τ),
    value t ->
    i --> i' ->
    ifold Γ τ tf i t --> ifold Γ τ tf i' t
  | ST_Fold3 : forall Γ τ tf tf' i  (t : tm Γ τ),
    value t ->
    value i ->
    tf --> tf' ->
    ifold Γ τ tf i t --> ifold Γ τ tf' i t

  | ST_FoldN0 : forall Γ τ tf (t : tm Γ τ),
    value t ->
    value tf ->
    ifold Γ τ tf (nval _ 0) t --> t
  | ST_FoldNS : forall Γ τ n tf (t : tm Γ τ),
    value t ->
    value tf ->
    ifold Γ τ tf (nval _ (S n)) t -->
      ifold Γ τ tf (nval _ n)
        (* (abs _ _ _ f) *)
        (app _ _ _ (app _ _ _ tf (nval _ n)) t) *)

  (* Nat *)
  (* | ST_NvalS : forall Γ (t t' : tm Γ ℕ),
    t --> t' ->
    nvalS Γ t --> nvalS Γ t' *)
  | ST_NSucc : forall Γ (t t' : tm Γ ℕ),
    t --> t' ->
    nsucc Γ t --> nsucc Γ t'
  | ST_NSuccVal : forall Γ n (t t' : tm Γ ℕ),
    nsucc Γ (nval Γ n) --> nval Γ (S n)

  | ST_Nrec1 : forall Γ τ tf i (t t' : tm Γ τ),
    t --> t' ->
    nrec Γ τ tf i t --> nrec Γ τ tf i t'
  | ST_Nrec2 : forall Γ τ tf i i' (t : tm Γ τ),
    value t ->
    i --> i' ->
    nrec Γ τ tf i t --> nrec Γ τ tf i' t
  | ST_Nrec3 : forall Γ τ tf tf' i  (t : tm Γ τ),
    value t ->
    value i ->
    tf --> tf' ->
    nrec Γ τ tf i t --> nrec Γ τ tf' i t

  | ST_NrecN0 : forall Γ τ tf (t : tm Γ τ),
    value t ->
    value tf ->
    nrec Γ τ tf (nval _ 0) t --> t
  | ST_NrecNS : forall Γ τ n tf (t : tm Γ τ),
    value t ->
    value tf ->
    nrec Γ τ tf (nval _ (S n)) t -->
      app _ _ _ tf (nrec Γ τ tf (nval _ n) t)
      (* nrec Γ τ
        tf
        (nval _ n)
        (app _ _ _ (app _ _ _ tf (nval _ n)) t) *)
      (* (app _ _ _ (app _ _ _ tf (nval _ n)) (nrec Γ τ tf (nval _ n) t)) *)

  (* Add *)
  | ST_Add : forall Γ v1 v2,
      (add Γ (rval Γ v1) (rval Γ v2)) --> rval Γ (Rdefinitions.Rplus v1 v2)
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
      value e ->
      (t1 --> t1') ->
      (@case Γ τ σ ρ e t1 t2) --> (@case Γ τ σ ρ e t1' t2)
  | ST_Case2 : forall Γ τ σ ρ (t2 t2' : tm Γ (σ → ρ))
        (t1 : tm Γ (τ → ρ)) (e e' : tm Γ (τ <+> σ)),
      value e ->
      value t1 ->
      (t2 --> t2') ->
      (@case Γ τ σ ρ e t1 t2) --> (@case Γ τ σ ρ e t1 t2')
  | ST_CaseInl : forall Γ τ σ ρ t2 t1' (e : tm Γ τ),
      value e ->
      value t1' ->
      value t2 ->
      (@case Γ τ σ ρ (inl Γ _ _ e) t1' t2) --> (app Γ ρ τ t1' e)
  | ST_CaseInr : forall Γ τ σ ρ t1 t2' (e : tm Γ σ),
      value e ->
      value t1 ->
      value t2' ->
      (@case Γ τ σ ρ (inr Γ _ _ e) t1 t2') --> (app Γ ρ σ t2' e)

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
Proof with quick. intros. repeat econstructor... Qed.
Theorem multi_trans : forall {X : Type} {Rel : relation X} {x y z : X},
  multi Rel x y -> multi Rel y z -> multi Rel x z.
Proof with quick. intros. induction H... apply multi_step with y... Qed.
Notation step_normal_form := (normal_form step).
Definition deterministic {X : Type} (Rel : relation X) :=
  forall x y1 y2 : X, Rel x y1 -> Rel x y2 -> y1 = y2.
Definition halts {Γ τ} (t:tm Γ τ) : Prop := exists t', t -->* t' /\  value t'.

(** A trivial fact: *)
Lemma value_halts : forall Γ τ (v : tm Γ τ), value v -> halts v.
Proof.
  intros Γ τ v H. unfold halts.
  exists v. split.
  apply multi_refl.
  assumption.
Qed.

Lemma value__normal : forall Γ τ (t : tm Γ τ), value t -> step_normal_form t.
Proof with quick.
  intros Γ τ.
  induction τ;
    intros t Hv [t' Hstep];
    dependent destruction Hstep; dependent destruction Hv; subst...
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

Ltac auto_value_contradiction :=
  match goal with
  | [ H : value _ |- _ ] =>
      solve [value_contradiction H]
  | [ H : ?A --> _ |- _ ] =>
      assert (H': value A); quick;
        solve [value_contradiction H']
  | _ => idtac
  end.

Lemma step_deterministic : forall Γ τ,
  deterministic (@step Γ τ).
Proof with quick.
  unfold deterministic.
  intros Γ τ t t' t'' H1 H2.
  generalize dependent t''.
  dependent induction H1;
    intros t'' H2; dependent destruction H2;
      try erewrite IHstep; quick; auto_value_contradiction.
Qed.

Equations Rel {Γ} τ (t : tm Γ τ): Prop :=
Rel Real t := halts t;
Rel Nat t := halts t;
Rel (Array n τ) t := halts t /\ (exists (f : Fin.t n -> tm Γ τ),
  t -->* build Γ τ n f /\ forall i, Rel τ (f i));
Rel (τ1 × τ2) t :=
  halts t /\ (exists (r : tm Γ τ1) (s : tm Γ τ2),
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
  { apply (step_preserves_halting t t' H0)... }
  { simp Rel. splits...
    { apply (step_preserves_halting t t' H0).
      apply R_halts in H... }
    { simp Rel in H. destruct H as [Hh [f [Hst H']]].
      exists f. splits...
      dependent destruction Hst.
      { dependent destruction H0. }
      { rewrite <- (step_deterministic _ _ _ _ _ H H0)... } } }
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
    rewrite step_preserves_halting... }
  { simp Rel. splits...
    { apply (step_preserves_halting t t' H0).
      apply R_halts in H... }
    { simp Rel in H. destruct H as [Hh [f [Hst H']]].
      exists f. splits...
      econstructor... } }
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
  intros. induction H; econstructor. apply ST_App1... assumption.
Qed.

Lemma multistep_App2 : forall Γ τ σ (v : tm Γ (σ → τ)) (t t' : tm Γ σ),
  value v -> (t -->* t') -> (app _ _ _ v t) -->* (app _ _ _ v t').
Proof with quick.
  intros. induction H0; econstructor. apply ST_App2... assumption.
Qed.

Lemma multistep_Add1 : forall Γ (t t' : tm Γ Real) (t1 : tm Γ Real),
  (t -->* t') -> (add Γ t t1) -->* (add Γ t' t1).
Proof with quick.
  intros. induction H; econstructor. apply ST_Add1... assumption.
Qed.

Lemma multistep_Add2 : forall Γ (t t' : tm Γ Real) (v : tm Γ Real),
  value v -> (t -->* t') -> (add Γ v t) -->* (add Γ v t').
Proof with quick.
  intros. induction H0; econstructor. apply ST_Add2... assumption.
Qed.

Lemma multistep_Add : forall Γ r1 r2,
  value (rval Γ r1) -> value (rval Γ r2) ->
  (add Γ (rval Γ r1) (rval Γ r2)) -->* (rval Γ (Rdefinitions.Rplus r1 r2)).
Proof with quick. intros. repeat econstructor. Qed.

Lemma multistep_Tuple1 : forall Γ τ σ (t t' : tm Γ τ) (t1 : tm Γ σ),
  (t -->* t') -> (tuple Γ t t1) -->* (tuple Γ t' t1).
Proof with quick.
  intros. induction H; econstructor. apply ST_Tuple1... assumption.
Qed.

Lemma multistep_Tuple2 : forall Γ τ σ (t t' : tm Γ σ) (v : tm Γ τ),
  value v -> (t -->* t') -> (tuple Γ v t) -->* (tuple Γ v t').
Proof with quick.
  intros. induction H0; econstructor. apply ST_Tuple2... assumption.
Qed.

Lemma multistep_First : forall Γ τ σ (t t' : tm Γ (τ × σ)),
  (t -->* t') -> (first Γ t) -->* (first Γ t').
Proof with quick.
  intros. induction H; econstructor. apply ST_Fst... assumption.
Qed.

Lemma multistep_FirstTuple : forall Γ τ σ (t1 : tm Γ τ) (t2 : tm Γ σ),
  value t1 -> value t2 -> (first Γ (tuple Γ t1 t2)) -->* t1.
Proof with quick.
  intros. econstructor. apply ST_FstTuple... constructor.
Qed.

Lemma multistep_Second : forall Γ τ σ (t t' : tm Γ (τ × σ)),
  (t -->* t') -> (second Γ t) -->* (second Γ t').
Proof with quick.
  intros. induction H; econstructor. apply ST_Snd... assumption.
Qed.

Lemma multistep_SecondTuple : forall Γ τ σ (t1 : tm Γ τ) (t2 : tm Γ σ),
  value t1 -> value t2 -> (second Γ (tuple Γ t1 t2)) -->* t2.
Proof with quick. intros. econstructor. apply ST_SndTuple... constructor. Qed.

Lemma multistep_Case : forall Γ τ σ ρ e e' c1 c2,
  (e -->* e') -> (@case Γ τ σ ρ e c1 c2) -->* (@case Γ τ σ ρ e' c1 c2).
Proof with quick.
  intros. induction H; econstructor. apply ST_Case... assumption.
Qed.

Lemma multistep_Case1 : forall Γ τ σ ρ e c1 c1' c2,
  value e -> (c1 -->* c1') -> (@case Γ τ σ ρ e c1 c2) -->* (@case Γ τ σ ρ e c1' c2).
Proof with quick.
  intros. induction H0; econstructor. apply ST_Case1... assumption.
Qed.

Lemma multistep_Case2 : forall Γ τ σ ρ e c1 c2 c2',
  value e -> value c1 -> (c2 -->* c2') -> (@case Γ τ σ ρ e c1 c2) -->* (@case Γ τ σ ρ e c1 c2').
Proof with quick.
  intros. induction H1; econstructor. apply ST_Case2... assumption.
Qed.

Lemma multistep_CaseInl : forall Γ τ σ ρ e c1 c2,
  value e -> value c1 -> value c2 ->
    (@case Γ τ σ ρ (inl Γ _ _ e) c1 c2) -->* (@app Γ ρ τ c1 e).
Proof with quick.
  intros. econstructor... apply ST_CaseInl... constructor.
Qed.

Lemma multistep_CaseInr : forall Γ τ σ ρ e c1 c2,
  value e -> value c1 -> value c2 ->
    (@case Γ τ σ ρ (inr Γ _ _ e) c1 c2) -->* (@app Γ ρ σ c2 e).
Proof with quick.
  intros. econstructor... apply ST_CaseInr... constructor.
Qed.

Lemma multistep_Inl : forall Γ τ σ e e',
  (e -->* e') ->
    (@inl Γ τ σ e) -->* (@inl Γ τ σ e').
Proof with quick.
  intros. induction H; econstructor... apply ST_Inl...
Qed.

Lemma multistep_Inr : forall Γ τ σ e e',
  (e -->* e') ->
    (@inr Γ τ σ e) -->* (@inr Γ τ σ e').
Proof with quick.
  intros. induction H; econstructor. apply ST_Inr... assumption.
Qed.

Lemma multistep_Get : forall Γ τ n i (t t' : tm Γ (Array n τ)),
  (t -->* t') ->
    get Γ i t -->* get Γ i t'.
Proof with quick.
  intros. induction H; econstructor... econstructor. assumption.
Qed.

Lemma multistep_NSucc : forall Γ (t t' : tm Γ ℕ),
    t -->* t' ->
    nsucc Γ t -->* nsucc Γ t'.
Proof with quick.
  intros. induction H; econstructor... econstructor. assumption.
Qed.

Lemma multistep_NSuccVal : forall Γ n (t t' : tm Γ ℕ),
    nsucc Γ (nval Γ n) -->* nval Γ (S n).
Proof with quick.
  intros. econstructor... eapply ST_NSuccVal... constructor.
Qed.

Lemma multistep_Nrec1 : forall Γ τ tf i (t t' : tm Γ τ),
  t -->* t' -> nrec Γ τ tf i t -->* nrec Γ τ tf i t'.
Proof with quick.
  intros. induction H; econstructor... econstructor. assumption.
Qed.

Lemma multistep_Nrec2 : forall Γ τ tf i i' (t : tm Γ τ),
  value t -> i -->* i' -> nrec Γ τ tf i t -->* nrec Γ τ tf i' t.
Proof with quick.
  intros. induction H0; econstructor... econstructor; assumption.
Qed.

Lemma multistep_Nrec3 : forall Γ τ tf tf' i  (t : tm Γ τ),
  value t -> value i -> tf -->* tf' ->
    nrec Γ τ tf i t -->* nrec Γ τ tf' i t.
Proof with quick.
  intros. induction H1; econstructor... econstructor; assumption.
Qed.

(* Lemma multistep_NrecS : forall Γ τ n tf (t : tm Γ τ),
  value t ->
  value tf ->
    nrec Γ τ tf (nval _ (S n)) t -->*
      nrec Γ τ
        tf
        (nval _ n)
        (app _ _ _ (app _ _ _ tf (nval _ n)) t).
Proof with quick.
  intros. econstructor; econstructor; assumption.
Qed. *)

Lemma multistep_NrecS : forall Γ τ n tf (t : tm Γ τ),
    value t -> value tf ->
    nrec Γ τ tf (nval _ (S n)) t -->*
        (app _ _ _ tf (nrec Γ τ tf (nval _ n) t)).
Proof with quick.
  intros. econstructor; econstructor; assumption.
Qed.

Lemma subst_R :
  forall {Γ Γ' τ} (t : tm Γ τ) (s : sub Γ Γ'),
    instantiation s ->
    Rel τ (substitute s t).
Proof with quick.
  intros Γ Γ' τ t s.
  generalize dependent Γ.
  generalize dependent Γ'.
  dependent induction t; simpl.
  { (* Variables *)
    intros sb H.
    dependent induction H.
    { inversion v. }
    { dependent induction v; simp cons_sub... } }
  { (* App *)
    intros sb H.
    pose proof (IHt1 sb H).
    pose proof (IHt2 sb H).
    simp Rel in H0. destruct H0 as [Hh H']... }
  { (* Abs *)
    intros sb H.
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
  { (* Build *)
    intros sb H'.
    simp Rel.
    splits...
    { apply value_halts... }
    { exists (substitute sb ∘ t).
      splits... constructor. } }
  { (* Get *)
    intros sb H.
    pose proof (IHt sb H) as H'; clear IHt.
    simp Rel in H'.
    destruct H' as [Hh [f [Hst Hr]]].
    eapply multistep_preserves_R'...
    eapply multi_trans.
    eapply multistep_Get...
    econstructor. eapply ST_GetBuild.
    constructor. }
  { (* Rval *)
    intros sb H.
    simp Rel. apply value_halts... }
  { (* Add *)
    intros sb H.
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
    exists (rval Γ0 (Rdefinitions.RbaseSymbolsImpl.Rplus r r0)).
    splits...
    econstructor. }
  { (* NSucc *)
    intros sb H.
    pose proof (IHt sb H) as IHt.
    pose proof (R_halts IHt) as [t' [Hst Hv]].
    pose proof (multistep_preserves_R _ _ IHt Hst).
    clear IHt; rename H0 into IHt.
    eapply multistep_preserves_R'.
  2:{ eapply multistep_NSucc... }
    dependent destruction Hv.
    eapply multistep_preserves_R'.
    simp Rel. apply value_halts...
    eapply multistep_NSuccVal...
    all: pose proof (nval Γ0 n)... }
  { (* Nval *)
    intros sb H.
    simp Rel. apply value_halts... }
  { (* Bounded Iteration *)
    intros sb H.
    pose proof (IHt1 sb H) as IHt1.
    pose proof (R_halts IHt1) as [t1' [Hst1 Hv1]].
    pose proof (IHt2 sb H) as IHt2.
    pose proof (R_halts IHt2) as [t2' [Hst2 Hv2]].
    pose proof (IHt3 sb H) as IHt3.
    pose proof (R_halts IHt3) as [t3' [Hst3 Hv3]].
    dependent destruction Hv2.
    pose proof (multistep_preserves_R _ _ IHt1 Hst1) as IHt1'.
    pose proof (multistep_preserves_R _ _ IHt2 Hst2) as IHt2'.
    pose proof (multistep_preserves_R _ _ IHt3 Hst3) as IHt3'.
    eapply multistep_preserves_R'.
  2:{ eapply multi_trans.
      eapply multistep_Nrec1...
      eapply multi_trans.
      eapply multistep_Nrec2...
      eapply multi_trans.
      eapply multistep_Nrec3... econstructor. }
    clear Hst1 Hst2 Hst3.
    clear IHt1. clear IHt2. clear IHt3.
    clear t1 t2 t3.
    induction n.
    { intros. eapply multistep_preserves_R'.
    2:{ eapply multi_step. eapply ST_NrecN0... econstructor. }
      eapply multistep_preserves_R... econstructor. }
    { assert (H2': Rel ℕ (nval Γ0 n)).
      simp Rel. apply value_halts...
      simp Rel in IHt1'.
      destruct IHt1' as [Hh1 H1].
      eapply multistep_preserves_R'.
    2:{ eapply multi_trans.
        eapply multistep_NrecS... econstructor. }
      eapply H1.
      eapply IHn... } }
  { (* Tuple *)
    intros sb H.
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
    intros sb H.
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
    intros sb H.
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
    intros sb H.
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
    intros sb H.
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
    intros sb H.
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

Theorem soundness : forall τ (t t' : tm [] τ),
  (t -->* t') -> ⟦t⟧ₜₘ = ⟦t'⟧ₜₘ.
Proof with quick.
  intros.
  induction H...
  rewrite <- IHmulti.
  dependent induction H;
    extensionality ctx; simp denote_tm in *; quick;
    try solve [erewrite IHstep; constructor; quick]...
  { rewrite <- denote_sub_commutes...
    unfold hd_sub. simp cons_sub.
    destruct ctx... }
  { unfold compose.
    induction i...
    { induction n... }
    { unfold shave_fin. rewrite IHi... } }
  { specialize IHstep with t2 t2' t2'...
    rewrites... constructor. }
  { destruct (⟦ e ⟧ₜₘ ctx)... rewrite (IHstep t1 t1' t1')... constructor. }
  { destruct (⟦ e ⟧ₜₘ ctx)... rewrite (IHstep t2 t2' t2')... constructor. }
Qed.
