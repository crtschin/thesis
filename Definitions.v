Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.

Open Scope R_scope.

Inductive ty : Type :=
  | Real : ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
.

Notation "A × B" := (Prod A B) (left associativity, at level 90).
Notation "A → B" := (Arrow A B) (right associativity, at level 20).

(* STLC with well-typed well-scoped debruijn *)
(*
  Adapted from:
    - From Mathematics to Abstract Machine by Swierstra, et al.
    - Strongly Typed Term Representations in Coq by Benton, et al.
 *)

Notation Ctx := (list ty).

Inductive Var {T} : list T -> T -> Type :=
  | Top : forall Γ τ, Var (τ::Γ) τ
  | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ
.

Notation "x ∈ C" := (Var C x) (at level 75).

Inductive tm (Γ : Ctx) : ty -> Type :=
  (* Base STLC *)
  | var : forall τ,
    τ ∈ Γ -> tm Γ τ
  | app : forall τ σ,
    tm Γ (σ → τ) ->
    tm Γ σ ->
    tm Γ τ
  | abs : forall τ σ,
    tm (σ::Γ) τ -> tm Γ (σ → τ)

  (* Reals *)
  | const : R -> tm Γ Real
  | add : tm Γ Real -> tm Γ Real -> tm Γ Real

  (* Products (currently using projection instead of pattern matching) *)
  | tuple : forall τ σ,
    tm Γ τ ->
    tm Γ σ ->
    tm Γ (τ × σ)
  | fst : forall τ σ, tm Γ (τ × σ) -> tm Γ τ
  | snd : forall τ σ, tm Γ (τ × σ) -> tm Γ σ
.

Inductive Closed : ty -> Type :=
  | Closure : forall Γ τ, tm Γ τ -> Env Γ -> Closed τ
  | Clapp : forall τ σ, Closed (σ → τ) -> Closed σ -> Closed τ
  with Env : Ctx -> Type :=
  | Env_nil : Env []
  | Env_cons : forall Γ τ, Closed τ -> Env Γ -> Env (τ::Γ)
.

(* Examples *)
Definition ex_id :=
  abs [] Real Real
    (var [Real] Real (Top _ _)).

Definition ex_const :=
  abs [] (Real → Real) Real
    (abs [Real] (Real) (Real)
      (var [Real;Real] Real (Top [Real] Real))).

Definition ex_plus :=
  abs [] (Real → Real) Real
    (abs [Real] Real Real
      (add [Real;Real]
        (var [Real;Real] Real (Top [Real] Real))
          (var [Real;Real] Real (Top [Real] Real)))).

Definition neuron :=
  abs [] (Real → Real → Real) Real
    (abs [Real] (Real → Real) Real
      (abs [Real;Real] Real Real
        (add [Real;Real;Real]
          (add [Real;Real;Real]
            (var [Real;Real;Real] Real
              (Pop [Real;Real] Real Real (Top [Real] Real)))
            (var [Real;Real;Real] Real (Top [Real;Real] Real)))
          (var [Real;Real;Real] Real
            (Pop [Real;Real] Real Real
              (Pop [Real] Real Real
                (Top [] Real))))))).

(*
  Substitution

  Adapted from:
    Strongly Typed Term Representations in Coq by Benton, et al.
*)

(* Substitutes a variable typed in one context and swaps it
  with an expression with the same type typed in a different context.
*)
Definition sub Γ Γ' := forall (τ : ty), Var Γ τ -> tm Γ' τ.
Definition ren Γ Γ' := forall (τ : ty), Var Γ τ -> Var Γ' τ.

(* Helper functions for defining substitutions on the i'th variable *)
Definition id_sub {Γ} : sub Γ Γ := var Γ.
Program Definition cons_sub {Γ Γ' τ}
    (e: tm Γ' τ) (s: sub Γ Γ') : sub (τ::Γ) Γ'
  := fun σ (x : Var (τ::Γ) σ) =>
    match x with
    | Top _ _ => e
    | Pop _ _ _ v' => s σ v'
    end.

Notation "| a ; .. ; b |" :=
  (cons_sub a  .. ( cons_sub b id_sub) .. )
  (at level 12, no associativity).

(* For decomposing substitutions *)
Definition hd_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : tm Γ' τ := s τ (Top Γ τ).
Definition tl_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : sub Γ Γ'
  := fun σ x => s σ (Pop Γ σ τ x).

Program Definition rename_lifted {Γ Γ' τ} (r : ren Γ Γ')
  : ren (τ::Γ) (τ::Γ') := fun σ v =>
  match v with
  | Top _ _  => Top Γ' τ
  | Pop _ _ _ v' => Pop Γ' σ τ (r σ v')
  end.

Fixpoint rename {Γ Γ' τ} (r : ren Γ Γ') (t : tm Γ τ) : (tm Γ' τ) :=
  match t with
  | var _ _ v => var _ _ (r _ v)
  | app _ _ _ t1 t2 => app _ _ _ (rename r t1) (rename r t2)
  | abs _ _ _ f => abs _ _ _ (rename (rename_lifted r) f)

  | const _ r => const _ r
  | add _ t1 t2 => add _ (rename r t1) (rename r t2)

  | tuple _ _ _ t1 t2 => tuple _ _ _(rename r t1) (rename r t2)
  | fst _ _ _ p => fst _ _ _ (rename r p)
  | snd _ _ _ p => snd _ _ _ (rename r p)
  end.

Definition shift {Γ τ σ} : tm Γ τ -> tm (σ::Γ) τ
  := rename (fun ρ x => Pop Γ ρ σ x).

Program Definition substitute_lifted {Γ Γ' τ} (s : sub Γ Γ')
  : sub (τ::Γ) (τ::Γ') := fun τ' v =>
  match v with
  | Top _ _  => var (τ::Γ') τ (Top Γ' τ)
  | Pop _ _ _ w => shift (s τ' w)
  end.

Fixpoint substitute {Γ Γ' τ} (s : sub Γ Γ') (t : tm Γ τ) : tm Γ' τ :=
  match t with
  | var _ _ v => s _ v
  | app _ _ _ t1 t2 => app _ _ _ (substitute s t1) (substitute s t2)
  | abs _ _ _ f => abs _ _ _ (substitute (substitute_lifted s) f)

  | const _ r => const _ r
  | add _ t1 t2 => add _ (substitute s t1) (substitute s t2)

  | tuple _ _ _ t1 t2 => tuple _ _ _ (substitute s t1) (substitute s t2)
  | fst _ _ _ p => fst _ _ _ (substitute s p)
  | snd _ _ _ p => snd _ _ _ (substitute s p)
  end.

(*
  Typing
  TODO: Redundant to define this considering it is builtin to the
   structure of the language?
*)
Definition has_type {Γ τ} (t : tm Γ τ) : ty := τ.
Notation "Γ ⊢ t ∷ τ" := (@has_type Γ τ t) (at level 70).
Corollary has_type_refl Γ τ (t : tm Γ τ) :
  has_type t = τ.
Proof. reflexivity. Qed.

(*
  Evaluation
*)

(*
  Adapted from:
    From Mathematics to Abstract Machine by Swierstra, et al.
 *)
Inductive value : forall τ, Closed τ -> Prop :=
  | v_real : forall Γ r env,
    value Real (Closure Γ Real (const Γ r) env)
  | v_tuple : forall Γ τ σ t1 t2 env,
    value τ (Closure Γ τ t1 env) ->
    value σ (Closure Γ σ t2 env) ->
    value (τ × σ) (Closure Γ (τ × σ) (tuple Γ τ σ t1 t2) env)
  | v_abs : forall Γ τ σ b env,
    value (σ → τ) (Closure Γ (σ → τ) (abs Γ τ σ b) env)
.

Hint Constructors value.

Reserved Notation "t1 '⇓' t2" (at level 40).
Inductive eval : forall {τ}, tm [] τ -> tm [] τ -> Prop :=
  | EV_App : forall τ σ t1 t1' t2 t2',
      t1 ⇓ (abs [] τ σ t1') ->
      t2 ⇓ t2' ->
        (app [] τ σ t1 t2) ⇓ (substitute (| t2' |) t1')

  | EV_Add : forall t1 t1' t2 t2',
      t1 ⇓ t1' ->
      t2 ⇓ t2' ->
      (add [] t1 t2) ⇓ (add [] t1' t2')

  | EV_Tuple : forall τ σ t1 t1' t2 t2',
      t1 ⇓ t1' ->
      t2 ⇓ t2' ->
      (tuple [] τ σ t1 t2) ⇓ (tuple [] τ σ t1' t2')
  | EV_FstTuple : forall τ σ t1 t2,
      (fst [] τ σ (tuple [] τ σ t1 t2)) ⇓ t1
  | EV_SndTuple : forall τ σ t1 t2,
      (snd [] τ σ (tuple [] τ σ t1 t2)) ⇓ t2
where "t '⇓' v" := (eval t v).

(*
  Adapted from Software Foundations vol.2
 *)
(* Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma value__normal : forall τ t, value [] τ t -> normal_form (eval τ) t.
Proof with eauto.
  intros τ t H; dependent induction H.
  - intros [t H']. inversion H'.
  - assert (@nil ty = []). reflexivity.
    assert (t1 ~= t1). reflexivity.
    assert (t2 ~= t2). reflexivity.
    pose proof (IHvalue1 t1 H1 H2).
    pose proof (IHvalue2 t2 H1 H3).
    intros [t H']...
    unfold normal_form, not in H4. unfold normal_form, not in H5.
    apply H4.
  - intros [t H']. inversion H'.
Qed.


Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Theorem eval_deterministic : forall τ,
  deterministic (eval τ).
Proof with eauto.
  unfold deterministic.
  intros τ x y1 y2 H H'.
  generalize dependent y2.
  induction H; intros y2 H'; inversion H'; subst.
  - inversion H.
  Admitted.
Qed. *)