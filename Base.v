Set Warnings "-notation-overridden,-parsing".

Require Import Lists.List.
Import ListNotations.
Require Import Strings.String.
Require Import Reals.
Require Import Logic.JMeq.
Require Import Arith.PeanoNat.

Open Scope R_scope.

(*
Literature:

Main paper:
- Correctness of Automatic Differentiation via
  Diffeologies and Categorical Gluing by Huot, Stanton and Vakar.

Well-scoped, well-typed debruijn indices in language:
- Strongly Typed Term Representations in Coq by Benton, et al.
- Type-Preserving Renaming and Substitution by McBride.
- Parametric Higher-Order Abstract Syntax for Mechanized Semantics by Chlipala.

GADTs in Coq and the Program command:
- Elimination with a motive by McBride.
- Program-ing Finger Trees using Coq by Sozeau.

Notational conventions:
  capital greeks for typing environment
  lowercase greeks for types
  lowercase latin for terms
*)

Inductive ty : Type :=
  | Real : ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
.

Notation "A × B" := (Prod A B) (left associativity, at level 90).
Notation "A → B" := (Arrow A B) (right associativity, at level 20).



Module fst_attempt.

(* Just STLC with debruijn *)

Inductive smf : Type :=
  (* Base STLC *)
  | var : string -> smf
  | app : smf -> smf -> smf
  | abs : string -> ty -> smf -> smf

  (* Reals *)
  | const : R -> smf
  | add : smf -> smf -> smf

  (* Products (currently using projection instead of pattern matching) *)
  | pair : smf -> smf -> smf
  | fst : smf -> smf
  | snd : smf -> smf
.

Fixpoint Dt (τ : ty) : ty :=
  match τ with
  | Real => Real × Real
  | t1 × t2 => Dt t1 × Dt t2
  | t1 → t2 => Dt t1 → Dt t2
  end.

Fixpoint Dsmf (t : smf) : smf :=
  match t with
  | var s => t
  | app t1 t2 => app (Dsmf t1) (Dsmf t2)
  | abs s τ f => abs s τ (Dsmf f)

  | const r => pair t (const 0)
  | add t1 t2 =>
    let d1 := (Dsmf t1) in
    let d2 := (Dsmf t2) in
      pair (add (fst d1) (fst d2)) (add (snd d1) (snd d2))

  | pair t1 t2 => pair (Dsmf t1) (Dsmf t2)
  | fst p => fst (Dsmf p)
  | snd p => snd (Dsmf p)
  end.

Notation Ctx := (list (string * ty)).

Fixpoint Dctx (Γ : Ctx) : Ctx :=
  match Γ with
  | nil => nil
  | (h, τ) :: t => (h, Dt τ) :: Dctx t
  end.

Fixpoint lookup (Γ : Ctx) (x : string) : option ty :=
  match Γ with
  | nil => None
  | (h, τ) :: Γ' => if eqb x h then Some τ else lookup Γ' x
  end.

Inductive has_type : Ctx -> smf -> ty -> Prop :=
  | T_var : forall Γ x τ,
    lookup Γ x = Some τ ->
    has_type Γ (var x) τ
  | T_app : forall Γ t1 t2 τ σ,
    has_type Γ t1 (τ → σ) ->
    has_type Γ t2 τ ->
    has_type Γ (app t1 t2) σ
  | T_abs : forall Γ x t τ σ,
    has_type Γ t σ ->
    has_type ((x,τ)::Γ) (abs x τ t) (τ → σ)

  | T_const : forall Γ c,
    has_type Γ (const c) Real
  | T_add : forall Γ t1 t2,
    has_type Γ t2 Real ->
    has_type Γ t1 Real ->
    has_type Γ (add t1 t2) Real

  | T_pair : forall Γ t1 t2 τ σ,
    has_type Γ t1 τ ->
    has_type Γ t2 σ ->
    has_type Γ (pair t1 t2) (τ × σ)
  | T_fst : forall Γ τ σ p,
    has_type Γ p (τ × σ) ->
    has_type Γ (fst p) τ
  | T_snd : forall Γ τ σ p,
    has_type Γ p (τ × σ) ->
    has_type Γ (snd p) σ
.

Notation "Γ ⊢ t ∷ τ" := (has_type Γ t τ) (at level 70).

(* Lemma 1 *)

Lemma functorial_macro : forall Γ t τ,
  Γ ⊢ t ∷ τ -> Dctx Γ ⊢ Dsmf t ∷ Dt τ.
Proof with eauto.
Admitted.

(* Theorem 1 *)

End fst_attempt.


Module snd_attempt.

(* STLC with well-typed well-scoped debruijn *)

Notation Ctx := (list ty).

Inductive Var : Ctx -> ty -> Type :=
  | Top : forall Γ τ, Var (τ::Γ) τ
  | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ
.

Notation "x ∈ C" := (Var C x) (at level 75).

Inductive smf (Γ : Ctx) : ty -> Type :=
  (* Base STLC *)
  | var : forall τ,
    τ ∈ Γ -> smf Γ τ
  | app : forall τ σ,
    smf Γ (σ → τ) ->
    smf Γ σ ->
    smf Γ τ
  | abs : forall τ σ,
    smf (σ::Γ) τ -> smf Γ (σ → τ)

  (* Reals *)
  | const : R -> smf Γ Real
  | add : smf Γ Real -> smf Γ Real -> smf Γ Real

  (* Products (currently using projection instead of pattern matching) *)
  | tuple : forall τ σ,
    smf Γ τ ->
    smf Γ σ ->
    smf Γ (τ × σ)
  | fst : forall τ σ, smf Γ (τ × σ) -> smf Γ τ
  | snd : forall τ σ, smf Γ (τ × σ) -> smf Γ σ
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
(* Examples *)

(* Functorial macro *)

Fixpoint Dt τ : ty :=
  match τ with
  | Real => Real × Real
  | t1 × t2 => Dt t1 × Dt t2
  | t1 → t2 => Dt t1 → Dt t2
  end.

Fixpoint Dv Γ τ (v: τ ∈ Γ) : (Dt τ) ∈ (map Dt Γ) :=
  match v with
  | Top Γ τ => Top (map Dt Γ) (Dt τ)
  | Pop Γ τ σ t => Pop (map Dt Γ) (Dt τ) (Dt σ) (Dv Γ τ t)
  end.

Program Fixpoint Dsmf {Γ τ} (t : smf Γ τ) : smf (map Dt Γ) (Dt τ) :=
  match t with
  | var _ _ v => var (map Dt Γ) (Dt τ) (Dv Γ τ v)
  | app _ _ _ t1 t2 => app _ _ _ (Dsmf t1) (Dsmf t2)
  | abs _ _ _ f => abs _ _ _ (Dsmf f)

  | const _ r => tuple _ _ _ (const _ r) (const _ 0)
  | add _ t1 t2 =>
    let d1 := (Dsmf t1) in
    let d2 := (Dsmf t2) in
    tuple _ _ _
      (add _ (fst _ _ _ d1) (fst _ _ _ d2))
      (add _ (snd _ _ _ d1) (snd _ _ _ d2))

  | tuple _ _ _ t1 t2 => tuple _ _ _ (Dsmf t1) (Dsmf t2)
  | fst _ _ _ p => fst _ _ _ (Dsmf p)
  | snd _ _ _ p => snd _ _ _ (Dsmf p)
  end.

Lemma Dt_lift_var Γ τ : τ ∈ Γ -> (Dt τ) ∈ (map Dt Γ).
Proof with eauto.
  intros. induction H; constructor. assumption.
Qed.

(*
  Substitution

  Adapted from:
    Strongly Typed Term Representations in Coq by Benton, et al.
*)

(* Substitutes a variable typed in one context and swaps it
  with an expression with the same type typed in a different context.
*)
Definition sub Γ Γ' := forall τ, Var Γ τ -> smf Γ' τ.
Definition ren Γ Γ' := forall τ, Var Γ τ -> Var Γ' τ.

(* Helper functions for defining substitutions on the i'th variable *)
Definition id_sub {Γ} : sub Γ Γ := var Γ.
Program Definition cons_sub {Γ Γ' τ}
    (e: smf Γ' τ) (s: sub Γ Γ') : sub (τ::Γ) Γ'
  := fun σ (x : Var (τ::Γ) σ) =>
    match x with
    | Top _ _ => e
    | Pop _ _ _ v' => s σ v'
    end.

Notation "| a ; .. ; b |" :=
  (cons_sub a  .. ( cons_sub b id_sub) .. )
  (at level 12, no associativity).

(* For decomposing substitutions *)
Definition hd_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : smf Γ' τ := s τ (Top Γ τ).
Definition tl_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : sub Γ Γ'
  := fun σ x => s σ (Pop Γ σ τ x).

Program Definition rename_lifted {Γ Γ' τ} (r : ren Γ Γ')
  : ren (τ::Γ) (τ::Γ') := fun σ v =>
  match v with
  | Top _ _  => Top Γ' τ
  | Pop _ _ _ v' => Pop Γ' σ τ (r σ v')
  end.

Fixpoint rename {Γ Γ' τ} (r : ren Γ Γ') (t : smf Γ τ) : (smf Γ' τ) :=
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

Definition shift {Γ τ σ} : smf Γ τ -> smf (σ::Γ) τ
  := rename (fun ρ x => Pop Γ ρ σ x).

Program Definition substitute_lifted {Γ Γ' τ} (s : sub Γ Γ')
  : sub (τ::Γ) (τ::Γ') := fun τ' v =>
  match v with
  | Top _ _  => var (τ::Γ') τ (Top Γ' τ)
  | Pop _ _ _ w => shift (s τ' w)
  end.

Fixpoint substitute {Γ Γ' τ} (s : sub Γ Γ') (t : smf Γ τ) : smf Γ' τ :=
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
Definition has_type {Γ τ} (t : smf Γ τ) : ty := τ.
Notation "Γ ⊢ t ∷ τ" := (@has_type Γ τ t) (at level 70).
Corollary has_type_refl Γ τ (t : smf Γ τ) :
  has_type t = τ.
Proof. reflexivity. Qed.

(*
  Evaluation
*)

Inductive value : forall Γ τ, smf Γ τ -> Prop :=
  | v_real : forall Γ r,
      value Γ Real (const Γ r)
  | v_pair : forall Γ τ σ t1 t2,
      value Γ τ t1 ->
      value Γ σ t2 ->
      value Γ (τ × σ) (tuple Γ τ σ t1 t2)
  | v_abs : forall Γ τ σ t,
      value Γ (σ → τ) (abs Γ τ σ t)
.
Hint Constructors value.

Inductive eval : forall τ, smf [] τ -> smf [] τ -> Prop :=
  | EV_App : forall τ σ t1 t1' t2 t2' v,
      eval (σ → τ) t1 (abs _ τ σ t1') ->
      eval σ t2 t2' ->
      eval τ (substitute (| t2' |) t1') v ->
        eval τ (app _ τ σ t1 t2) v

  | EV_Add : forall t1 t1' t2 t2',
      eval Real t1 t1' ->
      eval Real t2 t2' ->
      eval Real (add _ t1 t2) (add _ t1' t2')

  | EV_Tuple : forall τ σ t1 t1' t2 t2',
      eval τ t1 t1' ->
      eval σ t2 t2' ->
      eval (τ × σ) (tuple _ τ σ t1 t2) (tuple _ τ σ t1' t2')
  | EV_FstTuple : forall τ σ t1 t2,
      eval τ (fst _ τ σ (tuple _ τ σ t1 t2)) t1
  | EV_SndTuple : forall τ σ t1 t2,
      eval σ (snd _ τ σ (tuple _ τ σ t1 t2)) t2
.

Lemma D_type : forall Γ τ
  (t : smf Γ τ),
  has_type (Dsmf t) = Dt τ.
Proof. trivial. Qed.

Lemma D_substitute : forall Γ Γ' τ
  (t : smf (τ::Γ) τ)
  (s : smf Γ τ)
  (sb : sub Γ Γ'),
  Dsmf (substitute (| s |) t) =
    substitute (| Dsmf s |) (Dsmf t).
Proof with eauto.
  induction τ; intros.
Admitted.