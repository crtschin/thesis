Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Relations.
Require Import Logic.JMeq.
Require Vectors.Fin.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.

Require Import CoLoR.Util.Vector.VecUtil.
Require Import Equations.Equations.

Open Scope list_scope.

Inductive ty :=
  | bool : ty
  | arrow : ty -> ty -> ty.
Notation "A → B" := (arrow A B) (right associativity, at level 20).

Definition Ctx := list ty.

Section extrinsic.
  (* Extrinsic formulation *)
  Require Import PeanoNat.
  Inductive tm : Type :=
    | var : nat -> tm
    | app : tm -> tm -> tm
    | abs : tm -> tm
    | tru : tm
    | fls : tm.

  Definition lt_S_length : forall {A} {l : list A} {n a},
    S n < length (a::l) -> n < length l.
  Proof with eauto.
    intros. simpl in H.
    unfold lt in *.
    inversion H...
    Print le.
    apply (@Nat.le_trans (S n) (S (S n)))...
  Defined.

  Equations elem {A} (n : nat) (l : list A) (pf : n < length l) : A :=
  elem O nil pf with pf := {};
  elem O (cons a l) _ := a;
  elem (S n) nil pf with pf := {};
  elem (S n) (cons a l) pf := elem n l (lt_S_length pf).

  Local Reserved Notation "Γ |- t ∷ τ" (at level 45).
  Inductive has_type : Ctx -> tm -> ty -> Prop :=
    | T_var : forall Γ n (pf : n < length Γ),
      Γ |- var n ∷ elem n Γ pf
    | T_app : forall Γ τ σ t1 t2,
      Γ |- t1 ∷ σ → τ ->
      Γ |- t2 ∷ σ ->
      Γ |- app t1 t2 ∷ τ
    | T_abs : forall Γ τ σ t,
      (σ::Γ) |- t ∷ τ ->
      Γ |- abs t ∷ σ → τ
    | T_tru : forall Γ,
      Γ |- tru ∷ bool
    | T_fls : forall Γ,
      Γ |- fls ∷ bool
  where "Γ |- t ∷ τ" := (has_type Γ t τ).

  Fixpoint substitute (n : nat) x t : tm :=
    match t with
    | var m => if n =? m then x else t
    | app t1 t2 =>
      app (substitute n x t1) (substitute n x t2)
    | abs t => abs (substitute (S n) x t)
    | tru => tru
    | fls => fls
    end.

  Lemma typing_ex1 : (has_type [bool] (var 0) bool).
    assert (H: 0 < length [bool]).
    { constructor. }
    assert (H': elem 0 [bool] H = bool).
    { simp elem. auto. }
    rewrite <- H'.
    apply T_var.
  Qed.

  Inductive value : tm -> Prop :=
    | v_abs : forall t,
        value (abs t)
    | v_tru : value tru
    | v_fls : value fls.

  Local Reserved Notation "t1 '-->' t2" (at level 40).
  Inductive step : tm -> tm -> Prop :=
    | ST_App1 : forall t1 t1' t2,
          t1 --> t1' ->
          app t1 t2 --> app t1' t2
    | ST_App2 : forall v1 t2 t2',
          value v1 ->
          t2 --> t2' ->
          app v1 t2 --> app v1 t2'
    | ST_AppAbs : forall t v,
          value v ->
          app (abs t) v --> substitute 0 v t
  where "t1 '-->' t2" := (step t1 t2).
End extrinsic.
Reset extrinsic.

Section intrinsic.
  Reserved Notation "τ '∈' Γ" (at level 75).
  Inductive Var : Ctx -> ty -> Type :=
    | Top : forall Γ τ, τ ∈ (τ::Γ)
    | Pop : forall Γ τ σ, τ ∈ Γ -> τ ∈ (σ::Γ)
  where "x ∈ Γ" := (Var Γ x).

  Derive Signature for Var.

  Inductive tm : Ctx -> ty -> Type :=
    | var : forall Γ τ,
      τ ∈ Γ -> tm Γ τ
    | app : forall Γ τ σ,
      tm Γ (σ → τ) -> tm Γ σ -> tm Γ τ
    | abs : forall Γ τ σ,
      tm (σ::Γ) τ -> tm Γ (σ → τ)
    | tru : forall Γ, tm Γ bool
    | fls : forall Γ, tm Γ bool.

  Definition ren (Γ Γ' : list ty) :=
    forall τ, Var Γ τ -> Var Γ' τ.

  Definition sub (Γ Γ' : list ty) :=
    forall τ, Var Γ τ -> tm Γ' τ.

  Equations rename_lifted {Γ Γ' τ} (r : ren Γ Γ')
    : ren (τ::Γ) (τ::Γ') :=
  rename_lifted r τ (Top Γ τ) => Top Γ' τ;
  rename_lifted r τ (Pop Γ τ σ v) => Pop Γ' τ σ (r τ v).

  Fixpoint rename {Γ Γ' τ} (r : ren Γ Γ')
    (t : tm Γ τ) : (tm Γ' τ) :=
    match t with
    | var v => var (r v)
    | app t1 t2 => app (rename r t1) (rename r t2)
    | abs f => abs (rename (rename_lifted r) f)
    | tru => tru
    | fls => fls
    end.

  (* Definition shift {Γ τ σ} : tm Γ τ -> tm (σ::Γ) τ
    := substitute (fun τ x => var (σ::Γ) τ x). *)
  Definition shift {Γ τ σ} : tm Γ τ -> tm (σ::Γ) τ
    := rename (fun τ x => Pop Γ τ σ x).

  Equations substitute_lifted {Γ Γ' τ} (s : sub Γ Γ')
    : sub (τ::Γ) (τ::Γ') :=
  substitute_lifted s τ (Top Γ σ) := var (σ::Γ') σ (Top Γ' σ);
  substitute_lifted s τ (Pop Γ τ σ v) := shift (s τ v).


  (* τ1 :: τ2 :: τ3 :: Γ
  cons_sub t1 (cons_sub t2 (cons_sub t3 id_sub))
  (| t1 ; t2 ; t3 |) : sub (τ1::τ2::τ3::Γ) Γ *)

  Fixpoint substitute {Γ Γ' τ} (s : sub Γ Γ') (t : tm Γ τ) : tm Γ' τ :=
    match t with
    | var v => s v
    | app t1 t2 => app (substitute s t1) (substitute s t2)
    | abs f => abs (substitute (substitute_lifted s) f)
    | tru => tru
    | fls => fls
    end.

  Inductive value : forall {Γ τ}, tm Γ τ -> Prop :=
    | v_abs : forall Γ τ σ (t : tm (σ::Γ) τ),
        value (abs Γ τ σ t)
    | v_tru : forall Γ, value (tru Γ)
    | v_fls : forall Γ, value (fls Γ).

  Local Reserved Notation "t1 '-->' t2" (at level 40).
  Inductive step : forall {Γ τ}, tm Γ τ -> tm Γ τ -> Prop :=
    | ST_AppAbs : forall t v,
          value v ->
          app (abs t) v --> substitute (cons_sub v id_sub) t
    | ST_App1 : forall t1 t1' t2,
          t1 --> t1' ->
          app t1 t2 --> app t1' t2
    | ST_App2 : forall v1 t2 t2',
          value v1 ->
          t2 --> t2' ->
          app v1 t2 --> app v1 t2'
  where "t1 '-->' t2" := (step t1 t2).