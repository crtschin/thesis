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

  Inductive value : tm -> Prop :=
    | v_abs : forall t,
        value (abs t)
    | v_tru : value tru
    | v_fls : value fls.

  Local Reserved Notation "t1 '-->' t2" (at level 40).
  Inductive step : tm -> tm -> Prop :=
    | ST_AppAbs : forall t v,
          value v ->
          app (abs t) v --> substitute 0 v t
    | ST_App1 : forall t1 t1' t2,
          t1 --> t1' ->
          app t1 t2 --> app t1' t2
    | ST_App2 : forall v1 t2 t2',
          value v1 ->
          t2 --> t2' ->
          app v1 t2 --> app v1 t2'
  where "t1 '-->' t2" := (step t1 t2).
End extrinsic.
Reset extrinsic.

Section intrinsic.
  Inductive Var : Ctx -> ty -> Set :=
    | Top : forall Γ τ, Var (τ::Γ) τ
    | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ.
  Notation "x ∈ Γ" := (Var Γ x) (at level 75).

  Inductive tm : Ctx -> ty -> Set :=
    | var : forall Γ τ,
      τ ∈ Γ -> tm Γ τ
    | app : forall Γ τ σ,
      tm Γ (σ → τ) -> tm Γ σ -> tm Γ τ
    | abs : forall Γ τ σ,
      tm (σ::Γ) τ -> tm Γ (σ → τ)
    | tru : forall Γ, tm Γ bool
    | fls : forall Γ, tm Γ bool.

  Inductive value : forall {Γ τ}, tm Γ τ -> Prop :=
    | v_abs : forall Γ τ σ (t : tm (σ::Γ) τ),
        value (abs Γ τ σ t)
    | v_tru : forall Γ, value (tru Γ)
    | v_fls : forall Γ, value (fls Γ).

  Local Reserved Notation "t1 '-->' t2" (at level 40).
  Inductive step : forall {Γ τ}, tm Γ τ -> tm Γ τ -> Prop :=
    | ST_AppAbs : forall t v,
          value v ->
          app (abs t) v --> substitute 0 v t
    | ST_App1 : forall t1 t1' t2,
          t1 --> t1' ->
          app t1 t2 --> app t1' t2
    | ST_App2 : forall v1 t2 t2',
          value v1 ->
          t2 --> t2' ->
          app v1 t2 --> app v1 t2'
  where "t1 '-->' t2" := (step t1 t2).