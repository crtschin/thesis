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
Import EqNotations.

Require Import AD.Definitions.
Require Import AD.Tactics.

Local Open Scope type_scope.
Local Open Scope list_scope.


(*
  Attempt at encoding a small SSA (static single assignment) language
    intrinsically.

    Adapted from both Software foundations and
      https://www.jantar.org/papers/chakravarty03perspective.pdf
*)

Definition block Γ := Env Γ -> Env Γ.
Equations lift_block {Γ τ} (t : tm Γ τ) :
  block Γ -> block (τ::Γ) :=
lift_block t f (env_cons t γ) := env_cons t (f γ).

(* Inductive subctx : Ctx -> Ctx -> Type :=
  | subctx_same : forall {Γ}, subctx Γ Γ
  | subctx_rem : forall {Γ Γ'} {τ : ty} {t: tm Γ τ},
    subctx Γ Γ' -> subctx (τ::Γ) Γ'.

Equations weaken {Γ Γ'}:
  (subctx Γ Γ') -> block Γ' -> block Γ :=
weaken subctx_same b e := e;
weaken (@subctx_rem Γ Γ' τ t s) b e := lift_block t (weaken s b) e.

Equations weaken_env {Γ Γ'}:
  (subctx Γ Γ') -> Env Γ' -> Env Γ :=
weaken_env subctx_same e := e;
weaken_env (@subctx_rem Γ Γ' τ t s) e := env_cons t (weaken_env s e).

Equations weaken_tm {Γ Γ' τ}:
  (subctx Γ Γ') -> tm Γ' τ -> tm Γ τ :=
weaken_tm subctx_same t := t;
weaken_tm (@subctx_rem Γ Γ' σ r s) t := shift (weaken_tm s t). *)

Definition State Γ := (Env Γ * list (block Γ)).
Fail Inductive com : forall (Γ Γ': Ctx),
  State Γ -> State Γ' -> ty -> Type :=
  | CReturn : forall {Γ γ φ τ},
    tm Γ τ ->
    com Γ Γ (γ, φ) (γ, φ) τ
  | CSeq : forall {Γ Γ' Γ'' τ σ γ γ' γ'' φ φ' φ''},
    com Γ Γ' (γ, φ) (γ', φ') τ ->
    com Γ' Γ'' (γ', φ') (γ'', φ'') σ ->
    com Γ Γ'' (γ, φ) (γ'', φ'') σ
  | CInit : forall {Γ τ σ γ φ} (t : tm Γ σ),
    com Γ (σ::Γ) (γ, φ) ((env_cons t γ), (map (lift_block t) φ)) τ
  | CCall : forall {Γ τ f γ φ},
    In f φ ->
    com Γ Γ (γ, φ) (f γ, φ) τ
  | CBlock : forall {Γ Γ' τ γ γ' φ φ'}
    (c : com Γ Γ' (γ, φ) (γ', φ') τ),
    com Γ Γ (γ, φ) (γ, compile c::φ) τ.

Notation "'RETURN' t" :=
  (CReturn t) (at level 65).
Notation "'init' t" :=
  (@CInit _ Real _ _ _ t) (at level 40, left associativity).
Notation "c ;; c'" :=
  (CSeq c c') (at level 65, right associativity).
Notation "'call' f" :=
  (CCall f) (at level 40, left associativity).
Notation "'block' { f }" :=
  (CBlock f) (at level 40, left associativity).

Definition com_add_ex :=
  @CInit [] Real Real env_nil [] (const [] 1) ;;
  init (const _ 2) ;;
  RETURN (add _ (var _ _ (Top _ Real)) (var _ _ (Pop _ _ _ (Top _ Real)))).
