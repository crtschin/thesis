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

Local Open Scope program_scope.
Local Open Scope R_scope.


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

Inductive subctx : Ctx -> Ctx -> Type :=
  | subctx_same : forall {Γ}, subctx Γ Γ
  | subctx_rem : forall {Γ Γ'} {τ : ty} {t: tm Γ τ},
    subctx Γ Γ' -> subctx (τ::Γ) Γ'.

Equations weaken {Γ Γ'}:
  (subctx Γ Γ') -> block Γ' -> block Γ :=
weaken subctx_same b e := e;
weaken (@subctx_rem Γ Γ' τ t s) b e := lift_block t (weaken s b) e.

Inductive com : forall (Γ : Ctx), Env Γ -> list (block Γ) -> Type :=
  | CSkip : forall {Γ γ φ}, com Γ γ φ
  | CInit : forall {Γ τ γ φ} (t : tm Γ τ),
    com Γ γ φ ->
    com (τ::Γ) (env_cons t γ) (map (lift_block t) φ)
  | CAss : forall {Γ τ γ φ} (t : tm Γ τ),
    com Γ γ φ ->
    τ ∈ Γ ->
    com (τ::Γ) (env_cons t γ) (map (lift_block t) φ)
  | CCall : forall {Γ f γ φ},
    com Γ γ φ ->
    In f φ ->
    com Γ (f γ) φ
  | CBlock : forall {Γ Γ' φ} {γ : Env Γ}
    (f : Env Γ' -> Env Γ') (w : subctx Γ Γ'),
    com Γ γ φ ->
    com Γ γ (weaken w f::φ)
.

Notation "'SKIP'" :=
  CSkip.
Notation "c ;; 'init' t" :=
  (CInit t c) (at level 65, right associativity).
Notation "c ;; v '::=' t" :=
  (CAss t c v) (at level 65, right associativity).
Notation "c ;; 'call' f" :=
  (CCall c f) (at level 65, right associativity).
Notation "c ;; w { f }" :=
  (CBlock f w c) (at level 65, right associativity).
