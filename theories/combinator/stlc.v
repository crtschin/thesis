Require Import Lists.List.
Import ListNotations.
Require Import Reals.
Require Import Coq.Program.Basics.
Require Import Equations.Equations.
Require Import CoLoR.Util.Vector.VecUtil.

Require Import AD.types.
Require Import AD.combinator.
Local Open Scope program_scope.

Definition Ctx : Type := list ty.

Reserved Notation "x ∈ Γ" (at level 75).
Inductive Var : Ctx -> ty -> Type :=
  | Top : forall {Γ τ}, τ ∈ τ::Γ
  | Pop : forall {Γ τ σ}, τ ∈ Γ -> τ ∈ σ::Γ
where  "x ∈ Γ" := (Var Γ x).
Derive Signature for Var.

(* STLC *)
Inductive tm (Γ : Ctx) : ty -> Type :=
  (* Base *)
  | var : forall {τ},
    τ ∈ Γ -> tm Γ τ
  | app : forall {τ σ},
    tm Γ (σ → τ) -> tm Γ σ -> tm Γ τ
  | abs : forall {τ σ},
    @tm (σ::Γ) τ -> tm Γ (σ → τ)

  (* Products *)
  | tuple : forall {A B},
    tm Γ A -> tm Γ B -> tm Γ (A × B)
  | first : forall {A B},
    tm Γ (A × B) -> tm Γ A
  | second : forall {A B},
    tm Γ (A × B) -> tm Γ B

  (* Reals *)
  | plus :
    tm Γ Real -> tm Γ Real -> tm Γ Real
  | rval : R -> tm Γ Real
  | mplus : forall {n},
    tm Γ (ℝ^n) -> tm Γ (ℝ^n) -> tm Γ (ℝ^n)
  | mrval : forall {n}, vector R n -> tm Γ (ℝ^n)

  (* Unit *)
  | it : tm Γ Unit
.

Definition ren (Γ Γ' : list ty) :=
  forall τ, Var Γ τ -> Var Γ' τ.
Definition sub (Γ Γ' : list ty) :=
  forall τ, Var Γ τ -> tm Γ' τ.

(* Helper functions for defining substitutions on the i'th variable *)
Definition id_sub {Γ} : sub Γ Γ := @var Γ.
Equations cons_sub {Γ Γ' τ} (e: tm Γ' τ) (s: sub Γ Γ')
  : sub (τ::Γ) Γ' :=
cons_sub e s τ (Top) := e;
cons_sub e s τ (@Pop Γ τ σ v) := s τ v.

Notation "| a ; .. ; b |" :=
  (cons_sub a  .. ( cons_sub b id_sub) .. )
  (at level 12, no associativity).

(* For decomposing substitutions and renames *)
Definition hd_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : tm Γ' τ := s τ Top.
Definition tl_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : sub Γ Γ'
  := fun σ x => s σ (Pop x).

Definition id_ren {Γ} : ren Γ Γ := fun _ x => x.
Definition hd_ren {Γ Γ' τ} (r : ren (τ::Γ) Γ') : Var Γ' τ
  := (r τ Top).
Definition tl_ren {Γ Γ' τ} (r : ren (τ::Γ) Γ') : ren Γ Γ'
  := fun σ x => r σ (Pop x).

Equations rename_lifted {Γ Γ' τ} (r : ren Γ Γ')
  : ren (τ::Γ) (τ::Γ') :=
rename_lifted r τ Top => Top;
rename_lifted r τ (@Pop Γ τ σ v) => @Pop Γ' τ σ (r τ v).

Fixpoint rename {Γ Γ' τ} (r : ren Γ Γ') (t : tm Γ τ) : (tm Γ' τ) :=
  match t with
  (* STLC *)
  | var _ v => var _ (r _ v)
  | app _ t1 t2 => app _ (rename r t1) (rename r t2)
  | abs _ f => abs _ (rename (rename_lifted r) f)

  (* Reals *)
  | rval _ r => rval _ r
  | plus _ t1 t2 => plus _ (rename r t1) (rename r t2)
  | mrval _ r => mrval _ r
  | mplus _ t1 t2 => mplus _ (rename r t1) (rename r t2)

  (* Products *)
  | tuple _ t1 t2 => tuple _ (rename r t1) (rename r t2)
  | first _ p => first _ (rename r p)
  | second _ p => second _ (rename r p)

  (* Unit *)
  | it _ => it _
  end.

Definition shift {Γ τ σ} : tm Γ τ -> tm (σ::Γ) τ
  := rename (fun ρ x => Pop x).

Equations substitute_lifted {Γ Γ' τ} (s : sub Γ Γ')
  : sub (τ::Γ) (τ::Γ') :=
substitute_lifted s τ (@Top Γ σ) := var (σ::Γ') Top;
substitute_lifted s τ (@Pop Γ τ σ v) := shift (s τ v).

Fixpoint substitute {Γ Γ' τ} (s : sub Γ Γ') (t : tm Γ τ) : tm Γ' τ :=
  match t with
  (* STLC *)
  | var _ v => s _ v
  | app _ t1 t2 => app _ (substitute s t1) (substitute s t2)
  | abs _ f => abs _ (substitute (substitute_lifted s) f)

  (* Reals *)
  | rval _ r => rval _ r
  | plus _ t1 t2 => plus _ (substitute s t1) (substitute s t2)
  | mrval _ r => mrval _ r
  | mplus _ t1 t2 => mplus _ (substitute s t1) (substitute s t2)

  (* Products *)
  | tuple _ t1 t2 => tuple  _ (substitute s t1) (substitute s t2)
  | first _ p => first _ (substitute s p)
  | second _ p => second _ (substitute s p)

  (* Unit *)
  | it _ => it _
  end.

Equations shift_var {Γ : list ty} {τ σ ρ : ty}
  : τ ∈ σ :: Γ -> τ ∈ σ :: ρ :: Γ :=
shift_var (@Top Γ τ) := @Top (ρ::Γ) τ;
shift_var (@Pop Γ τ σ v) := @Pop (ρ::Γ) τ σ (@Pop Γ τ ρ v).

Equations swap_var {Γ : list ty} {τ σ ρ : ty}
  : τ ∈ ρ :: σ :: Γ -> τ ∈ σ :: ρ :: Γ :=
swap_var (@Top Γ τ) := @Pop _ _ _ (@Top _ _);
swap_var (@Pop Γ τ σ v) := shift_var v.

Definition swap {Γ τ σ ρ} (t : tm (ρ::σ::Γ) τ) : tm (σ::ρ::Γ) τ
  := substitute (fun τ x => var (σ::ρ::Γ) (swap_var x)) t.