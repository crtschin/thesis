Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Arith.PeanoNat.
Require Import Coquelicot.Coquelicot.
Require Import Coq.Program.Equality.
Require Import Arith_base.
Import EqNotations.

From AD Require Import Definitions.
From AD Require Import Macro.
From AD Require Import Diffeology.

Local Open Scope nat_scope.
Local Open Scope R_scope.

(*
  Maps types in 'ty' to an underlying Type
  given a proof that that type is a diffeological space
*)
Fixpoint denote_t τ : DiffeoSp :=
  match τ with
  | Real => R_diffeology
  | Prod τ1 τ2 => denote_t τ1 *** denote_t τ2
  | Arrow τ1 τ2 => denote_t τ1 -D> denote_t τ2
  end.

(* Example denote_t_ex :
  denote_t ((Real × Real × Real × Real) → (Real × Real)) =
    diff_smooth (denote_t (Real × Real × Real × Real)) (denote_t (Real × Real)).
Proof. trivial. Qed. *)

Fixpoint denote_ctx Γ : DiffeoSp :=
  match Γ with
  | [] => unit_diffeology
  | τ :: Γ' => denote_t τ *** denote_ctx Γ'
  end.

Fixpoint denote_v {Γ τ} (v: τ ∈ Γ) : denote_ctx Γ -d> denote_t τ :=
  match v with
  | Top Γ' τ' => product_first
  | Pop Γ' τ' σ x => diffeological_smooth_comp (denote_v x) product_second
  end.

Fixpoint denote_tm {Γ τ} (t : tm Γ τ)
    : denote_ctx Γ -d> denote_t τ :=
  match t with
  | var σ v => denote_v v

  | const r => constant_smooth (r : carrier R_diffeology)
  | add t1 t2 =>
      uncurry add_smooth ∘d product_smooth (denote_tm t1) (denote_tm t2)

  | app σ ρ t1 t2 => diffeological_smooth_app (denote_tm t1) (denote_tm t2)
  | abs σ ρ f => curry (denote_tm f)

  | tuple σ ρ t1 t2 => product_smooth (denote_tm t1) (denote_tm t2)
  | first σ ρ t => product_first ∘d denote_tm t
  | second σ ρ t => product_second ∘d denote_tm t
  end.

Program Fixpoint S τ
  : (R -> denote_t τ) -> (R -> denote_t (Dt τ)) -> Prop :=
  match τ with
  | Real => fun f g =>
    g = fun u => (f u, Derive f u)
  | σ × ρ => fun f g =>
    forall f1 f2 g1 g2,
      S σ f1 f2 ->
      S ρ g1 g2 ->
        (f = fun r => (f1 r, g1 r)) /\
        (g = fun r => (f2 r, g2 r))
  | σ → ρ => fun f g =>
    forall f1 f2 g1 g2 (s1 : S σ g1 g2),
      S ρ (fun x => functional_diffeology_app (f1 x) (g1 x))
          (fun x => functional_diffeology_app (f2 x) (g2 x)) ->
      f = f1 /\ g = f2
  end.
