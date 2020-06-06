Require Import Lists.List.
Import ListNotations.
Require Import Reals.
Require Import Coq.Program.Basics.
Require Import Equations.Equations.

Local Open Scope program_scope.

(* Combinator Language definition *)

Inductive ty : Type :=
  | Real : ty
  | Unit : ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
.
Notation "'ℝ'" := (Real).
Notation "A × B" := (Prod A B) (left associativity, at level 89).
Notation "A → B" := (Arrow A B) (right associativity, at level 90).

(* Definition Ctx := list ty.

Inductive Var {T : Type} : list T -> T -> Type :=
  | Top : forall Γ τ, Var (τ::Γ) τ
  | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ
.
Derive Signature for Var.
Notation "x ∈ Γ" := (Var Γ x) (at level 75). *)

Inductive comb : ty -> ty -> Type :=
(* Category laws *)
  | id : forall {A}, comb A A
  | seq : forall {A B C},
    comb A B -> comb B C -> comb A C

  (* Monoidal *)
  | cross : forall {A B C D},
    comb A B -> comb C D -> comb (A × C) (B × D)

  (* Terminal *)
  | neg : forall {A},
    comb A Unit

  (* Cartesian *)
  | exl : forall {A B},
    comb (A × B) A
  | exr : forall {A B},
    comb (A × B)  B
  | dupl : forall {A},
    comb A (A × A)

  (* Closed *)
  | ev : forall {A B},
    comb ((A → B) × A) B
  (* | lam : forall {A B},
    comb B → (A → (B × A)) *)
  | curry : forall {A B C},
    comb (A × B) C -> comb A (B → C)
  | uncurry : forall {A B C},
    comb A (B → C) -> comb (A × B) C

  (* Const *)
  (* | cnst : forall {A},
    comb A A -> comb Unit A *)

  (* Numeric *)
  | cplus :
    comb (ℝ × ℝ) ℝ
  | crval : forall (r : R), comb Unit ℝ.

Notation "A ;; B" := (seq A B) (at level 40, left associativity).
Notation "<| A , B |>" := (dupl ;; cross A B) (at level 30).

(* Helpfull extras *)
Definition assoc1 {A B C} : comb ((A × B) × C) (A × (B × C)) :=
  <|exl;;exl, <|exl;;exr, exr|>|>.
Definition assoc2 {A B C} : comb (A × (B × C)) ((A × B) × C) :=
  <|<|exl, exr;;exl|>, exr;;exr|>.
Definition sym {A B} : comb (A × B) (B × A) :=
  <|exr, exl|>.

(* Denotations *)
Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t τ : Set :=
  match τ with
  | Real => R
  | Unit => unit
  | τ1 × τ2 => ⟦τ1⟧ₜ * ⟦τ2⟧ₜ
  | τ1 → τ2 => ⟦τ1⟧ₜ -> ⟦τ2⟧ₜ
  end
where "⟦ τ ⟧ₜ" := (denote_t τ).


(* Monoidal/Derivative operation *)

Equations Ot (τ : ty): comb Unit τ :=
  | ℝ => crval 0;
  | Unit => neg;
  | σ × ρ => <| (Ot σ), (Ot ρ) |>;
  (* | σ → ρ => Ot ρ ;; @lam σ ρ ;; id ;; _. *)
  | σ → ρ => curry (exl ;; (Ot ρ)).

Equations plust (τ : ty): comb (τ × τ) τ :=
  | ℝ => cplus;
  | Unit => neg;
  | σ × ρ =>
    <|
      <|exl;;exl, exr;;exl|>;;plust σ,
      <|exl;;exr, exr;;exr|>;; plust ρ
    |>;
  | σ → ρ => curry (
    <|
      <|exl ;; exl, exr|> ;; ev,
      <|exl ;; exr, exr|> ;; ev
    |> ;; plust ρ).

Fixpoint Dt (τ : ty) : ty * ty :=
  match τ with
  | ℝ => (ℝ, ℝ)
  | Unit => (Unit, Unit)
  | σ × ρ =>
      ((fst (Dt σ)) × (fst (Dt ρ)), (snd (Dt σ)) × (snd (Dt ρ)))
  | σ → ρ =>
      (fst (Dt σ) → (fst (Dt ρ) × (snd (Dt ρ) → snd (Dt σ)))
        , fst (Dt σ) × snd (Dt ρ))
  end.

(* Tips for writing this out:
    'Equations?' keywork shows the types of wildcards (_) and what's in scope.
    Liberal use of 'Check' and annotate what output type should be.
*)
Equations Dtm {τ σ} (t : comb τ σ)
  : (comb (fst (Dt τ)) (fst (Dt σ)) *
      comb (fst (Dt τ) × snd (Dt σ)) (snd (Dt τ))) :=
Dtm t with t => {
  | @id τ := (id, exr);
  | @seq τ σ ρ t1 t2 :=
    (fst (Dtm t1) ;; fst (Dtm t2),
    ((cross dupl id) ;; assoc1 ;;
      (cross id (cross (fst (Dtm t1)) id)) ;;
      (cross id (snd (Dtm t2))) ;; (snd (Dtm t1))));

  (* Monoidal *)
  | @cross τ σ ρ φ t1 t2 :=
    (cross (fst (Dtm t1)) (fst (Dtm t2)),
      (assoc1 ;; cross id (assoc2 ;; cross sym id ;; assoc1) ;;
        assoc2 ;; cross (snd (Dtm t1)) (snd (Dtm t2)) ));

  (* Terminal *)
  | @neg τ := (neg, exr ;; Ot (snd (Dt τ)));

  (* Cartesian *)
  | @exl τ σ := (exl, dupl ;; cross exr (neg ;; Ot (snd (Dt σ))));
  | @exr τ σ := (exr, dupl ;; cross (neg ;; Ot (snd (Dt τ))) exr);
  | @dupl τ := (dupl, exr ;; plust (snd (Dt τ)));

  (* Closed *)
  | @ev τ σ := (ev ;; exl,
    <|exl ;; exr, <|exr, <| exl ;; ev ;; exr, exr|> ;; ev|>|> ;; assoc2);
  | @curry τ σ ρ t' :=
    (curry (<| fst (Dtm t'), curry (snd (Dtm t') ;; exr) |>),
      assoc2 ;; snd (Dtm t') ;; exl);
    (* (curry (<| fst (Dtm t'), curry (snd (Dtm t') ;; exr) |>),
      assoc2 ;; snd (Dtm t') ;; exl); *)
  | @uncurry τ σ ρ t' := (<|exl ;; fst (Dtm t'), exr|> ;; ev ;; exl,
    <|<|exl ;; exl ;; fst (Dtm (t')), assoc1 ;; exr|>, assoc1 ;; snd (Dtm t') |> ;;
      <|exl ;; assoc2 ;; <|exl ;; ev ;; exr, exr|> ;; ev, exr|> ;; sym);

  (* Const *)
  (* | cnst t := _; *)

  (* Numeric *)
  | cplus := (t, <|exl ;; cplus, exr|>);
  | crval r := (t, neg)
}.

Reserved Notation "⟦ t ⟧ₜₘ".
Equations denote_tm {τ σ} (c : comb τ σ): ⟦τ⟧ₜ -> ⟦σ⟧ₜ :=
denote_tm c x with c := {
  | @id τ := x;
  | @seq τ σ ρ t1 t2 := ⟦t2⟧ₜₘ (⟦t1⟧ₜₘ x);

  (* Monoidal *)
  | @cross τ σ ρ φ t1 t2 := (⟦t1⟧ₜₘ (fst x), ⟦t2⟧ₜₘ (snd x));

  (* Terminal *)
  | @neg τ := tt;

  (* Cartesian *)
  | @exl τ σ := fst x;
  | @exr τ σ := snd x;
  | @dupl τ := (x, x);

  (* Closed *)
  | @ev τ σ := (fst x) (snd x);
  | @curry τ σ ρ t' := fun y => ⟦t'⟧ₜₘ  (x, y);
  | @uncurry τ σ ρ t' := ⟦t'⟧ₜₘ (fst x) (snd x);

  (* Const *)
  (* | cnst t := _; *)

  (* Numeric *)
  | cplus := Rplus (fst x) (snd x);
  | crval r := r
}
where "⟦ s ⟧ₜₘ" := (denote_tm s).
