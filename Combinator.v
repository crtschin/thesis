Require Import Lists.List.
Import ListNotations.
Require Import Reals.
Require Import Coq.Program.Basics.
Require Import Equations.Equations.
Require Import AD.DepList.

Local Open Scope program_scope.
Require Import Coquelicot.Derive.

Inductive ty : Type :=
  | Real : ty
  | Unit : ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
.
Notation "'ℝ'" := (Real).
Notation "A × B" := (Prod A B) (left associativity, at level 89).
Notation "A → B" := (Arrow A B) (right associativity, at level 90).

Definition Ctx := list ty.

Inductive Var {T : Type} : list T -> T -> Type :=
  | Top : forall Γ τ, Var (τ::Γ) τ
  | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ
.
Derive Signature for Var.
Notation "x ∈ Γ" := (Var Γ x) (at level 75).

(* STLC *)
Inductive stlc {Γ : Ctx} : ty -> Type :=
  | var : forall {τ},
    τ ∈ Γ -> stlc τ
  | app : forall {τ σ},
    stlc (σ → τ) -> stlc σ -> stlc τ
  | abs : forall {τ σ},
    @stlc (σ::Γ) τ -> stlc (σ → τ)
  | tuple : forall {A B},
    stlc A -> stlc B -> stlc (A × B)
  | first : forall {A B},
    stlc (A × B) -> stlc A
  | second : forall {A B},
    stlc (A × B) -> stlc B
  | plus :
    stlc ℝ -> stlc ℝ -> stlc ℝ
  | mul :
    stlc ℝ -> stlc ℝ -> stlc ℝ
  | rval : R -> stlc ℝ
  | it : stlc Unit
.

Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t τ : Set :=
  match τ with
  | Real => R
  | Unit => unit
  | τ1 × τ2 => ⟦τ1⟧ₜ * ⟦τ2⟧ₜ
  | τ1 → τ2 => ⟦τ1⟧ₜ -> ⟦τ2⟧ₜ
  end
where "⟦ τ ⟧ₜ" := (denote_t τ).

Definition denote_ctx (Γ : Ctx) := hlist denote_t Γ.
Notation "⟦ Γ ⟧ₜₓ" := (denote_ctx Γ).
Derive Signature for hlist.
Definition denote_ctx_hd {Γ : Ctx} (l : hlist denote_t Γ):= hhd l.
Definition denote_ctx_tl {Γ : Ctx} (l : hlist denote_t Γ):= htl l.
Definition denote_ctx_cons {Γ τ} t
  (l : hlist denote_t Γ):= @HCons ty denote_t τ Γ t l.

Equations denote_v {Γ τ} (v: τ ∈ Γ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ :=
denote_v (Top Γ τ) (HCons h t) := h;
denote_v (Pop Γ τ σ v) (HCons h t) := denote_v v t.
Notation "⟦ v ⟧ᵥ" := (denote_v v).

Reserved Notation "⟦ t ⟧ₜₘ".
Equations denote_tm {Γ τ} (t : @stlc Γ τ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ := {
(* STLC *)
denote_tm (Γ:=Γ) (τ:=τ) (var v) ctx := denote_v v ctx;
denote_tm (Γ:=Γ) (τ:=τ) (app t1 t2) ctx := (⟦t1⟧ₜₘ ctx) (⟦t2⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (abs f) ctx := fun x => ⟦ f ⟧ₜₘ (x  ::: ctx);
denote_tm (Γ:=Γ) (τ:=τ) (rval r) ctx := r;
denote_tm (Γ:=Γ) (τ:=τ) (plus t1 t2) ctx := ⟦t1⟧ₜₘ ctx + ⟦t2⟧ₜₘ ctx;
denote_tm (Γ:=Γ) (τ:=τ) (mul t1 t2) ctx := ⟦t1⟧ₜₘ ctx * ⟦t2⟧ₜₘ ctx;
denote_tm (Γ:=Γ) (τ:=τ) (tuple t1 t2) ctx := (⟦t1⟧ₜₘ ctx, ⟦t2⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (first t) ctx := fst (⟦t⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (second t) ctx := snd (⟦t⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (it) ctx := tt }
where "⟦ t ⟧ₜₘ" := (denote_tm t).

Definition shift {Γ τ σ} : @stlc Γ τ -> @stlc (σ::Γ) τ.
Admitted.

Definition id_comb {Γ A} : @stlc Γ (A → A) :=
  abs (var (Top _ _)).
Definition seq_comb {Γ A B C} :
    @stlc Γ (A → B) -> @stlc Γ (B → C) -> @stlc Γ (A → C) :=
  fun f g => abs (app (shift g) (app (shift f) (var (Top Γ A)))).
Definition cross_comb {Γ A B C D} :
    @stlc Γ (A → B) -> @stlc Γ (C → D) -> @stlc Γ ((A × C) → (B × D)) :=
  fun f g => abs (tuple
    (app (shift f) (first (var (Top _ _))))
    (app (shift g) (second (var (Top _ _))))).
Definition neg_comb {Γ A} : @stlc Γ (A → Unit) :=
  abs (it).
Definition exl_comb {Γ A B} : @stlc Γ ((A × B) → A) :=
  abs (first (var (Top _ _))).
Definition exr_comb {Γ A B} : @stlc Γ ((A × B) → B) :=
  abs (second (var (Top _ _))).
Definition dupl_comb {Γ A} : @stlc Γ (A → (A × A)) :=
  abs (tuple (var (Top _ _)) (var (Top _ _))).
Definition ev_comb {Γ A B} : @stlc Γ (((A → B) × A) → B) :=
  abs (app (first (var (Top _ _))) (second (var (Top _ _)))).
Definition curry_comb {Γ A B C} : @stlc Γ ((A × B) → C) -> @stlc Γ (A → (B → C)) :=
  fun t => abs (abs (app (shift (shift t)) (tuple (var (Pop _ _ _ (Top _ _))) (var (Top _ _))))).
Definition uncurry_comb {Γ A B C} : @stlc Γ (A → (B → C)) -> @stlc Γ ((A × B) → C) :=
  fun t => abs (app (app (shift t) (first (var (Top _ _)))) (second (var (Top _ _)))).
Definition cnst_comb {Γ A} : @stlc Γ A -> @stlc Γ (Unit → A) :=
  fun t => abs (shift t).
Definition cplus_comb {Γ} : @stlc Γ ((ℝ × ℝ) → ℝ) :=
  abs (plus (first (var (Top _ _))) (second (var (Top _ _)))).
Definition crval_comb {Γ} : R -> @stlc Γ (ℝ → ℝ) :=
  fun r => abs (rval r).

(* Language consisting of combinators *)
Inductive comb {Γ : Ctx} : forall τ, @stlc Γ τ -> Type :=
  (* Category laws *)
  | id : forall {A}, comb (A → A) id_comb
  | seq : forall {A B C f g},
    comb (A → B) f -> comb (B → C) g -> comb (A → C) (seq_comb f g)

  (* Monoidal *)
  | cross : forall {A B C D f g},
    comb (A → B) f -> comb (C → D) g -> comb ((A × C) → (B × D)) (cross_comb f g)

  (* Terminal *)
  | neg : forall {A},
    comb (A → Unit) neg_comb

  (* Cartesian *)
  | exl : forall {A B},
    comb ((A × B) → A) exl_comb
  | exr : forall {A B},
    comb ((A × B) → B) exr_comb
  | dupl : forall {A},
    comb (A → (A × A)) dupl_comb

  (* Closed *)
  | ev : forall {A B},
    comb (((A → B) × A) → B) ev_comb
  | curry : forall {A B C f},
    comb ((A × B) → C) f -> comb (A → (B → C)) (curry_comb f)
  | uncurry : forall {A B C f},
    comb (A → (B → C)) f -> comb ((A × B) → C) (uncurry_comb f)

  (* Const *)
  | cnst : forall {A f},
    comb A f -> comb (Unit → A) (cnst_comb f)

  (* Numeric *)
  | cplus :
    comb ((ℝ × ℝ) → ℝ) cplus_comb
  | crval : forall (r : R), comb (ℝ → ℝ) (crval_comb r)
.

Notation "A ;; B" := (seq_comb A B) (at level 40).
Notation "<| A , B |>" := (dupl_comb ;; cross_comb A B) (at level 40).
Notation "<>" := (it) (at level 40).

Equations Ot {Γ : Ctx} (τ: ty): @stlc Γ τ :=
  | ℝ => rval 0;
  | Unit => <>;
  | σ × ρ => tuple (Ot σ) (Ot ρ);
  | σ → ρ => abs (Ot ρ).

Equations plust {Γ : Ctx} (τ : ty): @stlc Γ (τ × τ → τ) :=
  | ℝ => cplus_comb;
  | Unit => neg_comb;
  | σ × ρ => abs (tuple
    (app (plust σ) (tuple
      (first (first (var (Top _ _))))
      (first (second (var (Top _ _))))))
    (app (plust ρ) (tuple
      (second (first (var (Top _ _))))
      (second (second (var (Top _ _)))))));
  | σ → ρ =>
    abs (abs (app (plust ρ)
      (tuple
        (app (first (var (Pop _ _ _ (Top _ _)))) (var (Top _ _)))
        (app (second (var (Pop _ _ _ (Top _ _)))) (var (Top _ _))))
    )).

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

Equations? Dtm Γ τ (t : @stlc Γ τ) (c : @comb Γ τ t)
  : @stlc (map (fst ∘ Dt) Γ) (fst (Dt τ)) :=
Dtm Γ τ t c with c => {
  | (@id Γ τ) => _;
  | (@seq τ σ ρ Γ t f1 f2) => _;

  | (@cross Γ t τ σ ρ φ μ f1 f2) => _;

  | (@neg Γ τ) => _;

  | (@exl Γ τ σ) => _;
  | (@exr Γ τ σ) => _;
  | (@dupl Γ τ) => _;

  | (@ev Γ τ σ) => _;
  | (@curry Γ t τ σ φ) => _;
  | (@uncurry Γ t τ σ φ) => _;

  | cnst t => _;

  | cplus => _;
  | crval r => _
}.
{ pose proof (abs
    (tuple (var (Top Γ τ)) (@id_comb (τ::Γ) τ))).
  admit. }
{ pose proof (abs
    (tuple (app neg (var (Top Γ τ))) (@cnst (τ::Γ) τ Unit (Ot τ)))).
  admit. }
{ pose proof (abs
    (tuple (tuple ((var (Top Γ τ))) (var (Top Γ τ)))
      (plust τ))).
  admit. }
{ pose proof (@abs Γ _ (τ×σ)
    (tuple (@fst' ((τ×σ)::Γ) τ σ (var (Top Γ (τ×σ))))
      (abs (tuple (var (Top ((τ×σ):: Γ) τ)) (Ot σ))))).
  admit. }
{ pose proof (@abs Γ _ (τ×σ)
    (tuple (@snd' ((τ×σ)::Γ) τ σ (var (Top Γ (τ×σ))))
      (abs (tuple (Ot τ) (var (Top ((τ×σ):: Γ) σ)))))).
  admit. }
{ admit. }
all: admit.
  (* pose proof (@abs Γ _ ((τ→σ)×τ)
    (tuple
      (fst' (app (fst' (var (Top _ _))) (snd' (var (Top _ _)))))
      (abs
        (tuple
          (tuple (snd' (var (Pop _ _ _ (Top _ _)))) (var (Top _ _)))
          (app
            (snd' (app (fst' (var (Top _ _))) (snd' (var (Top _ _)))))
            (var (Top _ _))))))). } *)
