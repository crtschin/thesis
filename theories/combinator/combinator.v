Require Import Lists.List.
Import ListNotations.
Require Import Reals.
Require Import Coq.Program.Basics.
Require Import Equations.Equations.
Require Import CoLoR.Util.Vector.VecUtil.

Require Import AD.types.
Require Import AD.target.
Local Open Scope program_scope.

(* Combinator Language definition *)
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
    comb (A × B) B
  | dupl : forall {A},
    comb A (A × A)

  (* Closed *)
  | ev : forall {A B},
    comb ((A → B) × A) B
  | curry : forall {A B C},
    comb (A × B) C -> comb A (B → C)

  (* Numeric *)
  | cplus : comb (Real × Real) Real
  | crval : forall (a : R), comb Unit Real

  | cmplus : forall {n}, comb (Reals n × Reals n) (Reals n)
  | cmrval : forall {n} (a : vector R n), comb Unit (Reals n)
.
Derive Signature for comb.

Fixpoint Dt (τ : ty) : s_ty * s_ty :=
  match τ with
  | ℝ => (sℝ, sℝ)
  | ℝ^n => (sℝ^n, sℝ^n)
  | Unit => (s_Unit, s_Unit)
  | σ × ρ =>
      ((fst (Dt σ)) s× (fst (Dt ρ)), (snd (Dt σ)) s× (snd (Dt ρ)))
  | σ → ρ =>
      (fst (Dt σ) s→ (fst (Dt ρ) s× (snd (Dt ρ) s⊸ snd (Dt σ)))
        , fst (Dt σ) s⊗ snd (Dt ρ))
  end.

(* Warning: the following takes a long time to typecheck/prove automatically
*)
Fixpoint Dcomb {τ σ} (t : comb τ σ)
  : (target (fst (Dt τ)) (fst (Dt σ)) *
      target (fst (Dt τ) s× snd (Dt σ)) (snd (Dt τ))) :=
  match t with
  (* Categorical *)
  | @id τ => (t_id, t_exr)
  | @seq τ σ ρ t1 t2 =>
      ((fst (Dcomb t1)) ;; (fst (Dcomb t2)),
      ((t_cross t_dupl t_id) ;; assoc1 ;;
        (t_cross t_id (t_cross (fst (Dcomb t1)) t_id)) ;;
        (t_cross t_id (snd (Dcomb t2))) ;; (snd (Dcomb t1))))

  (* Monoidal *)
  | @cross τ σ ρ φ t1 t2 =>
    (t_cross (fst (Dcomb t1)) (fst (Dcomb t2)),
      (assoc1 ;; t_cross t_id (assoc2 ;; t_cross sym t_id ;; assoc1) ;;
        assoc2 ;; t_cross (snd (Dcomb t1)) (snd (Dcomb t2))))

  (* Terminal *)
  | @neg τ => (t_neg, t_exr ;; t_O (snd (Dt τ)))

  (* Cartesian *)
  | @exl τ σ => (t_exl, t_dupl ;; t_cross t_exr (t_neg ;; t_O (snd (Dt σ))))
  | @exr τ σ => (t_exr, t_dupl ;; t_cross (t_neg ;; t_O (snd (Dt τ))) t_exr)
  | @dupl τ => (t_dupl, t_exr ;; t_plus (snd (Dt τ)))

  (* Closed *)
  | @ev τ σ =>
    (t_ev ;; t_exl
      , ⟨
          ⟨t_exl ;; t_exr, t_exr⟩ ;; t_msingleton ,
          t_cross (t_ev ;; t_exr ;; t_curry t_ev_l) t_id ;; t_ev
        ⟩)
  | @curry τ σ ρ t' =>
    (t_curry (⟨ fst (Dcomb t'), t_curry_l (snd (Dcomb t') ;; t_exr) ⟩)
      , t_cross t_id (⟨t_id, t_neg ;; t_curry t_exr⟩ ;; t_mfold) ;;
        assoc2 ;; snd (Dcomb t') ;; t_exl)

  (* Numeric *)
  | cplus => (t_cplus, t_exr ;; t_dupl)
  | crval r => (t_crval r, t_neg)

  | cmplus => (t_cmplus, t_exr ;; t_dupl)
  | cmrval r => (t_cmrval r, t_neg)
  end.

Notation "A ;; B" := (seq A B) (at level 40, left associativity).
Notation "⟨ A , B ⟩" := (dupl ;; cross A B) (at level 30).

(* Helpfull extras *)
Definition uncurry {A B C} : comb A (B → C) -> comb (A × B) C :=
  fun c => cross c id ;; ev.
Definition assoc1 {A B C} : comb ((A × B) × C) (A × (B × C)) :=
  ⟨exl;;exl, ⟨exl;;exr, exr⟩⟩.
Definition assoc2 {A B C} : comb (A × (B × C)) ((A × B) × C) :=
  ⟨⟨exl, exr;;exl⟩, exr;;exr⟩.
Definition sym {A B} : comb (A × B) (B × A) :=
  ⟨exr, exl⟩.