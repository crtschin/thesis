Require Import Lists.List.
Import ListNotations.
Require Import Reals.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Equations.Equations.
Require Import CoLoR.Util.Vector.VecUtil.

Require Import AD.types.
Require Import AD.stlc.
Require Import AD.combinator.
Require Import AD.denotation.

Local Open Scope program_scope.

Inductive ccl {Γ : Ctx} : ty -> Type :=
  (* Base *)
  | ccl_var : forall {τ},
    τ ∈ Γ -> ccl τ

  (* Reals *)
  | ccl_plus : ccl (Real × Real → Real)
  | ccl_rval : R -> ccl Real
  | ccl_mplus : forall {n},
    ccl (Reals n × Reals n → Reals n)
  | ccl_mrval : forall {n}, vector R n -> ccl (Reals n)

  (* Category laws *)
  | ccl_id : forall {A}, ccl (A → A)
  | ccl_seq : forall {A B C},
    ccl (A → B) -> ccl (B → C) -> ccl (A → C)

  (* Cartesian *)
  | ccl_exl : forall {A B},
    ccl (A × B → A)
  | ccl_exr : forall {A B},
    ccl ((A × B) → B)

  (* Monoidal *)
  | ccl_cross : forall {A B C},
    ccl (A → B) -> ccl (A → C) -> ccl (A → B × C)

  (* Closed *)
  | ccl_ev : forall {A B},
    ccl ((A → B) × A → B)
  | ccl_env : forall {A B C},
    @ccl (A::Γ) (B → C) -> @ccl Γ ((B → A → C))

  (* Const *)
  | ccl_const : forall {A B},
    ccl A -> ccl (B → A)
.

Local Notation "A ;;; B" := (ccl_seq A B) (at level 40, left associativity).
Local Notation "⟨ A ,, B ⟩" := (ccl_cross A B) (at level 30).

Fixpoint translate_context (Γ : Ctx) : ty :=
  match Γ with
  | nil => Unit
  | τ :: Γ' => τ × translate_context Γ'
  end.
Fixpoint untranslate_context (τ : ty) : Ctx :=
  match τ with
  | ℝ => ℝ :: []
  | ℝ^n => ℝ^n :: []
  | Unit => Unit :: []
  | σ × ρ => σ :: untranslate_context ρ
  | σ → ρ => (σ → ρ) :: []
  end.
Definition weaken {τ ρ} σ (c : comb τ ρ): comb (σ × τ) ρ := exr ;; c.
Fixpoint weaken_ctx Γ {τ} (c : comb Unit τ): comb (translate_context Γ) τ :=
  match Γ with
  | nil => c
  | τ' :: Γ' => weaken τ' (weaken_ctx Γ' c)
  end.

Fixpoint fetch {Γ τ} (v : τ ∈ Γ) : comb (translate_context Γ) τ :=
  match v with
  | @Top Γ τ => exl
  | @Pop Γ τ σ v' => exr ;; fetch v'
  end.

Fixpoint stlc_ccl {Γ τ} (t : tm Γ τ) : @ccl Γ (Unit → τ) :=
  match t with
  (* Base *)
  | @var _ τ v => ccl_const (ccl_var v)
  | @app _ τ σ t1 t2 => ⟨ stlc_ccl t1 ,, stlc_ccl t2 ⟩ ;;; ccl_ev
  | @abs _ τ σ t' => ccl_env (stlc_ccl t')

  (* Products *)
  | tuple _ t1 t2 => ⟨ stlc_ccl t1,, stlc_ccl t2 ⟩
  | @first _ τ σ t' => stlc_ccl t' ;;; ccl_exl
  | second _ t => stlc_ccl t ;;; ccl_exr

  (* Reals *)
  | plus _ t1 t2 => ⟨ stlc_ccl t1,, stlc_ccl t2 ⟩ ;;; ccl_plus
  | rval _ r => ccl_const (ccl_rval r)
  | mplus _ t1 t2 => ⟨ stlc_ccl t1,, stlc_ccl t2 ⟩ ;;; ccl_mplus
  | mrval _ r => ccl_const (ccl_mrval r)

  (* Unit *)
  | it _ => ccl_id
  end.

(* Fixpoint ccl_stlc {Γ τ} (c : @ccl Γ τ) : tm Γ τ :=
  match c with
  (* Base *)
  | @ccl_var _ τ v => var Γ v
  | @ccl_app _ τ σ t1 t2 =>
    app Γ (ccl_stlc t1) (ccl_stlc t2)

  (* Products *)
  | @ccl_tuple _ τ σ t1 t2 =>
    tuple Γ (ccl_stlc t1) (ccl_stlc t2)

  (* Reals *)
  | ccl_plus =>
    abs _ (plus _ (first _ (var _ Top)) (second _ (var _ Top)))
  | ccl_rval r => rval Γ r

  | ccl_mplus =>
    abs _ (mplus _ (first _ (var _ Top)) (second _ (var _ Top)))
  | ccl_mrval r => mrval Γ r

  (* Category laws *)
  | @ccl_id _ => abs _ (var _ Top)
  | @ccl_seq _ τ σ ρ t1 t2 =>
    abs Γ (app (τ::Γ) (shift (ccl_stlc t2))
      (app (τ::Γ) (shift (ccl_stlc t1)) (var (τ::Γ) Top)))

  (* Cartesian *)
  | @ccl_exl _ σ => abs _ (first _ (var _ Top))
  | @ccl_exr _ σ => abs _ (second _ (var _ Top))

  (* Monoidal *)
  | @ccl_cross _ _ σ ρ t1 t2 =>
    abs _ (tuple _
      (app _ (shift (ccl_stlc t1)) (var _ Top))
      (app _ (shift (ccl_stlc t2)) (var _ Top)))

  (* Closed *)
  | @ccl_ev _ σ => abs _ (app _ (first _ (var _ Top)) (second _ (var _ Top)))
  | @ccl_curry _ _ σ ρ t' =>
    abs _ (abs _ (app _ (shift (shift (ccl_stlc t'))) (tuple _ (var _ (Pop Top)) (var _ Top))))
  | @ccl_env _ _ σ ρ t' =>
    abs _ (abs _ (app _ (swap (shift (ccl_stlc t'))) (var _ (Pop Top))))

  (* Const *)
  | @ccl_const _ _ σ t' => abs _ (shift (ccl_stlc t'))

  (* Unit *)
  | ccl_it => it _
  end.

Fixpoint ccc_ccl {Γ τ σ} (c : comb σ τ) : @ccl Γ (σ → τ) :=
  match c with
  (* Categorical *)
  | @id τ => ccl_id
  | @seq τ σ ρ t1 t2 =>
    ccc_ccl t1 ;;; ccc_ccl t2

  (* Monoidal *)
  | @cross τ σ ρ φ t1 t2 =>
    ⟨ ccl_exl ;;; ccc_ccl t1 ,, ccl_exr ;;; ccc_ccl t2 ⟩

  (* Terminal *)
  | @neg τ => ccl_const (ccl_it)

  (* Cartesian *)
  | @exl τ σ => ccl_exl
  | @exr τ σ => ccl_exr
  | @dupl τ => ⟨ccl_id,, ccl_id⟩

  (* Closed *)
  | @ev τ σ => ccl_ev
  | @curry τ σ ρ t' =>
    ccl_curry (ccc_ccl t')

  (* Numeric *)
  | cplus => ccl_plus
  | crval r => ccl_const (ccl_rval r)

  | cmplus => ccl_mplus
  | cmrval r => ccl_const (ccl_mrval r)
  end. *)

Fixpoint ccl_ccc {Γ τ} (c : @ccl Γ τ) : comb (translate_context Γ) τ :=
  match c with
  (* Base *)
  | @ccl_var _ τ v => fetch v

  (* Reals *)
  | ccl_plus => curry (exr ;; cplus)
  | ccl_rval r => weaken_ctx Γ (crval r)
  | ccl_mplus => curry (exr ;; cmplus)
  | ccl_mrval r => weaken_ctx Γ (cmrval r)

  (* Category laws *)
  | @ccl_id _ τ => curry exr
  | @ccl_seq _ τ σ ρ t1 t2 =>
    ⟨ccl_ccc t2, ccl_ccc t1⟩ ;; curry (assoc1 ;; cross id ev ;; ev)

  (* Cartesian *)
  | @ccl_exl _ τ σ => curry (exr ;; exl)
  | @ccl_exr _ τ σ => curry (exr ;; exr)

  (* Monoidal *)
  | @ccl_cross _ τ σ ρ t1 t2 =>
    ⟨ ccl_ccc t1, ccl_ccc t2 ⟩ ;;
      curry (⟨⟨exl;;exl, exr⟩, ⟨exl;;exr, exr⟩⟩;; cross ev ev)

  (* Closed *)
  | @ccl_ev _ σ => curry (exr ;; ev)
  | @ccl_env _ τ σ ρ t' =>
    curry (curry (sym ;; assoc2 ;; cross (ccl_ccc t') id ;; ev))

  (* Const *)
  | @ccl_const _ τ σ t' => ccl_ccc t';; curry exl
  end.

(* Definition ccc_stlc {Γ τ σ} : comb σ τ -> tm Γ (σ → τ)
  := ccl_stlc ∘ ccc_ccl. *)

Definition stlc_ccc {Γ τ}
  : tm Γ τ -> comb (translate_context Γ) τ :=
  fun t => ⟨ ccl_ccc (stlc_ccl t), neg ⟩ ;; ev.
