Require Import List.
Require Import Program.
Require Import Equations.Equations.

Section hlist.
  (* heterogeneous lists
      From Adam Chlipala's section on
      heterogeneous lists in CPDT *)
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Definition hhd ls (hl : hlist ls) :=
    match hl in hlist ls return match ls with
                                  | nil => unit
                                  | x :: _ => B x
                                end with
      | HNil => tt
      | HCons _ _ v _ => v
    end.


  Definition htl ls (hl : hlist ls) :=
    match hl in hlist ls return match ls with
                                  | nil => unit
                                  | _ :: ls' => hlist ls'
                                end with
      | HNil => tt
      | HCons _ _ _ hl' => hl'
    end.
End hlist.
Derive Signature for hlist.
Arguments HCons [A B x ls] _ _.

(* minimal types variables and terms,
    2 simple types and just variables as terms *)
Inductive type : Type :=
  | Bool : type
  | Nat : type.

Inductive Var : list type -> type -> Type :=
  | Top : forall Γ τ, Var (τ::Γ) τ
  | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ.

Inductive tm (Γ : list type) : type -> Type :=
  | var : forall τ, Var Γ τ -> tm Γ τ.

(* Typed substitutions *)
Definition sub Γ Γ' :=
  forall τ, Var Γ τ -> tm Γ' τ.
Definition id_sub {Γ} : sub Γ Γ := var Γ.
(* Substitution projections *)
Definition hd_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : tm Γ' τ
  := s τ (Top Γ τ).
Definition tl_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : sub Γ Γ'
  := fun σ x => s σ (Pop Γ σ τ x).

(* Denotations *)
(* types -> Type *)
Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t (τ : type) : Type :=
  match τ with
  | Bool => bool
  | Nat => nat
  end
where "⟦ τ ⟧ₜ" := (denote_t τ).

(* contexts -> heterogeneous list *)
Definition denote_ctx (Γ : list type) := hlist type denote_t Γ.

(* variables -> lookup in heterogeneous list *)
Equations denote_v {Γ τ} (v: Var Γ τ) : denote_ctx Γ -> denote_t τ :=
denote_v (Top Γ τ) (HCons h t) := h;
denote_v (Pop Γ τ σ v) (HCons h t) := denote_v v t.

(* terms -> instances of Type, correct w.r.t. denote_t *)
Fixpoint denote_tm {Γ τ} (t : tm Γ τ) : denote_ctx Γ -> denote_t τ :=
  match t with
  | var _ _ v => denote_v v
  end.

(* Given a substitution from Γ to Γ', I am able to transform
    a heterogeneous list of type Γ' to Γ.
    A substitution 'uses up' types in the context by swapping
    it out for the appropriate terms, so we add the denotations
    of those same terms to the heterogeneous list Γ' to get Γ.
*)
Equations denote_sub {Γ Γ'} :
  sub Γ Γ' -> denote_ctx Γ' -> denote_ctx Γ :=
denote_sub (Γ:=nil) s ctx := HNil type denote_t;
denote_sub (Γ:=t::Γ_) s ctx :=
  HCons (denote_tm (hd_sub s) ctx) (denote_sub (tl_sub s) ctx).

Lemma denote_ctx_eq :
  forall (Γ : list type) (τ : type) (h h' : denote_t τ)
    (t t' : hlist type denote_t Γ),
  h = h' -> t = t' -> HCons h t = HCons h' t'.
Proof. intros. rewrite H. now rewrite H0. Qed.

(* The problematic lemma *)
Lemma problematic : forall Γ (ctx : denote_ctx Γ),
  denote_sub id_sub ctx = ctx.
Proof.
  induction Γ.
  { intros. dependent destruction ctx.
    now simp denote_sub. }
  { intros ctx.
    dependent destruction ctx.
    simp denote_sub.
    apply denote_ctx_eq; eauto.
    admit. }
Admitted.
