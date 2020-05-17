Import EqNotations.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Derive.
Require Import Coquelicot.Hierarchy.
Require Import Equations.Equations.
Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Relations.
Require Import Strings.String.
Require Vectors.Fin.

Require Import CoLoR.Util.Vector.VecUtil.
Require Import Equations.Equations.
Require Import AD.Tactics.

Local Open Scope program_scope.

Inductive ty : Type :=
  | Real : ty
  (* | Nat : ty *)
  | Array : nat -> ty -> ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
  (* | Sum  : ty -> ty -> ty *)
.

Notation "'ℝ'" := (Real).
(* Notation "'ℕ'" := (Nat). *)
Notation "A × B" := (Prod A B) (left associativity, at level 89).
(* Notation "A <+> B" := (Sum A B) (left associativity, at level 89). *)
Notation "A → B" := (Arrow A B) (right associativity, at level 90).

(*
  STLC with well-typed well-scoped debruijn

  Adapted from:
    - From Mathematics to Abstract Machine by Swierstra, et al.
    - Strongly Typed Term Representations in Coq by Benton, et al.
    - Efficient Differentiable Programming in a
        Functional Array-Processing Language by Amir Shaikhha, et al.
 *)
Definition Ctx {x} : Type := list x.

Inductive Var {T : Type} : list T -> T -> Type :=
  | Top : forall Γ τ, Var (τ::Γ) τ
  | Pop : forall Γ τ σ, Var Γ τ -> Var (σ::Γ) τ
.
Derive Signature for Var.

Notation "x ∈ Γ" := (Var Γ x) (at level 75).

Inductive tm (Γ : Ctx) : ty -> Type :=
  (* Base STLC *)
  | var : forall τ,
    τ ∈ Γ -> tm Γ τ
  | app : forall τ σ,
    tm Γ (σ → τ) ->
    tm Γ σ ->
    tm Γ τ
  | abs : forall τ σ,
    tm (σ::Γ) τ -> tm Γ (σ → τ)

  (* Arrays *)
  | build : forall τ n,
    (Fin.t n -> tm Γ τ) -> tm Γ (Array n τ)
  | get : forall {τ n},
    Fin.t n -> tm Γ (Array n τ) -> tm Γ τ

  (* Reals *)
  | rval : forall (r : R), tm Γ ℝ
  | add : tm Γ ℝ -> tm Γ ℝ -> tm Γ ℝ

  (* Nat *)
  (* | nsucc : tm Γ ℕ -> tm Γ ℕ
  | nval : forall (n : nat), tm Γ ℕ
  | nrec : forall τ,
    tm Γ (τ → τ) -> tm Γ ℕ -> tm Γ τ -> tm Γ τ *)

  (* Products (currently using projection instead of pattern matching) *)
  | tuple : forall {τ σ},
    tm Γ τ ->
    tm Γ σ ->
    tm Γ (τ × σ)
  | first : forall {τ σ}, tm Γ (τ × σ) -> tm Γ τ
  | second : forall {τ σ}, tm Γ (τ × σ) -> tm Γ σ

  (* Sums *)
  (* | case : forall {τ σ ρ}, tm Γ (τ <+> σ) ->
    tm Γ (τ → ρ) ->
    tm Γ (σ → ρ) ->
    tm Γ ρ
  | inl : forall τ σ, tm Γ τ -> tm Γ (τ <+> σ)
  | inr : forall τ σ, tm Γ σ -> tm Γ (τ <+> σ) *)
.

Inductive Env : Ctx -> Type :=
  | env_nil : Env []
  | env_cons : forall {Γ τ}, tm Γ τ -> Env Γ -> Env (τ::Γ)
.
Derive Signature for Env.

Equations shave_env {Γ τ} (G : Env (τ::Γ)) : Env Γ :=
shave_env (env_cons t G) := G.

Lemma build_eq : forall Γ τ n (ta ta' : Fin.t n -> tm Γ τ),
  ta = ta' -> build Γ τ n ta = build Γ τ n ta'.
Proof. intros; rewrites. Qed.

(* Examples *)
Definition real_id :=
  abs [] Real Real
    (var [Real] Real (Top _ _)).

Definition ex_const :=
  abs [] (Real → Real) Real
    (abs [Real] (Real) (Real)
      (var [Real;Real] Real (Top [Real] Real))).

Definition ex_plus :=
  abs [] (Real → Real) Real
    (abs [Real] Real Real
      (add [Real;Real]
        (var [Real;Real] Real (Pop [Real] Real Real (Top [] Real)))
          (var [Real;Real] Real (Top [Real] Real)))).

Definition neuron :=
  abs [] (Real → Real → Real) Real
    (abs [Real] (Real → Real) Real
      (abs [Real;Real] Real Real
        (add [Real;Real;Real]
          (add [Real;Real;Real]
            (var [Real;Real;Real] Real
              (Pop [Real;Real] Real Real (Top [Real] Real)))
            (var [Real;Real;Real] Real (Top [Real;Real] Real)))
          (var [Real;Real;Real] Real
            (Pop [Real;Real] Real Real
              (Pop [Real] Real Real
                (Top [] Real))))))).
(* End Examples *)

(*
  Context Substitution

  Adapted from:
    Strongly Typed Term Representations in Coq by Benton, et al.
*)

(*
  Substitutes a variable typed in one context and swaps it
    with an expression with the same type typed in a different context.
    Effectively 'using up' one of the variables in the context.
*)
Definition gren (f : ty -> ty) Γ Γ'  :=
  forall τ, Var (map f Γ) (f τ) -> Var (map f Γ') (f τ).
Definition gsub (f : ty -> ty) Γ Γ' :=
  forall τ, Var (map f Γ) (f τ) -> tm (map f Γ') (f τ).

Definition ren (Γ Γ' : list ty) :=
  forall τ, Var Γ τ -> Var Γ' τ.
Definition sub (Γ Γ' : list ty) :=
  forall τ, Var Γ τ -> tm Γ' τ.

(* Helper functions for defining substitutions on the i'th variable *)
Definition id_sub {Γ} : sub Γ Γ := var Γ.
Equations cons_sub {Γ Γ' τ} (e: tm Γ' τ) (s: sub Γ Γ')
  : sub (τ::Γ) Γ' :=
cons_sub e s τ (Top Γ σ) := e;
cons_sub e s τ (Pop Γ τ σ v) := s τ v.

Notation "| a ; .. ; b |" :=
  (cons_sub a  .. ( cons_sub b id_sub) .. )
  (at level 12, no associativity).

(* For decomposing substitutions and renames *)
Definition hd_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : tm Γ' τ := s τ (Top Γ τ).
Definition tl_sub {Γ Γ' τ} (s : sub (τ::Γ) Γ') : sub Γ Γ'
  := fun σ x => s σ (Pop Γ σ τ x).

Definition id_ren {Γ} : ren Γ Γ := fun _ x => x.
Definition hd_ren {Γ Γ' τ} (r : ren (τ::Γ) Γ') : Var Γ' τ
  := (r τ (Top Γ τ)).
Definition tl_ren {Γ Γ' τ} (r : ren (τ::Γ) Γ') : ren Γ Γ'
  := fun σ x => r σ (Pop Γ σ τ x).

Equations rename_lifted {Γ Γ' τ} (r : ren Γ Γ')
  : ren (τ::Γ) (τ::Γ') :=
rename_lifted r τ (Top Γ τ) => Top Γ' τ;
rename_lifted r τ (Pop Γ τ σ v) => Pop Γ' τ σ (r τ v).

Fixpoint rename {Γ Γ' τ} (r : ren Γ Γ') (t : tm Γ τ) : (tm Γ' τ) :=
  match t with
  (* STLC *)
  | var _ v => var _ _ (r _ v)
  | app _ _ t1 t2 => app _ _ _ (rename r t1) (rename r t2)
  | abs _ _ f => abs _ _ _ (rename (rename_lifted r) f)

  (* Arrays *)
  | build _ _ ta => build _ _ _ (rename r ∘ ta)
  | get _ _ ti ta => get _ ti (rename r ta)

  (* Nat *)
  (* | nval _ n => nval _ n
  | nsucc _ t => nsucc _ (rename r t)
  | nrec _ _ f i d => nrec _ _ (rename r f) (rename r i) (rename r d) *)

  (* Reals *)
  | rval r => rval _ r
  | add t1 t2 => add _ (rename r t1) (rename r t2)

  (* Products *)
  | tuple _ _ t1 t2 => tuple _ (rename r t1) (rename r t2)
  | first _ _ p => first _ (rename r p)
  | second _ _ p => second _ (rename r p)

  (* Sums *)
  (* | case _ e c1 c2 =>
      case _ (rename r e)
        (rename r c1)
        (rename r c2)
  | inl _ _ _ e => inl _ _ _ (rename r e)
  | inr _ _ _ e => inr _ _ _ (rename r e) *)
  end.

Definition shift {Γ τ σ} : tm Γ τ -> tm (σ::Γ) τ
  := rename (fun ρ x => Pop Γ ρ σ x).

Equations substitute_lifted {Γ Γ' τ} (s : sub Γ Γ')
  : sub (τ::Γ) (τ::Γ') :=
substitute_lifted s τ (Top Γ σ) := var (σ::Γ') σ (Top Γ' σ);
substitute_lifted s τ (Pop Γ τ σ v) := shift (s τ v).

Fixpoint substitute {Γ Γ' τ} (s : sub Γ Γ') (t : tm Γ τ) : tm Γ' τ :=
  match t with
  (* STLC *)
  | var _ v => s _ v
  | app _ _ t1 t2 => app _ _ _ (substitute s t1) (substitute s t2)
  | abs _ _ f => abs _ _ _ (substitute (substitute_lifted s) f)

  (* Arrays *)
  | build _ _ ta => build _ _ _ (substitute s ∘ ta)
  | get _ _ ti ta => get _ ti (substitute s ta)

  (* Nat *)
  (* | nval _ n => nval _ n
  | nsucc _ t => nsucc _ (substitute s t)
  | nrec _ _ f i d => nrec _ _ (substitute s f) (substitute s i) (substitute s d) *)


  (* Reals *)
  | rval r => rval _ r
  | add t1 t2 => add _ (substitute s t1) (substitute s t2)

  (* Products *)
  | tuple _ _ t1 t2 => tuple  _ (substitute s t1) (substitute s t2)
  | first _ _ p => first _ (substitute s p)
  | second _ _ p => second _ (substitute s p)

  (* Sums *)
  (* | case _ e c1 c2 =>
      case _ (substitute s e)
        (substitute s c1)
        (substitute s c2)
  | inl _ _ _ e => inl _ _ _ (substitute s e)
  | inr _ _ _ e => inr _ _ _ (substitute s e) *)
  end.

(*
  Tactics from:
    Strongly Typed Term Representations in Coq by Benton, et al.
*)
Ltac Rewrites E :=
  (intros; simpl; try rewrite E;
    repeat
      (match goal with | [H:context[_=_] |- _] => rewrite H end);
    auto).

Ltac ExtVar :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (@functional_extensionality_dep _ _ X Y) ;
      let t := fresh "t" in intro t;
      apply functional_extensionality;
      let v := fresh "v" in intro v;
      dependent destruction v; auto)
end.

Lemma lift_sub_id : forall Γ τ,
  substitute_lifted (@id_sub Γ) = @id_sub (τ::Γ).
Proof. intros. ExtVar. Qed.

Lemma app_sub_id : forall Γ τ (t : tm Γ τ),
  substitute id_sub t = t.
Proof with quick.
  induction t; rewrites;
  try (rewrite lift_sub_id; rewrites).
  { erewrite build_eq...
    extensionality x... }
Qed.

Lemma lift_ren_id : forall Γ τ,
  rename_lifted (@id_ren Γ) = @id_ren (τ::Γ).
Proof. intros. ExtVar. Qed.

Lemma app_ren_id : forall Γ τ (t : tm Γ τ),
  rename id_ren t = t.
Proof with quick.
  induction t; Rewrites lift_ren_id.
  { erewrite build_eq...
    extensionality x... }
Qed.

(* Composing substitutions and renames *)
Definition compose_ren_ren {Γ Γ' Γ''} (r : ren Γ' Γ'') (r' : ren Γ Γ')
  : ren Γ Γ'' := (fun t v => r t (r' t v)).
Definition compose_sub_ren {Γ Γ' Γ''} (s : sub Γ' Γ'') (r : ren Γ Γ')
  : sub Γ Γ'' := (fun t v => s t (r t v)).
Definition compose_ren_sub {Γ Γ' Γ''} (r : ren Γ' Γ'') (s : sub Γ Γ')
  : sub Γ Γ'' := (fun t v => rename r (s t v)).
Definition compose_sub_sub {Γ Γ' Γ''} (s : sub Γ' Γ'') (s' : sub Γ Γ')
  : sub Γ Γ'' := (fun t v => substitute s (s' t v)).

Lemma lift_ren_ren : forall Γ Γ' Γ'' τ (r : ren Γ' Γ'') (r' : ren Γ Γ'),
  rename_lifted (τ:=τ) (compose_ren_ren r r') =
    compose_ren_ren (rename_lifted r) (rename_lifted r').
Proof. intros. ExtVar. Qed.

Lemma app_ren_ren : forall Γ Γ' Γ'' τ
    (t : tm Γ τ) (r : ren Γ' Γ'') (r' : ren Γ Γ'),
  rename (compose_ren_ren r r') t = rename r (rename r' t).
Proof with quick.
  intros. generalize dependent Γ'. generalize dependent Γ''.
  induction t; Rewrites lift_ren_ren.
  { erewrite build_eq...
    extensionality x... }
Qed.

Lemma lift_sub_ren : forall Γ Γ' Γ'' τ (s : sub Γ' Γ'') (r : ren Γ Γ'),
  substitute_lifted (τ:=τ) (compose_sub_ren s r) =
    compose_sub_ren (substitute_lifted s) (rename_lifted r).
Proof. intros. ExtVar. Qed.

Lemma app_sub_ren : forall Γ Γ' Γ'' τ
    (t : tm Γ τ) (s : sub Γ' Γ'') (r : ren Γ Γ'),
  substitute (compose_sub_ren s r) t =
    substitute s (rename r t).
Proof with quick.
  intros. generalize dependent Γ'. generalize dependent Γ''.
  induction t; Rewrites lift_sub_ren.
  { erewrite build_eq...
    extensionality x... }
Qed.

Lemma lift_ren_sub : forall Γ Γ' Γ'' τ (r : ren Γ' Γ'') (s : sub Γ Γ'),
  substitute_lifted (τ:=τ) (compose_ren_sub r s) =
    compose_ren_sub (rename_lifted r) (substitute_lifted s).
Proof with eauto.
  intros. ExtVar. unfold compose_ren_sub.
  simp substitute_lifted. unfold shift.
  rewrite <- 2 app_ren_ren...
Qed.

Lemma app_ren_sub : forall Γ Γ' Γ'' τ
    (t : tm Γ τ) (r : ren Γ' Γ'') (s : sub Γ Γ'),
  substitute (compose_ren_sub r s) t =
    rename r (substitute s t).
Proof with eauto.
  intros. generalize dependent Γ'. generalize dependent Γ''.
  induction t; Rewrites lift_ren_sub.
  { erewrite build_eq...
    extensionality x... }
  (* { erewrite ifold_congr...
    extensionality x... } *)
Qed.

Lemma lift_sub_sub : forall Γ Γ' Γ'' τ (s : sub Γ' Γ'') (s' : sub Γ Γ'),
  substitute_lifted (τ:=τ) (compose_sub_sub s s') =
    compose_sub_sub (substitute_lifted s) (substitute_lifted s').
Proof with eauto.
  intros. ExtVar. unfold compose_sub_sub.
  simp substitute_lifted. unfold shift.
  rewrite <- app_ren_sub. rewrite <- app_sub_ren...
Qed.

Lemma app_sub_sub : forall Γ Γ' Γ'' τ
    (t : tm Γ τ) (s : sub Γ' Γ'') (s' : sub Γ Γ'),
  substitute (compose_sub_sub s s') t =
    substitute s (substitute s' t).
Proof with eauto.
  intros. generalize dependent Γ'. generalize dependent Γ''.
  induction t; Rewrites lift_sub_sub.
  { erewrite build_eq...
    extensionality x... }
  (* { erewrite ifold_congr...
    extensionality x... } *)
Qed.

Lemma rename_abs : forall Γ Γ' τ σ (t : tm (σ::Γ) τ) (r : ren Γ Γ'),
  rename r (abs Γ τ σ t) = abs Γ' τ σ (rename (rename_lifted r) t).
Proof. reflexivity. Qed.
Lemma substitute_abs : forall Γ Γ' τ σ (t : tm (σ::Γ) τ) (s : sub Γ Γ'),
  substitute s (abs Γ τ σ t) = abs Γ' τ σ (substitute (substitute_lifted s) t).
Proof. reflexivity. Qed.

Lemma tl_cons_sub : forall Γ Γ' τ (t : tm Γ' τ) (sb : sub Γ Γ'),
  tl_sub (cons_sub t sb) = sb.
Proof with quick.
  intros.
  extensionality σ; extensionality s.
  induction s; unfold tl_sub; simp cons_sub...
Qed.

Lemma subst_shift_refl :
  forall Γ τ σ (t : tm Γ τ) (s : tm Γ σ),
    substitute (| s |) (shift t) = t.
Proof with eauto.
  intros.
  unfold shift.
  rewrite <- app_sub_ren...
  generalize dependent σ.
  induction t; rewrites;
  try (unfold compose_sub_ren in *; quick;
    rewrite lift_sub_id;
    rewrite app_sub_id)...
  { erewrite build_eq...
    extensionality x... }
Qed.

(* Notations:
  ⟦ τ ⟧ₜ := denote_t τ, Currently piggybacks off of Coq's types.
  ⟦ Γ ⟧ₜₓ := denote_ctx Γ, A product list of types ensured to exist
                          in the context Γ.
  ⟦ v ⟧ₜₓ := denote_v v, A projection of the product list denoted by the typing
                          context relevant to the variable referenced by v
  ⟦ t ⟧ₜₘ := denote_tm t, Gives a function f of t such that it has the correct
                          denoted type of τ given the denoted context of Γ.
*)

Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t τ : Set :=
  match τ with
  | Real => R
  (* | Nat => nat *)
  | Array n τ => vector ⟦ τ ⟧ₜ n
  | τ1 × τ2 => ⟦τ1⟧ₜ * ⟦τ2⟧ₜ
  | τ1 → τ2 => ⟦τ1⟧ₜ -> ⟦τ2⟧ₜ
  (* | τ1 <+> τ2 => ⟦τ1⟧ₜ + ⟦τ2⟧ₜ *)
  end
where "⟦ τ ⟧ₜ" := (denote_t τ).

Reserved Notation "⟦ Γ ⟧ₜₓ".
Fixpoint denote_ctx (Γ : Ctx) : Type :=
  match Γ with
  | [] => unit
  | h :: t => ⟦h⟧ₜ * ⟦t⟧ₜₓ
  end
where "⟦ Γ ⟧ₜₓ" := (denote_ctx Γ).

Fixpoint denote_v {Γ τ} (v: τ ∈ Γ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ  :=
  match v with
  | Top Γ' τ' => fun gamma => fst gamma
  | Pop Γ' τ' σ x => fun gamma => denote_v x (snd gamma)
  end.
Notation "⟦ v ⟧ᵥ" := (denote_v v).

Require Import Vectors.Fin.

Fixpoint vector_nth {s : Set} {n}
  (i : Fin.t n) : vector s n -> s :=
  match i with
  | @F1 _    => fun ar => Vhead ar
  | @FS _ i' => fun ar => vector_nth i' (Vtail ar)
  end.

Fixpoint nat_to_fin n : Fin.t (S n) :=
  match n with
  | 0 => F1
  | S n' => F1
  end.

Definition shave_fin {A n} (f : Fin.t (S n) -> A) : Fin.t n -> A :=
  fun i => f (FS i).

Fixpoint iterate {A} (n : nat) (f : A -> A) (a : A) :=
  match n with
  | 0 => a
  | S n => f (iterate n f a)
  end.

Reserved Notation "⟦ t ⟧ₜₘ".
Equations denote_tm {Γ τ} (t : tm Γ τ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ := {
(* STLC *)
denote_tm (Γ:=Γ) (τ:=τ) (var Γ τ v) ctx := denote_v v ctx;
denote_tm (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) ctx := (⟦t1⟧ₜₘ ctx) (⟦t2⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) ctx := fun x => ⟦ f ⟧ₜₘ (x, ctx);
(* Arrays *)
denote_tm (Γ:=Γ) (τ:=τ) (build Γ τ n f) ctx :=
  denote_array n (denote_tm ∘ f) ctx;
denote_tm (Γ:=Γ) (τ:=τ) (get Γ i ta) ctx := vector_nth i (⟦ ta ⟧ₜₘ ctx);
(* Nat *)
(* denote_tm (Γ:=Γ) (τ:=τ) (nval Γ n) ctx := n;
denote_tm (Γ:=Γ) (τ:=τ) (nsucc Γ t) ctx := Datatypes.S (⟦t⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (nrec Γ τ tf ti ta) ctx :=
  iterate (⟦ ti ⟧ₜₘ ctx) (⟦ tf ⟧ₜₘ ctx) (⟦ ta ⟧ₜₘ ctx); *)
(* Reals *)
denote_tm (Γ:=Γ) (τ:=τ) (rval Γ r) ctx := r;
denote_tm (Γ:=Γ) (τ:=τ) (add Γ t1 t2) ctx := ⟦t1⟧ₜₘ ctx + ⟦t2⟧ₜₘ ctx;
(* Products *)
denote_tm (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) ctx := (⟦t1⟧ₜₘ ctx, ⟦t2⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (first Γ t) ctx := fst (⟦t⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (second Γ t) ctx := snd (⟦t⟧ₜₘ ctx)
(* Sums *)
(* denote_tm (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) ctx with ⟦e⟧ₜₘ ctx := {
  denote_tm (case Γ e c1 c2) ctx (Datatypes.inl x) := (⟦c1⟧ₜₘ ctx) x;
  denote_tm (case Γ e c1 c2) ctx (Datatypes.inr x) := (⟦c2⟧ₜₘ ctx) x
};
denote_tm (Γ:=Γ) (τ:=τ) (inl Γ τ σ e) ctx := Datatypes.inl (⟦e⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (inr Γ σ τ e) ctx := Datatypes.inr (⟦e⟧ₜₘ ctx)  *)
}
where "⟦ t ⟧ₜₘ" := (denote_tm t)
(* Helper for arrays *)
where denote_array {Γ τ} n (f : Fin.t n -> ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ)
  : ⟦Γ⟧ₜₓ -> ⟦Array n τ⟧ₜ by struct n :=
denote_array 0 f ctx := Vnil;
denote_array (S n) f ctx := Vcons (f (nat_to_fin n) ctx)
  ((denote_array n (shave_fin f)) ctx).

Equations denote_env {Γ} (G : Env Γ): ⟦ Γ ⟧ₜₓ :=
denote_env env_nil => tt;
denote_env (env_cons t G') with denote_env G' => {
  denote_env (env_cons t G') X => (⟦ t ⟧ₜₘ X, X)
}.
Notation "⟦ s ⟧ₑ" := (denote_env s).

Fixpoint denote_sub {Γ Γ'}: sub Γ Γ' -> denote_ctx Γ' -> denote_ctx Γ :=
  match Γ with
  | [] => fun s ctx => tt
  | h :: t => fun s ctx =>
      (denote_tm (hd_sub s) ctx, denote_sub (tl_sub s) ctx)
  end.
Notation "⟦ s ⟧ₛ" := (denote_sub s).

Fixpoint denote_ren {Γ Γ'}: ren Γ Γ' -> denote_ctx Γ' -> denote_ctx Γ :=
  match Γ with
  | [] => fun r ctx => tt
  | τ :: t => fun r ctx =>
      (denote_tm (var Γ' τ (hd_ren r)) ctx, denote_ren (tl_ren r) ctx)
  end.
Notation "⟦ r ⟧ᵣ" := (denote_ren r).

(* Lemmas for renaming and substitution in the denotated context.
  Many from Strongly Typed Terms in Coq by Nick Becton, et al.
*)

Lemma denote_ren_elim : forall Γ Γ' τ
  (r : ren Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  denote_ren r ctx = denote_ren (tl_ren (rename_lifted r)) (x, ctx).
Proof with eauto.
  induction Γ...
  intros. specialize IHΓ with (r:=tl_ren r).
  simpl. rewrite IHΓ with (x:=x)...
Qed.

Lemma denote_ren_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (r : ren Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (denote_ren r ctx) = ⟦ rename r t ⟧ₜₘ ctx.
Proof with quick.
  intros. generalize dependent Γ'.
  induction t; quick; try solve [simp denote_tm in *; rewrites]...
  { simp denote_tm in *; induction v; rewrites. }
  { simp denote_tm in *. specialize IHt with (r:=rename_lifted r).
    simpl in IHt. simp rename_lifted in IHt.
    apply functional_extensionality...
    rewrite <- IHt...
    rewrite <- denote_ren_elim... }
  { simp denote_tm in *. rewrites.
    unfold compose.
    induction n... rewrites.
    apply Vcons_eq.
    splits... }
  (* { simp denote_tm. rewrite IHt1.
    destruct (⟦ rename r t1 ⟧ₜₘ ctx);
      quick; rewrites. } *)
Qed.

Lemma denote_ren_shift : forall Γ Γ' τ (r:ren Γ Γ'),
  denote_ren (fun _ v => Pop _ _ τ (r _ v)) =
    fun se => denote_ren r (snd se).
Proof with quick.
  induction Γ... extensionality ctx.
  apply injective_projections...
  unfold tl_ren. rewrite IHΓ...
Qed.

Lemma denote_ren_id : forall Γ,
  denote_ren (@id_ren Γ) = Datatypes.id.
Proof with quick.
  intros. extensionality x.
  dependent induction Γ... destruct x...
  destruct x...
  apply injective_projections...
  unfold tl_ren, id_ren in *...
  rewrite denote_ren_shift...
Qed.

Lemma denote_shift : forall Γ τ σ (t : tm Γ τ) ctx,
    ⟦ shift (σ:=σ) t ⟧ₜₘ ctx = ⟦ t ⟧ₜₘ (snd ctx).
Proof with eauto.
  unfold shift. intros.
  rewrite <- denote_ren_commutes...
  pose proof denote_ren_elim as H.
  destruct ctx as [x ctx].
  specialize H with Γ Γ σ (fun t x => x) x ctx.
  unfold tl_ren in H.
  assert (H':
    (fun (σ0 : ty) (x : σ0 ∈ Γ) =>
       rename_lifted (fun (t : ty) (x0 : t ∈ Γ) => x0) σ0 (Pop Γ σ0 σ x)) =
    (fun (ρ : ty) (x0 : ρ ∈ Γ) => Pop Γ ρ σ x0)).
  { apply functional_extensionality_dep... }
  rewrite <- H'. rewrite <- H.
  fold (@id_ren Γ). rewrite denote_ren_commutes.
  rewrite app_ren_id...
Qed.

Lemma denote_sub_elim : forall Γ Γ' τ
  (s : sub Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  ⟦ s ⟧ₛ  ctx = ⟦ (tl_sub (substitute_lifted s)) ⟧ₛ (x, ctx).
Proof with eauto.
  induction Γ; intros...
  intros. specialize IHΓ with (s := (tl_sub s)).
  simpl. rewrite IHΓ with (x := x).
  unfold hd_sub. unfold tl_sub. simp substitute_lifted.
  erewrite denote_shift...
Qed.

Lemma denote_sub_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (s : sub Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (⟦ s ⟧ₛ  ctx) = ⟦ substitute s t ⟧ₜₘ ctx.
Proof with quick.
  intros. generalize dependent Γ'.
  induction t; intros; simp denote_tm; rewrites...
  { simpl. induction v...
    intros. simpl. rewrite IHv... }
  { specialize IHt with (s:=substitute_lifted s)...
    apply functional_extensionality...
    simp denote_tm.
    rewrite <- IHt...
    erewrite denote_sub_elim... }
  { simp denote_tm.
    unfold compose.
    induction n... rewrites.
    apply Vcons_eq... }
  (* { simp denote_tm.
    destruct (⟦ substitute s t1 ⟧ₜₘ ctx);
      quick; rewrites. } *)
Qed.

Lemma denote_sub_id : forall Γ τ (t : tm Γ τ) (ctx : ⟦ Γ ⟧ₜₓ),
  ⟦ t ⟧ₜₘ (⟦ id_sub ⟧ₛ ctx) = ⟦ t ⟧ₜₘ ctx.
Proof with quick.
  intros.
  rewrite denote_sub_commutes...
  rewrite app_sub_id...
Qed.

Lemma denote_sub_shift : forall Γ Γ' σ (s:sub Γ Γ'),
  denote_sub (fun _ v => shift (σ:=σ) (s _ v)) =
    fun ctx => denote_sub s (snd ctx).
Proof with quick.
  induction Γ... extensionality ctx.
  apply injective_projections...
  { unfold hd_sub. rewrite denote_shift... }
  { unfold tl_sub. rewrite IHΓ... }
Qed.

Lemma denote_sub_tl_simpl : forall Γ Γ' τ (ctx : ⟦ Γ' ⟧ₜₓ) (s : sub (τ::Γ) Γ'),
  ⟦ tl_sub s ⟧ₛ ctx = snd (⟦ s ⟧ₛ ctx).
Proof with quick.
  intros...
Qed.

Lemma denote_sub_id_ctx : forall Γ (ctx : ⟦ Γ ⟧ₜₓ),
  ⟦ id_sub ⟧ₛ ctx = ctx.
Proof with quick.
  intros Γ...
  unfold id_sub.
  induction Γ...
  { destruct ctx... }
  { (* TODO: Issue doing induction on elements in product list *)
    dependent destruction ctx...
    eapply injective_projections...
    rewrite denote_sub_tl_simpl.
    unfold denote_sub.
    admit. }
Admitted.

Lemma denote_sub_tl_cons :
  forall Γ Γ' τ (t : tm Γ' τ) ctx (sb : sub Γ Γ'),
    ⟦ (tl_sub (cons_sub t sb)) ⟧ₛ ctx = ⟦ sb ⟧ₛ ctx.
Proof with quick.
  intros.
  unfold id_sub.
  now rewrite tl_cons_sub.
Qed.

Definition letin {Γ τ σ} (e : tm Γ σ) (x : tm (σ::Γ) τ) : tm Γ τ :=
  app Γ τ σ (abs Γ τ σ x) e.
Definition vector_hot ( Γ : list ty ) ( n : nat ) ( i : Fin.t n ) :=
  build Γ ℝ n (fun j => if Fin.eqb i j then rval Γ 1 else rval Γ 0).
Definition vector_map { Γ τ σ n } ( a : tm Γ (Array n τ) )
  ( f : tm Γ τ -> tm Γ σ ) : tm Γ (Array n σ) :=
  build Γ σ n (fun i => f (get Γ i a)).
Definition vector_map2 { Γ τ σ ρ n }
  ( a1 : tm Γ (Array n τ) ) ( a2 : tm Γ (Array n σ) )
  ( f : tm Γ τ -> tm Γ σ -> tm Γ ρ ) : tm Γ (Array n ρ) :=
  build Γ ρ n (fun i => f (get Γ i a1) (get Γ i a2)).
Definition vector_zip { Γ τ σ n }
  ( a1 : tm Γ (Array n τ) ) ( a2 : tm Γ (Array n σ) )
  : tm Γ (Array n ( τ × σ )) :=
  vector_map2 a1 a2 (tuple Γ).
Definition vector_fill { Γ τ } ( n : nat ) ( e : tm Γ τ )
  : tm Γ (Array n τ) :=
  build Γ τ n (fun _ => e).
Definition vector_add {Γ n}
  ( a1 a2 : tm Γ (Array n Real) ) : tm Γ (Array n Real) :=
  vector_map2 a1 a2 (add Γ).
