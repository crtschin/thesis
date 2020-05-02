Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Vectors.Fin.
Require Import Arith.PeanoNat.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.

Require Import CoLoR.Util.Vector.VecUtil.
Require Import Equations.Equations.
Require Import AD.Tactics.

Local Open Scope program_scope.

Inductive ty : Type :=
  | Real : ty
  | Nat : ty
  | Array : nat -> ty -> ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
  | Sum  : ty -> ty -> ty
.

Notation "'ℝ'" := (Real).
Notation "'ℕ'" := (Nat).
Notation "A × B" := (Prod A B) (left associativity, at level 89).
Notation "A <+> B" := (Sum A B) (left associativity, at level 89).
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
  | ifold : forall τ,
    (tm Γ (ℕ → τ → τ)) -> tm Γ ℕ -> tm Γ τ -> tm Γ τ

  (* Reals *)
  | rval : forall (r : R), tm Γ Real
  | add : tm Γ Real -> tm Γ Real -> tm Γ Real

  (* Nat *)
  | nval : forall (n : nat), tm Γ Nat

  (* Products (currently using projection instead of pattern matching) *)
  | tuple : forall {τ σ},
    tm Γ τ ->
    tm Γ σ ->
    tm Γ (τ × σ)
  | first : forall {τ σ}, tm Γ (τ × σ) -> tm Γ τ
  | second : forall {τ σ}, tm Γ (τ × σ) -> tm Γ σ

  (* Sums *)
  | case : forall {τ σ ρ}, tm Γ (τ <+> σ) ->
    tm Γ (τ → ρ) ->
    tm Γ (σ → ρ) ->
    tm Γ ρ
  | inl : forall τ σ, tm Γ τ -> tm Γ (τ <+> σ)
  | inr : forall τ σ, tm Γ σ -> tm Γ (τ <+> σ)
.

Inductive Env : Ctx -> Type :=
  | env_nil : Env []
  | env_cons : forall {Γ τ}, tm Γ τ -> Env Γ -> Env (τ::Γ)
.
Derive Signature for Env.

Equations shave_env {Γ τ} (G : Env (τ::Γ)) : Env Γ :=
shave_env (env_cons t G) := G.

Lemma build_congr : forall Γ τ n (ta ta' : Fin.t n -> tm Γ τ),
  ta = ta' -> build Γ τ n ta = build Γ τ n ta'.
Proof with quick. intros. rewrites. Qed.

Lemma ifold_congr : forall Γ τ tf tf' i (ta : tm Γ τ),
  tf = tf' -> ifold Γ τ tf i ta = ifold Γ τ tf' i ta.
Proof with quick. intros. rewrites. Qed.

(* Examples *)
Definition ex_id :=
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
Definition hd_ren {Γ Γ' τ} (r : ren (τ::Γ) Γ') : tm Γ' τ := var Γ' τ (r τ (Top Γ τ)).
Definition tl_ren {Γ Γ' τ} (r : ren (τ::Γ) Γ') : ren Γ Γ'
  := fun σ x => r σ (Pop Γ σ τ x).

Equations rename_lifted {Γ Γ' τ} (r : ren Γ Γ')
  : ren (τ::Γ) (τ::Γ') :=
rename_lifted r τ (Top Γ τ) => Top Γ' τ;
rename_lifted r τ (Pop Γ τ σ v) => Pop Γ' τ σ (r τ v).

Fixpoint rename {Γ Γ' τ} (r : ren Γ Γ') (t : tm Γ τ) : (tm Γ' τ) :=
  match t with
  (* STLC *)
  | var _ _ v => var _ _ (r _ v)
  | app _ _ _ t1 t2 => app _ _ _ (rename r t1) (rename r t2)
  | abs _ _ _ f => abs _ _ _ (rename (rename_lifted r) f)

  (* Arrays *)
  | build _ _ _ ta => build _ _ _ (rename r ∘ ta)
  | get _ ti ta => get _ ti (rename r ta)
  | ifold _ _ tf ti ta => ifold _ _ (rename r tf) (rename r ti) (rename r ta)

  (* Nat *)
  | nval _ n => nval _ n

  (* Reals *)
  | rval _ r => rval _ r
  | add _ t1 t2 => add _ (rename r t1) (rename r t2)

  (* Products *)
  | tuple _ t1 t2 => tuple _ (rename r t1) (rename r t2)
  | first _ p => first _ (rename r p)
  | second _ p => second _ (rename r p)

  (* Sums *)
  | case _ e c1 c2 =>
      case _ (rename r e)
        (rename r c1)
        (rename r c2)
  | inl _ _ _ e => inl _ _ _ (rename r e)
  | inr _ _ _ e => inr _ _ _ (rename r e)
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
  | var _ _ v => s _ v
  | app _ _ _ t1 t2 => app _ _ _ (substitute s t1) (substitute s t2)
  | abs _ _ _ f => abs _ _ _ (substitute (substitute_lifted s) f)

  (* Arrays *)
  (* | build_nil _ _ => build_nil _ _ *)
  | build _ _ _ ta => build _ _ _ (substitute s ∘ ta)
  | get _ ti ta => get _ ti (substitute s ta)
  | ifold _ _ tf ti ta =>
    ifold _ _ (substitute s tf) (substitute s ti) (substitute s ta)

  (* Nat *)
  | nval _ n => nval _ n

  (* Reals *)
  | rval _ r => rval _ r
  | add _ t1 t2 => add _ (substitute s t1) (substitute s t2)

  (* Products *)
  | tuple _ t1 t2 => tuple  _ (substitute s t1) (substitute s t2)
  | first _ p => first _ (substitute s p)
  | second _ p => second _ (substitute s p)

  (* Sums *)
  | case _ e c1 c2 =>
      case _ (substitute s e)
        (substitute s c1)
        (substitute s c2)
  | inl _ _ _ e => inl _ _ _ (substitute s e)
  | inr _ _ _ e => inr _ _ _ (substitute s e)
  end.
(*
Equations substitute_env {Γ Γ'} (G: Env Γ) (sb : sub Γ Γ'): Env Γ' :=
substitute_env env_nil s := env_nil;
substitute_env (env_cons t G') s := env_cons (substitute sb t) G'. *)

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
  { erewrite build_congr...
    extensionality x... }
  (* { erewrite ifold_congr...
    extensionality x... } *)
Qed.

Lemma lift_ren_id : forall Γ τ,
  rename_lifted (@id_ren Γ) = @id_ren (τ::Γ).
Proof. intros. ExtVar. Qed.

Lemma app_ren_id : forall Γ τ (t : tm Γ τ),
  rename id_ren t = t.
Proof with quick.
  induction t; Rewrites lift_ren_id.
  { erewrite build_congr...
    extensionality x... }
  (* { erewrite ifold_congr...
    extensionality x... } *)
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
  { erewrite build_congr...
    extensionality x... }
  (* { erewrite ifold_congr...
    extensionality x... } *)
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
  { erewrite build_congr...
    extensionality x... }
  (* { erewrite ifold_congr...
    extensionality x... } *)
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
  { erewrite build_congr...
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
  { erewrite build_congr...
    extensionality x... }
  (* { erewrite ifold_congr...
    extensionality x... } *)
Qed.

(* Helpers *)
Definition array_add {Γ n} (t1 t2 : tm Γ (Array n Real)): tm Γ (Array n Real) :=
  (build _ _ _ (fun i =>
    (add _
      (get _ i t1))
      (get _ i t2))).

Definition array_tuple {Γ τ σ n} (t : tm Γ σ) (ta : tm Γ (Array n τ))
  : tm Γ (Array n (τ × σ)) :=
  (build _ _ _ (fun i =>
    (tuple _ (get _ i ta) (t)))).

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
  { erewrite build_congr...
    extensionality x... }
  (* { erewrite ifold_congr...
    extensionality x... } *)
Qed.

(* Lemma subst_cons_lift_cons :
  forall Γ Γ' τ σ (t : tm (σ::Γ) τ) (s : tm Γ' σ) (sb : sub Γ Γ'),
  substitute (| s |) (substitute (substitute_lifted sb) t) =
    substitute (cons_sub s sb) t.
Proof.
Admitted. *)

(*
  Typing
  Redundant to define this considering it is builtin to the
   structure of the language?
*)
Definition has_type {Γ τ} (t : tm Γ τ) : ty := τ.
Notation "Γ ⊢ t ∷ τ" := (@has_type Γ τ t) (at level 70).
Corollary has_type_refl Γ τ (t : tm Γ τ) :
  has_type t = τ.
Proof. reflexivity. Qed.

(* Fixpoint substitute_env {Γ Γ'} (s : sub Γ Γ') (E : Env Γ) : Env Γ' :=
  match E with
  | env_nil =>
  | env_cons c E' => env_cons (substitute_closed s c) (substitute_env s E')
  end
with substitute_closed {Γ Γ' τ} (s : sub Γ Γ') (c : Closed τ) : Closed τ :=
  match c with
  | closure t E => closure (substitute s t) (substitute_env s E)
  | clapp cf c => clapp (substitute_closed s cf) (substitute_closed s c)
  end. *)