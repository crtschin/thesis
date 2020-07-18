Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Reals.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.

Require Import Equations.Equations.
Require Import AD.Tactics.

Local Open Scope program_scope.

Inductive ty : Type :=
  | Real : ty
  | Bool : ty
  | Nat : ty
  | Array : nat -> ty -> ty
  | Arrow : ty -> ty -> ty
  | Prod  : ty -> ty -> ty
  | Sum  : ty -> ty -> ty
.

Notation "'ℝ'" := (Real).
Notation "'ℕ'" := (Nat).
Notation "'𝔹'" := (Bool).
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

  (* Bool *)
  | tru : tm Γ 𝔹
  | fls : tm Γ 𝔹
  | ifelse : forall τ,
    tm Γ 𝔹 -> tm Γ τ -> tm Γ τ -> tm Γ τ
  | rlt :
    tm Γ ℝ -> tm Γ ℝ -> tm Γ 𝔹

  (* Arrays *)
  | build : forall τ n,
    (Fin.t n -> tm Γ τ) -> tm Γ (Array n τ)
  | get : forall {τ n},
    Fin.t n -> tm Γ (Array n τ) -> tm Γ τ

  (* Reals *)
  | rval : forall (r : R), tm Γ ℝ
  | add : tm Γ ℝ -> tm Γ ℝ -> tm Γ ℝ
  | mul : tm Γ ℝ -> tm Γ ℝ -> tm Γ ℝ

  (* Nat *)
  | nsucc : tm Γ ℕ -> tm Γ ℕ
  | nval : forall (n : nat), tm Γ ℕ
  | nrec : forall τ,
    tm Γ (τ → τ) -> tm Γ ℕ -> tm Γ τ -> tm Γ τ

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

Lemma build_eq : forall Γ τ n (ta ta' : Fin.t n -> tm Γ τ),
  ta = ta' -> build Γ τ n ta = build Γ τ n ta'.
Proof. intros; rewrites. Qed.

(* Examples *)
Definition ex_id_real :=
  abs [] Real Real
    (var [Real] Real (Top _ _)).

Definition ex_const :=
  abs [] (Real → Real) Real
    (abs [Real] (Real) (Real)
      (var [Real;Real] Real (Top [Real] Real))).

Definition ex_plus {Γ} :=
  abs Γ _ _ (abs _ _ _
    (add _
      (var _ Real (Pop _ Real Real (Top _ Real)))
        (var _ Real (Top _ Real)))).

Definition ex_square {Γ} :=
  abs Γ _ _
    (mul _
      (var _ Real (Top _ Real))
      (var _ Real (Top _ Real))).

Definition square_plus {Γ : Ctx} :=
  app (ℝ::ℝ::Γ) _ _
  ((app _ _ _
    ex_plus
    (var _ Real (Pop _ Real Real (Top _ Real)))))
  (app _ _ _ ex_square (var _ Real (Top _ Real))).

Definition ex_square_plus {Γ} :=
  abs Γ _ _ (abs _ _ _ square_plus).

Definition ex_neuron :=
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
  | var _ _ v => var _ _ (r _ v)
  | app _ _ _ t1 t2 => app _ _ _ (rename r t1) (rename r t2)
  | abs _ _ _ f => abs _ _ _ (rename (rename_lifted r) f)

  (* Bool *)
  | tru _ => tru _
  | fls _ => fls _
  | ifelse _ _ b t f => ifelse _ _ (rename r b) (rename r t) (rename r f)
  | rlt _ t1 t2 => rlt _ (rename r t1) (rename r t2)

  (* Arrays *)
  | build _ _ _ ta => build _ _ _ (rename r ∘ ta)
  | get _ ti ta => get _ ti (rename r ta)

  (* Nat *)
  | nval _ n => nval _ n
  | nsucc _ t => nsucc _ (rename r t)
  | nrec _ _ f i d => nrec _ _ (rename r f) (rename r i) (rename r d)

  (* Reals *)
  | rval _ r => rval _ r
  | add _ t1 t2 => add _ (rename r t1) (rename r t2)
  | mul _ t1 t2 => mul _ (rename r t1) (rename r t2)

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

  (* Bool *)
  | tru _ => tru _
  | fls _ => fls _
  | ifelse _ _ b t f => ifelse _ _ (substitute s b) (substitute s t) (substitute s f)
  | rlt _ t1 t2 => rlt _ (substitute s t1) (substitute s t2)

  (* Arrays *)
  | build _ _ _ ta => build _ _ _ (substitute s ∘ ta)
  | get _ ti ta => get _ ti (substitute s ta)

  (* Nat *)
  | nval _ n => nval _ n
  | nsucc _ t => nsucc _ (substitute s t)
  | nrec _ _ f i d =>
    nrec _ _ (substitute s f) (substitute s i) (substitute s d)

  (* Reals *)
  | rval _ r => rval _ r
  | add _ t1 t2 => add _ (substitute s t1) (substitute s t2)
  | mul _ t1 t2 => mul _ (substitute s t1) (substitute s t2)

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

Definition letin {Γ τ σ} (e : tm Γ σ) (x : tm (σ::Γ) τ) : tm Γ τ :=
  app Γ τ σ (abs Γ τ σ x) e.
Definition ifold {Γ τ} (tf : tm Γ (ℕ → τ → τ)) (n : tm Γ ℕ) (td : tm Γ τ)
  : tm Γ τ :=
  nrec Γ τ
    (app Γ (τ → τ) ℕ (abs Γ (τ → τ) ℕ
      (app (ℕ::Γ) (τ → τ) ℕ (shift tf) (nsucc (ℕ::Γ) (var (ℕ::Γ) ℕ (Top Γ ℕ))))) (nval Γ 0%nat))
    n td.
Definition vector_hot ( Γ : list ty ) ( n : nat ) ( i : Fin.t n ) :=
  build Γ ℝ n (fun j => if Fin.eqb i j then rval Γ 1 else rval Γ 0).
Definition vector_map { Γ τ σ n } ( f : tm Γ (τ → σ) )
  ( a : tm Γ (Array n τ) ) : tm Γ (Array n σ) :=
  build Γ σ n (fun i => app Γ σ τ f (get Γ i a)).
Definition vector_map2 { Γ τ σ ρ n }
  ( a1 : tm Γ (Array n τ) ) ( a2 : tm Γ (Array n σ) )
  ( f : tm Γ (τ → σ → ρ) ) : tm Γ (Array n ρ) :=
  build Γ ρ n (fun i => app _ _ _ (app _ _ _ f (get Γ i a1)) (get Γ i a2)).
Definition vector_zip { Γ τ σ n }
  ( a1 : tm Γ (Array n τ) ) ( a2 : tm Γ (Array n σ) )
  : tm Γ (Array n ( τ × σ )) :=
  vector_map2 a1 a2 (abs _ _ _ (abs _ _ _
    (tuple _
      (var _ _ (Pop _ _ _ (Top _ _)))
      (var _ _ (Top _ _))))).
Definition vector_fill { Γ τ } ( n : nat ) ( e : tm Γ τ )
  : tm Γ (Array n τ) :=
  build Γ τ n (fun _ => e).
Definition vector_add {Γ n}
  ( a1 a2 : tm Γ (Array n Real) ) : tm Γ (Array n Real) :=
  vector_map2 a1 a2 (abs _ _ _ (abs _ _ _
    (add _
      (var _ _ (Pop _ _ _ (Top _ _)))
      (var _ _ (Top _ _))))).
Definition vector_scale {Γ n} ( s : tm Γ Real )
  ( a : tm Γ (Array n Real) ) : tm Γ (Array n Real) :=
  vector_map (abs _ _ _ (mul _ (shift s) (var _ _ (Top _ _)))) a.
Definition tm_compose {Γ τ σ ρ} : tm Γ (τ → σ) -> tm Γ (σ → ρ) -> tm Γ (τ → ρ)
  := fun f g =>
  abs _ _ _ (app _ _ _ (shift g) (app _ _ _ (shift f) (var _ _ (Top _ _)))).
