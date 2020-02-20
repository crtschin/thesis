Require Import Lists.List.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Arith.PeanoNat.
Require Import Program.
Require Import Coquelicot.Coquelicot.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Arith_base.
Require Import Vector.
Require Import mathcomp.algebra.vector.
From mathcomp Require Import ssralg.
Require Import Definitions.
Require Import Macro.

Local Open Scope nat_scope.
Local Open Scope R_scope.

Module sketch.
(*
  Currently just contains sketches and (probably) nonsense.
    Doubt that any of this is actually mathematically sound.
*)

(*
  Define R^n as a n-length vector.
*)
Definition EuclidSp : nat -> Type :=
  fun n => t R n
.

Definition constant_function {X Y} (f : X -> Y) : Prop :=
  exists y, forall (x : X), f x = y
.

(*
  Using Coquelicot's formulation:

*)

(*
  Functions which are differentiable over their complete input domain.
    Highly doubt that this definition is correct.

  Should look for a proper (hopefully existing) notion of
    multivariate differentiabiliy.
 *)
Inductive differentiable {X Y} (f : X -> Y) :=
  | const_diff :
    constant_function f -> differentiable f
.
Definition smooth_function {X Y} (f : X -> Y) : Prop :=
  differentiable f
.

Inductive plot : forall {U X}, (U -> X) -> Type :=
  | const_plot : forall U X (f : U -> X),
    constant_function f ->
    plot f
  | compose_plot : forall U V X (g : V -> U) (f : U -> X),
    smooth_function g ->
    plot f ->
    plot (compose f g)
.

(* Definition open_subset n (P : EuclidSp n) := @open P. *)
Record DiffeoSp := make_dsp {
  X :> Type;
  diff_plots : forall n (f : EuclidSp n -> X), plot f;
}.

Lemma R_plot n : forall n' (f : EuclidSp n' -> EuclidSp n),
  plot f.
Proof. Admitted.

Definition R_diff : forall n, make_dsp (EuclidSp n) (R_plot n).
  Admitted.

End sketch.

(*
  In the style of mathcomp/analysis which uses
    Canonical Structures
*)
Module Diff.

Section ClassDef.

Variable K : AbsRing.

Record mixin_of := {

}

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : Diff.mixin_of (UniformSpace.Pack T base T)
}.

Definition base2 T (cT : class_of T) : Diff.class_of T :=
  Diff.Class _ (base T cT) (mixin T cT).

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition NormedModuleAux := NormedModuleAux.Pack _ cT xclass xT.
Definition NormedModule := NormedModule.Pack _ cT xclass xT.
Definition UniformSpace := UniformSpace.Pack cT xclass xT.
Definition Diff := Diff.Pack cT xclass xT.

End ClassDef.


End DIFF.