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

(*
  Goal:
    Setup either a type (or an interface?) which models the Diff category in
    the paper containing diffeological spaces and smooth functions between
    diffeological spaces.

  Description of diffeological spaces:

    Like posets are sets with a partial ordering property, diffeological spaces
    are sets with a continuously differentiable property.

    Diffeological spaces describe sets X along with a diffeology P_X
    containing functions (f: U -> X) where U is some open subset of R^n for some
    n and every such function is a plot.

    A plot is defined as a function containing the following properties:
    - all constant functions are plots.
    - if (f: U -> V) is a smooth function, a p is a plot, f . p is also a plot.
    - stays a plot under gluing from some smaller set into its super set.

    Example:
    So R, R^n are diffeological spaces. But also the smooth functions between
    these spaces.

    These correspond to directly to the type system we use as:
    - ground types correspond to R
    - product types of arity n correspond to R^n
    - function types of some X to Y correspond to the smooth functions between
      the spaces corresponding to X and Y
    - coproduct types correspond to the 3rd property

  Expected to be needed/defined/proven:
    R^n: using std's vector or mathcomp's matrix with a single column
    open subsets: ?
    plots: as a prop containing the 3 properties
      constant functions
      smooth function
    diffeological space: written as some abstract interface containing the type
      and the plot property (relevant are type classes or canonical structures)
    membership: prove R, R^n and the smooth functions between spaces are members
      of diffeological spaces
*)

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

  (*
    Functions which are differentiable over their complete input domain.
      Highly doubt that this definition is correct.

    Should look for a proper (hopefully existing) notion of
      multivariate differentiabiliy.
  *)

  Definition constant_function {X Y} (f : X -> Y) : Prop :=
    exists y, forall (x : X), f x = y
  .

  Inductive differentiable {X Y} (f : X -> Y) :=
    | const_diff :
      constant_function f -> differentiable f
  .

  Definition smooth_function {X Y} : (X -> Y) -> Prop :=
    fun f => differentiable f
  .

  Inductive plot : forall {U X}, (U -> X) -> Prop :=
    | const_plot : forall U X (f : U -> X),
      constant_function f ->
      plot f
    | compose_plot : forall U V X (g : V -> U) (f : U -> X),
      smooth_function g ->
      plot f ->
      plot (compose f g)
  .

  Record DiffeoSp := make_dsp {
    X : Type;
    (* Subset of functions from (R^n -> X) which satisfy the requirements of
        being a plot *)
    diff_plots :
      forall n P,
      @sig (@sig (EuclidSp n) P -> X) plot;
  }.

  Lemma R_plot :
    forall n P,
      @sig (@sig (EuclidSp n) P -> R) plot.
  Proof.
    intros.
    econstructor. econstructor...
    Admitted.

  Lemma Rn_plot m :
    forall n P,
      @sig (@sig (EuclidSp n) P -> EuclidSp m) plot.
  Proof.
    intros.
    econstructor. econstructor...
    Admitted.

  Lemma smooth_plot X Y :
    forall n P,
      @sig (@sig (EuclidSp n) P -> (sig (@smooth_function X Y))) plot.
  Proof.
    intros.
    econstructor. econstructor...
    Admitted.

  Definition R_diff := make_dsp R R_plot.
  Definition Rn_diff m := make_dsp (EuclidSp m) (Rn_plot m).
  Definition Rsmooth_diff X Y := make_dsp
    (sig (@smooth_function X Y))
    (smooth_plot X Y).

End sketch.

(*
  In the style of mathcomp/analysis which uses
    Canonical Structures
*)
Module DIFF.

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