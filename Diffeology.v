Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Arith.PeanoNat.
Require Import Program.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.analysis.topology.
Require Import mathcomp.analysis.normedtype.
Require Import mathcomp.analysis.derive.
Require Import mathcomp.analysis.classical_sets.
Require Import Arith_base.
Require Import mathcomp.algebra.matrix.
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

  (*
    Currently just contains sketches and (probably) nonsense.
      Doubt that any of this is actually mathematically sound.
  *)

  (*
    Define R^n as a 1-col n-row matrix.
  *)
  Definition R_space_open n := forall (v : set 'rV[R]_n), open v.
  Definition R_space := forall n, R_space_open n.

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

  Definition smooth_function {X Y} (f : X -> Y) : Prop :=
    differentiable f
  .

  Inductive plot : forall {U X}, (U -> X) -> Prop :=
    | const_plot : forall U X (f : U -> X),
      constant_function f ->
      plot f
    | compose_plot : forall U V X (f : V -> U) (p : U -> X),
      smooth_function f ->
      plot p ->
      plot (compose p f)
  .

  (*
    Interface(?) of a diffeological space:
      In the actual proof would have to be integrated in existing hierarchy to
      get the definitions of derivatives proofs using either mathcomp's or
      Coquelicot's algebraic hierarchy.
  *)
  Record DiffeoSp := make_dsp {
    (* Subset of functions from (R^n -> X) which satisfy the requirements of
        being a plot *)
    carrier :> Set;
    plots :
      forall (f : R_space -> carrier),
        plot f;
  }.

  (* The set of smooth functions between diffeological spaces *)
  Record diff_smooth (D1 D2 : DiffeoSp) := make_dsmooth {
    dsmooth :> D1 -> D2;
    smooth_dsmooth : smooth_function dsmooth;
  }.

  Notation "a -d> b" := (diff_smooth a b) (at level 30).

  Definition smooth_compose {X Y Z} (f : X -d> Y) (g : Y -d> Z)
    : X -d> Z.
  Proof with auto.
    inversion f as [f' Hf].
    inversion g as [g' Hg].
    pose proof (compose g' f') as h.
    inversion Hf. inversion Hg.
    assert (H': smooth_function h). { admit. }
    exists (make_dsmooth X Z h H')...
  Admitted.

  Lemma R_plots :
    forall (f : R_space -> R),
      plot f.
  Proof.
    Admitted.

  Lemma product_plots (X Y : DiffeoSp) :
    forall (f : R_space -> carrier X * carrier Y),
      plot f.
  Proof.
    Admitted.

  Definition product_diffeology (X Y : DiffeoSp) : DiffeoSp :=
    make_dsp (carrier X * carrier Y)
      (product_plots X Y).

  Notation "a *d* b" := (product_diffeology a b) (at level 90).

  Definition d_fst (X Y : DiffeoSp)
    : X *d* Y -> X.
  Proof with auto.
    intros H. inversion H. assumption.
  Defined.

  Definition d_snd (X Y : DiffeoSp)
    : X *d* Y -> Y.
  Proof with auto.
    intros H. inversion H. assumption.
  Defined.

  Definition product_fst
    : forall (X Y : DiffeoSp), (X *d* Y) -d> X.
  Proof.
    inversion X as [X1 Hplot1].
    inversion Y as [X2 Hplot2].
    assert (smooth_function (d_fst X Y)).
    { admit. }
    exists (make_dsmooth (X *d* Y) X (d_fst X Y) H).
    Admitted.

  Definition product_snd
    : forall (X Y : DiffeoSp), (X *d* Y) -d> Y.
  Proof.
    inversion X as [X1 Hplot1].
    inversion Y as [X2 Hplot2].
    assert (smooth_function (d_snd X Y)).
    { admit. }
    exists (make_dsmooth (X *d* Y) Y (d_snd X Y) H).
    Admitted.

  Lemma smooth_plots X Y :
    forall (f : R_space -> diff_smooth X Y),
      plot f.
  Proof.
    Admitted.

  Definition functional_diffeology (X Y : DiffeoSp) : DiffeoSp :=
    make_dsp (diff_smooth X Y) (smooth_plots X Y).

  Notation "a -D> b" := (functional_diffeology a b) (at level 70).

  Definition R_diffeology := make_dsp R R_plots.

  Lemma unit_plots :
    forall (f : R_space -> ()),
      plot f.
  Proof.
    Admitted.

  Definition unit_diffeology := make_dsp unit unit_plots.

(*
  In the style of mathcomp.analysis which uses
    Canonical Structures
*)
(* Module Diff.

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

End Diff. *)