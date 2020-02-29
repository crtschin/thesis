Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Arith.PeanoNat.
Require Import Program.
Require Import Coquelicot.Coquelicot.
Require Import Arith_base.
From mathcomp Require Import ssralg.

From AD Require Import Tactics.
From AD Require Import Definitions.
From AD Require Import Macro.

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
    Functions which are differentiable over their complete input domain.
      Highly doubt that this definition is correct.

    Should look for a proper (hopefully existing) notion of
      multivariate differentiabiliy.
  *)

  Definition constant_function {X Y} (f : X -> Y) : Prop :=
    exists (a : Y), f = (fun _ => a).

  Program Definition smooth {K}
    {U V: NormedModule K} (f : U -> V) : Prop :=
    forall K l, filterdiff f K l.

  (* Fixpoint plot {K} {X} {U : NormedModule K} (f : U -> X): Prop :=
    constant_function f \/
      (forall {V : NormedModule K}
        (g : V -> U),
      smooth g). *)

  Inductive plot : forall {U X}, (U -> X) -> Prop :=
    | const_plot : forall U X (f : U -> X),
      constant_function f ->
      plot f
    | compose_plot :
      forall {K} {X} {U V: NormedModule K} (f : V -> U) (p : U -> X),
      smooth f ->
      plot p ->
      plot (p ∘ f)
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
      forall {K} (U : NormedModule K) (f : U -> carrier),
        plot f;
  }.

  Lemma compose_constant {X Y Z} {f : X -> Y} {g : Y -> Z} :
    constant_function f -> constant_function g -> constant_function (compose g f).
  Proof.
    intros. unfold constant_function in *.
    destruct H. destruct H0.
    exists x0. subst. unfold compose. reflexivity.
  Qed.

  Lemma R_plots :
    forall K {U : NormedModule K} (f : U -> R),
      plot f.
  Proof.
    intros.
    constructor.
    unfold constant_function.
    Admitted.

  Lemma product_plots (X Y : DiffeoSp) :
    forall K {U : NormedModule K} (f : U -> carrier X * carrier Y),
    plot f.
  Proof.
    Admitted.

  Definition product_diffeology (X Y : DiffeoSp) : DiffeoSp :=
    make_dsp (carrier X * carrier Y)
      (product_plots X Y).

  Notation "a *** b" := (product_diffeology a b) (at level 30).

  Definition d_first {X Y : DiffeoSp}
    : X *** Y -> X.
  Proof with auto. intros H. inversion H... Defined.

  Definition d_second {X Y : DiffeoSp}
    : X *** Y -> Y.
  Proof with auto. intros H. inversion H... Defined.

  Definition smooth_diffeological
    {D1 D2 : DiffeoSp} (f : D1 -> D2) : Prop :=
    forall K (U : NormedModule K)
      (p : U -> D1) (g : U -> D2),
      g = compose f p -> plot f /\ plot g
  .

  Lemma smooth_diffeological_comp :
    forall {D1 D2 D3 : DiffeoSp} (f1 : D1 -> D2) (f2 : D2 -> D3),
      smooth_diffeological f1 ->
      smooth_diffeological f2 ->
        smooth_diffeological (f2 ∘ f1).
  Proof.
    intros D1 D2 D3 f1 f2 H1 H2. unfold smooth_diffeological in *.
    intros K U g h Heq.
    specialize H1 with K U g (f1 ∘ g).
    specialize H2 with K U (f1 ∘ g) (f2 ∘ f1 ∘ g).
    pose proof (H1 eq_refl) as H.
    pose proof (H2 eq_refl) as H'.
    clear H1 H2.
    split.
    { apply compose_plot. }
  Admitted.

  (* The set of smooth functions between diffeological spaces *)
  Record diffeological_smooth (D1 D2 : DiffeoSp) := make_dsmooth {
    dsmooth :> D1 -> D2;
    smooth_dsmooth : smooth_diffeological dsmooth;
  }.

  Notation "a -d> b" := (diffeological_smooth a b) (at level 90).

  Lemma smooth_plots X Y :
    forall K {U : NormedModule K}
      (f : U -> diffeological_smooth X Y),
    plot f.
  Proof.
    intros. constructor. unfold constant_function.
    Admitted.

  Definition functional_diffeology (X Y : DiffeoSp) : DiffeoSp :=
    make_dsp (diffeological_smooth X Y) (smooth_plots X Y).

  Notation "a -D> b" := (functional_diffeology a b) (at level 70).

  Definition R_diffeology := make_dsp R R_plots.

  Lemma unit_plots :
    forall K {U : NormedModule K}
      (f : U -> ()),
    plot f.
  Proof.
    intros. constructor.
    unfold constant_function.
    exists tt. apply functional_extensionality.
    intros. remember (f x). induction u. reflexivity.
  Qed.

  Definition unit_diffeology := make_dsp unit unit_plots.

  Definition diffeological_smooth_comp :
    forall {D1 D2 D3:DiffeoSp},
      (D2 -d> D3) -> (D1 -d> D2) -> D1 -d> D3.
  Proof.
    intros D1 D2 D3 f g.
    inversion f as [f1 P1]. inversion g as [f2 P2].
    exists (fun n => f1 (f2 n)); intros.
    pose proof (smooth_diffeological_comp f2 f1 P2 P1).
    unfold compose in H... auto.
  Defined.

  Lemma functional_diffeology_app :
    forall {D1 D2 D3 : DiffeoSp}
      (f1 : D1 -> D2)
      (f2 : D1 -> (D2 -D> D3)),
    smooth_diffeological f1 ->
    smooth_diffeological f2 ->
    smooth_diffeological (fun d : D1 => f2 d (f1 d)).
  Proof.
    intros D1 D2 D3 f1 f2 H1 H2.
  Admitted.

  Definition diffeological_smooth_app :
    forall {D1 D2 D3:DiffeoSp},
      (D1 -d> D2) -> (D1 -d> (D2 -D> D3)) -> D1 -d> D3.
  Proof with auto.
    intros D1 D2 D3 f g.
    inversion f as [f1 P1]. inversion g as [f2 P2].
    exists (fun d => (f2 d) (f1 d)).
    pose proof (functional_diffeology_app f1 f2 P1 P2)...
  Defined.

  Definition curry {D1 D2 D3 : DiffeoSp} (f : D1 *** D2 -d> D3)
    : D2 -d> (D1 -D> D3).
  intros.
  pose proof (D1 *** D2).
  Admitted.

  Definition diffeological_smooth_abs :
    forall {D1 D2 D3:DiffeoSp},
      (D1 -d> D2) -> (D1 -d> (D2 -D> D3)) -> D1 -d> D3.
  Proof with auto.
    intros D1 D2 D3 f g.
    inversion f as [f1 P1]. inversion g as [f2 P2].
    exists (fun d => (f2 d) (f1 d)).
    pose proof (functional_diffeology_app f1 f2 P1 P2)...
  Defined.

  Definition product_smooth {X Y Z: DiffeoSp}
    (f : X -d> Y) (g : X -d> Z) : X -d> Y *** Z.
  Proof.
    inversion f as [f' P1].
    inversion g as [g' P2].
    exists (fun x => (f' x, g' x)).


  Definition product_first
    : forall {X Y : DiffeoSp}, X *** Y -d> X.
  Proof with auto.
    intros.
    exists fst. red.
    intros. rewrite H.
    splits.
    { constructor. }
    { constructor. }
    Admitted.

  Definition product_second
    : forall {X Y : DiffeoSp}, X *** Y -d> Y.
  Proof.
    Admitted.

  Definition constant_smooth {D1 D2 : DiffeoSp} (d : D2) : D1 -d> D2.
  Proof with eauto.
    exists (fun _ => d).
    unfold smooth_diffeological.
    intros. rewrite H.
    split; unfold compose;
      constructor; exists d...
  Defined.
