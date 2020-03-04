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

  Definition smooth {K}
    {U V: NormedModule K} (f : U -> V) : Prop :=
    forall k l, filterdiff f k l.

  (* Various sets of functions *)
  Record constant_functions X Y := make_constant {
    constant_fun :> X -> Y;
    constant_Prop : constant_function constant_fun;
  }.
  Notation "R1 -c> R2" :=
    (constant_functions R1 R2)
    (at level 93, right associativity).
  Record smooth_functions {K} (U V: NormedModule K) := make_sf {
    smooth_fun :> U -> V;
    smooth_Prop : smooth smooth_fun;
  }.
  Notation "R1 -s> R2" :=
    (smooth_functions R1 R2)
    (at level 94, right associativity).
  Record smooth_constant_functions {K} (U V: NormedModule K) := make_scf {
    sc_fun :> U -> V;
    sc_Prop : smooth sc_fun \/ constant_function sc_fun;
  }.
  Notation "R1 -sc> R2" :=
    (smooth_constant_functions R1 R2)
    (at level 95, right associativity).

  (* Fixpoint plot {K} {X} {U : NormedModule K} (f : U -> X): Prop :=
    constant_function f \/
      (forall {V : NormedModule K}
        (g : V -> U),
      smooth g /\ plot (f ∘ g)). *)

  Inductive plot : forall {K} {U : NormedModule K} {X}, (U -> X) -> Prop :=
    | const_plot :
      forall {K} {U : NormedModule K} {X} (f : U -> X),
        constant_function f ->
        plot f
    | compose_plot :
      forall {K} {U V: NormedModule K} {X} (f : V -> U) (p : U -> X),
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
        plot f
  }.

  (* Ground diffeological spaces *)
    (* R instance *)
      Lemma R_plots :
        forall K {U : NormedModule K} (f : U -> R),
          plot f.
      Proof.
        intros.
        constructor.
        Admitted.
      Definition R_diffeology := make_dsp R R_plots.

    (* unit instance *)
      Lemma unit_plots :
        forall K {U : NormedModule K}
          (f : U -> ()),
        plot f.
      Proof with eauto.
        intros. constructor.
        exists tt. apply functional_extensionality.
        intros. remember (f x). induction u. reflexivity.
      Qed.
      Definition unit_diffeology := make_dsp unit unit_plots.

  (* Functional Diffeologies *)
    (* Defining smooth maps between diffeological spaces *)
      Definition smooth_diffeological
        {D1 D2 : DiffeoSp} (f : D1 -> D2) : Prop :=
        forall K (U : NormedModule K)
          (p : U -> D1) (g : U -> D2),
          g = compose f p -> plot p /\ plot g
      .

    (* The set of smooth maps between diffeological spaces *)
      Record diffeological_smooth (D1 D2 : DiffeoSp) := make_dsmooth {
        dsmooth :> D1 -> D2;
        smooth_dsmooth : smooth_diffeological dsmooth;
      }.
      Notation "a -d> b" := (diffeological_smooth a b) (at level 89, right associativity).

    (* Proof smooth maps satisfy the plots requirement *)
      Lemma smooth_plots X Y :
        forall K {U : NormedModule K}
          (f : U -> diffeological_smooth X Y),
        plot f.
      Proof.
        Admitted.

      Definition functional_diffeology (X Y : DiffeoSp) : DiffeoSp :=
        make_dsp (diffeological_smooth X Y) (smooth_plots X Y).
      Notation "a -D> b" := (functional_diffeology a b) (right associativity, at level 70).

      Lemma smooth_diffeological_app :
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
          (D1 -d> (D2 -D> D3)) -> (D1 -d> D2) -> D1 -d> D3.
      Proof with auto.
        intros D1 D2 D3 g f.
        inversion f as [f1 P1]. inversion g as [f2 P2].
        exists (fun d => (f2 d) (f1 d)).
        pose proof (smooth_diffeological_app f1 f2 P1 P2)...
      Defined.

      Definition functional_diffeology_app :
        forall {D1 D2:DiffeoSp},
          (D1 -D> D2) -> D1 -> D2.
      Proof with auto.
        intros D1 D2 f g.
        inversion f as [f1 P1]. apply (f1 g).
      Defined.

      Definition diffeological_smooth_abs :
        forall {D1 D2 D3:DiffeoSp},
          (D1 -d> D2) -> (D1 -d> (D2 -D> D3)) -> D1 -d> D3.
      Proof with auto.
        intros D1 D2 D3 f g.
        inversion f as [f1 P1]. inversion g as [f2 P2].
        exists (fun d => (f2 d) (f1 d)).
        pose proof (smooth_diffeological_app f1 f2 P1 P2)...
      Defined.

  (* Products *)
    (* Diffeology *)
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

    (* Smooth maps between product diffeologies *)
      Definition product_smooth {X Y Z: DiffeoSp}
        (f : X -d> Y) (g : X -d> Z) : X -d> Y *** Z.
      Proof.
        inversion f as [f' P1].
        inversion g as [g' P2].
        exists (fun x => (f' x, g' x)).
      Admitted.

      Definition product_first
        : forall {X Y : DiffeoSp}, X *** Y -d> X.
      Proof with auto.
        intros.
        exists fst. red.
        intros. rewrite H.
        splits.
        Admitted.

      Definition product_second
        : forall {X Y : DiffeoSp}, X *** Y -d> Y.
      Proof.
        Admitted.

  (* Helpers over smooth maps *)
    Definition constant_smooth {D1 D2 : DiffeoSp} (d : D2) : D1 -d> D2.
    Proof with eauto.
      exists (fun _ => d).
      unfold smooth_diffeological.
      intros. rewrite H.
      split. admit.
      constructor. unfold compose.
        exists d...
    Admitted.

    Lemma smooth_diffeological_comp :
      forall {D1 D2 D3 : DiffeoSp} (f1 : D1 -> D2) (f2 : D2 -> D3),
        smooth_diffeological f1 ->
        smooth_diffeological f2 ->
          smooth_diffeological (f2 ∘ f1).
    Proof with eauto.
      intros D1 D2 D3 f1 f2 H1 H2. unfold smooth_diffeological in *.
      intros K U g h Heq.
      specialize H1 with K U g (f1 ∘ g).
      specialize H2 with K U (f1 ∘ g) (f2 ∘ f1 ∘ g).
      pose proof (H1 eq_refl) as [H1p H1pc].
      pose proof (H2 eq_refl) as [H2p H2pc].
      clear H1 H2.
      split.
      constructor.
    Admitted.

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
    Notation " A ∘d B " := (diffeological_smooth_comp A B) (at level 89).

    Definition product_diffeology_symm {D1 D2 : DiffeoSp}
      : D1 *** D2 -> D2 *** D1.
    Proof.
      intros.
    Admitted.

    Definition product_smooth_symm {D1 D2 : DiffeoSp}
      : D1 *** D2 -d> D2 *** D1.
    Proof.
      exists product_diffeology_symm.
    Admitted.

    Definition product_diffeological_symm {D1 D2 : DiffeoSp}
      : D1 *** D2 -D> D2 *** D1.
    Proof.
      exists product_diffeology_symm.
    Admitted.

    Definition curry {D1 D2 D3 : DiffeoSp} (f : D1 *** D2 -d> D3)
      : D2 -d> D1 -D> D3.
    Proof.
    Admitted.

    Definition uncurry {D1 D2 D3 : DiffeoSp} (f : D2 -d> D1 -D> D3)
      : D1 *** D2 -d> D3.
    Proof.
    Admitted.

    Lemma compose_constant {X Y Z} {f : X -> Y} {g : Y -> Z} :
      constant_function f -> constant_function g -> constant_function (compose g f).
    Proof.
      intros. unfold constant_function in *.
      destruct H. destruct H0.
      exists x0. subst. unfold compose. reflexivity.
    Qed.

    Definition add_smooth : R_diffeology -d> R_diffeology -D> R_diffeology.
    Admitted.