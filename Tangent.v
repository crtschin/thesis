Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.

Import EqNotations.

Open Scope type_scope.

Parameter T : forall {X Y}, X -> Y.
Parameter Tx : forall {X Y} (f : X -> Y), T f.
Axiom T_fun : forall {X Y : Type} (f : X -> Y),
  T f = (T X -> T Y).
Axiom T_prod : forall {X Y W V : Type},
  T (X, Y) = @pair W V (T X) (T Y).
Axiom T_sum : forall {X Y: Type},
  T (sum X Y) = sum (T X) (T Y).
Axiom T_comp : forall {X Y Z W V} (f : X -> Y) (g : Y -> Z),
  T (compose g f) = @compose W V (T f) (T g).

Check Tx.
Definition Derive {X Y} (f : X -> Y) {x : X} := (Tx f) x.