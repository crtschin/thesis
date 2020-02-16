Set Warnings "-notation-overridden,-parsing".

Require Import Lists.List.
Import ListNotations.
Require Import Strings.String.
Require Import Reals.
Require Import Logic.JMeq.
Require Import Arith.PeanoNat.
Require Import Program.Equality.

Require Import Definitions.
Require Import Macro.

Open Scope R_scope.

(*
Literature:

Main paper:
- Correctness of Automatic Differentiation via
    Diffeologies and Categorical Gluing by Huot, Staton and Vakar.

Well-scoped, well-typed debruijn indices in language:
- Strongly Typed Term Representations in Coq by Benton, et al.
- Type-Preserving Renaming and Substitution by McBride.
- Parametric Higher-Order Abstract Syntax for Mechanized Semantics by Chlipala.

Logical Relations:
- From Mathematics to Abstract Machine - Swierstra
- A Note on Logical Relations Between Semantics and Syntax by Pitts
- Logical Relations and The Typed Lambda Calculus - Statman
- Step-Indexed Syntactic Logical Relations for
    Recursive and Quantified Types - Ahman

Coq:
- Elimination with a motive by McBride.
- Program-ing Finger Trees using Coq by Sozeau.
- Improving Real Analysis in Coq by Boldo, et al.

Automatic Differentiation:
- The Simple Essence of Automatic Differentiation by Eliott.

Mathematics:
- An Introduction To Diffeology - Zemmour.

Notational conventions:
  capital greeks for typing environment
  lowercase greeks for types
  lowercase latin for terms
*)
