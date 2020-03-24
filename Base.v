Set Warnings "-notation-overridden,-parsing".

Require Import Lists.List.
Import ListNotations.
Require Import Strings.String.
Require Import Reals.
Require Import Logic.JMeq.
Require Import Arith.PeanoNat.
Require Import Program.Equality.

(*
Questions:
(* Equations *)
(* Opaque substitute_lifted *)
(* Sum types *)
(* Denotational instantiation *)

Notational conventions:
  capital greeks for typing environment
  lowercase greeks for types
  lowercase latin for terms

Functional extensionality is oft used and the derivative is (to be) defined axiomatically

Literature:

Main paper:
- Correctness of Automatic Differentiation via
    Diffeologies and Categorical Gluing by Huot, Staton and Vakar.

Very relevant:
- On the Versatility of Open Logical Relations - Barthe, et al.

Logical Relations:
- From Mathematics to Abstract Machine by Swierstra
- A Note on Logical Relations Between Semantics and Syntax by Pitts
- Logical Relations and The Typed Lambda Calculus by Statman
- Step-Indexed Syntactic Logical Relations for
    Recursive and Quantified Types by Ahman

Coq:
- Coq:
  + A short presentation of Coq by Bertot.
  + Theorem proving support in programming language semantics by Bertot.
- Denotational Semantics:
  + Some Domain Theory and Denotational Semantics in Coq by Benton, et al.
  + General Recursion Using Co-Inductive Types by Capretta.
- Well-scoped, well-typed debruijn indices in language:
  + Strongly Typed Term Representations in Coq by Benton, et al.
  + Type-Preserving Renaming and Substitution by McBride.
  + Parametric Higher-Order Abstract Syntax for Mechanized Semantics by Chlipala.
- GADTS:
  + Elimination with a motive by McBride.
  + Program-ing Finger Trees using Coq by Sozeau.
- Reals:
  + Improving Real Analysis in Coq by Boldo, et al.
- Modularity:
  + Canonical Structures for the working Coq user by Mahboubi and Tassi.
  + Packaging Mathematical Structures by Garillot, et al

Automatic Differentiation:
- The Simple Essence of Automatic Differentiation by Eliott.

Mathematics:
- An Introduction To Diffeology by Zemmour.
*)
