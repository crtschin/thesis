Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Arith.PeanoNat.
Require Import Program.
Require Import Coquelicot.Coquelicot.
Require Import Arith_base.

Ltac quick := simpl in *; intros; eauto.
Ltac splits := repeat try split.
Ltac eta_expand := repeat (apply functional_extensionality_dep; intros).
Ltac admitted := repeat admit.