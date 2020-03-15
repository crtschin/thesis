Require Import Logic.FunctionalExtensionality.

Create HintDb ad.

Ltac quick := simpl in *; intros; (eauto with ad).
Ltac splits := repeat try split.
Ltac eta_expand := repeat (apply functional_extensionality_dep; intros).
Ltac admitted := repeat admit.
Ltac rewrites := (
  intros; simpl;
    repeat (match goal with | [H:context[_=_] |- _] => rewrite H end);
    auto).