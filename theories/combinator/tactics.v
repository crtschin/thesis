Require Import Logic.FunctionalExtensionality.

Ltac quick := simpl in *; intros; (eauto with ad).
Ltac splits := repeat try split.
Ltac use H := (apply H || rewrite H); clear H.
Ltac rewrites := (
  intros; simpl;
    repeat (match goal with | [H:context[_=_] |- _] => erewrite H end);
    auto).