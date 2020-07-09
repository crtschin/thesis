Require Import Logic.FunctionalExtensionality.

Create HintDb ad.

Ltac quick := simpl in *; intros; (eauto with ad).
Ltac use H := (apply H || rewrite H); clear H.
Ltac splits := repeat try split.
Ltac rewrite_c H := try (rewrite H); clear H.
Ltac apply_c H := try (apply H); clear H.
Ltac rewrites := (
  intros; simpl;
    repeat (match goal with | [H:context[_=_] |- _] => erewrite H end);
    auto).
Ltac simp f := (autorewrite with f).