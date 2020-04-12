Section demo.

Inductive bool :=
  | false : bool
  | true : bool.
Check bool.
Inductive nat :=
  | O : nat
  | S : nat -> nat.
Check nat.

Lemma nat_discr :
  forall n, O <> S n.
Proof.
  intros n.
  discriminate.
Qed.

Variable (x : nat).
Check (O <> S x).
Check (O <> O).

Lemma O_refl_f : O <> O.
Proof.
  unfold not.
  intros H.
Abort.

Definition succ (n : nat) : nat :=
  S n.

Definition pred1 (n : nat) :=
  match n return
      (match n with
      | O => unit
      | S _ => nat end) with
  | O => tt
  | S n => n
  end.
Check pred1.

Definition pred2 (n : nat) : n <> O -> nat.
Proof.
  intros H.
  destruct n.
  - contradiction H. reflexivity.
  - apply n.
Defined.
Check pred2.
Print pred2.

Require Import Equations.Equations.

Equations pred (n : nat) (pf : n <> O): nat :=
pred O pf with pf eq_refl := {};
pred (S n) pf := n.
