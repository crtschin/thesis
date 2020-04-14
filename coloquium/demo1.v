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
Reset x.

Lemma O_refl_f : O <> O.
Proof.
  unfold not.
  intros H.
Abort.

Fixpoint times_two (n : nat) : nat :=
  match n with
  | O => O
  | S n => S (S (times_two n))
  end.

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

Require Import Equations.Equations.

Equations pred (n : nat) (pf : n <> O): nat :=
pred O pf with pf eq_refl := {};
pred (S n) pf := n.

(* Require Import Datatypes.
Require Import Coq.micromega.Lia.

Inductive ilist (A : Type): nat -> Type :=
  | ilist_nil : ilist A 0
  | ilist_cons : forall (a : A) (n : nat), ilist A n -> ilist A (S n)
.

Definition idx A (n m: nat) (l : ilist A m) : (n < m) -> A.
  intros H.
  destruct n; destruct l; try lia; assumption.
Qed. *)
