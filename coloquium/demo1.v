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

Require Import List.
Local Open Scope list_scope.

Fail Definition hd {A : Set} (l : list A) : A :=
  match l with
  | h :: t => h
  | nil => whoknows
  end.

Inductive li_list {A : Set} : nat -> Set :=
  | li_nil : li_list O
  | li_cons : forall n, A -> li_list n -> li_list (S n).

Definition hd' {A : Set} {n} (l : li_list n) :=
  match l in (li_list n) return
    (match n with
    | O => unit
    | S _ => A
    end) with
  | li_nil => tt
  | li_cons _ h t => h
  end.
Check hd'.

Definition hd {A : Set} {n} (l : li_list (S n)) : A := hd' l.
Check hd.

Reset hd.
Definition hd {A : Set} {n} (l : li_list (S n)) : A :=
  match l with
  | li_cons _ h t => h
  end.

Definition pred' (n : nat) :=
  match n return
      (match n with
      | O => unit
      | S _ => nat end) with
  | O => tt
  | S n => n
  end.
Check pred'.

Definition pred'' (n : nat) : n <> O -> nat.
Proof.
  intros H.
  destruct n.
  - contradiction H. reflexivity.
  - apply n.
Defined.
Check pred''.

Require Import Equations.Equations.

Equations pred (n : nat) (pf : n <> O): nat :=
pred O pf with pf eq_refl := {};
pred (S n) pf := n.
