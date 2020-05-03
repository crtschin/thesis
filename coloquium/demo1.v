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
Check (forall n, O <> S n).
Check nat_discr.

Lemma O_refl_f : O <> O.
Proof.
Abort.
Check (O <> O).
(* Check O_refl_f. *)

(*
Definition hd {A : Set} (l : list A) : A :=
  match l with
  | h :: t => h
  | nil => whoknows
  end.
*)

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

Reset hd.
Require Import Equations.Equations.

Equations hd {A : Set} {n} (l : @li_list A n) (pf : n <> O) : A :=
hd li_nil pf with pf eq_refl := {};
hd (li_cons a l) pf := a.
Check hd.
