Require Import AD.types.
Set Universe Polymorphism.
Record LinImpl (t1 t2 : Type) : Type := {
  func :> t1 -> t2;
  (* O : forall {t : Type}, t;
  adds : forall {t : Type}, t -> t -> t;
  linO : func O = O;
  linadds : forall d1 d2,
    adds (func d1) (func d2) = func (adds d1 d2); *)
}.
Notation "A ⊸ B" := (LinImpl A B) (right associativity, at level 90).
Check LinImpl.