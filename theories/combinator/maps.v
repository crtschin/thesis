Require Import Setoid.
Require Import Relations.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Sets.Multiset.
Require Import Setoid.

Local Open Scope program_scope.
Local Open Scope type_scope.

Module Mset.
  Definition type (t : Type) := (multiset t * list t).
  Definition mset_eq
    : forall A,
      type A -> type A -> Prop
    := fun A m1 m2 => meq (fst m1) (fst m2).
End Mset.
Definition mset := Mset.type.
Definition mset_eq A := Mset.mset_eq A.

Lemma mset_eq_refl :
  forall A (x : mset A),
    mset_eq _ x x.
Proof with eauto.
  intros.
  unfold mset_eq; unfold Mset.mset_eq...
  apply meq_refl.
Qed.

Lemma mset_eq_symm :
  forall A (x y : mset A),
    mset_eq _ x y -> mset_eq _ y x.
Proof with eauto.
  intros.
  unfold mset_eq in *; unfold Mset.mset_eq in *...
  apply meq_sym...
Qed.

Lemma mset_eq_trans :
  forall A (x y z  : mset A),
    mset_eq _ x y -> mset_eq _ y z -> mset_eq _ x z.
Proof with eauto.
  intros.
  unfold mset_eq in *; unfold Mset.mset_eq in *...
  eapply meq_trans...
Qed.

Add Parametric Relation (A : Type)
  : (multiset A) (@meq A)
  reflexivity proved by (@meq_refl A)
  symmetry proved by (@meq_sym A)
  transitivity proved by (@meq_trans A)
  as multiset_rel.

Add Parametric Morphism A : (@munion A)
  with signature (@meq A) ==> (@meq A) ==> (@meq A) as union_mor.
Proof with simpl; eauto.
  intros.
  now apply meq_congr.
Qed.

Add Parametric Relation (A : Type)
  : (mset A) (mset_eq A)
  reflexivity proved by (mset_eq_refl A)
  symmetry proved by (mset_eq_symm A)
  transitivity proved by (mset_eq_trans A)
  as mset_rel.

Record mset_eq_dec A :=
  mk_eq_dec
  {eqdec :> forall (x y:mset A), {mset_eq _ x y}+{~mset_eq _ x y}}.
