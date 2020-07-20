Require Import FunctionalExtensionality.
Require Import Lists.List.
Import ListNotations.
Require Import Reals.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Program.
From Equations Require Import Equations.
Require Import Equations.Prop.Tactics.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import Coquelicot.Coquelicot.

Require Import AD.tactics.
Require Import AD.types.
Require Import AD.stlc.
Require Import AD.combinator.
Require Import AD.denotation.
Require Import AD.translation.
Require Import AD.linearity.
Local Open Scope program_scope.

(*
Definition cardinalities := list nat.
Fixpoint arguments (cs : cardinalities) : Ctx :=
  match cs with
  | nil => nil
  | n :: cs => ℝ^n :: arguments cs
  end.

Lemma Dt_repeat_R_id : forall n,
  (translate_context (repeat ℝ n), translate_context (repeat ℝ n))
    = Dt (translate_context (repeat ℝ n)).
Proof.
  intros. induction n; simpl.
  - now reflexivity.
  - now rewrite <- IHn.
Qed.

Lemma Dt_args_id : forall cs,
  (translate_context (arguments cs), translate_context (arguments cs))
    = Dt (translate_context (arguments cs)).
Proof.
  intros. induction cs; simpl.
  - now reflexivity.
  - now rewrite <- IHcs.
Qed.

(* Compute (Dt (translate_context (arguments [1;2;3;4]))). *)

Equations? Dargs {cs} n (f : R -> ⟦ translate_context (arguments cs) ⟧ₜ) :
  R -> ⟦ fst (Dt (translate_context (arguments cs))) × snd (Dt (ℝ^ n)) ⟧ₜ :=
Dargs n f r with f_equal fst (Dt_args_id cs) := {
  | pf := (_, Vbuild (fun _ _ => 1%R))
}. apply (f r).
Defined.

Equations? D n (f : R -> ⟦ translate_context (repeat ℝ n) ⟧ₜ) :
  R -> ⟦ fst (Dt (translate_context (repeat ℝ n))) × snd (Dt ℝ) ⟧ₜ :=
D n f r with f_equal fst (Dt_repeat_R_id n) := {
  | pf := (_, 1)
}. apply (f r).
Defined.
*)
Fixpoint fin_to_nat {n} (i : Fin.t n) : nat :=
  match i with
  | Fin.F1 n' => 0
  | Fin.FS n' i' => S (fin_to_nat i')
  end.

Fixpoint nat_to_fin n : Fin.t (S n) :=
  match n with
  | 0 => Fin.F1
  | S n' => Fin.FS (nat_to_fin n')
  end.

(* transform a function (R^n -> R) to (R -> R) by inputting a
  one-hot encoded vector at position i *)
Equations multi_nth {n} (i : Fin.t n) : (R^n -> R) -> R -> R :=
multi_nth i f r :=
  f (Vmap (Rmult r) (vector_one_hot (fin_to_nat i) n)).

Equations multi_Deriv {n} (i : Fin.t n) : (R^n -> R) -> R^n -> R :=
multi_Deriv i f r => Derive (multi_nth i f) (vector_nth i r).

(* Pad the output of multi_Deriv into a R^n *)
Equations multi_Deriv_pad {n} (i : Fin.t n) : (R^n -> R) -> R^n -> R^n :=
multi_Deriv_pad i f r :=
  Vmap (Rmult (multi_Deriv i f r)) (vector_one_hot (fin_to_nat i) n)
.

(* Give all partial derivatives of the given function with respect to each of
    the input variables
*)
Equations multi_partials {n} : (R^n -> R) -> R^n -> R^n :=
multi_partials f r :=
  Vbuild (fun i pf =>
    Derive (fun x => f (vector_mul (vector_one_hot i n) r))
      (Vnth r pf)).

(* Give the derivatives with respect to each of the output variables
*)
Equations multi_Derive_o {n} : (R -> R^n) -> R -> R^n :=
multi_Derive_o f r :=
  Vbuild (fun i pf => Derive (fun x => Vnth (f x) pf) r).

Equations gradient {n} : (R^n -> R) -> R^n -> R :=
gradient f r := Vfold_left Rplus 0 (multi_partials f r).

Equations gradient_o {n} : (R -> R^n) -> R -> R :=
gradient_o f r := Vfold_left Rplus 0 (multi_Derive_o f r).

Derive Signature for vector.

Equations context_eq n :
  ⟦ translate_context (repeat ℝ (S n)) ⟧ₜ -> R^ (S n) :=
context_eq 0 (r, tt) := Vcons r Vnil;
context_eq (S n') (r, xs') := Vcons r (context_eq n' xs').

Equations context_eq' n :
  R^ (S n) -> ⟦ translate_context (repeat ℝ (S n)) ⟧ₜ :=
context_eq' 0 (Vcons r Vnil) := (r, tt);
context_eq' (S n') (Vcons r xs') := (r, (context_eq' n' xs')).

Definition Rel_prod_fst {σ ρ} : R * ⟦ snd (Dt (σ × ρ)) ⟧ₛₜ -> R * ⟦ snd (Dt σ) ⟧ₛₜ :=
  fun x => (fst x, fst (snd x)).

Definition Rel_prod_snd {σ ρ} : R * ⟦ snd (Dt (σ × ρ)) ⟧ₛₜ -> R * ⟦ snd (Dt ρ) ⟧ₛₜ :=
  fun x => (fst x, snd (snd x)).

Lemma Vmap2_plus_build_0_r: forall n v,
  Vmap2 Rplus v (Vbuild (fun (i : nat) (_ : (i < n)%nat) => 0)) = v.
Proof with (simpl in *; eauto).
  intros.
  dependent induction n...
  { now dependent destruction v. }
  { rewrite Vbuild_head; rewrite Rplus_0_r.
    rewrite Vbuild_tail; rewrite IHn.
    dependent destruction v... }
Qed.

Lemma Vmap2_plus_build_0_l: forall n v,
  Vmap2 Rplus (Vbuild (fun (i : nat) (_ : (i < n)%nat) => 0)) v = v.
Proof with (simpl in *; eauto).
  intros.
  dependent induction n...
  { now dependent destruction v. }
  { rewrite Vbuild_head; rewrite Rplus_0_l.
    rewrite Vbuild_tail; rewrite IHn.
    dependent destruction v... }
Qed.

(* TODO: Need to work out both the correct definitions of
    linearity and denotation of ⊗ before proceeding.

  Note: Might be slightly more appropriate to call it heterogeneous linearity,
    as it requires linearity with respect to ⟦O⟧ and ⟦plus⟧ which are both
    functions defined on multiple datatypes (products/sums/functions/reals)
*)
Equations Rel τ : (R -> ⟦ τ ⟧ₜ)
  -> (R -> ⟦ fst (Dt τ) ⟧ₛₜ) -> (R * ⟦ snd (Dt τ) ⟧ₛₜ -> R) -> Prop :=
Rel Unit f g h := f = g /\ h = fun x => 0;
Rel ℝ f g h :=
  (forall (x : R), ex_derive f x) /\
  f = g /\ h = fun x => Derive f (fst x) * snd x;
Rel (ℝ^n) f g h :=
  (forall i pf (x : R),
    ex_derive (fun x => @Vnth R n (f x) i pf) x) /\
  f = g /\ h = fun x => dot_product (multi_Derive_o f (fst x)) (snd x);
Rel (σ → ρ) f g h :=
  second_linear h /\
  forall g1 g2 g3,
  forall (rσ : Rel σ g1 g2 g3),
    Rel ρ (fun x => f x (g1 x))
      (fun x => fst (g x (g2 x)))
      (fun x => h (fst x, (g2 (fst x), snd x) :: nil)
        + g3 (fst x, snd (g (fst x) (g2 (fst x))) (snd x)));
Rel (σ × ρ) f g h :=
  exists f1 f2 f3 g1 g2 g3,
  exists (s1 : Rel σ f1 f2 f3) (s2 : Rel ρ g1 g2 g3),
    (f = fun r => (f1 r, g1 r)) /\
    (g = fun r => (f2 r, g2 r)) /\
    (h = fun r => (f3 (Rel_prod_fst r)) + (g3 (Rel_prod_snd r))).

Lemma Vbuild_cons : forall A n (f : forall i : nat, (i < S n)%nat -> A),
  Vcons (f 0%nat (Nat.lt_0_succ n))
    (Vbuild
      (fun (i : nat) (pf : (i < n)%nat) =>
        f (S i) (lt_n_S pf))) =
  Vbuild (fun (i : nat) (pf : (i < S n)%nat) => f i pf).
Proof with (simpl in *; eauto).
  intros.
  remember (Vbuild (fun (i : nat) (pf : (i < S n)%nat) => f i pf)).
  eassert (t = Vcons (Vhead t) (Vtail t)).
  { dependent destruction t; simpl; reflexivity. }
  rewrite Heqt.
  rewrite H in Heqt.
  rewrite <- Heqt.
  apply Vcons_eq. split.
  { rewrite H; rewrite Heqt...
    rewrite Vbuild_head... }
  { rewrite H; rewrite Heqt...
    rewrite Vbuild_tail... }
Qed.

Lemma Vmap2_build :
  forall A n (f : A -> A -> A) (g1 g2 : forall i, (i < n)%nat -> A),
    Vmap2 f (Vbuild g1) (Vbuild g2)
      = Vbuild (fun i pf => f (g1 i pf) (g2 i pf)).
Proof with (simpl in *; eauto).
  intros.
  induction n...
  repeat rewrite Vbuild_head;
    repeat rewrite Vbuild_tail.
  rewrite IHn...
  pose proof (Vbuild_cons A n
    (fun i pf => f (g1 i pf) (g2 i pf)))...
Qed.

Lemma Rel_eq : forall τ f f' g g' h h',
  f = f' -> g = g' -> h = h' -> Rel τ f g h = Rel τ f' g' h'.
Proof. intros; now subst. Qed.

Lemma Rel_linear : forall τ f g h,
  Rel τ f g h -> second_linear h.
Proof with simpl in *; eauto.
  intros.
  induction τ; simpl in *; simp Rel in *.
  { splits; intros; fold Dt denote_st in *.
    { destruct H as [eq1 [eq2 eq3]]. subst...
      unfold dot_product, vector_mul; simp multi_Derive_o.
      rewrite Vmap2_build.
      eassert (H: (fun (i : nat) (pf : (i < n)%nat) =>
        Derive (fun x : R => Vnth (g x) pf) r * 0) = _).
      { extensionality i. extensionality pf.
        rewrite Rmult_0_r... reflexivity. }
      use H. clear eq1 r g.
      induction n...
      remember (Vbuild (fun (i : nat) (_ : (i < S n)%nat) => 0)).
      eassert (t = Vcons (Vhead t) (Vtail t)).
      { dependent destruction t... }
      use H; use Heqt.
      rewrite Vbuild_tail; rewrite Vbuild_head...
      rewrite Rplus_0_r... }
    { destruct H as [eq1 [eq2 eq3]]. subst...
      unfold dot_product, vector_mul.
      simp multi_Derive_o.
      clear eq1.
      (* TODO:
        Should be true by the distributive
          law of multiiplication. *)
      induction n...
      { rewrite Rplus_0_r... }
      { rewrite 3 Rplus_0_l.
        remember (Vbuild
           (fun (i : nat) (pf : (i < S n)%nat) =>
            Derive (fun x : R => Vnth (g x) pf) r)).
        eassert (t = Vcons (Vhead t) (Vtail t)).
        { dependent destruction t... }
        rewrite Rmult_comm; rewrite Rmult_plus_distr_r.
        rewrite Rmult_comm; rewrite (@Rmult_comm (Vhead b)).
        admit. } }
    (* { exists (⟦target.t_O (snd (Dt (ℝ^n)))⟧ₜₒ tt);
        exists (dot_product (multi_Derive_o g r)
          (Vbuild (fun (i : nat) (_ : (i < n)%nat) => 0))).
      intros.
      unfold linear in H0; fold denote_st in *.
      destruct H0 as [eq1 eq2].
      rewrite eq1. destruct H as [ex [eq1' eq2']]. subst...  } *)  }
  { splits; intros; fold Dt denote_st in *.
    { destruct H as [eq1 [eq2 eq3]].
      subst... rewrite Rmult_0_r... }
    { destruct H as [eq1 [eq2 eq3]].
      subst...
      rewrite Rmult_comm.
      rewrite Rmult_plus_distr_r.
      rewrite Rmult_comm.
      rewrite (@Rmult_comm b)... }
    (* { exists (⟦target.t_O (snd (Dt (ℝ)))⟧ₜₒ tt);
        exists 0; intros.
      intros.
      unfold linear in H0; fold denote_st in *.
      destruct H0 as [eq1 eq2].
      rewrite eq1. destruct H as [ex [eq1' eq2']]. subst...
      rewrite Rmult_0_r... } *) }
  { splits; intros; fold Dt denote_st in *.
    { destruct H as [eq1 eq2].
      subst... }
    { destruct H as [eq1 eq2].
      subst... rewrite Rplus_0_r... }
    (* { exists (⟦target.t_O (snd (Dt (Unit)))⟧ₜₒ tt);
        exists 0; intros.
      intros.
      unfold linear in H0; fold denote_st in *.
      destruct H0 as [eq1 eq2].
      rewrite eq1. destruct H as [eq1' eq2']. subst... } *) }
  { splits; intros; fold Dt denote_st in *.
    { destruct H; unfold second_linear in H...
      destruct H as [eq1 eq2]... }
    { destruct H; unfold second_linear in H...
      destruct H as [eq1 eq2];
        fold denote_st in *.
      rewrite eq2... }
    (* { exists (⟦target.t_O (snd (Dt (τ1 → τ2)))⟧ₜₒ tt);
        exists 0; intros.
      unfold linear in H0; fold denote_st in *.
      destruct H0 as [eq1 eq2]; rewrite eq1.
      destruct H as [[eq1' [eq2' eqf]] H].
      subst... } *) }
  { splits; intros; fold Dt denote_st in *.
    { destruct H as [f1 [f2 [f3 [g1 [g2 [g3
        [R1 [R2 [eq1 [eq2 eq3]]]]]]]]]].
      subst. unfold Rel_prod_fst, Rel_prod_snd...
      edestruct IHτ1 as [eq1 _]...
      edestruct IHτ2 as [eq2 _]...
      erewrite eq1... erewrite eq2...
      rewrite Rplus_0_r... }
    { destruct H as [f1 [f2 [f3 [g1 [g2 [g3
        [R1 [R2 [eq1 [eq2 eq3]]]]]]]]]].
      subst. unfold Rel_prod_fst, Rel_prod_snd...
      edestruct IHτ1 as [eq11 eq12]...
      edestruct IHτ2 as [eq21 eq22]...
      fold denote_st in *.
      rewrite eq12; rewrite eq22.
      rewrite 2 Rplus_assoc.
      rewrite (@Rplus_comm (f3 (r, fst b))).
      rewrite Rplus_assoc.
      rewrite (@Rplus_comm (g3 (r, snd b)))... }
    (* { exists (⟦target.t_O (snd (Dt (τ1 × τ2)))⟧ₜₒ tt);
        exists 0; intros.
      unfold linear in H0; fold denote_st in *.
      destruct H0 as [eq1 eq2]; rewrite eq1.
      destruct H as [f1 [f2 [f3 [g1 [g2 [g3
        [R1 [R2 [eq1' [eq2' eq3']]]]]]]]]].
      subst...
      pose proof (IHτ1 _ _ _ R1) as IHτ1; destruct IHτ1 as [eq11 [eq12 eq1f]].
      pose proof (IHτ2 _ _ _ R2) as IHτ2; destruct IHτ2 as [eq21 [eq22 eq2f]].
      fold denote_st in *.
      unfold Rel_prod_fst, Rel_prod_snd...
      rewrite eq11; rewrite eq21. rewrite Rplus_0_r... } *) }
Admitted.

Lemma huh : forall A B (c : comb A B) (d : ⟦ fst (Dt A) ⟧ₛₜ),
  ⟦ snd (Dcomb c) ⟧ₜₒ (d, denote_O (snd (Dt B))) =
    ⟦ target.t_O (snd (Dt A)) ⟧ₜₒ ().
Proof with simpl in *; eauto.
  intros.
  dependent induction c; try solve [simpl in *; eauto].
  { induction A... destruct d. rewrites. }
  { rewrites. rewrite <- denote_O_eq. rewrite IHc1... }
  { rewrites. }
  { rewrite denote_O_eq... }
  { rewrite denote_O_eq... }
  { simpl... rewrite <- denote_plus_eq.
    rewrite denote_plus_O_r. rewrite denote_O_eq... }
  { (* TODO:
      Weird, don't think this is true,
        nor is it very clear what's needed to make
        this true *)
    simpl. destruct d as [p d]...
    remember (p d) as p'.
    clear p Heqp'. destruct p' as [d' f]...
    apply injective_projections...
  all: rewrite denote_O_eq...
  all: admit. }
  { simpl... fold Dt.
    specialize IHc with (d, denote_O (fst (Dt B))).
    rewrite IHc... }
Admitted.

Lemma Rel_substitute :
  forall τ σ,
  forall (c : comb τ σ),
  forall (f : R -> ⟦ τ ⟧ₜ),
  forall (g : R -> ⟦ fst (Dt τ) ⟧ₛₜ),
  forall (h : R * ⟦ snd (Dt τ) ⟧ₛₜ -> R),
  Rel τ f g h ->
  Rel σ (fun x => ⟦c⟧ₒ (f x))
    (fun x => ⟦fst (Dcomb (c))⟧ₜₒ (g x))
    (fun x => h (fst x, (⟦snd (Dcomb (c))⟧ₜₒ (g (fst x), snd x)))).
Proof with (simpl in *; try eauto).
  intros.
  dependent induction c.
  { simpl.
    erewrite Rel_eq...
    extensionality x. destruct x... }
  { simpl.
    erewrite Rel_eq... }
  { simpl. simp Rel in *.
    destruct H as [f1 [f2 [f3 [g1 [g2 [g3
      [R1 [R2 [eq1 [eq2 eq3]]]]]]]]]].
    pose proof (IHc1 _ _ _ R1) as IHc1.
    pose proof (IHc2 _ _ _ R2) as IHc2.
    exists (⟦c1⟧ₒ ∘ f1).
    exists (⟦fst (Dcomb c1)⟧ₜₒ ∘ f2)...
    exists (fun x => f3 (fst x, ⟦ snd (Dcomb c1) ⟧ₜₒ (f2 (fst x), snd x))).
    exists (⟦c2⟧ₒ ∘ g1).
    exists (⟦fst (Dcomb c2)⟧ₜₒ ∘ g2)...
    exists (fun x => g3 (fst x, ⟦ snd (Dcomb c2) ⟧ₜₒ (g2 (fst x), snd x))).
    exists IHc1; exists IHc2.
    unfold compose; subst.
    unfold Rel_prod_fst, Rel_prod_snd... }
  { simp Rel. split...
    apply Rel_linear in H.
    destruct H as [eq1 eq2].
    extensionality x; destruct x; destruct u... }
  { simp Rel in *...
    destruct H as [f1 [f2 [f3 [g1 [g2 [g3
      [R1 [R2 [eq1 [eq2 eq3]]]]]]]]]].
    subst.
    erewrite Rel_eq...
    { unfold Rel_prod_fst, Rel_prod_snd...
      extensionality x; subst.
      destruct x...
      apply Rel_linear in R2;
        destruct R2 as [eq1 eq2].
      rewrite eq1. rewrite Rplus_0_r... } }
  { simp Rel in *...
    destruct H as [f1 [f2 [f3 [g1 [g2 [g3
      [R1 [R2 [eq1 [eq2 eq3]]]]]]]]]].
    subst.
    erewrite Rel_eq...
    { unfold Rel_prod_fst, Rel_prod_snd...
      extensionality x; subst.
      destruct x...
      apply Rel_linear in R1;
        destruct R1 as [eq1 eq2].
      rewrite eq1. rewrite Rplus_0_l... } }
  { simpl; simp Rel in *.
    exists f; exists g; exists h.
    exists f; exists g; exists h.
    exists H; exists H.
    repeat split...
    extensionality x; destruct x as [r [a1 a2]]...
    unfold Rel_prod_fst, Rel_prod_snd...
    apply Rel_linear in H;
      destruct H as [eq1 [eq2 eqf]].
    rewrite eq2... }
  { simp Rel in H.
    destruct H as [f1 [f2 [f3 [g1 [g2 [g3
      [R1 [R2 [eq1 [eq2 eq3]]]]]]]]]].
    subst.
    simp Rel in *.
    destruct R1 as [lin R1].
    pose proof (R1 _ _ _ R2) as R1... }
  { simp Rel in *. intros.
    split.
    { unfold second_linear; fold denote_st in *.
      simpl fst; simpl (snd (_, _)).
      repeat split.
      { intros.
        apply Rel_linear in H.
        destruct H as [eq1 [eq2 eqf]]; fold denote_st in *.
        pose proof (eqf r (fun _ => ⟦ snd (Dcomb (curry c)) ⟧ₜₒ (g r, []))).
        specialize eq1 with r.
        destruct H as [q [w e]].
        apply f_equal. apply injective_projections...
        remember (g r). fold Dt in *.
        pose proof huh as H'.
        pose proof (H' (A × B) C c
          (d, denote_O (fst (Dt B)))) as H'...
        rewrite H'... }
      { (* TODO:
          Weird, might be true,
            fold_left plus (a ++ b) 0 =
            fold_left plus a 0 + fold_left plus b 0

          But need to show this is preserved by h
        *)
        fold denote_st;
          simpl fst; simpl (snd (_, _)); intros.
        simpl...
        fold Dt.
        admit. } }
    { intros...
      erewrite Rel_eq. apply IHc.
      simp Rel.
      exists f; exists g; exists h.
      exists g1; exists g2; exists g3.
      exists H; exists rσ.
      repeat split; reflexivity.
      all: simpl; try reflexivity.
      extensionality x; destruct x...
      unfold Rel_prod_fst, Rel_prod_snd...
      fold Dt.
      repeat rewrite denote_plus_O_r... } }
  { simpl. simp Rel in H.
    destruct H as [f1 [f2 [f3 [g1 [g2 [g3
      [R1 [R2 [eq1 [eq2 eq3]]]]]]]]]].
    simp Rel in *.
    destruct R1 as [r1eq1 [r1eq2 r1eq3]].
    destruct R2 as [r2eq1 [r2eq2 r2eq3]].
    subst.
    repeat split; simpl in *; intros...
    { pose proof r1eq1 x as r1eq1.
      pose proof r2eq1 x as r2eq1.
      apply (ex_derive_plus _ _ _ r1eq1 r2eq1). }
    { extensionality x. rewrite Derive_plus...
      rewrite Rmult_plus_distr_r... } }
  { simpl. simp Rel in *.
    destruct H as [eq1 eq2].
    subst. repeat split...
    apply ex_derive_const.
    extensionality x.
    rewrite Derive_const. rewrite Rmult_0_l... }
  { simp Rel in *...
    destruct H as [f1 [f2 [f3 [g1 [g2 [g3
      [R1 [R2 [eq1 [eq2 eq3]]]]]]]]]].
    simp Rel in *...
    destruct R1 as [r1eq1 [r1eq2 r1eq3]].
    destruct R2 as [r2eq1 [r2eq2 r2eq3]].
    subst.
    repeat split...
    { intros.
      induction n...
      { inversion pf. }
      { (* TODO:
          Should follow from induction hypothesis
        *)
        pose proof (r1eq1 i pf x) as r1eq1.
        pose proof (r2eq1 i pf x) as r2eq1.
        pose proof (@ex_derive_plus _ _ _ _ _ r1eq1 r2eq1).
        destruct i...
      all: admit. } }
    { extensionality x.
      unfold dot_product, vector_mul.
      simp multi_Derive_o.
      destruct x...
      induction n...
      { rewrite Rplus_0_l... }
      { repeat rewrite Rplus_0_l.
        repeat rewrite Vbuild_head;
          repeat rewrite Vbuild_tail...
        admit. } } }
  { simp Rel in *.
    destruct H as [eq1 eq2]...
    unfold dot_product, vector_mul.
    subst.
    repeat split...
    { intros. apply ex_derive_const. }
    { extensionality x.
      simp multi_Derive_o. destruct x...
      eassert (H': (fun (i : nat) (pf : (i < n)%nat) =>
          Derive (fun _ : R => Vnth a pf) r) = _).
      { extensionality i. extensionality pf.
        rewrite Derive_const. reflexivity. }
      use H'.
      clear a g.
      induction n...
      rewrite Vbuild_head; rewrite Vbuild_tail.
      rewrite Rplus_0_l; rewrite Rmult_0_l.
      erewrite <- IHn... } }
Admitted.

Fixpoint D n
  : (R -> ⟦ translate_context (repeat ℝ n) ⟧ₜ) ->
    ((R -> ⟦ fst (Dt (translate_context (repeat Real n))) ⟧ₛₜ) *
    (R -> ⟦ snd (Dt (translate_context (repeat Real n))) ⟧ₛₜ)) :=
  match n with
  | 0%nat => fun f => (f, f)
  | (Datatypes.S n) => fun f =>
      (fun r => (fst (f r), fst (D n (snd ∘ f)) r),
      fun r => (Derive (fun x => fst (f x)) r, snd (D n (snd ∘ f)) r))
  end.

Fixpoint denote_untranslate n
  : ⟦ snd (Dt (translate_context (repeat ℝ n))) ⟧ₛₜ -> R^ n :=
  match n with
  | 0%nat => fun v => Vnil
  | S n' => fun v => Vcons (fst v) (denote_untranslate n' (snd v))
  end.

Lemma fundamental_property :
  forall n (c : comb (translate_context (repeat ℝ (S n))) (ℝ))
    (f : R -> ⟦ translate_context (repeat ℝ (S n)) ⟧ₜ),
  Rel ℝ (⟦ c ⟧ₒ ∘ f)
    (fun x => ⟦fst (Dcomb c)⟧ₜₒ (fst (D _ f) x))
    (fun x => Vfold_left Rplus 0
      (denote_untranslate _ (⟦snd (Dcomb c)⟧ₜₒ (fst (D _ f) (fst x), 1)))).
Proof with simpl in *; eauto.
  intros.
  unfold compose.
  (* apply Rel_substitute. *)
Admitted.

Lemma Rel_correctness_R :
  forall n (c : comb (translate_context (repeat ℝ (S n))) (ℝ))
    (f : R -> ⟦ translate_context (repeat ℝ (S n)) ⟧ₜ),
  Rel ℝ (⟦ c ⟧ₒ ∘ f)
    (fun x => ⟦fst (Dcomb c)⟧ₜₒ (fst (D _ f) x))
    (fun x => Vfold_left Rplus 0
      (denote_untranslate _ (⟦snd (Dcomb c)⟧ₜₒ (fst (D _ f) (fst x), 1)))) ->
  (fun x => Vfold_left Rplus 0
    (denote_untranslate (S n)
    (⟦ snd (Dcomb c) ⟧ₜₒ (fst (D (S n) f) (fst x), 1)))) =
  (fun x => Derive (fun x0 : R => ⟦ c ⟧ₒ (f x0)) (fst x) * snd x).
Proof with (simpl in *; eauto).
  intros.
  simp Rel in H. unfold compose in *.
  destruct H as [ex [eq1 eq2]].
  extensionality x...
  apply equal_f with x in eq2...
  (* apply equal_f with x in eq1...
  apply equal_f with (x, 1) in eq2...
  rewrite Rplus_0_l in eq2. unfold compose in *.
  rewrite Rmult_1_r in eq2. *)
Qed.

Theorem reverse_correctness:
  forall n (c : comb (translate_context (repeat ℝ (S n))) (ℝ))
    (f : R -> ⟦ translate_context (repeat ℝ (S n)) ⟧ₜ),
  (fun x => Vfold_left Rplus 0
    (denote_untranslate (S n)
    (⟦ snd (Dcomb c) ⟧ₜₒ (fst (D (S n) f) (fst x), 1)))) =
  (fun x => Derive (fun x0 : R => ⟦ c ⟧ₒ (f x0)) (fst x) * snd x).
  (* denote_untranslate (S n) ∘
    (fun x => ⟦ snd (Dcomb c) ⟧ₜₒ (fst (D _ f) x, 1))
  = fun x => multi_partials
    (⟦ c ⟧ₒ ∘ context_eq' n) (context_eq n (f x)). *)
Proof.
  intros.
  apply Rel_correctness_R.
  apply fundamental_property.
Qed.
