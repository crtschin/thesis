Require Import Lists.List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Arith_base.
Require Import Coquelicot.Derive.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Equations.Equations.
Import EqNotations.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import micromega.Lia.

From Equations Require Import Equations.
From AD Require Import Tactics.
From AD Require Import DepList.
From AD Require Import Simply.
From AD Require Direct.

Local Open Scope program_scope.
Local Open Scope type_scope.

(* Continuation *)

Fixpoint Dt_c (n : nat) (σ : ty) : ty :=
  match σ with
  | Real => Real × (Real → Array n Real)
  (* | Nat => Nat *)
  | Array m τ => Array m (Dt_c n τ)
  | τ1 × τ2 => (Dt_c n τ1 × Dt_c n τ2)
  | τ1 → τ2 => (Dt_c n τ1 → Dt_c n τ2)
  | τ1 <+> τ2 => (Dt_c n τ1 <+> Dt_c n τ2)
  end.

Definition Dctx_c n Γ : Ctx := map (Dt_c n) Γ.

Fixpoint Dv_c n {Γ τ} (v: τ ∈ Γ) : (Dt_c n τ) ∈ (map (Dt_c n) Γ) :=
  match v with
  | Top Γ τ => Top (map (Dt_c n) Γ) (Dt_c n τ)
  | Pop Γ τ σ t =>
      Pop (map (Dt_c n) Γ) (Dt_c n τ) (Dt_c n σ) (Dv_c n t)
  end.

Equations Dtm_c n {Γ τ} : tm Γ τ -> tm (map (Dt_c n) Γ) (Dt_c n τ) :=
(* STLC *)
Dtm_c n (Γ:=Γ) (τ:=τ) (var Γ τ v) := var _ _ (Dv_c n v);
Dtm_c n (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) := app _ _ _ (Dtm_c n t1) (Dtm_c n t2);
Dtm_c n (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) := abs _ _ _ (Dtm_c n f);
(* Arrays *)
Dtm_c n (Γ:=Γ) (τ:=τ) (build Γ τ m ta) =>
  build _ _ _ (Dtm_c n ∘ ta);
Dtm_c n (Γ:=Γ) (τ:=τ) (get Γ ti ta) => get _ ti (Dtm_c n ta);
(* Reals *)
Dtm_c n (Γ:=Γ) (τ:=τ) (rval Γ r) :=
  tuple _ (rval _ r) (abs _ _ _ (build _ _ _ (const (rval _ 0))));
Dtm_c n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) with Dtm_c n t1 := {
  Dtm_c n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 with Dtm_c n t2 := {
    Dtm_c n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 d2 :=
      tuple _
        (add _ (first _ d1) (first _ d2))
        (abs _ _ _
          (vector_add
            ((app _ _ _ (shift (second _ d1)) (var _ _ (Top _ _))))
            ((app _ _ _ (shift (second _ d2)) (var _ _ (Top _ _))))))
  }
};
Dtm_c n (Γ:=Γ) (τ:=τ) (mul Γ t1 t2) with Dtm_c n t1 := {
  Dtm_c n (Γ:=Γ) (τ:=τ) (mul Γ t1 t2) d1 with Dtm_c n t2 := {
    Dtm_c n (Γ:=Γ) (τ:=τ) (mul Γ t1 t2) d1 d2 :=
      tuple _
        (mul _ (first _ d1) (first _ d2))
        (abs _ _ _
          (vector_add
            ((app _ _ _ (shift (second _ d1))
              (mul _ (shift (first _ d2)) (var _ _ (Top _ _)))))
            ((app _ _ _ (shift (second _ d2))
              (mul _ (shift (first _ d1)) (var _ _ (Top _ _)))))))
  }
};
(* Products *)
Dtm_c n (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) := tuple _ (Dtm_c n t1) (Dtm_c n t2);
Dtm_c n (Γ:=Γ) (τ:=τ) (first Γ p) := first _ (Dtm_c n p);
Dtm_c n (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm_c n p);
Dtm_c n (Γ:=Γ) (τ:=τ) (case Γ e t1 t2) :=
  case _ (Dtm_c n e) (Dtm_c n t1) (Dtm_c n t2);
Dtm_c n (Γ:=Γ) (τ:=τ) (inl Γ p) := inl _ (Dtm_c n p);
Dtm_c n (Γ:=Γ) (τ:=τ) (inr Γ p) := inr _ (Dtm_c n p)
.

(* Forward *)
Fixpoint Dt n τ : ty :=
  match τ with
  | Real => Real × Array n Real
  (* | Nat => Nat *)
  | Array m t => Array m (Dt n t)
  | t1 × t2 => Dt n t1 × Dt n t2
  | t1 → t2 => Dt n t1 → Dt n t2
  | t1 <+> t2 => Dt n t1 <+> Dt n t2
  end.

Definition Dctx n Γ : Ctx := map (Dt n) Γ.

Fixpoint Dv {Γ τ n} (v: τ ∈ Γ) : (Dt n τ) ∈ (Dctx n Γ) :=
  match v with
  | Top Γ τ => Top (map (Dt n) Γ) (Dt n τ)
  | Pop Γ τ σ t => Pop (map (Dt n) Γ) (Dt n τ) (Dt n σ) (Dv t)
  end.

Equations Dtm {Γ τ} n : tm Γ τ -> tm (map (Dt n) Γ) (Dt n τ) :=
(* STLC *)
Dtm n (Γ:=Γ) (τ:=τ) (var Γ τ v) := var _ _ (Dv v);
Dtm n (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) := app _ _ _ (Dtm n t1) (Dtm n t2);
Dtm n (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) := abs _ _ _ (Dtm n f);
(* Arrays *)
(* Dtm n (Γ:=Γ) (τ:=τ) (build_nil Γ τ) => build_nil _ _; *)
Dtm n (Γ:=Γ) (τ:=τ) (build Γ τ m ta) =>
  build _ _ _ (Dtm n ∘ ta);
Dtm n (Γ:=Γ) (τ:=τ) (get Γ ti ta) => get _ ti (Dtm n ta);
(* Nat *)
(* Dtm n (Γ:=Γ) (τ:=τ) (nval Γ m) := nval _ m;
Dtm n (Γ:=Γ) (τ:=τ) (nsucc Γ m) := nsucc _ (Dtm n m);
Dtm n (Γ:=Γ) (τ:=τ) (nrec Γ τ tf ti t) :=
  nrec _ _ (Dtm n tf) (Dtm n ti) (Dtm n t); *)
(* Reals *)
Dtm n (Γ:=Γ) (τ:=τ) (rval Γ r) :=
  tuple _ (rval _ r) (build _ _ n (fun _ => rval _ 0));
Dtm n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) with Dtm n t1 := {
  Dtm n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 with Dtm n t2 := {
    Dtm n (Γ:=Γ) (τ:=τ) (add Γ t1 t2) d1 d2 :=
      tuple _
        (add _ (first _ d1) (first _ d2))
        (vector_add (second _ d1) (second _ d2))
  }
};
Dtm n (Γ:=Γ) (τ:=τ) (mul Γ t1 t2) with Dtm n t1 := {
  Dtm n (Γ:=Γ) (τ:=τ) (mul Γ t1 t2) d1 with Dtm n t2 := {
    Dtm n (Γ:=Γ) (τ:=τ) (mul Γ t1 t2) d1 d2 :=
      tuple _
        (mul _ (first _ d1) (first _ d2))
        (vector_add
          (vector_map (second _ d1) (mul _ (first _ d2)))
          (vector_map (second _ d2) (mul _ (first _ d1))))
  }
};
(* Products *)
Dtm n (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) := tuple _ (Dtm n t1) (Dtm n t2);
Dtm n (Γ:=Γ) (τ:=τ) (first Γ p) := first _ (Dtm n p);
Dtm n (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm n p);
(* Sums *)
Dtm n (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) := case _ (Dtm n e) (Dtm n c1) (Dtm n c2);
Dtm n (Γ:=Γ) (τ:=τ) (inl Γ e) := inl _ (Dtm n e);
Dtm n (Γ:=Γ) (τ:=τ) (inr Γ e) := inr _ (Dtm n e).

Lemma vector_eq : forall A n (h h' : A) (t t' : vector A n),
  h = h' -> t = t' -> Vcons h t = Vcons h' t'.
Proof. rewrites. Qed.

(*
  For some arguments (ctx = x_1, ..., x_n : ⟦ repeat ℝ n ⟧ₜₓ)
  Need to augment ctx for Dtm with arguments to get all
    partial derivatives.
    ex. ctx = x, y
        ctx' = (x, [1, 0]), (y, [0, 1])

  Try and augment Dtm and Dtm_c such that they both give
    equal output on f : R^n -> R.
    Dtm:
      input: tuple (R * R)
        (pos to eval at,
          one-hot enc which var to take the part deriv of)
      output: tuple (R * R)
        (evaluate function at pos,
          partial deriv at pos)

    Dtm_c:
      input: tuple (R * R -> Array ℝ n)
        (pos to eval at,
          one-hot encoding with id instead of 1)
      output: tuple (R * R -> Array ℝ n)
        (evaluate function at pos,
          function which evaluated at 1 gives the partial derivs)
*)

(* Helper function for creating one-hot encoding vectors with variable start
    indices *)
Equations vector_one_hot' (j i n : nat) : vector R n  :=
vector_one_hot' j i 0 := Vnil;
vector_one_hot' j i (S n') :=
  Vcons (if Nat.eqb i j then 1 else 0) (vector_one_hot' (S j) i n').

(* Create a one-hot encoding of length n with the one at position i *)
Equations vector_one_hot (i n : nat) : vector R n :=
vector_one_hot i n := vector_one_hot' 0 i n.

(* Create a one-hot encoding matrix of with width n and height m.
    Current row-index is tracked in i.
*)
Equations one_hots (i n m : nat) : ⟦repeat (Array n ℝ) m⟧ₜₓ :=
one_hots i n 0 := HNil;
one_hots i n (S m) :=
  @denote_ctx_cons (repeat (Array n ℝ) m) (Array n ℝ)
    (vector_one_hot i n) (one_hots (S i) n m).

(* Simply tuples the input vector with the matrix *)
Equations Dtm_ctx' n m (ctx : ⟦repeat ℝ n⟧ₜₓ) (ctx2 : ⟦repeat (Array m ℝ) n⟧ₜₓ)
  : ⟦map (Dt m) (repeat ℝ n)⟧ₜₓ :=
Dtm_ctx' 0 m ctx ctx' := HNil;
Dtm_ctx' (S n) m (HCons x hl) (HCons x' hl') :=
  @denote_ctx_cons (map (Dt m) (repeat ℝ n)) (Dt m ℝ)
  (x, x') (Dtm_ctx' n m hl hl').

(* Couple the one-hot encoded matrices with the input vectors for input to
    the macro Dtm
  Ex.
    [x]    [x], [1 0 0]
    [y] => [y], [0 1 0]
    [z]    [z], [0 0 1]
*)
Equations Dtm_ctx {n m} (ctx : ⟦repeat ℝ n⟧ₜₓ) : ⟦map (Dt m) (repeat ℝ n)⟧ₜₓ :=
Dtm_ctx ctx := Dtm_ctx' n m ctx (one_hots 0 m n).

(* Helper function for creating one-hot id encoding vectors with variable start
    indices *)
Equations vector_one_hot_c' (j i n : nat) : R -> vector R n  :=
vector_one_hot_c' j i 0 r := Vnil;
vector_one_hot_c' j i (S n) r :=
  Vcons (if Nat.eqb i j then r else 0) (vector_one_hot_c' (S j) i n r).

(* Create a one-hot id encoding matrix of with width n and height m.
    Current row-index is tracked in i.
*)
Equations vector_one_hot_c (i n : nat) : R -> vector R n :=
vector_one_hot_c i n r := vector_one_hot_c' 0 i n r.

(* Create a one-hot id encoding vector of length n with the id at position i *)
Equations one_hots_c (i n m : nat) : ⟦repeat (ℝ → Array n ℝ) m⟧ₜₓ :=
one_hots_c i n 0 := HNil;
one_hots_c i n (S m) :=
  @denote_ctx_cons (repeat (ℝ → Array n ℝ) m) (ℝ → Array n ℝ)
    (vector_one_hot_c i n) (one_hots_c (S i) n m).

Equations Dtm_ctx_c' n m
  (ctx : ⟦repeat ℝ n⟧ₜₓ) (ctx' : ⟦repeat (ℝ → Array m ℝ) n⟧ₜₓ)
  : ⟦map (Dt_c m) (repeat ℝ n)⟧ₜₓ :=
Dtm_ctx_c' 0 m ctx ctx' := HNil;
Dtm_ctx_c' (S n) m (HCons x hl) (HCons x' hl') :=
  @HCons ty denote_t (Dt_c m ℝ)
  (map (Dt_c m) (repeat ℝ n))
  (x, x') (Dtm_ctx_c' n m hl hl').

(* Couple the matrices with the input vectors for input to
    the macro Dtm_c
  Ex.
    [x]    [x], (\a. [a 0 0])
    [y] => [y], (\a. [0 a 0])
    [z]    [z], (\a. [0 0 a])
*)
Equations Dtm_ctx_c {n m} (ctx : ⟦repeat ℝ n⟧ₜₓ)
  : ⟦map (Dt_c m) (repeat ℝ n)⟧ₜₓ :=
Dtm_ctx_c ctx := Dtm_ctx_c' n m ctx (one_hots_c 0 m n).

Equations trigger_ctx_c {n} m (ctx : ⟦ repeat (ℝ → Array n ℝ) m ⟧ₜₓ)
  : ⟦ repeat (Array n ℝ) m ⟧ₜₓ :=
trigger_ctx_c 0 HNil => HNil;
trigger_ctx_c (S m) (t ::: xs) =>
  @denote_ctx_cons (repeat (Array n ℝ) m) (Array n ℝ)
  (t 1) (trigger_ctx_c m xs).

Lemma vector_one_hot'_same : forall j i n,
  vector_one_hot' j i n = vector_one_hot_c' j i n 1.
Proof with quick.
  intros i j n.
  generalize dependent i.
  generalize dependent j.
  induction n...
  simp vector_one_hot' vector_one_hot_c'.
  apply Vcons_eq. splits.
  rewrite IHn...
Qed.

Lemma vector_one_hot_same : forall i n,
  vector_one_hot i n = vector_one_hot_c i n 1.
Proof with quick.
  intros.
  simp vector_one_hot vector_one_hot_c.
  generalize dependent i.
  induction n...
  apply vector_one_hot'_same.
Qed.

Lemma one_hots_same : forall i n m,
  one_hots i n m = trigger_ctx_c m (one_hots_c i n m).
Proof with quick.
  intros.
  generalize dependent i.
  generalize dependent n.
  induction m; quick; simp one_hots; simp one_hots_c;
    simp trigger_ctx_c.
  { unfold denote_ctx_cons. simp trigger_ctx_c.
    unfold denote_ctx_cons.
    rewrites. rewrite vector_one_hot_same... }
Qed.

Ltac eval_denote :=
    repeat (try (rewrite denote_shift);
      simp denote_tm; quick; unfold compose; simp denote_tm;
      quick; simp denote_v; quick).

(* y + x * x *)
Example derivative_example_dtm :
  (⟦ Dtm 2 square_plus ⟧ₜₘ
    (@Dtm_ctx 2 2
      (@denote_ctx_cons (ℝ::[]) ℝ 7
        (@denote_ctx_cons [] ℝ 13 HNil))))
    = ((13 + 7 * 7)%R,
      Vcons (0 + (7 * 1 + 7 * 1))%R (Vcons (1 + (7 * 0 + 7 * 0))%R Vnil)).
Proof with quick.
  intros. unfold square_plus.
  simp Dtm...
Qed.

(* y + (x * x) *)
Example derivative_example_dtm_c :
  (⟦ Dtm_c 2 square_plus ⟧ₜₘ
    (@Dtm_ctx_c 2 2
      (@denote_ctx_cons (ℝ::[]) ℝ 7
        (@denote_ctx_cons [] ℝ 13 HNil))))
    = ((13 + 7 * 7)%R, (fun x =>
      Vcons (0 + (7 * x + 7 * x))%R (Vcons (x + (0 + 0))%R Vnil))).
Proof with quick.
  intros. unfold square_plus.
  simp Dtm_c...
Qed.

Example derivative_example :
  snd (⟦ Dtm 2 square_plus ⟧ₜₘ
    (@Dtm_ctx 2 2
      (@denote_ctx_cons (ℝ::[]) ℝ 7
        (@denote_ctx_cons [] ℝ 13 HNil))))
  =
  snd ((⟦ Dtm_c 2 square_plus ⟧ₜₘ
    (@Dtm_ctx_c 2 2
      (@denote_ctx_cons (ℝ::[]) ℝ 7
        (@denote_ctx_cons [] ℝ 13 HNil))))) 1.
Proof with quick.
  rewrite derivative_example_dtm.
  rewrite derivative_example_dtm_c. simpl.
  now rewrite Rmult_0_r...
Qed.

(*
  Logical relations proof between the denotations given by the
  forward and reverse mode macros
*)

Equations S n τ :
  (R -> ⟦ Dt n τ ⟧ₜ) -> (R -> ⟦ Dt_c n τ ⟧ₜ) -> Prop :=
S n ℝ f g := ((fun r => (fst (f r))) = fun r => (fst (g r))) /\
  (fun r => (snd (f r))) = fun r => (snd (g r)) 1;
S n (Array m τ) f g := forall i,
  exists f1 g1,
    S n τ f1 g1 /\
    (fun r => vector_nth i (f r)) = f1 /\
    (fun r => vector_nth i (g r)) = g1;
S n (σ × ρ) f g :=
  exists f1 f2 g1 g2,
  exists (s1 : S n σ f1 f2) (s2 : S n ρ g1 g2),
    (f = fun r => (f1 r, g1 r)) /\
    (g = fun r => (f2 r, g2 r));
S n (σ → ρ) f g :=
  forall (g1 : R -> ⟦ Dt n σ ⟧ₜ)
    (g2 : R -> ⟦ Dt_c n σ ⟧ₜ) (sσ : S n σ g1 g2),
    S n ρ (fun x => f x (g1 x))
      (fun x => g x (g2 x));
S n (σ <+> ρ) f g :=
  (exists g1 g2,
    S n σ g1 g2 /\
      f = Datatypes.inl ∘ g1 /\
      g = Datatypes.inl ∘ g2) \/
  (exists g1 g2,
    S n ρ g1 g2 /\
      f = Datatypes.inr ∘ g1 /\
      g = Datatypes.inr ∘ g2).

(* Helper definition to ensure that the context is only built
    from terms whose denotation are in the relation
*)
Inductive instantiation : forall n Γ,
    (R -> ⟦ Dctx n Γ ⟧ₜₓ) -> (R -> ⟦ Dctx_c n Γ ⟧ₜₓ) -> Prop :=
  | inst_empty : forall n,
      instantiation n [] (Basics.const HNil) (Basics.const HNil)
  | inst_cons :
      forall n Γ τ,
      forall g1 g2,
      forall (sb: R -> ⟦ Dctx n Γ ⟧ₜₓ),
      forall (sb_c: R -> ⟦ Dctx_c n Γ ⟧ₜₓ),
        instantiation n Γ sb sb_c ->
        S n τ g1 g2 ->
        instantiation n (τ::Γ)
          (fun r => (g1 r ::: sb r)) (fun r => (g2 r ::: sb_c r)).

(* Very useful helper definitions for rewriting the relations,
    as the denotations we're working on are functions *)
Lemma inst_eq : forall n Γ f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> instantiation n Γ f1 f2 = instantiation n Γ g1 g2.
Proof. intros; rewrites. Qed.

Lemma S_eq : forall n τ f1 f2 g1 g2,
  g1 = f1 -> g2 = f2 -> S n τ f1 f2 = S n τ g1 g2.
Proof. intros; rewrites. Qed.

Lemma denote_array_eq :
  forall Γ τ n f1 f1' (ctx : ⟦ Γ ⟧ₜₓ) (ctx' : ⟦ Γ ⟧ₜₓ),
    f1 = f1' -> ctx = ctx' ->
    denote_array (τ:=τ) n f1 ctx = denote_array (τ:=τ) n f1' ctx'.
Proof. intros; rewrites. Qed.

Lemma Vcons_eq' : forall A n (t t': A) (tl tl': vector A n),
  Vcons t tl = Vcons t' tl' -> t = t' /\ tl = tl'.
Proof with quick.
  intros. split; dependent destruction H...
Qed.

Lemma vector_nth_eq : forall (A : Set) n (i : Fin.t n) (v v': vector A n),
  v = v' -> vector_nth i v = vector_nth i v'.
Proof with quick.
  intros. rewrites.
Qed.

Lemma denote_array_eq_const_correct :
  forall Γ m n (ctx : ⟦ Dctx m Γ ⟧ₜₓ) (ctx_c : ⟦ Dctx_c m Γ ⟧ₜₓ),
  @denote_array (Dctx m Γ) ℝ n (const (const 0)) ctx =
    @denote_array (ℝ::Dctx_c m Γ) ℝ n (const (const 0))
      (@denote_ctx_cons (Dctx_c m Γ) ℝ 1 ctx_c).
Proof with quick.
  unfold const.
  intros; induction n...
  - apply Vcons_eq. split...
Qed.

Lemma denote_array_eq_add_correct :
  forall n m Γ x1 x2 f1 f2
    (d: ⟦ Dctx_c m Γ ⟧ₜₓ) (d0: ⟦ Dctx m Γ ⟧ₜₓ),
  x1 d0 = f1 d 1 -> x2 d0 = f2 d 1 ->
  @denote_array (Dctx m Γ) ℝ n
    (fun i ctx => (vector_nth i (x1 ctx) + vector_nth i (x2 ctx))%R) d0 =
  @denote_array (ℝ :: Dctx_c m Γ) ℝ n
    (fun i ctx => (vector_nth i (f1 (htl ctx) (denote_ctx_hd ctx)) +
      vector_nth i (f2 (htl ctx) (denote_ctx_hd ctx)))%R)
    (@denote_ctx_cons (Dctx_c m Γ) ℝ 1 d).
Proof with quick.
  intros; induction n...
  { apply Vcons_eq. split; rewrites...
    { unfold shave_fin...
      erewrite (IHn (fun x => Vtail (x1 x)) (fun x => Vtail (x2 x))
        (fun ctx x => Vtail (f1 ctx x)) (fun ctx x => Vtail (f2 ctx x)))...
      all: apply f_equal... } }
Qed.

Lemma denote_array_eq_mul_correct :
  forall (n: nat) m (Γ: Ctx)
    x1 x2 f1 f2
    x1' x2' f1' f2'
    (d: ⟦ Dctx m Γ ⟧ₜₓ)
    (d0: ⟦ Dctx_c m Γ ⟧ₜₓ),
  x2 d = f2 d0 1 -> x1 d = f1 d0 1 ->
  x1' d = f1' d0 1 -> x2' d = f2' d0 1 ->
    @denote_array (Dctx m Γ) ℝ n
      (fun (i : Fin.t n) (ctx : ⟦ Dctx m Γ ⟧ₜₓ) =>
      (vector_nth i
          (@denote_array (Dctx m Γ) ℝ n
            (fun (x : Fin.t n) (ctx' : ⟦ Dctx m Γ ⟧ₜₓ) =>
              x2 ctx' *
              vector_nth x (x1' ctx')) ctx) +
        vector_nth i
          (@denote_array (Dctx m Γ) ℝ n
            (fun (x : Fin.t n) (ctx' : ⟦ Dctx m Γ ⟧ₜₓ) =>
              x1 ctx' *
              vector_nth x (x2' ctx')) ctx))%R) d =
    @denote_array (ℝ :: Dctx_c m Γ) ℝ n
      (fun (i : Fin.t n) (ctx : ⟦ ℝ :: Dctx_c m Γ ⟧ₜₓ) =>
    (vector_nth i
        ((f1' (htl ctx)
          ((f2 (htl ctx) (denote_ctx_hd ctx)) * denote_ctx_hd ctx))) +
    vector_nth i
      ((f2' (htl ctx)
         ((f1 (htl ctx) (denote_ctx_hd ctx)) * denote_ctx_hd ctx))))%R)
      (@denote_ctx_cons (Dctx_c m Γ) ℝ 1 d0).
Proof with quick.
  induction n...
  { apply Vcons_eq.
    unfold shave_fin...
    rewrite (IHn m Γ x1 x2 f1 f2
      (fun x => Vtail (x1' x)) (fun x => Vtail (x2' x))
      (fun x => @Vtail _ _ ∘ (f1' x)) (fun x => @Vtail _ _ ∘ (f2' x))
      d d0)...
  all: unfold compose.
  all: rewrites.
    split.
    { erewrite vector_nth_eq.
    2:{ apply Vcons_eq. split.
        rewrite <- H. rewrite <- H1.
        all: reflexivity. }
      erewrite (vector_nth_eq _ _ _
        (Vcons (f1 d0 1 * vector_nth (nat_to_fin n) (f2' d0 1))%R
            (@denote_array (Dctx m Γ) ℝ n
              (fun (i : Fin.t n) (ctx' : ⟦ Dctx m Γ ⟧ₜₓ) =>
                x1 ctx' * vector_nth i (Vtail (x2' ctx')))%R d))).
    2:{ apply Vcons_eq; split.
        rewrite <- H0. rewrite <- H2.
        all: reflexivity. }
    all: rewrites.
    all: admit. }
    { admit. } }
Admitted.
(*
denote_array n
  (fun (i : Fin.t n) (ctx : ⟦ map (Dt n) Γ ⟧ₜₓ) =>
   (vector_nth i
      (denote_array n
         (fun (x : Fin.t n) (ctx' : ⟦ map (Dt n) Γ ⟧ₜₓ) =>
          fst (⟦ Dtm n t2 ⟧ₜₘ ctx') *
          vector_nth x (snd (⟦ Dtm n t1 ⟧ₜₘ ctx'))) ctx) +
    vector_nth i
      (denote_array n
         (fun (x : Fin.t n) (ctx' : ⟦ map (Dt n) Γ ⟧ₜₓ) =>
          fst (⟦ Dtm n t1 ⟧ₜₘ ctx') *
          vector_nth x (snd (⟦ Dtm n t2 ⟧ₜₘ ctx'))) ctx))%R) d =
denote_array n
  (fun (i : Fin.t n) (ctx : ⟦ ℝ :: map (Dt_c n) Γ ⟧ₜₓ) =>
   (vector_nth i
      (snd (⟦ Dtm_c n t1 ⟧ₜₘ (htl ctx))
         (fst (⟦ Dtm_c n t2 ⟧ₜₘ (htl ctx)) * denote_ctx_hd ctx)) +
    vector_nth i
      (snd (⟦ Dtm_c n t2 ⟧ₜₘ (htl ctx))
         (fst (⟦ Dtm_c n t1 ⟧ₜₘ (htl ctx)) * denote_ctx_hd ctx)))%R)
  (1 ::: d0)
      *)

Lemma S_subst :
  forall Γ τ n,
  forall (t : tm Γ τ),
  forall (sb : R -> ⟦ Dctx n Γ ⟧ₜₓ),
  forall (sb_c : R -> ⟦ Dctx_c n Γ ⟧ₜₓ),
  instantiation n Γ sb sb_c ->
  S n τ (fun x => ⟦Dtm n t⟧ₜₘ (sb x))
    (fun x => ⟦Dtm_c n t⟧ₜₘ (sb_c x)).
Proof with quick.
  dependent induction t...
  { (* Var *)
    simp Dtm Dtm_c.
    dependent induction v; quick;
      dependent destruction H...
    { pose proof (IHv sb0 sb_c0 H) as IHv.
      erewrite S_eq.
      apply IHv.
    all: extensionality x; simp denote_tm... } }
  { (* App *)
    simp Dtm Dtm_c.
    pose proof (IHt1 sb sb_c H) as IHt1.
    pose proof (IHt2 sb sb_c H) as IHt2.
    simp S in IHt1.
    erewrite S_eq.
    apply IHt1...
  all: extensionality x; simp denote_tm... }
  { (* App *)
    intros. simp S Dtm Dtm_c...
    specialize IHt with
      (fun r => (g1 r ::: sb r)) (fun r => (g2 r ::: sb_c r))...
    eapply IHt. constructor; assumption. }
  { (* Build *)
    intros. simp S...
    induction n0.
    { inversion i. }
    { pose proof (IHn0 (shave_fin t)) as IHn0.
      simp Dtm denote_tm in *...
      dependent destruction i...
      clear IHn0.
      exists (fun r =>
        ⟦ Dtm n (t (nat_to_fin n0)) ⟧ₜₘ (sb r)).
      exists (fun r =>
        ⟦ Dtm_c n (t (nat_to_fin n0)) ⟧ₜₘ (sb_c r))... } }
  { (* Get
        Proven by logical relation where (τ:=Array n τ) *)
    pose proof (IHt sb sb_c H) as IHt. simp S in *.
    specialize IHt with t.
    destruct IHt as [f1 [g1 [Hs1 [Heq1 Heq2]]]]; subst.
    erewrite S_eq... }
  { (* Const *)
    simp S. split;
      extensionality x; simp Dtm Dtm_c; simp denote_tm...
    { clear r. simp denote_tm.
      unfold compose.
      unfold const.
      eassert (H': (fun (i : Fin.t n) =>
        ⟦ rval (map (Dt n) Γ) 0 ⟧ₜₘ) = const (const 0)).
      { extensionality i. extensionality ctx. simp denote_tm... }
      rewrite_c H'. unfold compose.
      eassert (H': (fun _ : Fin.t n =>
        ⟦ rval (ℝ :: map (Dt_c n) Γ) 0 ⟧ₜₘ) = const (const 0)).
      { extensionality i. extensionality ctx. unfold const. simp denote_tm... }
      rewrite_c H'.
      apply denote_array_eq_const_correct. } }
  { (* Add *)
    simp Dtm Dtm_c.
    pose proof (IHt1 sb sb_c H) as [IHeq1 IHeq1'].
    pose proof (IHt2 sb sb_c H) as [IHeq2 IHeq2'].
    clear IHt1 IHt2.
    simp S in *. split; extensionality r;
      eapply equal_f in IHeq1; eapply equal_f in IHeq2;
      eapply equal_f in IHeq1'; eapply equal_f in IHeq2';
      simp denote_tm...
    { rewrites. }
    { unfold vector_add, vector_map2...
      simp denote_tm; unfold compose...
      erewrite denote_array_eq...
      erewrite (denote_array_eq (ℝ :: map (Dt_c n) Γ))...
    2:{ extensionality i. extensionality ctx. simp denote_tm.
        rewrite 2 denote_shift. simp denote_tm.
        eassert (⟦ Top (map (Dt_c n) Γ) ℝ ⟧ᵥ = denote_ctx_hd).
        { extensionality xs. dependent destruction xs... }
        rewrite H0.
        reflexivity. }
    2:{ extensionality i. extensionality ctx. simp denote_tm.
        reflexivity. }
      clear IHeq1 IHeq2.
      remember (sb_c r); remember (sb r).
      rewrite <- Heqd in IHeq2', IHeq1';
        rewrite <- Heqd0 in IHeq2', IHeq1'.
      clear Heqd Heqd0 sb sb_c H r.
      apply (denote_array_eq_add_correct n n Γ
        (fun d => snd (⟦ Dtm n t1 ⟧ₜₘ d))
        (fun d => snd (⟦ Dtm n t2 ⟧ₜₘ d))
        (fun d x => snd (⟦ Dtm_c n t1 ⟧ₜₘ d) x)
        (fun d x => snd (⟦ Dtm_c n t2 ⟧ₜₘ d) x)
        d d0 IHeq1' IHeq2'). } }
  { (* Mul *)
    simp Dtm Dtm_c.
    pose proof (IHt1 sb sb_c H) as [IHeq1 IHeq1'].
    pose proof (IHt2 sb sb_c H) as [IHeq2 IHeq2'].
    clear IHt1 IHt2.
    simp S in *.
    split; extensionality r;
      eapply equal_f in IHeq1; eapply equal_f in IHeq2;
      eapply equal_f in IHeq1'; eapply equal_f in IHeq2';
      simp denote_tm...
    { rewrites. }
    { remember (sb r); remember (sb_c r).
      rewrite <- Heqd in IHeq1', IHeq2', IHeq1, IHeq2.
      rewrite <- Heqd0 in IHeq1', IHeq2', IHeq1, IHeq2.
      clear sb sb_c H Heqd Heqd0 r.
      unfold vector_add, vector_map2...
      simp denote_tm; unfold compose...
      erewrite denote_array_eq...
      erewrite (denote_array_eq (ℝ :: map (Dt_c n) Γ))...
  2:{ extensionality i. extensionality ctx.
      simp denote_tm. rewrite 4 denote_shift.
      simp denote_tm.
      eassert (⟦ Top (map (Dt_c n) Γ) ℝ ⟧ᵥ = denote_ctx_hd).
      { extensionality xs. dependent destruction xs... }
      rewrite_c H. reflexivity. }
  2:{ extensionality i. extensionality ctx.
      simp denote_tm. unfold vector_map.
      simp denote_tm. unfold compose.
      erewrite (denote_array_eq _ _ _ (fun x : Fin.t n =>
       ⟦ mul (map (Dt n) Γ) (first (map (Dt n) Γ) (Dtm n t1))
           (get (map (Dt n) Γ) x (second (map (Dt n) Γ) (Dtm n t2))) ⟧ₜₘ))...
    2:{ extensionality x; extensionality ctx'.
        simp denote_tm. reflexivity. }
        erewrite denote_array_eq...
    2:{ extensionality x; extensionality ctx'.
        simp denote_tm. reflexivity. }
      reflexivity. }
      apply (denote_array_eq_mul_correct
        n n Γ (fst ∘ ⟦ Dtm n t1 ⟧ₜₘ) (fst ∘ ⟦ Dtm n t2 ⟧ₜₘ)
        (fun ctx x => fst (⟦ Dtm_c n t1 ⟧ₜₘ ctx))
        (fun ctx x => fst (⟦ Dtm_c n t2 ⟧ₜₘ ctx))
        (snd ∘ ⟦ Dtm n t1 ⟧ₜₘ)
        (snd ∘ ⟦ Dtm n t2 ⟧ₜₘ)
        (fun ctx => snd (⟦ Dtm_c n t1 ⟧ₜₘ ctx))
        (fun ctx => snd (⟦ Dtm_c n t2 ⟧ₜₘ ctx))
        d d0 IHeq2 IHeq1 IHeq1' IHeq2'). } }
  { (* Products *)
    simp Dtm Dtm_c.
    pose proof (IHt1 sb sb_c H) as IHt1.
    pose proof (IHt2 sb sb_c H) as IHt2.
    simp S.
    exists (fun x : R => ⟦ Dtm n t1 ⟧ₜₘ (sb x));
      exists (fun x : R => ⟦ Dtm_c n t1 ⟧ₜₘ (sb_c x)).
    exists (fun x : R => ⟦ Dtm n t2 ⟧ₜₘ (sb x));
      exists (fun x : R => ⟦ Dtm_c n t2 ⟧ₜₘ (sb_c x)).
    exists IHt1; exists IHt2.
    split... }
  { (* Projection 1 *)
    simp Dtm Dtm_c.
    pose proof (IHt sb sb_c H) as IHt.
    simp S in IHt.
    destruct IHt as [f1 [f2 [g1 [g2 [S1 [S2 [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x...
    { eapply equal_f in Heq1. simp denote_tm. erewrite Heq1... }
    { eapply equal_f in Heq2. simp denote_tm. erewrite Heq2... } }
  { (* Projection 2 *)
    simp Dtm Dtm_c.
    pose proof (IHt sb sb_c H) as IHt.
    simp S in IHt.
    destruct IHt as [f1 [f2 [g1 [g2 [S1 [S2 [Heq1 Heq2]]]]]]].
    erewrite S_eq; quick; extensionality x...
    { eapply equal_f in Heq1. simp denote_tm. erewrite Heq1... }
    { eapply equal_f in Heq2. simp denote_tm. erewrite Heq2... } }
  { (* Case *)
    intros.
    pose proof (IHt1 sb sb_c H) as IHt1.
    pose proof (IHt2 sb sb_c H) as IHt2.
    pose proof (IHt3 sb sb_c H) as IHt3.
    simp S in *. simp Dtm Dtm_c.
    (* Either term denotates to inl or inr *)
    destruct IHt1 as [[g1 [g2 H']]|[g1 [g2 H']]].
    { (* Scrutinee is inl *)
      clear IHt3.
      destruct H' as [Hs [Heq1 Heq2]].
      erewrite S_eq...
      { extensionality x. eapply equal_f in Heq1.
        simp denote_tm. now rewrite Heq1. }
      { extensionality x. eapply equal_f in Heq2.
        simp denote_tm. now rewrite Heq2. } }
    { (* Scrutinee is inr *)
      clear IHt2.
      destruct H' as [Hs [Heq1 Heq2]].
      erewrite S_eq...
      { extensionality x. eapply equal_f in Heq1.
        simp denote_tm. rewrite Heq1... }
      { extensionality x. eapply equal_f in Heq2.
        simp denote_tm. rewrite Heq2... } } }
  { (* Inl *)
    intros. simp S. left...
    exists (⟦ Dtm n t ⟧ₜₘ ∘ sb );
      exists (⟦ Dtm_c n t ⟧ₜₘ ∘ sb_c)... }
  { (* Inl *)
    intros. simp S. right...
    exists (⟦ Dtm n t ⟧ₜₘ ∘ sb );
      exists (⟦ Dtm_c n t ⟧ₜₘ ∘ sb_c)... }
  Grab Existential Variables.
  all: apply r.
Qed.

Lemma inst_correct :
  forall (i n m: nat) (f: R -> ⟦ repeat ℝ m ⟧ₜₓ),
    instantiation n (repeat ℝ m)
      (fun x : R => Dtm_ctx' m n (f x) (one_hots i n m))
      (fun x : R => Dtm_ctx_c' m n (f x) (one_hots_c i n m)).
Proof with quick.
  intros. generalize dependent i.
  generalize dependent n.
  induction m...
  { erewrite inst_eq.
  2,3: extensionality x; remember (f x);
      dependent destruction d; simp Dtm_ctx' Dtm_ctx_c'; reflexivity.
    apply inst_empty. }
  { erewrite inst_eq.
    apply inst_cons. apply IHm.
    clear IHm.
    simp S.
  2,3: extensionality x; simp one_hots one_hots_c.
  2,3: unfold denote_ctx_cons...
    all: admit. }
Admitted.

Lemma fundamental_property :
  forall τ n m,
  forall (t : tm (repeat ℝ m) τ),
  forall (f : R -> ⟦ repeat ℝ m ⟧ₜₓ),
  S n τ (fun x => ⟦Dtm n t⟧ₜₘ (@Dtm_ctx m n (f x)))
    (fun x => ⟦Dtm_c n t⟧ₜₘ (@Dtm_ctx_c m n (f x))).
Proof with quick.
  intros.
  apply S_subst.
  clear t.
  erewrite inst_eq.
2,3: extensionality x; simp Dtm_ctx Dtm_ctx_c;
    generalize dependent n; quick; reflexivity.
  apply inst_correct.
  (* induction m...
  { erewrite inst_eq.
  2,3: extensionality x; remember (f x);
      dependent destruction d;
      simp Dtm_ctx Dtm_ctx_c Dtm_ctx' Dtm_ctx_c';
      reflexivity.
    eassert (H: (fun _ : R => HNil) = const HNil)...
    rewrite_c H.
    constructor. }
  { rewrite (inst_eq n (ℝ :: repeat ℝ m) _ _
      (fun x =>
        (@denote_ctx_cons (Dctx n (repeat ℝ m)) (Dt n ℝ)
          (* (repeat ℝ m) *)
          ((denote_ctx_hd ∘ f) x, vector_one_hot 0 n)
          (Dtm_ctx' m n ((denote_ctx_tl ∘ f) x) (one_hots 1 n m))))
      (fun x =>
        (@denote_ctx_cons (Dctx_c n (repeat ℝ m)) (Dt_c n ℝ)
          ((denote_ctx_hd ∘ f) x, vector_one_hot_c 0 n)
          (Dtm_ctx_c' m n ((denote_ctx_tl ∘ f) x) (one_hots_c 1 n m))))).
  2,3: extensionality x; unfold compose; remember (f x);
      dependent destruction d...
  all: unfold denote_ctx_cons; unfold denote_ctx_hd;
      unfold denote_ctx_tl; unfold compose; simpl.
    apply inst_cons.
    specialize IHm with (fun x => htl (f x))...
    erewrite inst_eq in IHm.
  2,3: extensionality x; simp Dtm_ctx Dtm_ctx_c; reflexivity.

    simp S. split... extensionality x.
    { rewrite vector_one_hot_same... }
    all: unfold denote_ctx_cons.
    all: admit. *)
Qed.

Lemma S_correctness_R :
  forall n
    (t : tm (repeat ℝ n) ℝ)
    (ctx : R -> ⟦ repeat ℝ n ⟧ₜₓ),
  S n ℝ
    (⟦ Dtm n t ⟧ₜₘ ∘ Dtm_ctx ∘ ctx)
    (⟦ Dtm_c n t ⟧ₜₘ ∘ Dtm_ctx_c ∘ ctx) ->
  (fun r => snd (⟦ Dtm n t ⟧ₜₘ (Dtm_ctx (ctx r)))) =
    fun r => (snd (⟦ Dtm_c n t ⟧ₜₘ (Dtm_ctx_c (ctx r)))) 1.
Proof with quick.
  intros.
  simp S in *. destruct H as [Heq1 Heq2].
  apply Heq2.
Qed.

Lemma correctness :
  forall n
    (t : tm (repeat ℝ n) ℝ) (ctx : ⟦ repeat ℝ n ⟧ₜₓ),
  snd (⟦ Dtm n t ⟧ₜₘ (Dtm_ctx ctx)) =
    snd (⟦ Dtm_c n t ⟧ₜₘ (Dtm_ctx_c ctx)) 1.
Proof with quick.
  intros.
  pose proof (S_correctness_R n t (const ctx)) as H.
  unfold const in *.
  assert (H': forall A (x y : A),
    @const A R x = const y -> x = y).
  { intros. unfold const in *.
    pose proof 0. apply equal_f in H0... }
  apply_c H'.
  unfold const.
  apply H.
  apply fundamental_property.
Qed.
