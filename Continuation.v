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

From AD Require vect.
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
  (* | τ1 <+> τ2 => (Dt_c n τ1 <+> Dt_c n τ2) *)
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
(* Dtm_c n (Γ:=Γ) (τ:=τ) (build_nil Γ τ) => build_nil _ _; *)
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
Dtm_c n (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm_c n p).

(* Forward *)
Fixpoint Dt n τ : ty :=
  match τ with
  | Real => Real × Array n Real
  (* | Nat => Nat *)
  | Array m t => Array m (Dt n t)
  | t1 × t2 => Dt n t1 × Dt n t2
  | t1 → t2 => Dt n t1 → Dt n t2
  (* | t1 <+> t2 => Dt t1 <+> Dt t2 *)
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
Dtm n (Γ:=Γ) (τ:=τ) (second Γ p) := second _ (Dtm n p).
(* Sums *)
(* Dtm (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) := case _ (Dtm e) (Dtm c1) (Dtm c2);
Dtm (Γ:=Γ) (τ:=τ) (inl Γ _ _ e) := inl _ _ _ (Dtm e);
Dtm (Γ:=Γ) (τ:=τ) (inr Γ _ _ e) := inr _ _ _ (Dtm e). *)

Lemma vector_eq : forall A n (h h' : A) (t t' : vector A n),
  h = h' -> t = t' -> Vcons h t = Vcons h' t'.
Proof. rewrites. Qed.

(*
  C&P code for evaluating the denotation (useful for examples):
    simp denote_tm.
    unfold denote_ctx_cons.
    simp denote_v...
    apply injective_projections...
    extensionality x...
    unfold vector_add, vector_map2, vector_hot.
    repeat (simp denote_tm; unfold compose)...
    unfold shave_fin.
    apply vector_eq.
    { repeat (rewrite denote_shift; quick;
        simp denote_v; simp denote_tm)...
      simp denote_v...
      admit. }
    { repeat (simp denote_tm; unfold compose)...
      repeat (rewrite denote_shift; quick;
        repeat (simp denote_v; simp denote_tm))...
      repeat (simp denote_tm; unfold compose)...
      unfold shave_fin.
      repeat (simp denote_tm; unfold compose)...
      repeat (rewrite denote_shift; quick;
        repeat (simp denote_v; simp denote_tm))...
      admit. }
*)

(* y + x * x *)
Example derivative_example_2 :
  (⟦ Dtm 2 square_plus ⟧ₜₘ
    (@denote_ctx_cons (map (Dt 2) (ℝ::[])) (Dt 2 ℝ)
        (7, Vcons 1 (Vcons 0 Vnil))
    (@denote_ctx_cons (map (Dt 2) []) (Dt 2 ℝ)
        (13, Vcons 0 (Vcons 1 Vnil))
        HNil)))
    = ((13 + 7 * 7)%R,
      Vcons (0 + (7 * 1 + 7 * 1))%R (Vcons (1 + (7 * 0 + 7 * 0))%R Vnil)).
Proof with quick.
  intros. unfold square_plus.
  simp Dtm...
Qed.

Example derivative_example_2_c :
  (⟦ Dtm_c 2 square_plus ⟧ₜₘ
    (@denote_ctx_cons (map (Dt_c 2) (ℝ::[])) (Dt_c 2 ℝ)
        (7, fun x => Vcons x (Vcons 0 Vnil))
    (@denote_ctx_cons (map (Dt_c 2) ([])) (Dt_c 2 ℝ)
        (13, fun y => Vcons 0 (Vcons y Vnil))
        HNil)))
    = ((13 + 7 * 7)%R, (fun x =>
      Vcons (0 + (7 * x + 7 * x))%R (Vcons (x + (0 + 0))%R Vnil))).
Proof with quick.
  intros. unfold square_plus.
  simp Dtm_c...
Qed.

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

Equations vector_one_hot' (j i n : nat) : vector R n  :=
vector_one_hot' j i 0 := Vnil;
vector_one_hot' j i (S n') :=
  Vcons (if Nat.eqb i j then 1 else 0) (vector_one_hot' (S j) i n').

Equations vector_one_hot (i n : nat) : vector R n :=
vector_one_hot i n := vector_one_hot' 0 i n.

Equations one_hots (i n m : nat) : ⟦repeat (Array n ℝ) m⟧ₜₓ :=
one_hots i n 0 := HNil;
one_hots i n (S m) :=
  @denote_ctx_cons (repeat (Array n ℝ) m) (Array n ℝ)
    (vector_one_hot i n) (one_hots (S i) n m).

Equations Dtm_ctx' n m (ctx : ⟦repeat ℝ n⟧ₜₓ) (ctx2 : ⟦repeat (Array m ℝ) n⟧ₜₓ)
  : ⟦map (Dt m) (repeat ℝ n)⟧ₜₓ :=
Dtm_ctx' 0 m ctx ctx' := HNil;
Dtm_ctx' (S n) m (HCons x hl) (HCons x' hl') :=
  @HCons ty denote_t (Dt m ℝ)
  (map (Dt m) (repeat ℝ n))
  (x, x') (Dtm_ctx' n m hl hl').

Equations Dtm_ctx {n} (ctx : ⟦repeat ℝ n⟧ₜₓ) : ⟦map (Dt n) (repeat ℝ n)⟧ₜₓ :=
Dtm_ctx ctx := Dtm_ctx' n n ctx (one_hots 0 n n).

Equations vector_one_hot_c' (j i n : nat) : R -> vector R n  :=
vector_one_hot_c' j i 0 r := Vnil;
vector_one_hot_c' j i (S n) r :=
  Vcons (if Nat.eqb i j then r else 0) (vector_one_hot_c' (S j) i n r).

Equations vector_one_hot_c (i n : nat) : R -> vector R n :=
vector_one_hot_c i n r := vector_one_hot_c' 0 i n r.

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

Equations Dtm_ctx_c {n} (ctx : ⟦repeat ℝ n⟧ₜₓ)
  : ⟦map (Dt_c n) (repeat ℝ n)⟧ₜₓ :=
Dtm_ctx_c ctx := Dtm_ctx_c' n n ctx (one_hots_c 0 n n).

(*
  Logical relations proof between the denotations given by the
  forward and reverse mode macros
*)

Equations S n τ :
  (R -> ⟦ Dt n τ ⟧ₜ) -> (R -> ⟦ Dt_c n τ ⟧ₜ) -> Prop :=
S n ℝ f g :=
  (fun r => (snd (f r))) = fun r => (snd (g r)) 1;
S n (Array m τ) f g := True;
S n (τ × σ) f g := True;
S n (τ → σ) f g := True.

(* Equations? pad_Dt n τ (t : ⟦ Dt n τ ⟧ₜ)
  : ⟦ Dt (Datatypes.S n) τ ⟧ₜ :=
pad_Dt n ℝ (r, rs) := (r, Vcons 0 rs);
pad_Dt n (Array m τ) t := Vmap (pad_Dt n τ) t;
pad_Dt n (τ × σ) (t1, t2) := (pad_Dt n τ t1, pad_Dt n σ t2);
pad_Dt n (τ → σ) t := _. *)

Equations? pad_Dtm_ctx n Γ (ctx : ⟦ Dctx n Γ ⟧ₜₓ)
  : ⟦ Dctx (Datatypes.S n) Γ ⟧ₜₓ :=
pad_Dtm_ctx n nil ctx := ctx;
pad_Dtm_ctx n (t::l) (HCons h hl) := _ ::: pad_Dtm_ctx n l hl.

(* Instantiation here keeps track of how many function arguments
    there are/partial derivs are to be calculated. *)
Inductive instantiation : forall n Γ,
    (R -> ⟦ Dctx n Γ ⟧ₜₓ) -> (R -> ⟦ Dctx_c n Γ ⟧ₜₓ) -> Prop :=
  | inst_empty :
      instantiation 0 [] (Basics.const HNil) (Basics.const HNil)
  | inst_args :
      forall n Γ τ,
      forall g1 g2,
      forall (sb: R -> ⟦ Dctx n Γ ⟧ₜₓ),
      forall (sb_c: R -> ⟦ Dctx_c n Γ ⟧ₜₓ),
        instantiation n Γ sb sb_c ->
        S (Datatypes.S n) ℝ g1 g2 ->
        instantiation (Datatypes.S n) (ℝ::Γ)
          (fun r => (g1 r ::: sb r)) (fun r => (g2 r ::: sb_c r))
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

Lemma S_subst :
  forall Γ τ n,
  forall (t : tm Γ τ),
  forall (sb : R -> ⟦ Dctx n Γ ⟧ₜₓ),
  forall (sb_c : R -> ⟦ Dctx_c n Γ ⟧ₜₓ),
  instantiation n Γ sb sb_c ->
  S n τ (fun x => ⟦Dtm n t⟧ₜₘ (sb x))
    (fun x => ⟦Dtm_c n t⟧ₜₘ (sb_c x)).
Proof with quick.
Admitted.

Lemma fundamental_property :
  forall τ n,
  forall (t : tm (repeat ℝ n) τ),
  forall (f : R -> ⟦ repeat ℝ n ⟧ₜₓ),
  S n τ (fun x => ⟦Dtm n t⟧ₜₘ (Dtm_ctx (f x)))
    (fun x => ⟦Dtm_c n t⟧ₜₘ (Dtm_ctx_c (f x))).
Proof with quick.
  intros.
  apply S_subst.
  induction n...
  { constructor. }
  { constructor. }
Qed.

Lemma S_correctness_R :
  forall n
    (t : tm (repeat ℝ n) ℝ)
    (ctx : R -> ⟦ repeat ℝ n ⟧ₜₓ),
  S n ℝ
    (⟦ Dtm n t ⟧ₜₘ ∘ Dtm_ctx ∘ ctx)
    (⟦ Dtm_c n t ⟧ₜₘ ∘ Dtm_ctx_c ∘ ctx) ->
  (fun r => snd (⟦ Dtm n t ⟧ₜₘ (Dtm_ctx (ctx r)))) =
    (fun r => (snd (⟦ Dtm_c n t ⟧ₜₘ (Dtm_ctx_c (ctx r)))) 1).
Proof with quick.
  intros.
  simp S in *.
Qed.

Lemma correctness :
  forall n
    (t : tm (repeat ℝ n) ℝ) (ctx : ⟦ repeat ℝ n ⟧ₜₓ),
  snd (⟦ Dtm n t ⟧ₜₘ (Dtm_ctx ctx)) =
    (snd (⟦ Dtm_c n t ⟧ₜₘ (Dtm_ctx_c ctx))) 1.
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
