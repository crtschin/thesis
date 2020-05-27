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

Equations Dtm_ctx {n m} (ctx : ⟦repeat ℝ n⟧ₜₓ) : ⟦map (Dt m) (repeat ℝ n)⟧ₜₓ :=
Dtm_ctx ctx := Dtm_ctx' n m ctx (one_hots 0 m n).

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

Equations Dtm_ctx_c {n m} (ctx : ⟦repeat ℝ n⟧ₜₓ)
  : ⟦map (Dt_c m) (repeat ℝ n)⟧ₜₓ :=
Dtm_ctx_c ctx := Dtm_ctx_c' n m ctx (one_hots_c 0 m n).

(* y + x * x *)
Example derivative_example_dtm :
  (⟦ Dtm 2 square_plus ⟧ₜₘ
    (@Dtm_ctx 2 2
      (@denote_ctx_cons (ℝ::[]) ℝ 7
        (@denote_ctx_cons [] ℝ 13 HNil))))
    (* (@denote_ctx_cons (map (Dt 2) (ℝ::[])) (Dt 2 ℝ)
        (7, Vcons 1 (Vcons 0 Vnil))
    (@denote_ctx_cons (map (Dt 2) []) (Dt 2 ℝ)
        (13, Vcons 0 (Vcons 1 Vnil))
        HNil))) *)
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
    (* (@denote_ctx_cons (map (Dt_c 2) (ℝ::[])) (Dt_c 2 ℝ)
        (7, fun x => Vcons x (Vcons 0 Vnil))
    (@denote_ctx_cons (map (Dt_c 2) ([])) (Dt_c 2 ℝ)
        (13, fun y => Vcons 0 (Vcons y Vnil))
        HNil))) *)
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
(* S n ℝ f g with n := {
  | 0%nat => ((fun r => (fst (f r))) = fun r => (fst (g r))) /\
      (fun r => (snd (f r))) = fun r => (snd (g r)) 1;
  | Datatypes.S n' => ((fun r => (fst (f r))) = fun r => (fst (g r))) /\
      (fun r => (snd (f r))) = fun r => (snd (g r)) 1
}; *)
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

Equations pad_Dt n τ (t : ⟦ Dt n τ ⟧ₜ)
  : ⟦ Dt (Datatypes.S n) τ ⟧ₜ := {
pad_Dt n ℝ (r, rs) := (r, Vcons 0 rs);
pad_Dt n (Array m τ) t := Vmap (pad_Dt n τ) t;
pad_Dt n (τ × σ) (t1, t2) := (pad_Dt n τ t1, pad_Dt n σ t2);
pad_Dt n (τ <+> σ) t with t := {
  | Datatypes.inl t' => Datatypes.inl (pad_Dt n τ t');
  | Datatypes.inr t' => Datatypes.inr (pad_Dt n σ t')
};
pad_Dt n (τ → σ) t := fun t' => pad_Dt n σ (t (unpad_Dt n τ t')) }
with unpad_Dt n τ (t : ⟦ Dt (Datatypes.S n) τ ⟧ₜ)
  : ⟦ Dt n τ ⟧ₜ :=
unpad_Dt n ℝ (r, rs) := (r, Vtail rs);
unpad_Dt n (Array m τ) t := Vmap (unpad_Dt n τ) t;
unpad_Dt n (τ × σ) (t1, t2) := (unpad_Dt n τ t1, unpad_Dt n σ t2);
unpad_Dt n (τ <+> σ) t with t := {
  | Datatypes.inl t' => Datatypes.inl (unpad_Dt n τ t');
  | Datatypes.inr t' => Datatypes.inr (unpad_Dt n σ t')
};
unpad_Dt n (τ → σ) t := fun t' => unpad_Dt n σ (t (pad_Dt n τ t')).

Equations pad_Dt_c n τ (t : ⟦ Dt_c n τ ⟧ₜ)
  : ⟦ Dt_c (Datatypes.S n) τ ⟧ₜ := {
pad_Dt_c n ℝ (r, rs) := (r, fun x => Vcons 0 (rs x));
pad_Dt_c n (Array m τ) t := Vmap (pad_Dt_c n τ) t;
pad_Dt_c n (τ × σ) (t1, t2) := (pad_Dt_c n τ t1, pad_Dt_c n σ t2);
pad_Dt_c n (τ <+> σ) t with t := {
  | Datatypes.inl t' => Datatypes.inl (pad_Dt_c n τ t');
  | Datatypes.inr t' => Datatypes.inr (pad_Dt_c n σ t')
};
pad_Dt_c n (τ → σ) t := fun t' => pad_Dt_c n σ (t (unpad_Dt_c n τ t')) }
with unpad_Dt_c n τ (t : ⟦ Dt_c (Datatypes.S n) τ ⟧ₜ)
  : ⟦ Dt_c n τ ⟧ₜ :=
unpad_Dt_c n ℝ (r, rs) := (r, fun x => Vtail (rs x));
unpad_Dt_c n (Array m τ) t := Vmap (unpad_Dt_c n τ) t;
unpad_Dt_c n (τ × σ) (t1, t2) := (unpad_Dt_c n τ t1, unpad_Dt_c n σ t2);
unpad_Dt_c n (τ <+> σ) t with t := {
  | Datatypes.inl t' => Datatypes.inl (unpad_Dt_c n τ t');
  | Datatypes.inr t' => Datatypes.inr (unpad_Dt_c n σ t')
};
unpad_Dt_c n (τ → σ) t := fun t' => unpad_Dt_c n σ (t (pad_Dt_c n τ t')).

Equations pad_Dtm_ctx n Γ (ctx : ⟦ Dctx n Γ ⟧ₜₓ)
  : ⟦ Dctx (Datatypes.S n) Γ ⟧ₜₓ :=
pad_Dtm_ctx n nil ctx := ctx;
pad_Dtm_ctx n (τ::l) (HCons h hl) := pad_Dt n τ h ::: pad_Dtm_ctx n l hl.

Equations pad_Dtm_ctx_c n Γ (ctx : ⟦ Dctx_c n Γ ⟧ₜₓ)
  : ⟦ Dctx_c (Datatypes.S n) Γ ⟧ₜₓ :=
pad_Dtm_ctx_c n nil ctx := ctx;
pad_Dtm_ctx_c n (τ::l) (HCons h hl) :=
  pad_Dt_c n τ h ::: pad_Dtm_ctx_c n l hl.

Equations unpad_Dtm_ctx n Γ (ctx : ⟦ Dctx (Datatypes.S n) Γ ⟧ₜₓ)
  : ⟦ Dctx n Γ ⟧ₜₓ :=
unpad_Dtm_ctx n nil ctx := ctx;
unpad_Dtm_ctx n (τ::l) (HCons h hl) := unpad_Dt n τ h ::: unpad_Dtm_ctx n l hl.

Equations unpad_Dtm_ctx_c n Γ (ctx : ⟦ Dctx_c (Datatypes.S n) Γ ⟧ₜₓ)
  : ⟦ Dctx_c n Γ ⟧ₜₓ :=
unpad_Dtm_ctx_c n nil ctx := ctx;
unpad_Dtm_ctx_c n (τ::l) (HCons h hl) :=
  unpad_Dt_c n τ h ::: unpad_Dtm_ctx_c n l hl.

Equations Dtm_cons n Γ τ (x : ⟦ Dt n τ ⟧ₜ) (xs : ⟦ Dctx n Γ ⟧ₜₓ) :
  ⟦Dctx n (τ::Γ)⟧ₜₓ :=
Dtm_cons n Γ τ x xs := x ::: xs.

Equations Dtm_cons_c n Γ τ (x : ⟦ Dt_c n τ ⟧ₜ) (xs : ⟦ Dctx_c n Γ ⟧ₜₓ) :
  ⟦Dctx_c n (τ::Γ)⟧ₜₓ :=
Dtm_cons_c n Γ τ x xs := x ::: xs.

(* Instantiation here keeps track of how many function arguments
    there are/partial derivs are to be calculated. *)
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
      induction n...
      (* { remember (sb x). dependent destruction d.
        remember (sb_c x). dependent destruction d.
        unfold const.
        induction n... unfold shave_fin.
        apply Vcons_eq. splits. apply IHn.
        dependent destruction H. constructor. } *)
      { apply Vcons_eq. split...
        unfold shave_fin, const.
        eassert (H': (fun (_ : Fin.t n) (_ : ⟦ ℝ ::
          map (Dt_c (Datatypes.S n)) Γ ⟧ₜₓ) => 0) = const (const 0)).
        { extensionality i. extensionality ctx... }
        rewrite_c H'.
        eassert (H': (fun (_ : Fin.t n) (_ : ⟦
          map (Dt (Datatypes.S n)) Γ ⟧ₜₓ) => 0) = const (const 0)).
        { extensionality i. extensionality ctx... }
        rewrite_c H'.
        pose proof (IHn
          (unpad_Dtm_ctx n Γ ∘ sb) (unpad_Dtm_ctx_c n Γ ∘ sb_c)) as IHn.
        (* apply IHn.
        fold const. *)

        (* remember (sb x). dependent destruction d.
        remember (sb_c x). dependent destruction d0.
        dependent destruction n...
        pose proof (IHΓ (denote_ctx_tl ∘ sb) (denote_ctx_tl ∘ sb_c)) as H'.
        unfold compose in H'.
        rewrite <- Heqd in H'.
        rewrite <- Heqd0 in H'...
        apply Vcons_eq' in H'. destruct H' as [Heq1 Heq2].
        apply Vcons_eq. split... *)
        all: admit. } } }
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
        reflexivity. }
    2:{ extensionality i. extensionality ctx. simp denote_tm.
        reflexivity. }
      rewrites.
      induction n...
      eapply Vcons_eq. split...
      { rewrites... }
      { unfold shave_fin...
        admit. } } }
  { (* Mul *)
    simp Dtm Dtm_c.
    pose proof (IHt1 sb sb_c H) as [IHeq1 IHeq1'].
    pose proof (IHt2 sb sb_c H) as [IHeq2 IHeq2'].
    clear IHt1 IHt2.
    simp S in *.
    split; extensionality r;
      eapply equal_f in IHeq1;
      eapply equal_f in IHeq2;
      eapply equal_f in IHeq1';
      eapply equal_f in IHeq2'.
    { simp denote_tm...
      rewrites. }
    { simp denote_tm...
      unfold vector_add, vector_map2...
      simp denote_tm; unfold compose...
      erewrite denote_array_eq...
      erewrite (denote_array_eq (ℝ :: map (Dt_c n) Γ))...
  2:{ extensionality i. extensionality ctx.
      simp denote_tm. rewrite 4 denote_shift.
      simp denote_tm. reflexivity. }
  2:{ extensionality i. extensionality ctx.
      simp denote_tm. unfold vector_map.
      simp denote_tm. unfold compose.
      reflexivity. }
      induction n...
      apply Vcons_eq. splits...
      { unfold shave_fin. simp denote_tm...
        eassert (H':
          (fun i : Fin.t n =>
            ⟦ mul (map (Dt (Datatypes.S n)) Γ)
              (first _ (Dtm _ t2)) (get _ (Fin.FS i)
                (second _ (Dtm _ t1))) ⟧ₜₘ) = _).
        { extensionality i. extensionality ctx. now simp denote_tm. }
        rewrite_c H'...
        eassert (H':
          (fun i : Fin.t n =>
            ⟦ mul (map (Dt (Datatypes.S n)) Γ) (first _ (Dtm _ t1))
              (get _ (Fin.FS i) (second _ (Dtm _ t2))) ⟧ₜₘ) = _).
        { extensionality i. extensionality ctx. now simp denote_tm. }
        rewrite_c H'...
        rewrites. simp denote_v.
        admit. }
      { admit. } } }
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
  induction m...
  { erewrite inst_eq.
  2,3: extensionality x; remember (f x);
      dependent destruction d;
      simp Dtm_ctx Dtm_ctx_c Dtm_ctx' Dtm_ctx_c';
      reflexivity.
    eassert (H: (fun _ : R => HNil) = const HNil)...
    rewrite_c H.
    constructor. }
  { erewrite inst_eq.
    instantiate (2:=fun x => @Dtm_ctx (Datatypes.S m) n
      (HCons (hhd (f x)) (htl (f x))))...
    instantiate (1:=fun x => @Dtm_ctx_c (Datatypes.S m) n
      (HCons (hhd (f x)) (htl (f x))))...
    (* constructor... *)
    all: admit. }
Admitted.

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
