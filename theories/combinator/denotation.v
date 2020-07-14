Require Import Lists.List.
Require Import Coq.Sets.Multiset.
Import ListNotations.
Require Import Coq.Reals.Reals.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Equations.Equations.
Require Import CoLoR.Util.Vector.VecUtil.
Require Vectors.Fin.

Require Import AD.types.
Require Import AD.maps.
Require Import AD.stlc.
Require Import AD.combinator.
Require Import AD.target.

Local Open Scope program_scope.

(* Denotations *)
Notation "'R^' n" := (vector R n) (at level 24).

Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t τ : Set :=
  match τ with
  | ℝ => R
  | ℝ^n => vector R n
  | Unit => unit
  | τ1 × τ2 => ⟦τ1⟧ₜ * ⟦τ2⟧ₜ
  | τ1 → τ2 => ⟦τ1⟧ₜ -> ⟦τ2⟧ₜ
  end
where "⟦ τ ⟧ₜ" := (denote_t τ).

Reserved Notation "⟦ t ⟧ₒ".
Fixpoint denote_comb {τ σ} (c : comb τ σ): ⟦τ⟧ₜ -> ⟦σ⟧ₜ :=
  match c with
(* denote_comb c x with c := { *)
  | @id τ => fun x => x
  | @seq τ σ ρ t1 t2 => fun x => ⟦t2⟧ₒ (⟦t1⟧ₒ x)

  (* Monoidal *)
  | @cross τ σ ρ φ t1 t2 => fun x => (⟦t1⟧ₒ (fst x), ⟦t2⟧ₒ (snd x))

  (* Terminal *)
  | @neg τ => fun x => tt

  (* Cartesian *)
  | @exl τ σ => fun x => fst x
  | @exr τ σ => fun x => snd x
  | @dupl τ => fun x => (x, x)

  (* Closed *)
  | @ev τ σ => fun x => (fst x) (snd x)
  | @curry τ σ ρ t' => fun x => fun y => ⟦t'⟧ₒ (x, y)

  (* Const *)
  (* | cnst t => _ *)

  (* Numeric *)
  | cplus => fun x => Rplus (fst x) (snd x)
  | crval r => fun x => r

  | cmplus => fun x => Vmap2 Rplus (fst x) (snd x)
  | cmrval r => fun x => r
 end
where "⟦ s ⟧ₒ" := (denote_comb s).

Reserved Notation "⟦ Γ ⟧ₜₓ".
Fixpoint denote_ctx Γ : Type :=
  match Γ with
  | nil => unit
  | τ :: Γ' => (⟦τ⟧ₜ * ⟦Γ'⟧ₜₓ)
  end
where "⟦ Γ ⟧ₜₓ" := (denote_ctx Γ).

Reserved Notation "⟦ v ⟧ᵥ".
Fixpoint denote_v {τ Γ} (v : τ ∈ Γ) : ⟦ Γ ⟧ₜₓ -> ⟦ τ ⟧ₜ :=
  match v with
  | Top => fun xs => fst xs
  | Pop v' => fun xs => ⟦ v' ⟧ᵥ (snd xs)
  end
where "⟦ v ⟧ᵥ" := (denote_v v).

Reserved Notation "⟦ t ⟧ₜₘ".
Fixpoint denote_tm {Γ τ} (t : tm Γ τ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ :=
  match t with
  (* Base *)
  | var _ v => fun xs => ⟦ v ⟧ᵥ xs
  | app _ t1 t2 => fun xs => (⟦ t1 ⟧ₜₘ xs) (⟦ t2 ⟧ₜₘ xs)
  | abs _ t => fun xs x => (⟦ t ⟧ₜₘ (x, xs))

  (* Products *)
  | tuple _ t1 t2 => fun xs => (⟦ t1 ⟧ₜₘ xs, ⟦ t2 ⟧ₜₘ xs)
  | first _ t => fun xs => fst (⟦ t ⟧ₜₘ xs)
  | second _ t => fun xs => snd (⟦ t ⟧ₜₘ xs)

  (* Reals *)
  | plus _ t1 t2 => fun xs => Rplus (⟦ t1 ⟧ₜₘ xs) (⟦ t2 ⟧ₜₘ xs)
  | rval _ r => fun _ => r

  | mplus _ t1 t2 => fun xs => Vmap2 Rplus (⟦ t1 ⟧ₜₘ xs) (⟦ t2 ⟧ₜₘ xs)
  | mrval _ r => fun _ => r

  (* Unit *)
  | it _ => fun _ => tt
  end
where "⟦ t ⟧ₜₘ" := (denote_tm t).

(* Helper functions *)
Definition vector_mul {n} : vector R n -> vector R n -> vector R n
  := Vmap2 (n:=n) Rmult.
Definition vector_plus {n} : vector R n -> vector R n -> vector R n
  := Vmap2 (n:=n) Rplus.
Definition dot_product {n} : vector R n -> vector R n -> R
  := fun x y => Vfold_left Rplus 0%R (vector_mul x y).
Definition vector_sum {n} : vector R n -> R
  := fun x => Vfold_left Rplus 0%R x.
Definition shave_fin {A n} (f : Fin.t (S n) -> A) : Fin.t n -> A :=
  fun i => f (Fin.FS i).
Definition shave_Rn {A n} (f : R^(S n) -> A) : R^n -> A :=
  fun i => f (Vcons 0%R i).

(* Helper function for creating one-hot encoding vectors with variable start
    indices *)
Equations vector_one_hot' (j i n : nat) : vector R n  :=
vector_one_hot' j i 0 := Vnil;
vector_one_hot' j i (S n') :=
  Vcons (if Nat.eqb i j then 1 else 0)%R (vector_one_hot' (S j) i n').

(* Create a one-hot encoding of length n with the one at position i *)
Equations vector_one_hot (i n : nat) : vector R n :=
vector_one_hot i n := vector_one_hot' 0 i n.

Fixpoint vector_nth {s : Set} {n}
  (i : Fin.t n) : vector s n -> s :=
  match i with
  | @Fin.F1 _    => fun ar => Vhead ar
  | @Fin.FS _ i' => fun ar => vector_nth i' (Vtail ar)
  end.

Reserved Notation "⟦ τ ⟧ₛₜ".
Fixpoint denote_st (τ : s_ty) : Type :=
  match τ with
  | sℝ => R
  | sℝ^n => vector R n
  | s_Unit => unit
  | τ1 s× τ2 => ⟦τ1⟧ₛₜ * ⟦τ2⟧ₛₜ
  | τ1 s→ τ2 => ⟦τ1⟧ₛₜ -> ⟦τ2⟧ₛₜ
  | σ <x> ρ => Mset.type (⟦σ⟧ₛₜ * ⟦ρ⟧ₛₜ)
  end
where "⟦ τ ⟧ₛₜ" := (denote_st τ).

Definition from_option {A} (o : option A) (default : A) : A :=
  match o with
  | None => default
  | Some o' => o'
  end.

Fixpoint denote_O τ : ⟦τ⟧ₛₜ :=
  match τ with
  | sℝ => 0%R
  | sℝ^n => Vbuild (fun _ _ => 0%R)
  | s_Unit => tt
  | τ1 s× τ2 => (denote_O τ1, denote_O τ2)
  | τ1 s→ τ2 => fun _ => denote_O τ2
  | σ <x> ρ => (EmptyBag _, [])
  end.

Fixpoint denote_plus τ : ⟦τ⟧ₛₜ -> ⟦τ⟧ₛₜ -> ⟦τ⟧ₛₜ :=
  match τ with
  | sℝ => fun t1 t2 => Rplus t1 t2
  | sℝ^n => fun t1 t2 => vector_plus t1 t2
  | s_Unit => fun t1 t2 => tt
  | τ1 s× τ2 => fun t1 t2 => (denote_plus _ (fst t1) (fst t2)
                  , denote_plus _ (snd t1) (snd t2))
  | τ1 s→ τ2 => fun t1 t2 => fun x => denote_plus _ (t1 x) (t2 x)
  | σ <x> ρ => fun t1 t2 =>
    (munion (fst t1) (fst t2), snd t1 ++ snd t2)
    (* combine s_ty denote_st eq_denote_t
      (fun τ x => denote_plus τ (fst x) (snd x))
      (denote_O ρ) t1 t2 *)
  end.

Definition Reqb :
  forall (x y : R), bool.
  Admitted.
Axiom Reqb_eq : forall x y, Reqb x y = true <-> x = y.
Axiom Reqb_eqdec : forall (x y : R), { x = y } + { ~ x = y }.

Lemma denote_eqdec : forall τ (x y : ⟦ τ ⟧ₛₜ),
  {eq x y} + {~eq x y}.
Proof.
  intros.
  dependent induction τ.
  { eapply Vector.eq_dec.
    intros. apply Reqb_eq. }
  { apply Reqb_eqdec. }
  { destruct x; destruct y.
    admit. }
  { admit. }
Admitted.

Reserved Notation "⟦ t ⟧ₜₒ".
Fixpoint denote_target {τ σ} (c : target τ σ): ⟦τ⟧ₛₜ -> ⟦σ⟧ₛₜ :=
  match c with
(* denote_target c x with c := { *)
  | @t_id τ => fun x => x
  | @t_seq τ σ ρ t1 t2 => fun x => ⟦t2⟧ₜₒ (⟦t1⟧ₜₒ x)

  (* Monoidal *)
  | @t_cross τ σ ρ φ t1 t2 => fun x => (⟦t1⟧ₜₒ (fst x), ⟦t2⟧ₜₒ (snd x))

  (* Terminal *)
  | @t_neg τ => fun x => tt

  (* Cartesian *)
  | @t_exl τ σ => fun x => fst x
  | @t_exr τ σ => fun x => snd x
  | @t_dupl τ => fun x => (x, x)

  (* Closed *)
  | @t_ev τ σ => fun x => (fst x) (snd x)
  | @t_curry τ σ ρ t' => fun x => fun y => ⟦t'⟧ₜₒ (x, y)

  (* Numeric *)
  | t_cplus => fun x => Rplus (fst x) (snd x)
  | t_crval r => fun x => r

  | t_cmplus => fun x => Vmap2 Rplus (fst x) (snd x)
  | t_cmrval r => fun x => r

  (* Maps *)
  | @t_mempty τ σ => fun x => (EmptyBag _, [])
  | @t_msingleton τ σ => fun x =>
    (@SingletonBag _ eq (denote_eqdec _) x, x::nil)
  | @t_mplus τ σ => fun x =>
    (munion (fst (fst x)) (fst (snd x)), snd (fst x) ++ snd (snd x))
  | @t_mfold τ σ ρ => fun x =>
    fold_left
      (fun (a : ⟦ρ⟧ₛₜ) (b : ⟦τ⟧ₛₜ * ⟦σ⟧ₛₜ) =>
        denote_plus ρ (snd x b) a)
      (snd (fst x)) (denote_O ρ)
  end
where "⟦ s ⟧ₜₒ" := (denote_target s).
