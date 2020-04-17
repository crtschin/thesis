Require Import Lists.List.
Require Import Vectors.Fin.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.
Require Import Strings.String.
Require Import Relations.
Require Import Logic.JMeq.
Require Import Reals.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Coquelicot.Derive.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Equations.Equations.
Import EqNotations.

Require Import AD.Definitions.
Require Import AD.Macro.
(* Require AD.DepList. *)
Require Import AD.Tactics.
(* Require Import AD.Normalization. *)

Local Open Scope program_scope.

(* Notations:

  ⟦ τ ⟧ₜ := denote_t τ, Currently piggybacks off of Coq's types.
  ⟦ Γ ⟧ₜₓ := denote_ctx Γ, A product list of types ensured to exist
                          in the context Γ.
  ⟦ v ⟧ₜₓ := denote_v v, A projection of the product list denoted by the typing
                        context relevant to the variable referenced by v
  ⟦ t ⟧ₜₘ := denote_tm t, Gives a function f of t such that it has the correct
                          denoted type of τ given the denoted context of Γ.
*)

(*
  Goal: Write out the logical relation over types with the goal of having both
    the proof of differentiability and witness in one.
*)

(*
Agda-style generics
*)

(* Inductive Functor : Type :=
  | Id : Functor
  | K : Set -> Functor
  | Fprod : Functor -> Functor -> Functor
  | Fadd : Functor -> Functor -> Functor.

Fixpoint denote_functor (f : Functor): Set -> Set :=
  fun s => match f with
  | Id => s
  | K a => a
  | Fprod a b => prod (denote_functor a s) (denote_functor b s)
  | Fadd a b => sum (denote_functor a s) (denote_functor b s)
  end.
Notation "⟦ f ⟧₋" := (denote_functor f). *)

(* Inductive Fixed F : Set :=
  | unfix : ⟦ F ⟧₋ (Fixed F) -> Fixed F
. *)

(*
  CPDT-style universe types
*)

(* Record constructor : Type := Con {
  nonrecursive : Type;
  recursive : nat;
}.
Definition datatype := list constructor.
Section denote.
  Variable T : Type.
  Definition denote_constructor (c : constructor) :=
    nonrecursive c -> ilist T (recursive c) -> T.
  Definition denote_datatype := hlist denote_constructor.
End denote.
Notation "[ v , r ~> x ]" := ((fun v r => x) : denote_constructor _ (Con _ _)).

Definition Empty_set_dt : datatype := nil.
Definition unit_dt : datatype := Con unit 0 :: nil.
Definition bool_dt : datatype := Con unit 0 :: Con unit 0 :: nil.
Definition nat_dt : datatype := Con unit 0 :: Con unit 1 :: nil.
Definition list_dt (A : Type) : datatype := Con unit 0 :: Con A 1 :: nil.
Definition reals_dt : datatype := Con R 0 :: nil.
Definition fn_dt (A : Type) (B : Type) : datatype := Con (A -> B) 0 :: nil.
Definition prod_dt (A : Type) (B : Type) : datatype := Con (A * B) 0 :: nil.
Definition sum_dt (A : Type) (B : Type) : datatype := Con A 0 :: Con B 0 :: nil.
Definition functor_dt (A : Type) (B : Type) : datatype :=
  Con R 0 :: Con A 0 :: Con B 0 ::Con (A -> B) 0 :: Con (A * B) 0 :: nil.

Definition Empty_set_den : denote_datatype Empty_set Empty_set_dt :=
  HNil.
Definition unit_den : denote_datatype unit unit_dt :=
  [_, _ ~> tt] ::: HNil.
Definition bool_den : denote_datatype bool bool_dt :=
  [_, _ ~> true] ::: [_, _ ~> false] ::: HNil.
Definition nat_den : denote_datatype nat nat_dt :=
  [_, _ ~> O] ::: [_, r ~> S (hd r)] ::: HNil.
Definition list_den (A : Type) : denote_datatype (list A) (list_dt A) :=
  [_, _ ~> nil] ::: [x, r ~> x :: hd r] ::: HNil.
Definition reals_den : denote_datatype R reals_dt :=
  [a, r ~> a] ::: HNil.
Definition prod_den (A : Type) (B : Type) : denote_datatype
  (A * B) (prod_dt A B) :=
  [a, r ~> a] ::: HNil.
Definition fn_den (A : Type) (B : Type) : denote_datatype
  (A -> B) (fn_dt A B) :=
  [a, r ~> a] ::: HNil.
Definition sum_den (A : Type) (B : Type) : denote_datatype
  (sum A B) (sum_dt A B) :=
  [a, r ~> Datatypes.inl a] ::: [a, r ~> Datatypes.inr a] ::: HNil.

Definition fix_denote (T : Type) (dt : datatype) :=
  forall (R : Type), denote_datatype R dt -> (T -> R). *)

(* Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t τ : datatype :=
  match τ with
  | Real => reals_dt
  | τ1 × τ2 => prod_dt (denote_datatype' ⟦τ1⟧ₜ) (denote_datatype' ⟦τ2⟧ₜ)
  | τ1 → τ2 => fn_dt (denote_datatype' ⟦τ1⟧ₜ) (denote_datatype' ⟦τ2⟧ₜ)
  | τ1 <+> τ2 => sum_dt (denote_datatype' ⟦τ1⟧ₜ) (denote_datatype' ⟦τ2⟧ₜ)
  end
with denote_datatype' (d : datatype) : Type :=
  match d with
  | [] => unit
  | h :: f => denote_constructor _ h * denote_datatype f
  end
where "⟦ τ ⟧ₜ" := (denote_t τ). *)

Fixpoint denote_array_type n (s : Set) : Set :=
  match n with
  | O => unit
  | S n => s * denote_array_type n s
  end.

Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t τ : Set :=
  match τ with
  | Real => R
  | Array n τ => denote_array_type n ⟦ τ ⟧ₜ
  | τ1 × τ2 => ⟦τ1⟧ₜ * ⟦τ2⟧ₜ
  | τ1 → τ2 => ⟦τ1⟧ₜ -> ⟦τ2⟧ₜ
  | τ1 <+> τ2 => ⟦τ1⟧ₜ + ⟦τ2⟧ₜ
  end
where "⟦ τ ⟧ₜ" := (denote_t τ).

Reserved Notation "⟦ Γ ⟧ₜₓ".
Fixpoint denote_ctx (Γ : Ctx) : Type :=
  match Γ with
  | [] => unit
  | h :: t => ⟦h⟧ₜ * ⟦t⟧ₜₓ
  end
where "⟦ Γ ⟧ₜₓ" := (denote_ctx Γ).

Fixpoint denote_v {Γ τ} (v: τ ∈ Γ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ  :=
  match v with
  | Top Γ' τ' => fun gamma => fst gamma
  | Pop Γ' τ' σ x => fun gamma => denote_v x (snd gamma)
  end.
Notation "⟦ v ⟧ᵥ" := (denote_v v).

Equations denote_idx {s : Set} {n}
  (i : Fin.t n) : denote_array_type n s -> s :=
denote_idx (@F1 n)    ar => fst ar;
denote_idx (@FS n i') ar => denote_idx i' (snd ar).

Equations nat_to_fin n : Fin.t (S n) :=
nat_to_fin 0 := F1;
nat_to_fin (S n) := FS (nat_to_fin n).

Reserved Notation "⟦ t ⟧ₜₘ".
Fixpoint denote_tm {Γ τ} (t : tm Γ τ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ :=
  match t with
  (* Base STLC *)
  | var σ v => fun ctx => denote_v v ctx
  | app σ ρ t1 t2 => fun ctx => (⟦t1⟧ₜₘ ctx) (⟦t2⟧ₜₘ ctx)
  | abs σ ρ f => fun ctx => fun x => ⟦ f ⟧ₜₘ (x, ctx)

  (* STLC extra *)
  (* Non-recursive let-bindings *)
  | letn σ ρ t b => fun ctx => ⟦ b ⟧ₜₘ (⟦ t ⟧ₜₘ ctx, ctx)

  (* Arrays *)
  (* | build_nil σ => fun ctx => tt *)
  | build σ n f => fun ctx => denote_array (nat_to_fin n) f ctx
  | get σ n i t => fun ctx => denote_idx i (⟦ t ⟧ₜₘ ctx)

  (* Reals *)
  | rval r => fun ctx => r
  | add t1 t2 => fun ctx => ⟦t1⟧ₜₘ ctx + ⟦t2⟧ₜₘ ctx

  (* Products *)
  | tuple σ ρ t1 t2 => fun ctx => (⟦t1⟧ₜₘ ctx, ⟦t2⟧ₜₘ ctx)
  | first σ ρ t => fun ctx => fst (⟦t⟧ₜₘ ctx)
  | second σ ρ t => fun ctx => snd (⟦t⟧ₜₘ ctx)

  (* Sums *)
  | case τ σ ρ e c1 c2 => fun ctx =>
    match (⟦e⟧ₜₘ ctx) with
    | Datatypes.inl x => (⟦c1⟧ₜₘ ctx) x
    | Datatypes.inr x => (⟦c2⟧ₜₘ ctx) x
    end
  | inl τ σ e => fun ctx => Datatypes.inl (⟦e⟧ₜₘ ctx)
  | inr τ σ e => fun ctx => Datatypes.inr (⟦e⟧ₜₘ ctx)
  end
with denote_array {Γ τ n} (i : Fin.t (S n)) (f : Fin.t n -> tm Γ τ)
  : ⟦Γ⟧ₜₓ -> ⟦Array n τ⟧ₜ :=
  fun ctx =>
  match i with
  | F1 n' => ⟦ f F1 ⟧ₜₘ ctx
  | FS n' i' => (⟦ f (FS i') ⟧ₜₘ ctx, (denote_array i' f) ctx)
  end
where "⟦ t ⟧ₜₘ" := (denote_tm t).

Equations denote_env {Γ} (G : Env Γ): ⟦ Γ ⟧ₜₓ :=
denote_env env_nil => tt;
denote_env (env_cons t G') with denote_env G' => {
  denote_env (env_cons t G') X => (⟦ t ⟧ₜₘ X, X)
}.
Notation "⟦ s ⟧ₑ" := (denote_env s).

Fixpoint denote_sub {Γ Γ'}: sub Γ Γ' -> denote_ctx Γ' -> denote_ctx Γ :=
  match Γ with
  | [] => fun s ctx => tt
  | h :: t => fun s ctx =>
      (denote_tm (hd_sub s) ctx, denote_sub (tl_sub s) ctx)
  end.
Notation "⟦ s ⟧ₛ" := (denote_sub s).

Fixpoint denote_ren {Γ Γ'}: ren Γ Γ' -> denote_ctx Γ' -> denote_ctx Γ :=
  match Γ with
  | [] => fun r ctx => tt
  | h :: t => fun r ctx =>
      (denote_tm (hd_ren r) ctx, denote_ren (tl_ren r) ctx)
  end.
Notation "⟦ r ⟧ᵣ" := (denote_ren r).

(* Lemmas for renaming and substitution in the denotated context. *)
(* Many from Strongly Typed Terms in Coq by Nick Becton, et al. *)
(* Lemma denote_shave_env_snd : forall τ Γ (e : Env τ (τ::Γ)),
  snd ⟦ e ⟧ₑ = ⟦ shave_env e ⟧ₑ.
Proof with quick.
  dependent induction e.
  simp shave_env.
  simp denote_env...
Qed.

Lemma Ddenote_shave_env_snd : forall τ Γ (e : Env τ (τ::Γ)),
  snd ⟦ Denv e ⟧ₑ = ⟦ Denv (shave_env e) ⟧ₑ.
Proof with quick.
  dependent induction e.
  simp shave_env.
  simp denote_env...
Qed. *)

Lemma denote_ren_elim : forall Γ Γ' τ
  (r : ren Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  denote_ren r ctx = denote_ren (tl_ren (rename_lifted r)) (x, ctx).
Proof with eauto.
  induction Γ...
  intros. specialize IHΓ with (r:=tl_ren r).
  simpl. rewrite IHΓ with (x:=x)...
Qed.

Lemma denote_ren_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (r : ren Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (denote_ren r ctx) = ⟦ rename r t ⟧ₜₘ ctx.
Proof with quick.
  intros. generalize dependent Γ'.
  induction t; quick; rewrites...
  { induction v... rewrite IHv... }
  { specialize IHt with (r:=rename_lifted r).
    simpl in IHt. simp rename_lifted in IHt.
    apply functional_extensionality...
    rewrite <- IHt...
    rewrite <- denote_ren_elim... }
  { specialize IHt1 with Γ' r ctx.
    specialize IHt2 with (σ::Γ') (rename_lifted r) (⟦ rename r t1 ⟧ₜₘ ctx, ctx).
    erewrite denote_ren_elim... }
Qed.

Lemma denote_ren_shift : forall Γ Γ' τ (r:ren Γ Γ'),
  denote_ren (fun _ v => Pop _ _ τ (r _ v)) =
    fun se => denote_ren r (snd se).
Proof with quick.
  induction Γ... extensionality ctx.
  apply injective_projections...
  unfold tl_ren. rewrite IHΓ...
Qed.

Lemma denote_ren_id : forall Γ,
  denote_ren (@id_ren Γ) = Datatypes.id.
Proof with quick.
  intros. extensionality x.
  dependent induction Γ... destruct x...
  destruct x...
  apply injective_projections...
  unfold tl_ren, id_ren in *...
  rewrite denote_ren_shift...
Qed.

Lemma denote_shift : forall Γ τ σ (t : tm Γ τ) ctx,
    ⟦ shift (σ:=σ) t ⟧ₜₘ ctx = ⟦ t ⟧ₜₘ (snd ctx).
Proof with eauto.
  unfold shift. intros.
  rewrite <- denote_ren_commutes...
  pose proof denote_ren_elim as H.
  destruct ctx as [x ctx].
  specialize H with Γ Γ σ (fun t x => x) x ctx.
  unfold tl_ren in H.
  assert (H':
    (fun (σ0 : ty) (x : σ0 ∈ Γ) =>
       rename_lifted (fun (t : ty) (x0 : t ∈ Γ) => x0) σ0 (Pop Γ σ0 σ x)) =
    (fun (ρ : ty) (x0 : ρ ∈ Γ) => Pop Γ ρ σ x0)).
  { apply functional_extensionality_dep... }
  rewrite <- H'. rewrite <- H.
  fold (@id_ren Γ). rewrite denote_ren_commutes.
  rewrite app_ren_id...
Qed.

Lemma denote_sub_elim : forall Γ Γ' τ
  (s : sub Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  denote_sub s ctx = denote_sub (tl_sub (substitute_lifted s)) (x, ctx).
Proof with eauto.
  induction Γ; intros...
  intros. specialize IHΓ with (s := (tl_sub s)).
  simpl. rewrite IHΓ with (x := x).
  unfold hd_sub. unfold tl_sub. simp substitute_lifted.
  erewrite denote_shift...
Qed.

Lemma denote_sub_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (s : sub Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (denote_sub s ctx) = ⟦ substitute s t ⟧ₜₘ ctx.
Proof with quick.
  intros. generalize dependent Γ'.
  induction t; intros; rewrites...
  { simpl. induction v...
    intros. simpl. rewrite IHv... }
  { specialize IHt with (s:=substitute_lifted s)...
    apply functional_extensionality...
    rewrite <- IHt...
    erewrite denote_sub_elim... }
  { specialize IHt1 with Γ' s ctx.
    specialize IHt2 with (σ::Γ') (substitute_lifted s)
      (⟦ substitute s t1 ⟧ₜₘ ctx, ctx).
    erewrite denote_sub_elim... }
Qed.

Lemma denote_sub_id : forall Γ τ (t : tm Γ τ) (ctx : ⟦ Γ ⟧ₜₓ),
  ⟦ t ⟧ₜₘ (denote_sub id_sub ctx) = ⟦ t ⟧ₜₘ ctx.
Proof with quick.
  intros.
  rewrite denote_sub_commutes...
  rewrite app_sub_id...
Qed.

Lemma denote_sub_shift : forall Γ Γ' σ (s:sub Γ Γ'),
  denote_sub (fun _ v => shift (σ:=σ) (s _ v)) =
    fun ctx => denote_sub s (snd ctx).
Proof with quick.
  induction Γ... extensionality ctx.
  apply injective_projections...
  { unfold hd_sub. rewrite denote_shift... }
  { unfold tl_sub. rewrite IHΓ... }
Qed.

Lemma denote_sub_tl_simpl : forall Γ Γ' τ (ctx : ⟦ Γ' ⟧ₜₓ) (s : sub (τ::Γ) Γ'),
  ⟦ tl_sub s ⟧ₛ ctx = snd (⟦ s ⟧ₛ ctx).
Proof with quick.
  intros...
Qed.

(* Lemma denote_sub_id_ctx : forall Γ (ctx : ⟦Γ⟧ₜₓ),
  denote_sub id_sub ctx = ctx.
Proof with quick.
  induction Γ.
  { simpl denote_sub. destruct ctx... }
  { simpl denote_sub. destruct ctx...
    apply injective_projections...
    rewrite denote_sub_tl_simpl.
    (* eapply IHΓ. *)
    assert (⟦ @id_sub (a::Γ) ⟧ₛ (d, d0) = (d, d0)).
    { rewrites. admit. }
    rewrite H... }
Admitted.

Lemma denote_sub_tl_snd : forall Γ τ ctx,
  ⟦ tl_sub (Γ:=Γ) (τ:=τ) id_sub ⟧ₛ ctx = snd ctx.
Proof with quick.
  (* pose proof (tl_sub (Γ:=Γ) (τ:=τ) id_sub). *)
  induction Γ...
  { destruct ctx... destruct u... }
  { destruct ctx...
    destruct p... apply injective_projections...
    rewrite denote_sub_tl_simpl.
    rewrite denote_sub_tl_simpl.
    rewrite denote_sub_id_ctx... }
Admitted. *)

Lemma denote_sub_tl_cons :
  forall Γ Γ' τ (t : tm Γ' τ) ctx (sb : sub Γ Γ'),
  denote_sub (tl_sub (cons_sub t sb)) ctx = denote_sub sb ctx.
Proof with quick.
  intros.
  unfold id_sub.
  rewrite tl_cons_sub.
  fold (@id_sub Γ)...
Qed.

Theorem soundness : forall τ (t t' : tm [] τ),
  (t -->* t') -> ⟦t⟧ₜₘ = ⟦t'⟧ₜₘ.
Proof with quick.
  intros.
  induction H...
  rewrite <- IHmulti.
  dependent induction H;
    extensionality ctx; quick;
    try (erewrite IHstep; constructor)...
  { rewrite <- denote_sub_commutes...
    unfold hd_sub. simp cons_sub.
    destruct ctx... }
  { erewrite <- (IHstep t2 t2' t2')...
    constructor. }
Qed.

(* Program Fixpoint Ddenote_sub {Γ Γ'}
  : sub Γ Γ' -> denote_ctx (Dctx Γ') -> denote_ctx (Dctx Γ) :=
  match Γ with
  | [] => fun s ctx => tt
  | h :: t => fun s ctx =>
      (denote_tm (Dtm (hd_sub s)) ctx, Ddenote_sub (tl_sub s) ctx)
  end.
Notation "⟦ s ⟧ₛₛ" := (Ddenote_sub s).

Program Fixpoint Ddenote_ren {Γ Γ'}
  : ren Γ Γ' -> denote_ctx (Dctx Γ') -> denote_ctx (Dctx Γ) :=
  match Γ with
  | [] => fun r ctx => tt
  | h :: t => fun r ctx =>
      (denote_tm (Dtm (hd_ren r)) ctx, Ddenote_ren (tl_ren r) ctx)
  end.
Notation "⟦ r ⟧ᵣ" := (denote_ren r).

Lemma Ddenote_ren_elim : forall Γ Γ' τ
  (r : ren Γ Γ') (x : ⟦ Dt τ ⟧ₜ) (ctx : ⟦ Dctx Γ' ⟧ₜₓ),
  Ddenote_ren r ctx = Ddenote_ren (tl_ren (rename_lifted r)) (x, ctx).
Proof with eauto.
  induction Γ...
  intros. specialize IHΓ with (r:=tl_ren r).
  simpl. rewrite IHΓ with (x:=x)...
Qed.

Lemma Ddenote_ren_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (r : ren Γ Γ') (ctx : ⟦ Dctx Γ' ⟧ₜₓ),
    ⟦ Dtm t ⟧ₜₘ (Ddenote_ren r ctx) = ⟦ Dtm (rename r t) ⟧ₜₘ ctx.
Proof with quick.
  intros. generalize dependent Γ'.
  induction t; quick; simp Dtm; rewrites...
  { induction v... simp Dtm. }
  { specialize IHt with (r:=rename_lifted r).
    simpl in IHt. simp rename_lifted in IHt.
    apply functional_extensionality...
    rewrite <- IHt...
    rewrite <- Ddenote_ren_elim... }
Qed. *)

(* Lemma Ddenote_shift : forall Γ τ σ (t : tm Γ τ) ctx,
    ⟦ Dtm (shift (σ:=σ) t) ⟧ₜₘ ctx = ⟦ Dtm t ⟧ₜₘ (snd ctx).
Proof with quick.
  unfold shift. intros.
  rewrite <- Ddenote_ren_commutes...
  pose proof Ddenote_ren_elim as H.
  destruct ctx as [x ctx]...
  specialize H with Γ Γ σ id_ren x ctx.
  rewrite lift_ren_id in *.
  assert (H': tl_ren id_ren = (fun (ρ : ty) (x : ρ ∈ Γ) => Pop Γ ρ σ x)).
  { apply functional_extensionality_dep... }
  rewrite <- H'; clear H'.
  (* rewrite H. *)
  (* rewrite Ddenote_ren_commutes. *)
Admitted.

Lemma Ddenote_sub_elim : forall Γ Γ' τ
  (s : sub Γ Γ') (x : ⟦ Dt τ ⟧ₜ) (ctx : ⟦ Dctx Γ' ⟧ₜₓ),
  Ddenote_sub s ctx = Ddenote_sub (tl_sub (substitute_lifted s)) (x, ctx).
Proof with quick.
  induction Γ; intros...
  intros. specialize IHΓ with (s := (tl_sub s)).
  simpl. rewrite IHΓ with (x := x).
  unfold hd_sub. unfold tl_sub. simp substitute_lifted...
  apply injective_projections...
  pose proof Ddenote_shift as H.
  (* rewrite H. *)
  admit.
Admitted.

Lemma Ddenote_sub_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (s : sub Γ Γ') (ctx : ⟦ Dctx Γ' ⟧ₜₓ),
    ⟦ Dsubstitute s t ⟧ₜₘ ctx = ⟦ Dtm t ⟧ₜₘ (Ddenote_sub s ctx).
Proof with quick.
  intros Γ Γ' τ t.
  generalize dependent Γ'.
  induction t; quick; simp Dtm Dsubstitute; rewrites.
  { induction v; quick; rewrite <- IHv... }
  { fold denote_t. extensionality x.
    specialize IHt with (σ::Γ') (substitute_lifted s) (x, ctx).
    (* rewrite IHt. *)
    (* erewrite Ddenote_sub_elim...  *)
    admit.
    }
Admitted. *)