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
Require Import Equations.CoreTactics.
Require Import Equations.Equations.
Import EqNotations.

Require Import AD.DepList.
Require Import AD.vect.
Require Import CoLoR.Util.Vector.VecUtil.
Require Import AD.Definitions.
Require Import AD.Macro.
Require Import AD.Tactics.

Local Open Scope program_scope.

(* Notations:
  ⟦ τ ⟧ₜ := denote_t τ, Currently piggybacks off of Coq's types.
  ⟦ Γ ⟧ₜₓ := denote_ctx Γ, A heterogeneous list of types ensured to exist
                          in the context Γ w.r.t. denote_t.
  ⟦ v ⟧ₜₓ := denote_v v, A projection of the product list denoted by the typing
                          context relevant to the variable referenced by v
  ⟦ t ⟧ₜₘ := denote_tm t, Gives a function f of t such that it has the correct
                          denoted type of τ given the denoted context of Γ.
*)

Reserved Notation "⟦ τ ⟧ₜ".
Fixpoint denote_t τ : Set :=
  match τ with
  | Real => R
  | Nat => nat
  | Array n τ => vector ⟦ τ ⟧ₜ n
  | τ1 × τ2 => ⟦τ1⟧ₜ * ⟦τ2⟧ₜ
  | τ1 → τ2 => ⟦τ1⟧ₜ -> ⟦τ2⟧ₜ
  | τ1 <+> τ2 => ⟦τ1⟧ₜ + ⟦τ2⟧ₜ
  end
where "⟦ τ ⟧ₜ" := (denote_t τ).

(* Given a substitution from Γ to Γ', one is able to transform
    a heterogeneous list of type Γ' to Γ.

    Intuitively:
    A substitution 'uses up' types in the context by swapping
    it out for the appropriate terms, so we add the denotations
    of those same terms to the heterogeneous list Γ' to get Γ.
*)
Definition denote_ctx (Γ : Ctx) := hlist denote_t Γ.
Notation "⟦ Γ ⟧ₜₓ" := (denote_ctx Γ).
Derive Signature for hlist.
Definition denote_ctx_hd {Γ : Ctx} (l : hlist denote_t Γ):= hhd l.
Definition denote_ctx_tl {Γ : Ctx} (l : hlist denote_t Γ):= htl l.
Definition denote_ctx_cons {Γ τ} t
  (l : hlist denote_t Γ):= @HCons ty denote_t τ Γ t l.

Lemma denote_ctx_eq :
  forall (Γ : Ctx) (τ : ty) (h h' : ⟦ τ ⟧ₜ) (t t' : hlist denote_t Γ),
  h = h' -> t = t' -> h ::: t = h' ::: t'.
Proof. intros; rewrites. Qed.

Equations denote_v {Γ τ} (v: τ ∈ Γ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ :=
denote_v (Top Γ τ) (HCons h t) := h;
denote_v (Pop Γ τ σ v) (HCons h t) := denote_v v t.
Notation "⟦ v ⟧ᵥ" := (denote_v v).

Fixpoint vector_nth {s : Set} {n}
  (i : Fin.t n) : vector s n -> s :=
  match i with
  | @F1 _    => fun ar => Vhead ar
  | @FS _ i' => fun ar => vector_nth i' (Vtail ar)
  end.

Fixpoint nat_to_fin n : Fin.t (S n) :=
  match n with
  | 0 => F1
  | S n' => F1
  end.

Definition shave_fin {A n} (f : Fin.t (S n) -> A) : Fin.t n -> A :=
  fun i => f (FS i).

Fixpoint iterate {A} (n : nat) (f : A -> A) (a : A) :=
  match n with
  | 0 => a
  | S n => f (iterate n f a)
  end.

Reserved Notation "⟦ t ⟧ₜₘ".
Equations denote_tm {Γ τ} (t : tm Γ τ) : ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ := {
(* STLC *)
denote_tm (Γ:=Γ) (τ:=τ) (var Γ τ v) ctx := denote_v v ctx;
denote_tm (Γ:=Γ) (τ:=τ) (app Γ τ σ t1 t2) ctx := (⟦t1⟧ₜₘ ctx) (⟦t2⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (abs Γ τ σ f) ctx := fun x => ⟦ f ⟧ₜₘ (x ::: ctx);
(* Arrays *)
denote_tm (Γ:=Γ) (τ:=τ) (build Γ τ n f) ctx :=
  denote_array n (denote_tm ∘ f) ctx;
denote_tm (Γ:=Γ) (τ:=τ) (get Γ i ta) ctx := vector_nth i (⟦ ta ⟧ₜₘ ctx);
(* Nat *)
denote_tm (Γ:=Γ) (τ:=τ) (nval Γ n) ctx := n;
denote_tm (Γ:=Γ) (τ:=τ) (nsucc Γ t) ctx := Datatypes.S (⟦t⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (nrec Γ τ tf ti ta) ctx :=
  iterate (⟦ ti ⟧ₜₘ ctx) (⟦ tf ⟧ₜₘ ctx) (⟦ ta ⟧ₜₘ ctx);
(* Reals *)
denote_tm (Γ:=Γ) (τ:=τ) (rval Γ r) ctx := r;
denote_tm (Γ:=Γ) (τ:=τ) (add Γ t1 t2) ctx := ⟦t1⟧ₜₘ ctx + ⟦t2⟧ₜₘ ctx;
denote_tm (Γ:=Γ) (τ:=τ) (mul Γ t1 t2) ctx := ⟦t1⟧ₜₘ ctx * ⟦t2⟧ₜₘ ctx;
(* Products *)
denote_tm (Γ:=Γ) (τ:=τ) (tuple Γ t1 t2) ctx := (⟦t1⟧ₜₘ ctx, ⟦t2⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (first Γ t) ctx := fst (⟦t⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (second Γ t) ctx := snd (⟦t⟧ₜₘ ctx);
(* Sums *)
denote_tm (Γ:=Γ) (τ:=τ) (case Γ e c1 c2) ctx with ⟦e⟧ₜₘ ctx := {
  denote_tm (case Γ e c1 c2) ctx (Datatypes.inl x) := (⟦c1⟧ₜₘ ctx) x;
  denote_tm (case Γ e c1 c2) ctx (Datatypes.inr x) := (⟦c2⟧ₜₘ ctx) x
};
denote_tm (Γ:=Γ) (τ:=τ) (inl Γ τ σ e) ctx := Datatypes.inl (⟦e⟧ₜₘ ctx);
denote_tm (Γ:=Γ) (τ:=τ) (inr Γ σ τ e) ctx := Datatypes.inr (⟦e⟧ₜₘ ctx) }
where "⟦ t ⟧ₜₘ" := (denote_tm t)
(* Helper for arrays *)
where denote_array {Γ τ} n (f : Fin.t n -> ⟦Γ⟧ₜₓ -> ⟦τ⟧ₜ)
  : ⟦Γ⟧ₜₓ -> ⟦Array n τ⟧ₜ  :=
denote_array 0 f ctx := Vnil;
denote_array (S n) f ctx := Vcons (f (nat_to_fin n) ctx)
  ((denote_array n (shave_fin f)) ctx).

Reserved Notation "⟦ s ⟧ₑ".
Equations denote_env {Γ} (G : Env Γ): ⟦ Γ ⟧ₜₓ :=
denote_env env_nil => HNil;
denote_env (env_cons t G') with denote_env G' => {
  denote_env (env_cons t G') X => ⟦ t ⟧ₜₘ X ::: X }
where "⟦ s ⟧ₑ" := (denote_env s).

Fixpoint denote_sub {Γ Γ'}: sub Γ Γ' -> ⟦ Γ' ⟧ₜₓ -> ⟦ Γ ⟧ₜₓ :=
  match Γ with
  | [] => fun s ctx => HNil
  | h :: t => fun s ctx =>
      denote_tm (hd_sub s) ctx ::: denote_sub (tl_sub s) ctx
  end.
Notation "⟦ s ⟧ₛ" := (denote_sub s).

Fixpoint denote_ren {Γ Γ'}: ren Γ Γ' -> ⟦ Γ' ⟧ₜₓ -> ⟦ Γ ⟧ₜₓ :=
  match Γ with
  | [] => fun r ctx => HNil
  | τ :: t => fun r ctx =>
      denote_tm (var Γ' τ (hd_ren r)) ctx ::: denote_ren (tl_ren r) ctx
  end.
Notation "⟦ r ⟧ᵣ" := (denote_ren r).

(* Lemmas for renaming and substitution in the denotated context.
  Many from Strongly Typed Terms in Coq by Nick Becton, et al.
*)
Lemma denote_ren_elim : forall Γ Γ' τ
  (r : ren Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  denote_ren r ctx = denote_ren (tl_ren (rename_lifted r)) (x ::: ctx).
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
  induction t; quick; try solve [simp denote_tm in *; rewrites]...
  { simp denote_tm in *. induction v; simp denote_v...
    simp denote_v. }
  { simp denote_tm in *. specialize IHt with (r:=rename_lifted r).
    simpl in IHt. simp rename_lifted in IHt.
    apply functional_extensionality...
    rewrite <- IHt...
    rewrite <- denote_ren_elim... }
  { simp denote_tm in *. rewrites.
    unfold compose.
    induction n... rewrites.
    apply Vcons_eq.
    splits... }
  { simp denote_tm. rewrite IHt1.
    destruct (⟦ rename r t1 ⟧ₜₘ ctx);
      quick; rewrites. }
Qed.

Lemma denote_ren_shift : forall Γ Γ' τ (r:ren Γ Γ'),
  denote_ren (fun _ v => Pop _ _ τ (r _ v)) =
    fun se => denote_ren r (htl se).
Proof with quick.
  induction Γ... extensionality ctx.
  apply denote_ctx_eq;
    simp denote_tm...
  { unfold hd_ren. dependent elimination ctx.
    simp denote_v... }
  { unfold tl_ren. rewrite IHΓ... }
Qed.

Lemma denote_ren_id : forall Γ,
  denote_ren (@id_ren Γ) = Datatypes.id.
Proof with quick.
  intros. extensionality x.
  dependent induction Γ;
    dependent destruction x...
  apply denote_ctx_eq...
  unfold tl_ren, id_ren in *...
  rewrite denote_ren_shift...
Qed.

Lemma denote_shift : forall Γ τ σ (t : tm Γ τ) ctx,
    ⟦ shift (σ:=σ) t ⟧ₜₘ ctx = ⟦ t ⟧ₜₘ (htl ctx).
Proof with eauto.
  unfold shift. intros.
  rewrite <- denote_ren_commutes...
  pose proof denote_ren_elim as H.
  dependent destruction ctx.
  specialize H with Γ Γ σ (fun t x => x) d ctx.
  unfold tl_ren in H.
  symmetry in H.
  assert (H':
    (fun (ρ : ty) (x : ρ ∈ Γ) => Pop Γ ρ σ x) =
    (fun (τ : ty) (x : τ ∈ Γ) =>
       rename_lifted (fun (t : ty) (v : t ∈ Γ) => v) τ (Pop Γ τ σ x))
    ) by (extensionality x; quick).
  rewrite_c H'. rewrite_c H.
  fold (@id_ren Γ). rewrite denote_ren_commutes.
  rewrite app_ren_id...
Qed.

Lemma denote_sub_elim : forall Γ Γ' τ
  (s : sub Γ Γ') (x : ⟦ τ ⟧ₜ) (ctx : ⟦ Γ' ⟧ₜₓ),
  ⟦ s ⟧ₛ  ctx = ⟦ (tl_sub (substitute_lifted s)) ⟧ₛ (x ::: ctx).
Proof with eauto.
  induction Γ; intros...
  intros. specialize IHΓ with (s := (tl_sub s)).
  simpl. rewrite IHΓ with (x := x).
  unfold hd_sub. unfold tl_sub. simp substitute_lifted.
  erewrite denote_shift...
Qed.

Lemma denote_sub_commutes :
  forall Γ Γ' τ (t : tm Γ τ) (s : sub Γ Γ') (ctx : ⟦ Γ' ⟧ₜₓ),
    ⟦ t ⟧ₜₘ (⟦ s ⟧ₛ  ctx) = ⟦ substitute s t ⟧ₜₘ ctx.
Proof with quick.
  intros. generalize dependent Γ'.
  induction t; intros; simp denote_tm; rewrites...
  { simpl. induction v...
    intros. simp denote_v. }
  { specialize IHt with (s:=substitute_lifted s)...
    apply functional_extensionality...
    simp denote_tm.
    rewrite <- IHt...
    erewrite denote_sub_elim... }
  { simp denote_tm.
    unfold compose.
    induction n... rewrites.
    apply Vcons_eq... }
  { simp denote_tm.
    destruct (⟦ substitute s t1 ⟧ₜₘ ctx);
      quick; rewrites. }
Qed.

Lemma denote_sub_id : forall Γ τ (t : tm Γ τ) (ctx : ⟦ Γ ⟧ₜₓ),
  ⟦ t ⟧ₜₘ (⟦ id_sub ⟧ₛ ctx) = ⟦ t ⟧ₜₘ ctx.
Proof with quick.
  intros.
  rewrite denote_sub_commutes...
  rewrite app_sub_id...
Qed.

Lemma denote_sub_shift : forall Γ Γ' σ (s:sub Γ Γ'),
  denote_sub (fun _ v => shift (σ:=σ) (s _ v)) =
    fun ctx => denote_sub s (htl ctx).
Proof with quick.
  induction Γ... extensionality ctx.
  apply denote_ctx_eq...
  { unfold hd_sub. rewrite denote_shift... }
  { unfold tl_sub. rewrite IHΓ... }
Qed.

Lemma denote_sub_tl_simpl :
  forall Γ Γ' τ (ctx : ⟦ Γ' ⟧ₜₓ) (sb : sub (τ::Γ) Γ'),
    ⟦ tl_sub sb ⟧ₛ ctx = htl (⟦ sb ⟧ₛ ctx).
Proof. quick. Qed.

Lemma denote_sub_id_ren : forall Γ Γ' (ctx : ⟦ Γ' ⟧ₜₓ) (r : ren Γ Γ'),
  ⟦ compose_sub_ren id_sub r ⟧ₛ ctx = ⟦ r ⟧ᵣ ctx.
Proof with quick.
  intros Γ Γ' ctx r.
  unfold compose_sub_ren.
  induction Γ...
  unfold tl_sub.
  erewrite IHΓ...
Qed.

Lemma denote_sub_id_ctx : forall Γ ctx,
  ⟦ @id_sub Γ ⟧ₛ ctx = ctx.
Proof with quick.
  intros.
  assert (H: id_sub = compose_sub_ren (@id_sub Γ) id_ren)...
  rewrite_c H.
  rewrite denote_sub_id_ren.
  rewrite denote_ren_id...
Qed.

Lemma denote_sub_tl_cons :
  forall Γ Γ' τ (t : tm Γ' τ) ctx (sb : sub Γ Γ'),
    ⟦ (tl_sub (cons_sub t sb)) ⟧ₛ ctx = ⟦ sb ⟧ₛ ctx.
Proof with quick.
  intros.
  unfold id_sub.
  now rewrite tl_cons_sub.
Qed.

Example denote_square :
  ⟦ ex_square ⟧ₜₘ HNil = (fun x => x * x).
Proof with quick.
  extensionality x. unfold ex_square.
  simp denote_tm.
  reflexivity.
Qed.
