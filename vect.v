Require Import Reals.
From Coquelicot Require Import Hierarchy Rcomplements Continuity Derive.
From mathcomp Require Import ssreflect ssrfun eqtype ssrbool ssrnat bigop ssralg
  matrix fintype zmodp.
Require Import AD.coquelicotComplements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section VectAbelianGroup.

Variable R : AbelianGroup.
Variable n : nat.

Definition vplus (x y : 'rV[R]_n) := \row_i (plus (x 0 i) (y 0 i)).

Lemma addvC x y : vplus x y = vplus y x.
Proof. by apply/matrixP=> i j; rewrite !mxE plus_comm. Qed.

Lemma addvA x y z : vplus x (vplus y z) = vplus (vplus x y) z.
Proof. by apply/matrixP=> i j; rewrite !mxE plus_assoc. Qed.

Definition v0 : 'rV[R]_n := \row_i zero.

Lemma addv0 x : vplus x v0 = x.
Proof. by apply/matrixP=> i j; rewrite !mxE plus_zero_r ord1. Qed.

Definition vopp (x : 'rV[R]_n) := \row_i (opp (x 0 i)).

Lemma subv_eq0 x : vplus x (vopp x) = v0.
Proof. by apply/matrixP=> i j; rewrite !mxE plus_opp_r. Qed.

End VectAbelianGroup.

Definition vect_AbelianGroupMixin (R : AbelianGroup) (n : nat):=
  AbelianGroup.Mixin 'rV[R]_n _ _ _ (@addvC _ _) (@addvA _ _) (@addv0 _ _)
  (@subv_eq0 _ _).

Canonical vect_AbelianGroup (R : AbelianGroup) (n : nat) :=
  AbelianGroup.Pack _ (vect_AbelianGroupMixin R n) 'rV[R]_n.

Section vectRing.

Variable R : Ring.
Variable n : nat.

Definition vmult (x y : 'rV[R]_n) := \row_i (mult (x 0 i) (y 0 i)).

Lemma mulvA x y z : vmult x (vmult y z) = vmult (vmult x y) z.
Proof. by apply/matrixP=> i j; rewrite !mxE mult_assoc. Qed.

Definition v1 : 'rV[R]_n := \row_i one.

Lemma mulv1 x : vmult x v1 = x.
Proof. by apply/matrixP=> i j; rewrite !mxE mult_one_r ord1. Qed.

Lemma mul1v x : vmult v1 x = x.
Proof. by apply/matrixP=> i j; rewrite !mxE mult_one_l ord1. Qed.

Lemma mulvDl x y z : vmult (vplus x y) z = vplus (vmult x z) (vmult y z).
Proof. by apply/matrixP=> i j; rewrite !mxE mult_distr_r. Qed.

Lemma mulvDr x y z : vmult x (vplus y z) = vplus (vmult x y) (vmult x z).
Proof. by apply/matrixP=> i j; rewrite !mxE mult_distr_l. Qed.

End vectRing.

Definition vect_RingMixin (R : Ring) (n : nat) :=
  Ring.Mixin _ _ _ (@mulvA R n) (@mulv1 _ _) (@mul1v _ _) (@mulvDl _ _)
  (@mulvDr _ _).

Canonical vect_Ring (R : Ring) (n : nat) :=
  Ring.Pack _ (Ring.Class _ _ (vect_RingMixin R n)) 'rV[R]_n.

Local Open Scope R_scope.

Section BigRmax.

Lemma Rmax_eq x y : x = y -> Rmax x y = x.
Proof. by move->; rewrite Rmax_left //; apply: Rle_refl. Qed.

Lemma bigRmax_mkcond (I : finType) (P : pred I) F :
  (forall i, 0 <= F i) ->
  \big[Rmax/0]_(i | P i) F i = \big[Rmax/0]_i (if P i then F i else 0).
Proof.
move=> Fge0; rewrite unlock.
elim: (index_enum I)=> //= i r ->; case P=> //; rewrite Rmax_right //=.
case: r=> [|a r] /=; first exact: Rle_refl; case: (P a); last exact: Rmax_l.
by apply/Rmax_Rle; left.
Qed.

Lemma bigRmax_split (I : finType) (P : pred I) F1 F2 :
  \big[Rmax/0]_(i | P i) (Rmax (F1 i) (F2 i)) =
  Rmax (\big[Rmax/0]_(i | P i) F1 i) (\big[Rmax/0]_(i | P i) F2 i).
Proof.
elim/big_rec3: _=> [|i x y _ _ ->]; first by rewrite Rmax_eq.
rewrite [RHS]Rmax_assoc [LHS]Rmax_assoc; congr (Rmax _ _).
by rewrite -[RHS]Rmax_assoc (Rmax_comm y) Rmax_assoc.
Qed.

Lemma bigRmaxID (I : finType) (P : pred I) F :
  (forall i, 0 <= F i) ->
  \big[Rmax/0]_i F i = Rmax (\big[Rmax/0]_(i | P i) F i)
                            (\big[Rmax/0]_(i | ~~ (P i)) F i).
Proof.
move=> Fge0; rewrite (bigRmax_mkcond P Fge0)
  (bigRmax_mkcond (fun i => ~~ P i) Fge0) -bigRmax_split.
by apply: eq_bigr => i; case: (P i); [rewrite Rmax_left|rewrite Rmax_right].
Qed.

Lemma bigRmaxD1 (I : finType) (F : I -> R) i : (forall i, 0 <= F i) ->
  \big[Rmax/0]_j F j = Rmax (F i) (\big[Rmax/0]_(j | j != i) F j).
Proof.
move=> Fge0; rewrite (bigRmaxID (pred1 i)) //; congr (Rmax _ _).
by rewrite -big_filter filter_index_enum enum1 unlock /= Rmax_left.
Qed.

Lemma leq_bigRmax (I : finType) (F : I -> R) :
  (forall i, 0 <= F i) -> forall i, F i <= \big[Rmax/0]_i F i.
Proof. by move=> Fge0 i; rewrite (bigRmaxD1 i) //; apply: Rmax_l. Qed.

Lemma bigRmax_leq (I : finType) (F : I -> R) (x : R) :
  (forall i, 0 <= F i) -> \big[Rmax/0]_j F j <= x -> forall i, F i <= x.
Proof. by move=> Fge0 leFx i; apply: Rle_trans leFx; apply: leq_bigRmax. Qed.

Lemma bigRmax_lt (I : finType) (F : I -> R) (x : R) :
  0 < x -> (forall i, F i < x) -> \big[Rmax/0]_j F j < x.
Proof. by move=> xgt0 ltFx; elim/big_ind: _ => // ??; apply: Rmax_lub_lt. Qed.

Lemma bigRmax_le_compat (I : finType) (F1 F2 : I -> R) :
  (forall i, F1 i <= F2 i) -> \big[Rmax/0]_i (F1 i) <= \big[Rmax/0]_i (F2 i).
Proof.
move=> F1leF2; rewrite unlock.
elim: (index_enum I)=> /= [|i r F1rleF2r]; first exact: Rle_refl.
exact: Rmax_le_compat.
Qed.
Arguments bigRmax_le_compat [I F1] _ _.

Lemma bigRmax_opconst_r (I : finType) (F : I -> R) c op :
  (forall i, 0 <= F i) -> 0 <= c ->
  (forall x y z, 0 <= z -> 0 <= x <= y -> 0 <= op x z <= op y z) ->
  \big[Rmax/0]_i (op (F i) c) <= op (\big[Rmax/0]_i F i) c.
Proof.
move=> Fge0 cge0 opndec1; rewrite unlock.
elim: (index_enum I)=> /= [|i r rop_le_opr].
  suff [] : 0 <= op 0 c <= op 0 c by [].
  by apply: opndec1=> //; split; apply: Rle_refl.
apply: Rmax_lub; first by apply opndec1=> //; split=> //; apply: Rmax_l.
apply: Rle_trans rop_le_opr _; apply opndec1=> //; split; last exact: Rmax_r.
by case: r=> /= [|a r]; [apply: Rle_refl|apply/Rmax_Rle; left].
Qed.

Lemma bigRmax_opconst_l (I : finType) (F : I -> R) c op :
  (forall i, 0 <= F i) -> 0 <= c ->
  (forall x y z, 0 <= z -> 0 <= x <= y -> 0 <= op z x <= op z y) ->
  \big[Rmax/0]_i (op c (F i)) <= op c (\big[Rmax/0]_i F i).
Proof.
move=> Fge0 cge0 opndec2; rewrite unlock.
elim: (index_enum I)=> /= [|i r rop_le_opr].
  suff [] : 0 <= op c 0 <= op c 0 by [].
  by apply: opndec2=> //; split; apply: Rle_refl.
apply: Rmax_lub; first by apply opndec2=> //; split=> //; apply: Rmax_l.
apply: Rle_trans rop_le_opr _; apply opndec2=> //; split; last exact: Rmax_r.
by case: r=> /= [|a r]; [apply: Rle_refl|apply/Rmax_Rle; left].
Qed.

Lemma bigRmax_ge0 (I : finType) (F : I -> R) :
  (forall i, 0 <= F i) -> 0 <= \big[Rmax/0]_i F i.
Proof.
move=> Fge0; rewrite unlock.
elim: (index_enum I)=> /= [|i r Frge0]; first exact: Rle_refl.
by apply: Rle_trans (Fge0 i) _; apply: Rmax_l.
Qed.

Lemma bigRmax_le_ndec (I : finType) (F1 F2 : I -> R) op :
  (forall i, 0 <= F1 i) -> (forall i, 0 <= F2 i) ->
  (forall x y z, 0 <= z -> 0 <= x <= y -> 0 <= op x z <= op y z) ->
  (forall x y z, 0 <= z -> 0 <= x <= y -> 0 <= op z x <= op z y) ->
  \big[Rmax/0]_i (op (F1 i) (F2 i)) <= op (\big[Rmax/0]_i F1 i)
                                          (\big[Rmax/0]_i F2 i).
Proof.
move=> F1ge0 F2ge0 opndec1 opndec2.
have : \big[Rmax/0]_i (op (F1 i) (\big[Rmax/0]_j F2 j)) <=
       op (\big[Rmax/0]_i F1 i) (\big[Rmax/0]_i F2 i).
  by apply: bigRmax_opconst_r=> //; apply: bigRmax_ge0.
apply/Rle_trans/bigRmax_le_compat => i.
by apply opndec2 => //; split=> //; apply: leq_bigRmax.
Qed.

Lemma bigRmax_eq0 (I : finType) (F : I -> R) :
  (forall i, 0 <= F i) -> \big[Rmax/0]_i F i = 0 -> forall i, F i = 0.
Proof.
move=> Fge0 maxF0 i; apply: Rle_antisym=> //; rewrite -maxF0.
exact: leq_bigRmax.
Qed.

End BigRmax.

Section vectAbsRing.

Variable A : AbsRing.
Variable n : nat.

Definition vabs (x : 'rV[A]_n.+1) := \big[Rmax/0]_i (abs (x ord0 i)).

Lemma vabs0 : vabs zero = 0.
Proof.
rewrite /vabs (eq_bigr (fun _ => 0))=> [|i _]; last by rewrite mxE abs_zero.
rewrite big_const_ord iterS Rmax_eq //.
by elim: n=> [|? ih] //=; rewrite Rmax_eq.
Qed.

Lemma vabs_opp1 : vabs (opp one) = 1.
Proof.
rewrite /vabs (eq_bigr (fun _ => 1))=> [|i _]; last by rewrite !mxE abs_opp_one.
rewrite big_const_ord iterS Rmax_left //.
by elim: n=> [|? ih]; [apply: Rle_0_1|rewrite /= Rmax_left //; apply: Rle_refl].
Qed.

Lemma vabs_triangle x y : vabs (plus x y) <= (vabs x) + (vabs y).
Proof.
suff : \big[Rmax/0]_i (abs (x ord0 i) + abs (y ord0 i)) <= vabs x + vabs y.
  apply: Rle_trans; apply: bigRmax_le_compat => i; rewrite mxE.
  exact: abs_triangle.
apply: bigRmax_le_ndec=> [i|i|a b c|a b c]; try exact: abs_ge_0.
  move=> cge0 [age0 aleb]; split; first exact: Rplus_le_le_0_compat.
  exact: Rplus_le_compat_r.
move=> cge0 [age0 aleb]; split; first exact: Rplus_le_le_0_compat.
exact: Rplus_le_compat_l.
Qed.

Lemma vabsM x y : vabs (mult x y) <= (vabs x) * (vabs y).
Proof.
suff : \big[Rmax/0]_i (abs (x ord0 i) * abs (y ord0 i)) <= vabs x * vabs y.
  apply: Rle_trans; apply: bigRmax_le_compat => i; rewrite mxE.
  exact: abs_mult.
apply: bigRmax_le_ndec=> [i|i|a b c|a b c]; try exact: abs_ge_0.
  move=> cge0 [age0 aleb]; split; first exact: Rmult_le_pos.
  exact: Rmult_le_compat_r.
move=> cge0 [age0 aleb]; split; first exact: Rmult_le_pos.
exact: Rmult_le_compat_l.
Qed.

Lemma vabs_eq0 x : vabs x = 0 -> x = zero.
Proof.
move=> absx0; apply/matrixP=> i j.
rewrite ord1 [RHS]mxE -(abs_eq_zero (x ord0 j)) //.
by apply: (bigRmax_eq0 _ absx0) => k; apply: abs_ge_0.
Qed.

End vectAbsRing.

Definition vect_AbsRingMixin (R : AbsRing) (n : nat) :=
  AbsRing.Mixin _ _ (@vabs0 R n) (@vabs_opp1 _ _) (@vabs_triangle _ _)
  (@vabsM _ _) (@vabs_eq0 _ _).

Canonical vect_AbsRing (R : AbsRing) (n : nat) :=
  AbsRing.Pack _ (AbsRing.Class _ _ (vect_AbsRingMixin R n)) 'rV[R]_n.+1.

Section vectUnifSpace.

Variable U : UniformSpace.
Variable n : nat.

Definition vball (x : 'rV[U]_n) e (y : 'rV[U]_n) :=
  forall i, ball (x ord0 i) e (y ord0 i).

Lemma vball_refl x (e : posreal) : vball x e x.
Proof. by move=> ?; apply: ball_center. Qed.

Lemma vball_sym x y e : vball x e y -> vball y e x.
Proof. by move=> xe_y ?; apply/ball_sym/xe_y. Qed.

Lemma vball_triangle x y z e1 e2 :
  vball x e1 y -> vball y e2 z -> vball x (e1 + e2) z.
Proof.
by move=> xe1_y ye2_z ?; apply: ball_triangle; [apply: xe1_y| apply: ye2_z].
Qed.

End vectUnifSpace.

Definition vect_UniformSpaceMixin (U : UniformSpace) (n : nat) :=
  UniformSpace.Mixin _ _ (@vball_refl U n) (@vball_sym _ _)
    (@vball_triangle _ _).

Canonical vect_UniformSpace (U : UniformSpace) (n : nat) :=
  UniformSpace.Pack _ (vect_UniformSpaceMixin U n) 'rV[U]_n.

Local Open Scope classical_set_scope.

Lemma big_and_proj n (A : set 'I_n) (i : 'I_n) :
  \big[and/True]_j A j -> A i.
Proof.
elim: n i A=> [[]|n ihn i A] //.
rewrite big_ord_recl; move => [A0 /ihn AS].
case: (eqVneq ord0 i)=> [<-|ine0] //.
by case: (unlift_some ine0)=> j ->.
Qed.

Lemma filt_big_and n U (A : 'I_n -> set U) (F : set (set U)) :
  Filter F -> (forall i, F (A i)) -> F (fun x => \big[and/True]_i A i x).
Proof.
move=> Ffilter; elim: n A=> [|n ihn] A FA.
  by apply: filter_imp filter_true => ?; rewrite big_ord0.
have : F [set p : U | A ord0 p /\ \big[and/True]_(i < n) A (lift ord0 i) p].
  by apply: filter_and=> //; apply: ihn=> i; apply: FA.
by apply: filter_imp => x Ax; rewrite big_ord_recl.
Qed.

Section vectCompleteSpace.

Variable T : CompleteSpace.
Variable n : nat.

Definition proj (F : set (set 'rV[T]_n)) (i : 'I_n) (A : set T) :=
  F (fun x => A (x ord0 i)).

Definition vlim (F : set (set 'rV[T]_n)) := \row_i (lim (proj F i)).

Instance proj_proper (F : set (set 'rV[T]_n)) (i : 'I_n) :
  ProperFilter F -> ProperFilter (proj F i).
Proof.
move=> Fproper; split; first by move=> A /filter_ex.
split; first exact: filter_true.
  by move=> A B FA FB; apply: filter_and.
by move=> A B sAB; apply: filter_imp.
Qed.

Lemma proj_cauchy (F : set (set 'rV[T]_n)) (i : 'I_n) :
  Filter F -> cauchy F -> cauchy (proj F i).
Proof.
move=> Ffilter Fcauchy eps; have [x Fxe] := Fcauchy eps; exists (x ord0 i).
exact: (@filter_imp _ F) Fxe.
Qed.

Lemma vcomplete_cauchy F :
  ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (vlim F) eps).
Proof.
move=> Fproper Fcauchy eps.
have Fi_limF : forall i, proj F i (ball (vlim F ord0 i) eps).
  by move=> i; rewrite mxE; apply: complete_cauchy; apply: proj_cauchy.
have: F (fun y => \big[and/True]_(i < n) (ball (vlim F ord0 i) eps (y ord0 i))).
  exact: filt_big_and.
by apply: filter_imp => y limFe_y i; apply: big_and_proj limFe_y.
Qed.

Lemma proj_le (F1 F2 : set (set 'rV[T]_n)) :
  filter_le F1 F2 -> forall i, filter_le (proj F1 i) (proj F2 i).
Proof. by move=> F1leF2 ?? /F1leF2. Qed.

Lemma close_vlim (F1 F2 : set (set 'rV[T]_n)) :
  filter_le F1 F2 -> filter_le F2 F1 -> close (vlim F1) (vlim F2).
Proof. by move=> ????; rewrite !mxE; apply: close_lim; apply: proj_le. Qed.

End vectCompleteSpace.

Definition vect_CompleteSpaceMixin (T : CompleteSpace) (n : nat) :=
  CompleteSpace.Mixin _ (@vlim T n) (@vcomplete_cauchy _ _) (@close_vlim _ _).

Canonical vect_CompleteSpace (T : CompleteSpace) (n : nat) :=
  CompleteSpace.Pack _ (CompleteSpace.Class _ _ (vect_CompleteSpaceMixin T n))
  'rV[T]_n.

Section vectModuleSpace.

Variable K : Ring.
Variable V : ModuleSpace K.
Variable n : nat.

Definition vscal (x : K) (u : 'rV[V]_n) := \row_i (scal x (u ord0 i)).

Lemma scalA x y u : vscal x (vscal y u) = vscal (mult x y) u.
Proof. by apply/matrixP=> ? ?; rewrite !mxE scal_assoc. Qed.

Lemma scal1 u : vscal one u = u.
Proof. by apply/matrixP=> ? ?; rewrite !mxE !ord1 scal_one. Qed.

Lemma scalDr x u v : vscal x (plus u v) = plus (vscal x u) (vscal x v).
Proof. by apply/matrixP=> ? ?; rewrite !mxE scal_distr_l. Qed.

Lemma scalDl x y u : vscal (plus x y) u = plus (vscal x u) (vscal y u).
Proof. by apply/matrixP=> i j; rewrite !mxE scal_distr_r. Qed.

End vectModuleSpace.

Definition vect_ModuleSpaceMixin (K : Ring) (V : ModuleSpace K) (n : nat) :=
  ModuleSpace.Mixin _ _ (@vscal K V n) (@scalA _ _ _) (@scal1 _ _ _)
  (@scalDr _ _ _) (@scalDl _ _ _).

Canonical vect_ModuleSpace (K : Ring) (V : ModuleSpace K) (n : nat) :=
  ModuleSpace.Pack _ _ (ModuleSpace.Class _ _ _ (vect_ModuleSpaceMixin V n))
  'rV[V]_n.

Canonical vect_NormedModuleAux (K : AbsRing) (V : NormedModuleAux K)
  (n : nat) :=
  NormedModuleAux.Pack _ _ (NormedModuleAux.Class K 'rV[V]_n
    (ModuleSpace.class _ _) (vect_UniformSpaceMixin _ _)) 'rV[V]_n.

Section vectNormedModule.

Variable K : AbsRing.
Variable V : NormedModule K.
Variable n : nat.

Definition vnorm (x : 'rV[V]_n) := \big[Rmax/0]_i (norm (x ord0 i)).

Definition vnorm_factor := (@norm_factor _ V).

Lemma vnorm_triangle x y : vnorm (plus x y) <= vnorm x + vnorm y.
Proof.
suff : \big[Rmax/0]_i (norm (x ord0 i) + norm (y ord0 i)) <= vnorm x + vnorm y.
  apply: Rle_trans; apply: bigRmax_le_compat => i; rewrite mxE.
  exact: norm_triangle.
apply: bigRmax_le_ndec=> [i|i|a b c|a b c]; try exact: norm_ge_0.
 move=> cge0 [age0 aleb]; split; first exact: Rplus_le_le_0_compat.
 exact: Rplus_le_compat_r.
move=> cge0 [age0 aleb]; split; first exact: Rplus_le_le_0_compat.
exact: Rplus_le_compat_l.
Qed.

Lemma vnorm_scal l x : vnorm (scal l x) <= abs l * vnorm x.
Proof.
suff : \big[Rmax/0]_i (abs l * norm (x ord0 i)) <= abs l * vnorm x.
  apply: Rle_trans; apply: bigRmax_le_compat => i; rewrite mxE.
  exact: norm_scal.
apply: bigRmax_opconst_l => [i||a b c cge0 [age0 aleb]]; first exact: norm_ge_0.
  exact: abs_ge_0.
by split; [apply: Rmult_le_pos|apply: Rmult_le_compat_l].
Qed.

Lemma vnorm_lt_ball x y eps : vnorm (minus y x) < eps -> ball x eps y.
Proof.
move=> xy_e i; apply: norm_compat1; apply: Rle_lt_trans xy_e.
rewrite /vnorm (eq_bigr (fun i => norm (minus (y ord0 i) (x ord0 i)))).
  by apply: leq_bigRmax => ?; apply: norm_ge_0.
by move=> ? _; rewrite !mxE.
Qed.

Lemma ball_vnorm_lt (x y : 'rV[V]_n) (eps : posreal) :
  ball x eps y -> vnorm (minus y x) < vnorm_factor * eps.
Proof.
move=> xe_y; rewrite /vnorm unlock.
elim: (index_enum _)=> /= [|i r hr].
  by apply: Rmult_lt_0_compat; [apply: norm_factor_gt_0|apply: cond_pos].
by apply/Rmax_Rlt; split=> //; rewrite !mxE; apply: norm_compat2.
Qed.

Lemma vnorm_eq0 x : vnorm x = 0 -> x = zero.
Proof.
move/bigRmax_eq0=> nxeq0; apply/matrixP=> i j; rewrite [RHS]mxE ord1.
by apply/norm_eq_zero/nxeq0 => ?; apply: norm_ge_0.
Qed.

End vectNormedModule.

Definition vect_NormedModuleMixin (K : AbsRing) (V : NormedModule K)
  (n : nat) :=
  NormedModule.Mixin _ _ (@vnorm K V n) (@vnorm_factor _ _)
  (@vnorm_triangle _ _ _) (@vnorm_scal _ _ _) (@vnorm_lt_ball _ _ _)
  (@ball_vnorm_lt _ _ _) (@vnorm_eq0 _ _ _).

Canonical vect_NormedModule (K : AbsRing) (V : NormedModule K) (n : nat) :=
  NormedModule.Pack K 'rV[V]_n (NormedModule.Class K 'rV[V]_n _
    (vect_NormedModuleMixin V n)) 'rV[V]_n.

Canonical vect_CompleteNormedModule (K : AbsRing) (V : CompleteNormedModule K)
  (n : nat) :=
  CompleteNormedModule.Pack K 'rV[V]_n (CompleteNormedModule.Class K 'rV[V]_n
    (NormedModule.class _ _) (vect_CompleteSpaceMixin V n)) 'rV[V]_n.

Lemma vect_hausdorff (U : UniformSpace) (n : nat) :
  hausdorff U -> hausdorff (vect_UniformSpace U n).
Proof.
move=> hU x y clx_y; apply/matrixP=> i j; rewrite ord1 {i}.
apply: hU => A B xj_A yj_B.
set f := fun z : 'rV[U]_n => z ord0 j.
have fcont z : continuous f z.
  by move=> C [eps fzeps_C]; exists eps=> t zeps_t; apply/fzeps_C/zeps_t.
suff : nonempty (setI (preimage f A) (preimage f B)).
  by move=> [z]; exists (f z).
by apply: clx_y; apply: locally_preimage.
Qed.

Lemma is_linear_component (K : AbsRing) (V : NormedModule K) n i :
  is_linear (fun p : 'rV[V]_n => p ord0 i).
Proof.
split; try by move=> ??; rewrite mxE.
exists 1; split; first exact: Rlt_0_1.
by move=> p; rewrite Rmult_1_l; apply: leq_bigRmax => j; apply: norm_ge_0.
Qed.

Global Instance diff_component (K : AbsRing) (V : NormedModule K) n i F :
  diff (fun p : 'rV[V]_n => p ord0 i) F (fun p => p ord0 i).
Proof. exact/filterdiff_linear/is_linear_component. Qed.

Global Instance deriv_component (K : AbsRing) (V : NormedModule K) n
  (f : K -> 'rV[V]_n) i x p :
  deriv f x p -> deriv ((fun y : 'rV[V]_n => y ord0 i) \o f) x (p ord0 i).
Proof. by move=> f'xp; apply: deriv_eq. Qed.