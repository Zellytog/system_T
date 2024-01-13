Require Import system_T_first_def.
Require Import system_T_substi.
Require Import system_T_reduction.
Require Import system_T_types.
Require Import system_T_normal_form_SN.
Require Import system_T_context_wh_red.
Require Import system_T_weak_head_expansion.
Require Import system_T_sat.
Require Import PeanoNat.
Require Import List.
Require Import Lt.

(* ********************************************************************************************* *)

(** III. The strong normalization theorem *)

(** 9. Adequacy theorem and strong normalization.

This file proves the adequacy theorem: is t : T then t ∈ [[T]]. For this, we introduce the notion
  of valid permutation, which is a predicate over a context Γ and a permutation σ saying that for
  all i, σᵢ ∈ [[Γᵢ]]. The adequacy is then stated as Γ ⊢ t : T -> t[σᵢ/xᵢ] ∈ [[T]].*)


Inductive valid_perm : ctx -> perm -> Prop :=
  | valid_nil : valid_perm nil nil
  | valid_cons : forall (Γ : ctx) (σ : perm) (T : type) (t : term), valid_perm Γ σ ->
    interpretation T t -> valid_perm (T :: Γ) (t :: σ).

Lemma adequacy_var : forall (Γ : ctx) (σ : perm) (T : type) (k n : nat), binds k T Γ ->
  valid_perm Γ σ -> [[T]] ({n ↦ σ} {{n + k}}).
Proof.
intros. generalize T k H; clear T k H; induction H0; intros. inversion H.
inversion H1. rewrite <- (simul_tl_r ({{n + 0}}) t σ n). rewrite Nat.add_0_r. simpl.
replace (n =? n) with true; try (symmetry; apply Nat.eqb_eq; reflexivity).
rewrite simul_lift. apply H.
rewrite <- simul_tl_r.
replace ({n ~> lift n (length σ) t} {{n + S n0}}) with ({{n + n0}}).
apply IHvalid_perm. apply H5.
simpl. assert (n < n + S n0). rewrite Nat.add_comm. simpl. rewrite Nat.add_comm.
apply le_lt_n_Sm. apply Nat.le_add_r. specialize (Nat.lt_neq _ _ H7); intro.
apply Nat.neq_sym in H8.
apply Nat.eqb_neq in H8; rewrite H8. apply Nat.lt_le_incl in H7. apply Nat.ltb_ge in H7.
rewrite H7. f_equal. rewrite <- Nat.add_sub_assoc. simpl. rewrite Nat.sub_0_r. reflexivity.
apply le_n_S. apply Nat.le_0_l.
Qed.

Theorem adequacy : forall (Γ : ctx) (σ : perm) (T : type) (t : term), Γ ⊢ t ~: T -> valid_perm Γ σ
  -> [[T]] ({0 ↦ σ} t).
Proof.
intros; generalize σ H0; clear σ H0; induction H; intros.
  - apply (adequacy_var _ _ _ _ 0 H H0).
  - simpl. unfold ArrowInterp; intros.
    assert (saturated_set (interpretation T2)). apply interp_sub_SAT.
    destruct H2 as (H3 & H4 & H2 & H5); clear H3 H4 H5.
    specialize (H2 hole (simul_subst 1 (lift_perm 0 1 σ) t) u).
    apply H2. simpl. rewrite <- simul_tl_l. apply IHtyping. apply valid_cons. apply H0. apply H1.
    apply (interp_sub_SAT T1). apply H1.
  - specialize (IHtyping1 σ H1). specialize (IHtyping2 σ H1). simpl in IHtyping1.
    unfold ArrowInterp in IHtyping1. specialize (IHtyping1 ({0 ↦ σ} t2)). simpl.
    apply IHtyping1. apply IHtyping2.
  - apply zeroIsNat.
  - specialize (IHtyping σ H0) as H1; clear H0. simpl; simpl in H1.
    apply succIsNat. apply H1.
  - simpl. specialize (IHtyping1 σ H2) as IH1. specialize (IHtyping2 σ H2) as IH2.
    specialize (IHtyping3 σ H2) as IH3. simpl in IH2; simpl in IH3.
    specialize rec_for_NatInterp. intro. specialize (H3 ({0 ↦ σ} t3)).
    destruct H3; clear H4.
    specialize (H3 IH3 (interpretation T) _ ({0 ↦ σ} t2) (interp_sub_SAT T) IH1).
    apply H3. intros. specialize (IH2 w H4 x H5). apply IH2.
  - simpl. unfold BoolInterp. intros.
    destruct H as (H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
    specialize (H11 hole). simpl in H11. apply H11. apply (H4 v H2). apply H1.
  - simpl. unfold BoolInterp. intros. destruct H as
    (H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
    specialize (H12 hole). simpl in H12. apply H12. apply (H4 u H1). apply H2.
  - specialize (IHtyping1 σ H2).
    simpl in IHtyping1. assert (BoolInterp ({0 ↦ σ} t1)). apply IHtyping1.
    unfold BoolInterp in IHtyping1.
    specialize (IHtyping2 σ H2). specialize (IHtyping3 σ H2).
    specialize (IHtyping1 (interpretation T) _ _ (interp_sub_SAT T) IHtyping2 IHtyping3).
    apply IHtyping1.
  - simpl. unfold TimesInterp. specialize (IHtyping1 σ H1). specialize (IHtyping2 σ H1).
    assert (saturated_set (interpretation T1)). apply interp_sub_SAT.
    destruct H2 as (H3 & H4 & H5 & H6 & H7 & H8); clear H4 H5 H7 H8.
    assert (saturated_set (interpretation T2)). apply interp_sub_SAT.
    destruct H2 as (H4 & H5 & H7 & H8 & H9 & H10); clear H5 H7 H8 H10.
    specialize (H6 hole). specialize (H9 hole). simpl in H6. simpl in H9.
    split. apply H6; try apply IHtyping1; try( apply H4; apply IHtyping2).
    apply H9; try apply IHtyping2; try( apply H3; apply IHtyping1).
  - simpl. specialize (IHtyping σ H0). simpl in IHtyping.
    unfold TimesInterp in IHtyping. destruct IHtyping. apply H1.
  - simpl. specialize (IHtyping σ H0). simpl in IHtyping.
    unfold TimesInterp in IHtyping. destruct IHtyping. apply H2.
  - simpl. unfold UnitInterp. apply normal_form_SN. apply star_normal_form.
  - simpl. unfold SumInterp. intros.
    assert (saturated_set (interpretation T1)). apply interp_sub_SAT.
    assert (saturated_set (interpretation T2)). apply interp_sub_SAT.
    destruct H1 as (H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13); clear H7 H8 H9 H10 H12 H13.
    specialize (H11 hole). simpl in H11. specialize (IHtyping σ H0).
    apply (H11 ({0 ↦ σ} t) u v). destruct H4 as (H1 & H10); clear H10. apply H1. apply IHtyping.
    specialize (H3 ({{0}})). destruct H5 as (H10 & H8 & H20); clear H10 H20.
    specialize (H8 hole 0). simpl in H8. specialize (H8 holeSN). apply H3 in H8.
    apply H6 in H8. apply SN_subst in H8. apply H8.
    apply H2. apply IHtyping.
  - simpl. unfold SumInterp. intros.
    assert (saturated_set (interpretation T1)). apply interp_sub_SAT.
    assert (saturated_set (interpretation T2)). apply interp_sub_SAT.
    destruct H1 as (H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13); clear H7 H8 H9 H10 H11 H13.
    specialize (H12 hole). simpl in H12. specialize (IHtyping σ H0).
    apply (H12 ({0 ↦ σ} t) u v). destruct H5 as (H1 & H10); clear H10. apply H1. apply IHtyping.
    specialize (H2 ({{0}})). destruct H4 as (H10 & H8 & H20); clear H10 H20.
    specialize (H8 hole 0). simpl in H8. specialize (H8 holeSN). apply H2 in H8.
    apply H6 in H8. apply SN_subst in H8. apply H8.
    apply H3. apply IHtyping.
  - specialize (IHtyping3 σ H2).
    simpl in IHtyping3. unfold SumInterp in IHtyping3.
    simpl. apply IHtyping3. apply interp_sub_SAT.
    intros. assert (valid_perm (T1 :: Γ) (w :: σ)). apply (valid_cons _ _ _ _ H2). apply H3.
    specialize (IHtyping1 _ H4). rewrite simul_tl_l in IHtyping1. simpl in IHtyping1.
    apply IHtyping1.
    intros. assert (valid_perm (T2 :: Γ) (w :: σ)). apply (valid_cons _ _ _ _ H2). apply H3.
    specialize (IHtyping2 _ H4). rewrite simul_tl_l in IHtyping2. simpl in IHtyping2.
    apply IHtyping2.
  - specialize (IHtyping σ H0); clear H0. simpl in IHtyping. unfold VoidInterp in IHtyping.
    unfold Bot_SAT in IHtyping. destruct IHtyping. destruct H1.
    destruct H1. destruct H1. assert (saturated_set (interpretation T));
    try apply (interp_sub_SAT T).
    apply (wh_star_compat (casebot hole)) in H2. simpl in H2. simpl.
    apply (SAT_wh_expansion_star _ _ (δb (x [ₑ {{x0}}]))).
    apply H3. apply SN_deltaNil. apply H0.
    destruct H3 as (_ & H3 & _). specialize (H3 (casebot x) x0).
    simpl in H3; apply H3. apply casebotSN; apply H1.
    apply H2.
Qed.

Lemma binds_ineq : forall (Γ : ctx) (T : type) (n : nat), binds n T Γ -> n < length Γ.
Proof.
intros; generalize T n H; clear T n H; induction Γ; intros. inversion H. inversion H.
apply Nat.lt_0_succ. specialize (IHΓ T n0 H3). simpl. apply le_n_S. apply IHΓ.
Qed.

Lemma typing_ind : forall (Γ : ctx) (T : type) (t : term), Γ ⊢ t ~: T -> max_ind t <= length Γ.
Proof.
intros. induction H; simpl; try apply Nat.le_0_l; try apply IHtyping;
  try apply (Nat.max_lub _ _ _ IHtyping1 (Nat.max_lub _ _ _ IHtyping2 IHtyping3));
  try apply (Nat.max_lub _ _ _ IHtyping1 IHtyping2).
  - apply (binds_ineq Γ T k H).
  - simpl in IHtyping. apply (Nat.sub_le_mono_r _ _ 1) in IHtyping. simpl in IHtyping.
    rewrite Nat.sub_0_r in IHtyping. apply IHtyping.
  - simpl in IHtyping1. simpl in IHtyping2.
    apply (Nat.sub_le_mono_r _ _ 1) in IHtyping1. simpl in IHtyping1;
    rewrite Nat.sub_0_r in IHtyping1.
    apply (Nat.sub_le_mono_r _ _ 1) in IHtyping2. simpl in IHtyping2;
    rewrite Nat.sub_0_r in IHtyping2.
    apply (Nat.max_lub _ _ _ IHtyping1 (Nat.max_lub _ _ _ IHtyping2 IHtyping3)).
Qed.

Lemma all_id_perm_valid : forall (Γ : ctx) (k : nat), valid_perm Γ (id_perm k (length Γ)).
Proof.
induction Γ; intros. simpl. apply valid_nil.
simpl. apply valid_cons. apply IHΓ. apply inAllSAT. apply interp_sub_SAT.
Qed.

Theorem Strong_Normalization : forall (Γ : ctx) (T : type) (t : term), Γ ⊢ t ~: T -> SN t.
Proof.
intros. specialize (typing_ind _ _ _ H). intro. specialize (adequacy Γ).
intro. specialize (H1 (id_perm 0 (length Γ)) T t H (all_id_perm_valid Γ 0)).
rewrite perm_stat in H1; try apply H0.
assert (saturated_set (interpretation T)); try apply (interp_sub_SAT T).
apply H1. rewrite Nat.add_0_r. apply H0.
Qed.