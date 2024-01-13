Require Import system_T_first_def.
Require Import system_T_substi.
Require Import PeanoNat.
Require Import List.
Require Import Lt.

(* ********************************************************************************************* *)

(** I. First definitions *)

(** 3. Reduction.

This file describes the behavior of the reduction rule, noted ⊳. We start with a bit of rewritting
  system theory, about transitive closure and so on. Then, we introduce the reduction relation, and
  finally we prove the Church-Rosser property.*)

(** A. Rewritting system theory.

We define the notion of rewritting rule, some properties and closure on them. A rewriting rule is a
  relation R ⊆ Λ².*)

Definition rewrite : Type := term -> term -> Prop.

Inductive t_closure (R : rewrite) : rewrite :=
  | t_one : forall t u : term, R t u -> t_closure R t u
  | t_add : forall t u v : term, t_closure R t u -> R u v -> t_closure R t v.

Inductive rt_closure (R : rewrite) : rewrite :=
  | rt_refl : forall t : term, rt_closure R t t
  | rt_add : forall t u v : term, rt_closure R t u -> R u v -> rt_closure R t v.

Inductive rts_closure (R : rewrite) : rewrite :=
  | rts_refl : forall t : term, rts_closure R t t
  | rts_add : forall t u v : term, rts_closure R t u -> R u v -> rts_closure R t v
  | rts_sym : forall t u v : term, rts_closure R t u -> R v u -> rts_closure R t v.

Notation "R >+" := (t_closure R) (at level 65).
Notation "R >*" := (rt_closure R) (at level 65).
Notation "R >~" := (rts_closure R) (at level 65).

Lemma closure_R_in_t : forall (R : rewrite) (t u : term), R t u -> R >+ t u.
Proof.
intros. apply t_one. apply H.
Qed.

Lemma closure_R_in_rt : forall (R : rewrite) (t u : term), R t u -> R >* t u.
Proof.
intros. apply (rt_add _ _ _ _ (rt_refl R t) H).
Qed.

Lemma closure_R_in_rts : forall (R : rewrite) (t u : term), R t u -> R >~ t u.
Proof.
intros. apply (rts_add _ _ _ _ (rts_refl R t) H).
Qed.

Lemma closure_t_trans : forall (R : rewrite) (t u v : term), R >+ t u -> R >+ u v -> R >+ t v.
Proof.
intros. induction H0. apply (t_add _ _ _ _ H H0). apply (t_add _ _ u).
apply IHt_closure. apply H. apply H1.
Qed.

Lemma closure_rt_trans : forall (R : rewrite) (t u v : term), R >* t u -> R >* u v -> R >* t v.
Proof.
intros. induction H0. apply H. apply (rt_add _ _ u). apply IHrt_closure.
apply H. apply H1.
Qed.

Lemma closure_rts_trans : forall (R : rewrite) (t u v : term), R >~ t u -> R >~ u v -> R >~ t v.
Proof.
intros. induction H0. apply H. apply (rts_add _ _ u). apply IHrts_closure.
apply H. apply H1. apply (rts_sym _ _ u). apply IHrts_closure. apply H.
apply H1.
Qed.

Lemma closure_rts_sym : forall (R : rewrite) (t u : term), R >~ t u -> R >~ u t.
Proof.
intros. induction H. apply rts_refl. apply (closure_rts_trans _ _ u).
apply (rts_sym _ _ _ _ (rts_refl R v) H0). apply IHrts_closure.
apply (closure_rts_trans _ _ u).
apply (rts_add _ _ _ _ (rts_refl R v) H0). apply IHrts_closure.
Qed.

Lemma closure_t_in_rt : forall (R : rewrite) (t u : term), R >+ t u -> R >* t u.
Proof.
intros. induction H. apply (rt_add _ _ _ _ (rt_refl R t) H).
apply (rt_add _ _ _ _ IHt_closure H0).
Qed.

Lemma closure_t_in_rts : forall (R : rewrite) (t u : term), R >+ t u -> R >~ t u.
Proof.
intros. induction H. apply (rts_add _ _ _ _ (rts_refl R t) H).
apply (rts_add _ _ _ _ IHt_closure H0).
Qed.

Lemma closure_rt_in_rts : forall (R : rewrite) (t u : term), R >* t u -> R >~ t u.
Proof.
intros. induction H. apply rts_refl. apply (rts_add _ _ _ _ IHrt_closure H0).
Qed.

(** We define the main properties of diamond, local confluence and confluence.*)

Definition Diamond_prop (R : rewrite) : Prop := forall t u v : term,
  R t u /\ R t v -> exists w : term, R u w /\ R v w.

Definition Local_confluence (R : rewrite) : Prop := forall t u v : term,
  R t u /\ R t v -> exists w : term, R >* u w /\ R >* v w.

Definition Confluence (R : rewrite) : Prop := forall t u v : term,
  R >* t u /\ R >* t v -> exists w : term, R >* u w /\ R >* v w.

Definition Church_Rosser_prop (R : rewrite) : Prop := forall t u : term,
  R >~ t u -> exists v : term, R >* t v /\ R >* u v.

Lemma confluence_is_rt_diamond : forall (R : rewrite), Confluence R <-> Diamond_prop (R >*).
Proof.
intro; split; intro. unfold Diamond_prop; intros. specialize (H t u v H0).
  destruct H. exists x. apply H.
  unfold Confluence; intros. specialize (H t u v H0).
  destruct H. exists x. apply H.
Qed.

Lemma diamond_gives_confluence : forall (R : rewrite), Diamond_prop R -> Confluence R.
Proof.
intros. unfold Confluence; intros. destruct H0.
generalize v H1; clear v H1; induction H0; intros. exists v. split; try apply H1. apply rt_refl.
specialize (IHrt_closure v0 H2); destruct IHrt_closure. destruct H3.
assert (exists y : term, R x y /\ R >* v y). clear H4. induction H3.
exists v. split. apply H1. apply rt_refl.
specialize (IHrt_closure H0 H1). destruct IHrt_closure. destruct H5.
unfold Diamond_prop in H. specialize (H u v1 x (conj H4 H5)). destruct H. destruct H.
exists x0. split. apply H. apply (rt_add _ _ _ _ H6 H7).
destruct H5. destruct H5. specialize (rt_add _ _ _ _ H4 H5); intro.
exists x0. apply (conj H6 H7).
Qed.

Lemma CR_equiv_confluence : forall (R : rewrite), Confluence R <-> Church_Rosser_prop R.
Proof.
intro; split; intro. unfold Church_Rosser_prop. intros.
induction H0. exists t. split; apply rt_refl.
destruct IHrts_closure. destruct H2. unfold Confluence in H. specialize (H u v x).
assert (R >* u v /\ R >* u x). split. apply closure_R_in_rt. apply H1. apply H3.
specialize (H H4). destruct H. destruct H. exists x0. split; try apply H.
apply (closure_rt_trans _ _ _ _ H2 H5). destruct IHrts_closure. destruct H2. exists x.
split; try apply H2. apply (closure_rt_trans R v u x); try apply H3. apply closure_R_in_rt.
apply H1.
unfold Confluence. intros. unfold Church_Rosser_prop in H. specialize (H u v).
apply H. apply (closure_rts_trans _ _ t). apply closure_rts_sym.
apply closure_rt_in_rts. apply H0. apply closure_rt_in_rts. apply H0.
Qed.

Lemma diamond_stable_equiv : forall (R T : rewrite), (forall t u : term, R t u <-> T t u) ->
  Diamond_prop R -> Diamond_prop T.
Proof.
intros. unfold Diamond_prop; intros. unfold Diamond_prop in H0. destruct H1.
apply H in H1. apply H in H2. assert (R t u /\ R t v). split. apply H1. apply H2.
specialize (H0 t u v H3). destruct H0. destruct H0. apply H in H0. apply H in H4.
exists x. split; try apply H0; apply H4.
Qed.

(** B. β-Reduction.

We define the β-reduction as the least compatible relation ⊳ containing the following rules :

------------------      ------------      ------------      ------------------------------------
(λx.t) u ⊳ t [u/x]      π₁ ⟨t,u⟩ ⊳ t      π₂ ⟨t,u⟩ ⊳ u      δ (x₀ ↦ t | x₁ ↦ u) (κ₁ v) ⊳ t[v/x₀]

------------------------------------      -----------------      --------------------------------
δ (x₀ ↦ t | x₁ ↦ u) (κ₁ v) ⊳ t[v/x₀]      Recₜ t u zero ⊳ t      Rec t u (Sₜ v) ⊳ u v (Rec t u v)

-----------------------      -----------------------
if Tt then t else u ⊳ t      if Ff then t else u ⊳ u
*)

Inductive βred : term -> term -> Prop :=
  | β_NZ : forall t1 t2, βred (Recₜ t1 t2 zero) t1
  | β_NS : forall t1 t2 t3, βred (Recₜ t1 t2 (Sₜ t3)) (( t2 @ₜ t3) @ₜ (Recₜ t1 t2 t3))
  | β_BT : forall t1 t2, βred (IfThenElse Tt t1 t2) t1
  | β_BF : forall t1 t2, βred (IfThenElse Ff t1 t2) t2
  | β_to : forall t1 t2, βred ((λₜ t1) @ₜ t2) ({ 0 ~> t2 } t1)
  | β_times1 : forall t1 t2, βred (π₁ (⟨ t1 , t2 ⟩)) t1
  | β_times2 : forall t1 t2, βred (π₂ (⟨ t1 , t2 ⟩)) t2
  | β_plus1 : forall t1 t2 t3, βred (δ(0 ↦ t1 |0 ↦ t2) (κ₁ t3)) ({ 0 ~> t3 } t1)
  | β_plus2 : forall t1 t2 t3, βred (δ(0 ↦ t1 |0 ↦ t2) (κ₂ t3)) ({ 0 ~> t3 } t2)
  | β_rec1 : forall t1 t2 t3 t4, βred t1 t2 -> βred (Recₜ t1 t3 t4) (Recₜ t2 t3 t4)
  | β_rec2 : forall t1 t2 t3 t4, βred t2 t3 -> βred (Recₜ t1 t2 t4) (Recₜ t1 t3 t4)
  | β_rec3 : forall t1 t2 t3 t4, βred t3 t4 -> βred (Recₜ t1 t2 t3) (Recₜ t1 t2 t4)
  | β_succ : forall t1 t2, βred t1 t2 -> βred (Sₜ t1) (Sₜ t2)
  | β_ite1 : forall t1 t2 t3 t4, βred t1 t2 -> βred (IfThenElse t1 t3 t4) (IfThenElse t2 t3 t4)
  | β_ite2 : forall t1 t2 t3 t4, βred t2 t3 -> βred (IfThenElse t1 t2 t4) (IfThenElse t1 t3 t4)
  | β_ite3 : forall t1 t2 t3 t4, βred t3 t4 -> βred (IfThenElse t1 t2 t3) (IfThenElse t1 t2 t4)
  | β_abs : forall t1 t2, βred t1 t2 -> βred (λₜ t1) (λₜ t2)
  | β_app1 : forall t1 t2 t3, βred t1 t2 -> βred (t1 @ₜ t3) (t2 @ₜ t3)
  | β_app2 : forall t1 t2 t3, βred t2 t3 -> βred (t1 @ₜ t2) (t1 @ₜ t3)
  | β_pair1 : forall t1 t2 t3, βred t1 t2 -> βred (⟨ t1 , t3 ⟩) (⟨ t2 , t3 ⟩)
  | β_pair2 : forall t1 t2 t3, βred t2 t3 -> βred (⟨ t1 , t2 ⟩) (⟨ t1 , t3 ⟩)
  | β_proj1 : forall t1 t2, βred t1 t2 -> βred (π₁ t1) (π₁ t2)
  | β_proj2 : forall t1 t2, βred t1 t2 -> βred (π₂ t1) (π₂ t2)
  | β_inj1 : forall t1 t2, βred t1 t2 -> βred (κ₁ t1) (κ₁ t2)
  | β_inj2 : forall t1 t2, βred t1 t2 -> βred (κ₂ t1) (κ₂ t2)
  | β_delta1 : forall t1 t2 t3 t4, βred t1 t2 -> βred (delta t1 t3 t4) (delta t2 t3 t4)
  | β_delta2 : forall t1 t2 t3 t4, βred t2 t3 -> βred (delta t1 t2 t4) (delta t1 t3 t4)
  | β_delta3 : forall t1 t2 t3 t4, βred t3 t4 -> βred (delta t1 t2 t3) (delta t1 t2 t4)
  | β_deltaNil : forall t1 t2, βred t1 t2 -> βred (δb t1) (δb t2).

Notation "t ⊳ u" := (βred t u) (at level 68).
Notation "t ⊳+ u" := (βred >+ t u) (at level 68).
Notation "t ⊳* u" := (βred >* t u) (at level 68).
Notation "t =β u" := (βred >~ t u) (at level 68).

Lemma β_trans : forall (t u v : term), t ⊳* u -> u ⊳* v -> t ⊳* v.
Proof.
intros. apply (closure_rt_trans _ _ _ _ H H0).
Qed.

Lemma β_refl : forall (t : term), t ⊳* t.
Proof.
intro. apply rt_refl.
Qed.

Lemma β_add : forall (t u v : term), t ⊳* u -> u ⊳ v -> t ⊳* v.
Proof.
intros. apply (rt_add _ _ _ _ H H0).
Qed.

Lemma β_sub_star : forall (t u : term), t ⊳ u -> t ⊳* u.
Proof.
intros. apply (closure_R_in_rt _ _ _ H).
Qed.

(** The relation ⊳* is compatible, as ⊳ is compatible.*)

Definition compat (R : term -> term -> Prop) : Prop := (forall t1 t2, R t1 t2 -> R (λₜ t1) (λₜ t2))
  /\ (forall t1 t2 t3, R t1 t2 -> R (t1 @ₜ t3) (t2 @ₜ t3))
  /\ (forall t1 t2 t3, R t2 t3 -> R (t1 @ₜ t2) (t1 @ₜ t3))
  /\ (forall t1 t2, R t1 t2 -> R (Sₜ t1) (Sₜ t2))
  /\ (forall t1 t2 t3 t4, R t1 t2 -> R (Recₜ t1 t3 t4) (Recₜ t2 t3 t4))
  /\ (forall t1 t2 t3 t4, R t2 t3 -> R (Recₜ t1 t2 t4) (Recₜ t1 t3 t4))
  /\ (forall t1 t2 t3 t4, R t3 t4 -> R (Recₜ t1 t2 t3) (Recₜ t1 t2 t4))
  /\ (forall t1 t2 t3 t4, R t1 t2 -> R (IfThenElse t1 t3 t4) (IfThenElse t2 t3 t4))
  /\ (forall t1 t2 t3 t4, R t2 t3 -> R (IfThenElse t1 t2 t4) (IfThenElse t1 t3 t4))
  /\ (forall t1 t2 t3 t4, R t3 t4 -> R (IfThenElse t1 t2 t3) (IfThenElse t1 t2 t4))
  /\ (forall t1 t2 t3, R t1 t2 -> R (⟨ t1, t3 ⟩) (⟨ t2, t3 ⟩))
  /\ (forall t1 t2 t3, R t2 t3 -> R (⟨ t1, t2 ⟩) (⟨ t1, t3 ⟩))
  /\ (forall t1 t2, R t1 t2 -> R (π₁ t1) (π₁ t2))
  /\ (forall t1 t2, R t1 t2 -> R (π₂ t1) (π₂ t2))
  /\ (forall t1 t2, R t1 t2 -> R (κ₁ t1) (κ₁ t2))
  /\ (forall t1 t2, R t1 t2 -> R (κ₂ t1) (κ₂ t2))
  /\ (forall t1 t2 t3 t4, R t1 t2 -> R (delta t1 t3 t4) (delta t2 t3 t4))
  /\ (forall t1 t2 t3 t4, R t2 t3 -> R (delta t1 t2 t4) (delta t1 t3 t4))
  /\ (forall t1 t2 t3 t4, R t3 t4 -> R (delta t1 t2 t3) (delta t1 t2 t4))
  /\ (forall t1 t2, R t1 t2 -> R (δb t1) (δb t2)).

Lemma β_compat : compat (βred >*).
Proof.
split. intros. induction H. apply β_refl. apply (β_add _ (λₜ u) _); try apply IHrt_closure.
 apply β_abs. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (u @ₜ t3) _); try apply IHrt_closure.
 apply β_app1. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (t1 @ₜ u) _); try apply IHrt_closure.
 apply β_app2. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (Sₜ u) _); try apply IHrt_closure.
 apply β_succ. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (Recₜ u t3 t4)); try apply IHrt_closure.
 apply β_rec1. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (Recₜ t1 u t4)); try apply IHrt_closure.
 apply β_rec2. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (Recₜ t1 t2 u)); try apply IHrt_closure.
 apply β_rec3. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (IfThenElse u t3 t4));
try apply IHrt_closure. apply β_ite1. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (IfThenElse t1 u t4));
try apply IHrt_closure. apply β_ite2. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (IfThenElse t1 t2 u));
try apply IHrt_closure. apply β_ite3. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (⟨ u, t3 ⟩) _).
 apply IHrt_closure. apply β_pair1. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (⟨ t1, u ⟩) _).
 apply IHrt_closure. apply β_pair2. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (π₁ u) _).
 apply IHrt_closure. apply β_proj1. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (π₂ u) _).
 apply IHrt_closure. apply β_proj2. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (κ₁ u) _).
 apply IHrt_closure. apply β_inj1. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (κ₂ u) _).
 apply IHrt_closure. apply β_inj2. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (delta u t3 t4)); try apply IHrt_closure.
 apply β_delta1. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (delta t1 u t4)); try apply IHrt_closure.
 apply β_delta2. apply H0.
split. intros. induction H. apply β_refl. apply (β_add _ (delta t1 t2 u)); try apply IHrt_closure.
 apply β_delta3. apply H0.
intros. induction H. apply β_refl. apply (β_add _ (δb u) _).
 apply IHrt_closure. apply β_deltaNil. apply H0.
Qed.

(** We list here some properties of closure of both ⊳ and ⊳* : they are closed under lift, under
  substitution and over substitution for ⊳*.*)

Lemma lift_red : forall (t1 t2 : term) (n k : nat), t1 ⊳ t2 -> lift n k t1 ⊳ lift n k t2.
Proof.
intros. generalize n k. clear n k. induction H; simpl;intros.
 - apply β_NZ.
 - apply β_NS.
 - apply β_BT.
 - apply β_BF.
 - rewrite lift_subst_0_r. apply β_to.
 - apply β_times1.
 - apply β_times2.
 - rewrite lift_subst_0_r. apply β_plus1.
 - rewrite lift_subst_0_r. apply β_plus2.
 - apply β_rec1. apply IHβred.
 - apply β_rec2. apply IHβred.
 - apply β_rec3. apply IHβred.
 - apply β_succ. apply IHβred.
 - apply β_ite1. apply IHβred.
 - apply β_ite2. apply IHβred.
 - apply β_ite3. apply IHβred.
 - apply β_abs. apply IHβred.
 - apply β_app1. apply IHβred.
 - apply β_app2. apply IHβred.
 - apply β_pair1. apply IHβred.
 - apply β_pair2. apply IHβred.
 - apply β_proj1. apply IHβred.
 - apply β_proj2. apply IHβred.
 - apply β_inj1. apply IHβred.
 - apply β_inj2. apply IHβred.
 - apply β_delta1. apply IHβred.
 - apply β_delta2. apply IHβred.
 - apply β_delta3. apply IHβred.
 - apply β_deltaNil. apply IHβred.
Qed.

Lemma lift_red_star : forall (t u : term) (k n : nat), t ⊳* u -> lift k n t ⊳* lift k n u.
Proof.
intros. induction H. apply β_refl. apply (β_add _ (lift k n u)). apply IHrt_closure.
apply lift_red. apply H0.
Qed.

Lemma lift_red_rev_eq : forall (t u : term), t ⊳ u -> forall (k n : nat) (v w : term),
  t = lift k n v -> u = lift k n w -> v ⊳ w.
Proof.
intros t u H; induction H; intros; simpl.
  - assert (Recₜ t1 t2 zero = lift k n v); try apply H.
   symmetry in H. apply lift_compat_rec in H. destruct H. destruct H. destruct H.
   rewrite H in H1. simpl in H1. rewrite H0 in H1.
Admitted.

Lemma lift_red_rev : forall (t u : term) (k n : nat), lift k n t ⊳ lift k n u -> t ⊳ u.
Proof.
intros. specialize (lift_red_rev_eq (lift k n t) (lift k n u) H k n t u); intro.
apply H0; reflexivity.
Qed.

Lemma lift_red_inv : forall (t u : term) (k n : nat), lift k n t ⊳ u -> exists v : term, u = lift k n v.
Proof.
intros. induction t.
 - inversion H.
Admitted.

Lemma subst_red_r : forall (t1 t2 u : term), forall (n : nat), t1 ⊳ t2 -> {n ~> u} t1 ⊳ {n ~> u} t2.
Proof.
intros. generalize n u. clear n u. induction H;simpl;intros;firstorder.
 - apply β_NZ.
 - apply β_NS.
 - apply β_BT.
 - apply β_BF.
 - rewrite substi_comm_0. apply β_to.
 - apply β_times1.
 - apply β_times2.
 - rewrite substi_comm_0. apply β_plus1.
 - rewrite substi_comm_0. apply β_plus2.
 - apply β_rec1. apply IHβred.
 - apply β_rec2. apply IHβred.
 - apply β_rec3. apply IHβred.
 - apply β_succ. apply IHβred.
 - apply β_ite1. apply IHβred.
 - apply β_ite2. apply IHβred.
 - apply β_ite3. apply IHβred.
 - apply β_abs. apply IHβred.
 - apply β_app1. apply IHβred.
 - apply β_app2. apply IHβred.
 - apply β_pair1. apply IHβred.
 - apply β_pair2. apply IHβred.
 - apply β_proj1. apply IHβred.
 - apply β_proj2. apply IHβred.
 - apply β_inj1. apply IHβred.
 - apply β_inj2. apply IHβred.
 - apply β_delta1. apply IHβred.
 - apply β_delta2. apply IHβred.
 - apply β_delta3. apply IHβred.
 - apply β_deltaNil. apply IHβred.
Qed.

Lemma subst_red_r_star : forall (t1 t2 u : term), forall (n : nat), t1 ⊳* t2 ->
  {n ~> u} t1 ⊳* {n ~> u} t2.
Proof.
intros; induction H. apply β_refl. apply (β_add _ _ _ IHrt_closure). apply subst_red_r. apply H0.
Qed.

Lemma subst_red_l : forall (t u1 u2 : term), forall (n : nat), u1 ⊳ u2 ->
  {n ~> u1} t ⊳* {n ~> u2} t.
Proof.
intro t. induction t;simpl;intros.
  - case (n =? n0) eqn : H1. apply β_sub_star. apply H. case (n <? n0) eqn : H2.
    apply β_refl. apply β_refl.
  - apply (lift_red u1 u2 0 1) in H. apply (IHt (lift 0 1 u1) (lift 0 1 u2) (S n)) in H.
    apply β_compat. apply H.
  - apply (β_trans _ ({n ~> u2} t1 @ₜ {n ~> u1} t2) _). apply (IHt1 _ _ n) in H. apply β_compat.
    apply H. apply (IHt2 _ _ n) in H. apply β_compat. apply H.
  - apply β_refl.
  - apply β_compat. apply IHt. apply H.
  - apply (β_trans _ (Recₜ ({n ~> u2} t1) ({n ~> u2} t2) ({n ~> u1} t3))).
    apply (β_trans _ (Recₜ ({n ~> u2} t1) ({n ~> u1} t2) ({n ~> u1} t3))).
    apply (IHt1 _ _ n) in H. apply β_compat; apply H.
    apply (IHt2 _ _ n) in H; apply β_compat; apply H.
    apply (IHt3 _ _ n) in H; apply β_compat; apply H.
  - apply β_refl.
  - apply β_refl.
  - apply (β_trans _ (IfThenElse ({n ~> u2} t1) ({n ~> u2} t2) ({n ~> u1} t3))).
    apply (β_trans _ (IfThenElse ({n ~> u2} t1) ({n ~> u1} t2) ({n ~> u1} t3))).
    apply (IHt1 _ _ n) in H. apply β_compat; apply H.
    apply (IHt2 _ _ n) in H; apply β_compat; apply H.
    apply (IHt3 _ _ n) in H; apply β_compat; apply H.
  - apply (β_trans _ (⟨ {n ~> u2} t1 , {n ~> u1} t2⟩) _). apply (IHt1 _ _ n) in H. apply β_compat.
    apply H. apply (IHt2 _ _ n) in H. apply β_compat. apply H.
  - apply β_compat. apply IHt. apply H.
  - apply β_compat. apply IHt. apply H.
  - apply β_refl.
  - apply β_compat. apply IHt. apply H.
  - apply β_compat. apply IHt. apply H.
  - assert (u1 ⊳ u2). apply H. apply (lift_red u1 u2 0 1) in H.
    apply (β_trans _ (delta ({S n ~> lift 0 1 u2} t1) ({S n ~> lift 0 1 u2} t2) ({n ~> u1} t3))).
    apply (β_trans _ (delta ({S n ~> lift 0 1 u2} t1) ({S n ~> lift 0 1 u1} t2) ({n ~> u1} t3))).
    apply (IHt1 _ _ (S n)) in H. apply β_compat. apply H.
    apply (IHt2 _ _ (S n)) in H. apply β_compat. apply H.
    apply (IHt3 _ _ n) in H0. apply β_compat. apply H0.
  - apply β_compat. apply IHt. apply H.
Qed.

Lemma subst_red_l_star : forall (t u1 u2 : term), forall (n : nat), u1 ⊳* u2 ->
  {n ~> u1} t ⊳* {n ~> u2} t.
Proof.
intros. induction H. apply β_refl. apply (β_trans _ _ _ IHrt_closure).
apply subst_red_l. apply H0.
Qed.

(** C. Church-Rosser property.

We prove the Church-Rosser property for our lambda-calculus by the method of parallel reduction: we
  define a relation ⊳|| which can reduce several redexes in parallel, and prove that this reduction
  has the diamond property. What's more, we have ⊳⊆⊳||⊆⊳*, so ⊳||* = ⊳*, thus by using the fact
  that ⊳||* has the diamond property, so do ⊳*, giving us the Church-Rosser property for ⊳*.*)

Inductive par_red : term -> term -> Prop :=
  | par_var : forall n : nat, par_red {{n}} {{n}}
  | par_zero : par_red zero zero
  | par_Tt : par_red Tt Tt
  | par_Ff : par_red Ff Ff
  | par_star : par_red star star
  | par_beta_to : forall t t' u u', par_red t t' -> par_red u u' -> par_red (λₜ t @ₜ u) ({0 ~> u'} t')
  | par_beta_pair1 : forall t t' u u', par_red t t' -> par_red u u' -> par_red (π₁ (⟨ t , u ⟩)) t'
  | par_beta_pair2 : forall t t' u u', par_red t t' -> par_red u u' -> par_red (π₂ (⟨ t , u ⟩)) u'
  | par_beta_inj1 : forall t t' u u' v v', par_red t t' -> par_red u u' -> par_red v v' ->
    par_red (delta t u (κ₁ v)) ({0 ~> v'} t')
  | par_beta_inj2 : forall t t' u u' v v', par_red t t' -> par_red u u' -> par_red v v' ->
    par_red (delta t u (κ₂ v)) ({0 ~> v'} u')
  | par_beta_rec1 : forall t t' u u', par_red t t' -> par_red u u' -> par_red (Recₜ t u zero) t'
  | par_beta_rec2 : forall t t' u u' v v', par_red t t' -> par_red u u' -> par_red v v' ->
    par_red (Recₜ t u (Sₜ v)) ((u' @ₜ v') @ₜ (Recₜ t' u' v'))
  | par_beta_ite1 : forall t t' u u', par_red t t' -> par_red u u' -> par_red (IfThenElse Tt t u) t'
  | par_beta_ite2 : forall t t' u u', par_red t t' -> par_red u u' -> par_red (IfThenElse Ff t u) u'
  | par_app : forall t t' u u' : term, par_red t t' -> par_red u u' -> par_red (t @ₜ u) (t' @ₜ u')
  | par_abs : forall t u : term, par_red t u -> par_red (λₜ t) (λₜ u)
  | par_pair : forall t t' u u' : term, par_red t t' -> par_red u u' -> par_red (⟨ t , u ⟩) (⟨ t' , u' ⟩)
  | par_inj : forall t t' u u' v v', par_red t t' -> par_red u u' -> par_red v v' ->
    par_red (delta t u v) (delta t' u' v')
  | par_rec : forall t t' u u' v v', par_red t t' -> par_red u u' -> par_red v v' ->
    par_red (Recₜ t u v) (Recₜ t' u' v')
  | par_ite : forall t t' u u' v v', par_red t t' -> par_red u u' -> par_red v v' ->
    par_red (IfThenElse t u v) (IfThenElse t' u' v')
  | par_bot : forall t t', par_red t t' -> par_red (δb t) (δb t')
  | par_succ : forall t t', par_red t t' -> par_red (Sₜ t) (Sₜ t')
  | par_proj1 : forall t t', par_red t t' -> par_red (π₁ t) (π₁ t')
  | par_proj2 : forall t t', par_red t t' -> par_red (π₂ t) (π₂ t')
  | par_inj1 : forall t t', par_red t t' -> par_red (κ₁ t) (κ₁ t')
  | par_inj2 : forall t t', par_red t t' -> par_red (κ₂ t) (κ₂ t').

Notation "t ⊳|| u" := (par_red t u) (at level 68).
Notation "t ⊳||* u" := (par_red >* t u) (at level 68).

Lemma is_refl_par_red : forall t : term, t ⊳|| t.
Proof.
induction t.
 - apply par_var.
 - apply par_abs; apply IHt.
 - apply par_app; try apply IHt1; try apply IHt2.
 - apply par_zero.
 - apply par_succ; apply IHt.
 - apply par_rec; try apply IHt1; try apply IHt2; try apply IHt3.
 - apply par_Tt.
 - apply par_Ff.
 - apply par_ite; try apply IHt1; try apply IHt2; try apply IHt3.
 - apply par_pair; try apply IHt1; apply IHt2.
 - apply par_proj1; apply IHt.
 - apply par_proj2; apply IHt.
 - apply par_star.
 - apply par_inj1; apply IHt.
 - apply par_inj2; apply IHt.
 - apply par_inj; try apply IHt1; try apply IHt2; apply IHt3.
 - apply par_bot; apply IHt.
Qed.

Lemma red_in_par : forall t u : term, t ⊳ u -> t ⊳|| u.
Proof.
intros; induction H.
 - apply (par_beta_rec1 t1 t1 t2 t2); apply is_refl_par_red.
 - apply (par_beta_rec2 t1 t1 t2 t2 t3 t3); apply is_refl_par_red.
 - apply (par_beta_ite1 t1 t1 t2 t2); apply is_refl_par_red.
 - apply (par_beta_ite2 t1 t1 t2 t2); apply is_refl_par_red.
 - apply (par_beta_to t1 t1 t2 t2); apply is_refl_par_red.
 - apply (par_beta_pair1 t1 t1 t2 t2); apply is_refl_par_red.
 - apply (par_beta_pair2 t1 t1 t2 t2); apply is_refl_par_red.
 - apply (par_beta_inj1 t1 t1 t2 t2 t3 t3); apply is_refl_par_red.
 - apply (par_beta_inj2 t1 t1 t2 t2 t3 t3); apply is_refl_par_red.
 - apply (par_rec t1 t2 t3 t3 t4 t4); try apply is_refl_par_red; apply IHβred.
 - apply (par_rec t1 t1 t2 t3 t4 t4); try apply is_refl_par_red; apply IHβred.
 - apply (par_rec t1 t1 t2 t2 t3 t4); try apply is_refl_par_red; apply IHβred.
 - apply (par_succ t1 t2); apply IHβred.
 - apply (par_ite t1 t2 t3 t3 t4 t4); try apply is_refl_par_red; apply IHβred.
 - apply (par_ite t1 t1 t2 t3 t4 t4); try apply is_refl_par_red; apply IHβred.
 - apply (par_ite t1 t1 t2 t2 t3 t4); try apply is_refl_par_red; apply IHβred.
 - apply (par_abs t1 t2); apply IHβred.
 - apply (par_app t1 t2 t3 t3); try apply is_refl_par_red; apply IHβred.
 - apply (par_app t1 t1 t2 t3); try apply is_refl_par_red; apply IHβred.
 - apply (par_pair t1 t2 t3 t3); try apply is_refl_par_red; apply IHβred.
 - apply (par_pair t1 t1 t2 t3); try apply is_refl_par_red; apply IHβred.
 - apply par_proj1; apply IHβred.
 - apply par_proj2; apply IHβred.
 - apply par_inj1; apply IHβred.
 - apply par_inj2; apply IHβred.
 - apply (par_inj t1 t2 t3 t3 t4 t4); try apply is_refl_par_red; apply IHβred.
 - apply (par_inj t1 t1 t2 t3 t4 t4); try apply is_refl_par_red; apply IHβred.
 - apply (par_inj t1 t1 t2 t2 t3 t4); try apply is_refl_par_red; apply IHβred.
 - apply par_bot; apply IHβred.
Qed.

Lemma par_in_red_star : forall t u : term, t ⊳|| u -> t ⊳* u.
Proof.
intros; induction H; try apply β_refl.
 - apply (subst_red_r_star t t' u 0) in IHpar_red1.
   apply (subst_red_l_star t' u u' 0) in IHpar_red2.
   specialize (β_trans _ _ _ IHpar_red1 IHpar_red2); intro.
   apply (β_trans _ ({0 ~> u} t)). apply β_sub_star. apply β_to.
   apply H1.
 - apply (β_trans _ t). apply β_sub_star. apply β_times1. apply IHpar_red1.
 - apply (β_trans _ u). apply β_sub_star. apply β_times2. apply IHpar_red2.
 - apply (β_trans _ ({0 ~> v} t)). apply β_sub_star. apply β_plus1.
   apply (subst_red_r_star t t' v 0) in IHpar_red1.
   apply (subst_red_l_star t' v v' 0) in IHpar_red3.
   apply (β_trans _ _ _ IHpar_red1 IHpar_red3).
 - apply (β_trans _ ({0 ~> v} u)). apply β_sub_star. apply β_plus2.
   apply (subst_red_r_star u u' v 0) in IHpar_red2.
   apply (subst_red_l_star u' v v' 0) in IHpar_red3.
   apply (β_trans _ _ _ IHpar_red2 IHpar_red3).
 - apply (β_trans _ t). apply β_sub_star. apply β_NZ. apply IHpar_red1.
 - apply (β_trans _ (Recₜ t' u' (Sₜ v'))).
   assert (Recₜ t u (Sₜ v) ⊳* Recₜ t' u (Sₜ v)); try apply β_compat; try apply IHpar_red1.
   assert (Recₜ t' u (Sₜ v) ⊳* Recₜ t' u' (Sₜ v)); try apply β_compat; try apply IHpar_red2.
   assert (Recₜ t' u' (Sₜ v) ⊳* Recₜ t' u' (Sₜ v')); try apply β_compat;
   try apply β_compat; try apply IHpar_red3.
   apply (β_trans _ _ _ (β_trans _ _ _ H2 H3) H4).
   apply β_sub_star. apply β_NS.
 - apply (β_trans _ t). apply β_sub_star. apply β_BT. apply IHpar_red1.
 - apply (β_trans _ u). apply β_sub_star. apply β_BF. apply IHpar_red2.
 - apply (β_trans _ (t @ₜ u')). apply β_compat. apply IHpar_red2.
   apply β_compat. apply IHpar_red1.
 - apply β_compat; apply IHpar_red.
 - apply (β_trans _ (⟨ t , u' ⟩)). apply β_compat. apply IHpar_red2.
   apply β_compat. apply IHpar_red1.
 - apply (β_trans _ (delta t' u' v)). apply (β_trans _ (delta t' u v)).
   apply β_compat; apply IHpar_red1. apply β_compat; apply IHpar_red2.
   apply β_compat; apply IHpar_red3.
 - apply (β_trans _ (Recₜ t' u' v)). apply (β_trans _ (Recₜ t' u v)).
   apply β_compat; apply IHpar_red1. apply β_compat; apply IHpar_red2.
   apply β_compat; apply IHpar_red3.
 - apply (β_trans _ (IfThenElse t' u' v)). apply (β_trans _ (IfThenElse t' u v)).
   apply β_compat; apply IHpar_red1. apply β_compat; apply IHpar_red2.
   apply β_compat; apply IHpar_red3.
 - apply β_compat; apply IHpar_red.
 - apply β_compat; apply IHpar_red.
 - apply β_compat; apply IHpar_red.
 - apply β_compat; apply IHpar_red.
 - apply β_compat; apply IHpar_red.
 - apply β_compat; apply IHpar_red.
Qed.

Theorem red_par_trans_is_red_trans : forall (t u : term), t ⊳||* u <-> t ⊳* u.
Proof.
intros; split; intro. induction H. apply β_refl. apply (β_trans _ _ _ IHrt_closure).
apply par_in_red_star. apply H0. induction H. apply rt_refl.
apply (rt_add _ _ _ _ IHrt_closure). apply red_in_par in H0. apply H0.
Qed.

Lemma red_par_lift : forall (t t' : term) (k n : nat), t ⊳|| t' -> lift k n t ⊳|| lift k n t'.
Proof.
intros t t' k n H; generalize k n; clear k n; induction H; intros; simpl;
  try apply is_refl_par_red.
  - rewrite lift_subst_0_r. apply par_beta_to. apply IHpar_red1. apply IHpar_red2.
  - apply (par_beta_pair1 _ _ _ (lift k n u')); try (apply IHpar_red1; apply H);
    apply IHpar_red2; apply H0.
  - apply (par_beta_pair2 _ (lift k n t')); try (apply IHpar_red1; apply H);
    apply IHpar_red2; apply H0.
  - rewrite lift_subst_0_r. apply (par_beta_inj1 _ _ _ (lift (S k) n u')). apply IHpar_red1.
    apply IHpar_red2. apply IHpar_red3.
  - rewrite lift_subst_0_r. apply (par_beta_inj2 _ (lift (S k) n t')). apply IHpar_red1.
    apply IHpar_red2. apply IHpar_red3.
  - apply (par_beta_rec1 _ _ _ (lift k n u')). apply IHpar_red1.
    apply IHpar_red2.
  - apply par_beta_rec2. apply IHpar_red1. apply IHpar_red2. apply IHpar_red3.
  - apply (par_beta_ite1 _ _ _ (lift k n u')). apply IHpar_red1. apply IHpar_red2.
  - apply (par_beta_ite2 _ (lift k n t')). apply IHpar_red1. apply IHpar_red2.
  - apply par_app. apply IHpar_red1. apply IHpar_red2.
  - apply par_abs. apply IHpar_red.
  - apply par_pair. apply IHpar_red1. apply IHpar_red2.
  - apply par_inj. apply IHpar_red1. apply IHpar_red2. apply IHpar_red3.
  - apply par_rec. apply IHpar_red1. apply IHpar_red2. apply IHpar_red3.
  - apply par_ite. apply IHpar_red1. apply IHpar_red2. apply IHpar_red3.
  - apply par_bot. apply IHpar_red.
  - apply par_succ. apply IHpar_red.
  - apply par_proj1. apply IHpar_red.
  - apply par_proj2. apply IHpar_red.
  - apply par_inj1. apply IHpar_red.
  - apply par_inj2. apply IHpar_red.
Qed.

Lemma red_par_subst : forall (t t' u u' : term) (n : nat), t ⊳|| t' -> u ⊳|| u' ->
  {n ~> u} t ⊳|| {n ~> u'} t'.
Proof.
intros; generalize u u' n H0; clear u u' n H0; induction H; intros; simpl;
  try apply is_refl_par_red.
  - case (n =? n0) eqn : H1. apply H0. case (n <? n0) eqn : H2. apply is_refl_par_red.
    apply is_refl_par_red.
  - rewrite substi_comm_0. apply par_beta_to. apply IHpar_red1. apply red_par_lift. apply H1.
    apply IHpar_red2. apply H1.
  - apply (par_beta_pair1 _ _ _ _ (IHpar_red1 _ _ _ H1) (IHpar_red2 _ _ _ H1)).
  - apply (par_beta_pair2 _ _ _ _ (IHpar_red1 _ _ _ H1) (IHpar_red2 _ _ _ H1)).
  - rewrite substi_comm_0. apply (par_beta_inj1 _ _ _ ({S n ~> lift 0 1 u'0} u')).
    apply IHpar_red1. apply red_par_lift. apply H2. apply IHpar_red2. apply red_par_lift. apply H2.
    apply IHpar_red3. apply H2.
  - rewrite substi_comm_0. apply (par_beta_inj2 _ ({S n ~> lift 0 1 u'0} t')).
    apply IHpar_red1. apply red_par_lift. apply H2. apply IHpar_red2. apply red_par_lift. apply H2.
    apply IHpar_red3. apply H2.
  - apply (par_beta_rec1 _ _ _ _ (IHpar_red1 _ _ _ H1) (IHpar_red2 _ _ _ H1)).
  - apply (par_beta_rec2 _ _ _ _ _ _ (IHpar_red1 _ _ _ H2) (IHpar_red2 _ _ _ H2)
    (IHpar_red3 _ _ _ H2)).
  - apply (par_beta_ite1 _ _ _ _ (IHpar_red1 _ _ _ H1) (IHpar_red2 _ _ _ H1)).
  - apply (par_beta_ite2 _ _ _ _ (IHpar_red1 _ _ _ H1) (IHpar_red2 _ _ _ H1)).
  - apply par_app. apply IHpar_red1. apply H1. apply IHpar_red2. apply H1.
  - apply par_abs. apply IHpar_red. apply red_par_lift. apply H0.
  - apply par_pair. apply IHpar_red1. apply H1. apply IHpar_red2. apply H1.
  - apply par_inj. apply IHpar_red1. apply red_par_lift. apply H2. apply IHpar_red2.
    apply red_par_lift. apply H2. apply IHpar_red3. apply H2.
  - apply par_rec. apply IHpar_red1. apply H2. apply IHpar_red2. apply H2. apply IHpar_red3.
    apply H2.
  - apply par_ite. apply IHpar_red1. apply H2. apply IHpar_red2. apply H2. apply IHpar_red3.
    apply H2.
  - apply par_bot. apply IHpar_red. apply H0.
  - apply par_succ. apply IHpar_red. apply H0.
  - apply par_proj1. apply IHpar_red. apply H0.
  - apply par_proj2. apply IHpar_red. apply H0.
  - apply par_inj1. apply IHpar_red. apply H0.
  - apply par_inj2. apply IHpar_red. apply H0.
Qed.

Fixpoint total_red (t : term) : term :=
  match t with
    | {{n}} => {{n}}
    | Tt => Tt
    | Ff => Ff
    | star => star
    | zero => zero
    | Sₜ t => Sₜ (total_red t)
    | λₜ t => λₜ (total_red t)
    | (λₜ t) @ₜ u => {0 ~> total_red u} (total_red t)
    | t @ₜ u => total_red t @ₜ total_red u
    | ⟨ t , u ⟩ => ⟨ total_red t , total_red u ⟩
    | π₁ (⟨ t , u ⟩) => total_red t
    | π₂ (⟨ t , u ⟩) => total_red u
    | π₁ t => π₁ (total_red t)
    | π₂ t => π₂ (total_red t)
    | κ₁ t => κ₁ (total_red t)
    | κ₂ t => κ₂ (total_red t)
    | delta t u (κ₁ v) => {0 ~> total_red v} (total_red t)
    | delta t u (κ₂ v) => {0 ~> total_red v} (total_red u)
    | delta t u v => delta (total_red t) (total_red u) (total_red v)
    | δb t => δb (total_red t)
    | IfThenElse Tt u v => total_red u
    | IfThenElse Ff u v => total_red v
    | IfThenElse t u v => IfThenElse (total_red t) (total_red u) (total_red v)
    | Recₜ t u zero => total_red t
    | Recₜ t u (Sₜ v) => ((total_red u) @ₜ (total_red v)) @ₜ
      (Recₜ (total_red t) (total_red u) (total_red v))
    | Recₜ t u v => Recₜ (total_red t) (total_red u) (total_red v)
  end.

Lemma red_par_to_total : forall (t u : term), t ⊳|| u -> u ⊳|| total_red t.
Proof.
intro t ; induction t; intros; simpl; try (inversion H; apply is_refl_par_red).
  - inversion H. apply par_abs. apply IHt. apply H1.
  - inversion H. apply red_par_subst. apply par_abs in H2. rewrite H0 in H2.
    apply IHt1 in H2. rewrite <- H0 in H2. simpl in H2. inversion H2. apply H7.
    apply IHt2. apply H4. case t1 eqn : H5;
      try apply (par_app _ _ _ _ (IHt1 t' H2) (IHt2 u' H4)).
    inversion H2. rewrite <- H8 in H2.
    specialize (IHt1 (λₜ u1) H2). specialize (IHt2 u' H4). simpl in IHt1.
    inversion IHt1.
    specialize (par_beta_to _ _ _ _ H11 IHt2); intro. apply H12.
  - inversion H. apply par_succ. apply IHt. apply H1.
  - inversion H. apply IHt1. apply H4. apply par_app. apply par_app.
    apply IHt2. apply H5. apply par_succ in H6. rewrite H2 in H6. specialize (IHt3 _ H6).
    rewrite <- H2 in IHt3. simpl in IHt3. inversion IHt3. apply H9.
    apply par_rec. apply IHt1. apply H3. apply IHt2. apply H5.
    apply par_succ in H6. rewrite H2 in H6. specialize (IHt3 _ H6).
    rewrite <- H2 in IHt3. simpl in IHt3. inversion IHt3. apply H9.
    case t3 eqn : H7; try apply (par_rec _ _ _ _ _ _ (IHt1 _ H3) (IHt2 _ H5) (IHt3 _ H6)).
    inversion H6. apply (par_beta_rec1 _ _ _ (total_red t2)). apply IHt1. apply H3.
    apply IHt2. apply H5. inversion H6. apply par_beta_rec2.
    apply IHt1. apply H3. apply IHt2. apply H5. specialize (IHt3 v' H6).
    rewrite <- H10 in IHt3. simpl in IHt3. inversion IHt3. apply H13.
  - inversion H. apply IHt2. apply H4. apply IHt3. apply H5.
    case t1 eqn : H7; try apply (par_ite _ _ _ _ _ _ (IHt1 _ H3) (IHt2 _ H5) (IHt3 _ H6)).
    inversion H3. apply (par_beta_ite1 _ _ _ (total_red t3)). apply IHt2. apply H5. apply IHt3.
    apply H6. inversion H3. apply (par_beta_ite2 _ (total_red t2)). apply IHt2. apply H5.
    apply IHt3. apply H6.
  - inversion H. apply par_pair. apply IHt1. apply H2. apply IHt2. apply H4.
  - inversion H. rewrite <- H0 in IHt. specialize (IHt (⟨u, u'⟩) (par_pair _ _ _ _ H1 H2)).
    inversion IHt. apply H7. case t eqn : H3; try (apply par_proj1; apply IHt; apply H1).
    inversion H1. specialize (IHt (⟨ t'0,u' ⟩) (par_pair _ _ _ _ H6 H8)). simpl in IHt.
    inversion IHt. specialize (par_beta_pair1 _ _ _ _ H12 H14); intro. apply H15.
  - inversion H. rewrite <- H0 in IHt. specialize (IHt (⟨t', u⟩) (par_pair _ _ _ _ H1 H2)).
    inversion IHt. apply H9. case t eqn : H3; try (apply par_proj2; apply IHt; apply H1).
    inversion H1. specialize (IHt (⟨ t'0,u' ⟩) (par_pair _ _ _ _ H6 H8)). simpl in IHt.
    inversion IHt. specialize (par_beta_pair2 _ _ _ _ H12 H14); intro. apply H15.
  - inversion H. apply par_inj1. apply IHt. apply H1.
  - inversion H. apply par_inj2. apply IHt. apply H1.
  - inversion H. apply red_par_subst. apply IHt1. apply H3. apply par_inj1 in H6.
    rewrite H2 in H6. apply IHt3 in H6. rewrite <- H2 in H6. simpl in H6. inversion H6.
    apply H9. apply red_par_subst. apply IHt2. apply H5. apply par_inj2 in H6.
    rewrite H2 in H6. apply IHt3 in H6. rewrite <- H2 in H6. simpl in H6. inversion H6.
    apply H9. case t3 eqn : H7;try apply (par_inj _ _ _ _ _ _ (IHt1 _ H3) (IHt2 _ H5) (IHt3 _ H6)).
    inversion H6. specialize (IHt3 _ H6). rewrite <- H10 in IHt3. simpl in IHt3. inversion IHt3.
    apply (par_beta_inj1 _ _ _ _ _ _ (IHt1 _ H3) (IHt2 _ H5) H13).
    inversion H6. specialize (IHt3 _ H6). rewrite <- H10 in IHt3. simpl in IHt3. inversion IHt3.
    apply (par_beta_inj2 _ _ _ _ _ _ (IHt1 _ H3) (IHt2 _ H5) H13).
  - inversion H. apply par_bot. apply IHt. apply H1.
Qed.

Lemma red_par_diamond : Diamond_prop par_red.
Proof.
unfold Diamond_prop. intros.
exists (total_red t). split; apply red_par_to_total; apply H.
Qed.

Lemma red_par_confl : Confluence par_red.
Proof.
apply diamond_gives_confluence. apply red_par_diamond.
Qed.

Theorem Church_Rosser : Confluence βred.
Proof.
apply confluence_is_rt_diamond. apply (diamond_stable_equiv _ _ red_par_trans_is_red_trans).
apply -> confluence_is_rt_diamond. apply red_par_confl.
Qed.

Corollary join_βeq : forall (t u : term), t =β u -> exists v : term, t ⊳* v /\ u ⊳* v.
Proof.
intros. assert (Church_Rosser_prop βred). apply CR_equiv_confluence. apply Church_Rosser.
apply H0. apply H.
Qed.