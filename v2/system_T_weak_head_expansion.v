Require Import system_T_first_def.
Require Import system_T_substi.
Require Import system_T_reduction.
Require Import system_T_normal_form_SN.
Require Import system_T_context_wh_red.
Require Import PeanoNat.
Require Import List.

(* ********************************************************************************************* *)

(** II. The structure of SN *)

(** 7. Weak head expansion.

This file contains the proof of the main result allowing our next constructions to work, which is
  the weak head expansion : under certain conditions, we have that if t ⊳ₕ u and SN (E [u]), then
  SN (E [t]). To prove this, we first prove the weak standardization lemma, which describes the
  possible reductions appearing in E [t] ⊳ u where t is a redex.*)

(** A. Weak standardization.*)

Lemma weak_stand_lambda : forall (E : Elim) (t u v : term), E [ₑ λₜ t @ₜ u ] ⊳ v ->
  (v = E [ₑ {0 ~> u} t]) \/ (exists E' : Elim, E ⊳ₑ E' /\ v = E' [ₑ λₜ t @ₜ u]) \/
  (exists t' : term, t ⊳ t' /\ v = E [ₑ λₜ t' @ₜ u]) \/
  (exists u' : term, u ⊳ u' /\ v = E [ₑ λₜ t @ₜ u']).
Proof.
induction E; intros; simpl.
 - inversion H.
  + left. reflexivity.
  + inversion H3. right. right. left. exists t4. split. apply H5. reflexivity.
  + right. right. right. exists t3. split. apply H3. reflexivity.
 - simpl in H. inversion H.
  + rewrite <- H0 in H. rewrite <- H1 in H. exfalso.
    assert (forall (E : Elim) (t u v : term), E [ₑ t @ₜ u] <> (λₜ v)).
    induction E0;intros;simpl;intro; try inversion H3. symmetry in H1. apply H3 in H1. apply H1.
  + apply IHE in H3. destruct H3. left. rewrite H3. reflexivity.
    right. destruct H3. destruct H3. left. exists (apli x t). simpl. split.
    apply appβE1. apply H3. f_equal. apply H3. right.
    destruct H3. destruct H3. left. exists x. split. apply H3. f_equal. apply H3.
    destruct H3. right. exists x. split; try f_equal; apply H3.
  + right. left. exists (apli E t3). split. apply appβE2. apply H3. reflexivity.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ λₜ t @ₜ u]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj1 x). split. apply projβE1. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    destruct H1. right. right. right. exists x. split; try (simpl; f_equal); apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ λₜ t @ₜ u]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left; reflexivity.
    right. destruct H1. left. destruct H1. exists (proj2 x). split. apply projβE2; apply H1.
    simpl; f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x. split; try (f_equal); apply H1.
    destruct H1. right. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), κ₁ t <> E [ₑ λₜ u @ₜ v]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), κ₂ t <> E [ₑ λₜ u @ₜ v]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (cases t3 t0 E). split; simpl; try reflexivity.
    apply casesβE1. apply H4.
  + right. left. exists (cases t t4 E). split; simpl; try reflexivity.
    apply casesβE2. apply H4.
  + apply IHE in H4. destruct H4. left. rewrite H4. reflexivity.
    right. destruct H4. destruct H4. left. exists (cases t t0 x).
    split; simpl; try f_equal; try (apply casesβE3; try reflexivity); apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H. apply IHE in H1. destruct H1.
  + left. rewrite H1. reflexivity.
  + right. destruct H1. destruct H1. left. exists (casebot x).
    split; simpl; try apply casebotβE; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x.
    split; simpl; try f_equal; apply H1.
    right. destruct H1. exists x. split; simpl; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), zero <> E [ₑ λₜ t @ₜ u]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), Sₜ t <> E [ₑ λₜ u @ₜ v]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (recel t3 t0 E). split; try reflexivity.
    apply recelβE1. apply H4.
  + right. left. exists (recel t t4 E). split; try reflexivity.
    apply recelβE2. apply H4.
  + apply IHE in H4. destruct H4.
    left. f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists (recel t t0 x).
    split; simpl; try f_equal; try apply recelβE3; apply H4.
    right. destruct H4.
    left. destruct H4. exists x. split; simpl; try f_equal; apply H4.
    right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), Tt <> E [ₑ λₜ t @ₜ u]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + assert (forall (E : Elim) (t u : term), Ff <> E [ₑ λₜ t @ₜ u]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + apply IHE in H4. destruct H4.
   left. rewrite H4. reflexivity.
   right. destruct H4. left. destruct H4. exists (ifel x t t0).
   split; simpl; try f_equal; try apply ifelβE1; apply H4.
   right. destruct H4. left. destruct H4. exists x.
   split; simpl; try f_equal; apply H4.
   right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
  + right. left. exists (ifel E t4 t0). split; try reflexivity.
    apply ifelβE2. apply H4.
  + right. left. exists (ifel E t t5). split; try reflexivity; apply ifelβE3; apply H4.
Qed.

Lemma weak_stand_pair1 : forall (E : Elim) (t u v : term), E [ₑ (π₁ (⟨ t , u ⟩))] ⊳ v ->
  (v = E [ₑ t]) \/ (exists (E' : Elim), E ⊳ₑ E' /\ v = E' [ₑ π₁ (⟨ t , u ⟩)]) \/
  (exists (t' : term), t ⊳ t' /\ v = E [ₑ π₁ (⟨ t' , u ⟩)]) \/
  (exists (u' : term), u ⊳ u' /\ v = E [ₑ π₁ (⟨ t , u' ⟩)]).
Proof.
induction E; intros; simpl.
 - simpl in H. inversion H.
  + left. reflexivity.
  + inversion H2. right. right. inversion H1. left. exists t3.
    split; try reflexivity; apply H7. right. exists t4. split; try reflexivity; apply H7.
 - simpl in H. inversion H.
  + rewrite <- H0 in H. rewrite <- H1 in H. exfalso.
    assert (forall (E : Elim) (t u v : term), E [ₑ π₁ (⟨ t , u ⟩)] <> (λₜ v)).
    induction E0;intros;simpl;intro; try inversion H3. symmetry in H1. apply H3 in H1. apply H1.
  + apply IHE in H3. destruct H3. left. rewrite H3. reflexivity.
    right. destruct H3. destruct H3. left. exists (apli x t). simpl. split.
    apply appβE1. apply H3. f_equal. apply H3. right.
    destruct H3. destruct H3. left. exists x. split. apply H3. f_equal. apply H3.
    destruct H3. right. exists x. split; try f_equal; apply H3.
  + right. left. exists (apli E t3). split. apply appβE2. apply H3. reflexivity.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ π₁ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj1 x). split. apply projβE1. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    destruct H1. right. right. right. exists x. split; try (simpl; f_equal); apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ π₁ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left; reflexivity.
    right. destruct H1. left. destruct H1. exists (proj2 x). split. apply projβE2; apply H1.
    simpl; f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x. split; try (f_equal); apply H1.
    destruct H1. right. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), κ₁ t <> E [ₑ π₁ (⟨ u , v ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), κ₂ t <> E [ₑ π₁ (⟨ u , v ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (cases t3 t0 E). split; simpl; try reflexivity.
    apply casesβE1. apply H4.
  + right. left. exists (cases t t4 E). split; simpl; try reflexivity.
    apply casesβE2. apply H4.
  + apply IHE in H4. destruct H4. left. rewrite H4. reflexivity.
    right. destruct H4. destruct H4. left. exists (cases t t0 x).
    split; simpl; try f_equal; try (apply casesβE3; try reflexivity); apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H. apply IHE in H1. destruct H1.
  + left. rewrite H1. reflexivity.
  + right. destruct H1. destruct H1. left. exists (casebot x).
    split; simpl; try apply casebotβE; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x.
    split; simpl; try f_equal; apply H1.
    right. destruct H1. exists x. split; simpl; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), zero <> E [ₑ π₁ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), Sₜ t <> E [ₑ π₁ (⟨ u , v ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (recel t3 t0 E). split; try reflexivity.
    apply recelβE1. apply H4.
  + right. left. exists (recel t t4 E). split; try reflexivity.
    apply recelβE2. apply H4.
  + apply IHE in H4. destruct H4.
    left. f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists (recel t t0 x).
    split; simpl; try f_equal; try apply recelβE3; apply H4.
    right. destruct H4.
    left. destruct H4. exists x. split; simpl; try f_equal; apply H4.
    right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), Tt <> E [ₑ π₁ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + assert (forall (E : Elim) (t u : term), Ff <> E [ₑ π₁ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + apply IHE in H4. destruct H4.
   left. rewrite H4. reflexivity.
   right. destruct H4. left. destruct H4. exists (ifel x t t0).
   split; simpl; try f_equal; try apply ifelβE1; apply H4.
   right. destruct H4. left. destruct H4. exists x.
   split; simpl; try f_equal; apply H4.
   right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
  + right. left. exists (ifel E t4 t0). split; try reflexivity.
    apply ifelβE2. apply H4.
  + right. left. exists (ifel E t t5). split; try reflexivity; apply ifelβE3; apply H4.
Qed.

Lemma weak_stand_pair2 : forall (E : Elim) (t u v : term), E [ₑ (π₂ (⟨ t , u ⟩))] ⊳ v ->
  (v = E [ₑ u]) \/ (exists (E' : Elim), E ⊳ₑ E' /\ v = E' [ₑ π₂ (⟨ t , u ⟩)]) \/
  (exists (t' : term), t ⊳ t' /\ v = E [ₑ π₂ (⟨ t' , u ⟩)]) \/
  (exists (u' : term), u ⊳ u' /\ v = E [ₑ π₂ (⟨ t , u' ⟩)]).
Proof.
induction E; intros; simpl.
 - simpl in H. inversion H.
  + left. reflexivity.
  + inversion H2. right. right. inversion H1. left. exists t3.
    split; try reflexivity; apply H7. right. exists t4. split; try reflexivity; apply H7.
 - simpl in H. inversion H.
  + rewrite <- H0 in H. rewrite <- H1 in H. exfalso.
    assert (forall (E : Elim) (t u v : term), E [ₑ π₂ (⟨ t , u ⟩)] <> (λₜ v)).
    induction E0;intros;simpl;intro; try inversion H3. symmetry in H1. apply H3 in H1. apply H1.
  + apply IHE in H3. destruct H3. left. rewrite H3. reflexivity.
    right. destruct H3. destruct H3. left. exists (apli x t). simpl. split.
    apply appβE1. apply H3. f_equal. apply H3. right.
    destruct H3. destruct H3. left. exists x. split. apply H3. f_equal. apply H3.
    destruct H3. right. exists x. split; try f_equal; apply H3.
  + right. left. exists (apli E t3). split. apply appβE2. apply H3. reflexivity.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ π₂ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj1 x). split. apply projβE1. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    destruct H1. right. right. right. exists x. split; try (simpl; f_equal); apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ π₂ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left; reflexivity.
    right. destruct H1. left. destruct H1. exists (proj2 x). split. apply projβE2; apply H1.
    simpl; f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x. split; try (f_equal); apply H1.
    destruct H1. right. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), κ₁ t <> E [ₑ π₂ (⟨ u , v ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), κ₂ t <> E [ₑ π₂ (⟨ u , v ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (cases t3 t0 E). split; simpl; try reflexivity.
    apply casesβE1. apply H4.
  + right. left. exists (cases t t4 E). split; simpl; try reflexivity.
    apply casesβE2. apply H4.
  + apply IHE in H4. destruct H4. left. rewrite H4. reflexivity.
    right. destruct H4. destruct H4. left. exists (cases t t0 x).
    split; simpl; try f_equal; try (apply casesβE3; try reflexivity); apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H. apply IHE in H1. destruct H1.
  + left. rewrite H1. reflexivity.
  + right. destruct H1. destruct H1. left. exists (casebot x).
    split; simpl; try apply casebotβE; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x.
    split; simpl; try f_equal; apply H1.
    right. destruct H1. exists x. split; simpl; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), zero <> E [ₑ π₂ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), Sₜ t <> E [ₑ π₂ (⟨ u , v ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (recel t3 t0 E). split; try reflexivity.
    apply recelβE1. apply H4.
  + right. left. exists (recel t t4 E). split; try reflexivity.
    apply recelβE2. apply H4.
  + apply IHE in H4. destruct H4.
    left. f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists (recel t t0 x).
    split; simpl; try f_equal; try apply recelβE3; apply H4.
    right. destruct H4.
    left. destruct H4. exists x. split; simpl; try f_equal; apply H4.
    right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), Tt <> E [ₑ π₂ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + assert (forall (E : Elim) (t u : term), Ff <> E [ₑ π₂ (⟨ t , u ⟩)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + apply IHE in H4. destruct H4.
   left. rewrite H4. reflexivity.
   right. destruct H4. left. destruct H4. exists (ifel x t t0).
   split; simpl; try f_equal; try apply ifelβE1; apply H4.
   right. destruct H4. left. destruct H4. exists x.
   split; simpl; try f_equal; apply H4.
   right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
  + right. left. exists (ifel E t4 t0). split; try reflexivity.
    apply ifelβE2. apply H4.
  + right. left. exists (ifel E t t5). split; try reflexivity; apply ifelβE3; apply H4.
Qed.

Lemma weak_stand_inj1 : forall (E : Elim) (t u v w : term), E [ₑ (δ(0 ↦ t |0 ↦ u) (κ₁ v))] ⊳ w ->
  w = E [ₑ({0 ~> v} t)] \/ (exists (E' : Elim), E ⊳ₑ E' /\ w = E' [ₑ (δ(0 ↦ t |0 ↦ u) (κ₁ v))]) \/
  (exists (t' : term), t ⊳ t' /\ w = E [ₑ (δ(0 ↦ t' |0 ↦ u) (κ₁ v))]) \/
  (exists (u' : term), u ⊳ u' /\ w = E [ₑ (δ(0 ↦ t |0 ↦ u') (κ₁ v))]) \/
  (exists (v' : term), v ⊳ v' /\ w = E [ₑ (δ(0 ↦ t |0 ↦ u) (κ₁ v'))]).
Proof.
induction E; intros; simpl.
 - simpl in H. inversion H.
  + left. reflexivity.
  + right. right. left. exists t2.
    split; try reflexivity. apply H4.
  + right. right. right. left. exists t3; split; try reflexivity; apply H4.
  + right. right. right. right. inversion H4. exists t5; split; try reflexivity; apply H6.
 - simpl in H. inversion H.
  + rewrite <- H0 in H. rewrite <- H1 in H. exfalso.
    assert (forall (E : Elim) (t u v w : term), (λₜ t) <> E [ₑ delta u v (κ₁ w)]).
    induction E0;intros;simpl;intro; try inversion H3. apply H3 in H1. apply H1.
  + apply IHE in H3. destruct H3. left. rewrite H3. reflexivity.
    right. destruct H3. destruct H3. left. exists (apli x t). simpl. split.
    apply appβE1. apply H3. f_equal. apply H3. right.
    destruct H3. destruct H3. left. exists x. split. apply H3. f_equal. apply H3.
    right. destruct H3. left. destruct H3. exists x. split; try f_equal; apply H3.
    right. destruct H3. exists x. split; try f_equal; apply H3.
  + right. left. exists (apli E t3). split. apply appβE2. apply H3. reflexivity.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ delta t u (κ₁ v)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj1 x). split. apply projβE1. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    right. right. right. destruct H1. left. destruct H1. exists x. split; try f_equal; apply H1.
    right. destruct H1. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ delta t u (κ₁ v)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj2 x). split. apply projβE2. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    right. right. right. destruct H1. left. destruct H1. exists x. split; try f_equal; apply H1.
    right. destruct H1. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v w : term), κ₁ t <> E [ₑ delta u v (κ₁ w)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v w : term), κ₂ t <> E [ₑ delta u v (κ₁ w)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (cases t3 t0 E). split; simpl; try reflexivity.
    apply casesβE1. apply H4.
  + right. left. exists (cases t t4 E). split; simpl; try reflexivity.
    apply casesβE2. apply H4.
  + apply IHE in H4. destruct H4. left. rewrite H4. reflexivity.
    right. destruct H4. destruct H4. left. exists (cases t t0 x).
    split; simpl; try f_equal; try (apply casesβE3; try reflexivity); apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H. apply IHE in H1. destruct H1.
  + left. rewrite H1. reflexivity.
  + right. destruct H1. destruct H1. left. exists (casebot x).
    split; simpl; try apply casebotβE; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x.
    split; simpl; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x. split; try f_equal; apply H1.
    right. destruct H1. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), zero <> E [ₑ delta t u (κ₁ v)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v w : term), Sₜ t <> E [ₑ delta u v (κ₁ w)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (recel t3 t0 E). split; try reflexivity.
    apply recelβE1. apply H4.
  + right. left. exists (recel t t4 E). split; try reflexivity.
    apply recelβE2. apply H4.
  + apply IHE in H4. destruct H4.
    left. f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists (recel t t0 x).
    split; simpl; try f_equal; try apply recelβE3; apply H4.
    right. destruct H4.
    left. destruct H4. exists x. split; simpl; try f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), Tt <> E [ₑ delta t u (κ₁ v)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + assert (forall (E : Elim) (t u v : term), Ff <> E [ₑ delta t u (κ₁ v)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + apply IHE in H4. destruct H4.
   left. rewrite H4. reflexivity.
   right. destruct H4. left. destruct H4. exists (ifel x t t0).
   split; simpl; try f_equal; try apply ifelβE1; apply H4.
   right. destruct H4. left. destruct H4. exists x.
   split; simpl; try f_equal; apply H4.
   right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
  + right. left. exists (ifel E t4 t0). split; try reflexivity.
    apply ifelβE2. apply H4.
  + right. left. exists (ifel E t t5). split; try reflexivity; apply ifelβE3; apply H4.
Qed.

Lemma weak_stand_inj2 : forall (E : Elim) (t u v w : term), E [ₑ (δ(0 ↦ t |0 ↦ u) (κ₂ v))] ⊳ w ->
  w = E [ₑ ({0 ~> v} u)] \/ (exists (E' : Elim), E ⊳ₑ E' /\ w = E' [ₑ (δ(0 ↦ t |0 ↦ u) (κ₂ v))]) \/
  (exists (t' : term), t ⊳ t' /\ w = E [ₑ (δ(0 ↦ t' |0 ↦ u) (κ₂ v))]) \/
  (exists (u' : term), u ⊳ u' /\ w = E [ₑ (δ(0 ↦ t |0 ↦ u') (κ₂ v))]) \/
  (exists (v' : term), v ⊳ v' /\ w = E [ₑ (δ(0 ↦ t |0 ↦ u) (κ₂ v'))]).
Proof.
induction E; intros; simpl.
 - simpl in H. inversion H.
  + left. reflexivity.
  + right. right. left. exists t2.
    split; try reflexivity. apply H4.
  + right. right. right. left. exists t3; split; try reflexivity; apply H4.
  + right. right. right. right. inversion H4. exists t5; split; try reflexivity; apply H6.
 - simpl in H. inversion H.
  + rewrite <- H0 in H. rewrite <- H1 in H. exfalso.
    assert (forall (E : Elim) (t u v w : term), (λₜ t) <> E [ₑ delta u v (κ₂ w)]).
    induction E0;intros;simpl;intro; try inversion H3. apply H3 in H1. apply H1.
  + apply IHE in H3. destruct H3. left. rewrite H3. reflexivity.
    right. destruct H3. destruct H3. left. exists (apli x t). simpl. split.
    apply appβE1. apply H3. f_equal. apply H3. right.
    destruct H3. destruct H3. left. exists x. split. apply H3. f_equal. apply H3.
    right. destruct H3. left. destruct H3. exists x. split; try f_equal; apply H3.
    right. destruct H3. exists x. split; try f_equal; apply H3.
  + right. left. exists (apli E t3). split. apply appβE2. apply H3. reflexivity.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ delta t u (κ₂ v)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj1 x). split. apply projβE1. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    right. right. right. destruct H1. left. destruct H1. exists x. split; try f_equal; apply H1.
    right. destruct H1. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ delta t u (κ₂ v)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj2 x). split. apply projβE2. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    right. right. right. destruct H1. left. destruct H1. exists x. split; try f_equal; apply H1.
    right. destruct H1. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v w : term), κ₁ t <> E [ₑ delta u v (κ₂ w)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v w : term), κ₂ t <> E [ₑ delta u v (κ₂ w)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (cases t3 t0 E). split; simpl; try reflexivity.
    apply casesβE1. apply H4.
  + right. left. exists (cases t t4 E). split; simpl; try reflexivity.
    apply casesβE2. apply H4.
  + apply IHE in H4. destruct H4. left. rewrite H4. reflexivity.
    right. destruct H4. destruct H4. left. exists (cases t t0 x).
    split; simpl; try f_equal; try (apply casesβE3; try reflexivity); apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H. apply IHE in H1. destruct H1.
  + left. rewrite H1. reflexivity.
  + right. destruct H1. destruct H1. left. exists (casebot x).
    split; simpl; try apply casebotβE; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x.
    split; simpl; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x. split; try f_equal; apply H1.
    right. destruct H1. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), zero <> E [ₑ delta t u (κ₂ v)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v w : term), Sₜ t <> E [ₑ delta u v (κ₂ w)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (recel t3 t0 E). split; try reflexivity.
    apply recelβE1. apply H4.
  + right. left. exists (recel t t4 E). split; try reflexivity.
    apply recelβE2. apply H4.
  + apply IHE in H4. destruct H4.
    left. f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists (recel t t0 x).
    split; simpl; try f_equal; try apply recelβE3; apply H4.
    right. destruct H4.
    left. destruct H4. exists x. split; simpl; try f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), Tt <> E [ₑ delta t u (κ₂ v)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + assert (forall (E : Elim) (t u v : term), Ff <> E [ₑ delta t u (κ₂ v)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + apply IHE in H4. destruct H4.
   left. rewrite H4. reflexivity.
   right. destruct H4. left. destruct H4. exists (ifel x t t0).
   split; simpl; try f_equal; try apply ifelβE1; apply H4.
   right. destruct H4. left. destruct H4. exists x.
   split; simpl; try f_equal; apply H4.
   right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
  + right. left. exists (ifel E t4 t0). split; try reflexivity.
    apply ifelβE2. apply H4.
  + right. left. exists (ifel E t t5). split; try reflexivity; apply ifelβE3; apply H4.
Qed.

Lemma weak_stand_rec1 : forall (E : Elim) (t u v : term), E [ₑ (Recₜ t u zero)] ⊳ v ->
  v = E [ₑ t] \/ (exists (E' : Elim), E ⊳ₑ E' /\ v = E' [ₑ (Recₜ t u zero)]) \/
  (exists (t' : term), t ⊳ t' /\ v = E [ₑ (Recₜ t' u zero)]) \/
  (exists (u' : term), u ⊳ u' /\ v = E [ₑ (Recₜ t u' zero)]).
Proof.
induction E; intros; simpl.
 - simpl in H. inversion H.
  + left. reflexivity.
  + right. right. left. exists t2. split; try reflexivity; apply H4.
  + right. right. right. exists t3. split; try reflexivity; apply H4.
  + inversion H4.
 - simpl in H. inversion H.
  + rewrite <- H0 in H. rewrite <- H1 in H. exfalso.
    assert (forall (E : Elim) (t u v : term), (λₜ t) <> E [ₑ Recₜ u v zero]).
    induction E0;intros;simpl;intro; try inversion H3. apply H3 in H1. apply H1.
  + apply IHE in H3. destruct H3. left. rewrite H3. reflexivity.
    right. destruct H3. destruct H3. left. exists (apli x t). simpl. split.
    apply appβE1. apply H3. f_equal. apply H3. right.
    destruct H3. destruct H3. left. exists x. split. apply H3. f_equal. apply H3.
    destruct H3. right. exists x. split; try f_equal; apply H3.
  + right. left. exists (apli E t3). split. apply appβE2. apply H3. reflexivity.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ Recₜ u v zero]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj1 x). split. apply projβE1. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    destruct H1. right. right. right. exists x. split; try (simpl; f_equal); apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ Recₜ u v zero]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left; reflexivity.
    right. destruct H1. left. destruct H1. exists (proj2 x). split. apply projβE2; apply H1.
    simpl; f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x. split; try (f_equal); apply H1.
    destruct H1. right. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), κ₁ t <> E [ₑ Recₜ u v zero]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), κ₂ t <> E [ₑ Recₜ u v zero]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (cases t3 t0 E). split; simpl; try reflexivity.
    apply casesβE1. apply H4.
  + right. left. exists (cases t t4 E). split; simpl; try reflexivity.
    apply casesβE2. apply H4.
  + apply IHE in H4. destruct H4. left. rewrite H4. reflexivity.
    right. destruct H4. destruct H4. left. exists (cases t t0 x).
    split; simpl; try f_equal; try (apply casesβE3; try reflexivity); apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H. apply IHE in H1. destruct H1.
  + left. rewrite H1. reflexivity.
  + right. destruct H1. destruct H1. left. exists (casebot x).
    split; simpl; try apply casebotβE; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x.
    split; simpl; try f_equal; apply H1.
    right. destruct H1. exists x. split; simpl; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), zero <> E [ₑ Recₜ t u zero]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), Sₜ t <> E [ₑ Recₜ u v zero]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (recel t3 t0 E). split; try reflexivity.
    apply recelβE1. apply H4.
  + right. left. exists (recel t t4 E). split; try reflexivity.
    apply recelβE2. apply H4.
  + apply IHE in H4. destruct H4.
    left. f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists (recel t t0 x).
    split; simpl; try f_equal; try apply recelβE3; apply H4.
    right. destruct H4.
    left. destruct H4. exists x. split; simpl; try f_equal; apply H4.
    right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), Tt <> E [ₑ Recₜ t u zero]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + assert (forall (E : Elim) (t u : term), Ff <> E [ₑ Recₜ t u zero]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + apply IHE in H4. destruct H4.
   left. rewrite H4. reflexivity.
   right. destruct H4. left. destruct H4. exists (ifel x t t0).
   split; simpl; try f_equal; try apply ifelβE1; apply H4.
   right. destruct H4. left. destruct H4. exists x.
   split; simpl; try f_equal; apply H4.
   right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
  + right. left. exists (ifel E t4 t0). split; try reflexivity.
    apply ifelβE2. apply H4.
  + right. left. exists (ifel E t t5). split; try reflexivity; apply ifelβE3; apply H4.
Qed.

Lemma weak_stand_rec2 : forall (E : Elim) (t u v w : term), E [ₑ(Recₜ t u (Sₜ v))] ⊳ w ->
  w = E [ₑ((u @ₜ v) @ₜ (Recₜ t u v))] \/ (exists (E' : Elim), E ⊳ₑ E' /\ w = E' [ₑ(Recₜ t u (Sₜ v))]) \/
  (exists t' : term, t ⊳ t' /\ w = E [ₑ(Recₜ t' u (Sₜ v))]) \/
  (exists u' : term, u ⊳ u' /\ w = E [ₑ(Recₜ t u' (Sₜ v))]) \/
  (exists v' : term, v ⊳ v' /\ w = E [ₑ(Recₜ t u (Sₜ v'))]).
Proof.
induction E; intros; simpl.
 - simpl in H. inversion H.
  + left. reflexivity.
  + right. right. left. exists t2.
    split; try reflexivity. apply H4.
  + right. right. right. left. exists t3; split; try reflexivity; apply H4.
  + right. right. right. right. inversion H4. exists t5; split; try reflexivity; apply H6.
 - simpl in H. inversion H.
  + rewrite <- H0 in H. rewrite <- H1 in H. exfalso.
    assert (forall (E : Elim) (t u v w : term), (λₜ t) <> E [ₑ Recₜ u v (Sₜ w)]).
    induction E0;intros;simpl;intro; try inversion H3. apply H3 in H1. apply H1.
  + apply IHE in H3. destruct H3. left. rewrite H3. reflexivity.
    right. destruct H3. destruct H3. left. exists (apli x t). simpl. split.
    apply appβE1. apply H3. f_equal. apply H3. right.
    destruct H3. destruct H3. left. exists x. split. apply H3. f_equal. apply H3.
    right. destruct H3. left. destruct H3. exists x. split; try f_equal; apply H3.
    right. destruct H3. exists x. split; try f_equal; apply H3.
  + right. left. exists (apli E t3). split. apply appβE2. apply H3. reflexivity.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ Recₜ t u (Sₜ v)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj1 x). split. apply projβE1. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    right. right. right. destruct H1. left. destruct H1. exists x. split; try f_equal; apply H1.
    right. destruct H1. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ Recₜ t u (Sₜ v)]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj2 x). split. apply projβE2. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    right. right. right. destruct H1. left. destruct H1. exists x. split; try f_equal; apply H1.
    right. destruct H1. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v w : term), κ₁ t <> E [ₑ Recₜ u v (Sₜ w)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v w : term), κ₂ t <> E [ₑ Recₜ u v (Sₜ w)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (cases t3 t0 E). split; simpl; try reflexivity.
    apply casesβE1. apply H4.
  + right. left. exists (cases t t4 E). split; simpl; try reflexivity.
    apply casesβE2. apply H4.
  + apply IHE in H4. destruct H4. left. rewrite H4. reflexivity.
    right. destruct H4. destruct H4. left. exists (cases t t0 x).
    split; simpl; try f_equal; try (apply casesβE3; try reflexivity); apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H. apply IHE in H1. destruct H1.
  + left. rewrite H1. reflexivity.
  + right. destruct H1. destruct H1. left. exists (casebot x).
    split; simpl; try apply casebotβE; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x.
    split; simpl; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x. split; try f_equal; apply H1.
    right. destruct H1. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), zero <> E [ₑ Recₜ t u (Sₜ v)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v w : term), Sₜ t <> E [ₑ Recₜ u v (Sₜ w)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (recel t3 t0 E). split; try reflexivity.
    apply recelβE1. apply H4.
  + right. left. exists (recel t t4 E). split; try reflexivity.
    apply recelβE2. apply H4.
  + apply IHE in H4. destruct H4.
    left. f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists (recel t t0 x).
    split; simpl; try f_equal; try apply recelβE3; apply H4.
    right. destruct H4.
    left. destruct H4. exists x. split; simpl; try f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), Tt <> E [ₑ Recₜ t u (Sₜ v)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + assert (forall (E : Elim) (t u v : term), Ff <> E [ₑ Recₜ t u (Sₜ v)]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + apply IHE in H4. destruct H4.
   left. rewrite H4. reflexivity.
   right. destruct H4. left. destruct H4. exists (ifel x t t0).
   split; simpl; try f_equal; try apply ifelβE1; apply H4.
   right. destruct H4. left. destruct H4. exists x.
   split; simpl; try f_equal; apply H4.
   right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
  + right. left. exists (ifel E t4 t0). split; try reflexivity.
    apply ifelβE2. apply H4.
  + right. left. exists (ifel E t t5). split; try reflexivity; apply ifelβE3; apply H4.
Qed.

Lemma weak_stand_ite1 : forall (E : Elim) (t u v : term), E [ₑ(IfThenElse Tt t u)] ⊳ v ->
  v = E [ₑ t] \/ (exists (E' : Elim), E ⊳ₑ E' /\ v = E' [ₑ(IfThenElse Tt t u)]) \/
  (exists (t' : term), t ⊳ t' /\ v = E [ₑ(IfThenElse Tt t' u)]) \/
  (exists (u' : term), u ⊳ u' /\ v = E [ₑ(IfThenElse Tt t u')]).
Proof.
induction E; intros; simpl.
 - simpl in H. inversion H.
  + left. reflexivity.
  + inversion H4.
  + right. right. left. exists t3. split; try reflexivity; apply H4.
  + right. right. right. exists t4. split; try reflexivity; apply H4.
 - simpl in H. inversion H.
  + rewrite <- H0 in H. rewrite <- H1 in H. exfalso.
    assert (forall (E : Elim) (t u v : term), (λₜ t) <> E [ₑ IfThenElse Tt u v]).
    induction E0;intros;simpl;intro; try inversion H3. apply H3 in H1. apply H1.
  + apply IHE in H3. destruct H3. left. rewrite H3. reflexivity.
    right. destruct H3. destruct H3. left. exists (apli x t). simpl. split.
    apply appβE1. apply H3. f_equal. apply H3. right.
    destruct H3. destruct H3. left. exists x. split. apply H3. f_equal. apply H3.
    destruct H3. right. exists x. split; try f_equal; apply H3.
  + right. left. exists (apli E t3). split. apply appβE2. apply H3. reflexivity.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ IfThenElse Tt u v]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj1 x). split. apply projβE1. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    destruct H1. right. right. right. exists x. split; try (simpl; f_equal); apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ IfThenElse Tt u v]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left; reflexivity.
    right. destruct H1. left. destruct H1. exists (proj2 x). split. apply projβE2; apply H1.
    simpl; f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x. split; try (f_equal); apply H1.
    destruct H1. right. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), κ₁ t <> E [ₑ IfThenElse Tt u v]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), κ₂ t <> E [ₑ IfThenElse Tt u v]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (cases t3 t0 E). split; simpl; try reflexivity.
    apply casesβE1. apply H4.
  + right. left. exists (cases t t4 E). split; simpl; try reflexivity.
    apply casesβE2. apply H4.
  + apply IHE in H4. destruct H4. left. rewrite H4. reflexivity.
    right. destruct H4. destruct H4. left. exists (cases t t0 x).
    split; simpl; try f_equal; try (apply casesβE3; try reflexivity); apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H. apply IHE in H1. destruct H1.
  + left. rewrite H1. reflexivity.
  + right. destruct H1. destruct H1. left. exists (casebot x).
    split; simpl; try apply casebotβE; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x.
    split; simpl; try f_equal; apply H1.
    right. destruct H1. exists x. split; simpl; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), zero <> E [ₑ IfThenElse Tt t u]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), Sₜ t <> E [ₑ IfThenElse Tt u v]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (recel t3 t0 E). split; try reflexivity.
    apply recelβE1. apply H4.
  + right. left. exists (recel t t4 E). split; try reflexivity.
    apply recelβE2. apply H4.
  + apply IHE in H4. destruct H4.
    left. f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists (recel t t0 x).
    split; simpl; try f_equal; try apply recelβE3; apply H4.
    right. destruct H4.
    left. destruct H4. exists x. split; simpl; try f_equal; apply H4.
    right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), Tt <> E [ₑ IfThenElse Tt t u]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + assert (forall (E : Elim) (t u : term), Ff <> E [ₑ IfThenElse Tt t u]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + apply IHE in H4. destruct H4.
   left. rewrite H4. reflexivity.
   right. destruct H4. left. destruct H4. exists (ifel x t t0).
   split; simpl; try f_equal; try apply ifelβE1; apply H4.
   right. destruct H4. left. destruct H4. exists x.
   split; simpl; try f_equal; apply H4.
   right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
  + right. left. exists (ifel E t4 t0). split; try reflexivity.
    apply ifelβE2. apply H4.
  + right. left. exists (ifel E t t5). split; try reflexivity; apply ifelβE3; apply H4.
Qed.

Lemma weak_stand_ite2 : forall (E : Elim) (t u v : term), E [ₑ(IfThenElse Ff t u)] ⊳ v ->
  v = E [ₑ u] \/ (exists E' : Elim, E ⊳ₑ E' /\ v = E' [ₑ(IfThenElse Ff t u)]) \/
  (exists t' : term, t ⊳ t' /\ v = E [ₑ(IfThenElse Ff t' u)]) \/
  (exists u' : term, u ⊳ u' /\ v = E [ₑ(IfThenElse Ff t u')]).
Proof.
induction E; intros; simpl.
 - simpl in H. inversion H.
  + left. reflexivity.
  + inversion H4.
  + right. right. left. exists t3. split; try reflexivity; apply H4.
  + right. right. right. exists t4. split; try reflexivity; apply H4.
 - simpl in H. inversion H.
  + rewrite <- H0 in H. rewrite <- H1 in H. exfalso.
    assert (forall (E : Elim) (t u v : term), (λₜ t) <> E [ₑ IfThenElse Ff u v]).
    induction E0;intros;simpl;intro; try inversion H3. apply H3 in H1. apply H1.
  + apply IHE in H3. destruct H3. left. rewrite H3. reflexivity.
    right. destruct H3. destruct H3. left. exists (apli x t). simpl. split.
    apply appβE1. apply H3. f_equal. apply H3. right.
    destruct H3. destruct H3. left. exists x. split. apply H3. f_equal. apply H3.
    destruct H3. right. exists x. split; try f_equal; apply H3.
  + right. left. exists (apli E t3). split. apply appβE2. apply H3. reflexivity.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ IfThenElse Ff u v]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left. reflexivity.
    destruct H1. destruct H1. right. left. exists (proj1 x). split. apply projβE1. apply H1.
    simpl; f_equal; apply H1.
    destruct H1.
    destruct H1. right. right. left. exists x. split; try (simpl; f_equal); apply H1.
    destruct H1. right. right. right. exists x. split; try (simpl; f_equal); apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (u v t1 t2 : term),  ⟨ t1 , t2 ⟩ <> E [ₑ IfThenElse Ff u v]).
    induction E0; intros; simpl; intro; try inversion H2. apply H2 in H1. inversion H1.
  + apply IHE in H1. destruct H1.
    rewrite H1. left; reflexivity.
    right. destruct H1. left. destruct H1. exists (proj2 x). split. apply projβE2; apply H1.
    simpl; f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x. split; try (f_equal); apply H1.
    destruct H1. right. exists x. split; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u v : term), κ₁ t <> E [ₑ IfThenElse Ff u v]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), κ₂ t <> E [ₑ IfThenElse Ff u v]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (cases t3 t0 E). split; simpl; try reflexivity.
    apply casesβE1. apply H4.
  + right. left. exists (cases t t4 E). split; simpl; try reflexivity.
    apply casesβE2. apply H4.
  + apply IHE in H4. destruct H4. left. rewrite H4. reflexivity.
    right. destruct H4. destruct H4. left. exists (cases t t0 x).
    split; simpl; try f_equal; try (apply casesβE3; try reflexivity); apply H4.
    right. destruct H4. left. destruct H4. exists x. split; try f_equal; apply H4.
    right. destruct H4. exists x. split; try f_equal; apply H4.
 - simpl in H. inversion H. apply IHE in H1. destruct H1.
  + left. rewrite H1. reflexivity.
  + right. destruct H1. destruct H1. left. exists (casebot x).
    split; simpl; try apply casebotβE; try f_equal; apply H1.
    right. destruct H1. left. destruct H1. exists x.
    split; simpl; try f_equal; apply H1.
    right. destruct H1. exists x. split; simpl; try f_equal; apply H1.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), zero <> E [ₑ IfThenElse Ff t u]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + assert (forall (E : Elim) (t u v : term), Sₜ t <> E [ₑ IfThenElse Ff u v]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H3. inversion H3.
  + right. left. exists (recel t3 t0 E). split; try reflexivity.
    apply recelβE1. apply H4.
  + right. left. exists (recel t t4 E). split; try reflexivity.
    apply recelβE2. apply H4.
  + apply IHE in H4. destruct H4.
    left. f_equal; apply H4.
    right. destruct H4. left. destruct H4. exists (recel t t0 x).
    split; simpl; try f_equal; try apply recelβE3; apply H4.
    right. destruct H4.
    left. destruct H4. exists x. split; simpl; try f_equal; apply H4.
    right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
 - simpl in H. inversion H.
  + assert (forall (E : Elim) (t u : term), Tt <> E [ₑ IfThenElse Ff t u]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + assert (forall (E : Elim) (t u : term), Ff <> E [ₑ IfThenElse Ff t u]).
    induction E0; intros; simpl; intro; inversion H4. apply H4 in H1. inversion H1.
  + apply IHE in H4. destruct H4.
   left. rewrite H4. reflexivity.
   right. destruct H4. left. destruct H4. exists (ifel x t t0).
   split; simpl; try f_equal; try apply ifelβE1; apply H4.
   right. destruct H4. left. destruct H4. exists x.
   split; simpl; try f_equal; apply H4.
   right. destruct H4. exists x. split; simpl; try f_equal; apply H4.
  + right. left. exists (ifel E t4 t0). split; try reflexivity.
    apply ifelβE2. apply H4.
  + right. left. exists (ifel E t t5). split; try reflexivity; apply ifelβE3; apply H4.
Qed.

(** B. Weak head expansion.

We prove the different necessary forms of weak head expansion:
  - if E[t[u/x]] is SN and u is SN, then E[(λ t) u] is SN
  - for i ∈ {1,2}, if SN (E[tᵢ]) and SN t₃₋ᵢ, then SN (E[πᵢ ⟨ t₁, t₂ ⟩])
  - for i ∈ {1,2}, if SN (E[tᵢ[u/x₀]]) and SN t₃₋ᵢ, then SN (E[δ (x₀ ↦ t₁ | x₀ ↦ t₂) (κᵢ u)])
  - if SN (E[t]) and SN u then SN (E[if true then t else u]), resp with false
  - if SN (E[u]) then SN (E[Rec u v zero])
  - if SN (E[v t (Rec u v t)]), SN t and SN u then SN (E[Rec u v (S t)]).

Each proof is an induction on the different SN predicate, using standardization to control the
  form of a reduction starting from e.g. E[(λ t) u].
*)

Lemma weak_head_lambda_eq : forall (u : term), SN u -> forall t : term, SN t -> forall (E : Elim)
  (v : term), t = E [ₑ {0 ~> u} v] -> SN (E [ₑ (λₜ v @ₜ u)]).
Proof.
intros u H; induction H; intros t H1; induction H1; intros.
split; intros. apply weak_stand_lambda in H4. destruct H4. assert (SN t0);
try (split; intros; apply H1; apply H5). rewrite H3 in H5. rewrite H4. apply H5.
destruct H4. destruct H4. destruct H4. rewrite H5. specialize (H2 (x [ₑ {0 ~> t1} v])).
assert (t0 ⊳ x [ₑ{0 ~> t1} v]). rewrite H3. apply βE_to_β. apply H4.
specialize (H2 H6 x v). apply H2. reflexivity.
destruct H4. destruct H4. destruct H4. specialize (H2 (E [ₑ {0 ~> t1} x])).
assert (t0 ⊳ E [ₑ{0 ~> t1} x]). rewrite H3. apply ctx_compat. apply subst_red_r. apply H4.
specialize (H2 H6 E x). rewrite H5. apply H2. reflexivity.
destruct H4. destruct H4. specialize (H0 x H4). rewrite H5. assert (SN t0);
try (split; intros; apply H1; apply H6). specialize (H0 (E [ₑ{0 ~> x} v])).
assert (SN (E [ₑ{0 ~> x} v])). rewrite H3 in H6. apply (reduc_SN_star _ _ H6).
apply ctx_compat_star. apply subst_red_l. apply H4. specialize (H0 H7).
specialize (H0 E v). apply H0. reflexivity.
Qed.

Theorem weak_head_lambda : forall (E : Elim) (t u : term), SN (E [ₑ({0 ~> u} t)]) -> SN u
  -> SN (E [ₑ(λₜ t @ₜ u)]).
Proof.
intros. specialize (weak_head_lambda_eq u H0 (E [ₑ{0 ~> u} t]) H E t); intro. apply H1. trivial.
Qed.

Lemma weak_head_pair1_eq : forall (u : term), SN u -> forall t : term, SN t -> forall (E : Elim)
  (v : term), t = E [ₑv] -> SN (E [ₑπ₁ (⟨ v , u ⟩)]).
Proof.
intros u H; induction H; intros t H1; induction H1; intros. split; intros.
apply weak_stand_pair1 in H4. destruct H4. rewrite H4. rewrite <- H3. split; intros; apply H1;
apply H5. destruct H4. destruct H4. destruct H4. apply (βE_to_β _ _ v) in H4. rewrite <- H3 in H4.
specialize (H2 (x [ₑv]) H4 x v). rewrite H5. apply H2. reflexivity. destruct H4. destruct H4.
destruct H4. apply (ctx_compat E) in H4. rewrite <- H3 in H4. specialize (H2 (E [ₑx]) H4 E x).
rewrite H5. apply H2. reflexivity.
destruct H4. destruct H4. assert (SN t0); try (split; intros; apply H1;apply H6). rewrite H3 in H6.
specialize (H0 x H4 (E [ₑv]) H6 E v). rewrite H5. apply H0. reflexivity.
Qed.

Theorem weak_head_pair1 : forall (E : Elim) (t u : term), SN (E [ₑ t]) -> SN u ->
  SN (E [ₑπ₁ (⟨ t , u ⟩)]).
Proof.
intros. specialize (weak_head_pair1_eq u H0 (E [ₑt]) H E t); intro. apply H1. reflexivity.
Qed.

Lemma weak_head_pair2_eq : forall (u : term), SN u -> forall t : term, SN t -> forall (E : Elim)
  (v : term), t = E [ₑv] -> SN (E [ₑπ₂ (⟨ u , v ⟩)]).
Proof.
intros u H; induction H; intros t H1; induction H1; intros. split; intros.
apply weak_stand_pair2 in H4. destruct H4. rewrite H4. rewrite <- H3. split; intros; apply H1;
apply H5. destruct H4. destruct H4. destruct H4. apply (βE_to_β _ _ v) in H4. rewrite <- H3 in H4.
specialize (H2 (x [ₑv]) H4 x v). rewrite H5. apply H2. reflexivity. destruct H4. destruct H4.
destruct H4. assert (SN t0); try (split; intros; apply H1;apply H6). rewrite H3 in H6.
specialize (H0 x H4 (E [ₑv]) H6 E v). rewrite H5. apply H0. reflexivity. destruct H4.
destruct H4. apply (ctx_compat E) in H4. rewrite <- H3 in H4. specialize (H2 (E [ₑx]) H4 E x).
rewrite H5. apply H2. reflexivity.
Qed.

Theorem weak_head_pair2 : forall (E : Elim) (t u : term), SN (fill E u) -> SN t ->
  SN (fill E (π₂ (⟨ t , u ⟩))).
Proof.
intros. specialize (weak_head_pair2_eq t H0 (E [ₑu]) H E u); intro. apply H1. trivial.
Qed.

Lemma weak_head_inj1_eq : forall (u : term), SN u -> forall (v : term), SN v -> forall (t : term),
  SN t -> forall (E : Elim) (w : term), t = E [ₑ{0 ~> v} w] -> SN (E [ₑδ(0 ↦ w |0 ↦ u) (κ₁ v)]).
Proof.
intros u H; induction H; intros v H1; induction H1; intros t H3; induction H3; intros.
split; intros. apply weak_stand_inj1 in H6. destruct H6. rewrite H6. rewrite <- H5.
split; intros; apply H3; apply H7. destruct H6. destruct H6. destruct H6.
specialize (H4 (x [ₑ{0 ~> t0} w])). assert (t2 ⊳ x[ₑ{0 ~> t0} w]).
rewrite H5. apply βE_to_β. apply H6. specialize (H4 H8 x w). rewrite H7. apply H4.
reflexivity. destruct H6. destruct H6. destruct H6. rewrite H7.
assert (t2 ⊳ E [ₑ{0 ~> t0} x]). rewrite H5. apply ctx_compat. apply subst_red_r. apply H6.
specialize (H4 _ H8 E x). apply H4. reflexivity. destruct H6. destruct H6. destruct H6.
specialize (H0 x H6). assert (SN t0). split; intros; apply H1; apply H8. specialize (H0 t0 H8).
assert (SN t2). split; intros; apply H3; apply H9. specialize (H0 t2 H9).
specialize (H0 E w). rewrite H7. apply H0. apply H5.
destruct H6. destruct H6. assert (SN t2). split; intros; apply H3; apply H8.
assert (SN (E [ₑ{0 ~> x} w])). apply (reduc_SN_star _ _ H8). rewrite H5.
apply ctx_compat_star. apply subst_red_l. apply H6.
specialize (H2 x H6 _ H9 E w). rewrite H7. apply H2. reflexivity.
Qed.

Theorem weak_head_inj1 : forall (E : Elim) (t u v : term), SN (E [ₑ{0 ~> v} t]) -> SN u -> SN v
  -> SN (E [ₑδ(0 ↦ t |0 ↦ u) (κ₁ v)]).
Proof.
intros. specialize (weak_head_inj1_eq u H0 v H1 _ H E t); intro. apply H2. reflexivity.
Qed.

Lemma weak_head_inj2_eq : forall (u : term), SN u -> forall (v : term), SN v -> forall (t : term),
  SN t -> forall (E : Elim) (w : term), t = E [ₑ{0 ~> v} w] -> SN (E [ₑδ(0 ↦ u |0 ↦ w) (κ₂ v)]).
Proof.
intros u H; induction H; intros v H1; induction H1; intros t H3; induction H3; intros.
split; intros. apply weak_stand_inj2 in H6. destruct H6. rewrite H6. rewrite <- H5.
split; intros; apply H3; apply H7. destruct H6. destruct H6. destruct H6.
specialize (H4 (x [ₑ{0 ~> t0} w])). assert (t2 ⊳ x[ₑ{0 ~> t0} w]).
rewrite H5. apply βE_to_β. apply H6. specialize (H4 H8 x w). rewrite H7. apply H4.
reflexivity. destruct H6. destruct H6. destruct H6.
specialize (H0 x H6). assert (SN t0). split; intros; apply H1; apply H8. specialize (H0 t0 H8).
assert (SN t2). split; intros; apply H3; apply H9. specialize (H0 t2 H9).
specialize (H0 E w). rewrite H7. apply H0. apply H5.
destruct H6. destruct H6. destruct H6. rewrite H7.
assert (t2 ⊳ E [ₑ{0 ~> t0} x]). rewrite H5. apply ctx_compat. apply subst_red_r. apply H6.
specialize (H4 _ H8 E x). apply H4. reflexivity.
destruct H6. destruct H6. assert (SN t2). split; intros; apply H3; apply H8.
assert (SN (E [ₑ{0 ~> x} w])). apply (reduc_SN_star _ _ H8). rewrite H5.
apply ctx_compat_star. apply subst_red_l. apply H6.
specialize (H2 x H6 _ H9 E w). rewrite H7. apply H2. reflexivity.
Qed.

Theorem weak_head_inj2 : forall (E : Elim) (t u v : term), SN (fill E ({0 ~> v} u)) -> SN t -> SN v
  -> SN (fill E (δ(0 ↦ t |0 ↦ u) (κ₂ v))).
Proof.
intros. specialize (weak_head_inj2_eq t H0 v H1 _ H E u); intro. apply H2. reflexivity.
Qed.

Lemma weak_head_rec1_eq : forall (u : term), SN u -> forall (t : term), SN t -> forall (E : Elim)
  (v : term), t = E [ₑv] -> SN (E [ₑRecₜ v u zero]).
Proof.
intros u H; induction H; intros t H1; induction H1; intros. split; intros.
apply weak_stand_rec1 in H4. destruct H4. rewrite H4. rewrite <- H3. split; intros; apply H1;
apply H5. destruct H4. destruct H4. destruct H4. apply (βE_to_β _ _ v) in H4. rewrite <- H3 in H4.
specialize (H2 (x [ₑv]) H4 x v). rewrite H5. apply H2. reflexivity. destruct H4. destruct H4.
destruct H4. apply (ctx_compat E) in H4. rewrite <- H3 in H4. specialize (H2 (E [ₑx]) H4 E x).
rewrite H5. apply H2. reflexivity.
destruct H4. destruct H4. assert (SN t0); try (split; intros; apply H1;apply H6). rewrite H3 in H6.
specialize (H0 x H4 (E [ₑv]) H6 E v). rewrite H5. apply H0. reflexivity.
Qed.

Theorem weak_head_rec1 : forall (E : Elim) (t u : term), SN (E [ₑt]) -> SN u ->
  SN (E [ₑRecₜ t u zero]).
Proof.
intros. specialize (weak_head_rec1_eq _ H0 _ H E t); intro. apply H1. trivial.
Qed.

Lemma weak_head_rec2_eq : forall (u : term), SN u -> forall (v : term), SN v -> forall (t : term),
  SN t -> forall (E : Elim) (w : term), t = E [ₑ(w @ₜ v) @ₜ (Recₜ u w v)] ->
  SN (E [ₑRecₜ u w (Sₜ v)]).
Proof.
intros u H; induction H; intros v H1; induction H1; intros t H3. apply SN_equiv_SN_plus in H3.
induction H3. intros.
(*assert (SN_plus t2) as H10. apply SN_equiv_SN_plus. split; apply H3. induction H10 as [t2 H10 H11].
intros.*)
split; intros. apply weak_stand_rec2 in H6. destruct H6. rewrite H6. rewrite <- H5.
apply SN_equiv_SN_plus; apply expansion_plus; apply H3.
destruct H6. destruct H6. destruct H6.
assert (t2 ⊳+ x [ₑ(w @ₜ t0) @ₜ Recₜ t1 w t0]). apply closure_R_in_t.
rewrite H5. apply βE_to_β. apply H6.
specialize (H4 _ H8 x w). rewrite H7. apply H4. reflexivity. destruct H6. destruct H6. destruct H6.
specialize (H0 x H6). assert (SN t0). split; intros; apply H1; apply H8. specialize (H0 t0 H8).
assert (SN (E [ₑ(w @ₜ t0) @ₜ Recₜ x w t0])). assert (SN t2).
apply SN_equiv_SN_plus; split; apply H3.
apply (reduc_SN _ _ H9). rewrite H5. apply ctx_compat.
apply β_app2. apply β_rec1. apply H6. specialize (H0 _ H9).
specialize (H0 E w). rewrite H7. apply H0. reflexivity.
destruct H6. destruct H6. destruct H6. rewrite H7.
2 :{ destruct H6. destruct H6. specialize (H2 _ H6). rewrite H7.
assert (SN (E [ₑ(w @ₜ x) @ₜ Recₜ t1 w x])).
assert (SN t2); try (apply SN_equiv_SN_plus; split; apply H3).
 try (split; intros; apply H3;apply H8).
rewrite H5 in H8. apply (reduc_SN _ (E [ₑ (w @ₜ t0) @ₜ Recₜ t1 w x])) in H8.
apply (reduc_SN _ _ H8). apply ctx_compat. apply β_app1. apply β_app2. apply H6. apply ctx_compat.
apply β_app2. apply β_rec3. apply H6. specialize (H2 _ H8 E w). apply H2. reflexivity. }
assert (t2 ⊳+ E [ₑ(x @ₜ t0) @ₜ Recₜ t1 x t0]).
apply (t_add _ _ (E [ₑ(x @ₜ t0) @ₜ Recₜ t1 w t0])). rewrite H5. apply closure_R_in_t.
apply ctx_compat. apply β_app1. apply β_app1. apply H6. apply ctx_compat. apply β_app2.
apply β_rec2. apply H6.
assert (SN (E [ₑ(x @ₜ t0) @ₜ Recₜ t1 x t0])). assert (SN t2); try (apply expansion; apply H3).
rewrite H5 in H8. apply SN_equiv_SN_plus; split; apply H3. rewrite H5 in H9.
apply (reduc_SN_star _ _ H9). rewrite <- H5. apply closure_t_in_rt. apply H8.
specialize (H4 _ H8 E x). apply H4. reflexivity.
Qed.

Theorem weak_head_rec2 : forall (E : Elim) (t u v : term), SN (E [ₑu @ₜ v @ₜ Recₜ t u v]) ->
  SN t -> SN v -> SN (E [ₑRecₜ t u (Sₜ v)]).
Proof.
intros. specialize (weak_head_rec2_eq _ H0 _ H1 _ H E u); intro. apply H2. trivial.
Qed.

Lemma weak_head_ite1_eq : forall (u : term), SN u -> forall (t : term), SN t -> forall (E : Elim)
  (v : term), t = E [ₑv] -> SN (E [ₑIfThenElse Tt v u]).
Proof.
intros u H; induction H; intros t H1; induction H1; intros. split; intros.
apply weak_stand_ite1 in H4. destruct H4. rewrite H4. rewrite <- H3. split; intros; apply H1;
apply H5. destruct H4. destruct H4. destruct H4. apply (βE_to_β _ _ v) in H4. rewrite <- H3 in H4.
specialize (H2 (x [ₑv]) H4 x v). rewrite H5. apply H2. reflexivity. destruct H4. destruct H4.
destruct H4. apply (ctx_compat E) in H4. rewrite <- H3 in H4. specialize (H2 (E [ₑx]) H4 E x).
rewrite H5. apply H2. reflexivity.
destruct H4. destruct H4. assert (SN t0); try (split; intros; apply H1;apply H6). rewrite H3 in H6.
specialize (H0 x H4 (E [ₑv]) H6 E v). rewrite H5. apply H0. reflexivity.
Qed.

Theorem weak_head_ite1 : forall (E : Elim) (t u : term), SN (E [ₑt]) -> SN u ->
  SN (E [ₑIfThenElse Tt t u]).
Proof.
intros. specialize (weak_head_ite1_eq _ H0 _ H E t); intro. apply H1. trivial.
Qed.

Lemma weak_head_ite2_eq : forall (v : term), SN v -> forall (t : term), SN t -> forall (E : Elim)
  (u : term), t = E [ₑu] -> SN (E [ₑIfThenElse Ff v u]).
Proof.
intros u H; induction H; intros t H1; induction H1; intros. split; intros.
apply weak_stand_ite2 in H4. destruct H4. rewrite H4. rewrite <- H3. split; intros; apply H1;
apply H5. destruct H4. destruct H4. destruct H4. apply (βE_to_β _ _ u) in H4. rewrite <- H3 in H4.
specialize (H2 (x [ₑu]) H4 x u). rewrite H5. apply H2. reflexivity. destruct H4. destruct H4.
destruct H4.
assert (SN t0); try (split; intros; apply H1;apply H6). rewrite H3 in H6.
specialize (H0 x H4 (E [ₑu]) H6 E u). rewrite H5. apply H0. reflexivity. destruct H4. destruct H4.
apply (ctx_compat E) in H4. rewrite <- H3 in H4. specialize (H2 (E [ₑx]) H4 E x).
rewrite H5. apply H2. reflexivity.
Qed.

Theorem weak_head_ite2 : forall (E : Elim) (t u : term), SN (E [ₑu]) -> SN t -> 
  SN (E [ₑIfThenElse Ff t u]).
Proof.
intros. specialize (weak_head_ite2_eq _ H0 _ H E u); intro. apply H1; reflexivity.
Qed.

(**
This last result will also be useful, and uses the weak standardization.*)

Lemma SN_lift_fill : forall (E : Elim) (t : term) (k n : nat),
  SN (E [ₑ t]) -> SN (E [ₑ lift k n t]).
Proof.
apply (induction_ext (fun E => forall (t : term) (k n : nat), SN (E [ₑ t])
  -> SN (E [ₑlift k n t]))); intros; simpl; simpl in H; try (rewrite compose_fill; simpl);
  try (rewrite compose_fill in H0; simpl in H0). 7 :{
  - apply SN_lift. apply H.
  - rewrite compose_fill in H0. simpl in H0. rewrite compose_fill. simpl.
    
Admitted.