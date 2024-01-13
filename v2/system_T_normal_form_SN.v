Require Import system_T_first_def.
Require Import system_T_substi.
Require Import system_T_reduction.
Require Import PeanoNat.
Require Import List.
Require Import Lt.
Require Import Bool.

(* ********************************************************************************************* *)

(** II. The structure of SN *)

(** 5. Normal forms and SN.

This file contains the definitions of normal forms, strongly normalizing terms and results about
  it.*)

(** A. Normal form.

We take the usual definition of normal form: it is a term such that there is no reduction starting
  from it.*)

Definition normal_form t : Prop := ~ (exists t', t ⊳ t').

Lemma normal_form_red_eq : forall t1 t2 : term, normal_form t1 -> t1 ⊳* t2 -> t1 = t2.
Proof.
intros. induction H0. reflexivity. rewrite IHrt_closure. rewrite IHrt_closure in H. destruct H.
exists v. apply H1. apply H. apply H.
Qed.

Lemma var_normal_form : forall (n : nat), normal_form {{n}}.
Proof.
intros n H. inversion H. inversion H0.
Qed.

Lemma lambda_normal_form : forall (t : term), normal_form t <-> normal_form (λₜ t).
Proof.
intros. split; intros. intro. destruct H0. inversion H0. apply H. exists t2. apply H2.
intro. destruct H0. apply H. exists (λₜ x). apply β_abs. apply H0.
Qed.

Lemma app_normal_form : forall (t u : term), normal_form (t @ₜ u) ->
  normal_form t /\ normal_form u.
Proof.
intros. split. intro. apply H. destruct H0. exists (x @ₜ u). apply β_app1. apply H0.
intro. apply H. destruct H0. exists (t @ₜ x). apply β_app2. apply H0.
Qed.

Lemma pair_normal_form : forall (t u : term),
  normal_form (⟨ t , u ⟩) <-> normal_form t /\ normal_form u.
Proof.
intros. split;intros. split;intro. inversion H0. apply H. exists (⟨ x , u⟩).
apply (@β_pair1 t x u). apply H1. inversion H0. apply H. exists (⟨ t , x ⟩).
apply (@β_pair2 t u x). apply H1. intro. destruct H0. destruct H. inversion H0. apply H. exists t2.
apply H5. apply H1. exists t3. apply H5.
Qed.

Lemma proj_normal_form1 : forall (t : term), normal_form (π₁ t) -> normal_form t.
Proof.
intros. intro. destruct H0. apply H. exists (π₁ x). apply β_proj1. apply H0.
Qed.

Lemma proj_normal_form2 : forall (t : term), normal_form (π₂ t) -> normal_form t.
Proof.
intros. intro. destruct H0. apply H. exists (π₂ x). apply β_proj2. apply H0.
Qed.

Lemma star_normal_form : normal_form star.
Proof.
intro; inversion H; inversion H0.
Qed.

Lemma sum_normal_form_1 : forall (t : term), normal_form t <-> normal_form (κ₁ t).
Proof.
intros. split;intros. intro. destruct H0. inversion H0. apply H. exists t2. apply H2.
intro. destruct H0. apply H. exists (κ₁ x). apply (β_inj1 t x H0).
Qed.

Lemma sum_normal_form_2 : forall (t : term), normal_form t <-> normal_form (κ₂ t).
Proof.
intros. split;intros. intro. destruct H0. inversion H0. apply H. exists t2. apply H2.
intro. destruct H0. apply H. exists (κ₂ x). apply (β_inj2 t x H0).
Qed.

Lemma delta_normal_form : forall (t u v : term), normal_form (δ(0 ↦ t |0 ↦ u) v) ->
  normal_form t /\ normal_form u /\ normal_form v.
Proof.
intros. repeat split; intro; destruct H0; apply H. exists (delta x u v). apply β_delta1. apply H0.
exists (delta t x v). apply β_delta2. apply H0. exists (delta t u x). apply β_delta3. apply H0.
Qed.

Lemma bool_normal_form : normal_form Tt /\ normal_form Ff.
Proof.
split; intro; inversion H; inversion H0.
Qed.

Lemma ite_normal_form : forall (t u v : term), normal_form (IfThenElse t u v) ->
  normal_form t /\ normal_form u /\ normal_form v.
Proof.
intros. repeat split; intro; destruct H0; apply H. exists (IfThenElse x u v). apply β_ite1.
apply H0. exists (IfThenElse t x v). apply β_ite2. apply H0.
exists (IfThenElse t u x). apply β_ite3. apply H0.
Qed.

Lemma nat_normal_form : forall (n : nat), normal_form (code_nat n).
Proof.
induction n. intro. destruct H. inversion H. intro. inversion H.
inversion H0. apply IHn. exists t2. apply H2.
Qed.

Lemma succ_normal_form : forall (t : term), normal_form (Sₜ t) <-> normal_form t.
Proof.
intros; split; intro; unfold normal_form; intro.
destruct H0. apply β_succ in H0. destruct H. exists (Sₜ x). apply H0.
destruct H0. destruct H. inversion H0. exists t2. apply H1.
Qed.

Lemma rec_normal_form : forall (t u v : term), normal_form (Recₜ t u v) -> normal_form t /\
  normal_form u /\ normal_form v.
Proof.
intros. repeat split; intro; destruct H0; apply H. exists (Recₜ x u v). apply β_rec1. apply H0.
exists (Recₜ t x v). apply β_rec2. apply H0.
exists (Recₜ t u x). apply β_rec3. apply H0.
Qed.

Lemma case_nil_normal_form : forall (t : term), normal_form t <-> normal_form (δb t).
Proof.
intros. split; intro. intro. destruct H0. inversion H0. apply H. exists t2. apply H2.
intro. apply H. destruct H0. exists (δb x). apply β_deltaNil. apply H0.
Qed.

Lemma unicity_normal_form : forall (t u v : term), t ⊳* u -> t ⊳* v -> normal_form u ->
  normal_form v -> u = v.
Proof.
intros. assert (Confluence βred). apply Church_Rosser. unfold Confluence in H3.
assert (t ⊳* u /\ t ⊳* v). split; try apply H; apply H0. apply H3 in H4.
destruct H4. destruct H4. specialize (normal_form_red_eq _ _ H1 H4); intro.
specialize (normal_form_red_eq _ _ H2 H5); intro. rewrite H6. rewrite H7.
reflexivity.
Qed.

Fixpoint normal_bool (t : term) : bool :=
  match t with
    | {{n}} => true
    | Tt => true
    | Ff => true
    | star => true
    | zero => true
    | λₜ u => normal_bool u
    | ⟨ u,v ⟩ => normal_bool u && normal_bool v
    | κ₁ u => normal_bool u
    | κ₂ u => normal_bool u
    | δb u => normal_bool u
    | Sₜ u => normal_bool u
    | (λₜ u) @ₜ v => false
    | u @ₜ v => normal_bool u && normal_bool v
    | π₁ (⟨ u,v ⟩) => false
    | π₁ u => normal_bool u
    | π₂ (⟨ u,v ⟩) => false
    | π₂ u => normal_bool u
    | delta u v (κ₁ w) => false
    | delta u v (κ₂ w) => false
    | delta u v w => normal_bool u && normal_bool v && normal_bool w
    | Recₜ u v zero => false
    | Recₜ u v (Sₜ w) => false
    | Recₜ u v w => normal_bool u && normal_bool v && normal_bool w
    | IfThenElse Tt u v => false
    | IfThenElse Ff u v => false
    | IfThenElse u v w => normal_bool u && normal_bool v && normal_bool w
  end.

Lemma normal_bool_normal : forall (t : term), normal_bool t = true <-> normal_form t.
Proof.
intros; split; intro. induction t.
 - apply var_normal_form.
 - apply -> lambda_normal_form. apply IHt. inversion H. reflexivity.
 - inversion H. case t1 eqn: H2.
 2 :{ inversion H1. }
Admitted.

Lemma normal_bool_red : forall (t : term), normal_bool t = false <-> exists v : term, t ⊳ v.
Proof.
intro t; induction t; intros; split; intro; try inversion H.
  - inversion H0.
  - apply IHt in H1. destruct H1. exists (λₜ x). apply β_abs. apply H0.
  - simpl. apply IHt. destruct H. inversion H0. exists t2. apply H2.
  - case t1 eqn : H2; try (simpl in H1;apply IHt2 in H1; destruct H1 ; exists (t1 @ₜ x);
    rewrite H2; apply β_app2; apply H0); try (apply andb_false_iff in H1; destruct H1;
    try (apply IHt1 in H0; destruct H0; rewrite <- H2 in H0; rewrite <- H2;
    exists (x @ₜ t2); apply β_app1; apply H0); try (apply IHt2 in H0; destruct H0; rewrite <- H2;
    exists (t1 @ₜ x); apply β_app2; apply H0)). exists ({0 ~> t2} t). apply β_to.
  - inversion H0. simpl. reflexivity. assert (exists v : term, t1 ⊳ v). exists t3; apply H4.
    apply IHt1 in H5. simpl. case t1 eqn : H6; try reflexivity; try (rewrite H5; reflexivity).
    assert (exists v : term, t2 ⊳ v). exists t4. apply H4. apply IHt2 in H5. simpl.
    case t1 eqn : H6; try rewrite H5; try rewrite andb_false_r; reflexivity.
  - inversion H0.
  - apply IHt in H1. destruct H1. exists (Sₜ x). apply β_succ. apply H0.
  - simpl. apply IHt. inversion H0. exists t2. apply H2.
Admitted.

(** B. Weakly normalizing terms.

We define the notion of weakly normalizing terms as terms for which there exists a reduction
  sequence to a normal form.*)

Definition WN (t : term) : Prop := exists (u : term), t ⊳* u /\ normal_form u.

Lemma normal_form_WN : forall (t : term), normal_form t -> WN t.
Proof.
intros. exists t. split; try apply H. apply β_refl.
Qed.

Lemma reduc_WN : forall (t u : term), WN t -> t ⊳* u -> WN u.
Proof.
intros. destruct H. destruct H.
specialize Church_Rosser; intro. unfold Confluence in H2. specialize (H2 t u x).
assert (t ⊳* u /\ t ⊳* x); try (split; try apply H; apply H0). apply H2 in H3. destruct H3.
destruct H3. apply (normal_form_red_eq _ _ H1) in H4. rewrite <- H4 in H3.
exists x. split; try apply H1. apply H3.
Qed.

(** C. Strongly normalizing terms

We give the definition of strongly normalizing term as an inductive set defined by

                                     ∀ t ⊳ u, u ∈ SN
                                     ---------------
                                          t ∈ SN

We can thus think of SN as the biggest part of Λ on which ⊳ is well founded.*)

Inductive SN : term -> Prop :=
  | expansion : forall t1, (forall t2, t1 ⊳ t2 -> SN t2) -> SN t1.

(** An equivalent predicate is the same induction but with ⊳+.*)

Inductive SN_plus : term -> Prop :=
  | expansion_plus : forall t1, (forall t2, t1 ⊳+ t2 -> SN_plus t2) -> SN_plus t1.

(**
We give a few results about normal forms.*)

Lemma normal_form_SN : forall t, normal_form t -> SN t.
Proof.
intro t. intro H. apply expansion. intros t2 H0. exfalso. apply H.
exists t2. apply H0.
Qed.

Lemma SN_WN : forall (t : term), SN t -> WN t.
Proof.
intros. induction H. case (normal_bool t1) eqn : H1.
apply normal_bool_normal in H1. exists t1. split; try apply H1. apply β_refl.
apply normal_bool_red in H1. destruct H1. specialize (H0 x H1).
destruct H0. destruct H0. exists x0. split; try apply H2.
apply (β_trans _ _ _ (β_sub_star _ _ H1) H0).
Qed.

(**
This is another usual definition of strongly normalising term, that there are no infinite reduction
  sequences, but this definition is not intuitionnisticly equivalent, hence our choice to use the
  other, stronger definition.*)

Lemma SN_no_inf_seq : forall t, SN t -> ~(exists f : nat -> term,
  f 0 = t /\ forall n : nat, f n ⊳ f (S n)).
Proof.
intros. induction H. intro. destruct H1. destruct H1. apply (H0 (x 1)). rewrite <- H1. apply H2.
exists (fun n => x (S n)). split. reflexivity. intro. apply H2.
Qed.

(**
SN is stable by reduction.*)
Lemma reduc_SN : forall t u : term, SN t -> t ⊳ u -> SN u.
Proof.
intros. destruct H. apply H. apply H0.
Qed.

Lemma reduc_SN_star : forall t u : term, SN t -> t ⊳* u -> SN u.
Proof.
intros. induction H0. apply H. apply (reduc_SN u v). apply IHrt_closure. apply H. apply H1.
Qed.

Lemma SN_equiv_SN_plus : forall (t1 : term), SN t1 <-> SN_plus t1.
Proof.
intro; split; intro. induction H. split; intros. induction H1. apply (H0 _ H1).
specialize (IHt_closure H H0). inversion IHt_closure. split; intros.
apply H3. apply (closure_t_trans _ _ v). apply closure_R_in_t. apply H2. apply H5.
induction H. split; intros. apply H0. apply closure_R_in_t. apply H1.
Qed.

(**
We now give stability results : by compatibility of ⊳, knowing that C[t] is SN gives that t is
SN, as for any context, C[t] ⊳ C[u] -> t ⊳ u.

We prove in each case a lemma which allows us to make an induction on SN t, but each
SN_foo_eq lemma is just a preliminary lemma to prove SN_foo.*)

(**
Stability for constructors.*)

Lemma SN_lambda_eq : forall t : term, SN t -> (forall u : term, (t = λₜ u) -> SN u).
Proof.
intros t H. induction H. intros. split; intros. apply β_abs in H2.
inversion H2. rewrite <- H1 in H2. specialize (H0 (λₜ t2) H2 t2). apply H0; reflexivity.
Qed.

Lemma SN_inj1_eq : forall t : term, SN t -> (forall u : term, (t = κ₁ u) -> SN u).
Proof.
intros t H. induction H. intros. split; intros. apply β_inj1 in H2.
inversion H2. rewrite <- H1 in H2. specialize (H0 (κ₁ t2) H2 t2). apply H0; reflexivity.
Qed.

Lemma SN_inj2_eq : forall t : term, SN t -> (forall u : term, (t = κ₂ u) -> SN u).
Proof.
intros t H. induction H. intros. split; intros. apply β_inj2 in H2.
inversion H2. rewrite <- H1 in H2. specialize (H0 (κ₂ t2) H2 t2). apply H0; reflexivity.
Qed.

Lemma SN_pair1_eq : forall t : term, SN t -> (forall v u : term, (t = ⟨ v , u ⟩) -> SN v).
Proof.
intros t H. induction H. intros. split; intros. apply (β_pair1 _ _ u) in H2.
inversion H2. rewrite <- H1 in H2. specialize (H0 (⟨t2 , u ⟩) H2 t2 u). apply H0. reflexivity.
rewrite <- H1 in H2. specialize (H0 (⟨ t2 , u ⟩) H2 t2 u). apply H0. reflexivity.
Qed.

Lemma SN_pair2_eq : forall t : term, SN t -> (forall u v : term, (t = ⟨ u , v ⟩) -> SN v).
Proof.
intros t H. induction H. intros. split; intros. apply (β_pair2 u _ _) in H2.
inversion H2. rewrite <- H1 in H2. specialize (H0 (⟨u , t2 ⟩) H2 u t2). apply H0. reflexivity.
rewrite <- H1 in H2. specialize (H0 (⟨ u , t2 ⟩) H2 u t2). apply H0. reflexivity.
Qed.

Lemma SN_succ_eq : forall t : term, SN t -> (forall u : term, (t = Sₜ u) -> SN u).
Proof.
intros t H. induction H. intros. split; intros. apply β_succ in H2. inversion H2.
rewrite <- H1 in H2. specialize (H0 (Sₜ t2) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_lambda : forall t : term, SN t <-> SN (λₜ t).
Proof.
intros.
split; intro.
induction H. split; intros. inversion H1.
apply H0. apply H3.
apply (SN_lambda_eq (λₜ t)). apply H. reflexivity.
Qed.

Lemma SN_inj1 : forall t : term, SN t <-> SN (κ₁ t).
Proof.
split; intros.
induction H. split; intros. inversion H1.
apply H0. apply H3.
apply (SN_inj1_eq (κ₁ t)). apply H. reflexivity.
Qed.

Lemma SN_inj2 : forall t : term, SN t <-> SN (κ₂ t).
Proof.
split; intros.
induction H. split; intros. inversion H1.
apply H0. apply H3.
apply (SN_inj2_eq (κ₂ t)). apply H. reflexivity.
Qed.

Lemma SN_pair : forall t u : term, SN t /\ SN u <-> SN (⟨ t , u ⟩).
Proof.
intros t u. split; intros. destruct H. generalize u H0; clear u H0. induction H.
intros. induction H1. split; intros.
inversion H3. apply H0. apply H7. split; intros. apply H1 in H8. apply H8.
apply H2. apply H7.
split. apply (SN_pair1_eq (⟨ t , u ⟩) H t u). reflexivity.
apply (SN_pair2_eq (⟨ t , u ⟩) H t u). reflexivity.
Qed.

Lemma SN_succ : forall t : term, SN t <-> SN (Sₜ t).
Proof.
split; intros.
 - induction H. split; intros. inversion H1. apply H0. apply H3.
 - apply (SN_succ_eq (Sₜ t)). apply H. reflexivity.
Qed.

(**
Stability for destructors.*)

Lemma SN_app1_eq : forall t u : term, SN t -> forall v : term, t = v @ₜ u -> SN v.
Proof.
intros t u H. induction H. intros. split; intros.
apply (β_app1 _ _ u) in H2. rewrite <- H1 in H2.
specialize (H0 (t2 @ₜ u) H2 t2). apply H0; reflexivity.
Qed.

Lemma SN_app1 : forall t u : term, SN (t @ₜ u) -> SN t.
Proof.
intros. apply (SN_app1_eq (t @ₜ u) u H t). reflexivity.
Qed.

Lemma SN_app2_eq : forall t u : term, SN t -> forall v : term, t = u @ₜ v -> SN v.
Proof.
intros t u H. induction H. intros. split; intros.
apply (β_app2 u _ _) in H2. rewrite <- H1 in H2.
specialize (H0 (u @ₜ t2) H2 t2). apply H0; reflexivity.
Qed.

Lemma SN_app2 : forall t u : term, SN (t @ₜ u) -> SN u.
Proof.
intros. apply (SN_app2_eq (t @ₜ u) t H u). reflexivity.
Qed.

Lemma SN_delta1_eq : forall (t u v : term), SN t -> forall w : term, t = δ(0 ↦ w |0 ↦ u) v -> SN w.
Proof.
intros t u v H; induction H; intros. split; intros. apply (β_delta1 _ _ u v) in H2.
rewrite <- H1 in H2. specialize (H0 (delta t2 u v) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_proj1_eq : forall (t : term), SN t -> forall u : term, t = π₁ u -> SN u.
Proof.
intros t H; induction H; intros; split; intros.
apply β_proj1 in H2. rewrite <- H1 in H2.
specialize (H0 (π₁ t2) H2 t2). apply H0; reflexivity.
Qed.

Lemma SN_proj1 : forall (t : term), SN (π₁ t) -> SN t.
Proof.
intros. apply (SN_proj1_eq (π₁ t) H t). reflexivity.
Qed.

Lemma SN_proj2_eq : forall (t : term), SN t -> forall u : term, t = π₂ u -> SN u.
Proof.
intros t H; induction H; intros; split; intros.
apply β_proj2 in H2. rewrite <- H1 in H2.
specialize (H0 (π₂ t2) H2 t2). apply H0; reflexivity.
Qed.

Lemma SN_proj2 : forall (t : term), SN (π₂ t) -> SN t.
Proof.
intros. apply (SN_proj2_eq (π₂ t) H t). reflexivity.
Qed.

Lemma SN_delta1 : forall t u v : term, SN (δ(0 ↦ u |0 ↦ v) t) -> SN u.
Proof.
intros. specialize (SN_delta1_eq (delta u v t) v t H). intros. apply H0.
reflexivity.
Qed.

Lemma SN_delta2_eq : forall (t u v : term), SN t -> forall w : term, t = δ(0 ↦ u |0 ↦ w) v -> SN w.
Proof.
intros t u v H; induction H; intros. split; intros. apply (β_delta2 u _ _ v) in H2.
rewrite <- H1 in H2. specialize (H0 (delta u t2 v) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_delta2 : forall t u v : term, SN (δ(0 ↦ u |0 ↦ v) t) -> SN v.
Proof.
intros. specialize (SN_delta2_eq (delta u v t) u t H). intros. apply H0.
reflexivity.
Qed.

Lemma SN_delta3_eq : forall (t u v : term), SN t -> forall w : term, t = δ(0 ↦ u |0 ↦ v) w -> SN w.
Proof.
intros t u v H; induction H; intros. split; intros. apply (β_delta3 u v) in H2.
rewrite <- H1 in H2. specialize (H0 (delta u v t2) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_delta3 : forall t u v : term, SN (δ(0 ↦ u |0 ↦ v) t) -> SN t.
Proof.
intros. specialize (SN_delta3_eq (delta u v t) u v H). intros. apply H0.
reflexivity.
Qed.

Lemma SN_deltaNil_eq : forall t : term, SN t -> forall v : term, t = δb v -> SN v.
Proof.
intros t H. induction H. intros. split; intros.
apply β_deltaNil in H2. rewrite <- H1 in H2. specialize (H0 (δb t2) H2 t2).
apply H0. reflexivity.
Qed.

Lemma SN_deltaNil : forall t : term, SN (δb t) <-> SN t.
Proof.
intros. split; intro. apply (SN_deltaNil_eq (δb t) H t). reflexivity.
induction H. split; intros. inversion H1. apply H0 in H3. apply H3.
Qed.

Lemma SN_rec1_eq : forall t u v : term, SN t -> forall w : term, t = Recₜ w u v -> SN w.
Proof.
intros t u v H; induction H; intros. split; intros. apply (β_rec1 _ _ u v) in H2.
rewrite <- H1 in H2. specialize (H0 (Recₜ t2 u v) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_rec1 : forall t u v : term, SN (Recₜ u v t) -> SN u.
Proof.
intros. specialize (SN_rec1_eq (Recₜ u v t) v t H). intros. apply H0.
reflexivity.
Qed.

Lemma SN_rec2_eq : forall t u v : term, SN t -> forall w : term, t = Recₜ u w v -> SN w.
Proof.
intros t u v H; induction H; intros. split; intros. apply (β_rec2 u _ _ v) in H2.
rewrite <- H1 in H2. specialize (H0 (Recₜ u t2 v) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_rec2 : forall t u v : term, SN (Recₜ u v t) -> SN v.
Proof.
intros. specialize (SN_rec2_eq (Recₜ u v t) u t H). intros. apply H0.
reflexivity.
Qed.

Lemma SN_rec3_eq : forall t u v : term, SN t -> forall w : term, t = Recₜ u v w -> SN w.
Proof.
intros t u v H; induction H; intros. split; intros. apply (β_rec3 u v) in H2.
rewrite <- H1 in H2. specialize (H0 (Recₜ u v t2) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_rec3 : forall t u v : term, SN (Recₜ u v t) -> SN t.
Proof.
intros. specialize (SN_rec3_eq (Recₜ u v t) u v H). intros. apply H0.
reflexivity.
Qed.

Lemma SN_ite1_eq : forall t u v : term, SN t -> forall w : term, t = IfThenElse w u v -> SN w.
Proof.
intros t u v H; induction H; intros. split; intros. apply (β_ite1 _ _ u v) in H2.
rewrite <- H1 in H2. specialize (H0 (IfThenElse t2 u v) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_ite1 : forall t u v : term, SN (IfThenElse t u v) -> SN t.
Proof.
intros. specialize (SN_ite1_eq (IfThenElse t u v) u v H). intros. apply H0.
reflexivity.
Qed.

Lemma SN_ite2_eq : forall t u v : term, SN t -> forall w : term, t = IfThenElse u w v -> SN w.
Proof.
intros t u v H; induction H; intros. split; intros. apply (β_ite2 u _ _ v) in H2.
rewrite <- H1 in H2. specialize (H0 (IfThenElse u t2 v) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_ite2 : forall t u v : term, SN (IfThenElse t u v) -> SN u.
Proof.
intros. specialize (SN_ite2_eq (IfThenElse t u v) t v H). intros. apply H0.
reflexivity.
Qed.

Lemma SN_ite3_eq : forall t u v : term, SN t -> forall w : term, t = IfThenElse u v w -> SN w.
Proof.
intros t u v H; induction H; intros. split; intros. apply (β_ite3 u v) in H2.
rewrite <- H1 in H2. specialize (H0 (IfThenElse u v t2) H2 t2). apply H0. reflexivity.
Qed.

Lemma SN_ite3 : forall t u v : term, SN (IfThenElse t u v) -> SN v.
Proof.
intros. specialize (SN_ite3_eq (IfThenElse t u v) t u H). intros. apply H0.
reflexivity.
Qed.

(**
Stability by lifting: when weakening the context, being SN does not change.*)

Lemma SN_lift_direct : forall (t : term) (k n : nat), SN t -> SN (lift k n t).
Proof.
intros. induction H. split; intros. specialize (lift_red_inv _ _ _ _ H1); intro.
destruct H2. rewrite H2. apply H0. rewrite H2 in H1. apply lift_red_rev in H1. apply H1.
Qed.

Lemma SN_lift_rev : forall (t : term) (k n : nat), SN t -> forall u : term, t = lift k n u -> SN u.
Proof.
intros t k n H; induction H.
intros. split; intros. apply (lift_red _ _ k n) in H2.
rewrite <- H1 in H2. specialize (H0 _ H2 t2).
apply H0. reflexivity.
Qed.

Lemma SN_lift : forall (t : term) (k n : nat), SN t <-> SN (lift k n t).
Proof.
intros. split; intro.
apply SN_lift_direct. apply H.
specialize (SN_lift_rev (lift k n t) k n H t); intro.
apply H0; reflexivity.
Qed.

(**
Stability by substitution: if t[u/x] is SN, then so is t.*)

Lemma SN_subst_eq : forall (t u : term) (n : nat), SN t -> forall v : term, t = {n ~> u} v -> SN v.
Proof.
intros t u n H; generalize u n; induction H. intros.
split; intros. apply (subst_red_r _ _ u0 n0) in H2. rewrite <- H1 in H2.
specialize (H0 ({n0 ~> u0} t2) H2 u0 n0 t2). apply H0; reflexivity.
Qed.

Lemma SN_subst : forall (t u : term) (n : nat), SN ({n ~> u} t) -> SN t.
Proof.
intros. specialize (SN_subst_eq ({n ~> u} t) u n H t). intro. apply H0.
reflexivity.
Qed.