Require Import system_T_first_def.
Require Import system_T_substi.
Require Import system_T_reduction.
Require Import system_T_types.
Require Import system_T_normal_form_SN.
Require Import system_T_context_wh_red.
Require Import system_T_weak_head_expansion.
Require Import system_T_sat.
Require Import system_T_adequacy.


(* ********************************************************************************************* *)

(** III. The strong normalization theorem *)

(** 10. Consequences.

We now study the consequences of the strong normalization theorem by studying the normal forms of
  typable terms.*)

(** A. Normal forms.

This part describes the normal forms of the different types.*)

Lemma typing_nats : forall (n : nat) (T : type), ⊢ code_nat n ~: T -> T = type_nat.
Proof.
induction n; intros. inversion H. reflexivity.
inversion H. apply IHn in H2. apply H2.
Qed.

Lemma empty_typing : forall (t : term) (T : type), normal_form t -> ⊢ t ~: T -> t = star \/
  t = Tt \/ t = Ff \/ (exists n : nat, t = code_nat n) \/ (exists u : term, t = λₜ u) \/
  (exists u v : term, t = ⟨ u , v ⟩) \/ (exists u : term, t = κ₁ u) \/
  (exists u : term, t = κ₂ u).
Proof.
induction t; intros.
  - inversion H0. inversion H3.
  - right. right. right. right. left. exists t. reflexivity.
  - inversion H0. assert (normal_form (t1 @ₜ t2)) as Hx; try apply H.
    apply app_normal_form in H. destruct H. assert (⊢ t1 ~: T1 →ₜ T); try apply H4.
    apply (IHt1 _ H) in H4. destruct H4; try (rewrite H4 in H8; inversion H8).
    destruct H4; try (rewrite H4 in H8; inversion H8).
    destruct H4; try (rewrite H4 in H8; inversion H8). destruct H4. destruct H4. rewrite H4 in H8.
    apply typing_nats in H8. inversion H8. destruct H4. destruct H4. exfalso. apply Hx.
    rewrite H4. exists ({0 ~> t2} x). apply β_to. destruct H4. destruct H4. destruct H4.
    rewrite H4 in H8. inversion H8. destruct H4. destruct H4. rewrite H4 in H8. inversion H8.
    destruct H4. rewrite H4 in H8; inversion H8.
  - right. right. right. left. exists 0. simpl. reflexivity.
  - inversion H0.
Admitted.

Lemma normal_form_nat : forall (t : term), normal_form t -> ⊢ t ~: type_nat -> exists n : nat,
  t = code_nat n.
Proof.
intros. specialize (empty_typing _ _ H H0); intro. destruct H1. rewrite H1 in H0. inversion H0.
destruct H1. rewrite H1 in H0; inversion H0. destruct H1. rewrite H1 in H0; inversion H0.
destruct H1. apply H1. destruct H1. destruct H1.
rewrite H1 in H0. inversion H0. destruct H1. destruct H1. destruct H1.
rewrite H1 in H0. inversion H0. destruct H1. destruct H1. rewrite H1 in H0. inversion H0.
destruct H1. rewrite H1 in H0; inversion H0.
Qed.

Corollary empty_type_nat : forall (t : term), ⊢ t ~: type_nat -> exists n : nat, t ⊳* code_nat n.
Proof.
intros. specialize (Strong_Normalization _ _ _ H); intro. apply SN_WN in H0. destruct H0.
destruct H0. specialize (subject_reduction_star _ _ _ _ H H0); intro.
specialize (normal_form_nat x H1 H2); intro. destruct H3. exists x0. rewrite H3 in H0. apply H0.
Qed.

Lemma normal_form_bool : forall (t : term), normal_form t -> ⊢ t ~: type_bool -> t = Tt \/ t = Ff.
Proof.
intros. specialize (empty_typing _ _ H H0); intro. destruct H1. rewrite H1 in H0. inversion H0.
destruct H1. left. apply H1. destruct H1. right. apply H1. destruct H1. destruct H1.
rewrite H1 in H0. specialize (typing_nats x type_bool H0); intro. inversion H2.
destruct H1. destruct H1. rewrite H1 in H0. inversion H0. destruct H1. destruct H1. destruct H1.
rewrite H1 in H0. inversion H0. destruct H1. destruct H1. rewrite H1 in H0. inversion H0.
destruct H1. rewrite H1 in H0; inversion H0.
Qed.

Corollary empty_type_bool : forall (t : term), ⊢ t ~: type_bool -> t ⊳* Tt \/ t ⊳* Ff.
Proof.
intros. specialize (Strong_Normalization _ _ _ H); intro. apply SN_WN in H0. destruct H0.
destruct H0. specialize (subject_reduction_star _ _ _ _ H H0); intro.
specialize (normal_form_bool x H1 H2); intro. destruct H3. left. rewrite H3 in H0. apply H0.
right. rewrite H3 in H0. apply H0.
Qed.

Lemma normal_form_fun : forall (t : term) (T1 T2 : type), normal_form t -> ⊢ t ~: T1 →ₜ T2 ->
  exists u : term, t = λₜ u.
Proof.
intros. specialize (empty_typing _ _ H H0); intro. destruct H1. rewrite H1 in H0. inversion H0.
destruct H1. rewrite H1 in H0; inversion H0. destruct H1. rewrite H1 in H0; inversion H0.
destruct H1. destruct H1.
rewrite H1 in H0. specialize (typing_nats x (T1 →ₜ T2) H0); intro. inversion H2.
destruct H1. apply H1. destruct H1. destruct H1. destruct H1.
rewrite H1 in H0. inversion H0. destruct H1. destruct H1. rewrite H1 in H0. inversion H0.
destruct H1. rewrite H1 in H0. inversion H0.
Qed.

Corollary empty_type_fun : forall (t : term) (T1 T2 : type), ⊢ t ~: T1 →ₜ T2 -> exists u : term,
  t ⊳* λₜ u.
Proof.
intros. specialize (Strong_Normalization _ _ _ H); intro. apply SN_WN in H0. destruct H0.
destruct H0. specialize (subject_reduction_star _ _ _ _ H H0); intro.
specialize (normal_form_fun x _ _ H1 H2); intro. destruct H3.
exists x0. rewrite H3 in H0. apply H0.
Qed.

Lemma normal_form_prod : forall (t : term) (T1 T2 : type), normal_form t -> ⊢ t ~: T1 ×ₜ T2 ->
  exists u v : term, t = ⟨u,v⟩.
Proof.
intros. specialize (empty_typing _ _ H H0); intro. destruct H1. rewrite H1 in H0. inversion H0.
destruct H1. rewrite H1 in H0; inversion H0. destruct H1. rewrite H1 in H0; inversion H0.
destruct H1. destruct H1.
rewrite H1 in H0. specialize (typing_nats x (T1 ×ₜ T2) H0); intro. inversion H2.
destruct H1. destruct H1. rewrite H1 in H0. inversion H0. destruct H1. apply H1.
destruct H1. destruct H1. rewrite H1 in H0. inversion H0. destruct H1.
rewrite H1 in H0; inversion H0.
Qed.

Corollary empty_type_prof : forall (t : term) (T1 T2 : type), ⊢ t ~: T1 ×ₜ T2 -> exists u v : term,
  t ⊳* ⟨u,v⟩.
Proof.
intros. specialize (Strong_Normalization _ _ _ H); intro. apply SN_WN in H0. destruct H0.
destruct H0. specialize (subject_reduction_star _ _ _ _ H H0); intro.
specialize (normal_form_prod x _ _ H1 H2); intro. destruct H3. destruct H3.
exists x0. exists x1. rewrite H3 in H0. apply H0.
Qed.

Lemma normal_form_unit : forall (t : term), normal_form t -> ⊢ t ~: type_unit -> t = star.
Proof.
intros. specialize (empty_typing _ _ H H0); intro. destruct H1. apply H1.
destruct H1. rewrite H1 in H0; inversion H0. destruct H1. rewrite H1 in H0; inversion H0.
destruct H1. destruct H1.
rewrite H1 in H0. specialize (typing_nats x type_unit H0); intro. inversion H2.
destruct H1. destruct H1. rewrite H1 in H0. inversion H0. destruct H1.
destruct H1. destruct H1. rewrite H1 in H0. inversion H0. destruct H1.
destruct H1. rewrite H1 in H0. inversion H0. destruct H1.
rewrite H1 in H0; inversion H0.
Qed.

Corollary empty_type_unit : forall (t : term), ⊢ t ~: type_unit -> t ⊳* star.
Proof.
intros. specialize (Strong_Normalization _ _ _ H); intro. apply SN_WN in H0. destruct H0.
destruct H0. specialize (subject_reduction_star _ _ _ _ H H0); intro.
specialize (normal_form_unit x H1 H2); intro. destruct H3. apply H0.
Qed.

Lemma normal_form_sum : forall (t : term) (T1 T2 : type), normal_form t -> ⊢ t ~: T1 +ₜ T2 ->
  exists u : term, t = κ₁ u \/ t = κ₂ u.
Proof.
intros. specialize (empty_typing _ _ H H0); intro. destruct H1. rewrite H1 in H0. inversion H0.
destruct H1. rewrite H1 in H0; inversion H0. destruct H1. rewrite H1 in H0; inversion H0.
destruct H1. destruct H1.
rewrite H1 in H0. specialize (typing_nats x (T1 +ₜ T2) H0); intro. inversion H2.
destruct H1. destruct H1. rewrite H1 in H0. inversion H0. destruct H1. destruct H1. destruct H1.
rewrite H1 in H0. inversion H0. destruct H1. destruct H1. exists x. left. apply H1.
destruct H1. exists x. right. apply H1.
Qed.

Corollary empty_type_sum : forall (t : term) (T1 T2 : type), ⊢ t ~: T1 +ₜ T2 -> exists u : term,
  t ⊳* κ₁ u \/ t ⊳* κ₂ u.
Proof.
intros. specialize (Strong_Normalization _ _ _ H); intro. apply SN_WN in H0. destruct H0.
destruct H0. specialize (subject_reduction_star _ _ _ _ H H0); intro.
specialize (normal_form_sum _ _ _ H1 H2); intro. destruct H3. exists x0. destruct H3.
left. rewrite H3 in H0. apply H0. right. rewrite H3 in H0. apply H0.
Qed.

Lemma no_normal_form_void : forall (t : term), normal_form t -> ~(⊢ t ~: type_void).
Proof.
intros. intro. specialize (empty_typing _ _ H H0); intro. destruct H1. rewrite H1 in H0.
inversion H0. destruct H1. rewrite H1 in H0; inversion H0. destruct H1.
rewrite H1 in H0; inversion H0. destruct H1. destruct H1.
rewrite H1 in H0. specialize (typing_nats x type_void H0); intro. inversion H2.
destruct H1. destruct H1. rewrite H1 in H0. inversion H0. destruct H1. destruct H1. destruct H1.
rewrite H1 in H0. inversion H0. destruct H1. destruct H1. rewrite H1 in H0. inversion H0.
destruct H1. rewrite H1 in H0; inversion H0.
Qed.

Corollary consistency : forall (t : term), ~(⊢ t ~: type_void).
Proof.
intros; intro. specialize (Strong_Normalization _ _ _ H); intro. apply SN_WN in H0. destruct H0.
destruct H0. specialize (subject_reduction_star _ _ _ _ H H0); intro.
apply (no_normal_form_void _ H1 H2).
Qed.