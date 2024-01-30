Require Import system_T_first_def.
Require Import system_T_substi.
Require Import system_T_reduction.
Require Import system_T_types.
Require Import system_T_normal_form_SN.
Require Import system_T_context_wh_red.
Require Import system_T_weak_head_expansion.
Require Import PeanoNat.
Require Import List.

(* *********************************************************** *)

(** III. The strong normalization theorem 

We give here the outline of the proof of the strong normalization
   theorem :
   - we construct for each type T a set [[T]] ⊆ SN in such a way
     that if t : T then t ∈ [[T]].
   - we prove by induction that, indeed, t : T -> t ∈ [[T]]
   - this means that t : T -> SN t. *)

(** 8. Saturated sets.

In this file, we construct the saturated sets associated to each
   type, and prove that the interpretation function indeed gives
   saturated sets. The properties of a saturated set are what we
   need for the proof: it must contain only strong normalizing
   terms, it must be stable by weak head expansion and it must
   be stable by lifting in an elimination context.*)

Definition saturated_set (A : term -> Prop) : Prop :=
  (forall t, A t -> SN t)
  /\ (forall E : Elim, forall n : nat, SNE E -> A(E [ₑ {{n}}]))
  /\ (forall E : Elim, forall t u : term,
         A (E [ₑ{0 ~> u} t]) -> SN u -> A (E [ₑ λₜ t @ₜ u]))
  /\ (forall E : Elim, forall t u : term,
         SN u -> A (E [ₑ t]) -> A (E [ₑ π₁ (⟨ t , u ⟩)]))
  /\ (forall E : Elim, forall t u : term,
         SN t -> A (E [ₑ u]) -> A (E [ₑ π₂ (⟨ t , u ⟩)]))
  /\ (forall E : Elim, forall t u v : term,
         SN t -> SN v -> A (E [ₑ{0 ~> t} u]) ->
         A (E [ₑ delta u v (κ₁ t)]))
  /\ (forall E : Elim, forall t u v : term,
         SN t -> SN u -> A (E [ₑ{0 ~> t} v]) ->
         A (E [ₑ delta u v (κ₂ t)]))
  /\ (forall E : Elim, forall t u : term,
         SN u -> A (E [ₑ t]) -> A (E [ₑ IfThenElse Tt t u]))
  /\ (forall E : Elim, forall t u : term,
         SN t -> A (E [ₑ u]) -> A (E [ₑ IfThenElse Ff t u]))
  /\ (forall E : Elim, forall t u : term,
         SN u -> A (E [ₑ t]) -> A (E [ₑ Recₜ t u zero]))
  /\ (forall E : Elim, forall t u v : term,
         SN t -> SN v -> A (E [ₑ ( u @ₜ v) @ₜ (Recₜ t u v)]) ->
         A (E [ₑ Recₜ t u (Sₜ v)]))
  /\ (forall (E : Elim) (t : term) (k n : nat),
         A (E [ₑ t]) -> A (E [ₑ lift k n t])).

(** First, we give the result that if A is saturated, then a is
    stable by weak head expansion, granted that the expansion
    gives a strongly normalising term.*)

Lemma SAT_0_expansion : forall (A : term -> Prop) (t u : term),
    saturated_set A -> SN t -> A u -> t ⊳₀ u -> A t.
Proof.
  intros A t u H.
  destruct H as
    (H & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  intros.
  induction H13.
  - specialize (H1 hole _ _ H12 (SN_app2 _ _ H11)).
    simpl in H1; apply H1.
  - assert (SN u). apply SN_proj1 in H11. apply SN_pair in H11.
    apply H11.
    specialize (H2 hole _ _ H13 H12). simpl in H2; apply H2.
  - assert (SN t). apply SN_proj2 in H11. apply SN_pair in H11.
    apply H11.
    specialize (H3 hole _ _ H13 H12). simpl in H3; apply H3.
  - specialize (H4 hole); simpl in H4; apply H4.
    apply SN_delta3 in H11. apply SN_inj1 in H11.
    apply H11. apply SN_delta2 in H11. apply H11. apply H12.
  - specialize (H5 hole); simpl in H5; apply H5.
    apply SN_delta3 in H11. apply SN_inj2 in H11.
    apply H11. apply SN_delta1 in H11. apply H11. apply H12.
  - specialize (H8 hole); simpl in H8; apply H8.
    apply SN_rec2 in H11. apply H11. apply H12.
  - specialize (H9 hole); simpl in H9; apply H9.
    apply SN_rec1 in H11. apply H11.
    apply SN_rec3 in H11. apply SN_succ in H11. apply H11.
    apply H12.
  - specialize (H6 hole); simpl in H6; apply H6.
    apply SN_ite3 in H11. apply H11. apply H12.
  - specialize (H7 hole); simpl in H7; apply H7.
    apply SN_ite2 in H11. apply H11. apply H12.
Qed.

Lemma SAT_0_exp_ctx : forall (A : term -> Prop) (E : Elim)
                             (t u : term),
    saturated_set A -> SN (E[ₑ t]) -> A (E[ₑ u]) -> t ⊳₀ u ->
    A (E[ₑ t]).
Proof.
  intros A E t u H.
  destruct H as
    (H & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  intros. generalize H11 H12; clear H11 H12.
  induction H13; intros.
  - apply H1. apply H12. apply SNE_fill_SN in H11.
    apply SN_app2 in H11. apply H11.
  - apply H2; try apply H12. apply SNE_fill_SN in H11.
    apply SN_proj1 in H11.
    apply SN_pair in H11; apply H11.
  - apply H3; try apply H12. apply SNE_fill_SN in H11.
    apply SN_proj2 in H11.
    apply SN_pair in H11; apply H11.
  - apply H4; try apply H12; apply SNE_fill_SN in H11.
    apply SN_delta3 in H11.
    apply SN_inj1 in H11. apply H11. apply SN_delta2 in H11.
    apply H11.
  - apply H5; try apply H12; apply SNE_fill_SN in H11.
    apply SN_delta3 in H11.
    apply SN_inj2 in H11. apply H11. apply SN_delta1 in H11.
    apply H11.
  - apply H8; try apply H12. apply SNE_fill_SN in H11.
    apply SN_rec2 in H11. apply H11.
  - apply H9; try apply H12; apply SNE_fill_SN in H11.
    apply SN_rec1 in H11. apply H11.
    apply SN_rec3 in H11. apply SN_succ in H11. apply H11.
  - apply H6; try apply H12. apply SNE_fill_SN in H11.
    apply SN_ite3 in H11. apply H11.
  - apply H7; try apply H12. apply SNE_fill_SN in H11.
    apply SN_ite2 in H11. apply H11.
Qed.

Lemma SAT_wh_expansion : forall (A : term -> Prop) (t u : term),
    saturated_set A -> SN t -> A u -> t ⊳ₕ u -> A t.
Proof.
  intros. apply equiv_wh_ind in H2.
  destruct H2; destruct H2; destruct H2.
  destruct H2. destruct H3.
  rewrite H2; rewrite H2 in H0; rewrite H3 in H1.
  apply (SAT_0_exp_ctx A x x0 x1 H H0 H1 H4).
Qed.

Lemma SAT_wh_expansion_star : forall (A : term -> Prop)
                                     (t u : term),
    saturated_set A -> SN t -> A u -> t ⊳ₕ* u -> A t.
Proof.
  intros. induction H2. apply H1. specialize (IHrt_closure H0).
  apply (SAT_wh_expansion A u v H) in H3. apply IHrt_closure.
  apply H3. apply (reduc_SN_star t _ H0). apply wh_star_β_star.
  apply H2. apply H1.
Qed.

(** We prove that SAT is a complete lattice with regard to ⊆,
    with top element being SAT and bottom element being the
    wh-expansion closure of variables.*)

Definition Top_SAT : term -> Prop := SN.
Definition Bot_SAT (t : term) : Prop :=
  SN t /\
    (exists E : Elim, exists n : nat,
        SNE E /\ t ⊳ₕ* (E [ₑ {{n}}])).

Lemma Top_is_SAT : saturated_set Top_SAT.
Proof.
  unfold saturated_set.
  split; intros; try (apply H).
  split. intros. apply SNE_var_SN. apply H.
  split; intros. apply weak_head_lambda. apply H. apply H0.
  split; intros. apply weak_head_pair1. apply H0. apply H.
  split; intros. apply weak_head_pair2. apply H0. apply H.
  split; intros. apply weak_head_inj1. apply H1. apply H0.
  apply H.
  split; intros. apply weak_head_inj2. apply H1. apply H0.
  apply H.
  split; intros. apply weak_head_ite1. apply H0. apply H.
  split; intros. apply weak_head_ite2. apply H0. apply H.
  split; intros. apply weak_head_rec1. apply H0. apply H.
  split; intros. apply weak_head_rec2. apply H1. apply H.
  apply H0.
  apply lift_ctx_SN. apply H.
Qed.

Lemma Bot_is_SAT : saturated_set Bot_SAT.
Proof.
  unfold saturated_set.
  split; intros. destruct H. apply H.
  split; intros. unfold Bot_SAT. split.
  apply SNE_var_SN. apply H.
  exists E. exists n. split; try apply H. apply rt_refl.
  split; intros. destruct H. destruct H1. destruct H1.
  destruct H1. unfold Bot_SAT.
  split. apply weak_head_lambda. apply H. apply H0.
  exists x. exists x0. split; try apply H1.
  assert (E [ₑ λₜ t @ₜ u] ⊳ₕ* E [ₑ {0 ~> u} t]).
  apply wh_star_wh. apply equiv_wh_ind. exists E.
  exists (λₜ t @ₜ u). exists ({0 ~> u} t).
  repeat (split; try reflexivity). apply to_0.
  apply (wh_trans _ _ _ H3 H2).
  split; intros. destruct H0. destruct H1. destruct H1.
  unfold Bot_SAT.
  split; try (apply weak_head_pair1; try apply H0; try apply H).
  exists x. exists x0. split; try apply H1. destruct H1.
  assert (E [ₑ π₁ (⟨ t, u ⟩)] ⊳ₕ* E [ₑ t]). apply wh_star_wh.
  apply equiv_wh_ind. exists E.
  exists (π₁ (⟨ t, u ⟩)). exists t.
  repeat (split; try reflexivity). apply proj1_0.
  apply (wh_trans _ _ _ H3 H2).
  split; intros. destruct H0. destruct H1. destruct H1.
  unfold Bot_SAT.
  split; try (apply weak_head_pair2; try apply H0; try apply H).
  exists x. exists x0. split; try apply H1. destruct H1.
  assert (E [ₑ π₂ (⟨ t, u ⟩)] ⊳ₕ* E [ₑ u]). apply wh_star_wh.
  apply equiv_wh_ind. exists E.
  exists (π₂ (⟨ t, u ⟩)). exists u.
  repeat (split; try reflexivity). apply proj2_0.
  apply (wh_trans _ _ _ H3 H2).
  split; intros. destruct H1. destruct H2. destruct H2.
  destruct H2. unfold Bot_SAT.
  split; try (apply weak_head_inj1; try apply H1;
              try apply H; try apply H0).
  exists x. exists x0. split; try apply H2.
  assert (E [ₑ delta u v (κ₁ t)] ⊳ₕ* E [ₑ {0 ~> t} u]).
  apply wh_star_wh. apply equiv_wh_ind. exists E.
  exists (delta u v (κ₁ t)). exists ({0 ~> t} u).
  repeat (split; try reflexivity). apply inj1_0.
  apply (wh_trans _ _ _ H4 H3).
  split; intros. destruct H1. destruct H2. destruct H2.
  destruct H2. unfold Bot_SAT.
  split; try (apply weak_head_inj2; try apply H1;
              try apply H; try apply H0).
  exists x. exists x0. split; try apply H2.
  assert (E [ₑ delta u v (κ₂ t)] ⊳ₕ* E [ₑ {0 ~> t} v]).
  apply wh_star_wh. apply equiv_wh_ind. exists E.
  exists (delta u v (κ₂ t)). exists ({0 ~> t} v).
  repeat (split; try reflexivity). apply inj2_0.
  apply (wh_trans _ _ _ H4 H3).
  split; intros. destruct H0. destruct H1. destruct H1.
  destruct H1. unfold Bot_SAT.
  split; try (apply weak_head_ite1; try apply H0; try apply H).
  exists x. exists x0. split; try apply H1.
  assert (E [ₑ IfThenElse Tt t u] ⊳ₕ* E [ₑ t]). apply wh_star_wh.
  apply equiv_wh_ind. exists E.
  exists (IfThenElse Tt t u). exists t.
  repeat (split; try reflexivity). apply Tt_0.
  apply (wh_trans _ _ _ H3 H2).
  split; intros. destruct H0. destruct H1. destruct H1.
  destruct H1. unfold Bot_SAT.
  split; try (apply weak_head_ite2; try apply H0; try apply H).
  exists x. exists x0. split; try apply H1.
  assert (E [ₑ IfThenElse Ff t u] ⊳ₕ* E [ₑ u]). apply wh_star_wh.
  apply equiv_wh_ind. exists E.
  exists (IfThenElse Ff t u). exists u.
  repeat (split; try reflexivity). apply Ff_0.
  apply (wh_trans _ _ _ H3 H2).
  split; intros. destruct H0. destruct H1. destruct H1.
  destruct H1. unfold Bot_SAT.
  split; try (apply weak_head_rec1; try apply H0; try apply H).
  exists x. exists x0. split; try apply H1.
  assert (E [ₑ Recₜ t u zero] ⊳ₕ* E [ₑ t]). apply wh_star_wh.
  apply equiv_wh_ind. exists E.
  exists (Recₜ t u zero). exists t.
  repeat (split; try reflexivity). apply rec1_0.
  apply (wh_trans _ _ _ H3 H2).
  split; intros. destruct H1. destruct H2. destruct H2.
  destruct H2. unfold Bot_SAT.
  split; try (apply weak_head_rec2; try apply H1;
              try apply H; try apply H0).
  exists x. exists x0. split; try apply H2.
  assert (E [ₑ Recₜ t u (Sₜ v)] ⊳ₕ* E [ₑ (u @ₜ v) @ₜ Recₜ t u v]).
  apply wh_star_wh.
  apply equiv_wh_ind. exists E.
  exists (Recₜ t u (Sₜ v)). exists ((u @ₜ v) @ₜ Recₜ t u v).
  repeat (split; try reflexivity).
  apply rec2_0. apply (wh_trans _ _ _ H4 H3).
  unfold Bot_SAT in H. destruct H. destruct H0. destruct H0.
  destruct H0.
  unfold Bot_SAT. split. apply lift_ctx_SN. apply H.
  specialize (elim_to_var_ctx_lift E x t k n x0 H1); intro.
  destruct H2; destruct H2. exists x1. exists x2. split;
    try apply H2.
  apply (wh_star_β_star) in H2. apply (SN_SNE _ ({{x2}})).
  assert (SN (E [ₑ lift k n t])). apply lift_ctx_SN. apply H.
  apply (reduc_SN_star _ _ H3 H2).
Qed.

Lemma Union_SAT : forall (A : Type) (P : A -> Prop)
                         (f : A -> term -> Prop) (a : A),
    P a -> (forall (a : A), P a -> saturated_set (f a)) ->
    saturated_set (fun t => exists (a : A), P a /\ f a t).
Proof.
  intros. split. intros. destruct H1. specialize (H0 x).
  apply H0; apply H1.
  split. intros. specialize (H0 a). exists a. split; try apply H.
  apply H0. apply H. apply H1.
  clear a H.
  split; intros. destruct H. specialize (H0 x). exists x.
  split; try apply H. destruct H.
  apply (H0 H). apply H2. apply H1.
  split; intros. destruct H1; destruct H1; specialize (H0 x H1).
  exists x. split; try apply H1.
  destruct H0 as (_ & _ & _ & H3 & _). apply H3. apply H.
  apply H2.
  split; intros. destruct H1; destruct H1; specialize (H0 x H1).
  exists x. split; try apply H1.
  destruct H0 as (_ & _ & _ & _ & H3 & _). apply H3. apply H.
  apply H2.
  split; intros. destruct H2; destruct H2; specialize (H0 x H2).
  exists x. split; try apply H2.
  destruct H0 as (_ & _ & _ & _ & _ & H4 & _). apply H4. apply H.
  apply H1. apply H3.
  split; intros. destruct H2; destruct H2; specialize (H0 x H2).
  exists x. split; try apply H2.
  destruct H0 as (_ & _ & _ & _ & _ & _ & H4 & _). apply H4.
  apply H. apply H1. apply H3.
  split; intros. destruct H1; destruct H1; specialize (H0 x H1).
  exists x. split; try apply H1.
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & H4 & _). apply H4.
  apply H. apply H2.
  split; intros. destruct H1; destruct H1; specialize (H0 x H1).
  exists x. split; try apply H1.
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & H4 & _).
  apply H4. apply H. apply H2.
  split; intros. destruct H1; destruct H1; specialize (H0 x H1).
  exists x. split; try apply H1.
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H4 & _).
  apply H4. apply H. apply H2.
  split; intros. destruct H2; destruct H2; specialize (H0 x H2).
  exists x. split; try apply H2.
  destruct H0 as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H4 & _).
  apply H4. apply H. apply H1.
  apply H3.
  destruct H. destruct H. exists x. split; try apply H.
  apply (H0 x H). apply H1.
Qed.

Lemma Inter_SAT : forall (A : Type) (P : A -> Prop)
                         (f : A -> term -> Prop) (a : A),
    P a -> (forall (a : A), P a -> saturated_set (f a)) ->
    saturated_set (fun t => forall (a : A), P a -> f a t).
Proof.
  intros A P f a Hinf; intros. split. intros.
  specialize (H a Hinf). apply H in H0. apply H0.
  apply Hinf.
  clear a Hinf; split. intros. specialize (H a). apply H.
  apply H1. apply H0.
  split; intros. specialize (H a). apply H in H0. apply H0.
  apply H2. apply H2. apply H1.
  split; intros. specialize (H a).
  destruct (H H2) as (_ & _ & _ & H3 & _).
  apply H3. apply H0. apply (H1 a H2).
  split; intros. specialize (H a H2).
  destruct H as (_ & _ & _ & _ & H3 & _).
  apply H3. apply H0. apply (H1 a H2).
  split; intros. specialize (H a H3).
  destruct H as (_ & _ & _ & _ & _ & H4 & _).
  apply H4. apply H0. apply H1. apply (H2 a H3).
  split; intros. specialize (H a H3).
  destruct H as (_ & _ & _ & _ & _ & _ & H4 & _).
  apply H4. apply H0. apply H1. apply (H2 a H3).
  split; intros. specialize (H a H2).
  destruct H as (_ & _ & _ & _ & _ & _ & _ & H4 & _).
  apply H4. apply H0. apply (H1 a H2).
  split; intros. specialize (H a H2).
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H3 & _).
  apply H3. apply H0. apply (H1 a H2).
  split; intros. specialize (H a H2).
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H3 & _).
  apply H3. apply H0. apply (H1 a H2).
  split; intros. specialize (H a H3).
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H4 & _).
  apply H4. apply H0. apply H1. apply (H2 a H3).
  apply (H a H1). apply (H0 a H1).
Qed.

Lemma Top_is_greatest : forall (A : term -> Prop) (t : term),
    saturated_set A -> A t -> SN t.
Proof.
  intros. apply H; apply H0.
Qed.

Lemma Bot_is_lowest : forall (A : term -> Prop) (t : term),
    saturated_set A -> Bot_SAT t -> A t.
Proof.
  intros. destruct H0. destruct H1. destruct H1. destruct H1.
  assert (saturated_set A); try apply H.
  destruct H as (_ & H & _). specialize (H x x0 H1).
  apply (SAT_wh_expansion_star _ _ _ H3 H0 H H2).
Qed.

Lemma Union_is_lub : forall (A : Type) (f : A -> term -> Prop)
                            (P : A -> Prop) (a : A),
    (forall (b : A) (t : term), P b -> f b t ->
                                exists a : A, P a /\ f a t) /\
      (forall C : term -> Prop,
          (forall (b : A) (t : term), P b -> f b t -> C t) ->
          (forall t : term, (exists a : A, P a /\ f a t) -> C t)
      ).
Proof.
  intros. split; intros. exists b. split. apply H. apply H0.
  destruct H0. destruct H0. apply (H x t). apply H0. apply H1.
Qed.

Lemma Inter_is_glb : forall (A : Type) (f : A -> term -> Prop)
                            (P : A -> Prop) (a : A),
    (forall (b : A) (t : term),
        (forall a : A, P a -> f a t) -> P b -> f b t) /\
      (forall C : term -> Prop,
          (forall (b : A) (t : term), C t -> P b -> f b t) ->
          (forall t : term, C t -> forall b : A, P b -> f b t)).
Proof.
  intros. split; intros. apply H. apply H0.
  apply H. apply H0. apply H1.
Qed.

(** As we know that SAT is a complete lattice, we develop a bit
    of lattice theory, i.e. we prove Knaster-Tarski theorem and
    give a fixpoint construction for monotone functions on SAT,
    which will be used to construct the interpretation of nat.*)

Definition SAT_mono (f : (term -> Prop) -> term -> Prop) :=
  (forall A : term -> Prop,
      saturated_set A -> saturated_set (f A)) /\
    (forall A B : term -> Prop,
        (forall t : term, A t -> B t) ->
        (forall t : term, f A t -> f B t)).

Definition prefix_SAT (f : (term -> Prop) -> term -> Prop)
  (A : term -> Prop) : Prop :=
  saturated_set A /\ forall t : term, f A t -> A t.

Definition fixpoint_SAT (f : (term -> Prop) -> term -> Prop)
  (t : term) : Prop :=
  forall (A : term -> Prop), prefix_SAT f A -> A t.

Lemma fixpoint_SAT_is_SAT : forall
    (f : (term -> Prop) -> term -> Prop),
    SAT_mono f -> saturated_set (fixpoint_SAT f).
Proof.
  intros. unfold fixpoint_SAT. specialize Inter_SAT; intro.
  specialize (H0 (term -> Prop) (prefix_SAT f)
                (fun x => x) Top_SAT).
  apply H0. split. apply Top_is_SAT. intro.
  apply Top_is_greatest. apply H. apply Top_is_SAT.
  intros. apply H1.
Qed.

Lemma fixpoint_SAT_is_prefix : forall
    (f : (term -> Prop) -> term -> Prop),
    SAT_mono f -> forall t : term,
      f (fixpoint_SAT f) t -> fixpoint_SAT f t.
Proof.
  intros. unfold fixpoint_SAT. intros. apply H1. destruct H.
  apply (H2 (fixpoint_SAT f) _). intros. apply H3. apply H1.
  apply H0.
Qed.

Theorem Knaster_Tarski : forall
    (f : (term -> Prop) -> term -> Prop),
    SAT_mono f -> forall t : term,
      fixpoint_SAT f t <-> f (fixpoint_SAT f) t.
Proof.
  intros. split; try (apply fixpoint_SAT_is_prefix; apply H).
  intro.
  unfold fixpoint_SAT in H0.
  specialize (H0 (f (fixpoint_SAT f))).
  assert (prefix_SAT f (f (fixpoint_SAT f))). split.
  apply H.
  apply fixpoint_SAT_is_SAT. apply H. apply H.
  apply fixpoint_SAT_is_prefix. apply H. specialize (H0 H1).
  apply H0.
Qed.

(** Those are the definitions of the different cases of [[_]],
    along with the full definition of [[_]].*)

Definition ArrowInterp (A : term -> Prop) (B : term -> Prop) t
  : Prop := forall u : term, A u -> B ( t @ₜ u).
Definition TimesInterp (A : term -> Prop) (B : term -> Prop) t
  : Prop := (A (π₁ t)) /\ (B (π₂ t)).
Definition SumInterp (A : term -> Prop) (B : term -> Prop) t
  : Prop :=
  forall (C : term -> Prop), forall u v : term,
    saturated_set C ->
    (forall w : term, A w -> C ({0 ~> w} u)) ->
    (forall w : term, B w -> C ({0 ~> w} v)) ->
    C (δ(0 ↦ u |0 ↦ v) t).
Definition UnitInterp : term -> Prop := Top_SAT.
Definition VoidInterp : term -> Prop := Bot_SAT.
Definition BoolInterp t : Prop := forall (C : term -> Prop),
  forall u v : term,
  saturated_set C -> C u -> C v -> C (IfThenElse t u v).

Definition NatInterpAux (A : term -> Prop) (t : term) : Prop :=
  forall (B : term -> Prop), forall u v : term,
    saturated_set B -> B u ->
    (forall w : term , forall x : term,
        A w -> B x -> B (v @ₜ w @ₜ x)) ->
    B (Recₜ u v t).

Definition NatInterp : term -> Prop := fixpoint_SAT NatInterpAux.

Lemma is_incr_NatInterpAux : forall (A B : term -> Prop),
    (forall t : term, A t -> B t) ->
    forall t : term, NatInterpAux A t -> NatInterpAux B t.
Proof.
  intros. unfold NatInterpAux in H0. unfold NatInterpAux. intros.
  apply H0. apply H1. apply H2. intros. apply H3. apply H.
  apply H4. apply H5.
Qed.

Lemma is_SAT_NatInterpAux : forall (A : term -> Prop),
    saturated_set A -> saturated_set (NatInterpAux A).
Proof.
  intros.
  split. intros. unfold NatInterpAux in H0.
  specialize (H0 A ({{0}}) ({{0}}) H).
  assert (A (Recₜ {{0}} {{0}} t)). apply H0.
  destruct H as (_ & H1 & _). specialize (H1 hole 0 holeSN).
  simpl in H1. apply H1.
  intros. destruct H as (H3 & H4 & _).
  specialize (H4 (apli (apli hole w) x) 0).
  simpl in H4. apply H4. apply appSNE. apply appSNE.
  apply holeSN. apply H3. apply H1.
  apply H3. apply H2. apply H in H1. apply SN_rec3 in H1.
  apply H1.
  split; intros. unfold NatInterpAux. intros.
  destruct H1 as (H1 & H4 & _). assert (B (hole [ₑ{{0}}])).
  apply (H4 hole 0 holeSN).
  specialize (H4 (recel u v E) n). simpl in H4; apply H4.
  apply recelSN.
  apply H1; apply H2. specialize (H3 ({{0}}) ({{0}})).
  destruct H as (_ & H & _).
  specialize (H hole 0 holeSN). simpl in H. simpl in H5.
  specialize (H3 H H5).
  apply H1 in H3. apply SN_app1 in H3. apply SN_app1 in H3.
  apply H3. apply H0.
  split; intros. unfold NatInterpAux in H0.
  unfold NatInterpAux; intros. specialize (H0 B u0 v H2 H3 H4).
  destruct H2 as (_ & _ & H2 & _).
  specialize (H2 (recel u0 v E) t u).
  simpl in H2. apply (H2 H0 H1).
  split; intros. unfold NatInterpAux; intros.
  unfold NatInterpAux in H1.
  specialize (H1 B u0 v H2 H3 H4).
  destruct H2 as (_ & _ & _ & H2 & _).
  specialize (H2 (recel u0 v E) t u H0). simpl in H2.
  apply (H2 H1).
  split; intros. unfold NatInterpAux; intros.
  unfold NatInterpAux in H1.
  specialize (H1 B u0 v H2 H3 H4).
  destruct H2 as (_ & _ & _ & _ & H2 & _).
  specialize (H2 (recel u0 v E) t u H0). simpl in H2.
  apply (H2 H1).
  split; intros. unfold NatInterpAux; intros.
  unfold NatInterpAux in H2.
  specialize (H2 B u0 v0 H3 H4 H5).
  destruct H3 as (_ & _ & _ & _ & _ & H3 & _).
  specialize (H3 (recel u0 v0 E) t u v H0). simpl in H3.
  apply (H3 H1 H2).
  split; intros. unfold NatInterpAux; intros.
  unfold NatInterpAux in H2.
  specialize (H2 B u0 v0 H3 H4 H5).
  destruct H3 as (_ & _ & _ & _ & _ & _ & H3 & _).
  specialize (H3 (recel u0 v0 E) t u v H0). simpl in H3.
  apply (H3 H1 H2).
  split; intros. unfold NatInterpAux; intros.
  unfold NatInterpAux in H1.
  specialize (H1 B u0 v H2 H3 H4).
  destruct H2 as (_ & _ & _ & _ & _ & _ & _ & H2 & _).
  specialize (H2 (recel u0 v E) t u H0). simpl in H2.
  apply (H2 H1).
  split; intros. unfold NatInterpAux; intros.
  unfold NatInterpAux in H1.
  specialize (H1 B u0 v H2 H3 H4).
  destruct H2 as (_ & _ & _ & _ & _ & _ & _ & _ & H2 & _).
  specialize (H2 (recel u0 v E) t u H0). simpl in H2.
  apply (H2 H1).
  split; intros. unfold NatInterpAux; intros.
  unfold NatInterpAux in H1.
  specialize (H1 B u0 v H2 H3 H4).
  destruct H2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H2 & _).
  specialize (H2 (recel u0 v E) t u H0). simpl in H2.
  apply (H2 H1).
  split; intros. unfold NatInterpAux; intros.
  unfold NatInterpAux in H2.
  specialize (H2 B u0 v0 H3 H4 H5).
  destruct H3 as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H3 & _).
  specialize (H3 (recel u0 v0 E) t u v H0). simpl in H3.
  apply (H3 H1 H2).
  unfold NatInterpAux in H; unfold NatInterpAux; intros.
  unfold NatInterpAux in H0. specialize (H0 B u v H1 H2 H3).
  destruct H1 as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1).
  specialize (H1 (recel u v E) t k n). simpl in H1. apply H1.
  apply H0.
Qed.

Lemma is_mono_NatInterpAux : SAT_mono NatInterpAux.
Proof.
  split. apply is_SAT_NatInterpAux. apply is_incr_NatInterpAux.
Qed.

Lemma sat_nat : saturated_set NatInterp.
Proof.
  apply fixpoint_SAT_is_SAT. apply is_mono_NatInterpAux.
Qed.

Lemma rec_for_NatInterp : forall (t : term),
    NatInterp t <->
      (forall (A : term -> Prop),
        forall u v : term,
          saturated_set A -> A u ->
          (forall w x : term, NatInterp w -> A x ->
                              A (v @ₜ w @ₜ x)) ->
          A (Recₜ u v t)).
Proof.
  intros. apply Knaster_Tarski. apply is_mono_NatInterpAux.
Qed.

Lemma zeroIsNat : NatInterp zero.
Proof.
  unfold NatInterp. apply rec_for_NatInterp; intros.
  destruct H as (H2 & H4 & _ & _ & _ & _ & _ & _ & _ & H3 & _).
  specialize (H3 hole); simpl in H3. apply H3.
  specialize (H1 ({{0}}) ({{0}})).
  assert (A ((v @ₜ {{0}}) @ₜ {{0}})). apply H1.
  specialize sat_nat; intro.
  destruct H as (_ & H & _). specialize (H hole 0 holeSN).
  simpl in H. apply H. specialize (H4 hole 0 holeSN).
  simpl in H4; apply H4. apply H2 in H.
  apply SN_app1 in H. apply SN_app1 in H. apply H. apply H0.
Qed.

Lemma succIsNat : forall (t : term), NatInterp t ->
                                     NatInterp (Sₜ t).
Proof.
  intros.
  apply rec_for_NatInterp. intros.
  assert (saturated_set A) as HA; try apply H0.
  destruct H0 as
    (H3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 hole u v t). simpl in H0. apply H0.
  apply H3. apply H1. apply sat_nat. apply H.
  apply H2. apply H. specialize (rec_for_NatInterp t). intro.
  destruct H4; clear H5. specialize (H4 H A u v HA H1 H2).
  apply H4.
Qed.

Fixpoint interpretation T : term -> Prop :=
  match T with
    | type_var n => SN
    | type_nat => NatInterp
    | type_bool => BoolInterp
    | type_unit => UnitInterp
    | type_void => VoidInterp
    | T →ₜ U => ArrowInterp (interpretation T) (interpretation U)
    | T ×ₜ U => TimesInterp (interpretation T) (interpretation U)
    | T +ₜ U => SumInterp (interpretation T) (interpretation U)
  end.

Notation "[[ T ]]" := (interpretation T).

Lemma inAllSAT : forall (A : term -> Prop) (n : nat),
    saturated_set A -> A {{n}}.
Proof.
  intros. apply Bot_is_lowest; try apply H. split.
  apply normal_form_SN. apply var_normal_form.
  exists hole. exists n. split. apply holeSN. simpl.
  apply rt_refl.
Qed.

Lemma sat_arrow : forall (A B : term -> Prop),
    saturated_set A -> saturated_set B ->
    saturated_set (ArrowInterp A B).
Proof.
  intros. split. intros. unfold ArrowInterp in H1.
  specialize (H1 ({{0}}) (inAllSAT A 0 H)).
  apply H0 in H1. apply SN_app1 in H1. apply H1.
  split; intros. unfold ArrowInterp; intros.
  destruct H0 as (_ & H3 & _).
  specialize (H3 (apli E u) n). simpl in H3. apply H3.
  apply appSNE. apply H1.
  apply H. apply H2.
  split; intros. unfold ArrowInterp; intros.
  unfold ArrowInterp in H1.
  specialize (H1 u0 H3). destruct H0 as (_ & _ & H0 & _).
  specialize (H0 (apli E u0)).
  simpl in H0. apply (H0 t u H1 H2).
  split; intros. unfold ArrowInterp; intros.
  unfold ArrowInterp in H2.
  specialize (H2 u0 H3). destruct H0 as (_ & _ & _ & H0 & _).
  specialize (H0 (apli E u0)).
  simpl in H0. apply (H0 t u H1 H2).
  split; intros. unfold ArrowInterp; intros.
  unfold ArrowInterp in H2.
  specialize (H2 u0 H3). destruct H0 as (_ & _ & _ & _ & H0 & _).
  specialize (H0 (apli E u0)).
  simpl in H0. apply (H0 t u H1 H2).
  split; intros. unfold ArrowInterp; intros.
  unfold ArrowInterp in H3.
  specialize (H3 u0 H4).
  destruct H0 as (_ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (apli E u0)).
  simpl in H0. apply (H0 t u v H1 H2 H3).
  split; intros. unfold ArrowInterp; intros.
  unfold ArrowInterp in H3.
  specialize (H3 u0 H4).
  destruct H0 as (_ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (apli E u0)). simpl in H0.
  apply (H0 t u v H1 H2 H3).
  split; intros. unfold ArrowInterp; intros.
  unfold ArrowInterp in H2.
  specialize (H2 u0 H3).
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (apli E u0)). simpl in H0. apply (H0 t u H1 H2).
  split; intros. unfold ArrowInterp; intros.
  unfold ArrowInterp in H2.
  specialize (H2 u0 H3).
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (apli E u0)). simpl in H0. apply (H0 t u H1 H2).
  split; intros. unfold ArrowInterp; intros.
  unfold ArrowInterp in H2.
  specialize (H2 u0 H3).
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (apli E u0)). simpl in H0. apply (H0 t u H1 H2).
  split; intros. unfold ArrowInterp; intros.
  unfold ArrowInterp in H3.
  specialize (H3 u0 H4).
  destruct H0 as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (apli E u0)). simpl in H0.
  apply (H0 t u v H1 H2 H3).
  unfold ArrowInterp; intros; unfold ArrowInterp in H1.
  specialize (H1 u H2).
  replace (E [ₑ lift k n t] @ₜ u) with
    ((apli E u) [ₑ lift k n t]).
  apply H0. simpl. apply H1. simpl. reflexivity.
Qed.

Lemma sat_prod : forall (A B : term -> Prop),
    saturated_set A -> saturated_set B ->
    saturated_set (TimesInterp A B).
Proof.
  intros. split; intros. unfold TimesInterp in H1.
  destruct H1. apply H in H1. apply SN_proj1 in H1. apply H1.
  split; intros. unfold TimesInterp. destruct H as (_ & H & _).
  destruct H0 as (_ & H0 & _).
  split. specialize (H (proj1 E) n). simpl in H. apply H.
  apply proj1SN. apply H1.
  specialize (H0 (proj2 E) n). simpl in H0. apply H0.
  apply proj2SN. apply H1.
  split; intros. unfold TimesInterp; unfold TimesInterp in H1.
  destruct H1.
  destruct H as (_ & _ & H & _). specialize (H (proj1 E) t u).
  simpl in H. apply H in H1; try apply H2.
  destruct H0 as (_ & _ & H0 & _).
  specialize (H0 (proj2 E) t u). simpl in H0.
  apply H0 in H3; try apply H2.
  split; try apply H1; apply H3.
  split; intros. unfold TimesInterp; unfold TimesInterp in H2.
  destruct H2.
  destruct H as (_ & _ & _ & H & _).
  specialize (H (proj1 E) t u).
  simpl in H. apply H in H2; try apply H1.
  destruct H0 as (_ & _ & _ & H0 & _).
  specialize (H0 (proj2 E) t u). simpl in H0.
  apply H0 in H3; try apply H1.
  split; try apply H2; apply H3.
  split; intros. unfold TimesInterp; unfold TimesInterp in H2.
  destruct H2.
  destruct H as (_ & _ & _ & _ & H & _).
  specialize (H (proj1 E) t u).
  simpl in H. apply H in H2; try apply H1.
  destruct H0 as (_ & _ & _ & _ & H0 & _).
  specialize (H0 (proj2 E) t u). simpl in H0.
  apply H0 in H3; try apply H1.
  split; try apply H2; apply H3.
  split; intros. unfold TimesInterp; unfold TimesInterp in H3.
  destruct H3.
  destruct H as (_ & _ & _ & _ & _ & H & _).
  specialize (H (proj1 E) t u v H1 H2).
  simpl in H. apply H in H3.
  destruct H0 as (_ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (proj2 E) t u v H1 H2). simpl in H0.
  apply H0 in H4.
  split; try apply H3; apply H4.
  split; intros. unfold TimesInterp; unfold TimesInterp in H3.
  destruct H3.
  destruct H as (_ & _ & _ & _ & _ & _ & H & _).
  specialize (H (proj1 E) t u v H1 H2).
  simpl in H. apply H in H3.
  destruct H0 as (_ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (proj2 E) t u v H1 H2). simpl in H0.
  apply H0 in H4.
  split; try apply H3; apply H4.
  split; intros. unfold TimesInterp; unfold TimesInterp in H2.
  destruct H2.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & H & _).
  specialize (H (proj1 E) t u H1).
  simpl in H. apply H in H2.
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (proj2 E) t u H1). simpl in H0. apply H0 in H3.
  split; try apply H2; apply H3.
  split; intros. unfold TimesInterp; unfold TimesInterp in H2.
  destruct H2.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H & _).
  specialize (H (proj1 E) t u H1).
  simpl in H. apply H in H2.
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (proj2 E) t u H1). simpl in H0. apply H0 in H3.
  split; try apply H2; apply H3.
  split; intros. unfold TimesInterp; unfold TimesInterp in H2.
  destruct H2.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
  specialize (H (proj1 E) t u H1).
  simpl in H. apply H in H2.
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (proj2 E) t u H1). simpl in H0. apply H0 in H3.
  split; try apply H2; apply H3.
  split; intros. unfold TimesInterp; unfold TimesInterp in H3.
  destruct H3.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
  specialize (H (proj1 E) t u v H1 H2). simpl in H.
  apply H in H3.
  destruct H0 as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
  specialize (H0 (proj2 E) t u v H1 H2). simpl in H0.
  apply H0 in H4.
  split; try apply H3; apply H4.
  unfold TimesInterp; unfold TimesInterp in H1; destruct H1.
  split. replace (π₁ (E [ₑ lift k n t])) with
    ((proj1 E) [ₑ lift k n t]); try (simpl; reflexivity).
  apply H. simpl; apply H1.
  replace (π₂ (E [ₑ lift k n t])) with
    ((proj2 E) [ₑ lift k n t]); try (simpl; reflexivity).
  apply H0. simpl; apply H2.
Qed.

Lemma sat_sum : forall (A B : term -> Prop),
    saturated_set A -> saturated_set B ->
    saturated_set (SumInterp A B).
Proof.
  intros. split. intros. unfold SumInterp in H1.
  specialize (H1 Bot_SAT ({{1}}) ({{1}}) Bot_is_SAT).
  assert (Bot_SAT (δ(0 ↦ {{1}} |0 ↦ {{1}}) t)). apply H1.
  intros. simpl. assert (saturated_set Bot_SAT);
    try apply Bot_is_SAT.
  destruct H3 as (_ & H3 & _). specialize (H3 hole 0 holeSN).
  simpl in H3. apply H3.
  intros. simpl. assert (saturated_set Bot_SAT);
    try apply Bot_is_SAT.
  destruct H3 as (_ & H3 & _). specialize (H3 hole 0 holeSN).
  simpl in H3. apply H3.
  apply Bot_is_SAT in H2. apply SN_delta3 in H2. apply H2.
  split; intros. unfold SumInterp; intros.
  assert (saturated_set C) as H5; try apply H2.
  destruct H2 as (_ & H2 & _). specialize (H2 (cases u v E) n).
  simpl in H2; apply H2.
  apply casesSN; try apply H1.
  specialize (H3 ({{0}}) (inAllSAT A 0 H)). apply H5 in H3.
  apply SN_subst in H3. apply H3.
  specialize (H4 ({{0}}) (inAllSAT B 0 H0)). apply H5 in H4.
  apply SN_subst in H4. apply H4.
  split; intros. unfold SumInterp. unfold SumInterp in H1.
  intros.
  specialize (H1 C u0 v H3 H4 H5).
  destruct H3 as (_ & _ & H3 & _).
  specialize (H3 (cases u0 v E) t u). simpl in H3.
  apply (H3 H1 H2).
  split; intros. unfold SumInterp. unfold SumInterp in H2.
  intros.
  specialize (H2 C u0 v H3 H4 H5).
  destruct H3 as (_ & _ & _ & H3 & _).
  specialize (H3 (cases u0 v E) t u). simpl in H3.
  apply (H3 H1 H2).
  split; intros. unfold SumInterp. unfold SumInterp in H2.
  intros.
  specialize (H2 C u0 v H3 H4 H5).
  destruct H3 as (_ & _ & _ & _ & H3 & _).
  specialize (H3 (cases u0 v E) t u). simpl in H3.
  apply (H3 H1 H2).
  split; intros. unfold SumInterp. unfold SumInterp in H3.
  intros.
  specialize (H3 C u0 v0 H4 H5 H6).
  destruct H4 as (_ & _ & _ & _ & _ & H4 & _).
  specialize (H4 (cases u0 v0 E) t u v). simpl in H3.
  apply (H4 H1 H2 H3).
  split; intros. unfold SumInterp. unfold SumInterp in H3.
  intros.
  specialize (H3 C u0 v0 H4 H5 H6).
  destruct H4 as (_ & _ & _ & _ & _ & _ & H4 & _).
  specialize (H4 (cases u0 v0 E) t u v). simpl in H3.
  apply (H4 H1 H2 H3).
  split; intros. unfold SumInterp. unfold SumInterp in H2.
  intros.
  specialize (H2 C u0 v H3 H4 H5).
  destruct H3 as (_ & _ & _ & _ & _ & _ & _ & H3 & _).
  specialize (H3 (cases u0 v E) t u). simpl in H3.
  apply (H3 H1 H2).
  split; intros. unfold SumInterp. unfold SumInterp in H2.
  intros.
  specialize (H2 C u0 v H3 H4 H5).
  destruct H3 as (_ & _ & _ & _ & _ & _ & _ & _ & H3 & _).
  specialize (H3 (cases u0 v E) t u). simpl in H3.
  apply (H3 H1 H2).
  split; intros. unfold SumInterp. unfold SumInterp in H2.
  intros.
  specialize (H2 C u0 v H3 H4 H5).
  destruct H3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H3 & _).
  specialize (H3 (cases u0 v E) t u). simpl in H3.
  apply (H3 H1 H2).
  split; intros. unfold SumInterp. unfold SumInterp in H3.
  intros.
  specialize (H3 C u0 v0 H4 H5 H6).
  destruct H4 as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H4 & _).
  specialize (H4 (cases u0 v0 E) t u v). simpl in H4.
  apply (H4 H1 H2 H3).
  unfold SumInterp; intros; unfold SumInterp in H1.
  specialize (H1 C u v H2 H3 H4).
  replace (delta u v (E [ₑ lift k n t])) with
    ((cases u v E) [ₑ lift k n t]);
    try (simpl; reflexivity).
  apply H2. simpl; apply H1.
Qed.

Lemma sat_bool : saturated_set BoolInterp.
Proof.
  split; intros. unfold BoolInterp in H.
  specialize (H Bot_SAT ({{0}}) ({{0}})
                Bot_is_SAT (inAllSAT Bot_SAT 0 Bot_is_SAT)
                (inAllSAT Bot_SAT 0 Bot_is_SAT)).
  apply Bot_is_SAT in H. apply SN_ite1 in H. apply H.
  split; intros. unfold BoolInterp; intros.
  destruct H0 as (H3 & H0 & _).
  specialize (H0 (ifel E u v) n). simpl in H0. apply H0.
  apply ifelSN. apply H. apply H3. apply H1.
  apply H3. apply H2.
  split; intros. unfold BoolInterp; unfold BoolInterp in H;
    intros.
  specialize (H C u0 v H1 H2 H3).
  destruct H1 as (_ & _ & H1 & _).
  specialize (H1 (ifel E u0 v) t u).
  simpl in H1. apply (H1 H H0).
  split; intros. unfold BoolInterp; unfold BoolInterp in H0;
    intros.
  specialize (H0 C u0 v H1 H2 H3).
  destruct H1 as (_ & _ & _ & H1 & _).
  specialize (H1 (ifel E u0 v) t u). simpl in H1.
  apply (H1 H H0).
  split; intros. unfold BoolInterp; unfold BoolInterp in H0;
    intros.
  specialize (H0 C u0 v H1 H2 H3).
  destruct H1 as (_ & _ & _ & _ & H1 & _).
  specialize (H1 (ifel E u0 v) t u). simpl in H1.
  apply (H1 H H0).
  split; intros. unfold BoolInterp; unfold BoolInterp in H1;
    intros.
  specialize (H1 C u0 v0 H2 H3 H4).
  destruct H2 as (_ & _ & _ & _ & _ & H2 & _).
  specialize (H2 (ifel E u0 v0) t u v). simpl in H2.
  apply (H2 H H0 H1).
  split; intros. unfold BoolInterp; unfold BoolInterp in H1;
    intros.
  specialize (H1 C u0 v0 H2 H3 H4).
  destruct H2 as (_ & _ & _ & _ & _ & _ & H2 & _).
  specialize (H2 (ifel E u0 v0) t u v). simpl in H2.
  apply (H2 H H0 H1).
  split; intros. unfold BoolInterp; unfold BoolInterp in H0;
    intros.
  specialize (H0 C u0 v H1 H2 H3).
  destruct H1 as (_ & _ & _ & _ & _ & _ & _ & H1 & _).
  specialize (H1 (ifel E u0 v) t u). simpl in H1.
  apply (H1 H H0).
  split; intros. unfold BoolInterp; unfold BoolInterp in H0;
    intros.
  specialize (H0 C u0 v H1 H2 H3).
  destruct H1 as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & _).
  specialize (H1 (ifel E u0 v) t u). simpl in H1.
  apply (H1 H H0).
  split; intros. unfold BoolInterp; unfold BoolInterp in H0;
    intros.
  specialize (H0 C u0 v H1 H2 H3).
  destruct H1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & _).
  specialize (H1 (ifel E u0 v) t u). simpl in H1.
  apply (H1 H H0).
  split; intros. unfold BoolInterp; unfold BoolInterp in H1;
    intros.
  specialize (H1 C u0 v0 H2 H3 H4).
  destruct H2 as
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H2 & _).
  specialize (H2 (ifel E u0 v0) t u v). simpl in H2.
  apply (H2 H H0 H1).
  unfold BoolInterp; intros; unfold BoolInterp in H.
  specialize (H C u v H0 H1 H2).
  replace (IfThenElse (E [ₑ lift k n t]) u v) with
    ((ifel E u v) [ₑ lift k n t]);
    try (simpl; reflexivity). apply H0; simpl; apply H.
Qed.

Lemma sat_unit : saturated_set UnitInterp.
Proof.
  apply Top_is_SAT.
Qed.

Lemma sat_void : saturated_set VoidInterp.
Proof.
  apply Bot_is_SAT.
Qed.

Lemma interp_sub_SAT : forall (T : type), saturated_set [[T]].
Proof.
  intro T. induction T; simpl.
  apply sat_unit. apply sat_nat. apply sat_bool.
  apply sat_unit. apply sat_void. apply sat_arrow.
  apply IHT1. apply IHT2.
  apply sat_prod. apply IHT1. apply IHT2. apply sat_sum.
  apply IHT1. apply IHT2.
Qed.
