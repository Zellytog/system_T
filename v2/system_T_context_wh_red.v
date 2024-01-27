Require Import system_T_first_def.
Require Import system_T_substi.
Require Import system_T_reduction.
Require Import system_T_normal_form_SN.
Require Import PeanoNat.
Require Import List.

(* *********************************************************** *)

(** II. The structure of SN *)

(** 6. Elimination context and weak head reduction.

In this file, we introduce the notion of elimination context,
   which can be seen as indicating a procedure of treatment to a
   result: it will be a succession of eliminators, e.g.
   applications, projections, delta eliminations etc. We then
   define the weak head reduction, which is a weakening of
   β-reduction where we only reduce redexes which are not below a
   constructor.*)

(** A. Elimination context.

Elimination contexts are defined by

E[ ] ::= [ ] | E[ ] t | π₁ E[ ] | π₂ E[ ] | δ(0 ↦ t |0 ↦ u) E[ ]
         | δ⊥ E[ ]
*)

Inductive Elim : Set :=
| hole : Elim
| apli : Elim -> term -> Elim
| proj1 : Elim -> Elim
| proj2 : Elim -> Elim
| cases : term -> term -> Elim -> Elim
| casebot : Elim -> Elim
| recel : term -> term -> Elim -> Elim
| ifel : Elim -> term -> term -> Elim.

(** The function fill defines the notation E[t] for a term t. *)

Fixpoint fill E t : term :=
  match E with
  | hole => t
  | apli E u => (fill E t) @ₜ u
  | proj1 E => π₁ (fill E t)
  | proj2 E => π₂ (fill E t)
  | cases u v E => δ(0 ↦ u |0 ↦ v) (fill E t)
  | casebot E => δb (fill E t)
  | recel u v E => Recₜ u v (fill E t)
  | ifel E u v => IfThenElse (fill E t) u v
  end.

Notation "E [ₑ t ]" := (fill E t) (at level 67).

Lemma ctx_compat : forall (E : Elim) (t u : term),
    t ⊳ u -> E [ₑ t] ⊳ E [ₑ u].
Proof.
  intros. induction E; simpl.
  - apply H.
  - apply β_app1. apply IHE.
  - apply β_proj1. apply IHE.
  - apply β_proj2. apply IHE.
  - apply β_delta3. apply IHE.
  - apply β_deltaNil. apply IHE.
  - apply β_rec3. apply IHE.
  - apply β_ite1. apply IHE.
Qed.

Lemma ctx_compat_star : forall (E : Elim) (t u : term),
    t ⊳* u -> E [ₑ t] ⊳* E [ₑ u].
Proof.
  intros. induction H. apply β_refl.
  apply (β_add _ _ _ IHrt_closure). apply ctx_compat. apply H0.
Qed.

Fixpoint composE E F : Elim :=
  match E with
  | hole => F
  | apli E' t => apli (composE E' F) t
  | proj1 E' => proj1 (composE E' F)
  | proj2 E' => proj2 (composE E' F)
  | cases t u E' => cases t u (composE E' F)
  | casebot E' => casebot (composE E' F)
  | recel t u E' => recel t u (composE E' F)
  | ifel E' t u => ifel (composE E' F) t u
  end.

Fixpoint liftE (k n : nat) (E : Elim) : Elim :=
  match E with
  | hole => hole
  | apli E' t => apli (liftE k n E') (lift k n t)
  | proj1 E' => proj1 (liftE k n E')
  | proj2 E' => proj2 (liftE k n E')
  | cases t u E' =>
      cases (lift (S k) n t) (lift (S k) n u) (liftE k n E')
  | casebot E' => casebot (liftE k n E')
  | recel t u E' =>
      recel (lift k n t) (lift k n u) (liftE k n E')
  | ifel E' t u => ifel (liftE k n E') (lift k n t) (lift k n u)
  end.

Notation "E ∘ₑ F" := (composE E F) (at level 67).

Lemma composE_assoc : forall (E F G : Elim),
    E ∘ₑ (F ∘ₑ G) = (E ∘ₑ F) ∘ₑ G.
Proof.
  induction E; intros; simpl; f_equal; apply IHE.
Qed.

Lemma induction_ext : forall (P : Elim -> Prop),
    P hole -> (forall (E : Elim) (t : term),
                  P E -> P (E ∘ₑ apli hole t)) ->
    (forall E : Elim, P E -> P (E ∘ₑ proj1 hole)) ->
    (forall E : Elim, P E -> P (E ∘ₑ proj2 hole)) ->
    (forall (E : Elim) (t u : term),
        P E -> P (E ∘ₑ cases t u hole)) ->
    (forall E : Elim, P E -> P (E ∘ₑ casebot hole)) ->
    (forall (E : Elim) (t u : term), P E ->
                                     P (E ∘ₑ recel t u hole)) ->
    (forall (E : Elim) (t u : term), P E ->
                                     P (E ∘ₑ ifel hole t u)) ->
    forall E : Elim, P E.
Proof.
  intros. induction E. apply H.
Admitted.

Lemma compose_fill : forall (E F : Elim) (t : term),
    E ∘ₑ F [ₑ t ] = E [ₑ F [ₑ t]].
Proof.
  induction E;simpl;intros;try reflexivity;
    try (f_equal;apply IHE).
Qed.

Lemma lift_fill : forall (k n : nat) (E : Elim) (t : term),
  (liftE k n E) [ₑ lift k n t] = lift k n (E [ₑ t]).
Proof.
  intros k n E; generalize k n; clear k n; induction E; intros;
    simpl; try reflexivity;
    try (f_equal; rewrite IHE; reflexivity).
Qed.

(** We define SNE for the contexts constructed with strongly
    normalizing terms, and then the notion of context reduction,
    which is just a reduction in the contained terms. We also
    introduce an inductive notion of SN for the context, with
    regard to ⊳ₑ.*)

Inductive SNE : Elim -> Prop :=
| holeSN : SNE hole
| appSNE : forall (E : Elim) (t : term),
    SNE E -> SN t -> SNE (apli E t)
| proj1SN : forall (E : Elim), SNE E -> SNE (proj1 E)
| proj2SN : forall (E : Elim), SNE E -> SNE (proj2 E)
| casesSN : forall (t u : term) (E : Elim),
    SN t -> SN u -> SNE E -> SNE (cases t u E)
| casebotSN : forall (E : Elim), SNE E -> SNE (casebot E)
| recelSN : forall (t u : term) (E : Elim),
    SN t -> SN u -> SNE E -> SNE (recel t u E)
| ifelSN : forall (E : Elim) (t u : term),
    SNE E -> SN t -> SN u -> SNE (ifel E t u).

Inductive βE : Elim -> Elim -> Prop :=
| appβE1 : forall (E F : Elim) (t : term),
    βE E F -> βE (apli E t) (apli F t)
| appβE2 : forall (E : Elim) (t u : term),
    t ⊳ u -> βE (apli E t) (apli E u)
| projβE1 : forall (E F : Elim),
    βE E F -> βE (proj1 E) (proj1 F)
| projβE2 : forall (E F : Elim),
    βE E F -> βE (proj2 E) (proj2 F)
| casesβE1 : forall (t u v : term) (E : Elim),
    t ⊳ u -> βE (cases t v E) (cases u v E)
| casesβE2 : forall (t u v : term) (E : Elim),
    u ⊳ v -> βE (cases t u E) (cases t v E)
| casesβE3 : forall (t u : term) (E F : Elim),
    βE E F -> βE (cases t u E) (cases t u F)
| casebotβE : forall (E F : Elim),
    βE E F -> βE (casebot E) (casebot F)
| recelβE1 : forall (t u v : term) (E : Elim),
    t ⊳ u -> βE (recel t v E) (recel u v E)
| recelβE2 : forall (t u v : term) (E : Elim),
    u ⊳ v -> βE (recel t u E) (recel t v E)
| recelβE3 : forall (t u : term) (E F : Elim),
    βE E F -> βE (recel t u E) (recel t u F)
| ifelβE1 : forall (t u : term) (E F : Elim),
    βE E F -> βE (ifel E t u) (ifel F t u)
| ifelβE2 : forall (t u v : term) (E : Elim),
    t ⊳ u -> βE (ifel E t v) (ifel E u v)
| ifelβE3 : forall (t u v : term) (E : Elim),
    u ⊳ v -> βE (ifel E t u) (ifel E t v).

Notation "E ⊳ₑ F" := (βE E F) (at level 68).

Inductive βE_star : Elim -> Elim -> Prop :=
| βE_refl : forall E : Elim, βE_star E E
| βE_add : forall E F G : Elim,
    βE_star E F -> F ⊳ₑ G -> βE_star E G.

Notation "E ⊳ₑ* F" := (βE_star E F) (at level 68).

Lemma SNE_stable_βE : forall (E F : Elim),
    SNE E -> E ⊳ₑ F -> SNE F.
Proof.
  intros. induction H0; inversion H.
  - apply appSNE. apply IHβE in H3. apply H3. apply H4.
  - apply appSNE. apply H3. apply (reduc_SN _ _ H4 H0).
  - apply IHβE in H2. apply proj1SN. apply H2.
  - apply IHβE in H2. apply proj2SN. apply H2.
  - apply casesSN. apply (reduc_SN _ _ H4 H0). apply H5.
    apply H6.
  - apply casesSN. apply H4. apply (reduc_SN _ _ H5 H0).
    apply H6.
  - apply IHβE in H6. apply casesSN. apply H4. apply H5.
    apply H6.
  - apply casebotSN. apply IHβE. apply H2.
  - apply recelSN. apply (reduc_SN _ _ H4 H0). apply H5.
    apply H6.
  - apply recelSN. apply H4. apply (reduc_SN _ _ H5 H0).
    apply H6.
  - apply IHβE in H6. apply recelSN. apply H4. apply H5.
    apply H6.
  - apply IHβE in H4. apply ifelSN. apply H4. apply H5. apply H6.
  - apply ifelSN. apply H4. apply (reduc_SN _ _ H5 H0). apply H6.
  - apply ifelSN. apply H4. apply H5. apply (reduc_SN _ _ H6 H0).
Qed.

Lemma reduc_SNE_star : forall (E F : Elim),
    SNE E -> E ⊳ₑ* F -> SNE F.
Proof.
  intros. induction H0. apply H. apply IHβE_star in H.
  apply (SNE_stable_βE _ _ H H1).
Qed.

Inductive induc_SNE : Elim -> Prop :=
| expansionE : forall (E : Elim),
    (forall (F : Elim), E ⊳ₑ F -> induc_SNE F) -> induc_SNE E.

Lemma equiv_SNE_induc : forall (E : Elim), SNE E <-> induc_SNE E.
Proof.
  intro; split; intro.
  - induction H.
    + split; intros. inversion H.
    + induction IHSNE. split; intros. inversion H3. apply H2.
      apply H7.
      apply (SNE_stable_βE _ _ H) in H7. apply H7. clear H1 H2.
Admitted.

Lemma βE_to_β : forall (E F : Elim) (t : term),
    E ⊳ₑ F -> E [ₑ t] ⊳ F [ₑ t].
Proof.
  intros. generalize t; clear t. induction H; simpl; intros.
  - apply β_app1. apply IHβE.
  - apply β_app2. apply H.
  - apply β_proj1. apply IHβE.
  - apply β_proj2. apply IHβE.
  - apply β_delta1. apply H.
  - apply β_delta2. apply H.
  - apply β_delta3. apply IHβE.
  - apply β_deltaNil. apply IHβE.
  - apply β_rec1. apply H.
  - apply β_rec2. apply H.
  - apply β_rec3. apply IHβE.
  - apply β_ite1. apply IHβE.
  - apply β_ite2. apply H.
  - apply β_ite3. apply H.
Qed.

Lemma βE_to_β_star : forall (E F : Elim) (t : term),
    E ⊳ₑ* F -> E [ₑ t] ⊳* F [ₑ t].
Proof.
  intros. induction H. apply β_refl.
  apply (β_add _ (F [ₑ t])); try apply IHβE_star.
  apply βE_to_β. apply H0.
Qed.

Lemma SNE_fill_SN_eq : forall (E : Elim) (t : term),
    SN t -> forall v, t = E [ₑ v] -> SN v.
Proof.
  induction E; try (intros; simpl in H0; rewrite <- H0; apply H);
    intros u H; induction H; intros; split; intros;
    simpl in H1; apply (ctx_compat E) in H2; simpl in H0.
  - apply (β_app1 _ _ t) in H2. rewrite <- H1 in H2.
    specialize (H0 _ H2 t2). apply H0. reflexivity.
  - apply β_proj1 in H2. rewrite <- H1 in H2.
    specialize (H0 _ H2 t2). apply H0. reflexivity.
  - apply β_proj2 in H2. rewrite <- H1 in H2.
    specialize (H0 _ H2 t2). apply H0. reflexivity.
  - apply (β_delta3 t t0 _ _) in H2. rewrite <- H1 in H2.
    specialize (H0 _ H2 t2). apply H0. reflexivity.
  - apply β_deltaNil in H2. rewrite <- H1 in H2.
    specialize (H0 _ H2 t2). apply H0. reflexivity.
  - apply (β_rec3 t t0) in H2. rewrite <- H1 in H2.
    specialize (H0 _ H2 t2). apply H0. reflexivity.
  - apply (β_ite1 _ _ t t0) in H2. rewrite <- H1 in H2.
    specialize (H0 _ H2 t2). apply H0. reflexivity.
Qed.

Lemma SNE_fill_SN : forall (E : Elim) (t : term),
    SN (E [ₑ t]) -> SN t.
Proof.
  intros. specialize (SNE_fill_SN_eq E (E [ₑ t]) H t). intro.
  apply H0. reflexivity.
Qed.

Lemma SN_SNE : forall (E : Elim) (t : term),
    SN (E [ₑ t]) ->  SNE E.
Proof.
  intros. induction E; simpl in H. apply holeSN.
  specialize (IHE (SN_app1 _ _ H)). apply SN_app2 in H.
  apply appSNE. apply IHE. apply H.
  specialize (IHE (SN_proj1 _ H)). apply proj1SN. apply IHE.
  specialize (IHE (SN_proj2 _ H)). apply proj2SN. apply IHE.
  specialize (IHE (SN_delta3 _ _ _ H)).
  specialize (SN_delta1 _ _ _ H); intro. apply SN_delta2 in H.
  apply casesSN. apply H0. apply H. apply IHE.
  apply -> SN_deltaNil in H. apply casebotSN. apply (IHE H).
  specialize (IHE (SN_rec3 _ _ _ H)).
  specialize (SN_rec1 _ _ _ H); intro. apply SN_rec2 in H.
  apply recelSN. apply H0. apply H. apply IHE.
  specialize (IHE (SN_ite1 _ _ _ H)).
  specialize (SN_ite2 _ _ _ H); intro. apply SN_ite3 in H.
  apply ifelSN. apply IHE. apply H0. apply H.
Qed.

(**
Lemma SNELiftSNE_eq : forall (k n : nat) (E : Elim), SNE E -> forall (F : Elim),
  E = liftE k n F -> SNE F.
Proof.
intros k n E H; generalize k n; clear k n; induction H; intros; simpl.
 - induction F; try inversion H. apply holeSN.
 - 
Admitted.
*)

Lemma SNE_lift_SNE : forall (k n : nat) (E : Elim),
    SNE E -> SNE (liftE k n E).
Proof.
  intros k n E H; generalize k n; clear k n; induction H; intros.
  - apply holeSN.
  - apply appSNE. apply IHSNE. apply SN_lift_direct. apply H0.
  - apply proj1SN. apply IHSNE.
  - apply proj2SN. apply IHSNE.
  - apply casesSN; try apply SN_lift. apply H. apply H0.
    apply IHSNE.
  - apply casebotSN. apply IHSNE.
  - apply recelSN; try apply SN_lift. apply H. apply H0.
    apply IHSNE.
  - apply ifelSN; try apply SN_lift. apply IHSNE. apply H0.
    apply H1.
Qed.

Lemma SNE_comp : forall (E F: Elim),
    SNE (E ∘ₑ F) <-> SNE E /\ SNE F.
Proof.
  intros. split; intro. + induction E; simpl in H.
  - split; try apply holeSN. apply H.
  - inversion H. apply IHE in H2. destruct H2.
    split; try apply H4. apply appSNE. apply H2.
    apply H3.
  - inversion H. apply IHE in H1. destruct H1.
    split; try apply H2. apply proj1SN. apply H1.
  - inversion H. apply IHE in H1. destruct H1.
    split; try apply H2. apply proj2SN. apply H1.
  - inversion H. apply IHE in H5. destruct H5.
    split; try apply H6. apply casesSN. apply H3.
    apply H4. apply H5.
  - inversion H. apply IHE in H1. destruct H1.
    split; try apply H2. apply casebotSN. apply H1.
  - inversion H. apply IHE in H5. destruct H5.
    split; try apply H6. apply recelSN. apply H3.
    apply H4. apply H5.
  - inversion H. apply IHE in H3. destruct H3.
    split; try apply H6. apply ifelSN. apply H3.
    apply H4. apply H5.
    + induction E; simpl; simpl in H; inversion H.
  - apply H.
  - inversion H0. apply appSNE. apply IHE.
    split; try apply H4; apply H1. apply H5.
  - inversion H0. apply proj1SN. apply IHE.
    split; try apply H3; apply H1.
  - inversion H0. apply proj2SN. apply IHE.
    split; try apply H3; apply H1.
  - inversion H0. apply casesSN. apply H5. apply H6. apply IHE.
    split; try apply H7; apply H1.
  - inversion H0. apply casebotSN. apply IHE.
    split; try apply H3; apply H1.
  - inversion H0. apply recelSN. apply H5. apply H6. apply IHE.
    split; try apply H7; apply H1.
  - inversion H0. apply ifelSN. apply IHE.
    split; try apply H5; apply H1. apply H6. apply H7.
Qed.

Lemma var_is_not_constr : forall (E : Elim) (n : nat),
    (forall u : term, λₜ u <> fill E {{n}}) /\
      (forall (u v : term), (⟨ u , v ⟩) <> fill E {{n}}) /\
      (forall u : term, κ₁ u <> fill E {{n}}) /\
      (forall (u : term), κ₂ u <> fill E {{n}})
    /\ zero <> fill E {{n}} /\
      (forall u : term, Sₜ u <> fill E {{n}}) /\
      Tt <> fill E {{n}} /\ Ff <> fill E {{n}}.
Proof.
  intro. induction E; simpl;
    repeat (split; try (intros; intro; inversion H));
    try inversion H.
Qed.

Lemma var_fill_is_hole : forall (E : Elim) (n : nat) (v : term),
    E [ₑ {{n}}] ⊳ v -> exists (E' : Elim),
      E ⊳ₑ E' /\ v = E' [ₑ {{n}}].
Proof.
  induction E; intros; simpl; simpl in H; try simpl in IHE.
  - simpl in H. inversion H.
  - inversion H. apply var_is_not_constr in H1. inversion H1.
    apply IHE in H3. destruct H3;
      destruct H3.
    exists (apli x t). split. apply appβE1. apply H3.
    simpl; rewrite H4; reflexivity.
    exists (apli E t3). split. apply appβE2. apply H3.
    simpl; reflexivity.
  - inversion H. apply var_is_not_constr in H1. inversion H1.
    apply IHE in H1. destruct H1;
      destruct H1.
    exists (proj1 x). split. apply projβE1. apply H1.
    simpl; rewrite H3; reflexivity.
  - inversion H. apply var_is_not_constr in H1. inversion H1.
    apply IHE in H1. destruct H1;
      destruct H1.
    exists (proj2 x). split. apply projβE2. apply H1.
    simpl; rewrite H3; reflexivity.
  - inversion H. apply var_is_not_constr in H3. inversion H3.
    apply var_is_not_constr in H3.
    inversion H3.
    exists (cases t2 t0 E). split. apply casesβE1. apply H4.
    simpl; reflexivity.
    exists (cases t t3 E). split. apply casesβE2. apply H4.
    simpl; reflexivity.
    apply IHE in H4. destruct H4; destruct H4.
    exists (cases t t0 x).
    split; try (apply casesβE3; apply H4).
    simpl; rewrite H5; reflexivity.
  - inversion H. apply IHE in H1. destruct H1; destruct H1.
    exists (casebot x).
    split; try (apply casebotβE; apply H1).
    simpl; rewrite H3; reflexivity.
  - inversion H. apply var_is_not_constr in H3. inversion H3.
    apply var_is_not_constr in H3.
    inversion H3.
    exists (recel t2 t0 E). split. apply recelβE1. apply H4.
    simpl; reflexivity.
    exists (recel t t3 E). split. apply recelβE2. apply H4.
    simpl; reflexivity.
    apply IHE in H4. destruct H4; destruct H4.
    exists (recel t t0 x).
    split; try (apply recelβE3; apply H4).
    simpl; rewrite H5; reflexivity.
  - inversion H. apply var_is_not_constr in H1. inversion H1.
    apply var_is_not_constr in H1.
    inversion H1.
    apply IHE in H4. destruct H4; destruct H4.
    exists (ifel x t t0).
    split; try (apply ifelβE1; apply H4).
    simpl; rewrite H5; reflexivity.
    exists (ifel E t3 t0). split; try (apply ifelβE2; apply H4).
    simpl; reflexivity.
    exists (ifel E t t4). split; try (apply ifelβE3; apply H4).
    simpl; reflexivity.
Qed.

Lemma SNE_var_SN : forall (E : Elim) (n : nat),
    SNE E -> SN (E [ₑ {{n}}]).
Proof.
  intros. apply equiv_SNE_induc in H. induction H.
  split; intros. apply var_fill_is_hole in H1. destruct H1.
  destruct H1. rewrite H2. apply H0. apply H1.
Qed.

(** B. Weak head reduction.

The weak head reduction is a restriction of the β-reduction:
    instead of taking a compatible relation containing the
    standard reductions, we only close the relation under
    eliminators, so for example t ⊳ₕ t' gives t @ₜ u ⊳ₕ t' @ₜ u,
    but not λₜ t ⊳ₕ λₜ t'.*)

Inductive red_0 : rewrite :=
| to_0 : forall (t u : term), red_0 (λₜ t @ₜ u) ({0 ~> u} t)
| proj1_0 : forall (t u : term), red_0 (π₁ (⟨ t , u ⟩)) t
| proj2_0 : forall (t u : term), red_0 (π₂ (⟨ t , u ⟩)) u
| inj1_0 : forall (t u v : term),
    red_0 (delta t u (κ₁ v)) ({0 ~> v} t)
| inj2_0 : forall (t u v : term),
    red_0 (delta t u (κ₂ v)) ({0 ~> v} u)
| rec1_0 : forall (t u : term), red_0 (Recₜ t u zero) t
| rec2_0 : forall (t u v : term),
    red_0 (Recₜ t u (Sₜ v)) (u @ₜ v @ₜ (Recₜ t u v))
| Tt_0 : forall (t u : term), red_0 (IfThenElse Tt t u) t
| Ff_0 : forall (t u : term), red_0 (IfThenElse Ff t u) u.

Inductive wh_ind : rewrite :=
| wh_to : forall (t u : term), wh_ind (λₜ t @ₜ u) ({0 ~> u} t)
| wh_proj1 : forall (t u : term), wh_ind (π₁ (⟨ t , u ⟩)) t
| wh_proj2 : forall (t u : term), wh_ind (π₂ (⟨ t , u ⟩)) u
| wh_inj1 : forall (t u v : term),
    wh_ind (delta t u (κ₁ v)) ({0 ~> v} t)
| wh_inj2 : forall (t u v : term),
    wh_ind (delta t u (κ₂ v)) ({0 ~> v} u)
| wh_rec1 : forall (t u : term), wh_ind (Recₜ t u zero) t
| wh_rec2 : forall (t u v : term),
    wh_ind (Recₜ t u (Sₜ v)) (u @ₜ v @ₜ (Recₜ t u v))
| wh_Tt : forall (t u : term), wh_ind (IfThenElse Tt t u) t
| wh_Ff : forall (t u : term), wh_ind (IfThenElse Ff t u) u
| wh_app : forall (t u v : term),
    wh_ind t u -> wh_ind (t @ₜ v) (u @ₜ v)
| wh_pi1 : forall (t u : term),
    wh_ind t u -> wh_ind (π₁ t) (π₁ u)
| wh_pi2 : forall (t u : term),
    wh_ind t u -> wh_ind (π₂ t) (π₂ u)
| wh_delta : forall (t u v w : term),
    wh_ind t u -> wh_ind (delta v w t) (delta v w u)
| wh_bot : forall (t u : term),
    wh_ind t u -> wh_ind (δb t) (δb u)
| wh_rec : forall (t u v w : term),
    wh_ind t u -> wh_ind (Recₜ v w t) (Recₜ v w u)
| wh_ite : forall (t u v w : term),
    wh_ind t u -> wh_ind (IfThenElse t v w) (IfThenElse u v w).

Notation "t ⊳₀ u" := (red_0 t u) (at level 68).
Notation "t ⊳ₕ u" := (wh_ind t u) (at level 68).

Lemma red_0_wh : forall (t u : term), t ⊳₀ u -> t ⊳ₕ u.
Proof.
  intros. induction H; constructor.
Qed.

Lemma equiv_wh_ind : forall (t u : term),
    t ⊳ₕ u <-> exists (E : Elim) (t' u' : term),
      t = E [ₑ t'] /\ u = E [ₑ u'] /\ t' ⊳₀ u'.
Proof.
  intros. split; intro.
  + induction H; simpl.
  - exists hole. exists (λₜ t @ₜ u). exists ({0 ~> u} t). simpl.
    split; try reflexivity; split; try reflexivity. apply to_0.
  - exists hole. exists (π₁ (⟨ t , u⟩)). exists t. simpl.
    split; try reflexivity; split; try reflexivity.
    apply proj1_0.
  - exists hole. exists (π₂ (⟨ t , u⟩)). exists u. simpl.
    split; try reflexivity; split; try reflexivity.
    apply proj2_0.
  - exists hole. exists (delta t u (κ₁ v)). exists ({0 ~> v} t).
    simpl. split; try reflexivity;
      split; try reflexivity. apply inj1_0.
  - exists hole. exists (delta t u (κ₂ v)). exists ({0 ~> v} u).
    simpl. split; try reflexivity;
      split; try reflexivity. apply inj2_0.
  - exists hole. exists (Recₜ t u zero). exists t. simpl.
    split; try reflexivity; split; try reflexivity. apply rec1_0.
  - exists hole. exists (Recₜ t u (Sₜ v)).
    exists (u @ₜ v @ₜ (Recₜ t u v)). simpl. split;
      try reflexivity; split; try reflexivity. apply rec2_0.
  - exists hole. exists (IfThenElse Tt t u). exists t. simpl.
    split; try reflexivity; split; try reflexivity. apply Tt_0.
  - exists hole. exists (IfThenElse Ff t u). exists u. simpl.
    split; try reflexivity; split; try reflexivity. apply Ff_0.
  - destruct IHwh_ind. destruct H0; destruct H0.
    exists (apli x v). exists x0. exists x1. simpl.
    split; try (f_equal; apply H0).
    split; try (f_equal; apply H0).
  - destruct IHwh_ind. destruct H0; destruct H0.
    exists (proj1 x). exists x0. exists x1. simpl.
    split; try split; f_equal; apply H0.
  - destruct IHwh_ind. destruct H0; destruct H0.
    exists (proj2 x). exists x0. exists x1. simpl.
    split; try split; f_equal; apply H0.
  - destruct IHwh_ind. destruct H0; destruct H0.
    exists (cases v w x). exists x0. exists x1. simpl.
    split; try split; f_equal; apply H0.
  - destruct IHwh_ind. destruct H0; destruct H0.
    exists (casebot x). exists x0. exists x1. simpl.
    split; try split; f_equal; apply H0.
  - destruct IHwh_ind. destruct H0; destruct H0.
    exists (recel v w x). exists x0. exists x1. simpl.
    split; try split; f_equal; apply H0.
  - destruct IHwh_ind. destruct H0; destruct H0.
    exists (ifel x v w). exists x0. exists x1. simpl.
    split; try split; f_equal; apply H0.
    + destruct H. destruct H. destruct H.
      generalize t u x0 x1 H; clear t u x0 x1 H.
      induction x; simpl; intros; destruct H; destruct H0;
        rewrite H; rewrite H0.
  - apply red_0_wh. apply H1.
  - apply wh_app. specialize (IHx (x [ₑ x0]) (x [ₑ x1]) x0 x1).
    apply IHx. split; try split;
      try reflexivity; apply H1.
  - apply wh_pi1. specialize (IHx (x [ₑ x0]) (x [ₑ x1]) x0 x1).
    apply IHx. split; try split;
      try reflexivity; apply H1.
  - apply wh_pi2. specialize (IHx (x [ₑ x0]) (x [ₑ x1]) x0 x1).
    apply IHx. split; try split;
      try reflexivity; apply H1.
  - apply wh_delta. specialize (IHx (x [ₑ x0]) (x [ₑ x1]) x0 x1).
    apply IHx. split; try split;
      try reflexivity; apply H1.
  - apply wh_bot. specialize (IHx (x [ₑ x0]) (x [ₑ x1]) x0 x1).
    apply IHx. split; try split;
      try reflexivity; apply H1.
  - apply wh_rec. specialize (IHx (x [ₑ x0]) (x [ₑ x1]) x0 x1).
    apply IHx. split; try split;
      try reflexivity; apply H1.
  - apply wh_ite. specialize (IHx (x [ₑ x0]) (x [ₑ x1]) x0 x1).
    apply IHx. split; try split;
      try reflexivity; apply H1.
Qed.

Lemma weak_head_is_red : forall (t u : term), t ⊳ₕ u -> t ⊳ u.
Proof.
  intros. induction H; try apply ctx_compat.
  - apply β_to.
  - apply β_times1.
  - apply β_times2.
  - apply β_plus1.
  - apply β_plus2.
  - apply β_NZ.
  - apply β_NS.
  - apply β_BT.
  - apply β_BF.
  - apply β_app1. apply IHwh_ind.
  - apply β_proj1. apply IHwh_ind.
  - apply β_proj2. apply IHwh_ind.
  - apply β_delta3. apply IHwh_ind.
  - apply β_deltaNil. apply IHwh_ind.
  - apply β_rec3. apply IHwh_ind.
  - apply β_ite1. apply IHwh_ind.
Qed.

Notation "t ⊳ₕ* u" := (wh_ind >* t u) (at level 68).

Lemma wh_star_wh : forall (t u : term), t ⊳ₕ u -> t ⊳ₕ* u.
Proof.
  intros. apply (rt_add _ _ _ _ (rt_refl _ _) H).
Qed.

Lemma wh_star_β_star : forall (t u : term), t ⊳ₕ* u -> t ⊳* u.
Proof.
  intros. induction H. apply β_refl. apply (β_add t u v).
  apply IHrt_closure. apply weak_head_is_red. apply H0.
Qed.

Lemma wh_trans : forall (t u v : term),
    t ⊳ₕ* u -> u ⊳ₕ* v -> t ⊳ₕ* v.
Proof.
  intros. induction H0. apply H.
  apply (rt_add _ _ _ _ (IHrt_closure H) H1).
Qed.

Lemma wh_compat : forall (E : Elim) (t u : term),
    t ⊳ₕ u -> E [ₑ t] ⊳ₕ E [ₑ u].
Proof.
  induction E; intros; simpl. apply H. apply wh_app. apply IHE.
  apply H. apply wh_pi1. apply IHE.
  apply H. apply wh_pi2. apply IHE. apply H. apply wh_delta.
  apply IHE. apply H. apply wh_bot.
  apply IHE. apply H. apply wh_rec. apply IHE. apply H.
  apply wh_ite. apply IHE. apply H.
Qed.

Lemma wh_star_compat : forall (E : Elim) (t u : term),
    t ⊳ₕ* u -> E[ₑ t] ⊳ₕ* E[ₑ u].
Proof.
  intros. induction H. apply rt_refl.
  apply (rt_add _ _ _ _ IHrt_closure). apply wh_compat. apply H0.
Qed.

Lemma wh_lift : forall (k n : nat) (t u : term),
    t ⊳ₕ u -> lift k n t ⊳ₕ lift k n u.
Proof.
  intros k n t u H; generalize k n; clear k n;
    induction H; intros; simpl; try rewrite lift_subst_0_r;
    try constructor; try apply IHwh_ind.
Qed.

Lemma wh_star_lift : forall (k n : nat) (t u : term),
    t ⊳ₕ* u -> lift k n t ⊳ₕ* lift k n u.
Proof.
  intros. induction H. apply rt_refl.
  apply (rt_add _ _ _ _ IHrt_closure). apply wh_lift. apply H0.
Qed.

Lemma elim_wh_decomp : forall (E F : Elim) (t u : term),
    E [ₑ t] ⊳ₕ F [ₑ u] -> exists E' : Elim,
      E = F ∘ₑ E' /\ E' [ₑ t] ⊳ₕ u.
Proof.
  intros E F; generalize E; clear E; induction F; intros;
    simpl; simpl in H.
  - exists E. split; try reflexivity. apply H.
  - assert (exists E' : Elim, E = apli E' t). induction E. 
Admitted.

Lemma elim_wh_decomp_star_eq : forall (t u : term),
    t ⊳ₕ* u -> forall (E F : Elim) (t' u' : term),
      t = E [ₑ t'] -> u = F [ₑ u'] ->
      exists E' F' : Elim, E' [ₑ t'] ⊳ₕ* u' /\
                             E = F' ∘ₑ E' /\
                             F ⊳ₑ* F'.
Proof.
intros t u H; induction H; intros.
Admitted.

Lemma elim_wh_decomp_star : forall (E F : Elim) (t u : term),
    E [ₑ t] ⊳ₕ* F [ₑ u] ->
    exists E' F' : Elim, E = F' ∘ₑ E' /\ E' [ₑ t] ⊳ₕ* u.
Proof.
Admitted.

Lemma elim_to_var_lift : forall (E : Elim) (t : term)
                                (k m n : nat),
    E [ₑ t] ⊳ₕ* {{n}} -> E [ₑ(lift k m t)] ⊳ₕ* lift k m {{n}}.
Proof.
Admitted.

Lemma elim_to_var_ctx_lift :
  forall (E F : Elim) (t : term) (k m n : nat),
    E [ₑ t] ⊳ₕ* F [ₑ{{n}}] ->
    exists (F : Elim) (n' : nat),
      E [ₑ(lift k m t)] ⊳ₕ* F [ₑ{{n'}}].
Proof.
  intros.
  specialize (elim_wh_decomp_star E F t ({{n}}) H); intro.
  destruct H0; destruct H0.
  destruct H0. exists x0. exists (if n <? k then n else m + n).
  replace ({{if n <? k then n else m + n}}) with
    (lift k m {{n}});
    try (simpl; case (n <? k); reflexivity). rewrite H0.
  rewrite compose_fill. apply wh_star_compat.
  apply elim_to_var_lift. apply H1.
Qed.
