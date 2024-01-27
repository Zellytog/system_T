Require Import system_T_first_def.
Require Import PeanoNat.
Require Import List.
Require Import Lt.

(* *********************************************************** *)

(** I. First definitions *)

(** 2. Substitutions.

This file contains the definition of substitution and
     simultaneous substitutions, along with the useful results
     about it and the notion of maximal indexes of a term. *)

(** A. Substitution.

The function subst is the obvious way to define t[u/x] with De
    Bruijn indexes.*)

Fixpoint subst (k : nat) (u : term) (t : term) : term :=
  match t with
  | var i => if i =? k then u else
               (if i <? k then {{ i }} else {{ i - 1 }})
  | λₜ t1 => λₜ (subst (1 + k) (lift 0 1 u) t1)
  | t1 @ₜ t2 => (subst k u t1) @ₜ (subst k u t2)
  | zero => zero
  | Sₜ t1 => Sₜ (subst k u t1)
  | Recₜ x f p => Recₜ (subst k u x) (subst k u f) (subst k u p)
  | Tt => Tt
  | Ff => Ff
  | IfThenElse t1 t2 t3 =>
      IfThenElse (subst k u t1) (subst k u t2) (subst k u t3)
  | ⟨ t1 , t2 ⟩ => ⟨ (subst k u t1) , (subst k u t2) ⟩
  | π₁ t1 => π₁ (subst k u t1)
  | π₂ t2 => π₂ (subst k u t2)
  | star => star
  | κ₁ t1 => κ₁ (subst k u t1)
  | κ₂ t2 => κ₂ (subst k u t2)
  | delta t1 t2 t3 =>
      delta (subst (1 + k) (lift 0 1 u) t1)
        (subst (1 + k) (lift 0 1 u) t2) (subst k u t3)
  | δb t1 => δb (subst k u t1)
  end.

Notation "{ k ~> u } t" := (subst k u t) (at level 67).

(** We give here the essential lemmas about substitution. *)

Lemma lift_subst_low : forall (t u : term) (n k p : nat),
    p <= k ->
    lift k n ({p ~> u} t) = {p ~> lift k n u} (lift (1 + k) n t).
Proof.
  induction t; intros; simpl;
    try (f_equal; try apply IHt; try apply IHt1; try apply IHt2;
         try apply IHt3; apply H); 
    try reflexivity.
  - case (n =? p) eqn : H0. case (n <? S k) eqn : H1.
    unfold subst. rewrite H0. reflexivity.
    unfold subst. case (n0 + n =? p) eqn : H2. reflexivity.
    case (n0 + n <? p) eqn : H3. apply Nat.eqb_eq in H0.
    rewrite H0 in H3. apply Nat.ltb_lt in H3.
    replace p with (0 + p) in H3; try apply Nat.add_0_l.
    replace (n0 + (0 + p)) with (n0 + p) in H3; try reflexivity.
    apply Nat.add_lt_mono_r in H3. inversion H3.
    apply Nat.ltb_ge in H1. apply Nat.ltb_ge in H3.
    apply Nat.eqb_eq in H0. rewrite H0 in H1. exfalso.
    apply (Nat.le_trans _ _ _ H1) in H.
    apply Nat.nle_succ_diag_l in H. apply H.
    case (n <? p) eqn : H1. apply Nat.ltb_lt in H1.
    specialize (Nat.lt_le_trans _ _ _ H1 H); intro.
    assert (n < k); try apply H2.
    apply Nat.lt_lt_succ_r in H2. apply Nat.ltb_lt in H2.
    rewrite H2. simpl.
    rewrite H0. apply Nat.ltb_lt in H1. rewrite H1.
    apply Nat.ltb_lt in H3. rewrite H3. reflexivity.
    case (n - 1 <? k) eqn : H2. simpl. rewrite H2.
    apply Nat.ltb_lt in H2. rewrite Nat.sub_1_r in H2.
    specialize (Nat.lt_pred_lt_succ _ _ H2); intro.
    apply Nat.ltb_lt in H3. rewrite H3.
    simpl. rewrite H0. rewrite H1. reflexivity.
    apply Nat.ltb_ge in H1. apply Nat.eqb_neq in H0.
    simpl. rewrite H2. apply Nat.ltb_ge in H2.
    specialize (le_n_S _ _ H2); intro.
    assert (p < n). apply Nat.lt_eq_cases in H1.
    destruct H1. apply H1. symmetry in H1. apply H0 in H1.
    inversion H1. rewrite Nat.sub_1_r in H3.
    rewrite (Nat.lt_succ_pred p n) in H3; try apply H4.
    apply Nat.ltb_ge in H3. rewrite H3. simpl.
    assert (p < n) as H6; try apply H4.
    apply (Nat.lt_lt_add_l _ _ n0) in H4.
    specialize (Nat.lt_neq _ _ H4); intro.
    apply Nat.neq_sym in H5.
    apply Nat.eqb_neq in H5. rewrite H5.
    apply Nat.lt_le_incl in H4. apply Nat.ltb_ge in H4.
    rewrite H4. f_equal. case n eqn : H7. inversion H6. simpl.
    rewrite Nat.sub_0_r.
    replace (n0 + S n1 - 1) with (S n1 + n0 - 1). simpl.
    rewrite Nat.sub_0_r. apply Nat.add_comm.
    rewrite Nat.add_comm. reflexivity.
  - f_equal. rewrite lift_comm_0. apply IHt.
    apply le_n_S; apply H.
  - f_equal; try (apply IHt3; apply H);
      try rewrite lift_comm_0; try apply IHt1;
      try apply IHt2;
      try apply le_n_S; try apply H;
      apply (Nat.le_lt_trans _ p _ (Nat.le_0_l _) H).
Qed.

Corollary lift_subst_0_r : forall (t u : term) (n k : nat),
  lift k n ({0 ~> u} t) = ({0 ~> lift k n u} (lift (S k) n t)).
Proof.
intros. apply lift_subst_low. apply Nat.le_0_l.
Qed.

Lemma lift_subst_high : forall (t u : term) (n k p : nat),
    k <= p ->
    lift k n ({p ~> u} t) = {n + p ~> lift k n u} (lift k n t).
Proof.
  induction t; intros; simpl; try reflexivity;
    try (try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
         try rewrite IHt3; try reflexivity;
         apply H).
  - case (n =? p) eqn : H0. apply Nat.eqb_eq in H0.
    rewrite <- H0 in H.
    apply Nat.ltb_ge in H. rewrite H. simpl.
    apply (Nat.add_cancel_l _ _ n0) in H0.
    apply Nat.eqb_eq in H0. rewrite H0. reflexivity.
    case (n <? p) eqn : H1. case (n <? k) eqn : H2. simpl.
    rewrite H2. apply Nat.ltb_lt in H1.
    specialize (Nat.lt_lt_add_l _ _ n0 H1); intro.
    specialize (Nat.lt_neq _ _ H3); intro.
    apply Nat.eqb_neq in H4. rewrite H4. apply Nat.ltb_lt in H3.
    rewrite H3. reflexivity.
    simpl. rewrite H2. apply Nat.ltb_lt in H1.
    (*specialize (Plus.plus_lt_compat_l _ _ n0 H1); intro.*)
    specialize (Nat.add_lt_mono_l n p n0); intro.
    apply H3 in H1.
    specialize (Nat.lt_neq _ _ H1); intro.
    apply Nat.eqb_neq in H4; rewrite H4.
    apply Nat.ltb_lt in H1; rewrite H1. reflexivity.
    apply Nat.ltb_ge in H1.
    specialize (Nat.le_trans _ _ _ H H1); intro.
    apply Nat.ltb_ge in H2; rewrite H2.
    simpl. assert (p <= n) as H4; try apply H1.
    apply (Nat.add_le_mono_l _ _ n0) in H1.
    apply Nat.ltb_ge in H1. rewrite H1.
    apply Nat.eqb_neq in H0. assert (n0 + n <> n0 + p).
    intro. apply Nat.add_cancel_l in H3.
    apply H0. apply H3.
    apply Nat.eqb_neq in H3; rewrite H3.
    assert (p < n). apply Nat.lt_eq_cases in H4. destruct H4.
    apply H4. symmetry in H4. apply H0 in H4.
    inversion H4. specialize (Nat.le_lt_trans _ _ _ H H5); intro.
    apply Nat.le_succ_l in H6.
    apply Nat.le_succ_le_pred in H6.
    rewrite <- Nat.sub_1_r in H6. apply Nat.ltb_ge in H6.
    rewrite H6.
    f_equal. case n eqn : H7. inversion H5. simpl.
    rewrite Nat.sub_0_r.
    replace (n0 + S n1) with (S n1 + n0). simpl.
    rewrite Nat.sub_0_r. apply Nat.add_comm.
    rewrite Nat.add_comm. reflexivity.
  - f_equal. rewrite IHt; try (apply le_n_S; apply H). f_equal.
    rewrite Nat.add_comm.
    simpl. f_equal. rewrite Nat.add_comm. reflexivity.
    rewrite lift_comm_0. reflexivity.
  - f_equal; try rewrite IHt1; try rewrite IHt2;
      try rewrite IHt3; try (apply le_n_S; apply H);
      try apply H; try f_equal;
      try (rewrite Nat.add_comm; simpl; f_equal;
           rewrite Nat.add_comm; reflexivity);
      try (rewrite lift_comm_0; reflexivity).
Qed.

Corollary lift_subst_0_l : forall (t u : term) (n k : nat),
  lift 0 n ({k ~> u} t) = {n + k ~> lift 0 n u} (lift 0 n t).
Proof.
  intros. apply lift_subst_high. apply Nat.le_0_l.
Qed.

Lemma subst_lift_neutral : forall (t u : term) (k : nat),
    t = {k ~> u} (lift k 1 t).
Proof.
  induction t; intros; simpl; try f_equal; try apply IHt;
    try apply IHt1; try apply IHt2;
    try apply IHt3;
    try reflexivity.
  case (n <? k) eqn : H; unfold subst. rewrite H.
  apply Nat.ltb_lt in H. apply Nat.lt_neq in H.
  apply Nat.eqb_neq in H. rewrite H. reflexivity.
  replace (S n - 1) with n. apply Nat.ltb_ge in H.
  apply Nat.lt_succ_r in H. assert (k <> S n);
    try (apply Nat.lt_neq; apply H).
  apply Nat.neq_sym in H0. apply Nat.eqb_neq in H0.
  rewrite H0. apply Nat.lt_le_incl in H.
  apply Nat.ltb_ge in H. rewrite H. reflexivity.
  simpl. symmetry. apply Nat.sub_0_r.
Qed.

Lemma substi_comm_low : forall (t u v : term) (n k : nat),
    k <= n ->
    {n ~> u} ({k ~> v} t) =
                {k ~> ({n ~> u} v)} ({S n ~> lift k 1 u} t).
Proof.
  induction t; intros; simpl; try reflexivity;
    try (f_equal; try rewrite IHt; try rewrite IHt1;
         try rewrite IHt2; try rewrite IHt3; try reflexivity;
         apply H).
  - case (n =? k) eqn : H0. apply Nat.eqb_eq in H0. rewrite H0.
    apply Nat.lt_succ_r in H.
    apply Nat.ltb_lt in H. rewrite H. apply Nat.ltb_lt in H.
    apply Nat.lt_neq in H.
    apply Nat.eqb_neq in H; rewrite H. simpl.
    assert (k = k); try reflexivity.
    apply Nat.eqb_eq in H1. rewrite H1. reflexivity.
    case (n <? k) eqn : H1. apply Nat.ltb_lt in H1.
    specialize (Nat.lt_le_trans _ _ _ H1 H); intro.
    specialize (Nat.lt_trans _ _ _ H2 (Nat.lt_succ_diag_r _));
      intro.
    specialize (Nat.lt_neq _ _ H3); intro.
    apply Nat.ltb_lt in H3. apply Nat.eqb_neq in H4.
    rewrite H3; rewrite H4. apply Nat.ltb_lt in H1. simpl.
    rewrite H0; rewrite H1.
    specialize (Nat.lt_neq _ _ H2); intro.
    apply Nat.ltb_lt in H2; apply Nat.eqb_neq in H5.
    rewrite H2; rewrite H5. reflexivity.
    case (n - 1 <? n0) eqn : H2.
    assert (n < S n0).  apply Nat.ltb_lt in H2.
    rewrite Nat.sub_1_r in H2.
    apply Nat.lt_pred_lt_succ in H2. apply H2.
    specialize (Nat.lt_neq _ _ H3); intro.
    apply Nat.ltb_lt in H3; rewrite H3.
    apply Nat.eqb_neq in H4; rewrite H4.
    simpl. rewrite H2. rewrite H0. rewrite H1.
    apply Nat.ltb_lt in H2. apply Nat.lt_neq in H2.
    apply Nat.eqb_neq in H2. rewrite H2. reflexivity.
    case (n =? S n0) eqn : H3. rewrite <- subst_lift_neutral.
    apply Nat.eqb_eq in H3.
    apply (f_equal Nat.pred) in H3. rewrite Nat.pred_succ in H3.
    rewrite <- Nat.sub_1_r in H3.
    apply Nat.eqb_eq in H3. simpl. rewrite H2; rewrite H3.
    reflexivity.
    simpl. rewrite H2. assert (n - 1 <> n0). intro.
    case n eqn : H5. simpl in H4.
    apply Nat.ltb_ge in H1. apply Nat.eqb_neq in H0.
    rewrite <- H4 in H. inversion H.
    symmetry in H6. apply H0. apply H6. simpl in H4.
    rewrite Nat.sub_0_r in H4.
    apply (f_equal S) in H4. apply Nat.eqb_neq in H3.
    apply H3 in H4. apply H4.
    assert (n0 < n - 1). apply Nat.ltb_ge in H2.
    apply Nat.lt_eq_cases in H2. destruct H2. apply H2.
    symmetry in H2. apply H4 in H2. inversion H2.
    assert (S n0 <= n). rewrite Nat.sub_1_r in H5.
    apply Nat.lt_pred_lt in H5.
    apply Nat.le_succ_l in H5. apply H5.
    apply Nat.ltb_ge in H6; rewrite H6.
    specialize (Nat.lt_neq _ _ H5); intro.
    apply Nat.neq_sym in H7.
    apply Nat.eqb_neq in H7; rewrite H7.
    apply (Nat.le_lt_trans _ _ _ H) in H5.
    specialize (Nat.lt_neq _ _ H5); intro.
    apply Nat.neq_sym in H8. apply Nat.eqb_neq in H8.
    apply Nat.lt_le_incl in H5. apply Nat.ltb_ge in H5. simpl.
    rewrite H5; rewrite H8. reflexivity.
  - f_equal. rewrite IHt. 2 :{ apply le_n_S. apply H. }
                        rewrite lift_comm_0. f_equal.
    rewrite lift_subst_0_l. reflexivity.
  - f_equal; try (rewrite IHt1; try (apply le_n_S; apply H);
                  rewrite lift_comm_0; f_equal;
                  rewrite lift_subst_0_l; reflexivity);
      try (rewrite IHt2; try (apply le_n_S; apply H);
           rewrite lift_comm_0; f_equal;
           rewrite lift_subst_0_l; reflexivity).
    rewrite IHt3; try apply H. reflexivity.
Qed.

Corollary substi_comm_0 : forall (t u v : term) (n : nat),
    {n ~> u} ({0 ~> v} t) =
      {0 ~> ({n ~> u} v)} ({S n ~> lift 0 1 u} t).
Proof.
  intros. apply substi_comm_low. apply Nat.le_0_l.
Qed.

(** B. Simultaneous substitution.

The simultaneous substitution takes a list of terms and
    substitutes all the terms in the list instead of doing it
    term by term, the result is different between t[u/x₀][v/x₁]
    and t[u,v/x₀,x₁] because in the first, the possible free
    variables of u can be replaced by v. However, if we lift u,
    we have an equality, as the lemmas will prove. This amounts
    to considering that each uᵢ have distinct free variables one
    to another. 

We will call permutation a list of term, acting as a partial
   function from the set of variables to terms. *)

Definition perm := list term.

(** The function lift_perm is used to make the weakening
    mentioned before, when we need to lift the whole list
    instead of the sole term.*)

Fixpoint lift_perm (k n : nat) (σ : perm) :=
  match σ with
  | nil => nil
  | x :: xs => lift k n x :: lift_perm k n xs
  end.

Lemma lift_perm_length : forall (σ : perm) (k n : nat),
    length σ = length (lift_perm k n σ).
Proof.
  intros; induction σ. simpl. reflexivity.
  simpl. f_equal. apply IHσ.
Qed.

Lemma lift_0_perm : forall (σ : perm) (k : nat),
    lift_perm k 0 σ = σ.
Proof.
  induction σ; intros; simpl. reflexivity.
  rewrite lift_0_neutral. f_equal; apply IHσ.
Qed.

Lemma lift_comm_0_perm : forall (σ : perm) (n m k : nat),
    lift_perm 0 k (lift_perm n m σ) =
      lift_perm (k + n) m (lift_perm 0 k σ).
Proof.
  induction σ; intros. simpl. reflexivity.
  simpl. f_equal; try apply IHσ. apply lift_comm_0.
Qed.

Fixpoint simul_subst (k : nat) (σ : perm) (t : term) :=
  match t with
  | {{n}} => if n <? k then {{n}} else 
               (if n <? (length σ + k) then
                  nth (n - k) σ {{0}} else {{n - length σ}})
  | t @ₜ u => (simul_subst k σ t) @ₜ (simul_subst k σ u)
  | λₜ t => λₜ (simul_subst (1 + k) (lift_perm 0 1 σ) t)
  | ⟨ t , u ⟩ => ⟨ simul_subst k σ t , simul_subst k σ u ⟩
  | π₁ t => π₁ (simul_subst k σ t)
  | π₂ t => π₂ (simul_subst k σ t)
  | star => star
  | Tt => Tt
  | Ff => Ff
  | IfThenElse t u v =>
      IfThenElse (simul_subst k σ t) (simul_subst k σ u)
        (simul_subst k σ v)
  | zero => zero
  | Sₜ t => Sₜ (simul_subst k σ t)
  | Recₜ t u v =>
      Recₜ (simul_subst k σ t) (simul_subst k σ u)
        (simul_subst k σ v)
  | κ₁ t => κ₁ (simul_subst k σ t)
  | κ₂ t => κ₂ (simul_subst k σ t)
  | delta t u v =>
      delta (simul_subst (1 + k) (lift_perm 0 1 σ) t) 
        (simul_subst (1 + k) (lift_perm 0 1 σ) u)
        (simul_subst k σ v)
  | δb t => δb (simul_subst k σ t)
  end.

Notation "{ k ↦ σ } t" := (simul_subst k σ t) (at level 67).

Lemma simul_nil : forall (t : term) (k : nat),
    simul_subst k nil t = t.
Proof.
  intro. induction t; intros; simpl; try reflexivity;
    try (f_equal ; apply IHt);
    try (rewrite IHt1 ; rewrite IHt2 ; try rewrite IHt3 ;
         reflexivity).
  simpl. case (n <? k). reflexivity. rewrite Nat.sub_0_r.
  reflexivity.
Qed.

Lemma simul_one : forall (t u : term) (k : nat),
    {k ↦ (u :: nil)} t = {k ~> u} t.
Proof.
  induction t; intros; try (simpl; reflexivity);
    try (simpl; f_equal; apply IHt);
    try (simpl; rewrite IHt1; rewrite IHt2; try rewrite IHt3;
         reflexivity).
  unfold simul_subst.
  case (n <? k) eqn : H. assert (n <? k = true). apply H.
  apply Nat.ltb_lt in H.
  apply Nat.lt_neq in H. assert (n <> k).
  intro; apply H in H1; inversion H1.
  apply Nat.eqb_neq in H1. unfold subst.
  rewrite H0. rewrite H1. reflexivity. simpl.
  case (n <? S k) eqn : H0. apply Nat.ltb_ge in H.
  apply Nat.ltb_lt in H0. apply -> Nat.lt_succ_r in H0.
  specialize (Nat.le_antisymm _ _ H H0). intro.
  rewrite H1. assert (n =? n = true).
  apply Nat.eqb_eq; reflexivity. rewrite H2.
  rewrite Nat.sub_diag. reflexivity. apply Nat.ltb_ge in H0.
  apply -> Nat.le_succ_l in H0.
  apply Nat.lt_neq in H0. assert (n =? k = false).
  apply Nat.eqb_neq. apply Nat.neq_sym in H0.
  apply H0. rewrite H1. rewrite H. reflexivity.
Qed.

Lemma simul_lift : forall (t : term) (σ : perm) (k : nat), {k ↦ σ} (lift k (length σ) t) = t.
Proof.
  induction t; intros; simpl ; try reflexivity;
    try (f_equal; try apply IHt; try apply IHt1; try apply IHt3;
         apply IHt2).
  - case (n <? k) eqn : H. simpl. rewrite H. reflexivity.
    simpl. apply Nat.ltb_ge in H.
    assert (length σ + k <= length σ + n).
    apply (Nat.add_le_mono_l k n (length σ)); apply H.
    specialize (Nat.le_trans _ _ _ H
                  (Nat.le_add_r _ (length σ)));
      intro.
    rewrite Nat.add_comm in H1.
    apply Nat.ltb_ge in H0. apply Nat.ltb_ge in H1. rewrite H0.
    rewrite H1.
    rewrite Nat.add_comm. rewrite Nat.add_sub. reflexivity.
  - f_equal. rewrite (lift_perm_length _ 0 1). apply IHt.
  - f_equal; try apply IHt3; rewrite (lift_perm_length _ 0 1);
      try apply IHt1; apply IHt2.
Qed.

Lemma lift_nth_perm : forall (σ : perm) (k p n : nat),
    k < length σ ->
    nth k (lift_perm n p σ) ({{0}}) = lift n p (nth k σ ({{0}})).
Proof.
  induction σ; intros. inversion H.
  simpl. case k eqn : H0. reflexivity. apply IHσ. simpl in H.
  apply Nat.succ_lt_mono in H. apply H.
Qed.

Lemma simul_tl_var : forall (t : term) (n : nat) (σ : perm)
                            (k : nat),
    {k ↦ σ} ({k ~> lift k (length σ) t} {{n}})
    = {k ↦ (t :: σ)} {{n}}.
Proof.
  intros.
  simpl. case (n <? k) eqn : H. assert (n <> k).
  apply Nat.lt_neq. apply Nat.ltb_lt. apply H.
  apply Nat.eqb_neq in H0. rewrite H0. simpl. rewrite H.
  reflexivity. case (n =? k) eqn : H0.
  rewrite simul_lift.
  apply Nat.ltb_ge in H.
  specialize (Nat.le_trans _ _ _ H (Nat.le_add_r _ (length σ)));
    intro.
  rewrite Nat.add_comm in H1.
  specialize (Nat.le_lt_trans _ _ _ H1 (Nat.lt_succ_diag_r _));
    intro. apply Nat.ltb_lt in H2.
  apply Nat.eqb_eq in H0. rewrite H0 in H2. rewrite H0.
  rewrite H2.
  rewrite Nat.sub_diag. reflexivity.
  case (n - 1 <? length σ + k) eqn : H1. unfold simul_subst.
  rewrite H1.
  apply Nat.ltb_lt in H1. rewrite Nat.sub_1_r in H1.
  apply Nat.lt_pred_lt_succ in H1. apply Nat.ltb_lt in H1.
  rewrite H1.
  apply Nat.ltb_ge in H. apply Nat.eqb_neq in H0. assert (k < n).
  apply Nat.lt_eq_cases in H. destruct H. apply H.
  symmetry in H. apply H0 in H. inversion H.
  specialize (Nat.lt_le_pred _ _ H2); intro.
  rewrite <- Nat.sub_1_r in H3. apply Nat.ltb_ge in H3.
  rewrite H3. specialize (Nat.sub_gt _ _ H2); intro.
  case (n - k) eqn : H5.
  assert (0 = 0); try reflexivity. apply H4 in H6. inversion H6.
  apply (f_equal (fun n => n + k)) in H5.
  rewrite Nat.sub_add in H5; try apply H.
  simpl in H5. apply (f_equal Nat.pred) in H5. simpl in H5.
  rewrite <- Nat.sub_1_r in H5.
  symmetry in H5. apply Nat.add_sub_eq_r in H5. rewrite H5.
  reflexivity.
  apply Nat.ltb_ge in H. apply Nat.eqb_neq in H0. assert (k < n).
  apply Nat.lt_eq_cases in H; destruct H.
  apply H. symmetry in H. apply H0 in H; inversion H.
  apply Nat.le_succ_l in H2.
  apply Nat.le_succ_le_pred in H2. rewrite <- Nat.sub_1_r in H2.
  apply Nat.ltb_ge in H2.
  simpl. rewrite H2. rewrite H1. apply Nat.ltb_ge in H1.
  rewrite Nat.sub_1_r in H1.
  apply Nat.lt_eq_cases in H1. destruct H1.
  apply Nat.le_pred_le in H1. apply Nat.ltb_ge in H1. rewrite H1.
  rewrite <- Nat.sub_add_distr. simpl. reflexivity.
  rewrite H1. specialize (Nat.lt_succ_pred k n); intro.
  assert (k < n). apply Nat.lt_eq_cases in H. destruct H.
  apply H. symmetry in H. apply H0 in H.
  inversion H. apply H3 in H4. symmetry in H4. symmetry in H4.
  apply Nat.eq_le_incl in H4. apply Nat.ltb_ge in H4.
  rewrite H4. rewrite <- Nat.sub_add_distr. simpl. reflexivity.
Qed.

Lemma simul_tl_r : forall (t u : term) (σ : perm) (k : nat),
    {k ↦ σ} ({k ~> lift k (length σ) u} t) = {k ↦ (u :: σ)} t.
Proof.
  induction t; intros;
    try (simpl; f_equal; try apply IHt1; try apply IHt2;
         try apply IHt3; try apply IHt);
    try reflexivity;
    try (rewrite lift_comm_0; rewrite (lift_perm_length _ 0 1);
         try apply IHt; try apply IHt1;
         try apply IHt2).
  apply simul_tl_var.
Qed.

Lemma simul_tl_l : forall (t u : term) (σ : perm) (k : nat),
    {k ↦ u :: σ} t = {k ~> u} ({1 + k ↦ lift_perm k 1 σ} t).
Proof.
  induction t; intros; try (simpl; reflexivity);
    try (simpl; f_equal; apply IHt);
    try (simpl; f_equal; try apply IHt1; try apply IHt3;
         apply IHt2).
  2 :{ simpl. f_equal. rewrite lift_comm_0_perm. simpl.
       apply IHt. }
  2 :{ simpl; f_equal; try apply IHt3; rewrite lift_comm_0_perm;
       simpl; try apply IHt2; apply IHt1. }
  simpl. rewrite <- lift_perm_length. case (n <? k) eqn : H.
  apply Nat.ltb_lt in H.
  specialize (Nat.lt_trans _ _ _ H (Nat.lt_succ_diag_r _));
    intro.
  apply Nat.ltb_lt in H0. rewrite H0. simpl.
  apply Nat.ltb_lt in H. rewrite H.
  apply Nat.ltb_lt in H. apply Nat.lt_neq in H.
  apply Nat.eqb_neq in H. rewrite H. reflexivity.
  case (n <? S k) eqn : H0.
  apply Nat.ltb_ge in H. apply Nat.ltb_lt in H0.
  apply -> Nat.lt_succ_r in H0.
  specialize (Nat.le_antisymm _ _ H H0); intro. rewrite H1.
  assert (n < S (length σ + n)). apply Nat.lt_succ_r.
  apply Nat.le_add_l.
  apply Nat.ltb_lt in H2. rewrite H2. rewrite Nat.sub_diag.
  simpl. assert (n = n). trivial.
  apply Nat.eqb_eq in H3. rewrite H3. reflexivity.
  case (n <? S (length σ + k)) eqn : H1.
  assert (n < length σ + S k). rewrite Nat.add_comm. simpl.
  rewrite Nat.add_comm. apply Nat.ltb_lt.
  apply H1. apply Nat.ltb_lt in H2. rewrite H2.
  apply Nat.ltb_lt in H1. apply -> Nat.lt_succ_r in H1.
  apply (Nat.sub_le_mono_r _ _ k) in H1.
  rewrite Nat.add_sub in H1. case (n - k) eqn : H3.
  apply Nat.sub_0_le in H3. exfalso. apply Nat.lt_eq_cases in H3.
  destruct H3. apply Nat.ltb_ge in H.
  apply (Nat.lt_irrefl _ (Nat.le_lt_trans _ _ _ H H3)).
  apply Nat.ltb_ge in H0. rewrite H3 in H0.
  apply Nat.nle_succ_diag_l in H0. apply H0.
  replace (n - S k) with n0. rewrite lift_nth_perm.
  rewrite <- subst_lift_neutral. reflexivity.
  apply -> Nat.le_succ_l. apply H1.
  apply eq_add_S. replace (S (n - S k)) with (S n - S k). simpl.
  symmetry. apply H3.
  apply Nat.sub_succ_l. apply Nat.ltb_ge in H0; apply H0.
  apply Nat.ltb_ge in H1.
  replace (S (length σ + k)) with (length σ + S k) in H1.
  2 :{ rewrite Nat.add_comm. simpl. rewrite Nat.add_comm.
       reflexivity. }
  apply Nat.ltb_ge in H1. rewrite H1. simpl.
  apply Nat.ltb_ge in H1.
  rewrite Nat.add_comm in H1. simpl in H1.
  apply -> Nat.le_succ_l in H1.
  apply Nat.lt_add_lt_sub_r in H1.
  specialize (Nat.lt_neq _ _ H1); intro.
  apply Nat.lt_le_incl in H1. apply Nat.neq_sym in H2.
  apply Nat.eqb_neq in H2.
  apply Nat.ltb_ge in H1. rewrite H1; rewrite H2. f_equal.
  rewrite <- Nat.sub_add_distr. rewrite Nat.add_comm. simpl.
  reflexivity.
Qed.

(** Maximal index

This part introduces the maximal index of a term, which is the
     maximal n such that the variable n appears in the term. This
     is useful to prove that we can find a permutation which
     fixes a term, for any term: it suffices to take the
     permutation [i ↦ {{i}}] with more elements than the maximal
     index of the term. *)

Fixpoint max_ind (t : term) : nat :=
  match t with
  | {{ n }} => S n
  | λₜ t => max_ind t - 1
  | t @ₜ u => max (max_ind t) (max_ind u)
  | zero => 0
  | Sₜ t => max_ind t
  | Recₜ t u v => max (max_ind t) (max (max_ind u) (max_ind v))
  | Tt => 0
  | Ff => 0
  | IfThenElse t u v =>
      max (max_ind t) (max (max_ind u) (max_ind v))
  | star => 0
  | ⟨ t , u ⟩ => max (max_ind t) (max_ind u)
  | π₁ t => max_ind t
  | π₂ t => max_ind t
  | κ₁ t => max_ind t
  | κ₂ t => max_ind t
  | delta t u v =>
      max (max_ind t - 1) (max (max_ind u - 1) (max_ind v))
  | δb t => max_ind t
  end.

(** id_perm k n represents [k,k+1,k+2,...,k+n-1] *)

Fixpoint id_perm (k n : nat) : perm :=
  match n with
  | 0 => nil
  | S n => {{k}} :: id_perm (S k) n
  end.

Lemma length_id_n_n : forall (k n : nat),
    length (id_perm k n) = n.
Proof.
  intros k n; generalize k; clear k; induction n; intros; simpl; try reflexivity.
  f_equal. apply IHn.
Qed.

Lemma id_perm_id_id : forall (n p : nat) (k : nat),
    k < n ->
    nth k (id_perm p n) ({{0}}) = {{k + p}}.
Proof.
  induction n; intros.
  inversion H.
  simpl. induction k. simpl. reflexivity.
  clear IHk. apply Nat.succ_lt_mono in H.
  specialize (IHn (S p) k H).
  rewrite IHn. rewrite Nat.add_comm. simpl. rewrite Nat.add_comm.
  reflexivity.
Qed.

Lemma lift_perm_id : forall (n p : nat) (m : nat),
    lift_perm 0 m (id_perm p n) = id_perm (m + p) n.
Proof.
  induction n; intros. simpl. reflexivity.
  simpl. f_equal. rewrite IHn. f_equal. rewrite Nat.add_comm.
  simpl. rewrite Nat.add_comm. trivial.
Qed.

Lemma perm_stat_var : forall (k n p : nat),
    S p <= n + k ->
    {k ↦ id_perm k n} {{p}} = {{p}}.
Proof.
  intros. simpl.
  case (p <? k) eqn : H0. reflexivity. rewrite length_id_n_n.
  apply -> Nat.le_succ_l in H. apply Nat.ltb_lt in H. rewrite H.
  rewrite id_perm_id_id. rewrite Nat.add_comm.
  rewrite Nat.add_comm. rewrite Nat.sub_add.
  reflexivity. apply Nat.ltb_ge. apply H0.
  apply Nat.ltb_lt in H. replace p with (p - k + k) in H.
  apply Nat.add_lt_mono_r in H.
  apply H. apply Nat.sub_add. apply Nat.ltb_ge. apply H0.
Qed.

Lemma perm_stat : forall (t : term) (n : nat) (k : nat),
    max_ind t <= n + k ->
    {k ↦ id_perm k n} t = t.
Proof.
  induction t; simpl; try reflexivity; intros;
    try (f_equal; apply IHt; try apply H);
    try (f_equal;
         try (apply IHt1;
              apply (Nat.le_trans _ _ _ (Nat.le_max_l _ _) H));
         apply IHt2;
         apply (Nat.le_trans _ _ _ (Nat.le_max_r _ _) H));
    try (f_equal;
         try (apply IHt1;
              apply (Nat.le_trans _ _ _ (Nat.le_max_l _ _) H));
         try (apply IHt2;
              apply (Nat.le_trans _ _ _
                       (Nat.le_trans _ _ _
                          (Nat.le_max_l _ _)
                          (Nat.le_max_r _ _)) H));
         apply IHt3;
         apply (Nat.le_trans _ _ _
                  (Nat.le_trans _ _ _ (Nat.le_max_r _ _)
                     (Nat.le_max_r _ _)) H)).
  - case (n <? k) eqn : H0. reflexivity.
    assert (n < length (id_perm k n0) + k).
    rewrite length_id_n_n. apply -> Nat.le_succ_l. apply H.
    apply Nat.ltb_lt in H1. rewrite H1.
    rewrite id_perm_id_id. rewrite Nat.sub_add. reflexivity.
    apply Nat.ltb_ge. apply H0.
    apply -> Nat.le_succ_l in H. replace n with (n - k + k) in H.
    apply Nat.add_lt_mono_r in H.
    apply H. apply Nat.sub_add. apply Nat.ltb_ge. apply H0.
  - rewrite lift_perm_id. f_equal. apply IHt.
    rewrite Nat.sub_1_r in H.
    apply Nat.le_pred_le_succ in H. rewrite Nat.add_comm. simpl.
    rewrite Nat.add_comm. apply H.
  - f_equal. rewrite lift_perm_id. simpl. apply IHt1.
    rewrite Nat.add_comm; simpl; rewrite Nat.add_comm.
    apply Nat.le_pred_le_succ. rewrite <- Nat.sub_1_r.
    apply (Nat.le_trans _
             (Init.Nat.max (max_ind t1 - 1)
                (Init.Nat.max (max_ind t2 - 1) (max_ind t3)))).
    apply Nat.le_max_l. apply H. rewrite lift_perm_id.
    apply IHt2. rewrite Nat.add_comm; simpl;
      rewrite Nat.add_comm. apply Nat.le_pred_le_succ.
    rewrite <- Nat.sub_1_r.
    apply (Nat.le_trans _ (Init.Nat.max (max_ind t2 - 1)
                             (max_ind t3))).
    apply Nat.le_max_l.
    apply (Nat.le_trans _
             (Init.Nat.max (max_ind t1 - 1)
                (Init.Nat.max (max_ind t2 - 1) (max_ind t3)))).
    apply Nat.le_max_r. apply H. apply IHt3.
    apply (Nat.le_trans _
             (Init.Nat.max (max_ind t2 - 1) (max_ind t3))).
    apply Nat.le_max_r.
    apply (Nat.le_trans _
             (Init.Nat.max (max_ind t1 - 1)
                (Init.Nat.max (max_ind t2 - 1) (max_ind t3)))).
    apply Nat.le_max_r. apply H.
Qed.
