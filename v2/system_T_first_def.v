Require Import PeanoNat.
Require Import Lt.
Require Import List.
Require Import Arith.

(** ******************************************************************************************** *)

(** I. First definitions *)

(** 1. Terms.

This file contains the definitions of terms and other basic stuff. We also detail the lift
  operation which can be interpreted as a weakening.

Terms are given by the following BNF:
  t,u ::= x | λ x.t | t u | 0 | S t | Rec x0 f n | tt | ff | If b then t else u
    | ⟨ t,u ⟩ | π₁ t | π₂ t | ⟨⟩ | κ₁ t | κ₂ t | δ (x₁ ↦ t | x₂ ↦ u) v | δ⊥ t

We will write terms in De Bruijn indexes: a variable will be a number indicating how many
  abstractions one has to go through to find the one binding the variable. A free variable
  is then a variable for which there is no abstraction binding it, for example λ 1 has a free
  variable. *)

Inductive term : Set :=
  | var : nat -> term
  | λₜ : term -> term
  | app : term -> term -> term
  | zero : term
  | Sₜ : term -> term
  | Recₜ : term -> term -> term -> term
  | Tt : term
  | Ff : term
  | IfThenElse : term -> term -> term -> term
  | pair : term -> term -> term
  | π₁ : term -> term
  | π₂ : term -> term
  | star : term
  | κ₁ : term -> term
  | κ₂ : term -> term
  | delta : term -> term -> term -> term
  | δb : term -> term.

Notation "{{ x }}" := (var x) (at level 9).
Notation " t @ₜ u " := (app t u) (at level 68).
Notation "⟨ t , u ⟩" := (pair t u) (at level 69).
Notation "δ(0 ↦ t |0 ↦ u ) v " := (delta t u v) (at level 68).

(**
We define the code of n to be Sⁿ 0.*)

Fixpoint code_nat (n : nat) : term :=
  match n with
    | 0 => zero
    | S n => Sₜ (code_nat n)
  end.

(** The function lift k n increases the index of all variables greater or equal than k by n. It we
  interpret a term t in a context Γ, this corresponds to a weakening where we split the context Γ
  as Γ₁ ++ Γ₂ and then add a contexte Δ in between to have Γ₁ ++ Δ ++ Γ₂. *)

Fixpoint lift (k : nat) (n : nat) (t : term) : term :=
  match t with
    | var i => if i <? k then {{ i }} else {{ n + i }}
    | λₜ t1 => λₜ (lift (1 + k) n t1)
    | app t1 t2 => app (lift k n t1) (lift k n t2)
    | zero => zero
    | Sₜ t1 => Sₜ (lift k n t1)
    | Recₜ x f p => Recₜ (lift k n x) (lift k n f) (lift k n p)
    | Tt => Tt
    | Ff => Ff
    | IfThenElse t1 t2 t3 => IfThenElse (lift k n t1) (lift k n t2)
      (lift k n t3)
    | pair t1 t2 => pair (lift k n t1) (lift k n t2)
    | π₁ t1 => π₁ (lift k n t1)
    | π₂ t2 => π₂ (lift k n t2)
    | star => star
    | κ₁ t1 => κ₁ (lift k n t1)
    | κ₂ t2 => κ₂ (lift k n t2)
    | delta t1 t2 t3 => delta (lift (1 + k) n t1) (lift (1 + k) n t2) (lift k n t3)
    | δb t1 => δb (lift k n t1)
  end.

(** We give a useful result to rewrite lifts in the other files. *)

Lemma lift_comm_low : forall (t : term) (n m k p : nat), k <= p ->
  lift k n (lift p m t) = lift (n + p) m (lift k n t).
Proof.
induction t; intros; simpl;
  try (f_equal; try apply IHt; try apply IHt1; try apply IHt2; try apply IHt3; apply H);
  try reflexivity.
  - case (n <? p) eqn : H0. case (n <? k) eqn : H1. simpl.
    rewrite H1. apply Nat.ltb_lt in H0.
    apply (Nat.lt_lt_add_l _ _ n0) in H0. apply Nat.ltb_lt in H0. rewrite H0.
    reflexivity.
    simpl. rewrite H1. apply Nat.ltb_lt in H0.
    apply (plus_lt_compat_l _ _ n0) in H0. apply Nat.ltb_lt in H0. rewrite H0.
    reflexivity.
    case (n <? k) eqn : H1. simpl. apply Nat.ltb_lt in H1.
    apply Nat.ltb_ge in H0. apply (Nat.le_lt_trans _ _ _ H0) in H1.
    exfalso. apply (Nat.lt_irrefl _ (Nat.lt_le_trans _ _ _ H1 H)).
    simpl. case (m + n <? k) eqn : H2.
    apply Nat.ltb_ge in H1. apply Nat.ltb_lt in H2.
    apply (Nat.lt_le_trans _ _ _ H2) in H1.
    replace (m + n < n) with (m + n < 0 + n) in H1; try (simpl; reflexivity).
    apply Nat.add_lt_mono_r in H1. inversion H1.
    apply Nat.ltb_ge in H0. apply (plus_le_compat_l _ _ n0) in H0.
    apply Nat.ltb_ge in H0. rewrite H0. f_equal. rewrite Nat.add_comm.
    rewrite <- Nat.add_assoc. f_equal. apply Nat.add_comm.
  - f_equal. replace (S (n + p)) with (n + S p). apply IHt.
    apply le_n_S. apply H. rewrite Nat.add_comm. simpl; f_equal; apply Nat.add_comm.
  - f_equal; try replace (S (n + p)) with (n + S p);
    try apply IHt1; try apply IHt2; try apply IHt3; try apply le_n_S; try apply H;
    rewrite Nat.add_comm; simpl; f_equal; apply Nat.add_comm.
Qed.

Corollary lift_comm_0 : forall (t : term) (n m k : nat),
  lift 0 k (lift n m t) = lift (k + n) m (lift 0 k t).
Proof.
intros. apply lift_comm_low. apply Nat.le_0_l.
Qed.

Lemma lift_0_neutral : forall (t : term) (k : nat), lift k 0 t = t.
Proof.
induction t; intros; simpl; try reflexivity; try (f_equal; apply IHt);
  try (rewrite IHt1; rewrite IHt2; try rewrite IHt3; reflexivity).
case (n <? k); reflexivity.
Qed.

(** We prove that lift is compatible : if lift k n t = u @ₜ v then u and v can be written as
  lift k n u' and lift k n v'.*)

Lemma lift_compat_abs : forall (t u : term) (k n : nat), lift k n t = λₜ u -> exists t' : term,
  t = λₜ t'.
Proof.
induction t; intros; try inversion H.
  - case (n <? k) eqn : H2; inversion H1.
  - exists t. reflexivity.
Qed.

Lemma lift_compat_app : forall (t u v : term) (k n : nat), lift k n t = u @ₜ v -> exists u' : term,
  exists v' : term, t = u' @ₜ v'.
Proof.
induction t; intros; try inversion H.
  - case (n <? k) eqn : H2. inversion H1. inversion H1.
  - simpl in H. exists t1. exists t2. inversion H. split; reflexivity.
Qed.

Lemma lift_compat_pair : forall (t u v : term) (k n : nat), lift k n t = ⟨ u , v ⟩ ->
  exists u' : term, exists v' : term, t = ⟨ u' , v' ⟩.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t1. exists t2. split; reflexivity.
Qed.

Lemma lift_compat_proj1 : forall (t u : term) (k n : nat), lift k n t = π₁ u ->
  exists u' : term, t = π₁ u'.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t. reflexivity.
Qed.

Lemma lift_compat_proj2 : forall (t u : term) (k n : nat), lift k n t = π₂ u ->
  exists u' : term, t = π₂ u'.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t. reflexivity.
Qed.

Lemma lift_compat_inj1 : forall (t u : term) (k n : nat), lift k n t = κ₁ u ->
  exists u' : term, t = κ₁ u'.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t. reflexivity.
Qed.

Lemma lift_compat_inj2 : forall (t u : term) (k n : nat), lift k n t = κ₂ u ->
  exists u' : term, t = κ₂ u'.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t. reflexivity.
Qed.

Lemma lift_compat_delta : forall (t u v w : term) (k n : nat), lift k n t = delta u v w ->
  exists u' : term, exists v' : term, exists w' : term, t = delta u' v' w'.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t1; exists t2; exists t3. repeat (split; try reflexivity).
Qed.

Lemma lift_compat_succ : forall (t u : term) (k n : nat), lift k n t = Sₜ u -> exists u' : term,
  t = Sₜ u'.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t. reflexivity.
Qed.

Lemma lift_compat_rec : forall (t u v w : term) (k n : nat), lift k n t = Recₜ u v w ->
  exists u' : term, exists v' : term, exists w' : term, t = Recₜ u' v' w'.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t1; exists t2; exists t3. repeat (split; try reflexivity).
Qed.

Lemma lift_compat_ite : forall (t u v w : term) (k n : nat), lift k n t = IfThenElse u v w ->
  exists u' : term, exists v' : term, exists w' : term, t = IfThenElse u' v' w'.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t1; exists t2; exists t3. repeat (split; try reflexivity).
Qed.

Lemma lift_compat_delta_nil : forall (t u : term) (k n : nat), lift k n t = δb u ->
  exists u' : term, t = δb u'.
Proof.
induction t; intros; try inversion H; try (case (n <? k) eqn : H2; inversion H1; fail).
exists t. reflexivity.
Qed.