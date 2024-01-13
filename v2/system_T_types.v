Require Import system_T_first_def.
Require Import system_T_substi.
Require Import system_T_reduction.
Require Import PeanoNat.
Require Import List.
Require Import Lt.

(* ********************************************************************************************* *)

(** I. First definitions *)

(** 4. Typing.

In this file, we define the typing relation, along with the basic results: if a term is typed in a
  context Γ then its free variables are bound in Γ and the subject reduction theorem.*)

(** A. Types.
Types are given by the following BNF:

                    T,U ::= X | Nat | Bool | Unit | Void | T → U | T × U | T + U

where X is in a countable set of type variables and Nat, Bool, Unit and Void are the expected base
  types.*)

Inductive type : Set :=
  | type_var : nat -> type
  | type_nat : type
  | type_bool : type
  | type_unit : type
  | type_void : type
  | type_arrow : type -> type -> type
  | type_product : type -> type -> type
  | type_sum : type -> type -> type.

Notation "[ x ]" := (type_var x).
Notation "T →ₜ U" := (type_arrow T U) (at level 68, right associativity).
Notation "T ×ₜ U" := (type_product T U) (at level 67, right associativity).
Notation "T +ₜ U" := (type_sum T U) (at level 67, right associativity).

(**
To define typing, we first define context and the relation of appearance in a context.*)

Definition ctx := list type.

Inductive binds : nat -> type -> ctx -> Prop :=
  | binds_hd : forall T Γ, binds 0 T (T :: Γ)
  | binds_tl : forall n T U Γ, binds n T Γ -> binds (S n) T (U :: Γ).

(**
This function is used to erase a type, which is useful for the typing of substitution.*)

Fixpoint remove_type k (Γ : ctx) :=
  match k , Γ with
    | _ , nil => nil
    | 0 , T :: Γ => Γ
    | S n , T :: Γ => T :: (remove_type n Γ)
  end.

(**
We list here the typing rules:
                         Γ, x : T ⊢ t : U       Γ ⊢ t : T → U      Γ ⊢ u : T
---------(x,T) ∈ Γ       ----------------       ----------------------------
Γ ⊢ x : T                Γ ⊢ λx.t : T → U               Γ ⊢ t u : U

                    Γ ⊢ t : nat          Γ ⊢ t : T    Γ ⊢ u : nat → T → T    Γ ⊢ v : nat
-----------       ---------------        -----------------------------------------------
Γ ⊢ 0 : nat        Γ ⊢ S t : nat                       Γ ⊢ rec t u v : T

                                     Γ ⊢ t : Bool   Γ ⊢ u : T   Γ ⊢ v : T
-------------    -------------       ------------------------------------
Γ ⊢ tt : Bool    Γ ⊢ ff : Bool             Γ ⊢ if t then u else v : T

Γ ⊢ t : T       Γ ⊢ u : U        Γ ⊢ t : T × U     Γ ⊢ t : T × U
-------------------------       --------------    --------------
     Γ ⊢ ⟨t,u⟩ : T × U           Γ ⊢ π₁ t : T      Γ ⊢ π₂ t : U

                    Γ ⊢ t : T              Γ ⊢ t : U
-------------   ----------------        ----------------
Γ ⊢ ⟨⟩ : unit   Γ ⊢ κ₁ t : T + U        Γ ⊢ κ₂ t : T + U

Γ, x : U ⊢ u : T     Γ , x : V ⊢ v : T     Γ ⊢ t : U+V      Γ ⊢ t : void
------------------------------------------------------      ------------
             Γ ⊢ δ (x₁ ↦ u | x₂ ↦ v) t : T                  Γ ⊢ δ⊥ t : T
*)

Inductive typing : ctx -> term -> type -> Prop :=
  | typing_var : forall T k Γ, binds k T Γ -> typing Γ {{ k }} T
  | typing_abs : forall t T1 T2 Γ, typing (T1 :: Γ) t T2 -> typing Γ (λₜ t) (T1 →ₜ T2)
  | typing_app : forall t1 t2 T1 T2 Γ, typing Γ t1 (T1 →ₜ T2) -> typing Γ t2 T1
    -> typing Γ ( t1 @ₜ t2) T2
  | typing_zero : forall Γ, typing Γ zero type_nat
  | typing_succ : forall t Γ, typing Γ t type_nat -> typing Γ (Sₜ t) type_nat
  | typing_rec : forall t1 t2 t3 T Γ, typing Γ t1 T -> typing Γ t2 (type_nat →ₜ T →ₜ T)
    -> typing Γ t3 type_nat -> typing Γ (Recₜ t1 t2 t3) T
  | typing_tt : forall Γ, typing Γ Tt type_bool
  | typing_ff : forall Γ, typing Γ Ff type_bool
  | typing_ife : forall t1 t2 t3 T Γ, typing Γ t1 type_bool -> typing Γ t2 T -> typing Γ t3 T
    -> typing Γ (IfThenElse t1 t2 t3) T
  | typing_pair : forall t1 t2 T1 T2 Γ, typing Γ t1 T1 -> typing Γ t2 T2
    -> typing Γ (⟨ t1 , t2 ⟩) (T1 ×ₜ T2)
  | typing_proj1 : forall t T1 T2 Γ, typing Γ t (T1 ×ₜ T2) -> typing Γ (π₁ t) T1
  | typing_proj2 : forall t T1 T2 Γ, typing Γ t (T1 ×ₜ T2) -> typing Γ (π₂ t) T2
  | typing_star : forall Γ, typing Γ star type_unit
  | typing_inj1 : forall t T1 T2 Γ, typing Γ t T1 -> typing Γ (κ₁ t) (T1 +ₜ T2)
  | typing_inj2 : forall t T1 T2 Γ, typing Γ t T2 -> typing Γ (κ₂ t) (T1 +ₜ T2)
  | typing_delta : forall t1 t2 t3 T1 T2 T Γ, typing (T1 :: Γ) t1 T -> typing (T2 :: Γ) t2 T
    -> typing Γ t3 (T1 +ₜ T2) -> typing Γ (δ(0 ↦ t1 |0 ↦ t2) t3) T
  | typing_deltaNil : forall t T Γ, typing Γ t type_void -> typing Γ (δb t) T.

Notation "Γ ⊢ t ~: T" := (typing Γ t T) (at level 69).
Notation "⊢ t ~: T" := (typing nil t T) (at level 70).


(** B. Subject reduction.

We prove that the relation Γ ⊢ t : T is stable by reduction, and extend it to ⊳*.*)

(**
We first give a few results about interaction between binding, removing and substitution.*)

Lemma binds_inj : forall k T U Γ, binds k T Γ -> binds k U Γ -> T = U.
Proof.
intros. induction H. inversion H0. trivial. inversion H0. apply IHbinds. apply H4.
Qed.

Lemma binds_remove_lt : forall k k1 T Γ, k < k1 -> binds k T Γ -> binds k T (remove_type k1 Γ).
Proof.
intro. induction k.
 - intros k1 T Γ. case Γ eqn : H.
  + intros. case k1 eqn : H2. inversion H0. simpl. apply H1.
  + intros. case k1 eqn : H2. inversion H0. simpl. inversion H1. apply binds_hd.
 - intros. case k1 eqn : H1. inversion H. case Γ eqn : H2.
  + inversion H0.
  + simpl. apply binds_tl. apply IHk.
   ++ apply Lt.lt_S_n. apply H.
   ++ inversion H0. apply H6.
Qed.


Lemma binds_remove_gt : forall k k1 T Γ, k1 < k -> binds k T Γ ->
  binds (k - 1) T (remove_type k1 Γ).
Proof.
intros. generalize k T Γ H H0. clear k T Γ H H0. induction k1.
 - intros. case Γ eqn : H1. inversion H0.
   simpl. case k eqn : H2. inversion H.
   simpl. rewrite Nat.sub_0_r. inversion H0.
   apply H6.
 - intros. case Γ eqn : H1. inversion H0.
   simpl. case k eqn : H2. simpl. inversion H0.
   apply binds_hd. inversion H0. case n eqn : H8. simpl. inversion H. inversion H10. simpl.
   apply binds_tl. replace n1 with (S n1 - 1). apply IHk1. apply Lt.lt_S_n.
   apply H. apply H6. simpl. rewrite Nat.sub_0_r. trivial.
Qed.

Lemma binds_app : forall k T Γ1 Γ2, binds k T Γ2 -> binds (length Γ1 + k) T (Γ1 ++ Γ2).
Proof.
intros. induction Γ1. simpl. apply H. simpl. apply binds_tl. apply IHΓ1.
Qed.

Lemma binds_left : forall k T Γ1 Γ2, k < length Γ1 -> binds k T (Γ1 ++ Γ2) -> binds k T Γ1.
Proof.
intro. induction k.
 - intros. case Γ1 eqn : H1.
  + inversion H.
  + inversion H0. apply binds_hd.
 - intros. case Γ1 eqn : H1.
  + inversion H.
  + inversion H0. apply binds_tl. apply (IHk T l Γ2).
   ++ apply Lt.lt_S_n. apply H.
   ++ apply H5.
Qed.

Lemma binds_left_inv : forall k T Γ1 Γ2, k < length Γ1 -> binds k T Γ1 -> binds k T (Γ1 ++ Γ2).
Proof.
intro. induction k.
 - intros. case Γ1 eqn : H1.
  + inversion H.
  + inversion H0. simpl. apply binds_hd.
 - intros. case Γ1 eqn : H1.
  + inversion H.
  + simpl. apply binds_tl. apply IHk. apply Lt.lt_S_n. apply H.
    inversion H0. apply H5.
Qed.

Lemma binds_right : forall k T Γ1 Γ2, binds (length Γ1 + k) T (Γ1 ++ Γ2) -> binds k T Γ2.
Proof.
intros k T Γ1. generalize k T. clear k T. induction Γ1.
 - intros. simpl in H. apply H.
 - intros. apply IHΓ1. inversion H. apply H3.
Qed.

Lemma binds_right_inv : forall k T Γ1 Γ2, binds k T Γ2 -> binds (length Γ1 + k) T (Γ1 ++ Γ2).
Proof.
intros k T Γ1. generalize k T. clear k T. induction Γ1.
 - intros. simpl. apply H.
 - intros. simpl. apply binds_tl. apply IHΓ1. apply H.
Qed.

Lemma remove_concat : forall k T Γ, T :: remove_type k Γ = remove_type (S k) (T :: Γ).
Proof.
intros. induction Γ. simpl. trivial. simpl. trivial.
Qed.

Lemma type_lift : forall Γ1 Γ2 Γ3 T t, Γ1 ++ Γ3 ⊢ t ~: T ->
  Γ1 ++ Γ2 ++ Γ3 ⊢ lift (length Γ1) (length Γ2) t ~: T.
Proof.
intros Γ1 Γ2 Γ3 T t. generalize Γ1 Γ2 Γ3 T. clear Γ1 Γ2 Γ3 T. induction t;intros;simpl;inversion H.
 - case (n<? length Γ1) eqn : H4.
  + apply Nat.ltb_lt in H4. apply (@binds_left n T Γ1 Γ3 H4) in H2.
    apply (@binds_left_inv n T Γ1 (Γ2++Γ3) H4) in H2. apply typing_var in H2. apply H2.
  + apply Nat.ltb_ge in H4. apply typing_var. inversion H.
    replace n with (length Γ1 + (n - length Γ1)) in H2. apply binds_right in H2.
    apply (@binds_right_inv (n-length Γ1) T (Γ1++Γ2) Γ3) in H2.
    rewrite app_length in H2. rewrite <- Nat.add_comm in H2. rewrite Nat.add_assoc in H2.
    rewrite Nat.sub_add in H2. rewrite Nat.add_comm in H2. rewrite <- app_assoc in H2.
    apply H2. apply H4. rewrite Nat.add_comm. rewrite Nat.sub_add. trivial. apply H4.
 - apply typing_abs. apply (@IHt (T1 :: Γ1)). apply H2.
 - apply (@typing_app (lift (length Γ1) (length Γ2) t1)
   (lift (length Γ1) (length Γ2) t2) T1 T (Γ1++Γ2++Γ3)). apply IHt1. apply H3.
   apply IHt2. apply H5.
 - apply typing_zero.
 - apply typing_succ. apply IHt. apply H2.
 - apply typing_rec;firstorder.
 - apply typing_tt.
 - apply typing_ff.
 - simpl. apply typing_ife;firstorder.
 - apply typing_pair;firstorder.
 - apply (@typing_proj1 _ T T2). apply IHt. apply H2.
 - apply (@typing_proj2 _ T1 T). apply IHt. apply H2.
 - apply typing_star.
 - apply typing_inj1. apply IHt. apply H2.
 - apply typing_inj2. apply IHt. apply H2.
 - apply (@typing_delta _ _ _ T1 T2 T);firstorder.
  ++ apply (@IHt1 (T1 :: Γ1) Γ2 Γ3 T). apply H4.
  ++ apply (@IHt2 (T2 :: Γ1) Γ2 Γ3 T). apply H6.
 - apply typing_deltaNil. apply IHt. apply H2.
Qed.

(**
This gives us the important result that if Γ, x : T ⊢ t : U and Γ ⊢ u : T then Γ ⊢ t[u/x] : U.*)

Lemma typing_subst : forall Γ T U k t u, binds k U Γ -> (remove_type k Γ) ⊢ u ~: U -> Γ ⊢ t ~: T
    -> (remove_type k Γ) ⊢ { k ~> u } t ~: T.
Proof.
intros. generalize u k H H0. clear u k H H0. induction H1;simpl;intros.
 - case (k =? k0) eqn : H2. apply Nat.eqb_eq in H2. rewrite <- H2 in H0.
   apply (@binds_inj _ _ _ _ H) in H0.
   rewrite <- H0 in H1. apply H1. case (k <? k0) eqn : H3. apply typing_var. apply binds_remove_lt.
   apply Nat.ltb_lt. apply H3. apply H. apply typing_var. apply binds_remove_gt.
   apply Nat.eqb_neq in H2. apply Nat.ltb_ge in H3. destruct H3. exfalso. apply H2. trivial.
   apply Gt.le_gt_S. apply H3. apply H.
 - apply typing_abs. rewrite remove_concat. apply IHtyping.
   apply binds_tl. apply H. simpl. apply (@type_lift nil (T1 :: nil) (remove_type k Γ) U u).
   simpl. apply H0.
 - apply (@typing_app ({k ~> u} t1) ({k ~> u} t2) T1 T2 (remove_type k Γ)).
   apply IHtyping1. apply H. apply H0.
   apply IHtyping2. apply H. apply H0.
 - apply typing_zero.
 - apply typing_succ. apply IHtyping. apply H. apply H0.
 - apply typing_rec;firstorder.
 - apply typing_tt.
 - apply typing_ff.
 - apply typing_ife;firstorder.
 - apply typing_pair;firstorder.
 - apply (@typing_proj1 _ T1 T2). apply IHtyping. apply H. apply H0.
 - apply (@typing_proj2 _ T1 T2). apply IHtyping. apply H. apply H0.
 - apply typing_star.
 - apply typing_inj1. apply IHtyping. apply H. apply H0.
 - apply typing_inj2. apply IHtyping. apply H. apply H0.
 - apply (@typing_delta _ _ _ T1 T2 T);firstorder.
  + apply (@IHtyping1 _ (1 + k)). apply binds_tl. apply H. rewrite <- remove_concat.
    apply (@type_lift nil (T1 :: nil) (remove_type k Γ) U u). simpl. apply H0.
  + apply (@IHtyping2 _ (1 + k)). apply binds_tl. apply H. rewrite <- remove_concat.
    apply (@type_lift nil (T2 :: nil) (remove_type k Γ) U u). simpl. apply H0.
 - apply typing_deltaNil. apply IHtyping. apply H. apply H0.
Qed.

Theorem subject_reduction : forall t1 t2 T Γ, Γ ⊢ t1 ~: T -> t1 ⊳ t2 -> Γ ⊢ t2 ~: T.
Proof.
intros. generalize Γ T H. clear Γ T H. induction H0;intros;inversion H.
 - apply H4.
 - apply (@typing_app _ _ T). apply (@typing_app _ _ type_nat). apply H6.
   inversion H7. apply H10. apply typing_rec. apply H4. apply H6. inversion H7. apply H10.
 - apply H6.
 - apply H7.
 - inversion H3. apply (@typing_subst (T1 :: Γ) T T1 0 t1 t2). apply binds_hd.
   simpl. apply H5. apply H9.
 - inversion H2. apply H8.
 - inversion H2. apply H10.
 - apply (@typing_subst (T1 :: Γ) T T1 0 t1 t3). apply binds_hd. simpl. inversion H7.
   apply H11. apply H4.
 - apply (@typing_subst (T2 :: Γ) T T2 0 t2 t3). apply binds_hd. simpl. inversion H7.
   apply H11. apply H6.
 - apply typing_rec. apply (@IHβred Γ T H5). apply H7. apply H8.
 - apply typing_rec. apply H5. apply (@IHβred Γ (type_nat →ₜ T →ₜ T) H7). apply H8.
 - apply typing_rec. apply H5. apply H7. apply (@IHβred Γ type_nat H8).
 - apply typing_succ. apply IHβred. apply H3.
 - apply typing_ife. apply (@IHβred Γ type_bool H5). apply H7. apply H8.
 - apply typing_ife. apply H5. apply (@IHβred Γ T H7). apply H8.
 - apply typing_ife. apply H5. apply H7. apply (@IHβred Γ T H8).
 - apply typing_abs. apply IHβred. apply H3.
 - apply (@typing_app _ _ T1). apply IHβred. apply H4. apply H6.
 - apply (@typing_app _ _ T1). apply H4. apply IHβred. apply H6.
 - apply typing_pair. apply IHβred. apply H4. apply H6.
 - apply typing_pair. apply H4. apply IHβred. apply H6.
 - apply (@typing_proj1 _ _ T2). apply IHβred. apply H3.
 - apply (@typing_proj2 _ T1). apply IHβred. apply H3.
 - apply typing_inj1. apply IHβred. apply H3.
 - apply typing_inj2. apply IHβred. apply H3.
 - apply (@typing_delta _ _ _ T1 T2). apply IHβred. apply H5. apply H7. apply H8.
 - apply (@typing_delta _ _ _ T1 T2). apply H5. apply IHβred. apply H7. apply H8.
 - apply (@typing_delta _ _ _ T1 T2). apply H5. apply H7. apply IHβred. apply H8.
 - apply typing_deltaNil. apply IHβred; apply H3.
Qed.

Corollary subject_reduction_star : forall t1 t2 T Γ, Γ ⊢ t1 ~: T -> t1 ⊳* t2 -> Γ ⊢ t2 ~: T.
Proof.
intros. induction H0. apply H. apply (subject_reduction u v T Γ). apply (IHrt_closure H). apply H1.
Qed.