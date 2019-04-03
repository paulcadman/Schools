Require Import UniMath.Foundations.PartD.

(** The following axiom allows us to inhabit any type.
    It is a way of indicating where you need to fill in
    your own solutions. Remove it once you're done with
    all the exercises. *)
Axiom fill_me : forall {X : UU}, X.

(** Exercise 1.1. A × (B + C) → A × B + A × C, given types A, B, C *)

Locate "×".
Print dirprod.
Search (dirprod).
Search (coprod).
Search (_ -> dirprod _ _).
Search (dirprod _ _ -> _).
Search (?A -> ?A).

Print dirprod.

Check coprod_rect.

Definition exercise_1_1 (A B C : UU)
  : A × (B ⨿ C) → (A × B) ⨿ (A × C) :=
  λ p, (coprod_rect (λ _, (A × B) ⨿ (A × C))
              (λ b, ii1 (pr1 p,,b))
              (λ c, ii2 (pr1 p,,c)))(pr2 p).

(** Exercise 1.2. (A → A) → (A → A), given type A

    for extra credit, write down *five* elements of this type *)

Definition exercise_1_2 (A : UU)
  : (A → A) → (A → A)
  := λ f, (λ a, (f a)).

(** Exercise 1.3. Id_nat (0, succ 0) → empty *)

Search (_ -> empty).
Check nopathstruetofalse.
Check nopathsfalsetotrue.

Check nat_rect.
Check maponpaths.
Check transportf.

Definition not_zero : nat -> bool :=
  nat_rect (λ _, bool)
           true
           (λ _ _, false).

Definition exercise_1_3 : (0 = 1) → empty :=
  λ zeroIsNotOne, (nopathstruetofalse
                     (maponpaths not_zero
                                 zeroIsNotOne)).

Theorem exercise_1_3' : (0 = 1) → empty.
Proof.
  intros.
  apply (maponpaths not_zero) in X.
  unfold not_zero in X.
  compute in X.
  apply nopathstruetofalse in X.
  exact X.
Qed.

(** Exercise 1.4. ∑ (A : Universe) (A → empty) *)

Theorem exercise_1_4 : ∑ A:UU, (A → empty).
Proof.
  exact ((0=1),,exercise_1_3).
Qed.

(** Exercise 1.6. (∑ (x : A) B × P x) → B × ∑ (x : A) P x,
                  given types A, B, and P : A → Universe *)

Check pr1.
Check pr2.

Definition exercise_1_6' (A B:UU) (P:A -> UU) : (∑ x:A, B × P x) -> B :=
  λ s, (pr1 (pr2 s)).

Definition exercise_1_6'' (A B:UU) (P:A -> UU) : (∑ x:A, B × P x) -> ∑ x:A, P x :=
  λ s, (pr1 s,,pr2 (pr2 s)).

Theorem exercise_1_6 (A B:UU) (P:A → UU) : (∑ x:A, B × P x) → B × ∑ x:A, P x.
Proof.
  exact (λ s, (exercise_1_6' A B P s,,exercise_1_6'' A B P s)).
Qed.

(** Exercise 1.7. B → (B → A) → A, given types A and B *)

Theorem exercise_1_7 (A B : UU) : B → (B → A) → A.
Proof.
  exact (λ b f, f b).
Qed.

(** Exercise 1.8. B → ∏ (A : Universe) (B → A) → A, given type B *)

Theorem exercise_1_8 (B : UU) : B → ∏ A:UU, (B → A) → A.
Proof. exact (λ b, (λ _ f, f b)). Qed.

(** Exercise 1.9. (∏ (A : Universe) (B → A) → A) → B, given type B *)

Check idfun.
Theorem exercise_1_9 (B : UU) : (∏ A:UU, (B → A) → A) → B.
Proof. exact (λ u, ((u B) (idfun B))). Qed.

(** Exercise 2.1. Using the basic rules, construct addition on natural numbers. *)

Check nat_rect.

Definition nat_plus : nat → nat → nat :=
  λ n m, (nat_rect (λ _, nat)
                   m
                   (λ _, (λ k, S k )) n).

(** Exercise 2.2. State associativity and commutativity of addition in a type-theoretic way. *)

Definition exercise_2_2_assoc : UU := (∏ n m k: nat, (nat_plus n
                                                             (nat_plus m
                                                                       k)
                                                    =
                                                    (nat_plus (nat_plus n
                                                                        m)
                                                              k))).

Definition exercise_2_2_comm : UU := (∏ n m, (nat_plus n m = nat_plus m n)).

(** Exercise 2.3. Establish associativity and commutativity of addition. What does this mean in type theory? *)


Check idpath.

Search (?A = ?A).

Check idpath.

Lemma nat_plus_zero : (∏ n: nat, (nat_plus 0 n) = n).
Proof.
  exact (λ n, idpath n).
  (* intros. *)
  (* (* simpl. *) *)
  (* apply idpath. *)
Defined.

Eval compute in nat_plus_zero.

Check nat_rect.

Lemma nat_zero_zero : nat_plus 0 0 = 0.
Proof.
  apply idpath.
Defined.

Lemma nat_plus_succ : (∏ n m: nat, nat_plus (S n) m = S (nat_plus n m)).
Proof.
  intros.
  (* simpl *)
  apply idpath.
Qed.

Eval compute in nat_zero_zero.

Check idpath.

Lemma nat_zero_plus_step : (∏ n : nat, nat_plus n 0 = n -> nat_plus (S n) 0 = (S n)).
Proof.
  intros.
  rewrite nat_plus_succ.
  apply (maponpaths succ).
  exact X.
Qed.

Lemma nat_zero_plus : (∏ n : nat, (nat_plus n 0) = n).
Proof.
  exact (nat_rect (λ n, nat_plus n 0 = n)
                  (idpath 0)
                  nat_zero_plus_step
        ).
  Qed.

Lemma nat_plus_zero' : (∏ m k: nat, nat_plus 0 (nat_plus m k) =
  nat_plus (nat_plus 0 m) k).
Proof.
  intros.
  rewrite nat_plus_zero.
  rewrite nat_plus_zero.
  apply idpath.
Qed.

Print nat_plus_zero'.

Check maponpaths.

Search (_ = _).


Lemma nat_assoc_step : (∏ n m k, (nat_plus n (nat_plus m k) = nat_plus (nat_plus n m) k) -> (nat_plus (S n) (nat_plus m k) = nat_plus (nat_plus (S n) m) k)).
  intros.
  apply (maponpaths succ X).
Qed.

Theorem nat_plus_is_assoc : exercise_2_2_assoc.
Proof.
  exact (λ n m k,
         (nat_rect (λ n, (nat_plus n (nat_plus m k) = (nat_plus (nat_plus n m) k)))
                  (nat_plus_zero' m k)
                  (λ n p, (nat_assoc_step n m k p)))
         n).
Qed.

Lemma nat_plus_is_comm_base : ∏ m: nat, nat_plus 0 m = nat_plus m 0.
Proof.
  intros.
  cbn.
  rewrite nat_zero_plus.
  apply idpath.
Defined.

Lemma nat_plus_succ_right : ∏ n m: nat, nat_plus m (S n) = S (nat_plus m n).
Proof.
  intros.
  induction m.
  cbn.
  apply idpath.
  rewrite nat_plus_succ.
  apply maponpaths.
  rewrite nat_plus_succ.
  assumption.
Qed.

Lemma nat_plus_is_comm_step : ∏ m n: nat, nat_plus n m = nat_plus m n -> nat_plus (S n) m = nat_plus m (S n).
Proof.
  intros.
  rewrite nat_plus_succ_right.
  rewrite nat_plus_succ.
  apply maponpaths.
  assumption.
Qed.

Theorem nat_plus_is_comm : exercise_2_2_comm.
Proof.
  exact (λ n m,
         (nat_rect (λ n, nat_plus n m = nat_plus m n)
                   (nat_plus_is_comm_base m)
                   (nat_plus_is_comm_step m)) n
        ).
Qed.

(** Exercise 3. Write down the following types:

    1. even natural numbers *)

Definition exercise_3_1 : UU := ∑ (n:nat), (∑ (k:nat), n = nat_plus k k).

(** 2. prime numbers *)

Check nat_rect.

Definition nat_mult : nat → nat → nat :=
  λ n, nat_rect (λ _, nat) 0 (λ _ almost, nat_plus n almost).

(* Definition exercise_3_2 : UU :=
  ∑ (n : nat), (∏ (d1 d2 : nat), (n = nat_mult d1 d2) -> ((d1 = 1) ‌⨿ (d2 = 1))).
 *)

Print coprod.

Definition exercise_3_2 : UU :=
  ∑ (n : nat), ((n = 1) -> empty) × (∏ (d1 d2: nat), (n = nat_mult d1 d2) -> ((d1 = 1) ⨿ (d2 = 1))).


(** 3. functions A → nat which attain zero *)

Definition exercise_3_3 (A : UU) : UU :=
  ∑ (f: A -> nat), (∑ (a:A), f a = 0).

(** 4. the "less than" relation on natural numbers *)

Definition exercise_3_4 (n m : nat) : UU := (∑ (k:nat), (S (nat_plus n k)) = m).
