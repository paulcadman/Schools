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
  exact (λ s (exercise_1_6' s,,exercise_1_6'' s)).
Qed.

(** Exercise 1.7. B → (B → A) → A, given types A and B *)

Theorem exercise_1_7 (A B : UU) : B → (B → A) → A.
Proof. exact fill_me. Qed.

(** Exercise 1.8. B → ∏ (A : Universe) (B → A) → A, given type B *)

Theorem exercise_1_8 (B : UU) : B → ∏ A:UU, (B → A) → A.
Proof. exact fill_me. Qed.

(** Exercise 1.9. (∏ (A : Universe) (B → A) → A) → B, given type B *)

Theorem exercise_1_9 (B : UU) : (∏ A:UU, (B → A) → A) → B.
Proof. exact fill_me. Qed.

(** Exercise 2.1. Using the basic rules, construct addition on natural numbers. *)

Definition nat_plus : nat → nat → nat := fill_me.

(** Exercise 2.2. State associativity and commutativity of addition in a type-theoretic way. *)

Definition exercise_2_2_assoc : UU := fill_me.

Definition exercise_2_2_comm : UU := fill_me.

(** Exercise 2.3. Establish associativity and commutativity of addition. What does this mean in type theory? *)

Theorem nat_plus_is_assoc : exercise_2_2_assoc.
Proof.
  exact fill_me.
Qed.

Theorem nat_plus_is_comm : exercise_2_2_comm.
Proof.
  exact fill_me.
Qed.

(** Exercise 3. Write down the following types:

    1. even natural numbers *)

Definition exercise_3_1 : UU := fill_me.

(** 2. prime numbers *)

Definition nat_mult : nat → nat → nat := fill_me.

Definition exercise_3_2 : UU := fill_me.

(** 3. functions A → nat which attain zero *)

Definition exercise_3_3 (A : UU) : UU := fill_me.

(** 4. the "less than" relation on natural numbers *)

Definition exercise_3_4 (n m : nat) : UU := fill_me.
