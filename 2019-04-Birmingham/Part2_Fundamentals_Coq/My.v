Require Import UniMath.Foundations.Preamble.

Definition idfun : forall (A : UU), A -> A :=
  fun (A : UU) (a : A) => a.

Definition idfun' (A : UU) (a : A) : A := a.

About bool.
Print bool.
Check true.

About bool_rect.

Definition ifbool (A : UU) (x y : A) : bool -> A :=
  bool_rect (fun _ : bool => A) x y.

Definition negbool : bool -> bool :=
  ifbool bool false true.

Eval compute in negbool true.

Print nat.
Check nat_rect.

Definition nat_rect (A : UU) (a : A) (f : nat -> A -> A) : nat -> A := nat_rect (fun _ : nat => A) a f.

(*
nat_rect a f 0 = a
nat_rect a f (S n) = f n (nat_rect a f n)
 *)

Definition pred : nat -> nat :=
  nat_rect nat 0 (fun x _ => x).

(*
pred 0 = 0
pred (S n) = n
 *)

Eval compute in pred 3.

Definition even : nat -> bool :=
  nat_rect bool true (fun _ b => negbool b).

Definition add (m : nat) : nat -> nat :=
  nat_rect nat m (fun _ x => S x).

Notation "x + y" := (add x y).

Eval compute in 7 + 4.

Locate "+".

Definition iter (A : UU) (a : A) (f : A -> A) (n : nat) : A := nat_rect A a (λ _ x, f x) n.

Notation "f ^ n" := (λ x, iter _ x f n).

Eval compute in (pred ^ 2) 5.

Definition sub (m n : nat) : nat := (pred ^ n) m.

Definition idfun'' {A : UU} (a : A) : A := a.

Check idfun'' 3.
Check @idfun'' nat 3.

Print unit.
Print empty.

(* Σ types *)
(* "total2" in UniMath *)

Print total2.
Check tpair.
Locate ",,".

Check pr1.
Check pr2.

Definition even_nat : UU :=
  ∑ (n : nat), ifbool _ unit empty (even n).

Definition test20 : even_nat := (20,,tt).

Fail Definition test3 : even_nat := (3,,tt).

Definition dirprod (X Y : UU): UU :=
  ∑ (x : X), Y.

Notation "X × Y" := (dirprod X Y).

Section currysec.
  Variables (A B C : UU).
  Definition curry : (A × B -> C) -> (A -> B -> C) :=
    λ (f : A × B -> C) (a : A) (b: B), f (a,,b).
End currysec.

Check curry.
