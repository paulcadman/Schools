
Require Import UniMath.Foundations.Preamble.
Require Import UniMath.Foundations.PartA.
Require Import UniMath.Foundations.NaturalNumbers.

Definition less_than' : nat -> nat -> UU.
  intros m.
  induction m.
  - intro n.
    destruct n.
    + exact empty.
    + exact unit.
  (* everything below defining for S m *)
  - intro n.
    induction n. (* Can use destruct instead *)
    + exact empty.
    (* everything below defining for S n, inside 'the block' for S m *)
    + exact (IHm n).
Defined.

Definition less_than : nat -> nat -> bool.
  intros m.
  induction m.
  - intro n.
    destruct n.
    + exact false.
    + exact true.
  (* everything below defining for S m *)
  - intro n.
    destruct n. (* Can use destruct instead *)
    + exact false.
    (* everything below defining for S n, inside 'the block' for S m *)
    + exact (IHm n).
Defined.

Print less_than.

Eval compute in less_than' 3 4.

Lemma path_inverse (X : UU) : ∏ (x y: X), x = y -> y = x.
Proof.
  intros x y H.
  induction H.
  apply idpath.
Defined.

Search (?x = ?y -> ?y = ?x).

Search (pathsinv0).

Print pathsinv0inv0.

Lemma path_inverse_involution (X : UU) :
  ∏ (x y: X), (∏ (p: x = y), (path_inverse X y x (path_inverse X x y p)) = p).
Proof.
  intros.
  induction p.
  apply idpath.
Defined.

Print path_inverse.
About paths_ind.

Search (S _ = S _).

Print invmaponpathsS.

Lemma path_composition (X : UU) : ∏ (x y z: X), x = y -> y = z -> x = z.
  intros x y z H1 H2.
  induction H1.
  exact H2.
Defined.

Lemma map_on_path (X Y: UU) : ∏ (f : X -> Y), (∏ (x y: X), x = y -> f x = f y).
Proof.
  intros ? ? ? H.
  induction H.
  exact (idpath (f x)).
Defined.


Lemma path_composition_assoc (X : UU) :
  ∏ (x y z w: X), (∏ (p_xy : x = y) (p_yz : y = z) (p_zw : z = w),
                   (path_composition X x z w (path_composition X x y z p_xy p_yz) p_zw)
                   =
                   (path_composition X x y w p_xy (path_composition X y z w p_yz p_zw))).
Proof.
  intros.
  induction p_xy.
  induction p_yz.
  induction p_zw.
  apply idpath.
Defined.
