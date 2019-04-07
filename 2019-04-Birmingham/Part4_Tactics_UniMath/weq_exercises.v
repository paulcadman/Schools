(** *** Advanced exercise sheet for lecture 4: Tactics in Coq. *)

(** Some exercises about equivalences - recall from the course that associativity
    for products of types is not available "on the nose", i.e., just with equality.

    Exercises originally suggested by Benedikt Ahrens and Anders Mörtberg
    (for UniMath school 2017) and elaborated by Ralph Matthes (CNRS, IRIT,
    Univ. Toulouse, France)
*)
Require Import UniMath.Foundations.PartA.

Locate "≃". (** written in Agda mode as [\simeq] *)
Print weq.
Print isweq.
Print hfiber.

Section weqdef.

Variables X Y: UU.
Eval compute in (X ≃ Y).
(** there is a function [f] so that for given image [y] on can find the preimage [x] uniquely, but not only as element of [X] but even the pair consisting of the preimage and the proof that it is the preimage is unique. *)
End weqdef.


(** Prove that the identity function is an equivalence *)
Lemma idisweq (X : UU) : isweq (idfun X).
  unfold isweq.
  intro y.
  unfold iscontr.
  unfold hfiber.
  use tpair.
  - exists y.
    apply idpath.
  - cbn.
    intro t.
    induction t as [x H].
    unfold idfun in H.
    rewrite H.
    apply idpath.
Defined.

Check idfun.
(** Package this up as an equivalence *)
Definition idweq (X : UU) : X ≃ X.
  unfold weq.
  exists (idfun X).
  apply idisweq.
Defined.

Check isweq_iso.
(** consider finding an alternative proof with [isweq_iso] that is extremely useful in the UniMath library *)

Lemma idisweq_alt (X : UU) : isweq (idfun X).
Proof.
  use isweq_iso.
  - exact (idfun X).
  - intro.
    apply idpath.
  - intro.
    apply idpath.
Defined.


(** Prove that any map to empty is an equivalence *)
Lemma isweqtoempty {X : UU} (f : X -> ∅) : isweq f.
  unfold isweq.
  intro.
  unfold iscontr.
  unfold hfiber.
  use tpair.
  - induction y.
  - cbn.
    intro.
    induction y.
Defined.


(** Package this up as an equivalence *)
Definition weqtoempty {X : UU} (f : X -> ∅) : X ≃ ∅.
unfold weq.
use tpair.
- exact f.
- cbn.
  exact (isweqtoempty f).
Defined.


(** Prove that the composition of equivalences is an equivalence.

This is rather difficult to do directly from the definition. Important lemmas
to reason on equality of pairs in a sigma type are given by [base_paths] and
[fiber_paths] that are elimination rules (that use given equality of pairs)
and [total2_paths2_f] that is an introduction rule allowing to establish an
equation between pairs. There, transport arises, but transport along the
identity path is always the identity, and this already computationally, which
means that [cbn] gets rid of it. *)

Check base_paths.
Check fiber_paths.
Check total2_paths2_f.

Theorem compisweq {X Y Z : UU} (f : X -> Y) (g : Y -> Z)
        (isf : isweq f) (isg : isweq g) : isweq (g ∘ f).


Abort.

(** Package this up as an equivalence *)
Definition weqcomp {X Y Z : UU} (w1 : X ≃ Y) (w2 : Y ≃ Z) : X ≃ Z.
Abort.
