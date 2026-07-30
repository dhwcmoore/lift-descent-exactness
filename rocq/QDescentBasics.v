(** * Elementary descent facts

    Three results that need no finite-dimensional extension theorem:

    [[
      lift_obstruction_zero D r  <->  exists u, D u = r
      L = M o D                  ->  L(ker D) = 0
      L(ker D) = 0                <->  ker D subset ker L
    ]]

    The harder converse — [ker D subset ker L] implies an ambient [M]
    with [L = M o D] — needs the finite-dimensional extension argument
    and is deliberately left for a later unit, alongside construction of
    the unique intrinsic descended map on [im D].
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QObstruction.

(** ** 1. Lifting-obstruction vanishing is exactly repair existence

    [lift_obstruction_zero D r] already unfolds, through [linear_image],
    to exactly this existential — the two sides are the same
    proposition once unfolded. *)

Theorem lift_obstruction_zero_iff_repair
    {nU nV : nat}
    (D : QLinearMap nU nV)
    (r : QVec nV) :
  lift_obstruction_zero D r <-> exists u : QVec nU, lmap D u = r.
Proof.
  unfold lift_obstruction_zero, linear_image.
  split; intro H; exact H.
Qed.

(** ** "L(ker D) = 0" and "ker D subset ker L", stated pointwise

    Kept as two separate names, even though they turn out to unfold to
    the same universally-quantified statement (Theorem 3 below), because
    they record two different intended readings of the same fact:
    [vanishes_on_kernel] reads as a vanishing condition on values,
    [kernel_included] reads as a subset relation between kernels.
    [vanishes_on_kernel] names a *condition* only — no descended map has
    been constructed at this point, and this predicate does not claim
    one exists. Descent becomes a theorem, not a definition, once Unit
    10 constructs the intrinsic map on [im D]. *)

Definition vanishes_on_kernel
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    : Prop :=
  forall k : QVec nU,
    kernel D k ->
    lmap L k = zero_vec nW.

Definition kernel_included
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    : Prop :=
  forall k : QVec nU,
    kernel D k ->
    kernel L k.

(** ** 2. Ambient factorisation implies kernel vanishing

    The easy direction: given an explicit [M] with [L = M o D]
    pointwise, [L] vanishes on [ker D] because [D] already does, and
    [M] preserves zero. No finite-dimensional argument is needed here —
    that is only required for the converse, existence of such an [M]
    from kernel vanishing alone. *)

Theorem factorisation_implies_kernel_vanishing
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    (M : QLinearMap nV nW)
    (HLM : same_lmap L (precompose D M)) :
  vanishes_on_kernel D L.
Proof.
  unfold vanishes_on_kernel.
  intros k Hk.
  rewrite (HLM k).
  change (lmap M (lmap D k) = zero_vec nW).
  unfold kernel in Hk.
  rewrite Hk.
  apply lmap_preserves_zero.
Qed.

(** ** 3. Vanishing on the kernel is the same as kernel inclusion

    Both sides unfold to
    [forall k, lmap D k = zero_vec nV -> lmap L k = zero_vec nW] —
    the same proposition, since [kernel L k] is exactly
    [lmap L k = zero_vec nW]. *)

Theorem vanishes_on_kernel_iff_kernel_included
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW) :
  vanishes_on_kernel D L <-> kernel_included D L.
Proof.
  unfold vanishes_on_kernel, kernel_included, kernel.
  split; intro H; exact H.
Qed.
