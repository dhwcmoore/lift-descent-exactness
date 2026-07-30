(** * Lift and descent obstruction predicates

    The founding documents distinguish exactly two independent
    obstruction axes:

    [[
      [r] in coker D          (lifting / realisability)
      [L] in coker D_W^*       (descent), D_W^*(M) = M o D
    ]]

    An ambient map [M : V -> W] is a *witness* that the second class
    vanishes — [L] lies in the image of precomposition by [D] — not a
    third, independently named obstruction. This unit formalises only
    the zero/nonzero status of these two classes as propositions. It
    does not construct a quotient carrier type for either cokernel, does
    not state the R2 factorisation equivalences, and does not begin the
    three-way classification — those are later units' work.

    ** Why [same_lmap], not Leibniz equality on [QLinearMap]

    Two [QLinearMap] records being Leibniz-equal would also compare
    their [lmap_add]/[lmap_scale] proof fields, not just their
    underlying functions — precisely the redundant, proof-sensitive
    equality this project has avoided at every prior unit (see
    [QLinearMap.v]'s and [QSubspaceMap.v]'s notes on the same concern
    for other constructions). [same_lmap] states the mathematically
    meaningful content directly: two maps agree pointwise.
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QSubspace.

(** ** Pointwise equality of linear maps *)

Definition same_lmap
    {n m : nat}
    (F G : QLinearMap n m)
    : Prop :=
  forall x : QVec n,
    lmap F x = lmap G x.

(** ** Precomposition by [D]

    [precompose D M] is [M] applied after [D]; its underlying function
    is exactly [fun u => lmap M (lmap D u)]. *)

Definition precompose
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (M : QLinearMap nV nW)
    : QLinearMap nU nW.
Proof.
  refine {|
    lmap := fun u => lmap M (lmap D u);
    lmap_add := _;
    lmap_scale := _;
  |}.
  - intros x y.
    rewrite (lmap_add D x y).
    apply (lmap_add M).
  - intros a x.
    rewrite (lmap_scale D a x).
    apply (lmap_scale M).
Defined.

(** ** Membership in the image of precomposition by [D]

    States pointwise that [L] factors as [M] composed with [D]:
    [same_lmap L (precompose D M)], not equality of [QLinearMap]
    records. The witness [M] is not claimed unique — ambient extensions
    are generally nonunique outside [image D]; that is exactly the
    distinction the theorem ladder draws between the unique intrinsic
    map on [im D] and a generally nonunique ambient [M : V -> W]. *)

Definition precomposition_image
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    : Prop :=
  exists M : QLinearMap nV nW,
    same_lmap L (precompose D M).

(** ** Vanishing of the lifting obstruction: [ [r] = 0 in coker D ]

    A residue represents the zero cokernel class exactly when it lies
    in [im D]; reuses [linear_image] from [QSubspace.v] rather than a
    second, independently named image predicate. *)

Definition lift_obstruction_zero
    {nU nV : nat}
    (D : QLinearMap nU nV)
    (r : QVec nV)
    : Prop :=
  linear_image D r.

(** ** Vanishing of the descent obstruction: [ [L] = 0 in coker D_W^* ]

    [L] represents the zero cokernel class exactly when it lies in the
    image of precomposition by [D]. This is deliberately not defined as
    [L] vanishing on [ker D]; that intrinsic characterisation is
    equivalent, but the equivalence is an R2 theorem for a later unit,
    not a definition here. *)

Definition descent_obstruction_zero
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    : Prop :=
  precomposition_image D L.

(** ** [ [r] <> 0 in coker D ] *)

Definition lift_obstructed
    {nU nV : nat}
    (D : QLinearMap nU nV)
    (r : QVec nV)
    : Prop :=
  ~ lift_obstruction_zero D r.

(** ** [ [L] <> 0 in coker D_W^* ] *)

Definition descent_obstructed
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    : Prop :=
  ~ descent_obstruction_zero D L.
