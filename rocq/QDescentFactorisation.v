(** * The finite-rational descent factorisation equivalence

    Units 17a, 17b and 18a supplied the missing constructive machinery
    for the R2 descent equivalence: an elimination-derived projection
    onto [image_subspace D] (Unit 17a); a constructive ambient
    extension of any map defined on [image_subspace D] (Unit 17b); and
    a constructive preimage selector together with the actual induced
    map [induced_image_map D L H] on [image_subspace D], satisfying
    [induced_image_map_after_map] (Unit 18a). This unit is the final
    glue: it composes those two interfaces into an ambient factor map,
    and proves the finite-rational form of R2 —

    [[
      L vanishes on ker D
      <-> ker D subset ker L
      <-> exists M, L = M o D          (precomposition_image D L)
      <-> descent_obstruction_zero D L
    ]]

    together with extensional existence-and-uniqueness of the intrinsic
    map on [image_subspace D].

    This unit does NOT prove: a quotient carrier for [coker D] or
    [coker D_W^*]; the canonical isomorphism [coker D_W^* ≅ Hom(ker D,
    W)] as an isomorphism of constructed quotient objects; uniqueness
    of the ambient extension [M] (only of the intrinsic map on the
    image); Leibniz equality of [QLinearMap] or [QLinearMapFrom]
    records; obstruction or underdetermination witnesses; the
    operational three-way classification; the canonical exact value
    theorem; rank-nullity; generalisation beyond finite rational
    coordinate spaces; classical or choice-based preimage selection; or
    elimination-independence/canonicality of the selected extension.

    Phase 2 is complete, under this scope, at the level of the descent
    exact sequence, intrinsic image factorisation, constructive ambient
    extension, and the equivalence between kernel vanishing, kernel
    inclusion, ambient factorisation, and descent-obstruction
    vanishing. Quotient carrier constructions and the canonical
    cokernel isomorphism remain outside the implemented scope; Phase 3
    moves from structural equivalence to witnesses and classification. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QSubspaceMap.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QDescentBasics.
From LiftDescent Require Import QImageExtension.
From LiftDescent Require Import QImagePreimage.

Open Scope Qc_scope.

(** ** 1. Bridging the two [vanishes_on_kernel] constants

    [QDescentBasics.vanishes_on_kernel] and
    [QImagePreimage.vanishes_on_kernel] have the identical body
    ([forall k, kernel D k -> lmap L k = zero_vec w]) but are distinct
    constants, since Unit 18a did not import Unit 9's definition. The
    bridge is definitional; every subsequent statement in this file
    uses the qualified names throughout to avoid relying on import
    order for disambiguation. *)

Theorem image_preimage_vanishing_iff_descent_vanishing
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  QImagePreimage.vanishes_on_kernel D L <->
  QDescentBasics.vanishes_on_kernel D L.
Proof.
  split; intro H; exact H.
Qed.

(** ** 2. The ambient factor map, by composing the two sealed
    interfaces *)

Definition induced_ambient_map
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (H : QImagePreimage.vanishes_on_kernel D L)
    : QLinearMap v w :=
  extend_from_image D (induced_image_map D L H).

Theorem induced_ambient_map_after_map
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (H : QImagePreimage.vanishes_on_kernel D L)
    (x : QVec u) :
  lmap (induced_ambient_map D L H) (lmap D x) = lmap L x.
Proof.
  unfold induced_ambient_map.
  rewrite (extend_from_image_after_map D (induced_image_map D L H) x).
  apply induced_image_map_after_map.
Qed.

Theorem induced_ambient_map_factorisation
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (H : QImagePreimage.vanishes_on_kernel D L) :
  same_lmap L (precompose D (induced_ambient_map D L H)).
Proof.
  intro x.
  change (lmap L x = lmap (induced_ambient_map D L H) (lmap D x)).
  symmetry.
  apply induced_ambient_map_after_map.
Qed.

(** ** 3. Kernel vanishing implies ambient factorisation

    The difficult direction; all of the actual difficulty was already
    discharged by Units 11-18a. This is a two-line witness supply. *)

Theorem kernel_vanishing_implies_precomposition_image
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  QImagePreimage.vanishes_on_kernel D L ->
  precomposition_image D L.
Proof.
  intro H.
  exists (induced_ambient_map D L H).
  apply induced_ambient_map_factorisation.
Qed.

(** ** 4. Ambient factorisation implies kernel vanishing

    The easy direction, proved directly (three lines) rather than via
    the bridge theorem — the same argument as
    [QDescentBasics.factorisation_implies_kernel_vanishing], restated
    here so this file's [precomposition_image]-facing statement does
    not require an extra predicate conversion step. *)

Theorem precomposition_image_implies_kernel_vanishing
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  precomposition_image D L ->
  QImagePreimage.vanishes_on_kernel D L.
Proof.
  intros [M HM] k Hk.
  rewrite (HM k).
  change (lmap M (lmap D k) = zero_vec w).
  unfold kernel in Hk.
  rewrite Hk.
  apply lmap_preserves_zero.
Qed.

(** ** 5. The central factorisation equivalence *)

Theorem kernel_vanishing_iff_precomposition_image
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  QImagePreimage.vanishes_on_kernel D L <-> precomposition_image D L.
Proof.
  split.
  - apply kernel_vanishing_implies_precomposition_image.
  - apply precomposition_image_implies_kernel_vanishing.
Qed.

Theorem kernel_vanishing_iff_ambient_factorisation
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  QImagePreimage.vanishes_on_kernel D L <->
  exists M : QLinearMap v w, same_lmap L (precompose D M).
Proof.
  apply kernel_vanishing_iff_precomposition_image.
Qed.

(** ** 6. Connection to the descent obstruction predicate *)

Theorem descent_obstruction_zero_iff_kernel_vanishing
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  descent_obstruction_zero D L <-> QImagePreimage.vanishes_on_kernel D L.
Proof.
  unfold descent_obstruction_zero.
  symmetry.
  apply kernel_vanishing_iff_precomposition_image.
Qed.

Theorem descent_obstructed_iff_not_kernel_vanishing
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  descent_obstructed D L <-> ~ QImagePreimage.vanishes_on_kernel D L.
Proof.
  unfold descent_obstructed.
  split.
  - intros H HV. apply H. apply (descent_obstruction_zero_iff_kernel_vanishing D L). exact HV.
  - intros H HD. apply H. apply (descent_obstruction_zero_iff_kernel_vanishing D L). exact HD.
Qed.

(** ** 7. Connection to kernel inclusion *)

Theorem descent_obstruction_zero_iff_kernel_included
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  descent_obstruction_zero D L <-> kernel_included D L.
Proof.
  rewrite (descent_obstruction_zero_iff_kernel_vanishing D L).
  rewrite (image_preimage_vanishing_iff_descent_vanishing D L).
  apply vanishes_on_kernel_iff_kernel_included.
Qed.

(** ** 8. Extensional existence and uniqueness of the intrinsic map *)

Definition same_from_map
    {v w : nat}
    {S : QSubspace v}
    (T1 T2 : QLinearMapFrom v w S)
    : Prop :=
  forall y, subspace_mem S y -> from_map T1 y = from_map T2 y.

Definition image_factorisation
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (T : QLinearMapFrom v w (image_subspace D))
    : Prop :=
  forall x, from_map T (lmap D x) = lmap L x.

Theorem induced_image_map_factorises
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (H : QImagePreimage.vanishes_on_kernel D L) :
  image_factorisation D L (induced_image_map D L H).
Proof.
  intro x.
  apply induced_image_map_after_map.
Qed.

Theorem induced_image_map_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (H : QImagePreimage.vanishes_on_kernel D L)
    (T : QLinearMapFrom v w (image_subspace D)) :
  image_factorisation D L T ->
  same_from_map T (induced_image_map D L H).
Proof.
  intros HT y Hy.
  destruct Hy as [x Hx].
  rewrite <- Hx.
  rewrite (HT x).
  symmetry.
  apply induced_image_map_after_map.
Qed.

Theorem intrinsic_image_factorisation_exists_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (H : QImagePreimage.vanishes_on_kernel D L) :
  exists T : QLinearMapFrom v w (image_subspace D),
    image_factorisation D L T /\
    forall T', image_factorisation D L T' -> same_from_map T' T.
Proof.
  exists (induced_image_map D L H).
  split.
  - apply induced_image_map_factorises.
  - intros T' HT'.
    apply induced_image_map_unique.
    exact HT'.
Qed.

(** ** 9. Concrete probes

    Reuses Unit 18a's own probe matrices/maps (zero, identity, proper
    projection, failure case, zero-dimensional) rather than building a
    second collection; this file's probes exercise only the theorem-
    facing interface established above. *)

(** *** 9.1. Zero map: ambient factorisation exists only when [L]
    vanishes everywhere. *)

Example probe_zero_map_precomposition_image
    (L : QLinearMap 2 2) (H : QImagePreimage.vanishes_on_kernel zero_D18 L) :
  precomposition_image zero_D18 L.
Proof. apply kernel_vanishing_implies_precomposition_image. exact H. Qed.

Example probe_zero_map_L_is_zero
    (L : QLinearMap 2 2) (H : QImagePreimage.vanishes_on_kernel zero_D18 L)
    (x : QVec 2) :
  lmap L x = zero_vec 2.
Proof. apply probe_zero_forces_L_zero. exact H. Qed.

(** *** 9.2. Identity map: every [L] factors through the identity. *)

Example probe_identity_always_factors (L : QLinearMap 2 2) :
  QImagePreimage.vanishes_on_kernel id_D18 L -> precomposition_image id_D18 L.
Proof. apply kernel_vanishing_implies_precomposition_image. Qed.

(** *** 9.3. Proper projection: [D(x,y)=(x,0)], [L(x,y)=x] — reusing
    Unit 18a's [probe_proj_kernel_vanishing] witness directly. *)

Example probe_proper_projection_descent_obstruction_zero :
  descent_obstruction_zero proj_D L_map.
Proof.
  apply descent_obstruction_zero_iff_kernel_vanishing.
  apply probe_proj_kernel_vanishing.
Qed.

Example probe_proper_projection_kernel_included :
  kernel_included proj_D L_map.
Proof.
  apply descent_obstruction_zero_iff_kernel_included.
  apply probe_proper_projection_descent_obstruction_zero.
Qed.

(** *** 9.4. Failure case: [L'(x,y)=y] is not kernel-vanishing for the
    same [D] — reusing Unit 18a's [probe_Lp_not_kernel_vanishing]. *)

Example probe_failure_not_descent_obstruction_zero :
  ~ descent_obstruction_zero proj_D Lp_map.
Proof.
  intro H.
  apply probe_Lp_not_kernel_vanishing.
  apply (descent_obstruction_zero_iff_kernel_vanishing proj_D Lp_map).
  exact H.
Qed.

Example probe_failure_descent_obstructed :
  descent_obstructed proj_D Lp_map.
Proof.
  apply descent_obstructed_iff_not_kernel_vanishing.
  exact probe_Lp_not_kernel_vanishing.
Qed.

(** *** 9.5. Zero-dimensional boundary *)

Example probe_dim_0_0_factorisation_iff
    (L : QLinearMap 0 0) :
  QImagePreimage.vanishes_on_kernel dim00_D18 L <-> precomposition_image dim00_D18 L.
Proof. apply kernel_vanishing_iff_precomposition_image. Qed.
