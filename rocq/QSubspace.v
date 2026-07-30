(** * Subspaces, linear images, and the image corestriction

    This module gives [\widetilde D : U \to \operatorname{im} D] an
    explicit typed representation, distinct from [D : U \to V] itself,
    without turning image elements into a dependent subtype.

    ** Why a predicate-plus-closure representation, not a subtype

    The obvious alternative is [{v : QVec m | linear_image D v}]: bundle
    each image element with its own membership proof. That would make
    equality of image elements depend on equality of their membership
    proofs — two proofs of the same [Prop] are not equal by Coq's base
    logic without proof irrelevance, which this project has deliberately
    avoided everywhere else (see [QLinearMap.v]'s note on why it does not
    need proof irrelevance). Adopting a subtype here, just for
    [\widetilde D], would import exactly the axiom the rest of the
    development avoids, for a single definition.

    Instead, a [QSubspace n] is a predicate on ordinary ambient [QVec n]
    values together with proofs that the predicate is closed under zero,
    addition, and scalar multiplication — and a map "into" a subspace is
    an ordinary ambient [QLinearMap] together with a proof that every
    output satisfies the subspace's predicate. Elements of the "image"
    are still literally [QVec] values with ordinary Leibniz equality;
    only the *proof obligation* that they lie in the image is separate,
    exactly as it already is for [linear_image] and [image_set] in
    [LinearInstance.v]. No new equality principle is needed.
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.

(** ** Subspaces *)

Record QSubspace (n : nat) : Type := mkQSubspace {
  subspace_mem : QVec n -> Prop;

  subspace_zero :
    subspace_mem (zero_vec n);

  subspace_add :
    forall x y : QVec n,
      subspace_mem x ->
      subspace_mem y ->
      subspace_mem (vadd x y);

  subspace_scale :
    forall (a : Qc) (x : QVec n),
      subspace_mem x ->
      subspace_mem (vscale a x);
}.

Arguments subspace_mem {n}.
Arguments subspace_zero {n}.
Arguments subspace_add {n}.
Arguments subspace_scale {n}.

(** ** The image of a linear map

    Same equality orientation as [image_set] in [LinearInstance.v]:
    [lmap T u = v], not [v = lmap T u]. *)

Definition linear_image {n m : nat} (T : QLinearMap n m) : QVec m -> Prop :=
  fun v => exists u : QVec n, lmap T u = v.

(** ** The image as a subspace

    All three closure witnesses are explicit: [zero_vec n] for zero
    closure, [vadd u v] for additive closure (given witnesses [u], [v]
    for the two summands), and [vscale a u] for scalar closure (given
    witness [u]). Built with [refine]/[Defined] rather than [Program] so
    every witness stays visible in the source rather than behind
    generated obligations. *)

Definition image_subspace {n m : nat} (T : QLinearMap n m) : QSubspace m.
Proof.
  refine {|
    subspace_mem := linear_image T;
    subspace_zero := _;
    subspace_add := _;
    subspace_scale := _;
  |}.
  - exists (zero_vec n).
    apply lmap_preserves_zero.
  - intros x y [u Hu] [v Hv].
    exists (vadd u v).
    rewrite (lmap_add T u v), Hu, Hv.
    reflexivity.
  - intros a x [u Hu].
    exists (vscale a u).
    rewrite (lmap_scale T a u), Hu.
    reflexivity.
Defined.

(** ** A linear map into a designated subspace *)

Record QLinearMapInto (n m : nat) (S : QSubspace m) : Type := mkQLinearMapInto {
  into_map : QLinearMap n m;

  into_mem :
    forall u : QVec n,
      subspace_mem S (lmap into_map u);
}.

Arguments into_map {n m S}.
Arguments into_mem {n m S}.

(** ** The image corestriction [\widetilde D : U \to \operatorname{im} D]

    The underlying ambient map is [D] itself, unchanged; only the
    codomain is narrowed to [image_subspace D]. The range proof uses the
    direct witness [u]: [D u] is trivially in the image of [D] via [u]
    itself, by [reflexivity]. *)

Definition tilde_D {nU nV : nat} (D : QLinearMap nU nV) :
  QLinearMapInto nU nV (image_subspace D).
Proof.
  refine {| into_map := D; into_mem := _ |}.
  intros u.
  exists u.
  reflexivity.
Defined.
