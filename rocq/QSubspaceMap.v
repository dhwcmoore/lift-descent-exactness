(** * Kernel subspaces and domain-restricted linear maps

    Unit 5 gave [\widetilde D : U \to \operatorname{im} D] an explicit
    typed codomain restriction. This unit gives the domain side of the
    same picture the typed objects it needs:

    [[
      0 -> ker D -> U --D~--> im D -> 0
    ]]

    namely [ker D] as a [QSubspace], a representation of a linear map
    whose linearity is only required on a designated domain subspace,
    the restriction of an ambient map to such a domain, and the
    inclusion of a subspace into its ambient space. It proves no
    property of these objects — exactness is Unit 7's job.

    ** Why [QLinearMapFrom] is a total ambient function, not a
       dependent function on the subspace

    The obvious alternative to a total function [QVec n -> QVec m] is a
    dependent function [forall x : QVec n, subspace_mem S x -> QVec m].
    That would let the result depend computationally on *which* proof of
    membership was supplied for a given [x], so showing two applications
    at the same [x] with different membership proofs agree would need
    proof irrelevance or a separate proof-independence condition — the
    same axiom this project has avoided everywhere else (see
    [QSubspace.v]'s note on why image elements are not a dependent
    subtype; the concern here is the mirror image of that one, on
    inputs rather than outputs). A total ambient function has no such
    dependency: its behaviour outside [S] is mathematically
    insignificant implementation detail, and equality of
    [QLinearMapFrom] values is deliberately not defined in this unit —
    later results must compare two such maps only on [S], via whatever
    relation the theorem that needs it introduces.

    ** Why no ambient [QLinearMap] field

    A linear map defined on a subspace need not already have a chosen
    ambient linear extension to the whole space. Requiring a
    [QLinearMap] field would silently assume that such an extension has
    already been supplied — exactly the extension question Phase 2
    keeps separate from the unique intrinsic map on
    [\operatorname{im} D], per the theorem ladder's distinction between
    that intrinsic map and a generally nonunique ambient [M : V -> W].
    Baking an extension into the domain-map representation now would
    quietly resolve that question before Phase 2 is ready to.
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import LinearInstance.

(** ** 1. A linear map from a designated subspace

    [from_map] is total on the ambient [QVec n]; only [from_add] and
    [from_scale] constrain its behaviour, and only on inputs satisfying
    [subspace_mem S]. No [from_zero] field: it is derivable from scalar
    preservation together with [S]'s own zero closure, the same
    reasoning [QLinearMap.v] already used to omit [lmap_zero] — adding
    it here would again be a redundant proof obligation at every
    construction site. *)

Record QLinearMapFrom (n m : nat) (S : QSubspace n) : Type := mkQLinearMapFrom {
  from_map : QVec n -> QVec m;

  from_add :
    forall x y : QVec n,
      subspace_mem S x ->
      subspace_mem S y ->
      from_map (vadd x y) = vadd (from_map x) (from_map y);

  from_scale :
    forall (a : Qc) (x : QVec n),
      subspace_mem S x ->
      from_map (vscale a x) = vscale a (from_map x);
}.

Arguments from_map {n m S}.
Arguments from_add {n m S}.
Arguments from_scale {n m S}.

(** ** 2. The kernel as a subspace

    Carrier predicate is exactly [kernel T] from [LinearInstance.v] —
    no second, independently named kernel predicate. *)

Definition kernel_subspace {n m : nat} (T : QLinearMap n m) : QSubspace n.
Proof.
  refine {|
    subspace_mem := kernel T;
    subspace_zero := _;
    subspace_add := _;
    subspace_scale := _;
  |}.
  - apply lmap_preserves_zero.
  - intros x y Hx Hy.
    unfold kernel in *.
    rewrite (lmap_add T x y), Hx, Hy.
    apply vadd_0_r.
  - intros a x Hx.
    unfold kernel in *.
    rewrite (lmap_scale T a x), Hx.
    apply vec_ext.
    intros i.
    rewrite vscale_nth, zero_vec_nth, Qcmult_0_r.
    reflexivity.
Defined.

(** ** 3. Restriction of an ambient map to a domain subspace

    Underlying function is exactly [lmap T]; the membership hypotheses
    in [from_add]/[from_scale] go unused because [T] is already linear
    on every vector, not merely on [S]. *)

Definition restrict_domain {n m : nat} (S : QSubspace n) (T : QLinearMap n m) :
  QLinearMapFrom n m S :=
  {|
    from_map := lmap T;
    from_add := fun x y _ _ => lmap_add T x y;
    from_scale := fun a x _ => lmap_scale T a x;
  |}.

(** ** 4. Inclusion of a subspace into its ambient space

    Underlying function is the ambient identity; both closure
    obligations hold by [eq_refl] after beta reduction. One generic
    inclusion, usable as [subspace_inclusion (kernel_subspace D)] where
    the kernel inclusion is needed — no separate alias. *)

Definition subspace_inclusion {n : nat} (S : QSubspace n) : QLinearMapFrom n n S :=
  {|
    from_map := fun x => x;
    from_add := fun x y _ _ => eq_refl;
    from_scale := fun a x _ => eq_refl;
  |}.
