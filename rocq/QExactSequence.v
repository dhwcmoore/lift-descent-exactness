(** * The descent short exact sequence

    [[
      0 -> ker D --i--> U --D~--> im D -> 0
    ]]

    where [i := subspace_inclusion (kernel_subspace D)] and
    [D~ := tilde_D D]. This unit states and proves that this sequence is
    short exact — injective at the left, exact at the middle, surjective
    at the right — using only the typed objects Units 5 and 6 already
    built. It introduces neither obstruction space nor any factorisation
    result; those are later units' work.
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspaceMap.

(** ** Injectivity on a designated domain

    Both membership hypotheses are required: [QLinearMapFrom] places no
    constraint outside [S], so unrestricted injectivity would be the
    wrong notion. *)

Definition injective_from
    {n m : nat}
    {S : QSubspace n}
    (F : QLinearMapFrom n m S)
    : Prop :=
  forall x y : QVec n,
    subspace_mem S x ->
    subspace_mem S y ->
    from_map F x = from_map F y ->
    x = y.

(** ** Surjectivity onto a designated codomain *)

Definition surjective_into
    {n m : nat}
    {S : QSubspace m}
    (F : QLinearMapInto n m S)
    : Prop :=
  forall y : QVec m,
    subspace_mem S y ->
    exists x : QVec n,
      lmap (into_map F) x = y.

(** ** Exactness at the middle: [ker p = im i]

    Stated through pointwise membership, not predicate equality: [i] is
    a [QLinearMapFrom], not an ambient [QLinearMap], so its image cannot
    be phrased as [linear_image]. *)

Definition exact_at_middle
    {n m : nat}
    (S : QSubspace n)
    {R : QSubspace m}
    (i : QLinearMapFrom n n S)
    (p : QLinearMapInto n m R)
    : Prop :=
  forall u : QVec n,
    lmap (into_map p) u = zero_vec m <->
    exists k : QVec n,
      subspace_mem S k /\
      from_map i k = u.

(** ** The three conditions together *)

Definition short_exact_subspace
    {n m : nat}
    (S : QSubspace n)
    (R : QSubspace m)
    (i : QLinearMapFrom n n S)
    (p : QLinearMapInto n m R)
    : Prop :=
  injective_from i /\
  exact_at_middle S i p /\
  surjective_into p.

(** ** The descent short exact sequence itself

    Nearly tautological given how Units 5 and 6 were built:
    [subspace_mem (kernel_subspace D)] is [kernel D], [from_map
    (subspace_inclusion S)] is the identity, [subspace_mem
    (image_subspace D)] is [linear_image D], and [into_map (tilde_D D)]
    is [D] — all definitionally, not merely provably. No linearity
    calculation is needed anywhere in this proof. *)

Theorem descent_short_exact
    {nU nV : nat}
    (D : QLinearMap nU nV) :
  short_exact_subspace
    (kernel_subspace D)
    (image_subspace D)
    (subspace_inclusion (kernel_subspace D))
    (tilde_D D).
Proof.
  unfold short_exact_subspace.
  split; [| split].
  - unfold injective_from.
    intros x y _ _ Heq.
    exact Heq.
  - unfold exact_at_middle.
    intros u.
    split.
    + intros Hu.
      exists u.
      split.
      * exact Hu.
      * reflexivity.
    + intros [k [Hk Heq]].
      rewrite <- Heq.
      exact Hk.
  - unfold surjective_into.
    intros y Hy.
    exact Hy.
Qed.
