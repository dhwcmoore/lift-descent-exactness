(** * The intrinsic descended map, as a functional linear graph on [im D]

    Kernel vanishing determines a unique value of the intended intrinsic
    map [D u |-> L u] on every point of [im D], but it does not supply a
    total ambient function [QVec nV -> QVec nW]: constructing one would
    mean choosing a preimage for every [v in im D] (a selection problem)
    and choosing values outside [im D] (an extension problem), neither
    of which follows from [vanishes_on_kernel D L] alone — both need
    further finite-dimensional machinery this unit does not have yet.

    What kernel vanishing *does* give constructively, with the
    existential witnesses already in hand, is a relation on [QVec nV *
    QVec nW] that is total and single-valued on [im D]: the functional
    linear graph [descent_graph D L]. This is the exact object available
    at this point — not a workaround for the absence of a
    [QLinearMapFrom], but the correct representation of "an intrinsic
    linear map on [im D]" before any selection or extension theorem has
    been proved. [QLinearMapFrom]'s total ambient function is reserved
    for the ambient-extension unit, which is separate and later.
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspaceMap.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QDescentBasics.

(** ** 1. A functional linear graph on a designated domain subspace

    Meaningful only on [S]: no totality or functionality is asserted,
    or needed, outside it. *)

Record QLinearMapGraphFrom (n m : nat) (S : QSubspace n) : Type := mkQLinearMapGraphFrom {
  graph_rel : QVec n -> QVec m -> Prop;

  graph_total :
    forall x : QVec n,
      subspace_mem S x ->
      exists y : QVec m,
        graph_rel x y;

  graph_functional :
    forall (x : QVec n) (y1 y2 : QVec m),
      subspace_mem S x ->
      graph_rel x y1 ->
      graph_rel x y2 ->
      y1 = y2;

  graph_zero :
    graph_rel (zero_vec n) (zero_vec m);

  graph_add :
    forall (x1 x2 : QVec n) (y1 y2 : QVec m),
      subspace_mem S x1 ->
      subspace_mem S x2 ->
      graph_rel x1 y1 ->
      graph_rel x2 y2 ->
      graph_rel (vadd x1 x2) (vadd y1 y2);

  graph_scale :
    forall (a : Qc) (x : QVec n) (y : QVec m),
      subspace_mem S x ->
      graph_rel x y ->
      graph_rel (vscale a x) (vscale a y);
}.

Arguments graph_rel {n m S}.
Arguments graph_total {n m S}.
Arguments graph_functional {n m S}.
Arguments graph_zero {n m S}.
Arguments graph_add {n m S}.
Arguments graph_scale {n m S}.

(** ** 2. Extensional equality of two graph maps, on their domain *)

Definition same_graph_on
    {n m : nat}
    {S : QSubspace n}
    (F G : QLinearMapGraphFrom n m S)
    : Prop :=
  forall (x : QVec n),
    subspace_mem S x ->
    forall y : QVec m,
      graph_rel F x y <-> graph_rel G x y.

(** ** 3. The graph of the intended map [D u |-> L u] *)

Definition descent_graph
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    (v : QVec nV)
    (w : QVec nW)
    : Prop :=
  exists u : QVec nU,
    lmap D u = v /\ lmap L u = w.

(** ** 4. The commuting condition a graph map must satisfy *)

Definition descent_compatible
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    (G : QLinearMapGraphFrom nV nW (image_subspace D))
    : Prop :=
  forall u : QVec nU,
    graph_rel G (lmap D u) (lmap L u).

(** ** 5. Construction of the intrinsic descended map *)

Definition intrinsic_descent
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    (Hvanish : vanishes_on_kernel D L)
    : QLinearMapGraphFrom nV nW (image_subspace D).
Proof.
  refine {|
    graph_rel := descent_graph D L;
    graph_total := _;
    graph_functional := _;
    graph_zero := _;
    graph_add := _;
    graph_scale := _;
  |}.
  - (* totality: reuse the image-membership witness directly *)
    intros v Hv.
    destruct Hv as [u Hu].
    exists (lmap L u).
    exists u.
    split.
    + exact Hu.
    + reflexivity.
  - (* functionality: the displacement vsub u1 u2 lies in ker D *)
    intros v w1 w2 _ [u1 [Hu1v Hu1w]] [u2 [Hu2v Hu2w]].
    assert (Hker : kernel D (vsub u1 u2)).
    { unfold kernel.
      rewrite (lmap_preserves_sub D u1 u2).
      rewrite Hu1v, Hu2v.
      rewrite vsub_def.
      apply vadd_opp_r. }
    pose proof (Hvanish (vsub u1 u2) Hker) as HL0.
    rewrite (lmap_preserves_sub L u1 u2) in HL0.
    rewrite Hu1w, Hu2w in HL0.
    rewrite <- (vadd_0_r w1).
    rewrite <- (vadd_opp_l w2).
    rewrite <- vadd_assoc.
    rewrite <- vsub_def.
    rewrite HL0.
    apply vadd_0_l.
  - (* zero: witness zero_vec nU *)
    exists (zero_vec nU).
    split.
    + apply (lmap_preserves_zero D).
    + apply (lmap_preserves_zero L).
  - (* addition: witness vadd u1 u2 *)
    intros x1 x2 y1 y2 _ _ [u1 [Hu1x Hu1y]] [u2 [Hu2x Hu2y]].
    exists (vadd u1 u2).
    split.
    + rewrite (lmap_add D u1 u2), Hu1x, Hu2x. reflexivity.
    + rewrite (lmap_add L u1 u2), Hu1y, Hu2y. reflexivity.
  - (* scaling: witness vscale a u *)
    intros a x y _ [u [Hux Huy]].
    exists (vscale a u).
    split.
    + rewrite (lmap_scale D a u), Hux. reflexivity.
    + rewrite (lmap_scale L a u), Huy. reflexivity.
Defined.

(** ** 6. The intrinsic descended map is compatible *)

Theorem intrinsic_descent_compatible
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    (Hvanish : vanishes_on_kernel D L) :
  descent_compatible D L (intrinsic_descent D L Hvanish).
Proof.
  unfold descent_compatible.
  intros u.
  change (descent_graph D L (lmap D u) (lmap L u)).
  exists u.
  split; reflexivity.
Qed.

(** ** 7. Uniqueness: any compatible graph map agrees with the
    intrinsic one on [im D] *)

Theorem intrinsic_descent_unique
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW)
    (Hvanish : vanishes_on_kernel D L)
    (G : QLinearMapGraphFrom nV nW (image_subspace D))
    (HG : descent_compatible D L G) :
  same_graph_on G (intrinsic_descent D L Hvanish).
Proof.
  unfold same_graph_on.
  intros v Hv w.
  assert (Hv' := Hv).
  destruct Hv' as [u Hu].
  split.
  - intro HGvw.
    pose proof (HG u) as HGu.
    rewrite Hu in HGu.
    assert (Heq : w = lmap L u) by
      exact (graph_functional G v w (lmap L u) Hv HGvw HGu).
    rewrite Heq.
    change (descent_graph D L v (lmap L u)).
    exists u.
    split; [exact Hu | reflexivity].
  - intro Hintr.
    change (descent_graph D L v w) in Hintr.
    destruct Hintr as [u' [Hu'v Hu'w]].
    pose proof (HG u') as HGu'.
    rewrite Hu'v, Hu'w in HGu'.
    exact HGu'.
Qed.

(** ** 8. Kernel vanishing is equivalent to existence of a compatible
    intrinsic graph map *)

Theorem vanishes_on_kernel_iff_intrinsic_descent
    {nU nV nW : nat}
    (D : QLinearMap nU nV)
    (L : QLinearMap nU nW) :
  vanishes_on_kernel D L <->
  exists G : QLinearMapGraphFrom nV nW (image_subspace D),
    descent_compatible D L G.
Proof.
  split.
  - intro Hvanish.
    exists (intrinsic_descent D L Hvanish).
    apply intrinsic_descent_compatible.
  - intros [G HG].
    unfold vanishes_on_kernel.
    intros k Hk.
    pose proof (HG k) as HGk.
    unfold kernel in Hk.
    rewrite Hk in HGk.
    exact (graph_functional G (zero_vec nV) (lmap L k) (zero_vec nW)
             (subspace_zero (image_subspace D)) HGk (graph_zero G)).
Qed.
