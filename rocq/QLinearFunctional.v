(** * Linear functionals, coordinate detection, and the image residual

    Unit 19a supplies only the constructive finite-coordinate
    infrastructure the separator theorem (Unit 19b) needs. It
    deliberately reuses Phase 2's already-certified image projection
    ([linear_map_image_projection], Unit 17b) rather than developing
    transpose, row-space, or abstract dual-space machinery.

    The key construction: for [D : QLinearMap u v], the image
    projection [P_D : QLinearMap v v] fixes every point of
    [linear_image D]. The residual map [R_D(y) = y - P_D(y)] therefore
    vanishes exactly on [linear_image D] — and, since it is linear, a
    nonzero residual (for [y] outside the image) has some nonzero
    coordinate, whose coordinate functional composed with [R_D] gives
    the separator Unit 19b needs. Everything here is built from
    [linear_map_image_projection]'s public theorems
    ([linear_map_image_projection_in_image],
    [linear_map_image_projection_fixes_image]) — no elimination trace,
    pivot row, matrix, or row operation is inspected in this file.

    This unit does NOT prove: separator soundness; separator
    completeness; the R4 equivalence; separator normalisation;
    transpose identities; a nullspace basis; an abstract dual-space
    construction; gauge witnesses; kernel-basis extraction; verdict
    classification; the four-sector profile; canonical values; PCE
    certificate correspondence; or JSON/executable semantics. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Vector.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QMatrixAlgebra.
From LiftDescent Require Import QImageExtension.
From LiftDescent Require Import QImagePreimage.

Open Scope Qc_scope.

(** ** 1. Linear functionals as maps into the one-dimensional
    rational coordinate space — no abstract dual-space quotient. *)

Definition QLinearFunctional (n : nat) : Type :=
  QLinearMap n 1.

(** ** 2. The coordinate functional *)

Definition coordinate_functional_fun
    {n : nat} (i : Fin.t n) (x : QVec n) : QVec 1 :=
  Vector.cons Qc (Vector.nth x i) 0 (Vector.nil Qc).

Lemma coordinate_functional_add
    {n : nat} (i : Fin.t n) (x y : QVec n) :
  coordinate_functional_fun i (vadd x y)
  = vadd (coordinate_functional_fun i x) (coordinate_functional_fun i y).
Proof.
  unfold coordinate_functional_fun.
  apply vec_ext. intro k.
  pattern k. apply Fin.caseS'.
  - simpl. apply vadd_nth.
  - intro p. inversion p.
Qed.

Lemma coordinate_functional_scale
    {n : nat} (i : Fin.t n) (a : Qc) (x : QVec n) :
  coordinate_functional_fun i (vscale a x) = vscale a (coordinate_functional_fun i x).
Proof.
  unfold coordinate_functional_fun.
  apply vec_ext. intro k.
  pattern k. apply Fin.caseS'.
  - simpl. apply vscale_nth.
  - intro p. inversion p.
Qed.

Definition coordinate_functional
    {n : nat} (i : Fin.t n) : QLinearFunctional n :=
  {|
    lmap := coordinate_functional_fun i;
    lmap_add := coordinate_functional_add i;
    lmap_scale := coordinate_functional_scale i;
  |}.

Theorem coordinate_functional_value
    {n : nat} (i : Fin.t n) (x : QVec n) :
  Vector.nth (lmap (coordinate_functional i) x) Fin.F1 = Vector.nth x i.
Proof.
  reflexivity.
Qed.

(** ** 3. Constructive non-zero coordinate extraction

    By structural induction on the vector, using [Qc_eq_dec] — no
    classical logic, no choice, no
    [constructive_indefinite_description]. The zero-dimensional case
    ([QVec 0]) is vacuous: [zero_vec 0] is the unique inhabitant, so
    the premise [x <> zero_vec 0] is itself contradictory, discharged
    by [vec_ext] over the uninhabited [Fin.t 0]. *)

Theorem nonzero_vector_has_nonzero_coordinate
    {n : nat} (x : QVec n) :
  x <> zero_vec n -> exists i : Fin.t n, Vector.nth x i <> 0.
Proof.
  induction x as [| a n' x' IH].
  - intro H. exfalso. apply H. apply vec_ext. intro i. inversion i.
  - intro H.
    destruct (Qc_eq_dec a 0) as [Heq | Hneq].
    + assert (Hx' : x' <> zero_vec n').
      { intro Hz. apply H. subst a. unfold zero_vec. simpl. rewrite Hz. reflexivity. }
      destruct (IH Hx') as [i Hi].
      exists (Fin.FS i). exact Hi.
    + exists Fin.F1. exact Hneq.
Qed.

Theorem coordinate_functional_detects_nonzero
    {n : nat} (x : QVec n) (i : Fin.t n) :
  Vector.nth x i <> 0 -> lmap (coordinate_functional i) x <> zero_vec 1.
Proof.
  intros Hne Heq.
  apply Hne.
  rewrite <- (coordinate_functional_value i x).
  rewrite Heq.
  apply zero_vec_nth.
Qed.

(** ** 4. The image-residual map *)

Definition image_residual_map_fun
    {u v : nat} (D : QLinearMap u v) (y : QVec v) : QVec v :=
  vsub y (lmap (linear_map_image_projection D) y).

Lemma image_residual_map_add
    {u v : nat} (D : QLinearMap u v) (y1 y2 : QVec v) :
  image_residual_map_fun D (vadd y1 y2)
  = vadd (image_residual_map_fun D y1) (image_residual_map_fun D y2).
Proof.
  unfold image_residual_map_fun.
  rewrite (lmap_add (linear_map_image_projection D) y1 y2).
  apply vec_ext. intro i.
  rewrite !vsub_nth, !vadd_nth, !vsub_nth.
  ring.
Qed.

Lemma image_residual_map_scale
    {u v : nat} (D : QLinearMap u v) (a : Qc) (y : QVec v) :
  image_residual_map_fun D (vscale a y) = vscale a (image_residual_map_fun D y).
Proof.
  unfold image_residual_map_fun.
  rewrite (lmap_scale (linear_map_image_projection D) a y).
  apply vec_ext. intro i.
  rewrite vsub_nth, !vscale_nth, vsub_nth.
  ring.
Qed.

Definition image_residual_map
    {u v : nat} (D : QLinearMap u v) : QLinearMap v v :=
  {|
    lmap := image_residual_map_fun D;
    lmap_add := image_residual_map_add D;
    lmap_scale := image_residual_map_scale D;
  |}.

(** ** 5. The residual vanishes on the image *)

Theorem image_residual_on_image
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  linear_image D y -> lmap (image_residual_map D) y = zero_vec v.
Proof.
  intro Hy.
  simpl lmap. unfold image_residual_map_fun.
  rewrite (linear_map_image_projection_fixes_image D y Hy).
  apply vec_ext. intro i. rewrite vsub_nth, zero_vec_nth. ring.
Qed.

Theorem image_residual_after_map
    {u v : nat} (D : QLinearMap u v) (x : QVec u) :
  lmap (image_residual_map D) (lmap D x) = zero_vec v.
Proof.
  apply image_residual_on_image.
  exists x. reflexivity.
Qed.

(** ** 6. The residual characterises image membership *)

Theorem image_residual_zero_iff_image
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  lmap (image_residual_map D) y = zero_vec v <-> linear_image D y.
Proof.
  split.
  - intro H.
    simpl lmap in H. unfold image_residual_map_fun in H.
    assert (Hy : y = lmap (linear_map_image_projection D) y).
    { apply vec_ext. intro i.
      assert (Hi : Vector.nth (vsub y (lmap (linear_map_image_projection D) y)) i
                   = Vector.nth (zero_vec v) i) by (rewrite H; reflexivity).
      rewrite vsub_nth, zero_vec_nth in Hi.
      assert (Hring : Vector.nth y i
                       = Vector.nth y i - Vector.nth (lmap (linear_map_image_projection D) y) i
                         + Vector.nth (lmap (linear_map_image_projection D) y) i) by ring.
      rewrite Hi in Hring. rewrite Hring. ring. }
    rewrite Hy.
    apply linear_map_image_projection_in_image.
  - apply image_residual_on_image.
Qed.

Theorem not_image_implies_nonzero_residual
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  ~ linear_image D y -> lmap (image_residual_map D) y <> zero_vec v.
Proof.
  intros Hny Heq. apply Hny. apply image_residual_zero_iff_image. exact Heq.
Qed.

(** ** 7. Concrete probes

    Reuses Unit 18a's own zero/identity/proper-image maps rather than
    building a second collection. No elimination trace or matrix
    computation beyond what these probes' own [vm_compute] calls need
    is inspected. *)

(** *** 7.1. Zero map: the residual is the original vector. *)

Example probe_zero_map_residual_is_original :
  lmap (image_residual_map QImagePreimage.zero_D18)
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
  = Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Proof. vm_compute. reflexivity. Qed.

(** *** 7.2. Identity map: the residual is always zero. *)

Example probe_identity_residual_always_zero (y : QVec 2) :
  lmap (image_residual_map QImagePreimage.id_D18) y = zero_vec 2.
Proof.
  apply image_residual_on_image.
  exists y.
  unfold QImagePreimage.id_D18, QImagePreimage.id_map18. simpl lmap.
  apply identity_matrix_apply.
Qed.

(** *** 7.3. Proper image projection: an out-of-image vector survives
    with a nonzero residual. [proj_D(x,y) = (x,0)]; the [y]-axis
    vector [(0,1)] is not in the image, and its residual is [(0,1)]
    itself (unaffected, since the projection sends it to [(0,0)]). *)

Example probe_proper_image_out_of_image_nonzero_residual :
  lmap (image_residual_map QImagePreimage.proj_D)
    (Vector.cons Qc 0 1 (Vector.cons Qc 1 0 (Vector.nil Qc)))
  <> zero_vec 2.
Proof. vm_compute. discriminate. Qed.

(** *** 7.4. Zero-dimensional codomain: no non-zero residual can
    arise, since [QVec 0] has a unique inhabitant. *)

Example probe_dim_0_codomain_residual_zero
    {u : nat} (D : QLinearMap u 0) (y : QVec 0) :
  lmap (image_residual_map D) y = zero_vec 0.
Proof. apply vec_ext. intro i. inversion i. Qed.
