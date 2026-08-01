(** * An explicit projection onto [ker D] and finite kernel generators

    Unit 18a's [linear_map_image_preimage D] is a total constructive
    selector satisfying [D (linear_map_image_preimage D y) =
    linear_map_image_projection D y], but Unit 18a deliberately stopped
    short of proving it globally linear — that fact was not needed
    there. This unit proves it (by tracing linearity down through
    [pivot_preimage], the matrix-level selector, and the linear-map
    selector, in that order) and uses it to build

    [[
      K_D(x) = x - S_D(D x)
    ]]

    where [S_D] is the now-linear selector. Since [D (S_D (D x)) = D
    x] (Unit 18a), [D (K_D x) = 0] always; and since [S_D] is now known
    linear, [S_D] sends [0] to [0], so [K_D] fixes every [k in ker D].
    [K_D] is therefore an explicit projection with image exactly [ker
    D]. Composing it with each standard basis vector gives a finite
    family of kernel generators, and every kernel vector is recovered
    as a coordinate-weighted sum of them — with no claim that the
    generators are independent or form a basis.

    This unit does NOT prove: gauge-witness soundness or completeness;
    the R5 equivalence; extraction of a non-zero generator from failed
    kernel vanishing; decidability of kernel vanishing; linear
    independence of the kernel generators; that the generators form a
    basis; rank-nullity; uniqueness or canonicity of the kernel
    projection; independence from elimination order; verdict
    classification; the four-sector profile; canonical exact values;
    universal quotient recovery; ROC or PCE instantiation; or
    JSON/certificate/executable semantics. *)

From Coq Require Import List.
From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Vector.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QFiniteCoordinates.
From LiftDescent Require Import QMatrixAlgebra.
From LiftDescent Require Import QElementaryRows.
From LiftDescent Require Import QRowOperationSequence.
From LiftDescent Require Import QPivotStep.
From LiftDescent Require Import QEliminationStructure.
From LiftDescent Require Import QEliminationCorrectness.
From LiftDescent Require Import QImageProjection.
From LiftDescent Require Import QImageExtension.
From LiftDescent Require Import QImagePreimage.

Open Scope Qc_scope.

(** ** 1. Linearity of [pivot_preimage]

    By structural induction on the pivot list — the already-defined
    finite sum, not pivot correctness or any elimination invariant. *)

Theorem pivot_preimage_zero
    {m n : nat} (pivots : list (CompletedPivot m n)) :
  pivot_preimage pivots (zero_vec m) = zero_vec n.
Proof.
  induction pivots as [| p rest IH].
  - reflexivity.
  - simpl.
    rewrite zero_vec_nth.
    rewrite IH.
    apply vec_ext. intro k.
    rewrite vadd_nth, vscale_nth, zero_vec_nth.
    ring.
Qed.

Theorem pivot_preimage_add
    {m n : nat} (pivots : list (CompletedPivot m n)) (y1 y2 : QVec m) :
  pivot_preimage pivots (vadd y1 y2)
  = vadd (pivot_preimage pivots y1) (pivot_preimage pivots y2).
Proof.
  induction pivots as [| p rest IH].
  - simpl. apply vec_ext. intro k. rewrite vadd_nth, !zero_vec_nth. ring.
  - simpl.
    rewrite vadd_nth.
    rewrite IH.
    apply vec_ext. intro k.
    repeat (rewrite vadd_nth || rewrite vscale_nth).
    ring.
Qed.

Theorem pivot_preimage_scale
    {m n : nat} (pivots : list (CompletedPivot m n)) (a : Qc) (y : QVec m) :
  pivot_preimage pivots (vscale a y) = vscale a (pivot_preimage pivots y).
Proof.
  induction pivots as [| p rest IH].
  - simpl. apply vec_ext. intro k. rewrite vscale_nth, !zero_vec_nth. ring.
  - simpl.
    rewrite vscale_nth.
    rewrite IH.
    apply vec_ext. intro k.
    repeat (rewrite vadd_nth || rewrite vscale_nth).
    ring.
Qed.

(** ** 2. Linearity of the matrix-level selector

    The elimination trace and accumulated operation sequence are fixed
    parameters of [matrix_image_preimage A] — this proof never touches
    elimination correctness, only the already-established linearity of
    [image_projection A], [matrix_apply], and [pivot_preimage]. *)

Theorem matrix_image_preimage_add
    {u v : nat} (A : QMatrix v u) (y1 y2 : QVec v) :
  matrix_image_preimage A (vadd y1 y2)
  = vadd (matrix_image_preimage A y1) (matrix_image_preimage A y2).
Proof.
  unfold matrix_image_preimage.
  rewrite (lmap_add (image_projection A) y1 y2).
  rewrite (matrix_apply_add
             (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
             (lmap (image_projection A) y1) (lmap (image_projection A) y2)).
  apply pivot_preimage_add.
Qed.

Theorem matrix_image_preimage_scale
    {u v : nat} (A : QMatrix v u) (a : Qc) (y : QVec v) :
  matrix_image_preimage A (vscale a y) = vscale a (matrix_image_preimage A y).
Proof.
  unfold matrix_image_preimage.
  rewrite (lmap_scale (image_projection A) a y).
  rewrite (matrix_apply_scale
             (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
             a (lmap (image_projection A) y)).
  apply pivot_preimage_scale.
Qed.

(** ** 3. Linearity of the linear-map-level selector, packaged *)

Theorem linear_map_image_preimage_add
    {u v : nat} (D : QLinearMap u v) (y1 y2 : QVec v) :
  linear_map_image_preimage D (vadd y1 y2)
  = vadd (linear_map_image_preimage D y1) (linear_map_image_preimage D y2).
Proof.
  unfold linear_map_image_preimage.
  apply matrix_image_preimage_add.
Qed.

Theorem linear_map_image_preimage_scale
    {u v : nat} (D : QLinearMap u v) (a : Qc) (y : QVec v) :
  linear_map_image_preimage D (vscale a y) = vscale a (linear_map_image_preimage D y).
Proof.
  unfold linear_map_image_preimage.
  apply matrix_image_preimage_scale.
Qed.

Definition image_preimage_linear_map
    {u v : nat} (D : QLinearMap u v) : QLinearMap v u :=
  {|
    lmap := linear_map_image_preimage D;
    lmap_add := linear_map_image_preimage_add D;
    lmap_scale := linear_map_image_preimage_scale D;
  |}.

(** ** 4. Public selector equations, as thin wrappers around Unit 18a *)

Theorem image_preimage_linear_map_projection
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  lmap D (lmap (image_preimage_linear_map D) y) = lmap (linear_map_image_projection D) y.
Proof.
  simpl lmap.
  apply linear_map_image_preimage_projection.
Qed.

Theorem image_preimage_linear_map_on_image
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  linear_image D y -> lmap D (lmap (image_preimage_linear_map D) y) = y.
Proof.
  intro Hy.
  simpl lmap.
  apply linear_map_image_preimage_on_image.
  exact Hy.
Qed.

Theorem image_preimage_linear_map_after_map
    {u v : nat} (D : QLinearMap u v) (x : QVec u) :
  lmap D (lmap (image_preimage_linear_map D) (lmap D x)) = lmap D x.
Proof.
  apply image_preimage_linear_map_on_image.
  exists x. reflexivity.
Qed.

(** ** 5. The kernel projection [K_D = I - S_D D] *)

Definition kernel_projection_fun
    {u v : nat} (D : QLinearMap u v) (x : QVec u) : QVec u :=
  vsub x (lmap (image_preimage_linear_map D) (lmap D x)).

Lemma kernel_projection_add
    {u v : nat} (D : QLinearMap u v) (x1 x2 : QVec u) :
  kernel_projection_fun D (vadd x1 x2)
  = vadd (kernel_projection_fun D x1) (kernel_projection_fun D x2).
Proof.
  unfold kernel_projection_fun.
  rewrite (lmap_add D x1 x2).
  rewrite (lmap_add (image_preimage_linear_map D) (lmap D x1) (lmap D x2)).
  apply vec_ext. intro k.
  repeat (rewrite vadd_nth || rewrite vsub_nth).
  ring.
Qed.

Lemma kernel_projection_scale
    {u v : nat} (D : QLinearMap u v) (a : Qc) (x : QVec u) :
  kernel_projection_fun D (vscale a x) = vscale a (kernel_projection_fun D x).
Proof.
  unfold kernel_projection_fun.
  rewrite (lmap_scale D a x).
  rewrite (lmap_scale (image_preimage_linear_map D) a (lmap D x)).
  apply vec_ext. intro k.
  repeat (rewrite vscale_nth || rewrite vsub_nth).
  ring.
Qed.

Definition kernel_projection
    {u v : nat} (D : QLinearMap u v) : QLinearMap u u :=
  {|
    lmap := kernel_projection_fun D;
    lmap_add := kernel_projection_add D;
    lmap_scale := kernel_projection_scale D;
  |}.

(** ** 6. Projection properties *)

Theorem kernel_projection_in_kernel
    {u v : nat} (D : QLinearMap u v) (x : QVec u) :
  kernel D (lmap (kernel_projection D) x).
Proof.
  unfold kernel. simpl lmap. unfold kernel_projection_fun.
  rewrite (lmap_preserves_sub D x (lmap (image_preimage_linear_map D) (lmap D x))).
  rewrite (image_preimage_linear_map_after_map D x).
  apply vec_ext. intro k. rewrite vsub_nth, zero_vec_nth. ring.
Qed.

Theorem kernel_projection_fixes_kernel
    {u v : nat} (D : QLinearMap u v) (k : QVec u) :
  kernel D k -> lmap (kernel_projection D) k = k.
Proof.
  intro Hk.
  simpl lmap. unfold kernel_projection_fun.
  unfold kernel in Hk.
  rewrite Hk.
  rewrite (lmap_preserves_zero (image_preimage_linear_map D)).
  apply vec_ext. intro i. rewrite vsub_nth, zero_vec_nth. ring.
Qed.

Theorem kernel_projection_idempotent
    {u v : nat} (D : QLinearMap u v) (x : QVec u) :
  lmap (kernel_projection D) (lmap (kernel_projection D) x) = lmap (kernel_projection D) x.
Proof.
  apply kernel_projection_fixes_kernel.
  apply kernel_projection_in_kernel.
Qed.

Theorem kernel_projection_image_iff_kernel
    {u v : nat} (D : QLinearMap u v) (k : QVec u) :
  linear_image (kernel_projection D) k <-> kernel D k.
Proof.
  split.
  - intros [x Hx].
    rewrite <- Hx.
    apply kernel_projection_in_kernel.
  - intro Hk.
    exists k.
    apply kernel_projection_fixes_kernel.
    exact Hk.
Qed.

(** ** 7. Finite kernel generators *)

Definition kernel_generator
    {u v : nat} (D : QLinearMap u v) (i : Fin.t u) : QVec u :=
  lmap (kernel_projection D) (standard_basis i).

Theorem kernel_generator_in_kernel
    {u v : nat} (D : QLinearMap u v) (i : Fin.t u) :
  kernel D (kernel_generator D i).
Proof.
  unfold kernel_generator.
  apply kernel_projection_in_kernel.
Qed.

(** ** 8. Coordinate expansion through the projection

    Direct instance of the existing finite-coordinate representation
    theorem ([matrix_of_lmap_correct], Unit 11): every [QLinearMap] is
    recovered by applying the matrix of its values on the standard
    basis. Coefficients [a_i] are simply the coordinates of [x] (or,
    for a kernel vector, of [k] itself); no linear independence of the
    generators [g_i] is claimed. *)

Theorem kernel_projection_coordinate_expansion
    {u v : nat} (D : QLinearMap u v) (x : QVec u) :
  lmap (kernel_projection D) x
  = vsum (Vector.map2 vscale x (Vector.map (kernel_generator D) (all_positions u))).
Proof.
  rewrite <- (matrix_of_lmap_correct (kernel_projection D) x).
  unfold matrix_apply, matrix_of_lmap, kernel_generator.
  reflexivity.
Qed.

Theorem kernel_vector_coordinate_expansion
    {u v : nat} (D : QLinearMap u v) (k : QVec u) :
  kernel D k ->
  k = vsum (Vector.map2 vscale k (Vector.map (kernel_generator D) (all_positions u))).
Proof.
  intro Hk.
  rewrite <- (kernel_projection_coordinate_expansion D k).
  symmetry.
  apply kernel_projection_fixes_kernel.
  exact Hk.
Qed.

(** ** 9. Concrete probes *)

(** *** 9.1. Zero map: the projection acts as the identity, since
    [S_D(D x) = S_D(0) = 0] always. *)

Example probe_zero_map_projection_is_identity (x : QVec 2) :
  lmap (kernel_projection QImagePreimage.zero_D18) x = x.
Proof.
  unfold kernel_projection. simpl lmap. unfold kernel_projection_fun.
  assert (H0 : lmap QImagePreimage.zero_D18 x = zero_vec 2).
  { unfold QImagePreimage.zero_D18. simpl lmap. apply QImagePreimage.zero_mat2_apply_zero. }
  rewrite H0.
  rewrite (lmap_preserves_zero (image_preimage_linear_map QImagePreimage.zero_D18)).
  apply vec_ext. intro i. rewrite vsub_nth, zero_vec_nth. ring.
Qed.

(** *** 9.2. Identity map: the projection is the zero map, since the
    selector recovers [x] exactly ([D] is already onto). *)

Example probe_identity_projection_is_zero (x : QVec 2) :
  lmap (kernel_projection QImagePreimage.id_D18) x = zero_vec 2.
Proof.
  assert (Hid_identity : forall y : QVec 2, lmap QImagePreimage.id_D18 y = y).
  { intro y. unfold QImagePreimage.id_D18, QImagePreimage.id_map18. simpl lmap.
    apply identity_matrix_apply. }
  unfold kernel_projection. simpl lmap. unfold kernel_projection_fun.
  rewrite (Hid_identity x).
  assert (Hmem : linear_image QImagePreimage.id_D18 x).
  { exists x. apply Hid_identity. }
  pose proof (image_preimage_linear_map_on_image QImagePreimage.id_D18 x Hmem) as H.
  rewrite (Hid_identity (lmap (image_preimage_linear_map QImagePreimage.id_D18) x)) in H.
  rewrite H.
  apply vec_ext. intro i. rewrite vsub_nth, zero_vec_nth. ring.
Qed.

(** *** 9.3. Proper projection: [proj_D(x,y) = (x,0)]; the second
    standard basis vector [(0,1)] is already in [ker proj_D], so it
    survives as a non-zero kernel generator. *)

Example probe_proper_projection_second_generator_nonzero :
  kernel_generator QImagePreimage.proj_D (Fin.FS Fin.F1) <> zero_vec 2.
Proof.
  unfold kernel_generator.
  assert (Hmem : kernel QImagePreimage.proj_D (standard_basis (Fin.FS Fin.F1))).
  { unfold kernel. vm_compute. reflexivity. }
  rewrite (kernel_projection_fixes_kernel QImagePreimage.proj_D
             (standard_basis (Fin.FS Fin.F1)) Hmem).
  vm_compute. discriminate.
Qed.

(** *** 9.4. Zero-dimensional domain: [QVec 0] has a unique
    inhabitant, so the projection is trivial, and there is no
    [Fin.t 0] to index a kernel generator. *)

Example probe_dim_0_domain_projection_trivial
    {v : nat} (D : QLinearMap 0 v) (x : QVec 0) :
  lmap (kernel_projection D) x = x.
Proof. apply vec_ext. intro i. inversion i. Qed.

Example probe_dim_0_domain_no_generator
    {v : nat} (D : QLinearMap 0 v) (i : Fin.t 0) : False.
Proof. inversion i. Qed.
