(** * Constructive image preimages and the kernel-vanishing induced map

    Constructing [T : QLinearMapFrom v w (image_subspace D)] from a
    kernel-vanishing hypothesis needs [from_map : QVec v -> QVec w] to
    be an actual total function. Membership [linear_image D y] is only
    a propositional existential ([exists x, lmap D x = y]); Coq's base
    logic does not let that existential be eliminated into
    computational data of type [QVec u] without first having a
    computational preimage selector in hand. This unit builds exactly
    that selector — reusing Unit 17a's own elimination-derived
    [pivot_preimage] machinery, not a choice axiom — and uses it,
    together with a kernel-vanishing hypothesis, to build a
    genuinely well-defined [QLinearMapFrom (image_subspace D) w].

    Unit 17a's [image_projection]/[image_projection_in_image]/
    [image_projection_fixes_image], Unit 17b's
    [linear_map_image_projection] family, and Unit 16's elimination-
    correctness theorems are used as a sealed interface: this file
    never reproduces column locking, pivot-row support induction,
    coordinate projection, or the [P^{-1}CP] conjugation proof. The
    only elimination-specific step here is converting an already-
    projected, already-supported vector into a domain preimage via
    [pivot_preimage] itself.

    This unit does NOT prove: global linearity of the raw preimage
    selector; uniqueness of selected preimages; a right or two-sided
    inverse of [D]; injectivity or surjectivity of [D]; rank-nullity;
    a quotient-space construction; uniqueness of the induced map as a
    record; an ambient extension of the induced map (Unit 18b);
    existence of an ambient [M] with [L = M ∘ D] (Unit 18b); necessity
    or sufficiency of kernel vanishing for ambient factorisation
    (Unit 18b); the descent- or lift-obstruction equivalence; canonical
    or elimination-independent preimage selection; orthogonality or
    numerical stability; or any result beyond finite rational
    coordinate spaces.

    The strongest conclusion here is: kernel vanishing makes the
    explicit selected-preimage function into a well-defined linear map
    on [image_subspace D], and that map agrees with [L] after [D]. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QSubspaceMap.
From LiftDescent Require Import QFiniteCoordinates.
From LiftDescent Require Import QMatrixAlgebra.
From LiftDescent Require Import QElementaryRows.
From LiftDescent Require Import QRowOperationSequence.
From LiftDescent Require Import QPivotStep.
From LiftDescent Require Import QEliminationStructure.
From LiftDescent Require Import QEliminationCorrectness.
From LiftDescent Require Import QImageProjection.
From LiftDescent Require Import QImageExtension.

Open Scope Qc_scope.

(** ** 1. Kernel vanishing *)

Definition vanishes_on_kernel
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : Prop :=
  forall k,
    kernel D k ->
    lmap L k = zero_vec w.

(** ** 2. The matrix-level preimage selector

    All components are read off the single [run_elimination A] result
    (never recomputed independently), via [pivot_preimage] applied to
    the accumulated-transformation image of the projected vector. *)

Definition matrix_image_preimage
    {u v : nat}
    (A : QMatrix v u)
    (y : QVec v)
    : QVec u :=
  pivot_preimage
    (completed_pivots (elimination_trace (run_elimination A)))
    (matrix_apply
       (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
       (lmap (image_projection A) y)).

(** ** 3. The projected, transformed vector lies in, and is supported
    according to, the final image — bridging to
    [matrix_apply_pivot_preimage] without reproducing its induction. *)

Theorem projected_transformed_vector_in_final_image
    {u v : nat} (A : QMatrix v u) (y : QVec v) :
  linear_image
    (linear_map_of_matrix (elimination_matrix (run_elimination A)))
    (matrix_apply
       (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
       (lmap (image_projection A) y)).
Proof.
  destruct (image_projection_in_image A y) as [x Hx].
  simpl lmap in Hx.
  exists x.
  simpl lmap.
  rewrite (run_elimination_correct A).
  rewrite matrix_compose_apply.
  rewrite Hx.
  reflexivity.
Qed.

Theorem projected_transformed_vector_supported
    {u v : nat} (A : QMatrix v u) (y : QVec v) :
  supported_on
    (pivot_rows (elimination_trace (run_elimination A)))
    (matrix_apply
       (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
       (lmap (image_projection A) y)).
Proof.
  apply final_image_supported.
  apply projected_transformed_vector_in_final_image.
Qed.

(** ** 4. The central matrix-level preimage theorem *)

Theorem matrix_image_preimage_projection
    {u v : nat} (A : QMatrix v u) (y : QVec v) :
  matrix_apply A (matrix_image_preimage A y) = lmap (image_projection A) y.
Proof.
  unfold matrix_image_preimage.
  assert (Hstep1 :
    matrix_apply (elimination_matrix (run_elimination A))
      (pivot_preimage
         (completed_pivots (elimination_trace (run_elimination A)))
         (matrix_apply
            (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
            (lmap (image_projection A) y)))
    = matrix_apply
        (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
        (lmap (image_projection A) y)).
  { apply matrix_apply_pivot_preimage.
    - intros p Hp. apply run_elimination_completed_pivots. exact Hp.
    - apply run_elimination_pivot_rows_nodup.
    - apply projected_transformed_vector_supported. }
  rewrite (run_elimination_correct A) in Hstep1.
  rewrite matrix_compose_apply in Hstep1.
  assert (Hcancel :
    matrix_apply
      (row_operation_sequence_matrix
         (inverse_row_operation_sequence (elimination_operations (run_elimination A))))
      (matrix_apply
         (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
         (matrix_apply A
            (pivot_preimage
               (completed_pivots (elimination_trace (run_elimination A)))
               (matrix_apply
                  (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
                  (lmap (image_projection A) y)))))
    = matrix_apply
        (row_operation_sequence_matrix
           (inverse_row_operation_sequence (elimination_operations (run_elimination A))))
        (matrix_apply
           (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
           (lmap (image_projection A) y))).
  { f_equal. exact Hstep1. }
  rewrite <-
    (matrix_compose_apply
       (row_operation_sequence_matrix
          (inverse_row_operation_sequence (elimination_operations (run_elimination A))))
       (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
       (matrix_apply A
          (pivot_preimage
             (completed_pivots (elimination_trace (run_elimination A)))
             (matrix_apply
                (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
                (lmap (image_projection A) y)))))
    in Hcancel.
  rewrite <-
    (matrix_compose_apply
       (row_operation_sequence_matrix
          (inverse_row_operation_sequence (elimination_operations (run_elimination A))))
       (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
       (lmap (image_projection A) y))
    in Hcancel.
  destruct
    (row_operation_sequence_inverse_pair
       (elimination_operations (run_elimination A))
       (run_elimination_sequence_valid A))
    as [_ H2].
  rewrite H2 in Hcancel.
  rewrite (identity_matrix_apply
             (matrix_apply A
                (pivot_preimage
                   (completed_pivots (elimination_trace (run_elimination A)))
                   (matrix_apply
                      (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
                      (lmap (image_projection A) y)))))
    in Hcancel.
  rewrite (identity_matrix_apply (lmap (image_projection A) y)) in Hcancel.
  exact Hcancel.
Qed.

Theorem matrix_image_preimage_on_image
    {u v : nat} (A : QMatrix v u) (y : QVec v) :
  linear_image (linear_map_of_matrix A) y ->
  matrix_apply A (matrix_image_preimage A y) = y.
Proof.
  intro Hy.
  rewrite (matrix_image_preimage_projection A y).
  apply image_projection_fixes_image.
  exact Hy.
Qed.

(** ** 5. The linear-map-level selector

    A total function, not yet claimed linear — passes through the
    matrix representation exactly as [linear_map_image_projection]
    does. *)

Definition linear_map_image_preimage
    {u v : nat} (D : QLinearMap u v) (y : QVec v) : QVec u :=
  matrix_image_preimage (matrix_of_lmap D) y.

Theorem linear_map_image_preimage_projection
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  lmap D (linear_map_image_preimage D y) = lmap (linear_map_image_projection D) y.
Proof.
  unfold linear_map_image_preimage, linear_map_image_projection.
  rewrite <- (matrix_of_lmap_correct D (matrix_image_preimage (matrix_of_lmap D) y)).
  apply matrix_image_preimage_projection.
Qed.

Theorem linear_map_image_preimage_on_image
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  linear_image D y -> lmap D (linear_map_image_preimage D y) = y.
Proof.
  intro Hy.
  rewrite (linear_map_image_preimage_projection D y).
  apply linear_map_image_projection_fixes_image.
  exact Hy.
Qed.

(** ** 6. Kernel invariance *)

Lemma vsub_eq_zero {n : nat} (x y : QVec n) : vsub x y = zero_vec n -> x = y.
Proof.
  intro H.
  apply vec_ext. intro i.
  assert (Hi : Vector.nth (vsub x y) i = Vector.nth (zero_vec n) i) by (rewrite H; reflexivity).
  rewrite vsub_nth, zero_vec_nth in Hi.
  assert (Hx : Vector.nth x i = Vector.nth x i - Vector.nth y i + Vector.nth y i) by ring.
  rewrite Hi in Hx.
  rewrite Hx.
  ring.
Qed.

Theorem equal_image_difference_in_kernel
    {u v : nat} (D : QLinearMap u v) (x1 x2 : QVec u) :
  lmap D x1 = lmap D x2 -> kernel D (vsub x1 x2).
Proof.
  intro Heq.
  unfold kernel.
  rewrite (lmap_preserves_sub D x1 x2).
  rewrite Heq.
  apply vec_ext. intro i. rewrite vsub_nth, zero_vec_nth. ring.
Qed.

Theorem kernel_vanishing_equal_on_equal_images
    {u v w : nat} (D : QLinearMap u v) (L : QLinearMap u w) :
  vanishes_on_kernel D L ->
  forall x1 x2, lmap D x1 = lmap D x2 -> lmap L x1 = lmap L x2.
Proof.
  intros H x1 x2 Heq.
  apply vsub_eq_zero.
  rewrite <- (lmap_preserves_sub L x1 x2).
  apply H.
  apply equal_image_difference_in_kernel.
  exact Heq.
Qed.

(** ** 7. Selector agreement under kernel vanishing *)

Theorem image_preimage_agrees_under_kernel_vanishing
    {u v w : nat} (D : QLinearMap u v) (L : QLinearMap u w) :
  vanishes_on_kernel D L ->
  forall (y : QVec v) (x : QVec u),
    linear_image D y ->
    lmap D x = y ->
    lmap L (linear_map_image_preimage D y) = lmap L x.
Proof.
  intros H y x Hy Hx.
  apply (kernel_vanishing_equal_on_equal_images D L H).
  rewrite (linear_map_image_preimage_on_image D y Hy).
  symmetry. exact Hx.
Qed.

Theorem image_preimage_after_map_agrees
    {u v w : nat} (D : QLinearMap u v) (L : QLinearMap u w) (H : vanishes_on_kernel D L)
    (x : QVec u) :
  lmap L (linear_map_image_preimage D (lmap D x)) = lmap L x.
Proof.
  apply (image_preimage_agrees_under_kernel_vanishing D L H (lmap D x) x).
  - exists x. reflexivity.
  - reflexivity.
Qed.

(** ** 8. The induced image map

    The kernel-vanishing hypothesis is not needed computationally by
    the function itself — only to prove its restricted linearity: two
    candidate preimages for the same combined image (e.g. the selector
    at [vadd y1 y2] versus [vadd] of the two individual selections)
    always have equal [D]-images, and kernel vanishing is exactly what
    turns "equal [D]-images" into "equal [L]-images". The raw selector
    is not claimed additive or scale-preserving on its own. *)

Definition induced_image_map_fun
    {u v w : nat} (D : QLinearMap u v) (L : QLinearMap u w) (y : QVec v) : QVec w :=
  lmap L (linear_map_image_preimage D y).

Theorem induced_image_map_fun_add
    {u v w : nat} (D : QLinearMap u v) (L : QLinearMap u w) (H : vanishes_on_kernel D L)
    (y1 y2 : QVec v) :
  subspace_mem (image_subspace D) y1 -> subspace_mem (image_subspace D) y2 ->
  induced_image_map_fun D L (vadd y1 y2)
  = vadd (induced_image_map_fun D L y1) (induced_image_map_fun D L y2).
Proof.
  intros Hy1 Hy2.
  unfold induced_image_map_fun.
  assert (Hy12 : linear_image D (vadd y1 y2)).
  { destruct Hy1 as [x1 Hx1]. destruct Hy2 as [x2 Hx2].
    exists (vadd x1 x2).
    rewrite (lmap_add D x1 x2), Hx1, Hx2. reflexivity. }
  assert (HDeq :
    lmap D (linear_map_image_preimage D (vadd y1 y2))
    = lmap D (vadd (linear_map_image_preimage D y1) (linear_map_image_preimage D y2))).
  { rewrite (linear_map_image_preimage_on_image D (vadd y1 y2) Hy12).
    rewrite (lmap_add D (linear_map_image_preimage D y1) (linear_map_image_preimage D y2)).
    rewrite (linear_map_image_preimage_on_image D y1 Hy1).
    rewrite (linear_map_image_preimage_on_image D y2 Hy2).
    reflexivity. }
  rewrite (kernel_vanishing_equal_on_equal_images D L H _ _ HDeq).
  apply (lmap_add L).
Qed.

Theorem induced_image_map_fun_scale
    {u v w : nat} (D : QLinearMap u v) (L : QLinearMap u w) (H : vanishes_on_kernel D L)
    (a : Qc) (y : QVec v) :
  subspace_mem (image_subspace D) y ->
  induced_image_map_fun D L (vscale a y) = vscale a (induced_image_map_fun D L y).
Proof.
  intro Hy.
  unfold induced_image_map_fun.
  assert (Hay : linear_image D (vscale a y)).
  { destruct Hy as [x Hx]. exists (vscale a x). rewrite (lmap_scale D a x), Hx. reflexivity. }
  assert (HDeq :
    lmap D (linear_map_image_preimage D (vscale a y))
    = lmap D (vscale a (linear_map_image_preimage D y))).
  { rewrite (linear_map_image_preimage_on_image D (vscale a y) Hay).
    rewrite (lmap_scale D a (linear_map_image_preimage D y)).
    rewrite (linear_map_image_preimage_on_image D y Hy).
    reflexivity. }
  rewrite (kernel_vanishing_equal_on_equal_images D L H _ _ HDeq).
  apply (lmap_scale L).
Qed.

Definition induced_image_map
    {u v w : nat} (D : QLinearMap u v) (L : QLinearMap u w) (H : vanishes_on_kernel D L)
    : QLinearMapFrom v w (image_subspace D) :=
  {|
    from_map := induced_image_map_fun D L;
    from_add := induced_image_map_fun_add D L H;
    from_scale := induced_image_map_fun_scale D L H;
  |}.

(** ** 9. Agreement theorems *)

Theorem induced_image_map_after_map
    {u v w : nat} (D : QLinearMap u v) (L : QLinearMap u w) (H : vanishes_on_kernel D L)
    (x : QVec u) :
  from_map (induced_image_map D L H) (lmap D x) = lmap L x.
Proof.
  apply (image_preimage_after_map_agrees D L H x).
Qed.

Theorem induced_image_map_well_defined
    {u v w : nat} (D : QLinearMap u v) (L : QLinearMap u w) (H : vanishes_on_kernel D L)
    (y : QVec v) (x : QVec u) :
  lmap D x = y ->
  from_map (induced_image_map D L H) y = lmap L x.
Proof.
  intro Hx.
  rewrite <- Hx.
  apply induced_image_map_after_map.
Qed.

(** ** 10. Concrete probes *)

(** *** 10.1. Zero map *)

Definition zero_D18 : QLinearMap 2 2 := linear_map_of_matrix zero_mat2.
Definition id_map18 (n : nat) : QLinearMap n n := linear_map_of_matrix (identity_matrix n).

Example probe_zero_preimage_is_zero (y : QVec 2) :
  linear_map_image_preimage zero_D18 y = zero_vec 2.
Proof.
  unfold linear_map_image_preimage, matrix_image_preimage, zero_D18.
  rewrite (matrix_of_linear_map_of_matrix zero_mat2).
  rewrite probe_zero_image_projection_is_zero.
  vm_compute. reflexivity.
Qed.

Example probe_zero_kernel_vanishing (L : QLinearMap 2 2) :
  vanishes_on_kernel zero_D18 (id_map18 2) -> False \/ True.
Proof. intros _. right. exact I. Qed.

Lemma zero_mat2_apply_zero (x : QVec 2) : matrix_apply zero_mat2 x = zero_vec 2.
Proof.
  apply (Vector.caseS' x). intros x0 x'.
  apply (Vector.caseS' x'). intros x1 x''.
  revert x''. apply Vector.case0.
  apply vec_ext. intro i.
  unfold matrix_apply, zero_mat2, zero_col2.
  simpl.
  pattern i.
  apply Fin.caseS'.
  - ring.
  - intro p. pattern p. apply Fin.caseS'.
    + simpl. ring.
    + intro p'. apply (Fin.case0 (fun p' => _) p').
Qed.

Example probe_zero_forces_L_zero (L : QLinearMap 2 2) :
  vanishes_on_kernel zero_D18 L ->
  forall x, lmap L x = zero_vec 2.
Proof.
  intros H x.
  apply H.
  unfold kernel, zero_D18. simpl lmap.
  apply zero_mat2_apply_zero.
Qed.

Example probe_zero_induced_after_map
    (L : QLinearMap 2 2) (H : vanishes_on_kernel zero_D18 L) (x : QVec 2) :
  from_map (induced_image_map zero_D18 L H) (lmap zero_D18 x) = lmap L x.
Proof. apply induced_image_map_after_map. Qed.

(** *** 10.2. Identity map *)

Definition id_D18 : QLinearMap 2 2 := id_map18 2.

Example probe_identity_preimage_recovers (y : QVec 2) :
  lmap id_D18 (linear_map_image_preimage id_D18 y) = y.
Proof.
  apply linear_map_image_preimage_on_image.
  exists y. unfold id_D18, id_map18. simpl lmap.
  apply identity_matrix_apply.
Qed.

Example probe_identity_induced_agrees
    (L : QLinearMap 2 2) (H : vanishes_on_kernel id_D18 L) (y : QVec 2) :
  linear_image id_D18 y -> from_map (induced_image_map id_D18 L H) y = lmap L (linear_map_image_preimage id_D18 y).
Proof. intros _. reflexivity. Qed.

(** *** 10.3. Proper image: [(x, y) |-> (x, 0)], with [L(x,y) = x]
    vanishing on the kernel (the [y]-axis). *)

Definition proj_col0 : QVec 2 := Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Definition proj_col1 : QVec 2 := Vector.cons Qc 0 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Definition proj_mat : QMatrix 2 2 :=
  Vector.cons (QVec 2) proj_col0 1 (Vector.cons (QVec 2) proj_col1 0 (Vector.nil (QVec 2))).
Definition proj_D : QLinearMap 2 2 := linear_map_of_matrix proj_mat.

Definition L_col0 : QVec 1 := Vector.cons Qc 1 0 (Vector.nil Qc).
Definition L_col1 : QVec 1 := Vector.cons Qc 0 0 (Vector.nil Qc).
Definition L_mat : QMatrix 1 2 :=
  Vector.cons (QVec 1) L_col0 1 (Vector.cons (QVec 1) L_col1 0 (Vector.nil (QVec 1))).
Definition L_map : QLinearMap 2 1 := linear_map_of_matrix L_mat.

Example probe_proj_kernel_vanishing : vanishes_on_kernel proj_D L_map.
Proof.
  unfold vanishes_on_kernel.
  intro k.
  apply (Vector.caseS' k). intros k0 k'.
  apply (Vector.caseS' k'). intros k1 k''.
  pose proof (Vector.case0 (fun v : Vector.t Qc 0 => v = Vector.nil Qc) eq_refl k'') as Hnil.
  rewrite Hnil.
  intro Hk.
  unfold kernel, proj_D in Hk. simpl lmap in Hk.
  assert (Hk0 : k0 = 0).
  { assert (Hnth :
      Vector.nth
        (matrix_apply proj_mat (Vector.cons Qc k0 1 (Vector.cons Qc k1 0 (Vector.nil Qc))))
        Fin.F1
      = Vector.nth (zero_vec 2) Fin.F1) by (rewrite Hk; reflexivity).
    rewrite zero_vec_nth in Hnth.
    unfold matrix_apply, proj_mat, proj_col0, proj_col1 in Hnth.
    simpl in Hnth.
    assert (Hrw : k0 = k0 * 1 + (k1 * 0 + 0)) by ring.
    rewrite Hrw. exact Hnth. }
  unfold L_map. simpl lmap.
  apply vec_ext. intro i.
  unfold matrix_apply, L_mat, L_col0, L_col1.
  simpl.
  pattern i. apply Fin.caseS'.
  - simpl. rewrite Hk0. ring.
  - intro p. apply (Fin.case0 (fun p => _) p).
Qed.

Example probe_proj_equal_images_equal_L (x1 x2 : QVec 2) :
  lmap proj_D x1 = lmap proj_D x2 -> lmap L_map x1 = lmap L_map x2.
Proof. apply kernel_vanishing_equal_on_equal_images. apply probe_proj_kernel_vanishing. Qed.

Example probe_proj_induced_after_map (x : QVec 2) :
  from_map (induced_image_map proj_D L_map probe_proj_kernel_vanishing) (lmap proj_D x)
  = lmap L_map x.
Proof. apply induced_image_map_after_map. Qed.

(** *** 10.4. Failure when kernel vanishing does not hold: [L'(x,y)=y]
    is nonzero on the same kernel vector [(0,1)]. *)

Definition Lp_col0 : QVec 1 := Vector.cons Qc 0 0 (Vector.nil Qc).
Definition Lp_col1 : QVec 1 := Vector.cons Qc 1 0 (Vector.nil Qc).
Definition Lp_mat : QMatrix 1 2 :=
  Vector.cons (QVec 1) Lp_col0 1 (Vector.cons (QVec 1) Lp_col1 0 (Vector.nil (QVec 1))).
Definition Lp_map : QLinearMap 2 1 := linear_map_of_matrix Lp_mat.

Definition kernel_witness : QVec 2 := Vector.cons Qc 0 1 (Vector.cons Qc 1 0 (Vector.nil Qc)).

Example probe_kernel_witness_in_kernel : kernel proj_D kernel_witness.
Proof.
  unfold kernel, proj_D. simpl lmap.
  vm_compute. reflexivity.
Qed.

Example probe_Lp_nonzero_on_kernel :
  lmap Lp_map kernel_witness <> zero_vec 1.
Proof.
  unfold Lp_map. simpl lmap.
  vm_compute. discriminate.
Qed.

Example probe_Lp_not_kernel_vanishing : ~ vanishes_on_kernel proj_D Lp_map.
Proof.
  intro H.
  apply probe_Lp_nonzero_on_kernel.
  apply H.
  apply probe_kernel_witness_in_kernel.
Qed.

(** *** 10.5. Nontrivial elimination-derived image: [piv2_mat]'s
    accumulated row transformation is not the identity (Unit 17a's
    [probe_nontrivial_conjugation]). Only the public preimage/induced-
    map theorems are invoked; no elimination trace is inspected here. *)

Definition piv2_D18 : QLinearMap 2 2 := linear_map_of_matrix piv2_mat.

Example probe_piv2_preimage_projection (y : QVec 2) :
  lmap piv2_D18 (linear_map_image_preimage piv2_D18 y)
  = lmap (linear_map_image_projection piv2_D18) y.
Proof. apply linear_map_image_preimage_projection. Qed.

Example probe_piv2_induced_after_map
    (L : QLinearMap 2 2) (H : vanishes_on_kernel piv2_D18 L) (x : QVec 2) :
  from_map (induced_image_map piv2_D18 L H) (lmap piv2_D18 x) = lmap L x.
Proof. apply induced_image_map_after_map. Qed.

(** *** 10.6. Zero-dimensional boundaries *)

Definition dim00_D18 : QLinearMap 0 0 := linear_map_of_matrix mat_0_0.
Definition dim01_D18 : QLinearMap 1 0 := linear_map_of_matrix mat_0_1.
Definition dim20_D18 : QLinearMap 0 2 := linear_map_of_matrix mat_2_0.

Example probe_dim_0_0_induced_after_map
    (L : QLinearMap 0 0) (H : vanishes_on_kernel dim00_D18 L) (x : QVec 0) :
  from_map (induced_image_map dim00_D18 L H) (lmap dim00_D18 x) = lmap L x.
Proof. apply induced_image_map_after_map. Qed.

Example probe_dim_0_1_induced_after_map
    (L : QLinearMap 1 0) (H : vanishes_on_kernel dim01_D18 L) (x : QVec 1) :
  from_map (induced_image_map dim01_D18 L H) (lmap dim01_D18 x) = lmap L x.
Proof. apply induced_image_map_after_map. Qed.

Example probe_dim_2_0_induced_after_map
    (L : QLinearMap 0 2) (H : vanishes_on_kernel dim20_D18 L) (x : QVec 0) :
  from_map (induced_image_map dim20_D18 L H) (lmap dim20_D18 x) = lmap L x.
Proof. apply induced_image_map_after_map. Qed.
