(** * The separator theorem: R4 soundness and constructive completeness

    [[
      r not in im D
      <->
      exists y : V -> Q, y D = 0 /\ y(r) <> 0
    ]]

    Unit 19a supplied exactly the constructive bridge this theorem
    needs: the image-residual map [R_D(r) = r - P_D(r)], vanishing
    exactly on [linear_image D] ([image_residual_zero_iff_image]), and
    constructive extraction of a nonzero coordinate from a nonzero
    vector ([nonzero_vector_has_nonzero_coordinate]). This unit
    composes them: a coordinate of the residual, viewed as a linear
    functional, is a separator — it annihilates every point of the
    image (since the residual does) and detects [r] whenever some
    residual coordinate at [r] is nonzero (which happens exactly when
    [r] is outside the image).

    This unit does NOT prove: separator normalisation to [y(r) = 1];
    uniqueness or canonicity of separators; a basis of the left
    nullspace; transpose or rank identities; gauge-witness soundness
    or completeness; kernel-witness extraction; verdict classification;
    verdict exclusivity or completeness; the four-sector exactness
    profile; canonical exact values; the universal quotient; ROC or
    PCE instantiation; or certificate formats, JSON, or executable
    semantics. Phase 3 covers separator and gauge witnesses followed by
    classification; this unit stops after completing the separator
    half, R4. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Vector.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QMatrixAlgebra.
From LiftDescent Require Import QImageExtension.
From LiftDescent Require Import QImagePreimage.
From LiftDescent Require Import QLinearFunctional.

Open Scope Qc_scope.

(** ** 1. The separator predicate *)

Definition separator_witness
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (y : QLinearFunctional v)
    : Prop :=
  (forall x : QVec u, lmap y (lmap D x) = zero_vec 1)
  /\
  lmap y r <> zero_vec 1.

(** ** 2. Separator obtained from a residual coordinate *)

Definition residual_coordinate_separator
    {u v : nat}
    (D : QLinearMap u v)
    (i : Fin.t v)
    : QLinearFunctional v :=
  precompose (image_residual_map D) (coordinate_functional i).

(** ** 3. Residual-coordinate separators annihilate the image *)

Theorem residual_coordinate_separator_annihilates
    {u v : nat}
    (D : QLinearMap u v)
    (i : Fin.t v)
    (x : QVec u) :
  lmap (residual_coordinate_separator D i) (lmap D x) = zero_vec 1.
Proof.
  unfold residual_coordinate_separator.
  change
    (lmap (coordinate_functional i) (lmap (image_residual_map D) (lmap D x)) = zero_vec 1).
  rewrite (image_residual_after_map D x).
  apply lmap_preserves_zero.
Qed.

(** ** 4. A non-zero residual coordinate is detected *)

Theorem residual_coordinate_separator_detects
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (i : Fin.t v) :
  Vector.nth (lmap (image_residual_map D) r) i <> 0 ->
  lmap (residual_coordinate_separator D i) r <> zero_vec 1.
Proof.
  intro Hne.
  unfold residual_coordinate_separator.
  change
    (lmap (coordinate_functional i) (lmap (image_residual_map D) r) <> zero_vec 1).
  apply coordinate_functional_detects_nonzero.
  exact Hne.
Qed.

(** ** 5. Separator soundness *)

Theorem separator_witness_sound
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (y : QLinearFunctional v) :
  separator_witness D r y -> ~ linear_image D r.
Proof.
  intros [Hann Hnz] [x Hx].
  apply Hnz.
  rewrite <- Hx.
  apply Hann.
Qed.

(** ** 6. Constructive separator completeness

    [r not in im D] -> [R_D(r) <> 0] -> [some coordinate i of R_D(r)
    is nonzero] -> [residual_coordinate_separator D i] is a separator
    for [r]. No transpose theory, left-nullspace basis, elimination,
    classical choice, excluded middle, or
    [constructive_indefinite_description] is used. *)

Theorem separator_witness_complete
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v) :
  ~ linear_image D r ->
  exists y : QLinearFunctional v, separator_witness D r y.
Proof.
  intro Hnot.
  pose proof (not_image_implies_nonzero_residual D r Hnot) as Hres.
  destruct (nonzero_vector_has_nonzero_coordinate
              (lmap (image_residual_map D) r) Hres) as [i Hi].
  exists (residual_coordinate_separator D i).
  split.
  - intro x. apply residual_coordinate_separator_annihilates.
  - apply residual_coordinate_separator_detects. exact Hi.
Qed.

(** ** 7. The R4 equivalence *)

Theorem not_image_iff_separator_witness
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v) :
  ~ linear_image D r <-> exists y : QLinearFunctional v, separator_witness D r y.
Proof.
  split.
  - apply separator_witness_complete.
  - intros [y Hy]. apply (separator_witness_sound D r y). exact Hy.
Qed.

(** ** 8. Connection to the lifting obstruction *)

Theorem lift_obstructed_iff_separator_witness
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v) :
  lift_obstructed D r <-> exists y : QLinearFunctional v, separator_witness D r y.
Proof.
  unfold lift_obstructed, lift_obstruction_zero.
  apply not_image_iff_separator_witness.
Qed.

(** ** 9. Readable corollary *)

Theorem separator_witness_excludes_repair
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (y : QLinearFunctional v) :
  separator_witness D r y -> ~ exists x : QVec u, lmap D x = r.
Proof.
  intro H.
  apply (separator_witness_sound D r y H).
Qed.

(** ** 10. Concrete probes *)

(** *** 10.1. Zero map: a non-zero codomain vector has a
    residual-coordinate separator. *)

Example probe_zero_map_separator_exists :
  exists y : QLinearFunctional 2,
    separator_witness QImagePreimage.zero_D18
      (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc))) y.
Proof.
  apply separator_witness_complete.
  intros [x Hx].
  unfold QImagePreimage.zero_D18 in Hx. simpl lmap in Hx.
  rewrite (QImagePreimage.zero_mat2_apply_zero x) in Hx.
  revert Hx. vm_compute. intro Hx. discriminate Hx.
Qed.

(** *** 10.2. Identity map: no separator exists for any [r], since
    the image is the whole space. *)

Example probe_identity_no_separator (r : QVec 2) :
  ~ exists y : QLinearFunctional 2, separator_witness QImagePreimage.id_D18 r y.
Proof.
  intro H.
  apply (not_image_iff_separator_witness QImagePreimage.id_D18 r).
  - exact H.
  - exists r.
    unfold QImagePreimage.id_D18, QImagePreimage.id_map18. simpl lmap.
    apply identity_matrix_apply.
Qed.

(** *** 10.3. Proper image: [proj_D(x,y) = (x,0)]; the [y]-axis vector
    [(0,1)] is outside the image, and a separator detecting its
    missing second coordinate exists. *)

Example probe_proper_image_separator_exists :
  exists y : QLinearFunctional 2,
    separator_witness QImagePreimage.proj_D
      (Vector.cons Qc 0 1 (Vector.cons Qc 1 0 (Vector.nil Qc))) y.
Proof.
  apply separator_witness_complete.
  intro Hin.
  apply probe_proper_image_out_of_image_nonzero_residual.
  apply image_residual_zero_iff_image.
  exact Hin.
Qed.

(** *** 10.4. Zero-dimensional codomain: no separator can exist for
    [D : QLinearMap u 0], since every [QVec 0] lies in the image
    (there is a unique such vector, and every ambient map is total). *)

Example probe_dim_0_codomain_no_separator
    {u : nat} (D : QLinearMap u 0) (r : QVec 0) :
  ~ exists y : QLinearFunctional 0, separator_witness D r y.
Proof.
  intro H.
  apply (not_image_iff_separator_witness D r).
  - exact H.
  - destruct u as [| u'].
    + exists (zero_vec 0).
      apply vec_ext. intro i. inversion i.
    + exists (zero_vec (S u')).
      apply vec_ext. intro i. inversion i.
Qed.
