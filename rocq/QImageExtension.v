(** * Ambient extension from an image subspace

    Unit 17a constructed [image_projection] — an explicit, elimination-
    derived linear retraction of the ambient codomain onto a matrix's
    image — and sealed it behind five public theorems. This unit
    treats that construction as a closed interface: it never unfolds
    [image_projection], never inspects an elimination trace, pivot
    row, completed pivot, column lock, support predicate, or inverse
    row-operation sequence. It only uses:

    [[
      image_projection
      image_projection_in_image
      image_projection_fixes_image
    ]]

    (the remaining two, [image_projection_idempotent] and
    [image_projection_image], are not needed here).

    The construction: lift [image_projection] from matrices to
    arbitrary [QLinearMap]s via the existing [matrix_of_lmap] bridge;
    precompose a map [T] defined on [image_subspace D] with that
    lifted projection; the result is an ambient [QLinearMap] that
    agrees with [T] everywhere on [image_subspace D]. The decisive
    theorem is the existence, for every [D] and every [T] on
    [image_subspace D], of such an ambient extension — explicit and
    constructive, not merely asserted.

    This unit does NOT prove: extension from an arbitrary subspace
    (only from an image); uniqueness of the extension; canonicity
    independent of elimination order; orthogonality of the projection;
    norm-minimising extension; continuity/boundedness beyond finite
    algebraic linearity; rank-nullity; dimension formulas; a basis-
    extension theorem; a complement unique to the image; equality of
    [QLinearMapFrom] records from pointwise agreement; factorisation
    of an arbitrary map through [D]; that kernel vanishing is
    sufficient or necessary for factorisation; the final descent- or
    lift-obstruction equivalence; or any result beyond finite rational
    coordinate spaces. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QSubspaceMap.
From LiftDescent Require Import QFiniteCoordinates.
From LiftDescent Require Import QMatrixAlgebra.
From LiftDescent Require Import QImageProjection.
From LiftDescent Require Import QEliminationStructure.

Open Scope Qc_scope.

(** ** 1. The projection associated with an arbitrary linear map

    Passes through the existing matrix representation
    ([matrix_of_lmap], Unit 11) rather than constructing a second
    projection or rerunning elimination directly from [D]. *)

Definition linear_map_image_projection
    {u v : nat} (D : QLinearMap u v) : QLinearMap v v :=
  image_projection (matrix_of_lmap D).

(** The pointwise bridge between the matrix-level image predicate and
    [linear_image D] directly, via [matrix_of_lmap_correct] (Unit 11)
    — no record equality between [linear_map_of_matrix (matrix_of_lmap
    D)] and [D] is used or needed. *)

Lemma linear_image_matrix_of_lmap_iff
    {u v : nat} (D : QLinearMap u v) (w : QVec v) :
  linear_image (linear_map_of_matrix (matrix_of_lmap D)) w <-> linear_image D w.
Proof.
  split.
  - intros [x Hx]. exists x. simpl lmap in Hx. rewrite <- Hx.
    symmetry. apply matrix_of_lmap_correct.
  - intros [x Hx]. exists x. simpl lmap.
    rewrite matrix_of_lmap_correct. exact Hx.
Qed.

Theorem linear_map_image_projection_in_image
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  linear_image D (lmap (linear_map_image_projection D) y).
Proof.
  unfold linear_map_image_projection.
  apply linear_image_matrix_of_lmap_iff.
  apply image_projection_in_image.
Qed.

Theorem linear_map_image_projection_fixes_image
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  linear_image D y -> lmap (linear_map_image_projection D) y = y.
Proof.
  intro Hy.
  unfold linear_map_image_projection.
  apply image_projection_fixes_image.
  apply linear_image_matrix_of_lmap_iff.
  exact Hy.
Qed.

Theorem linear_map_image_projection_idempotent
    {u v : nat} (D : QLinearMap u v) (y : QVec v) :
  lmap (linear_map_image_projection D) (lmap (linear_map_image_projection D) y)
  = lmap (linear_map_image_projection D) y.
Proof.
  apply linear_map_image_projection_fixes_image.
  apply linear_map_image_projection_in_image.
Qed.

Theorem linear_map_image_projection_image
    {u v : nat} (D : QLinearMap u v) :
  same_set (linear_image (linear_map_image_projection D)) (linear_image D).
Proof.
  unfold same_set. intro y.
  split.
  - intros [x Hx]. rewrite <- Hx. apply linear_map_image_projection_in_image.
  - intro Hy. exists y. apply linear_map_image_projection_fixes_image. exact Hy.
Qed.

(** ** 2. Agreement on a subspace *)

Definition same_on_subspace
    {v w : nat} (S : QSubspace v) (T : QLinearMapFrom v w S) (M : QLinearMap v w) : Prop :=
  forall y, subspace_mem S y -> lmap M y = from_map T y.

(** ** 3. The ambient extension *)

Definition extend_from_image_fun
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D))
    (y : QVec v) : QVec w :=
  from_map T (lmap (linear_map_image_projection D) y).

Lemma extend_from_image_fun_add
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D))
    (y1 y2 : QVec v) :
  extend_from_image_fun D T (vadd y1 y2)
  = vadd (extend_from_image_fun D T y1) (extend_from_image_fun D T y2).
Proof.
  unfold extend_from_image_fun.
  rewrite (lmap_add (linear_map_image_projection D) y1 y2).
  apply (from_add T).
  - apply linear_map_image_projection_in_image.
  - apply linear_map_image_projection_in_image.
Qed.

Lemma extend_from_image_fun_scale
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D))
    (a : Qc) (y : QVec v) :
  extend_from_image_fun D T (vscale a y) = vscale a (extend_from_image_fun D T y).
Proof.
  unfold extend_from_image_fun.
  rewrite (lmap_scale (linear_map_image_projection D) a y).
  apply (from_scale T).
  apply linear_map_image_projection_in_image.
Qed.

Definition extend_from_image
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D))
    : QLinearMap v w :=
  {|
    lmap := extend_from_image_fun D T;
    lmap_add := extend_from_image_fun_add D T;
    lmap_scale := extend_from_image_fun_scale D T;
  |}.

(** ** 4. Agreement theorems *)

Theorem extend_from_image_agrees
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D)) (y : QVec v) :
  linear_image D y -> lmap (extend_from_image D T) y = from_map T y.
Proof.
  intro Hy.
  simpl lmap. unfold extend_from_image_fun.
  rewrite (linear_map_image_projection_fixes_image D y Hy).
  reflexivity.
Qed.

Theorem extend_from_image_same_on_image
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D)) :
  same_on_subspace (image_subspace D) T (extend_from_image D T).
Proof.
  unfold same_on_subspace. intros y Hy.
  apply extend_from_image_agrees.
  exact Hy.
Qed.

Theorem extend_from_image_after_map
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D)) (x : QVec u) :
  lmap (extend_from_image D T) (lmap D x) = from_map T (lmap D x).
Proof.
  apply extend_from_image_agrees.
  exists x. reflexivity.
Qed.

Theorem restrict_extend_from_image
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D)) (y : QVec v) :
  subspace_mem (image_subspace D) y ->
  from_map (restrict_domain (image_subspace D) (extend_from_image D T)) y = from_map T y.
Proof.
  intro Hy.
  simpl from_map.
  apply extend_from_image_agrees.
  exact Hy.
Qed.

(** ** 5. Existential ambient-extension theorems *)

Theorem image_subspace_ambient_extension
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D)) :
  exists M : QLinearMap v w, same_on_subspace (image_subspace D) T M.
Proof.
  exists (extend_from_image D T).
  apply extend_from_image_same_on_image.
Qed.

Theorem image_map_extension_exists
    {u v w : nat} (D : QLinearMap u v) (T : QLinearMapFrom v w (image_subspace D)) :
  exists M : QLinearMap v w, forall x, lmap M (lmap D x) = from_map T (lmap D x).
Proof.
  exists (extend_from_image D T).
  intro x.
  apply extend_from_image_after_map.
Qed.

(** ** 6. Concrete probes

    Reuse Unit 16a's example matrices and Unit 17a's already-proved
    concrete facts about them wherever possible, rather than
    re-deriving elimination-level results here. *)

Definition id_map (n : nat) : QLinearMap n n := linear_map_of_matrix (identity_matrix n).

(** *** 6.1. Zero map *)

Definition zero_D : QLinearMap 2 2 := linear_map_of_matrix zero_mat2.
Definition zero_T : QLinearMapFrom 2 2 (image_subspace zero_D) :=
  restrict_domain (image_subspace zero_D) (id_map 2).

Example probe_zero_projection_is_zero (y : QVec 2) :
  lmap (linear_map_image_projection zero_D) y = zero_vec 2.
Proof.
  unfold linear_map_image_projection, zero_D.
  rewrite (matrix_of_linear_map_of_matrix zero_mat2).
  apply probe_zero_image_projection_is_zero.
Qed.

Example probe_zero_extension_exists :
  exists M : QLinearMap 2 2, same_on_subspace (image_subspace zero_D) zero_T M.
Proof. apply image_subspace_ambient_extension. Qed.

Example probe_zero_extension_after_map (x : QVec 2) :
  lmap (extend_from_image zero_D zero_T) (lmap zero_D x) = from_map zero_T (lmap zero_D x).
Proof. apply extend_from_image_after_map. Qed.

Example probe_zero_agrees_at_zero :
  lmap (extend_from_image zero_D zero_T) (zero_vec 2) = from_map zero_T (zero_vec 2).
Proof.
  apply extend_from_image_agrees.
  exists (zero_vec 2). apply lmap_preserves_zero.
Qed.

(** *** 6.2. Identity map *)

Definition id_D : QLinearMap 2 2 := id_map 2.
Definition id_T : QLinearMapFrom 2 2 (image_subspace id_D) :=
  restrict_domain (image_subspace id_D) (id_map 2).

Example probe_identity_extension_after_map (x : QVec 2) :
  lmap (extend_from_image id_D id_T) (lmap id_D x) = from_map id_T (lmap id_D x).
Proof. apply extend_from_image_after_map. Qed.

Example probe_identity_agrees_on_image (y : QVec 2) :
  linear_image id_D y -> lmap (extend_from_image id_D id_T) y = from_map id_T y.
Proof. apply extend_from_image_agrees. Qed.

(** *** 6.3. Proper image: [tall_mat] embeds [QVec 2] into [QVec 3]
    with the third coordinate always zero. *)

Definition tall_D : QLinearMap 2 3 := linear_map_of_matrix tall_mat.
Definition tall_T : QLinearMapFrom 3 3 (image_subspace tall_D) :=
  restrict_domain (image_subspace tall_D) (id_map 3).

Example probe_tall_extension_exists :
  exists M : QLinearMap 3 3, same_on_subspace (image_subspace tall_D) tall_T M.
Proof. apply image_subspace_ambient_extension. Qed.

Example probe_tall_extension_after_map (x : QVec 2) :
  lmap (extend_from_image tall_D tall_T) (lmap tall_D x) = from_map tall_T (lmap tall_D x).
Proof. apply extend_from_image_after_map. Qed.

(** *** 6.4. Nontrivial elimination-derived image: [piv2_mat]'s
    accumulated row transformation is not the identity (Unit 17a's
    [probe_nontrivial_conjugation]); its image is the proper subspace
    spanned by the single recorded pivot row. The extension proof
    below only invokes the public extension theorems. *)

Definition piv2_D : QLinearMap 2 2 := linear_map_of_matrix piv2_mat.
Definition piv2_T : QLinearMapFrom 2 2 (image_subspace piv2_D) :=
  restrict_domain (image_subspace piv2_D) (id_map 2).

Example probe_piv2_extension_after_map (x : QVec 2) :
  lmap (extend_from_image piv2_D piv2_T) (lmap piv2_D x) = from_map piv2_T (lmap piv2_D x).
Proof. apply extend_from_image_after_map. Qed.

Example probe_piv2_agrees_on_image (y : QVec 2) :
  linear_image piv2_D y -> lmap (extend_from_image piv2_D piv2_T) y = from_map piv2_T y.
Proof. apply extend_from_image_agrees. Qed.

(** *** 6.5. Zero-dimensional boundaries *)

Definition dim00_D : QLinearMap 0 0 := linear_map_of_matrix mat_0_0.
Definition dim00_T : QLinearMapFrom 0 0 (image_subspace dim00_D) :=
  restrict_domain (image_subspace dim00_D) (id_map 0).

Example probe_dim_0_0_extension_exists :
  exists M : QLinearMap 0 0, same_on_subspace (image_subspace dim00_D) dim00_T M.
Proof. apply image_subspace_ambient_extension. Qed.

Definition dim01_D : QLinearMap 1 0 := linear_map_of_matrix mat_0_1.
Definition dim01_T : QLinearMapFrom 0 0 (image_subspace dim01_D) :=
  restrict_domain (image_subspace dim01_D) (id_map 0).

Example probe_dim_0_1_extension_exists :
  exists M : QLinearMap 0 0, same_on_subspace (image_subspace dim01_D) dim01_T M.
Proof. apply image_subspace_ambient_extension. Qed.

Definition dim20_D : QLinearMap 0 2 := linear_map_of_matrix mat_2_0.
Definition dim20_T : QLinearMapFrom 2 2 (image_subspace dim20_D) :=
  restrict_domain (image_subspace dim20_D) (id_map 2).

Example probe_dim_2_0_extension_exists :
  exists M : QLinearMap 2 2, same_on_subspace (image_subspace dim20_D) dim20_T M.
Proof. apply image_subspace_ambient_extension. Qed.

(** *** 6.6. Application-form agreement, the shape Unit 18 will use *)

Example probe_application_form_agreement (x : QVec 2) :
  exists M : QLinearMap 2 2,
    lmap M (lmap piv2_D x) = from_map piv2_T (lmap piv2_D x).
Proof.
  destruct (image_map_extension_exists piv2_D piv2_T) as [M HM].
  exists M. apply HM.
Qed.
