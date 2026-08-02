(** * The universal exact quotient, R8

    The ambiguity space of the pair [(D, L)] is [A_{D,L} = L(ker D)] —
    the values [L] takes on displacements that leave the residue
    unchanged. Unit 20a's kernel projection [K_D] already represents
    [ker D] as the image of an ambient linear map ([im K_D = ker D]),
    so composing with [L] gives an ambient map, [ambiguity_map D L :=
    L after K_D], whose image is exactly [A_{D,L}]
    ([ambiguity_subspace_iff_kernel_claim]).

    Unit 19a's image residual, applied to this ambiguity map, is a
    linear map on [W] that vanishes exactly on [A_{D,L}]
    ([ambiguity_quotient_map_zero_iff_ambiguity]) — its image is
    therefore a concrete finite-coordinate presentation of [W /
    A_{D,L}], and the residual itself is the quotient map [pi_{D,L}].
    The quotient claim [pi_{D,L} L] vanishes on [ker D] by
    construction and so descends through [D]
    ([quotient_claim_descends]) — the exactness half of R8.

    For the universal half: a post-map [q : W -> Q] has [q L]
    descending through [D] exactly when [q] annihilates [A_{D,L}]
    ([postcomposition_descends_iff_annihilates_ambiguity]). Any such
    [q] is therefore unaffected by subtracting the ambiguity-map image
    projection, giving [q pi_{D,L} = q]
    ([postcomposition_descends_invariant_under_quotient]). Restricting
    [q] to the quotient representative subspace ([restrict_domain])
    then supplies a factor through which [q] equals [pi_{D,L}]
    followed by that factor, and this factor is unique on the
    quotient subspace because every quotient element is the image of
    some [x : W] under [pi_{D,L}]
    ([universal_exact_quotient]).

    The quotient carrier is represented, following the representation
    already used throughout this project ([QSubspace.v]), as a
    predicate subspace of the ambient space [W] together with
    ordinary maps into and out of it — not as a dependent subtype of
    equivalence classes, which would reintroduce the proof-irrelevance
    concern [QSubspace.v] explains at length. Uniqueness of a factor
    is therefore stated extensionally on the quotient subspace
    ([same_from_map]), never as Leibniz equality of [QLinearMapFrom]
    records. The particular complementary subspace this presentation
    selects depends on the existing elimination-derived image
    projection; the universal property proved here, not that
    particular selection, is what makes this a quotient presentation.

    This unit does NOT prove or construct: a literal set of quotient
    equivalence classes; a dependent quotient carrier; equality of
    quotient-map records including their proof fields; the dimension
    of the quotient or of [A_{D,L}]; a basis of [A_{D,L}] or of the
    quotient representative subspace; rank-nullity; a minimal
    coordinate encoding of the quotient; independence of the selected
    complement from the elimination order; orthogonality or norm
    minimisation; a unique ambient complement of [A_{D,L}]; a
    canonical exact value for a particular residue, or its invariance
    under a selected repair or factor map; coordinate-transport
    results for a later unit; preservation or reflection properties of
    a noninvertible presentation map; realisability-obstruction-class
    or presented-claim-equivalence instantiation; admissibility or
    provenance checking; certificate, serialisation, command-line, or
    protocol semantics; an extracted runtime quotient representation;
    or any generalisation beyond finite rational coordinate spaces.
    This unit concerns only [D] and [L] — the residue [r] plays no
    role anywhere in this file. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QSubspaceMap.
From LiftDescent Require Import QExactSequence.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QImageExtension.
From LiftDescent Require Import QImagePreimage.
From LiftDescent Require Import QDescentFactorisation.
From LiftDescent Require Import QLinearFunctional.
From LiftDescent Require Import QKernelProjection.

Open Scope Qc_scope.

(** ** Part I: The ambiguity map and subspace *)

Definition ambiguity_map
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : QLinearMap u w :=
  precompose (kernel_projection D) L.

Definition ambiguity_subspace
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : QSubspace w :=
  image_subspace (ambiguity_map D L).

Theorem ambiguity_map_apply
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (x : QVec u) :
  lmap (ambiguity_map D L) x =
  lmap L (lmap (kernel_projection D) x).
Proof. reflexivity. Qed.

Theorem ambiguity_subspace_iff_kernel_claim
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (a : QVec w) :
  subspace_mem (ambiguity_subspace D L) a
  <->
  exists k : QVec u,
    kernel D k /\
    lmap L k = a.
Proof.
  split.
  - intros [x Hx].
    exists (lmap (kernel_projection D) x).
    split.
    + apply kernel_projection_in_kernel.
    + rewrite <- (ambiguity_map_apply D L x). exact Hx.
  - intros [k [Hk Heq]].
    exists k.
    rewrite (ambiguity_map_apply D L k).
    rewrite (kernel_projection_fixes_kernel D k Hk).
    exact Heq.
Qed.

Theorem kernel_claim_in_ambiguity_subspace
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (k : QVec u) :
  kernel D k ->
  subspace_mem
    (ambiguity_subspace D L)
    (lmap L k).
Proof.
  intro Hk.
  apply (ambiguity_subspace_iff_kernel_claim D L (lmap L k)).
  exists k. split; [exact Hk | reflexivity].
Qed.

(** ** Part II: The quotient presentation *)

Definition ambiguity_quotient_map
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : QLinearMap w w :=
  image_residual_map (ambiguity_map D L).

Definition ambiguity_quotient_subspace
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : QSubspace w :=
  image_subspace (ambiguity_quotient_map D L).

Definition ambiguity_quotient_corestriction
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : QLinearMapInto w w (ambiguity_quotient_subspace D L) :=
  tilde_D (ambiguity_quotient_map D L).

(** ** Part III: Kernel of the quotient map *)

Theorem ambiguity_quotient_map_zero_iff_ambiguity
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (a : QVec w) :
  lmap (ambiguity_quotient_map D L) a = zero_vec w
  <->
  subspace_mem (ambiguity_subspace D L) a.
Proof.
  unfold ambiguity_quotient_map.
  apply (image_residual_zero_iff_image (ambiguity_map D L) a).
Qed.

Theorem ambiguity_quotient_map_kills_ambiguity
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (a : QVec w) :
  subspace_mem (ambiguity_subspace D L) a ->
  lmap (ambiguity_quotient_map D L) a = zero_vec w.
Proof.
  intro Ha.
  apply (ambiguity_quotient_map_zero_iff_ambiguity D L a).
  exact Ha.
Qed.

Theorem ambiguity_quotient_map_kills_kernel_claim
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (k : QVec u) :
  kernel D k ->
  lmap (ambiguity_quotient_map D L) (lmap L k) = zero_vec w.
Proof.
  intro Hk.
  apply ambiguity_quotient_map_kills_ambiguity.
  apply kernel_claim_in_ambiguity_subspace.
  exact Hk.
Qed.

(** ** Part IV: Surjectivity and short exactness *)

Theorem ambiguity_quotient_corestriction_surjective
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  surjective_into (ambiguity_quotient_corestriction D L).
Proof.
  unfold surjective_into, ambiguity_quotient_corestriction.
  intros y Hy.
  exact Hy.
Qed.

Theorem ambiguity_quotient_short_exact
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  short_exact_subspace
    (ambiguity_subspace D L)
    (ambiguity_quotient_subspace D L)
    (subspace_inclusion (ambiguity_subspace D L))
    (ambiguity_quotient_corestriction D L).
Proof.
  unfold short_exact_subspace.
  split; [| split].
  - unfold injective_from, subspace_inclusion. simpl.
    intros x y _ _ Heq. exact Heq.
  - unfold exact_at_middle.
    intros a.
    split.
    + intro Ha.
      exists a.
      split.
      * apply (ambiguity_quotient_map_zero_iff_ambiguity D L a). exact Ha.
      * reflexivity.
    + intros [k [Hk Heq]].
      rewrite <- Heq.
      apply (ambiguity_quotient_map_zero_iff_ambiguity D L k).
      exact Hk.
  - apply ambiguity_quotient_corestriction_surjective.
Qed.

(** ** Part V: The quotient claim *)

Definition quotient_claim
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : QLinearMap u w :=
  precompose L (ambiguity_quotient_map D L).

Definition quotient_claim_into
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : QLinearMapInto u w (ambiguity_quotient_subspace D L).
Proof.
  refine {| into_map := quotient_claim D L; into_mem := _ |}.
  intro x.
  exists (lmap L x).
  reflexivity.
Defined.

Theorem quotient_claim_vanishes_on_kernel
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  QImagePreimage.vanishes_on_kernel D (quotient_claim D L).
Proof.
  intros k Hk.
  change (lmap (ambiguity_quotient_map D L) (lmap L k) = zero_vec w).
  apply ambiguity_quotient_map_kills_kernel_claim.
  exact Hk.
Qed.

Theorem quotient_claim_descends
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  descent_obstruction_zero D (quotient_claim D L).
Proof.
  apply descent_obstruction_zero_iff_kernel_vanishing.
  apply quotient_claim_vanishes_on_kernel.
Qed.

(** ** Part VI: Compatible post-maps *)

Theorem postcomposition_descends_implies_annihilates_ambiguity
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t) :
  descent_obstruction_zero D (precompose L q) ->
  forall a : QVec w,
    subspace_mem (ambiguity_subspace D L) a ->
    lmap q a = zero_vec t.
Proof.
  intro Hdesc.
  apply descent_obstruction_zero_iff_kernel_vanishing in Hdesc.
  intros a Ha.
  apply (ambiguity_subspace_iff_kernel_claim D L a) in Ha.
  destruct Ha as [k [Hk Heq]].
  rewrite <- Heq.
  exact (Hdesc k Hk).
Qed.

Theorem annihilates_ambiguity_implies_postcomposition_descends
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t) :
  (forall a : QVec w,
     subspace_mem (ambiguity_subspace D L) a ->
     lmap q a = zero_vec t) ->
  descent_obstruction_zero D (precompose L q).
Proof.
  intro Hann.
  apply descent_obstruction_zero_iff_kernel_vanishing.
  intros k Hk.
  apply (Hann (lmap L k)).
  apply (kernel_claim_in_ambiguity_subspace D L k).
  exact Hk.
Qed.

Theorem postcomposition_descends_iff_annihilates_ambiguity
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t) :
  descent_obstruction_zero D (precompose L q)
  <->
  forall a : QVec w,
    subspace_mem (ambiguity_subspace D L) a ->
    lmap q a = zero_vec t.
Proof.
  split.
  - apply postcomposition_descends_implies_annihilates_ambiguity.
  - apply annihilates_ambiguity_implies_postcomposition_descends.
Qed.

(** ** Part VII: Invariance under the quotient map *)

Theorem postcomposition_descends_kills_ambiguity_projection
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t) :
  descent_obstruction_zero D (precompose L q) ->
  forall x : QVec w,
    lmap q
      (lmap (linear_map_image_projection (ambiguity_map D L)) x)
    = zero_vec t.
Proof.
  intros Hdesc x.
  apply (postcomposition_descends_implies_annihilates_ambiguity D L q Hdesc
           (lmap (linear_map_image_projection (ambiguity_map D L)) x)).
  apply (linear_map_image_projection_in_image (ambiguity_map D L) x).
Qed.

Theorem postcomposition_descends_invariant_under_quotient
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t) :
  descent_obstruction_zero D (precompose L q) ->
  forall x : QVec w,
    lmap q (lmap (ambiguity_quotient_map D L) x) = lmap q x.
Proof.
  intro Hdesc.
  intro x.
  unfold ambiguity_quotient_map, image_residual_map. simpl lmap.
  unfold image_residual_map_fun.
  rewrite (lmap_preserves_sub q x
             (lmap (linear_map_image_projection (ambiguity_map D L)) x)).
  rewrite (postcomposition_descends_kills_ambiguity_projection D L q Hdesc x).
  apply vec_ext. intro i.
  rewrite vsub_nth, zero_vec_nth.
  ring.
Qed.

(** ** Part VIII: Quotient factor maps *)

Definition ambiguity_quotient_factorisation
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t)
    (T : QLinearMapFrom w t (ambiguity_quotient_subspace D L))
    : Prop :=
  forall x : QVec w,
    from_map T (lmap (ambiguity_quotient_map D L) x) = lmap q x.

Definition ambiguity_quotient_factor
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t)
    : QLinearMapFrom w t (ambiguity_quotient_subspace D L) :=
  restrict_domain (ambiguity_quotient_subspace D L) q.

Theorem ambiguity_quotient_factor_factorises
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t) :
  descent_obstruction_zero D (precompose L q) ->
  ambiguity_quotient_factorisation
    D L q
    (ambiguity_quotient_factor D L q).
Proof.
  intro Hdesc.
  unfold ambiguity_quotient_factorisation, ambiguity_quotient_factor,
    restrict_domain. simpl.
  apply (postcomposition_descends_invariant_under_quotient D L q Hdesc).
Qed.

Theorem ambiguity_quotient_factor_unique
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t) :
  descent_obstruction_zero D (precompose L q) ->
  forall T : QLinearMapFrom w t (ambiguity_quotient_subspace D L),
    ambiguity_quotient_factorisation D L q T ->
    same_from_map T (ambiguity_quotient_factor D L q).
Proof.
  intros Hdesc T HT.
  intros y Hy.
  destruct Hy as [x Hx].
  rewrite <- Hx.
  rewrite (HT x).
  symmetry.
  exact (ambiguity_quotient_factor_factorises D L q Hdesc x).
Qed.

(** ** Part IX: The central R8 theorem *)

Theorem universal_exact_quotient
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t) :
  descent_obstruction_zero D (precompose L q) ->
  exists T : QLinearMapFrom w t (ambiguity_quotient_subspace D L),
    ambiguity_quotient_factorisation D L q T
    /\
    forall T' : QLinearMapFrom w t (ambiguity_quotient_subspace D L),
      ambiguity_quotient_factorisation D L q T' ->
      same_from_map T' T.
Proof.
  intro Hdesc.
  exists (ambiguity_quotient_factor D L q).
  split.
  - apply (ambiguity_quotient_factor_factorises D L q Hdesc).
  - intros T' HT'.
    apply (ambiguity_quotient_factor_unique D L q Hdesc T' HT').
Qed.

(** ** Part X: Concrete probes *)

(** *** 1. Identity observation: no ambiguity, the quotient map is the
    identity. *)

Example probe_identity_observation_quotient_preserves :
  lmap
    (ambiguity_quotient_map QImagePreimage.id_D18 QImagePreimage.Lp_map)
    (Vector.cons Qc 1 0 (Vector.nil Qc))
  = Vector.cons Qc 1 0 (Vector.nil Qc).
Proof. vm_compute. reflexivity. Qed.

(** *** 2. Zero observation, identity claim: maximal ambiguity, the
    quotient map is zero. *)

Example probe_zero_observation_identity_claim_quotient_zero :
  lmap
    (ambiguity_quotient_map QImagePreimage.zero_D18 QImagePreimage.id_D18)
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
  = zero_vec 2.
Proof. vm_compute. reflexivity. Qed.

(** *** 3. Partial ambiguity: the ambiguous kernel claim is killed. *)

Example probe_partial_ambiguity_kernel_claim_killed :
  lmap
    (ambiguity_quotient_map QImagePreimage.proj_D QImagePreimage.id_D18)
    (lmap QImagePreimage.id_D18 QImagePreimage.kernel_witness)
  = zero_vec 2.
Proof.
  apply ambiguity_quotient_map_kills_kernel_claim.
  apply QImagePreimage.probe_kernel_witness_in_kernel.
Qed.

(** *** 4. Partial ambiguity: the determined coordinate survives. *)

Example probe_partial_ambiguity_exact_coordinate_survives :
  lmap
    (ambiguity_quotient_map QImagePreimage.proj_D QImagePreimage.id_D18)
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
  = Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Proof. vm_compute. reflexivity. Qed.

(** *** 5. Zero-dimensional quotient boundary: no fabricated index. *)

Example probe_dim00_ambiguity_quotient :
  lmap
    (ambiguity_quotient_map QImagePreimage.dim00_D18 QImagePreimage.dim00_D18)
    (zero_vec 0)
  = zero_vec 0.
Proof. apply vec_ext. intro i. inversion i. Qed.

(** *** 6. The generic short exact quotient sequence. *)

Example probe_ambiguity_quotient_short_exact
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  short_exact_subspace
    (ambiguity_subspace D L)
    (ambiguity_quotient_subspace D L)
    (subspace_inclusion (ambiguity_subspace D L))
    (ambiguity_quotient_corestriction D L).
Proof.
  apply ambiguity_quotient_short_exact.
Qed.

(** *** 7. The quotient claim always descends. *)

Example probe_quotient_claim_always_descends
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  descent_obstruction_zero D (quotient_claim D L).
Proof.
  apply quotient_claim_descends.
Qed.

(** *** 8. The generic universal property. *)

Example probe_universal_exact_quotient
    {u v w t : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (q : QLinearMap w t)
    (H : descent_obstruction_zero D (precompose L q)) :
  exists T : QLinearMapFrom w t (ambiguity_quotient_subspace D L),
    ambiguity_quotient_factorisation D L q T
    /\
    forall T' : QLinearMapFrom w t (ambiguity_quotient_subspace D L),
      ambiguity_quotient_factorisation D L q T' ->
      same_from_map T' T.
Proof.
  apply universal_exact_quotient.
  exact H.
Qed.
