(** * Finite kernel spanning and the finite vanishing test

    Unit 20a constructed the kernel projection [K_D = I - S_D D] and its
    finite family of projected standard-basis generators [g_i = K_D(e_i)],
    together with the coordinate expansion [K_D x = sum_i x_i g_i]
    ([kernel_projection_coordinate_expansion]) and its kernel-vector
    specialisation ([kernel_vector_coordinate_expansion]). This unit
    identifies the generator family with the matrix of the kernel
    projection ([kernel_generators := matrix_of_lmap (kernel_projection
    D)]) so that the coordinate expansion becomes the existing
    [matrix_of_lmap_correct] theorem rather than a re-derivation, and
    proves the finite spanning identity this presentation is for: the
    generator combinations are exactly [ker D]
    ([kernel_generator_span_iff_kernel]).

    The second half establishes the finite test the later constructive
    gauge-witness unit needs: a linear functional vanishes on all of
    [ker D] exactly when it vanishes on the finitely many generators
    ([kernel_zero_iff_kernel_generators_zero]). Both directions of this
    equivalence remain universally quantified — this unit does not
    convert a failing universal check into an existential nonzero
    generator witness.

    This unit does NOT prove: gauge-witness soundness or completeness;
    the R5 equivalence; constructive extraction of a nonzero generator
    from failed kernel vanishing; linear independence of the generators;
    that the generators form a basis; rank-nullity; a second kernel
    projection or matrix representation; row reduction or rank;
    verdict classification; the four-sector profile; canonical exact
    values; the universal quotient; ROC or PCE instantiation; or
    certificate, JSON, or executable semantics. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QFiniteCoordinates.
From LiftDescent Require Import QImagePreimage.
From LiftDescent Require Import QKernelProjection.

Open Scope Qc_scope.

(** ** 1. The generator matrix

    The matrix of the kernel projection: its [i]-th column is
    [K_D(e_i) = kernel_generator D i], by [kernel_generators_nth] below.
    No second enumeration of the columns is introduced. *)

Definition kernel_generators
    {n m : nat}
    (D : QLinearMap n m)
    : QMatrix n n :=
  matrix_of_lmap (kernel_projection D).

(** ** 2. Linear combination of kernel generators *)

Definition kernel_generator_combination
    {n m : nat}
    (D : QLinearMap n m)
    (coefficients : QVec n)
    : QVec n :=
  matrix_apply (kernel_generators D) coefficients.

(** ** 3. Generator-span predicate *)

Definition kernel_generator_span
    {n m : nat}
    (D : QLinearMap n m)
    (x : QVec n)
    : Prop :=
  exists coefficients : QVec n,
    x = kernel_generator_combination D coefficients.

(** ** 4. Columns are the Unit 20a generators *)

Theorem kernel_generators_nth
    {n m : nat}
    (D : QLinearMap n m)
    (i : Fin.t n) :
  Vector.nth (kernel_generators D) i =
  kernel_generator D i.
Proof.
  unfold kernel_generators, matrix_of_lmap.
  rewrite (Vector.nth_map _ _ i i eq_refl).
  rewrite (all_positions_nth n i).
  unfold kernel_generator.
  reflexivity.
Qed.

(** ** 5. Generator combination equals kernel projection *)

Theorem kernel_generator_combination_eq_projection
    {n m : nat}
    (D : QLinearMap n m)
    (x : QVec n) :
  kernel_generator_combination D x =
  lmap (kernel_projection D) x.
Proof.
  unfold kernel_generator_combination, kernel_generators.
  apply matrix_of_lmap_correct.
Qed.

(** ** 6. Every generator combination lies in the kernel *)

Theorem kernel_generator_combination_in_kernel
    {n m : nat}
    (D : QLinearMap n m)
    (coefficients : QVec n) :
  kernel D (kernel_generator_combination D coefficients).
Proof.
  rewrite (kernel_generator_combination_eq_projection D coefficients).
  apply kernel_projection_in_kernel.
Qed.

(** ** 7. Every kernel vector has its canonical generator expansion *)

Theorem kernel_vector_generator_expansion
    {n m : nat}
    (D : QLinearMap n m)
    (k : QVec n) :
  kernel D k ->
  k = kernel_generator_combination D k.
Proof.
  intro Hk.
  rewrite (kernel_generator_combination_eq_projection D k).
  symmetry.
  apply kernel_projection_fixes_kernel.
  exact Hk.
Qed.

(** ** 8. Soundness of the generator span *)

Theorem kernel_generator_span_sound
    {n m : nat}
    (D : QLinearMap n m)
    (x : QVec n) :
  kernel_generator_span D x ->
  kernel D x.
Proof.
  intros [coefficients Hc].
  rewrite Hc.
  apply kernel_generator_combination_in_kernel.
Qed.

(** ** 9. Completeness of the generator span *)

Theorem kernel_generator_span_complete
    {n m : nat}
    (D : QLinearMap n m)
    (k : QVec n) :
  kernel D k ->
  kernel_generator_span D k.
Proof.
  intro Hk.
  exists k.
  apply kernel_vector_generator_expansion.
  exact Hk.
Qed.

(** ** 10. The finite generator span is exactly the kernel *)

Theorem kernel_generator_span_iff_kernel
    {n m : nat}
    (D : QLinearMap n m)
    (x : QVec n) :
  kernel_generator_span D x <-> kernel D x.
Proof.
  split.
  - apply kernel_generator_span_sound.
  - apply kernel_generator_span_complete.
Qed.

(** ** 11. Pointwise-zero finite-sum helper *)

Lemma lmap_vsum_pointwise_zero
    {n p q : nat}
    (L : QLinearMap n p)
    (vectors : Vector.t (QVec n) q) :
  (forall i : Fin.t q,
      lmap L (Vector.nth vectors i) = zero_vec p) ->
  lmap L (vsum vectors) = zero_vec p.
Proof.
  induction vectors as [| v q' vectors' IH].
  - intros _. simpl. apply lmap_preserves_zero.
  - intro H.
    pose proof (H Fin.F1) as HF1. simpl in HF1.
    simpl vsum.
    rewrite (lmap_add L v (vsum vectors')).
    rewrite HF1.
    rewrite vadd_0_l.
    apply IH.
    intro i.
    pose proof (H (Fin.FS i)) as HFS. simpl in HFS.
    exact HFS.
Qed.

(** ** 12. Vanishing on generators implies vanishing on the whole kernel *)

Theorem kernel_generators_zero_implies_kernel_zero
    {n m p : nat}
    (D : QLinearMap n m)
    (L : QLinearMap n p) :
  (forall i : Fin.t n,
      lmap L (kernel_generator D i) = zero_vec p) ->
  forall k : QVec n,
    kernel D k ->
    lmap L k = zero_vec p.
Proof.
  intros Hgen k Hk.
  rewrite (kernel_vector_generator_expansion D k Hk).
  unfold kernel_generator_combination, matrix_apply.
  apply lmap_vsum_pointwise_zero.
  intro i.
  rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl).
  rewrite (kernel_generators_nth D i).
  rewrite (lmap_scale L (Vector.nth k i) (kernel_generator D i)).
  rewrite (Hgen i).
  apply vec_ext. intro j. rewrite vscale_nth, zero_vec_nth. ring.
Qed.

(** ** 13. Vanishing on the whole kernel implies vanishing on generators *)

Theorem kernel_zero_implies_kernel_generators_zero
    {n m p : nat}
    (D : QLinearMap n m)
    (L : QLinearMap n p) :
  (forall k : QVec n,
      kernel D k ->
      lmap L k = zero_vec p) ->
  forall i : Fin.t n,
    lmap L (kernel_generator D i) = zero_vec p.
Proof.
  intros H i.
  apply H.
  apply kernel_generator_in_kernel.
Qed.

(** ** 14. Finite generator criterion for kernel vanishing *)

Theorem kernel_zero_iff_kernel_generators_zero
    {n m p : nat}
    (D : QLinearMap n m)
    (L : QLinearMap n p) :
  (forall k : QVec n,
      kernel D k ->
      lmap L k = zero_vec p) <->
  (forall i : Fin.t n,
      lmap L (kernel_generator D i) = zero_vec p).
Proof.
  split.
  - apply kernel_zero_implies_kernel_generators_zero.
  - apply kernel_generators_zero_implies_kernel_zero.
Qed.

(** ** 15. Concrete probes *)

(** *** 15.1. Zero-dimensional domain: the unique [QVec 0] is a generator
    combination of itself, with no [Fin.t 0] witness required. *)

Example probe_dim0_domain_unique_representation
    {m : nat} (D : QLinearMap 0 m) (x : QVec 0) :
  kernel_generator_span D x.
Proof.
  exists x.
  apply vec_ext. intro i. inversion i.
Qed.

(** *** 15.2. Zero map: [K_D = id], so generator combinations reproduce
    the ordinary standard-basis coordinate expansion. *)

Example probe_zero_map_generator_combination_is_identity (x : QVec 2) :
  kernel_generator_combination QImagePreimage.zero_D18 x = x.
Proof.
  rewrite (kernel_generator_combination_eq_projection QImagePreimage.zero_D18 x).
  apply probe_zero_map_projection_is_identity.
Qed.

(** *** 15.3. Identity map: [K_D = 0], so every generator combination is
    zero. *)

Example probe_identity_generator_combination_zero (x : QVec 2) :
  kernel_generator_combination QImagePreimage.id_D18 x = zero_vec 2.
Proof.
  rewrite (kernel_generator_combination_eq_projection QImagePreimage.id_D18 x).
  apply probe_identity_projection_is_zero.
Qed.

(** *** 15.4. Nontrivial proper kernel: [D(x0,x1) = x0]. The first
    standard-basis vector is not in [ker D], so its projected generator
    is zero; the second already lies in [ker D], so it survives
    unchanged; and a vector with [x0 = 0] receives its expected
    generator expansion. The map is built locally, mirroring Unit 19a's
    own [coordinate_functional] construction, rather than importing
    [QLinearFunctional] for a single probe. *)

Let probe4_fun (x : QVec 2) : QVec 1 :=
  Vector.cons Qc (Vector.nth x Fin.F1) 0 (Vector.nil Qc).

Let probe4_add (x y : QVec 2) :
  probe4_fun (vadd x y) = vadd (probe4_fun x) (probe4_fun y).
Proof.
  apply vec_ext. intro k.
  pattern k. apply Fin.caseS'.
  - simpl. apply vadd_nth.
  - intro p. inversion p.
Qed.

Let probe4_scale (a : Qc) (x : QVec 2) :
  probe4_fun (vscale a x) = vscale a (probe4_fun x).
Proof.
  apply vec_ext. intro k.
  pattern k. apply Fin.caseS'.
  - simpl. apply vscale_nth.
  - intro p. inversion p.
Qed.

Let probe4_D : QLinearMap 2 1 :=
  {| lmap := probe4_fun; lmap_add := probe4_add; lmap_scale := probe4_scale |}.

Example probe4_generators :
  kernel_generator probe4_D Fin.F1 = zero_vec 2
  /\ kernel_generator probe4_D (Fin.FS Fin.F1) = standard_basis (Fin.FS Fin.F1).
Proof. split; vm_compute; reflexivity. Qed.

Example probe4_kernel_vector_expansion :
  kernel probe4_D (Vector.cons Qc 0 1 (Vector.cons Qc 1 0 (Vector.nil Qc)))
  /\ Vector.cons Qc 0 1 (Vector.cons Qc 1 0 (Vector.nil Qc))
     = kernel_generator_combination probe4_D
         (Vector.cons Qc 0 1 (Vector.cons Qc 1 0 (Vector.nil Qc))).
Proof.
  split.
  - vm_compute. reflexivity.
  - apply kernel_vector_generator_expansion. vm_compute. reflexivity.
Qed.
