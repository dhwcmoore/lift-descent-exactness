(** * The canonical exact value, R3, completing Phase 4

    An exact value for the instance [(D, r, L)] is a vector [x : W]
    attained by the claim [L] at every point of the repair fibre
    [repair_fibre D r] — [forall repair, D repair = r -> L repair =
    x]. Stated this way, the property is vacuous whenever the repair
    fibre is empty: it holds trivially of every [x] when there is no
    repair to test it against. Uniqueness of the exact value therefore
    needs the fibre to be inhabited, i.e. the lifting obstruction to
    vanish — a separate hypothesis from the property itself.

    Repair independence follows from machinery already certified in
    Phase 2: any two repairs of the same residue have the same
    [D]-image (both equal [r]), and once [L] vanishes on [ker D], [L]
    already agrees on any two vectors with equal [D]-images
    ([QImagePreimage.kernel_vanishing_equal_on_equal_images]) — that
    argument is reused here, not reproved. An ambient factor map [M]
    with [L = M after D] supplies a second expression for the same
    value: for any repair [u], [L u = M (D u) = M r], so [L u0 = M r]
    for every repair [u0] and every such [M]. Neither repairs nor
    ambient factor maps need be unique for this to hold — only the
    resulting value at the realised residue is.

    [repair_value] and [factor_value] are therefore witness-dependent
    construction routes, each defined from one selected repair or one
    selected factor map; [exact_value] is the intrinsic,
    witness-independent property they are each proved to satisfy. The
    central theorem, [canonical_exact_value_exists_unique], shows that
    lifting- and descent-obstruction vanishing together produce
    exactly one such value, and [canonical_exact_value_witnessed]
    exposes it concretely as both [L u0] and [M r] for any selected
    repair [u0] and factor map [M]. Four bridge theorems then connect
    this result to Phase 3's exact-profile condition, exact-profile
    witness, full-profile classifier, and operational classifier.

    Unit 23 already proved R8, the universal exact quotient. Unit 24
    therefore completes both R3 and, with it, Phase 4 as a whole.

    This unit does NOT prove or construct: a unique repair or a
    distinguished repair selector; a unique ambient factor map or a
    distinguished ambient extension; equality of linear-map records
    including their proof fields; an exact value when the lifting
    obstruction is nonzero, or in the underdetermined sector;
    constancy of the claim when the descent obstruction is nonzero;
    independence of a selected repair or ambient extension from the
    underlying elimination order as computational objects; any new
    quotient construction, a literal quotient carrier of equivalence
    classes, quotient dimensions, or a basis of the ambiguity space;
    rank-nullity; coordinate-transport results for a later unit;
    preservation or reflection properties of a noninvertible
    presentation map; realisability-obstruction-class or
    presented-claim-equivalence instantiation; admissibility or
    provenance checking; certificate, serialisation, command-line,
    protocol, or runtime semantics; or any generalisation beyond
    finite rational coordinate spaces.

    Positively: every repair yields the same value in the exact
    sector; every ambient factor map yields that same value at [r];
    the value is unique even though the underlying repair and factor
    map generally are not; and exact-profile and exact-verdict
    classification each imply its existence and uniqueness. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QImagePreimage.
From LiftDescent Require Import QDescentFactorisation.
From LiftDescent Require Import QVerdictClassification.
From LiftDescent Require Import QExactnessProfile.

Open Scope Qc_scope.

(** ** Part I: The exact-value property *)

Definition exact_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    : Prop :=
  forall repair : QVec u,
    repair_fibre D r repair ->
    lmap L repair = x.

(** ** Part II: Witness-dependent value constructions *)

Definition repair_value
    {u w : nat}
    (L : QLinearMap u w)
    (repair : QVec u)
    : QVec w :=
  lmap L repair.

Definition factor_value
    {v w : nat}
    (M : QLinearMap v w)
    (r : QVec v)
    : QVec w :=
  lmap M r.

(** ** Part III: Repair independence *)

Theorem repair_values_equal
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (repair1 repair2 : QVec u) :
  QImagePreimage.vanishes_on_kernel D L ->
  repair_fibre D r repair1 ->
  repair_fibre D r repair2 ->
  repair_value L repair1 =
  repair_value L repair2.
Proof.
  intros Hvan Hr1 Hr2.
  unfold repair_value.
  apply (QImagePreimage.kernel_vanishing_equal_on_equal_images D L Hvan).
  unfold repair_fibre in Hr1, Hr2.
  rewrite Hr1, Hr2.
  reflexivity.
Qed.

Theorem repair_value_is_exact
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (repair0 : QVec u) :
  QImagePreimage.vanishes_on_kernel D L ->
  repair_fibre D r repair0 ->
  exact_value D r L (repair_value L repair0).
Proof.
  intros Hvan Hr0.
  unfold exact_value.
  intros repair Hrepair.
  symmetry.
  apply (repair_values_equal D r L repair0 repair Hvan Hr0 Hrepair).
Qed.

(** ** Part IV: The factor-derived value *)

Theorem factor_value_is_exact
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (M : QLinearMap v w) :
  same_lmap L (precompose D M) ->
  exact_value D r L (factor_value M r).
Proof.
  intro HM.
  unfold exact_value.
  intros repair Hrepair.
  unfold factor_value.
  rewrite (HM repair).
  change (lmap M (lmap D repair) = lmap M r).
  unfold repair_fibre in Hrepair.
  rewrite Hrepair.
  reflexivity.
Qed.

(** ** Part V: Repair-factor agreement *)

Theorem repair_factor_value_agreement
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (repair0 : QVec u)
    (M : QLinearMap v w) :
  repair_fibre D r repair0 ->
  same_lmap L (precompose D M) ->
  repair_value L repair0 =
  factor_value M r.
Proof.
  intros Hrepair HM.
  unfold repair_value, factor_value.
  rewrite (HM repair0).
  change (lmap M (lmap D repair0) = lmap M r).
  unfold repair_fibre in Hrepair.
  rewrite Hrepair.
  reflexivity.
Qed.

(** ** Part VI: Factor-map independence on a realised residue *)

Theorem factor_values_equal
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (M1 M2 : QLinearMap v w) :
  lift_obstruction_zero D r ->
  same_lmap L (precompose D M1) ->
  same_lmap L (precompose D M2) ->
  factor_value M1 r =
  factor_value M2 r.
Proof.
  intros Hlift HM1 HM2.
  destruct Hlift as [repair0 Hrepair0].
  rewrite <- (repair_factor_value_agreement D r L repair0 M1 Hrepair0 HM1).
  rewrite <- (repair_factor_value_agreement D r L repair0 M2 Hrepair0 HM2).
  reflexivity.
Qed.

(** ** Part VII: Characterisation and uniqueness *)

Theorem exact_value_iff_repair_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (repair0 : QVec u)
    (Hvanish :
      QImagePreimage.vanishes_on_kernel D L)
    (Hrepair :
      repair_fibre D r repair0)
    (x : QVec w) :
  exact_value D r L x
  <->
  x = repair_value L repair0.
Proof.
  split.
  - intro Hexact.
    unfold exact_value in Hexact.
    symmetry.
    apply (Hexact repair0 Hrepair).
  - intro Heq.
    rewrite Heq.
    apply (repair_value_is_exact D r L repair0 Hvanish Hrepair).
Qed.

Theorem exact_value_unique_on_nonempty_fibre
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (repair0 : QVec u) :
  repair_fibre D r repair0 ->
  forall x1 x2 : QVec w,
    exact_value D r L x1 ->
    exact_value D r L x2 ->
    x1 = x2.
Proof.
  intros Hrepair0 x1 x2 Hx1 Hx2.
  unfold exact_value in Hx1, Hx2.
  rewrite <- (Hx1 repair0 Hrepair0).
  rewrite <- (Hx2 repair0 Hrepair0).
  reflexivity.
Qed.

(** ** Part VIII: Existence *)

Theorem canonical_exact_value_exists_from_repair
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (repair0 : QVec u) :
  QImagePreimage.vanishes_on_kernel D L ->
  repair_fibre D r repair0 ->
  exists x : QVec w,
    exact_value D r L x
    /\
    x = repair_value L repair0.
Proof.
  intros Hvan Hrepair0.
  exists (repair_value L repair0).
  split.
  - apply (repair_value_is_exact D r L repair0 Hvan Hrepair0).
  - reflexivity.
Qed.

(** ** Part IX: The central R3 theorem *)

Theorem canonical_exact_value_exists_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  lift_obstruction_zero D r ->
  descent_obstruction_zero D L ->
  exists! x : QVec w,
    exact_value D r L x.
Proof.
  intros Hlift Hdescent.
  apply descent_obstruction_zero_iff_kernel_vanishing in Hdescent.
  destruct Hlift as [repair0 Hrepair0].
  exists (repair_value L repair0).
  split.
  - apply (repair_value_is_exact D r L repair0 Hdescent Hrepair0).
  - intros x Hx.
    symmetry.
    apply (exact_value_iff_repair_value D r L repair0 Hdescent Hrepair0 x).
    exact Hx.
Qed.

(** ** Part X: The witnessed [x = L u0 = M r] equation *)

Theorem canonical_exact_value_witnessed
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  lift_obstruction_zero D r ->
  descent_obstruction_zero D L ->
  exists
    (repair0 : QVec u)
    (M : QLinearMap v w)
    (x : QVec w),
      repair_fibre D r repair0
      /\
      same_lmap L (precompose D M)
      /\
      exact_value D r L x
      /\
      x = repair_value L repair0
      /\
      x = factor_value M r.
Proof.
  intros Hlift Hdescent.
  destruct Hlift as [repair0 Hrepair0].
  destruct Hdescent as [M HM].
  assert (Hvan : QImagePreimage.vanishes_on_kernel D L).
  { apply descent_obstruction_zero_iff_kernel_vanishing. exists M. exact HM. }
  exists repair0, M, (repair_value L repair0).
  split.
  - exact Hrepair0.
  - split.
    + exact HM.
    + split.
      * apply (repair_value_is_exact D r L repair0 Hvan Hrepair0).
      * split.
        -- reflexivity.
        -- apply (repair_factor_value_agreement D r L repair0 M Hrepair0 HM).
Qed.

(** ** Part XI: Phase 3 bridges *)

Theorem profile_realisable_exact_condition_has_unique_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  exactness_profile_condition
    D r L
    ProfileRealisableExact ->
  exists! x : QVec w,
    exact_value D r L x.
Proof.
  intro Hcond.
  simpl in Hcond.
  destruct Hcond as [Hlift Hdescent].
  apply (canonical_exact_value_exists_unique D r L Hlift Hdescent).
Qed.

Theorem profile_realisable_exact_witness_has_unique_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  exactness_profile_witness
    D r L
    ProfileRealisableExact ->
  exists! x : QVec w,
    exact_value D r L x.
Proof.
  intro Hwit.
  apply profile_realisable_exact_condition_has_unique_value.
  apply (exactness_profile_witness_iff_condition D r L ProfileRealisableExact).
  exact Hwit.
Qed.

Theorem classified_realisable_exact_has_unique_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_exactness_profile D r L =
    ProfileRealisableExact ->
  exists! x : QVec w,
    exact_value D r L x.
Proof.
  intro Heq.
  apply (classify_exactness_profile_realisable_exact_iff D r L) in Heq.
  destruct Heq as [Hlift Hdescent].
  apply (canonical_exact_value_exists_unique D r L Hlift Hdescent).
Qed.

Theorem classified_operational_exact_has_unique_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_operational_verdict D r L =
    VerdictExact ->
  exists! x : QVec w,
    exact_value D r L x.
Proof.
  intro Heq.
  apply (classify_operational_verdict_exact_iff D r L) in Heq.
  destruct Heq as [Hlift Hdescent].
  apply (canonical_exact_value_exists_unique D r L Hlift Hdescent).
Qed.

(** ** Part XII: Concrete probes *)

(** *** 1. Proper projection: the canonical value is the first
    coordinate of the residue. *)

Example probe_projection_canonical_value :
  exact_value
    QImagePreimage.proj_D
    (Vector.cons Qc 1 1
      (Vector.cons Qc 0 0
        (Vector.nil Qc)))
    QImagePreimage.L_map
    (Vector.cons Qc 1 0
      (Vector.nil Qc)).
Proof.
  assert
    (Hrepair :
      repair_fibre
        QImagePreimage.proj_D
        (Vector.cons Qc 1 1
          (Vector.cons Qc 0 0
            (Vector.nil Qc)))
        (Vector.cons Qc 1 1
          (Vector.cons Qc 0 0
            (Vector.nil Qc)))).
  {
    vm_compute.
    reflexivity.
  }
  pose proof
    (repair_value_is_exact
      QImagePreimage.proj_D
      (Vector.cons Qc 1 1
        (Vector.cons Qc 0 0
          (Vector.nil Qc)))
      QImagePreimage.L_map
      (Vector.cons Qc 1 1
        (Vector.cons Qc 0 0
          (Vector.nil Qc)))
      QImagePreimage.probe_proj_kernel_vanishing
      Hrepair) as Hexact.
  replace
    (Vector.cons Qc 1 0
      (Vector.nil Qc))
    with
    (repair_value
      QImagePreimage.L_map
      (Vector.cons Qc 1 1
        (Vector.cons Qc 0 0
          (Vector.nil Qc)))).
  - exact Hexact.
  - vm_compute.
    reflexivity.
Qed.

(** *** 2. Two distinct repairs give the same value. *)

Example probe_projection_distinct_repairs_same_value :
  repair_value
    QImagePreimage.L_map
    (Vector.cons Qc 1 1
      (Vector.cons Qc 0 0
        (Vector.nil Qc)))
  =
  repair_value
    QImagePreimage.L_map
    (Vector.cons Qc 1 1
      (Vector.cons Qc 1 0
        (Vector.nil Qc))).
Proof.
  apply
    (repair_values_equal
      QImagePreimage.proj_D
      (Vector.cons Qc 1 1
        (Vector.cons Qc 0 0
          (Vector.nil Qc)))
      QImagePreimage.L_map
      (Vector.cons Qc 1 1
        (Vector.cons Qc 0 0
          (Vector.nil Qc)))
      (Vector.cons Qc 1 1
        (Vector.cons Qc 1 0
          (Vector.nil Qc)))).
  - apply QImagePreimage.probe_proj_kernel_vanishing.
  - vm_compute.
    reflexivity.
  - vm_compute.
    reflexivity.
Qed.

(** *** 3. Repair and constructive factor map agree. *)

Example probe_projection_repair_factor_agreement :
  repair_value
    QImagePreimage.L_map
    (Vector.cons Qc 1 1
      (Vector.cons Qc 0 0
        (Vector.nil Qc)))
  =
  factor_value
    (induced_ambient_map
      QImagePreimage.proj_D
      QImagePreimage.L_map
      QImagePreimage.probe_proj_kernel_vanishing)
    (Vector.cons Qc 1 1
      (Vector.cons Qc 0 0
        (Vector.nil Qc))).
Proof.
  apply
    (repair_factor_value_agreement
      QImagePreimage.proj_D
      (Vector.cons Qc 1 1
        (Vector.cons Qc 0 0
          (Vector.nil Qc)))
      QImagePreimage.L_map
      (Vector.cons Qc 1 1
        (Vector.cons Qc 0 0
          (Vector.nil Qc)))
      (induced_ambient_map
        QImagePreimage.proj_D
        QImagePreimage.L_map
        QImagePreimage.probe_proj_kernel_vanishing)).
  - vm_compute.
    reflexivity.
  - apply induced_ambient_map_factorisation.
Qed.

(** *** 4. Generic factor-map independence. *)

Example probe_factor_values_independent
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (M1 M2 : QLinearMap v w)
    (Hlift : lift_obstruction_zero D r)
    (HM1 : same_lmap L (precompose D M1))
    (HM2 : same_lmap L (precompose D M2)) :
  factor_value M1 r =
  factor_value M2 r.
Proof.
  exact
    (factor_values_equal
      D r L M1 M2
      Hlift HM1 HM2).
Qed.

(** *** 5. Zero map with zero claim: every repair yields zero. *)

Example probe_zero_map_zero_claim_exact_value :
  exact_value
    QImagePreimage.zero_D18
    (zero_vec 2)
    QImagePreimage.zero_D18
    (zero_vec 2).
Proof.
  unfold exact_value.
  intros repair Hrepair.
  exact Hrepair.
Qed.

(** *** 6. Zero-dimensional boundary: no fabricated index. *)

Example probe_dim00_exact_value :
  exact_value
    QImagePreimage.dim00_D18
    (zero_vec 0)
    QImagePreimage.dim00_D18
    (zero_vec 0).
Proof.
  unfold exact_value.
  intros repair _.
  apply vec_ext.
  intro i.
  inversion i.
Qed.

(** *** 7. Generic R3 existence and uniqueness. *)

Example probe_every_exact_instance_has_unique_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (Hlift : lift_obstruction_zero D r)
    (Hdescent : descent_obstruction_zero D L) :
  exists! x : QVec w,
    exact_value D r L x.
Proof.
  apply canonical_exact_value_exists_unique.
  - exact Hlift.
  - exact Hdescent.
Qed.

(** *** 8. Classified full-profile exactness gives a unique value. *)

Example probe_classified_realisable_exact_has_unique_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (Hclass :
      classify_exactness_profile D r L =
      ProfileRealisableExact) :
  exists! x : QVec w,
    exact_value D r L x.
Proof.
  apply classified_realisable_exact_has_unique_value.
  exact Hclass.
Qed.
