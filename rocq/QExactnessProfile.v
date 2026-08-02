(** * The full four-sector exactness profile and its collapse, R7

    Unit 21 constructed the three-way operational trichotomy
    ([operational_verdict]), deliberately collapsing both
    lifting-obstructed sectors: once [decide_lift_obstruction] returns
    obstructed, [classify_operational_verdict] never inspects
    [decide_descent_obstruction] at all, so the two sectors

    [[
      [r] <> 0,  [L] = 0
      [r] <> 0,  [L] <> 0
    ]]

    both surface as [VerdictObstructed], with no trace of which one
    held.

    This unit restores the independent status of both axes under
    failed lifting. The full profile is exactly the pair of the two
    obstruction statuses — [lift_obstruction_zero]/[lift_obstructed]
    together with [descent_obstruction_zero]/[descent_obstructed] —
    giving four sectors rather than three. The profile classifier,
    [classify_exactness_profile], reuses Unit 21's two constructive
    decisions verbatim, but — unlike the operational classifier —
    calls [decide_descent_obstruction] in *both* branches of
    [decide_lift_obstruction], not only the realisable one.

    Every sector carries positive evidence for both axes: a repair
    when lifting is zero, a separator witness when lifting is
    obstructed; an ambient factor map when descent is zero, a gauge
    witness when descent is obstructed. [exactness_profile_witness] is
    a proposition carrying this evidence, not a certificate format or
    an extracted runtime representation, and none of its components —
    repair, separator, factor map, or gauge direction — is claimed
    unique or canonical, nor independent of the underlying elimination
    order.

    [collapse_exactness_profile] is the forgetful map back onto
    [operational_verdict]. It is intentionally non-injective: the two
    realisable sectors are preserved exactly, but the two
    lifting-obstructed sectors are both sent to [VerdictObstructed].
    The central computational theorem of this unit,
    [classify_exactness_profile_collapse], shows this collapse
    commutes with classification: running the full-profile classifier
    and then forgetting agrees, on every instance, with running the
    Unit 21 operational classifier directly.

    This unit completes R7. It does NOT prove or construct: a fifth or
    inadmissible sector; admissibility or provenance checking of any
    kind; an application-level verdict; a quotient carrier type for
    either cokernel, or literal quotient elements representing the
    residue or claim class; the canonical cokernel isomorphism as a
    constructed quotient-space map; a canonical or unique separator,
    gauge witness, repair, or ambient factor map; a canonical exact
    value, or its independence from the particular repair or factor
    map chosen; a basis of the ambiguity space or its dimension;
    rank-nullity; the universal exact quotient; coordinate-change
    invariance; preservation or reflection properties of a
    noninvertible presentation map; realisability-obstruction-class or
    presented-claim-equivalence instantiation; certificate,
    serialisation, command-line, or protocol semantics; extraction of
    the witness relation into a runtime package; or any generalisation
    beyond finite rational coordinate spaces. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QImagePreimage.
From LiftDescent Require Import QDescentFactorisation.
From LiftDescent Require Import QLinearFunctional.
From LiftDescent Require Import QSeparatorWitness.
From LiftDescent Require Import QGaugeWitness.
From LiftDescent Require Import QVerdictClassification.

Open Scope Qc_scope.

(** ** Part I: The exactness-profile type

    Exactly the Cartesian product of the two independent obstruction
    statuses: two possibilities for lifting, two for descent, four
    constructors. *)

Inductive exactness_profile : Type :=
| ProfileRealisableExact
| ProfileRealisableUnderdetermined
| ProfileObstructedButDescending
| ProfileObstructedAndNonDescending.

(** ** Part II: The witness-bearing profile relation *)

Inductive exactness_profile_witness
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    : exactness_profile -> Prop :=

| WitnessProfileRealisableExact :
    forall (u0 : QVec u) (M : QLinearMap v w),
      repair_fibre D r u0 ->
      same_lmap L (precompose D M) ->
      exactness_profile_witness D r L ProfileRealisableExact

| WitnessProfileRealisableUnderdetermined :
    forall (u0 k : QVec u),
      repair_fibre D r u0 ->
      gauge_witness D L k ->
      exactness_profile_witness D r L ProfileRealisableUnderdetermined

| WitnessProfileObstructedButDescending :
    forall (y : QLinearFunctional v) (M : QLinearMap v w),
      separator_witness D r y ->
      same_lmap L (precompose D M) ->
      exactness_profile_witness D r L ProfileObstructedButDescending

| WitnessProfileObstructedAndNonDescending :
    forall (y : QLinearFunctional v) (k : QVec u),
      separator_witness D r y ->
      gauge_witness D L k ->
      exactness_profile_witness D r L ProfileObstructedAndNonDescending.

(** ** Part III: Semantic profile condition *)

Definition exactness_profile_condition
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (profile : exactness_profile)
    : Prop :=
  match profile with
  | ProfileRealisableExact =>
      lift_obstruction_zero D r /\ descent_obstruction_zero D L
  | ProfileRealisableUnderdetermined =>
      lift_obstruction_zero D r /\ descent_obstructed D L
  | ProfileObstructedButDescending =>
      lift_obstructed D r /\ descent_obstruction_zero D L
  | ProfileObstructedAndNonDescending =>
      lift_obstructed D r /\ descent_obstructed D L
  end.

(** ** Part IV: The full-profile classifier

    Unlike [classify_operational_verdict], the descent decision is
    called in both branches of the lifting decision. *)

Definition classify_exactness_profile
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    : exactness_profile :=
  match decide_lift_obstruction D r with
  | left _ =>
      match decide_descent_obstruction D L with
      | left _ => ProfileObstructedAndNonDescending
      | right _ => ProfileObstructedButDescending
      end
  | right _ =>
      match decide_descent_obstruction D L with
      | left _ => ProfileRealisableUnderdetermined
      | right _ => ProfileRealisableExact
      end
  end.

(** ** Part V: The collapse into the operational verdict *)

Definition collapse_exactness_profile
    (profile : exactness_profile)
    : operational_verdict :=
  match profile with
  | ProfileRealisableExact => VerdictExact
  | ProfileRealisableUnderdetermined => VerdictUnderdetermined
  | ProfileObstructedButDescending => VerdictObstructed
  | ProfileObstructedAndNonDescending => VerdictObstructed
  end.

(** ** Part VI: Witness and semantic-condition equivalence *)

Theorem exactness_profile_witness_iff_condition
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (profile : exactness_profile) :
  exactness_profile_witness D r L profile
  <->
  exactness_profile_condition D r L profile.
Proof.
  destruct profile; simpl.
  - split.
    + intro H.
      inversion H as [u0 M Hr Hf | | | ].
      split.
      * exists u0. exact Hr.
      * exists M. exact Hf.
    + intros [Hlz Hdz].
      destruct Hlz as [u0 Hu0].
      destruct Hdz as [M Hf].
      apply (WitnessProfileRealisableExact D r L u0 M Hu0 Hf).
  - split.
    + intro H.
      inversion H as [ | u0 k Hr Hg | | ].
      split.
      * exists u0. exact Hr.
      * apply (gauge_witness_sound D L k Hg).
    + intros [Hlz Hdo].
      destruct Hlz as [u0 Hu0].
      destruct (gauge_witness_complete D L Hdo) as [k Hk].
      apply (WitnessProfileRealisableUnderdetermined D r L u0 k Hu0 Hk).
  - split.
    + intro H.
      inversion H as [ | | y M Hy Hf | ].
      split.
      * apply (separator_witness_sound D r y Hy).
      * exists M. exact Hf.
    + intros [Hobs Hdz].
      destruct (separator_witness_complete D r Hobs) as [y Hy].
      destruct Hdz as [M Hf].
      apply (WitnessProfileObstructedButDescending D r L y M Hy Hf).
  - split.
    + intro H.
      inversion H as [ | | | y k Hy Hg].
      split.
      * apply (separator_witness_sound D r y Hy).
      * apply (gauge_witness_sound D L k Hg).
    + intros [Hobs Hdo].
      destruct (separator_witness_complete D r Hobs) as [y Hy].
      destruct (gauge_witness_complete D L Hdo) as [k Hk].
      apply (WitnessProfileObstructedAndNonDescending D r L y k Hy Hk).
Qed.

(** ** Part VII: Classifier witness and semantic theorems *)

Theorem classify_exactness_profile_witness
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  exactness_profile_witness D r L (classify_exactness_profile D r L).
Proof.
  unfold classify_exactness_profile.
  destruct (decide_lift_obstruction D r) as [Hobs | Hzero].
  - destruct (decide_descent_obstruction D L) as [Hdobs | Hdzero].
    + apply (exactness_profile_witness_iff_condition D r L
               ProfileObstructedAndNonDescending).
      simpl. split; assumption.
    + apply (exactness_profile_witness_iff_condition D r L
               ProfileObstructedButDescending).
      simpl. split; assumption.
  - destruct (decide_descent_obstruction D L) as [Hdobs | Hdzero].
    + apply (exactness_profile_witness_iff_condition D r L
               ProfileRealisableUnderdetermined).
      simpl. split; assumption.
    + apply (exactness_profile_witness_iff_condition D r L
               ProfileRealisableExact).
      simpl. split; assumption.
Qed.

Theorem classify_exactness_profile_condition
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  exactness_profile_condition D r L (classify_exactness_profile D r L).
Proof.
  apply (exactness_profile_witness_iff_condition D r L
           (classify_exactness_profile D r L)).
  apply classify_exactness_profile_witness.
Qed.

(** ** Part VIII: Uniqueness *)

Theorem exactness_profile_condition_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (profile1 profile2 : exactness_profile) :
  exactness_profile_condition D r L profile1 ->
  exactness_profile_condition D r L profile2 ->
  profile1 = profile2.
Proof.
  destruct profile1, profile2; simpl; intros H1 H2; try reflexivity.
  - exfalso. destruct H1 as [_ Hdz1]. destruct H2 as [_ Hdo2]. apply Hdo2. exact Hdz1.
  - exfalso. destruct H1 as [Hlz1 _]. destruct H2 as [Hobs2 _]. apply Hobs2. exact Hlz1.
  - exfalso. destruct H1 as [Hlz1 _]. destruct H2 as [Hobs2 _]. apply Hobs2. exact Hlz1.
  - exfalso. destruct H1 as [_ Hdo1]. destruct H2 as [_ Hdz2]. apply Hdo1. exact Hdz2.
  - exfalso. destruct H1 as [Hlz1 _]. destruct H2 as [Hobs2 _]. apply Hobs2. exact Hlz1.
  - exfalso. destruct H1 as [Hlz1 _]. destruct H2 as [Hobs2 _]. apply Hobs2. exact Hlz1.
  - exfalso. destruct H1 as [Hobs1 _]. destruct H2 as [Hlz2 _]. apply Hobs1. exact Hlz2.
  - exfalso. destruct H1 as [Hobs1 _]. destruct H2 as [Hlz2 _]. apply Hobs1. exact Hlz2.
  - exfalso. destruct H1 as [_ Hdz1]. destruct H2 as [_ Hdo2]. apply Hdo2. exact Hdz1.
  - exfalso. destruct H1 as [Hobs1 _]. destruct H2 as [Hlz2 _]. apply Hobs1. exact Hlz2.
  - exfalso. destruct H1 as [Hobs1 _]. destruct H2 as [Hlz2 _]. apply Hobs1. exact Hlz2.
  - exfalso. destruct H1 as [_ Hdo1]. destruct H2 as [_ Hdz2]. apply Hdo1. exact Hdz2.
Qed.

Theorem exactness_profile_witness_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (profile1 profile2 : exactness_profile) :
  exactness_profile_witness D r L profile1 ->
  exactness_profile_witness D r L profile2 ->
  profile1 = profile2.
Proof.
  intros H1 H2.
  apply (exactness_profile_condition_unique D r L profile1 profile2).
  - apply (exactness_profile_witness_iff_condition D r L profile1). exact H1.
  - apply (exactness_profile_witness_iff_condition D r L profile2). exact H2.
Qed.

(** ** Part IX: Profile completeness *)

Theorem exactness_profile_exists_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  exists! profile : exactness_profile,
    exactness_profile_witness D r L profile.
Proof.
  exists (classify_exactness_profile D r L).
  split.
  - apply classify_exactness_profile_witness.
  - intro profile'. intro Hp'.
    apply (exactness_profile_witness_unique D r L
             (classify_exactness_profile D r L) profile').
    + apply classify_exactness_profile_witness.
    + exact Hp'.
Qed.

(** ** Part X: Classifier characterisations *)

Theorem classify_exactness_profile_realisable_exact_iff
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_exactness_profile D r L = ProfileRealisableExact
  <->
  lift_obstruction_zero D r /\ descent_obstruction_zero D L.
Proof.
  split.
  - intro Heq.
    pose proof (classify_exactness_profile_condition D r L) as Hc.
    rewrite Heq in Hc. simpl in Hc. exact Hc.
  - intro Hcond.
    apply (exactness_profile_condition_unique D r L
             (classify_exactness_profile D r L) ProfileRealisableExact).
    + apply classify_exactness_profile_condition.
    + simpl. exact Hcond.
Qed.

Theorem classify_exactness_profile_realisable_underdetermined_iff
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_exactness_profile D r L = ProfileRealisableUnderdetermined
  <->
  lift_obstruction_zero D r /\ descent_obstructed D L.
Proof.
  split.
  - intro Heq.
    pose proof (classify_exactness_profile_condition D r L) as Hc.
    rewrite Heq in Hc. simpl in Hc. exact Hc.
  - intro Hcond.
    apply (exactness_profile_condition_unique D r L
             (classify_exactness_profile D r L) ProfileRealisableUnderdetermined).
    + apply classify_exactness_profile_condition.
    + simpl. exact Hcond.
Qed.

Theorem classify_exactness_profile_obstructed_but_descending_iff
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_exactness_profile D r L = ProfileObstructedButDescending
  <->
  lift_obstructed D r /\ descent_obstruction_zero D L.
Proof.
  split.
  - intro Heq.
    pose proof (classify_exactness_profile_condition D r L) as Hc.
    rewrite Heq in Hc. simpl in Hc. exact Hc.
  - intro Hcond.
    apply (exactness_profile_condition_unique D r L
             (classify_exactness_profile D r L) ProfileObstructedButDescending).
    + apply classify_exactness_profile_condition.
    + simpl. exact Hcond.
Qed.

Theorem classify_exactness_profile_obstructed_and_non_descending_iff
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_exactness_profile D r L = ProfileObstructedAndNonDescending
  <->
  lift_obstructed D r /\ descent_obstructed D L.
Proof.
  split.
  - intro Heq.
    pose proof (classify_exactness_profile_condition D r L) as Hc.
    rewrite Heq in Hc. simpl in Hc. exact Hc.
  - intro Hcond.
    apply (exactness_profile_condition_unique D r L
             (classify_exactness_profile D r L) ProfileObstructedAndNonDescending).
    + apply classify_exactness_profile_condition.
    + simpl. exact Hcond.
Qed.

(** ** Part XI: Collapse theorems *)

Theorem exactness_profile_witness_collapses
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (profile : exactness_profile) :
  exactness_profile_witness D r L profile ->
  operational_verdict_witness D r L (collapse_exactness_profile profile).
Proof.
  intro H.
  destruct H as [u0 M Hr Hf | u0 k Hr Hg | y M Hy Hf | y k Hy Hg]; simpl.
  - apply (WitnessExact D r L u0 M Hr Hf).
  - apply (WitnessUnderdetermined D r L u0 k Hr Hg).
  - apply (WitnessObstructed D r L y Hy).
  - apply (WitnessObstructed D r L y Hy).
Qed.

Theorem exactness_profile_condition_collapses
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (profile : exactness_profile) :
  exactness_profile_condition D r L profile ->
  operational_verdict_condition D r L (collapse_exactness_profile profile).
Proof.
  intro Hcond.
  apply (operational_verdict_witness_iff_condition D r L
           (collapse_exactness_profile profile)).
  apply exactness_profile_witness_collapses.
  apply (exactness_profile_witness_iff_condition D r L profile).
  exact Hcond.
Qed.

Theorem classify_exactness_profile_collapse
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  collapse_exactness_profile (classify_exactness_profile D r L)
  = classify_operational_verdict D r L.
Proof.
  unfold collapse_exactness_profile, classify_exactness_profile,
    classify_operational_verdict.
  destruct (decide_lift_obstruction D r) as [Hobs | Hzero].
  - destruct (decide_descent_obstruction D L); reflexivity.
  - destruct (decide_descent_obstruction D L); reflexivity.
Qed.

(** ** Part XII: Readable four-sector partition *)

Theorem exactness_profile_four_sector_partition
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  (lift_obstruction_zero D r /\ descent_obstruction_zero D L)
  \/
  (lift_obstruction_zero D r /\ descent_obstructed D L)
  \/
  (lift_obstructed D r /\ descent_obstruction_zero D L)
  \/
  (lift_obstructed D r /\ descent_obstructed D L).
Proof.
  pose proof (classify_exactness_profile_condition D r L) as Hc.
  destruct (classify_exactness_profile D r L) eqn:Hclass; simpl in Hc.
  - left. exact Hc.
  - right. left. exact Hc.
  - right. right. left. exact Hc.
  - right. right. right. exact Hc.
Qed.

(** ** Part XIII: Concrete probes *)

(** *** 1. Realisable exact sector. *)

Example probe_profile_realisable_exact :
  classify_exactness_profile
    QImagePreimage.proj_D
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
    QImagePreimage.L_map
  = ProfileRealisableExact.
Proof.
  apply classify_exactness_profile_realisable_exact_iff.
  split.
  - exists (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc))).
    vm_compute. reflexivity.
  - apply (descent_obstruction_zero_iff_kernel_vanishing
             QImagePreimage.proj_D QImagePreimage.L_map).
    apply QImagePreimage.probe_proj_kernel_vanishing.
Qed.

(** *** 2. Realisable underdetermined sector. *)

Example probe_profile_realisable_underdetermined :
  classify_exactness_profile
    QImagePreimage.proj_D
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
    QImagePreimage.Lp_map
  = ProfileRealisableUnderdetermined.
Proof.
  apply classify_exactness_profile_realisable_underdetermined_iff.
  split.
  - exists (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc))).
    vm_compute. reflexivity.
  - apply (gauge_witness_sound QImagePreimage.proj_D QImagePreimage.Lp_map
             QImagePreimage.kernel_witness).
    split.
    + apply QImagePreimage.probe_kernel_witness_in_kernel.
    + vm_compute. discriminate.
Qed.

(** *** 3. Obstructed but descending sector: failed lifting does not
    force failed descent. *)

Example probe_profile_obstructed_but_descending :
  classify_exactness_profile
    QImagePreimage.zero_D18
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
    QImagePreimage.zero_D18
  = ProfileObstructedButDescending.
Proof.
  apply classify_exactness_profile_obstructed_but_descending_iff.
  split.
  - intros [x Hx].
    unfold QImagePreimage.zero_D18 in Hx. simpl lmap in Hx.
    rewrite (QImagePreimage.zero_mat2_apply_zero x) in Hx.
    revert Hx. vm_compute. intro Hx. discriminate Hx.
  - exists QImagePreimage.zero_D18.
    intro x.
    change
      (lmap QImagePreimage.zero_D18 x
       = lmap QImagePreimage.zero_D18 (lmap QImagePreimage.zero_D18 x)).
    assert (Hz : lmap QImagePreimage.zero_D18 x = zero_vec 2).
    { unfold QImagePreimage.zero_D18. simpl lmap.
      apply QImagePreimage.zero_mat2_apply_zero. }
    rewrite Hz.
    symmetry.
    apply lmap_preserves_zero.
Qed.

(** *** 4. Obstructed and non-descending sector: the same failed
    lifting, but with an independently non-descending claim map. *)

Example probe_profile_obstructed_and_non_descending :
  classify_exactness_profile
    QImagePreimage.zero_D18
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
    QImagePreimage.id_D18
  = ProfileObstructedAndNonDescending.
Proof.
  apply classify_exactness_profile_obstructed_and_non_descending_iff.
  split.
  - intros [x Hx].
    unfold QImagePreimage.zero_D18 in Hx. simpl lmap in Hx.
    rewrite (QImagePreimage.zero_mat2_apply_zero x) in Hx.
    revert Hx. vm_compute. intro Hx. discriminate Hx.
  - apply (gauge_witness_sound QImagePreimage.zero_D18 QImagePreimage.id_D18
             (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))).
    split.
    + unfold kernel, QImagePreimage.zero_D18. simpl lmap.
      apply QImagePreimage.zero_mat2_apply_zero.
    + vm_compute. discriminate.
Qed.

(** *** 5. Zero-dimensional complete instance: no [Fin.t 0] witness is
    fabricated. *)

Example probe_profile_dim00_exact :
  classify_exactness_profile
    QImagePreimage.dim00_D18
    (zero_vec 0)
    QImagePreimage.dim00_D18
  = ProfileRealisableExact.
Proof.
  apply classify_exactness_profile_realisable_exact_iff.
  split.
  - exists (zero_vec 0). apply vec_ext. intro i. inversion i.
  - exists QImagePreimage.dim00_D18.
    intro x. apply vec_ext. intro i. inversion i.
Qed.

(** *** 6. The two obstructed sectors collapse identically — exactly
    what the collapse discards. *)

Example probe_obstructed_profiles_collapse_identically :
  collapse_exactness_profile ProfileObstructedButDescending
  = VerdictObstructed
  /\
  collapse_exactness_profile ProfileObstructedAndNonDescending
  = VerdictObstructed.
Proof.
  split; reflexivity.
Qed.

(** *** 7. Classifier collapse agrees with the operational classifier,
    generically. *)

Example probe_classified_profile_collapses
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  collapse_exactness_profile (classify_exactness_profile D r L)
  = classify_operational_verdict D r L.
Proof.
  apply classify_exactness_profile_collapse.
Qed.

(** *** 8. Every instance has a unique witness-bearing profile. *)

Example probe_every_instance_has_unique_profile
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  exists! profile : exactness_profile,
    exactness_profile_witness D r L profile.
Proof.
  apply exactness_profile_exists_unique.
Qed.
