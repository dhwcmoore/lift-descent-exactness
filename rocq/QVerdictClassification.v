(** * Witness-bearing operational verdict classification, R6

    R4 ([QSeparatorWitness.v]) supplies separator witnesses for failed
    lifting: a linear functional annihilating [im D] but detecting a
    residue outside it. R5 ([QGaugeWitness.v]) supplies gauge witnesses
    for failed descent: a kernel direction whose claim value moves. R2
    ([QDescentFactorisation.v]) supplies a positive ambient
    factorisation witness whenever the descent obstruction vanishes.

    This unit tests the lifting axis first. Failed lifting immediately
    produces the operational verdict [VerdictObstructed] — the descent
    axis is not inspected in that branch at all, and is examined only
    once realisability has separately been established. A realisable
    instance ([r] in [im D]) with a gauge witness is
    [VerdictUnderdetermined]; a realisable instance with an ambient
    factorisation witness is [VerdictExact]. This ordering is the
    formal statement of the founding documents' operational-priority
    rule: the lifting question and the descent question are logically
    independent, but the operational tag treats the former as taking
    precedence.

    The classifier is constructive throughout: both obstruction axes
    reduce to finite rational vector tests — the lifting axis through
    the image residual ([image_residual_map], Unit 19a), and the
    descent axis through the finite family of projected kernel
    generators ([kernel_generators], Unit 20b) — decided by structural
    recursion on [Qc_eq_dec], with no nonconstructive search anywhere.

    [operational_verdict_witness] carries the mathematical evidence
    behind each tag: a separator for [VerdictObstructed], a repair
    together with a gauge direction for [VerdictUnderdetermined], and a
    repair together with an ambient factor map for [VerdictExact]. It
    is a proposition, not a certificate format or an extracted runtime
    representation, and none of the witnesses it carries — separator,
    repair, gauge direction, or factor map — is claimed unique or
    canonical, nor independent of the underlying elimination order.

    The two central theorems of this unit are [operational_verdict_
    exists_unique] (every instance has exactly one witness-bearing
    verdict — trichotomy and exclusivity together) and the three
    classifier-equality characterisations, which make the
    operational-priority rule visible in closed form: a verdict of
    [VerdictObstructed] carries no information about the descent
    status of [L] at all.

    This unit does NOT prove or construct: the full four-sector
    exactness profile (that is Unit 22, together with the theorem
    collapsing it onto this operational classification); separate
    operational verdicts for the two lifting-obstructed profile
    sectors; retention of latent descent status inside
    [VerdictObstructed]; an inadmissible verdict, or admissibility or
    provenance checking of any kind (outside the intrinsic linear
    theory entirely); a canonical or unique separator, gauge witness,
    repair, or ambient factor map; a canonical exact value or its
    invariance under witness selection; the ambiguity-space dimension
    or a basis of it; rank-nullity; quotient carrier types for either
    cokernel; the universal exact quotient; coordinate-change
    invariance; preservation or reflection properties of a
    noninvertible presentation map; realisability-obstruction-class or
    presented-claim-equivalence instantiation; certificate,
    serialisation, command-line, or executable protocol semantics;
    extraction of the witness relation into a runtime dependent
    package; or any generalisation beyond finite rational coordinate
    spaces. *)

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
From LiftDescent Require Import QKernelProjection.
From LiftDescent Require Import QKernelSpanning.
From LiftDescent Require Import QGaugeWitness.

Open Scope Qc_scope.

(** ** Local constructive decision helpers

    Both helpers repeat, at file scope, a decision-procedure shape
    already used privately inside [QGaugeWitness.v]. They are kept
    local (via [Let]) rather than imported, because the earlier
    occurrence is itself file-local and not part of that unit's public
    interface. *)

Let qvec_zero_dec {n : nat} (x : QVec n) : {x = zero_vec n} + {x <> zero_vec n}.
Proof.
  induction x as [| a n' x' IH].
  - left. apply vec_ext. intro i. inversion i.
  - destruct (Qc_eq_dec a 0) as [Ha | Ha].
    + destruct IH as [IH | IH].
      * left. apply vec_ext. intro i.
        pattern i. apply Fin.caseS'.
        -- simpl. exact Ha.
        -- intro j. simpl. rewrite zero_vec_nth, IH. apply zero_vec_nth.
      * right. intro Heq. apply IH. apply vec_ext. intro i.
        assert (Hi : Vector.nth (Vector.cons Qc a n' x') (Fin.FS i)
                     = Vector.nth (zero_vec (S n')) (Fin.FS i))
          by (rewrite Heq; reflexivity).
        simpl in Hi. exact Hi.
    + right. intro Heq. apply Ha.
      assert (Hi : Vector.nth (Vector.cons Qc a n' x') Fin.F1
                   = Vector.nth (zero_vec (S n')) Fin.F1)
        by (rewrite Heq; reflexivity).
      simpl in Hi. exact Hi.
Qed.

Let finite_vector_family_zero_dec
    {p n : nat}
    (vectors : Vector.t (QVec p) n) :
  {forall i : Fin.t n, Vector.nth vectors i = zero_vec p}
  +
  {~ forall i : Fin.t n, Vector.nth vectors i = zero_vec p}.
Proof.
  induction vectors as [| head n' tail IH].
  - left. intro i. inversion i.
  - destruct (qvec_zero_dec head) as [Hz | Hnz].
    + destruct IH as [Hall | Hnall].
      * left. intro i.
        pattern i. apply Fin.caseS'.
        -- simpl. exact Hz.
        -- intro j. simpl. apply Hall.
      * right. intro Hcontra. apply Hnall. intro i.
        pose proof (Hcontra (Fin.FS i)) as Hi. simpl in Hi. exact Hi.
    + right. intro Hcontra.
      pose proof (Hcontra Fin.F1) as Hi. simpl in Hi. contradiction.
Qed.

(** ** Part I: The operational verdict type *)

Inductive operational_verdict : Type :=
| VerdictObstructed
| VerdictUnderdetermined
| VerdictExact.

(** ** Part II: The witness-bearing verdict relation *)

Inductive operational_verdict_witness
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    : operational_verdict -> Prop :=

| WitnessObstructed :
    forall y : QLinearFunctional v,
      separator_witness D r y ->
      operational_verdict_witness D r L VerdictObstructed

| WitnessUnderdetermined :
    forall u0 k : QVec u,
      repair_fibre D r u0 ->
      gauge_witness D L k ->
      operational_verdict_witness D r L VerdictUnderdetermined

| WitnessExact :
    forall (u0 : QVec u) (M : QLinearMap v w),
      repair_fibre D r u0 ->
      same_lmap L (precompose D M) ->
      operational_verdict_witness D r L VerdictExact.

(** ** Part III: Semantic verdict condition *)

Definition operational_verdict_condition
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (verdict : operational_verdict)
    : Prop :=
  match verdict with
  | VerdictObstructed =>
      lift_obstructed D r
  | VerdictUnderdetermined =>
      lift_obstruction_zero D r /\ descent_obstructed D L
  | VerdictExact =>
      lift_obstruction_zero D r /\ descent_obstruction_zero D L
  end.

(** ** Part IV: Lifting-axis decision *)

Definition decide_lift_obstruction
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v) :
  {lift_obstructed D r} + {lift_obstruction_zero D r}.
Proof.
  destruct (qvec_zero_dec (lmap (image_residual_map D) r)) as [Heq | Hne].
  - right.
    unfold lift_obstruction_zero.
    apply (image_residual_zero_iff_image D r).
    exact Heq.
  - left.
    unfold lift_obstructed, lift_obstruction_zero.
    intro Hmem.
    apply Hne.
    apply (image_residual_on_image D r Hmem).
Defined.

(** ** Part V: Descent-axis decision *)

Definition decide_descent_obstruction
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  {descent_obstructed D L} + {descent_obstruction_zero D L}.
Proof.
  destruct (finite_vector_family_zero_dec (gauge_generator_images D L))
    as [Hall | Hnall].
  - right.
    apply (descent_obstruction_zero_iff_kernel_vanishing D L).
    unfold QImagePreimage.vanishes_on_kernel.
    apply (kernel_zero_iff_kernel_generators_zero D L).
    intro i.
    rewrite <- (gauge_generator_images_nth D L i).
    apply Hall.
  - left.
    apply (descent_obstructed_iff_not_kernel_vanishing D L).
    intro Hvan.
    apply Hnall.
    intro i.
    rewrite (gauge_generator_images_nth D L i).
    apply Hvan.
    apply kernel_generator_in_kernel.
Defined.

(** ** Part VI: The operational classifier *)

Definition classify_operational_verdict
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    : operational_verdict :=
  match decide_lift_obstruction D r with
  | left _ => VerdictObstructed
  | right _ =>
      match decide_descent_obstruction D L with
      | left _ => VerdictUnderdetermined
      | right _ => VerdictExact
      end
  end.

(** ** Part VII: Witness and semantic-condition equivalence *)

Theorem operational_verdict_witness_iff_condition
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (verdict : operational_verdict) :
  operational_verdict_witness D r L verdict
  <->
  operational_verdict_condition D r L verdict.
Proof.
  destruct verdict; simpl.
  - split.
    + intro H.
      inversion H as [y Hy | | ].
      apply (separator_witness_sound D r y Hy).
    + intro H.
      destruct (separator_witness_complete D r H) as [y Hy].
      apply (WitnessObstructed D r L y Hy).
  - split.
    + intro H.
      inversion H as [ | u0 k Hr Hg | ].
      split.
      * exists u0. exact Hr.
      * apply (gauge_witness_sound D L k Hg).
    + intros [Hlz Hdo].
      destruct Hlz as [u0 Hu0].
      destruct (gauge_witness_complete D L Hdo) as [k Hk].
      apply (WitnessUnderdetermined D r L u0 k Hu0 Hk).
  - split.
    + intro H.
      inversion H as [ | | u0 M Hr Hf].
      split.
      * exists u0. exact Hr.
      * exists M. exact Hf.
    + intros [Hlz Hdz].
      destruct Hlz as [u0 Hu0].
      destruct Hdz as [M Hf].
      apply (WitnessExact D r L u0 M Hu0 Hf).
Qed.

(** ** Part VIII: Classifier witness and semantic theorems *)

Theorem classify_operational_verdict_witness
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  operational_verdict_witness D r L (classify_operational_verdict D r L).
Proof.
  unfold classify_operational_verdict.
  destruct (decide_lift_obstruction D r) as [Hobs | Hzero].
  - apply (operational_verdict_witness_iff_condition D r L VerdictObstructed).
    simpl. exact Hobs.
  - destruct (decide_descent_obstruction D L) as [Hdobs | Hdzero].
    + apply (operational_verdict_witness_iff_condition D r L VerdictUnderdetermined).
      simpl. split; assumption.
    + apply (operational_verdict_witness_iff_condition D r L VerdictExact).
      simpl. split; assumption.
Qed.

Theorem classify_operational_verdict_condition
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  operational_verdict_condition D r L (classify_operational_verdict D r L).
Proof.
  apply (operational_verdict_witness_iff_condition D r L
           (classify_operational_verdict D r L)).
  apply classify_operational_verdict_witness.
Qed.

(** ** Part IX: Uniqueness *)

Theorem operational_verdict_condition_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (verdict1 verdict2 : operational_verdict) :
  operational_verdict_condition D r L verdict1 ->
  operational_verdict_condition D r L verdict2 ->
  verdict1 = verdict2.
Proof.
  destruct verdict1, verdict2; simpl; intros H1 H2; try reflexivity.
  - exfalso. apply H1. destruct H2 as [Hz _]. exact Hz.
  - exfalso. apply H1. destruct H2 as [Hz _]. exact Hz.
  - exfalso. apply H2. destruct H1 as [Hz _]. exact Hz.
  - exfalso. destruct H1 as [_ Hd]. destruct H2 as [_ Hz]. apply Hd. exact Hz.
  - exfalso. apply H2. destruct H1 as [Hz _]. exact Hz.
  - exfalso. destruct H1 as [_ Hz]. destruct H2 as [_ Hd]. apply Hd. exact Hz.
Qed.

Theorem operational_verdict_witness_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (verdict1 verdict2 : operational_verdict) :
  operational_verdict_witness D r L verdict1 ->
  operational_verdict_witness D r L verdict2 ->
  verdict1 = verdict2.
Proof.
  intros H1 H2.
  apply (operational_verdict_condition_unique D r L verdict1 verdict2).
  - apply (operational_verdict_witness_iff_condition D r L verdict1). exact H1.
  - apply (operational_verdict_witness_iff_condition D r L verdict2). exact H2.
Qed.

(** ** Part X: The central R6 theorem *)

Theorem operational_verdict_exists_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  exists! verdict : operational_verdict,
    operational_verdict_witness D r L verdict.
Proof.
  exists (classify_operational_verdict D r L).
  split.
  - apply classify_operational_verdict_witness.
  - intro verdict'. intro Hv'.
    apply (operational_verdict_witness_unique D r L
             (classify_operational_verdict D r L) verdict').
    + apply classify_operational_verdict_witness.
    + exact Hv'.
Qed.

(** ** Part XI: Classifier characterisations *)

Theorem classify_operational_verdict_obstructed_iff
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_operational_verdict D r L = VerdictObstructed
  <->
  lift_obstructed D r.
Proof.
  split.
  - intro Heq.
    pose proof (classify_operational_verdict_condition D r L) as Hc.
    rewrite Heq in Hc.
    simpl in Hc.
    exact Hc.
  - intro Hobs.
    apply (operational_verdict_condition_unique D r L
             (classify_operational_verdict D r L) VerdictObstructed).
    + apply classify_operational_verdict_condition.
    + simpl. exact Hobs.
Qed.

Theorem classify_operational_verdict_underdetermined_iff
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_operational_verdict D r L = VerdictUnderdetermined
  <->
  lift_obstruction_zero D r /\ descent_obstructed D L.
Proof.
  split.
  - intro Heq.
    pose proof (classify_operational_verdict_condition D r L) as Hc.
    rewrite Heq in Hc.
    simpl in Hc.
    exact Hc.
  - intro Hcond.
    apply (operational_verdict_condition_unique D r L
             (classify_operational_verdict D r L) VerdictUnderdetermined).
    + apply classify_operational_verdict_condition.
    + simpl. exact Hcond.
Qed.

Theorem classify_operational_verdict_exact_iff
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_operational_verdict D r L = VerdictExact
  <->
  lift_obstruction_zero D r /\ descent_obstruction_zero D L.
Proof.
  split.
  - intro Heq.
    pose proof (classify_operational_verdict_condition D r L) as Hc.
    rewrite Heq in Hc.
    simpl in Hc.
    exact Hc.
  - intro Hcond.
    apply (operational_verdict_condition_unique D r L
             (classify_operational_verdict D r L) VerdictExact).
    + apply classify_operational_verdict_condition.
    + simpl. exact Hcond.
Qed.

(** ** Part XII: Readable semantic trichotomy *)

Theorem operational_three_way_trichotomy
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  lift_obstructed D r
  \/
  (lift_obstruction_zero D r /\ descent_obstructed D L)
  \/
  (lift_obstruction_zero D r /\ descent_obstruction_zero D L).
Proof.
  pose proof (classify_operational_verdict_condition D r L) as Hc.
  destruct (classify_operational_verdict D r L) eqn:Hclass; simpl in Hc.
  - left. exact Hc.
  - right. left. exact Hc.
  - right. right. exact Hc.
Qed.

(** ** Part XIII: Concrete probes *)

(** *** 1. Zero map, zero claim: obstructed lifting, with descent
    latently zero. *)

Example probe_zero_map_zero_claim_obstructed :
  classify_operational_verdict
    QImagePreimage.zero_D18
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
    QImagePreimage.zero_D18
  = VerdictObstructed.
Proof.
  apply classify_operational_verdict_obstructed_iff.
  intros [x Hx].
  unfold QImagePreimage.zero_D18 in Hx. simpl lmap in Hx.
  rewrite (QImagePreimage.zero_mat2_apply_zero x) in Hx.
  revert Hx. vm_compute. intro Hx. discriminate Hx.
Qed.

(** *** 2. Zero map, identity claim: obstructed lifting, with descent
    latently obstructed. Together with Probe 1, this confirms the
    operational classifier collapses both lifting-obstructed sectors
    to the same tag. *)

Example probe_zero_map_identity_claim_obstructed :
  classify_operational_verdict
    QImagePreimage.zero_D18
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
    QImagePreimage.id_D18
  = VerdictObstructed.
Proof.
  apply classify_operational_verdict_obstructed_iff.
  intros [x Hx].
  unfold QImagePreimage.zero_D18 in Hx. simpl lmap in Hx.
  rewrite (QImagePreimage.zero_mat2_apply_zero x) in Hx.
  revert Hx. vm_compute. intro Hx. discriminate Hx.
Qed.

(** *** 3. Proper projection, ambiguous claim: realisable, gauge
    witness present. *)

Example probe_proper_projection_underdetermined :
  classify_operational_verdict
    QImagePreimage.proj_D
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
    QImagePreimage.Lp_map
  = VerdictUnderdetermined.
Proof.
  apply classify_operational_verdict_underdetermined_iff.
  split.
  - exists (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc))).
    vm_compute. reflexivity.
  - apply (gauge_witness_sound QImagePreimage.proj_D QImagePreimage.Lp_map
             QImagePreimage.kernel_witness).
    split.
    + apply QImagePreimage.probe_kernel_witness_in_kernel.
    + vm_compute. discriminate.
Qed.

(** *** 4. Proper projection, exact claim: realisable, descent
    vanishes. *)

Example probe_proper_projection_exact :
  classify_operational_verdict
    QImagePreimage.proj_D
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)))
    QImagePreimage.L_map
  = VerdictExact.
Proof.
  apply classify_operational_verdict_exact_iff.
  split.
  - exists (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc))).
    vm_compute. reflexivity.
  - apply (descent_obstruction_zero_iff_kernel_vanishing
             QImagePreimage.proj_D QImagePreimage.L_map).
    apply QImagePreimage.probe_proj_kernel_vanishing.
Qed.

(** *** 5. Identity observation: always exact, since the identity
    map's kernel is trivial. *)

Example probe_identity_observation_exact :
  classify_operational_verdict
    QImagePreimage.id_D18
    (Vector.cons Qc 1 1 (Vector.cons Qc 1 0 (Vector.nil Qc)))
    QImagePreimage.Lp_map
  = VerdictExact.
Proof.
  apply classify_operational_verdict_exact_iff.
  split.
  - exists (Vector.cons Qc 1 1 (Vector.cons Qc 1 0 (Vector.nil Qc))).
    vm_compute. reflexivity.
  - apply (descent_obstruction_zero_iff_kernel_vanishing
             QImagePreimage.id_D18 QImagePreimage.Lp_map).
    intros k Hk.
    assert (Hzero : k = zero_vec 2).
    { rewrite <- (kernel_projection_fixes_kernel QImagePreimage.id_D18 k Hk).
      apply probe_identity_projection_is_zero. }
    rewrite Hzero.
    apply lmap_preserves_zero.
Qed.

(** *** 6. Zero-dimensional complete instance: no [Fin.t 0] witness is
    fabricated. *)

Example probe_dim00_exact :
  classify_operational_verdict
    QImagePreimage.dim00_D18
    (zero_vec 0)
    QImagePreimage.dim00_D18
  = VerdictExact.
Proof.
  apply classify_operational_verdict_exact_iff.
  split.
  - exists (zero_vec 0). apply vec_ext. intro i. inversion i.
  - apply (descent_obstruction_zero_iff_kernel_vanishing
             QImagePreimage.dim00_D18 QImagePreimage.dim00_D18).
    intros k Hk.
    apply vec_ext. intro i. inversion i.
Qed.

(** *** 7. Every instance has a unique witness-bearing verdict. *)

Example probe_every_instance_has_unique_witnessed_verdict
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  exists! verdict : operational_verdict,
    operational_verdict_witness D r L verdict.
Proof.
  apply operational_verdict_exists_unique.
Qed.
