(** * Combining lifting and descent transport into isomorphic invariance, R9

    Units 26a and 26b separately proved invariance of the lifting and
    descent obstruction statuses, with explicit witness transports on
    each axis:

    [[
      u0 |-> a(u0),   y |-> y after b^{-1},
      M  |-> c after M after b^{-1},   k |-> a(k).
    ]]

    Unit 27 combines those two halves rather than reproving either
    axis: it transports the four-sector exactness profile and its
    witness packages, the three-way operational verdict and its
    witness packages, and the unique exact value in the realisable
    exact sector, all by dispatching to the already-closed lifting and
    descent equivalences. No new obstruction-space isomorphism, no new
    classifier, and no new witness or canonical-value type is
    introduced here — [lifting_obstruction_space_isomorphism] and
    [kernel_space_isomorphism] remain the structural basis, unchanged.

    Every witness-package transport constructs its target evidence
    from the *supplied* source evidence via the explicit maps above —
    a transported repair, separator, factor map, or gauge direction —
    never by re-running separator or gauge completeness, and never by
    asking a classifier to manufacture replacement evidence. Two
    distinct presentations of the same profile sector may therefore
    carry witnesses that are individually different mathematical
    objects; only the profile and verdict *tags* are proved equal, by
    [exactness_profile_condition_unique]/[operational_verdict_
    condition_unique] applied to the transported semantic condition,
    never by comparing the internal computations of
    [decide_lift_obstruction]/[decide_descent_obstruction] across the
    two coordinate systems.

    The canonical-value API is deliberately relational
    ([exists! x, exact_value D r L x]), not a selected function, so
    this unit likewise defines only the direct coordinate maps [x |->
    c(x)] and [x' |-> c^{-1}(x')] on already-produced values, and
    proves the target's unique exact value is the forward image of the
    source's — it does not, and structurally cannot, extract a
    canonical value from an arbitrary proposition.

    Completing this unit, together with Units 26a and 26b, closes R9.
    It requires [PresentationIsomorphism] throughout; the weaker
    one-directional preservation and reflection theorems for a general
    (possibly noninvertible) presentation morphism are Units 28 and
    29, not this unit. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QImagePreimage.
From LiftDescent Require Import QDescentFactorisation.
From LiftDescent Require Import QLinearFunctional.
From LiftDescent Require Import QSeparatorWitness.
From LiftDescent Require Import QGaugeWitness.
From LiftDescent Require Import QVerdictClassification.
From LiftDescent Require Import QExactnessProfile.
From LiftDescent Require Import QCanonicalValue.
From LiftDescent Require Import QLinearIsomorphism.
From LiftDescent Require Import QPresentationMorphism.
From LiftDescent Require Import QLiftObstructionTransport.
From LiftDescent Require Import QDescentObstructionTransport.

Open Scope Qc_scope.

(** ** Part I: Exactness-profile condition transport *)

Theorem exactness_profile_condition_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (profile : exactness_profile) :
  exactness_profile_condition (inst_D I) r (inst_L I) profile ->
  exactness_profile_condition (inst_D I') r' (inst_L I') profile.
Proof.
  destruct profile; simpl; intros [H1 H2].
  - split.
    + apply (presentation_isomorphism_lift_obstruction_zero_iff P). exact H1.
    + apply (presentation_isomorphism_descent_obstruction_zero_iff P). exact H2.
  - split.
    + apply (presentation_isomorphism_lift_obstruction_zero_iff P). exact H1.
    + apply (presentation_isomorphism_descent_obstructed_iff P). exact H2.
  - split.
    + apply (presentation_isomorphism_lift_obstructed_iff P). exact H1.
    + apply (presentation_isomorphism_descent_obstruction_zero_iff P). exact H2.
  - split.
    + apply (presentation_isomorphism_lift_obstructed_iff P). exact H1.
    + apply (presentation_isomorphism_descent_obstructed_iff P). exact H2.
Qed.

Theorem exactness_profile_condition_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (profile : exactness_profile) :
  exactness_profile_condition (inst_D I') r' (inst_L I') profile ->
  exactness_profile_condition (inst_D I) r (inst_L I) profile.
Proof.
  exact (exactness_profile_condition_transport_forward
           (inverse_presentation_isomorphism P) profile).
Qed.

Theorem presentation_isomorphism_exactness_profile_condition_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (profile : exactness_profile) :
  exactness_profile_condition (inst_D I) r (inst_L I) profile
  <->
  exactness_profile_condition (inst_D I') r' (inst_L I') profile.
Proof.
  split.
  - apply (exactness_profile_condition_transport_forward P profile).
  - apply (exactness_profile_condition_transport_backward P profile).
Qed.

(** ** Part II: Exact transport of profile witness packages *)

Theorem exactness_profile_witness_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (profile : exactness_profile) :
  exactness_profile_witness (inst_D I) r (inst_L I) profile ->
  exactness_profile_witness (inst_D I') r' (inst_L I') profile.
Proof.
  intro H.
  destruct H as [u0 M Hr HM | u0 k Hr Hk | y M Hy HM | y k Hy Hk].
  - exact (WitnessProfileRealisableExact (inst_D I') r' (inst_L I')
             (lmap (iso_forward (pi_state P)) u0)
             (factor_map_transport_forward P M)
             (presentation_morphism_repair_transport
                (presentation_isomorphism_forward_morphism P) u0 Hr)
             (factor_map_transport_forward_factorises P M HM)).
  - exact (WitnessProfileRealisableUnderdetermined (inst_D I') r' (inst_L I')
             (lmap (iso_forward (pi_state P)) u0)
             (gauge_transport_forward P k)
             (presentation_morphism_repair_transport
                (presentation_isomorphism_forward_morphism P) u0 Hr)
             (gauge_transport_forward_witness P k Hk)).
  - exact (WitnessProfileObstructedButDescending (inst_D I') r' (inst_L I')
             (separator_transport_forward P y)
             (factor_map_transport_forward P M)
             (separator_transport_forward_witness P y Hy)
             (factor_map_transport_forward_factorises P M HM)).
  - exact (WitnessProfileObstructedAndNonDescending (inst_D I') r' (inst_L I')
             (separator_transport_forward P y)
             (gauge_transport_forward P k)
             (separator_transport_forward_witness P y Hy)
             (gauge_transport_forward_witness P k Hk)).
Qed.

Theorem exactness_profile_witness_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (profile : exactness_profile) :
  exactness_profile_witness (inst_D I') r' (inst_L I') profile ->
  exactness_profile_witness (inst_D I) r (inst_L I) profile.
Proof.
  exact (exactness_profile_witness_transport_forward
           (inverse_presentation_isomorphism P) profile).
Qed.

Theorem presentation_isomorphism_exactness_profile_witness_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (profile : exactness_profile) :
  exactness_profile_witness (inst_D I) r (inst_L I) profile
  <->
  exactness_profile_witness (inst_D I') r' (inst_L I') profile.
Proof.
  split.
  - apply (exactness_profile_witness_transport_forward P profile).
  - apply (exactness_profile_witness_transport_backward P profile).
Qed.

(** ** Part III: Full-profile classifier invariance *)

Theorem classify_exactness_profile_invariant
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  classify_exactness_profile (inst_D I) r (inst_L I)
  =
  classify_exactness_profile (inst_D I') r' (inst_L I').
Proof.
  pose proof (classify_exactness_profile_condition (inst_D I) r (inst_L I)) as Hc.
  pose proof (exactness_profile_condition_transport_forward P
                (classify_exactness_profile (inst_D I) r (inst_L I)) Hc) as Hc'.
  pose proof (classify_exactness_profile_condition (inst_D I') r' (inst_L I')) as Hc2.
  exact (exactness_profile_condition_unique (inst_D I') r' (inst_L I')
           (classify_exactness_profile (inst_D I) r (inst_L I))
           (classify_exactness_profile (inst_D I') r' (inst_L I'))
           Hc' Hc2).
Qed.

(** ** Part IV: Operational-verdict condition transport *)

Theorem operational_verdict_condition_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (verdict : operational_verdict) :
  operational_verdict_condition (inst_D I) r (inst_L I) verdict ->
  operational_verdict_condition (inst_D I') r' (inst_L I') verdict.
Proof.
  destruct verdict; simpl.
  - intro H1.
    apply (presentation_isomorphism_lift_obstructed_iff P).
    exact H1.
  - intros [H1 H2].
    split.
    + apply (presentation_isomorphism_lift_obstruction_zero_iff P). exact H1.
    + apply (presentation_isomorphism_descent_obstructed_iff P). exact H2.
  - intros [H1 H2].
    split.
    + apply (presentation_isomorphism_lift_obstruction_zero_iff P). exact H1.
    + apply (presentation_isomorphism_descent_obstruction_zero_iff P). exact H2.
Qed.

Theorem operational_verdict_condition_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (verdict : operational_verdict) :
  operational_verdict_condition (inst_D I') r' (inst_L I') verdict ->
  operational_verdict_condition (inst_D I) r (inst_L I) verdict.
Proof.
  exact (operational_verdict_condition_transport_forward
           (inverse_presentation_isomorphism P) verdict).
Qed.

Theorem presentation_isomorphism_operational_verdict_condition_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (verdict : operational_verdict) :
  operational_verdict_condition (inst_D I) r (inst_L I) verdict
  <->
  operational_verdict_condition (inst_D I') r' (inst_L I') verdict.
Proof.
  split.
  - apply (operational_verdict_condition_transport_forward P verdict).
  - apply (operational_verdict_condition_transport_backward P verdict).
Qed.

(** ** Part V: Exact transport of operational witness packages *)

Theorem operational_verdict_witness_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (verdict : operational_verdict) :
  operational_verdict_witness (inst_D I) r (inst_L I) verdict ->
  operational_verdict_witness (inst_D I') r' (inst_L I') verdict.
Proof.
  intro H.
  destruct H as [y Hy | u0 k Hr Hk | u0 M Hr HM].
  - exact (WitnessObstructed (inst_D I') r' (inst_L I')
             (separator_transport_forward P y)
             (separator_transport_forward_witness P y Hy)).
  - exact (WitnessUnderdetermined (inst_D I') r' (inst_L I')
             (lmap (iso_forward (pi_state P)) u0)
             (gauge_transport_forward P k)
             (presentation_morphism_repair_transport
                (presentation_isomorphism_forward_morphism P) u0 Hr)
             (gauge_transport_forward_witness P k Hk)).
  - exact (WitnessExact (inst_D I') r' (inst_L I')
             (lmap (iso_forward (pi_state P)) u0)
             (factor_map_transport_forward P M)
             (presentation_morphism_repair_transport
                (presentation_isomorphism_forward_morphism P) u0 Hr)
             (factor_map_transport_forward_factorises P M HM)).
Qed.

Theorem operational_verdict_witness_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (verdict : operational_verdict) :
  operational_verdict_witness (inst_D I') r' (inst_L I') verdict ->
  operational_verdict_witness (inst_D I) r (inst_L I) verdict.
Proof.
  exact (operational_verdict_witness_transport_forward
           (inverse_presentation_isomorphism P) verdict).
Qed.

Theorem presentation_isomorphism_operational_verdict_witness_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (verdict : operational_verdict) :
  operational_verdict_witness (inst_D I) r (inst_L I) verdict
  <->
  operational_verdict_witness (inst_D I') r' (inst_L I') verdict.
Proof.
  split.
  - apply (operational_verdict_witness_transport_forward P verdict).
  - apply (operational_verdict_witness_transport_backward P verdict).
Qed.

(** ** Part VI: Operational-classifier invariance *)

Theorem classify_operational_verdict_invariant
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  classify_operational_verdict (inst_D I) r (inst_L I)
  =
  classify_operational_verdict (inst_D I') r' (inst_L I').
Proof.
  rewrite <- (classify_exactness_profile_collapse (inst_D I) r (inst_L I)).
  rewrite <- (classify_exactness_profile_collapse (inst_D I') r' (inst_L I')).
  f_equal.
  apply (classify_exactness_profile_invariant P).
Qed.

(** ** Part VII: Exact-value transport *)

Definition exact_value_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (x : QVec nW)
    : QVec nW' :=
  lmap (iso_forward (pi_claim P)) x.

Definition exact_value_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (x' : QVec nW')
    : QVec nW :=
  lmap (iso_backward (pi_claim P)) x'.

Theorem exact_value_transport_left_inverse
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (x : QVec nW) :
  exact_value_transport_backward P (exact_value_transport_forward P x) = x.
Proof.
  apply (iso_left_inverse (pi_claim P) x).
Qed.

Theorem exact_value_transport_right_inverse
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (x' : QVec nW') :
  exact_value_transport_forward P (exact_value_transport_backward P x') = x'.
Proof.
  apply (iso_right_inverse (pi_claim P) x').
Qed.

Theorem exact_value_transport_forward_is_exact
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (x : QVec nW) :
  exact_value (inst_D I) r (inst_L I) x ->
  exact_value (inst_D I') r' (inst_L I') (exact_value_transport_forward P x).
Proof.
  intros Hexact repair' Hrepair'.
  change (lmap (inst_L I') repair' = lmap (iso_forward (pi_claim P)) x).
  pose proof (presentation_morphism_repair_transport
                (presentation_isomorphism_reverse_morphism P) repair' Hrepair'
    : repair_fibre (inst_D I) r (lmap (iso_backward (pi_state P)) repair')) as Hrep.
  pose proof (Hexact (lmap (iso_backward (pi_state P)) repair') Hrep) as Hval.
  pose proof (pi_L_square P (lmap (iso_backward (pi_state P)) repair')
    : lmap (iso_forward (pi_claim P))
        (lmap (inst_L I) (lmap (iso_backward (pi_state P)) repair'))
      = lmap (inst_L I')
          (lmap (iso_forward (pi_state P))
            (lmap (iso_backward (pi_state P)) repair'))) as Hsq.
  rewrite Hval in Hsq.
  rewrite (iso_right_inverse (pi_state P) repair') in Hsq.
  symmetry.
  exact Hsq.
Qed.

Theorem exact_value_transport_backward_is_exact
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (x' : QVec nW') :
  exact_value (inst_D I') r' (inst_L I') x' ->
  exact_value (inst_D I) r (inst_L I) (exact_value_transport_backward P x').
Proof.
  exact (exact_value_transport_forward_is_exact
           (inverse_presentation_isomorphism P) x').
Qed.

Theorem presentation_isomorphism_exact_value_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (x : QVec nW) :
  exact_value (inst_D I) r (inst_L I) x
  <->
  exact_value (inst_D I') r' (inst_L I') (exact_value_transport_forward P x).
Proof.
  split.
  - apply (exact_value_transport_forward_is_exact P x).
  - intro Hx'.
    pose proof (exact_value_transport_backward_is_exact P
                  (exact_value_transport_forward P x) Hx') as Hb.
    rewrite (exact_value_transport_left_inverse P x) in Hb.
    exact Hb.
Qed.

(** ** Part VIII: Canonical exact-value correspondence *)

Theorem presentation_isomorphism_canonical_exact_value_transport
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  lift_obstruction_zero (inst_D I) r ->
  descent_obstruction_zero (inst_D I) (inst_L I) ->
  exists x : QVec nW,
    exact_value (inst_D I) r (inst_L I) x
    /\
    exact_value (inst_D I') r' (inst_L I') (exact_value_transport_forward P x)
    /\
    (forall y : QVec nW,
      exact_value (inst_D I) r (inst_L I) y -> y = x)
    /\
    (forall y' : QVec nW',
      exact_value (inst_D I') r' (inst_L I') y' ->
      y' = exact_value_transport_forward P x).
Proof.
  intros Hlift Hdescent.
  destruct (canonical_exact_value_exists_unique (inst_D I) r (inst_L I) Hlift Hdescent)
    as [x [Hx Hxuniq]].
  exists x.
  split.
  - exact Hx.
  - split.
    + exact (exact_value_transport_forward_is_exact P x Hx).
    + split.
      * intros y Hy. symmetry. exact (Hxuniq y Hy).
      * intros y' Hy'.
        destruct Hlift as [u0 Hu0].
        pose proof (presentation_morphism_repair_transport
                       (presentation_isomorphism_forward_morphism P) u0 Hu0
          : repair_fibre (inst_D I') r' (lmap (iso_forward (pi_state P)) u0)) as Hmem'.
        exact (exact_value_unique_on_nonempty_fibre (inst_D I') r' (inst_L I')
                 (lmap (iso_forward (pi_state P)) u0) Hmem'
                 y' (exact_value_transport_forward P x) Hy'
                 (exact_value_transport_forward_is_exact P x Hx)).
Qed.

(** ** Part IX: Concrete probes *)

Example exact_value_transport_forward_application_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (x : QVec nW) :
  exact_value_transport_forward P x
  =
  lmap (iso_forward (pi_claim P)) x.
Proof.
  reflexivity.
Qed.

Example exactness_profile_witness_transport_forward_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (profile : exactness_profile)
    (H : exactness_profile_witness (inst_D I) r (inst_L I) profile) :
  exactness_profile_witness (inst_D I') r' (inst_L I') profile.
Proof.
  apply (exactness_profile_witness_transport_forward P profile).
  exact H.
Qed.

Example classify_exactness_profile_invariant_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  classify_exactness_profile (inst_D I) r (inst_L I)
  =
  classify_exactness_profile (inst_D I') r' (inst_L I').
Proof.
  apply (classify_exactness_profile_invariant P).
Qed.

Example classify_operational_verdict_invariant_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  classify_operational_verdict (inst_D I) r (inst_L I)
  =
  classify_operational_verdict (inst_D I') r' (inst_L I').
Proof.
  apply (classify_operational_verdict_invariant P).
Qed.
