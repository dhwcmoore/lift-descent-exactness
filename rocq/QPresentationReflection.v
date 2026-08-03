(** * Presentation Reflection

    Unit 28 proved the preservation half of R10 under
    [presentation_kernel_coverage]. This file proves the complementary
    reflection half for a general, possibly noninvertible
    [P : PresentationMorphism I r I' r'], using two independent
    conditions that do not mention kernel coverage at all:

    - [presentation_reconciliation_reflection] — target realisability at
      the distinguished residue [r'] implies source realisability at
      [r]. This is an instance-specific obligation about the residue
      alone, not a claim that [b] reflects zero on every vector of [V].

    - [presentation_claim_zero_reflection] — the claim map [c] reflects
      zero on all of [W]. This is a clean, compositional, map-level
      sufficient condition for the instance-specific descent-reflection
      implication [L'(ker D') = 0 -> L(ker D) = 0]; it is not asserted to
      be the weakest hypothesis under which that fixed-instance
      implication holds.

    Evidence transports asymmetrically. A source gauge witness
    transports explicitly along [pm_state], because its nonzero claim
    value survives claim-zero reflection pointwise. A source separator
    or a target factor map generally has no direct formula in terms of
    the morphism's components, so this file proves only existence of a
    replacement witness, regenerated through the existing completeness
    and factorisation theorems — never through an inverse of [b] or
    [c], neither of which is assumed to exist. *)

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
From LiftDescent Require Import QPresentationPreservation.

Open Scope Qc_scope.

(** ** Part I: Reconciliation reflection *)

Definition presentation_reconciliation_reflection
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    : Prop :=
  lift_obstruction_zero (inst_D I') r' ->
  lift_obstruction_zero (inst_D I) r.

Theorem identity_presentation_morphism_reconciliation_reflection
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV) :
  presentation_reconciliation_reflection (identity_presentation_morphism I r).
Proof.
  intro H. exact H.
Qed.

Theorem compose_presentation_morphism_reconciliation_reflection
    {nU0 nV0 nW0 nU1 nV1 nW1 nU2 nV2 nW2 : nat}
    {I0 : LinearInstance nU0 nV0 nW0}
    {r0 : QVec nV0}
    {I1 : LinearInstance nU1 nV1 nW1}
    {r1 : QVec nV1}
    {I2 : LinearInstance nU2 nV2 nW2}
    {r2 : QVec nV2}
    (P : PresentationMorphism I0 r0 I1 r1)
    (Q : PresentationMorphism I1 r1 I2 r2) :
  presentation_reconciliation_reflection P ->
  presentation_reconciliation_reflection Q ->
  presentation_reconciliation_reflection (compose_presentation_morphism P Q).
Proof.
  intros HP HQ Hz2.
  apply HP.
  apply HQ.
  exact Hz2.
Qed.

Theorem presentation_isomorphism_reconciliation_reflection
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  presentation_reconciliation_reflection (presentation_isomorphism_forward_morphism P).
Proof.
  intro Hz'.
  exact (presentation_morphism_lift_obstruction_zero_preserved
           (presentation_isomorphism_reverse_morphism P) Hz').
Qed.

(** ** Part II: Claim-zero reflection *)

Definition presentation_claim_zero_reflection
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    : Prop :=
  forall w : QVec nW,
    lmap (pm_claim P) w = zero_vec nW' ->
    w = zero_vec nW.

Theorem identity_presentation_morphism_claim_zero_reflection
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV) :
  presentation_claim_zero_reflection (identity_presentation_morphism I r).
Proof.
  intros w Hw. exact Hw.
Qed.

Theorem compose_presentation_morphism_claim_zero_reflection
    {nU0 nV0 nW0 nU1 nV1 nW1 nU2 nV2 nW2 : nat}
    {I0 : LinearInstance nU0 nV0 nW0}
    {r0 : QVec nV0}
    {I1 : LinearInstance nU1 nV1 nW1}
    {r1 : QVec nV1}
    {I2 : LinearInstance nU2 nV2 nW2}
    {r2 : QVec nV2}
    (P : PresentationMorphism I0 r0 I1 r1)
    (Q : PresentationMorphism I1 r1 I2 r2) :
  presentation_claim_zero_reflection P ->
  presentation_claim_zero_reflection Q ->
  presentation_claim_zero_reflection (compose_presentation_morphism P Q).
Proof.
  intros HP HQ w Hw.
  change (lmap (pm_claim Q) (lmap (pm_claim P) w) = zero_vec nW2) in Hw.
  apply HP.
  apply HQ.
  exact Hw.
Qed.

Theorem presentation_isomorphism_claim_zero_reflection
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  presentation_claim_zero_reflection (presentation_isomorphism_forward_morphism P).
Proof.
  intros w Hw.
  apply (linear_isomorphism_forward_zero_iff (pi_claim P) w).
  exact Hw.
Qed.

(** ** Part III: Lifting reflection and obstruction preservation *)

Theorem presentation_morphism_lift_obstruction_zero_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  lift_obstruction_zero (inst_D I') r' ->
  lift_obstruction_zero (inst_D I) r.
Proof.
  intro H. exact H.
Qed.

Theorem presentation_morphism_lift_obstructed_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  lift_obstructed (inst_D I) r ->
  lift_obstructed (inst_D I') r'.
Proof.
  unfold lift_obstructed.
  intros Hrecon Hobs Hzero'.
  apply Hobs.
  apply Hrecon.
  exact Hzero'.
Qed.

Theorem presentation_morphism_separator_witness_preserved_exists
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (y : QLinearFunctional nV) :
  presentation_reconciliation_reflection P ->
  separator_witness (inst_D I) r y ->
  exists y' : QLinearFunctional nV',
    separator_witness (inst_D I') r' y'.
Proof.
  intros Hrecon Hy.
  apply separator_witness_complete.
  apply (presentation_morphism_lift_obstructed_preserved P Hrecon).
  apply (separator_witness_sound (inst_D I) r y).
  exact Hy.
Qed.

(** ** Part IV: Descent reflection and obstruction preservation *)

Theorem presentation_morphism_claim_nonzero_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (w : QVec nW) :
  presentation_claim_zero_reflection P ->
  w <> zero_vec nW ->
  lmap (pm_claim P) w <> zero_vec nW'.
Proof.
  intros Hrefl Hne Heq.
  apply Hne.
  apply Hrefl.
  exact Heq.
Qed.

Theorem presentation_morphism_kernel_vanishing_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_claim_zero_reflection P ->
  QImagePreimage.vanishes_on_kernel (inst_D I') (inst_L I') ->
  QImagePreimage.vanishes_on_kernel (inst_D I) (inst_L I).
Proof.
  intros Hrefl Hvan' k Hk.
  pose proof (presentation_morphism_kernel_transport P k Hk) as Hk'.
  pose proof (Hvan' (lmap (pm_state P) k) Hk') as Hz'.
  pose proof (presentation_morphism_claim_transport P k
    : lmap (inst_L I') (lmap (pm_state P) k)
      = lmap (pm_claim P) (lmap (inst_L I) k)) as Hct.
  rewrite Hct in Hz'.
  apply Hrefl.
  exact Hz'.
Qed.

Theorem presentation_morphism_precomposition_image_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_claim_zero_reflection P ->
  precomposition_image (inst_D I') (inst_L I') ->
  precomposition_image (inst_D I) (inst_L I).
Proof.
  intros Hrefl Hprec'.
  apply kernel_vanishing_implies_precomposition_image.
  apply (presentation_morphism_kernel_vanishing_reflected P Hrefl).
  apply precomposition_image_implies_kernel_vanishing.
  exact Hprec'.
Qed.

Theorem presentation_morphism_factorisation_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (M' : QLinearMap nV' nW') :
  presentation_claim_zero_reflection P ->
  same_lmap (inst_L I') (precompose (inst_D I') M') ->
  exists M : QLinearMap nV nW,
    same_lmap (inst_L I) (precompose (inst_D I) M).
Proof.
  intros Hrefl HM'.
  apply (presentation_morphism_precomposition_image_reflected P Hrefl).
  exists M'.
  exact HM'.
Qed.

Theorem presentation_morphism_descent_obstruction_zero_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_claim_zero_reflection P ->
  descent_obstruction_zero (inst_D I') (inst_L I') ->
  descent_obstruction_zero (inst_D I) (inst_L I).
Proof.
  exact (presentation_morphism_precomposition_image_reflected P).
Qed.

Theorem presentation_morphism_descent_obstructed_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_claim_zero_reflection P ->
  descent_obstructed (inst_D I) (inst_L I) ->
  descent_obstructed (inst_D I') (inst_L I').
Proof.
  unfold descent_obstructed.
  intros Hrefl Hobs Hzero'.
  apply Hobs.
  apply (presentation_morphism_descent_obstruction_zero_reflected P Hrefl).
  exact Hzero'.
Qed.

Theorem presentation_morphism_gauge_witness_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (k : QVec nU) :
  presentation_claim_zero_reflection P ->
  gauge_witness (inst_D I) (inst_L I) k ->
  gauge_witness (inst_D I') (inst_L I') (lmap (pm_state P) k).
Proof.
  intros Hrefl [Hk Hne].
  split.
  - exact (presentation_morphism_kernel_transport P k Hk).
  - intro Heq.
    apply Hne.
    apply Hrefl.
    rewrite <- (presentation_morphism_claim_transport P k).
    exact Heq.
Qed.

(** ** Part V: Reflection of the exact sector *)

Theorem presentation_morphism_realisable_exact_condition_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  presentation_claim_zero_reflection P ->
  exactness_profile_condition (inst_D I') r' (inst_L I') ProfileRealisableExact ->
  exactness_profile_condition (inst_D I) r (inst_L I) ProfileRealisableExact.
Proof.
  intros Hrecon Hclaim [H1 H2].
  split.
  - apply Hrecon. exact H1.
  - apply (presentation_morphism_descent_obstruction_zero_reflected P Hclaim).
    exact H2.
Qed.

Theorem presentation_morphism_realisable_exact_witness_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  presentation_claim_zero_reflection P ->
  exactness_profile_witness (inst_D I') r' (inst_L I') ProfileRealisableExact ->
  exactness_profile_witness (inst_D I) r (inst_L I) ProfileRealisableExact.
Proof.
  intros Hrecon Hclaim H.
  inversion H as [u0' M' Hr' HM' | | | ].
  destruct (Hrecon (ex_intro _ u0' Hr')) as [u0 Hu0].
  destruct (presentation_morphism_factorisation_reflected P M' Hclaim HM') as [M HM].
  exact (WitnessProfileRealisableExact (inst_D I) r (inst_L I) u0 M Hu0 HM).
Qed.

Theorem presentation_morphism_operational_exact_condition_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  presentation_claim_zero_reflection P ->
  operational_verdict_condition (inst_D I') r' (inst_L I') VerdictExact ->
  operational_verdict_condition (inst_D I) r (inst_L I) VerdictExact.
Proof.
  intros Hrecon Hclaim [H1 H2].
  split.
  - apply Hrecon. exact H1.
  - apply (presentation_morphism_descent_obstruction_zero_reflected P Hclaim).
    exact H2.
Qed.

Theorem presentation_morphism_operational_exact_witness_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  presentation_claim_zero_reflection P ->
  operational_verdict_witness (inst_D I') r' (inst_L I') VerdictExact ->
  operational_verdict_witness (inst_D I) r (inst_L I) VerdictExact.
Proof.
  intros Hrecon Hclaim H.
  inversion H as [ | | u0' M' Hr' HM'].
  destruct (Hrecon (ex_intro _ u0' Hr')) as [u0 Hu0].
  destruct (presentation_morphism_factorisation_reflected P M' Hclaim HM') as [M HM].
  exact (WitnessExact (inst_D I) r (inst_L I) u0 M Hu0 HM).
Qed.

(** ** Part VI: Classifier-level consequences *)

Theorem presentation_morphism_classified_realisable_exact_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  presentation_claim_zero_reflection P ->
  classify_exactness_profile (inst_D I') r' (inst_L I') = ProfileRealisableExact ->
  classify_exactness_profile (inst_D I) r (inst_L I) = ProfileRealisableExact.
Proof.
  intros Hrecon Hclaim Heq.
  apply (classify_exactness_profile_realisable_exact_iff (inst_D I) r (inst_L I)).
  apply (presentation_morphism_realisable_exact_condition_reflected P Hrecon Hclaim).
  apply (classify_exactness_profile_realisable_exact_iff (inst_D I') r' (inst_L I')).
  exact Heq.
Qed.

Theorem presentation_morphism_classified_operational_exact_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  presentation_claim_zero_reflection P ->
  classify_operational_verdict (inst_D I') r' (inst_L I') = VerdictExact ->
  classify_operational_verdict (inst_D I) r (inst_L I) = VerdictExact.
Proof.
  intros Hrecon Hclaim Heq.
  apply (classify_operational_verdict_exact_iff (inst_D I) r (inst_L I)).
  apply (presentation_morphism_operational_exact_condition_reflected P Hrecon Hclaim).
  apply (classify_operational_verdict_exact_iff (inst_D I') r' (inst_L I')).
  exact Heq.
Qed.

Theorem presentation_morphism_classified_operational_obstructed_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  classify_operational_verdict (inst_D I) r (inst_L I) = VerdictObstructed ->
  classify_operational_verdict (inst_D I') r' (inst_L I') = VerdictObstructed.
Proof.
  intros Hrecon Heq.
  apply (classify_operational_verdict_obstructed_iff (inst_D I') r' (inst_L I')).
  apply (presentation_morphism_lift_obstructed_preserved P Hrecon).
  apply (classify_operational_verdict_obstructed_iff (inst_D I) r (inst_L I)).
  exact Heq.
Qed.

Theorem presentation_morphism_classified_operational_underdetermined_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_claim_zero_reflection P ->
  classify_operational_verdict (inst_D I) r (inst_L I) = VerdictUnderdetermined ->
  classify_operational_verdict (inst_D I') r' (inst_L I') = VerdictUnderdetermined.
Proof.
  intros Hclaim Heq.
  apply (classify_operational_verdict_underdetermined_iff (inst_D I') r' (inst_L I')).
  apply (classify_operational_verdict_underdetermined_iff (inst_D I) r (inst_L I)) in Heq.
  destruct Heq as [H1 H2].
  split.
  - exact (presentation_morphism_lift_obstruction_zero_preserved P H1).
  - exact (presentation_morphism_descent_obstructed_preserved P Hclaim H2).
Qed.

(** ** Part VII: Canonical exact-value reflection *)

Theorem presentation_morphism_canonical_exact_value_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_reconciliation_reflection P ->
  presentation_claim_zero_reflection P ->
  lift_obstruction_zero (inst_D I') r' ->
  descent_obstruction_zero (inst_D I') (inst_L I') ->
  exists x : QVec nW,
    exact_value (inst_D I) r (inst_L I) x
    /\
    exact_value (inst_D I') r' (inst_L I') (presentation_value_forward P x)
    /\
    (forall y : QVec nW,
       exact_value (inst_D I) r (inst_L I) y -> y = x)
    /\
    (forall y' : QVec nW',
       exact_value (inst_D I') r' (inst_L I') y' ->
       y' = presentation_value_forward P x).
Proof.
  intros Hrecon Hclaim Hlift' Hdescent'.
  pose proof (Hrecon Hlift') as Hlift.
  pose proof (presentation_morphism_descent_obstruction_zero_reflected P Hclaim Hdescent')
    as Hdescent.
  destruct (canonical_exact_value_exists_unique (inst_D I) r (inst_L I) Hlift Hdescent)
    as [x [Hx Hxuniq]].
  destruct (canonical_exact_value_exists_unique (inst_D I') r' (inst_L I') Hlift' Hdescent')
    as [x' [Hx' Hx'uniq]].
  pose proof Hlift as [u0 Hu0].
  pose proof (presentation_morphism_repair_transport P u0 Hu0) as Hu0'.
  pose proof (Hx u0 Hu0) as HxL.
  pose proof (Hx' (lmap (pm_state P) u0) Hu0') as Hx'L.
  pose proof (presentation_morphism_claim_transport P u0
    : lmap (inst_L I') (lmap (pm_state P) u0)
      = lmap (pm_claim P) (lmap (inst_L I) u0)) as Hct.
  assert (Heqx' : x' = presentation_value_forward P x).
  { change (x' = lmap (pm_claim P) x).
    rewrite <- HxL.
    rewrite <- Hct.
    symmetry.
    exact Hx'L.
  }
  exists x.
  split.
  - exact Hx.
  - split.
    + rewrite <- Heqx'. exact Hx'.
    + split.
      * intros y Hy. symmetry. exact (Hxuniq y Hy).
      * intros y' Hy'.
        transitivity x'.
        -- symmetry. exact (Hx'uniq y' Hy').
        -- exact Heqx'.
Qed.

(** ** Part VIII: Probes *)

Example identity_presentation_morphism_reconciliation_reflection_probe
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV) :
  presentation_reconciliation_reflection (identity_presentation_morphism I r).
Proof.
  apply identity_presentation_morphism_reconciliation_reflection.
Qed.

Example identity_presentation_morphism_claim_zero_reflection_probe
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV) :
  presentation_claim_zero_reflection (identity_presentation_morphism I r).
Proof.
  apply identity_presentation_morphism_claim_zero_reflection.
Qed.

Example presentation_isomorphism_reflection_conditions_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  presentation_reconciliation_reflection (presentation_isomorphism_forward_morphism P)
  /\
  presentation_claim_zero_reflection (presentation_isomorphism_forward_morphism P).
Proof.
  split.
  - apply presentation_isomorphism_reconciliation_reflection.
  - apply presentation_isomorphism_claim_zero_reflection.
Qed.

Example presentation_morphism_classified_operational_exact_reflected_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (Hreconciliation : presentation_reconciliation_reflection P)
    (Hclaim : presentation_claim_zero_reflection P)
    (Hexact :
      classify_operational_verdict (inst_D I') r' (inst_L I') = VerdictExact) :
  classify_operational_verdict (inst_D I) r (inst_L I) = VerdictExact.
Proof.
  apply
    (presentation_morphism_classified_operational_exact_reflected
      P
      Hreconciliation
      Hclaim).
  exact Hexact.
Qed.
