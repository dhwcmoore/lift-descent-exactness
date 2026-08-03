(** * Presentation Safety

    Units 28 and 29 established the two halves of R10 for a general,
    possibly noninvertible [P : PresentationMorphism I r I' r']:

    - preservation (source-to-target), under [presentation_kernel_coverage];
    - reflection (target-to-source), under [presentation_reconciliation_reflection]
      and [presentation_claim_zero_reflection].

    This file bundles exactly those three obligations into
    [PresentationSafety] and derives full two-way equivalence of the
    lifting axis, the descent axis, the four-sector exactness profile,
    the three-sector operational verdict, both classifiers, and the
    canonical exact value.

    [PresentationSafety] packages a compositional SUFFICIENT set of
    hypotheses for this equivalence. The file does not claim any of the
    three fields is logically necessary for a fixed-instance profile
    equivalence: global claim-zero reflection may be strictly stronger
    than the descent-reflection implication it is used for, kernel
    coverage may be stronger than what any one claim map requires, and
    reconciliation reflection is deliberately stated only at the
    distinguished residue rather than as a global image-reflection
    property of the residual map.

    The two witness-equivalence theorems below
    ([presentation_safe_exactness_profile_witness_iff] and
    [presentation_safe_operational_verdict_witness_iff]) are
    proposition-level existence equivalences, proved by routing through
    the semantic condition via [exactness_profile_witness_iff_condition]
    and [operational_verdict_witness_iff_condition]. They assert that a
    witness exists on one side if and only if one exists on the other;
    they do not identify, transport, or equate any particular source
    witness with any particular target witness. Direct termwise witness
    transport for invertible presentations remains the content of R9. *)

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
From LiftDescent Require Import QCanonicalValue.
From LiftDescent Require Import QLinearIsomorphism.
From LiftDescent Require Import QPresentationMorphism.
From LiftDescent Require Import QPresentationPreservation.
From LiftDescent Require Import QPresentationReflection.

Open Scope Qc_scope.

(** ** Part I: The safety package *)

Record PresentationSafety
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    : Prop :=
{
  presentation_safety_kernel_coverage :
    presentation_kernel_coverage P;

  presentation_safety_reconciliation_reflection :
    presentation_reconciliation_reflection P;

  presentation_safety_claim_zero_reflection :
    presentation_claim_zero_reflection P
}.

(** ** Part II: Structural closure *)

Theorem identity_presentation_morphism_safe
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV) :
  PresentationSafety (identity_presentation_morphism I r).
Proof.
  exact {|
    presentation_safety_kernel_coverage :=
      identity_presentation_morphism_kernel_coverage I r;
    presentation_safety_reconciliation_reflection :=
      identity_presentation_morphism_reconciliation_reflection I r;
    presentation_safety_claim_zero_reflection :=
      identity_presentation_morphism_claim_zero_reflection I r
  |}.
Qed.

Theorem compose_presentation_morphism_safe
    {nU0 nV0 nW0 nU1 nV1 nW1 nU2 nV2 nW2 : nat}
    {I0 : LinearInstance nU0 nV0 nW0}
    {r0 : QVec nV0}
    {I1 : LinearInstance nU1 nV1 nW1}
    {r1 : QVec nV1}
    {I2 : LinearInstance nU2 nV2 nW2}
    {r2 : QVec nV2}
    (P : PresentationMorphism I0 r0 I1 r1)
    (Q : PresentationMorphism I1 r1 I2 r2) :
  PresentationSafety P ->
  PresentationSafety Q ->
  PresentationSafety (compose_presentation_morphism P Q).
Proof.
  intros [HPk HPr HPc] [HQk HQr HQc].
  exact {|
    presentation_safety_kernel_coverage :=
      compose_presentation_morphism_kernel_coverage P Q HPk HQk;
    presentation_safety_reconciliation_reflection :=
      compose_presentation_morphism_reconciliation_reflection P Q HPr HQr;
    presentation_safety_claim_zero_reflection :=
      compose_presentation_morphism_claim_zero_reflection P Q HPc HQc
  |}.
Qed.

Theorem presentation_isomorphism_safe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  PresentationSafety (presentation_isomorphism_forward_morphism P).
Proof.
  exact {|
    presentation_safety_kernel_coverage :=
      presentation_isomorphism_kernel_coverage P;
    presentation_safety_reconciliation_reflection :=
      presentation_isomorphism_reconciliation_reflection P;
    presentation_safety_claim_zero_reflection :=
      presentation_isomorphism_claim_zero_reflection P
  |}.
Qed.

(** ** Part III: Equivalence of the lifting axis *)

Theorem presentation_safe_lift_obstruction_zero_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
  (lift_obstruction_zero (inst_D I) r
   <->
   lift_obstruction_zero (inst_D I') r').
Proof.
  intros [Hcov Hrecon Hclaim].
  split.
  - apply (presentation_morphism_lift_obstruction_zero_preserved P).
  - apply (presentation_morphism_lift_obstruction_zero_reflected P Hrecon).
Qed.

Theorem presentation_safe_lift_obstructed_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
  (lift_obstructed (inst_D I) r
   <->
   lift_obstructed (inst_D I') r').
Proof.
  intros [Hcov Hrecon Hclaim].
  split.
  - apply (presentation_morphism_lift_obstructed_preserved P Hrecon).
  - apply (presentation_morphism_lift_obstructed_reflected P).
Qed.

(** ** Part IV: Equivalence of the descent axis *)

Theorem presentation_safe_kernel_vanishing_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
  (QImagePreimage.vanishes_on_kernel (inst_D I) (inst_L I)
   <->
   QImagePreimage.vanishes_on_kernel (inst_D I') (inst_L I')).
Proof.
  intros [Hcov Hrecon Hclaim].
  split.
  - apply (presentation_morphism_kernel_vanishing_preserved P Hcov).
  - apply (presentation_morphism_kernel_vanishing_reflected P Hclaim).
Qed.

Theorem presentation_safe_precomposition_image_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
  (precomposition_image (inst_D I) (inst_L I)
   <->
   precomposition_image (inst_D I') (inst_L I')).
Proof.
  intros [Hcov Hrecon Hclaim].
  split.
  - apply (presentation_morphism_precomposition_image_preserved P Hcov).
  - apply (presentation_morphism_precomposition_image_reflected P Hclaim).
Qed.

Theorem presentation_safe_descent_obstruction_zero_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
  (descent_obstruction_zero (inst_D I) (inst_L I)
   <->
   descent_obstruction_zero (inst_D I') (inst_L I')).
Proof.
  intros [Hcov Hrecon Hclaim].
  split.
  - apply (presentation_morphism_descent_obstruction_zero_preserved P Hcov).
  - apply (presentation_morphism_descent_obstruction_zero_reflected P Hclaim).
Qed.

Theorem presentation_safe_descent_obstructed_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
  (descent_obstructed (inst_D I) (inst_L I)
   <->
   descent_obstructed (inst_D I') (inst_L I')).
Proof.
  intros [Hcov Hrecon Hclaim].
  split.
  - apply (presentation_morphism_descent_obstructed_preserved P Hclaim).
  - apply (presentation_morphism_descent_obstructed_reflected P Hcov).
Qed.

(** ** Part V: Full four-sector profile safety *)

Theorem presentation_safe_exactness_profile_condition_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (profile : exactness_profile) :
  PresentationSafety P ->
  (exactness_profile_condition (inst_D I) r (inst_L I) profile
   <->
   exactness_profile_condition (inst_D I') r' (inst_L I') profile).
Proof.
  intros Hsafe.
  destruct profile; simpl; split.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstruction_zero_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstruction_zero_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstruction_zero_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstruction_zero_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstruction_zero_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstructed_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstruction_zero_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstructed_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstructed_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstruction_zero_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstructed_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstruction_zero_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstructed_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstructed_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstructed_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstructed_iff P Hsafe); exact H2.
Qed.

Theorem presentation_safe_exactness_profile_witness_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (profile : exactness_profile) :
  PresentationSafety P ->
  (exactness_profile_witness (inst_D I) r (inst_L I) profile
   <->
   exactness_profile_witness (inst_D I') r' (inst_L I') profile).
Proof.
  intros Hsafe.
  split.
  - intro H.
    apply (exactness_profile_witness_iff_condition (inst_D I') r' (inst_L I') profile).
    apply (presentation_safe_exactness_profile_condition_iff P profile Hsafe).
    apply (exactness_profile_witness_iff_condition (inst_D I) r (inst_L I) profile).
    exact H.
  - intro H.
    apply (exactness_profile_witness_iff_condition (inst_D I) r (inst_L I) profile).
    apply (presentation_safe_exactness_profile_condition_iff P profile Hsafe).
    apply (exactness_profile_witness_iff_condition (inst_D I') r' (inst_L I') profile).
    exact H.
Qed.

Theorem presentation_safe_classify_exactness_profile_invariant
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
  classify_exactness_profile (inst_D I) r (inst_L I)
  =
  classify_exactness_profile (inst_D I') r' (inst_L I').
Proof.
  intro Hsafe.
  pose proof (classify_exactness_profile_condition (inst_D I) r (inst_L I)) as Hc.
  destruct (presentation_safe_exactness_profile_condition_iff P
              (classify_exactness_profile (inst_D I) r (inst_L I)) Hsafe)
    as [Hfwd _].
  pose proof (Hfwd Hc) as Hc'.
  pose proof (classify_exactness_profile_condition (inst_D I') r' (inst_L I')) as Hc''.
  exact (exactness_profile_condition_unique (inst_D I') r' (inst_L I')
           (classify_exactness_profile (inst_D I) r (inst_L I))
           (classify_exactness_profile (inst_D I') r' (inst_L I'))
           Hc' Hc'').
Qed.

(** ** Part VI: Operational-verdict safety *)

Theorem presentation_safe_operational_verdict_condition_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (verdict : operational_verdict) :
  PresentationSafety P ->
  (operational_verdict_condition (inst_D I) r (inst_L I) verdict
   <->
   operational_verdict_condition (inst_D I') r' (inst_L I') verdict).
Proof.
  intros Hsafe.
  destruct verdict; simpl; split.
  - intro H1. apply (presentation_safe_lift_obstructed_iff P Hsafe); exact H1.
  - intro H1. apply (presentation_safe_lift_obstructed_iff P Hsafe); exact H1.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstruction_zero_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstructed_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstruction_zero_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstructed_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstruction_zero_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstruction_zero_iff P Hsafe); exact H2.
  - intros [H1 H2]; split.
    + apply (presentation_safe_lift_obstruction_zero_iff P Hsafe); exact H1.
    + apply (presentation_safe_descent_obstruction_zero_iff P Hsafe); exact H2.
Qed.

Theorem presentation_safe_operational_verdict_witness_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (verdict : operational_verdict) :
  PresentationSafety P ->
  (operational_verdict_witness (inst_D I) r (inst_L I) verdict
   <->
   operational_verdict_witness (inst_D I') r' (inst_L I') verdict).
Proof.
  intros Hsafe.
  split.
  - intro H.
    apply (operational_verdict_witness_iff_condition (inst_D I') r' (inst_L I') verdict).
    apply (presentation_safe_operational_verdict_condition_iff P verdict Hsafe).
    apply (operational_verdict_witness_iff_condition (inst_D I) r (inst_L I) verdict).
    exact H.
  - intro H.
    apply (operational_verdict_witness_iff_condition (inst_D I) r (inst_L I) verdict).
    apply (presentation_safe_operational_verdict_condition_iff P verdict Hsafe).
    apply (operational_verdict_witness_iff_condition (inst_D I') r' (inst_L I') verdict).
    exact H.
Qed.

Theorem presentation_safe_classify_operational_verdict_invariant
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
  classify_operational_verdict (inst_D I) r (inst_L I)
  =
  classify_operational_verdict (inst_D I') r' (inst_L I').
Proof.
  intro Hsafe.
  pose proof (classify_operational_verdict_condition (inst_D I) r (inst_L I)) as Hc.
  destruct (presentation_safe_operational_verdict_condition_iff P
              (classify_operational_verdict (inst_D I) r (inst_L I)) Hsafe)
    as [Hfwd _].
  pose proof (Hfwd Hc) as Hc'.
  pose proof (classify_operational_verdict_condition (inst_D I') r' (inst_L I')) as Hc''.
  exact (operational_verdict_condition_unique (inst_D I') r' (inst_L I')
           (classify_operational_verdict (inst_D I) r (inst_L I))
           (classify_operational_verdict (inst_D I') r' (inst_L I'))
           Hc' Hc'').
Qed.

(** ** Part VII: Canonical exact-value safety *)

Theorem presentation_safe_canonical_exact_value_from_source
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
  lift_obstruction_zero (inst_D I) r ->
  descent_obstruction_zero (inst_D I) (inst_L I) ->
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
  intros [Hcov Hrecon Hclaim] Hlift Hdescent.
  exact (presentation_morphism_canonical_exact_value_preserved P Hcov Hlift Hdescent).
Qed.

Theorem presentation_safe_canonical_exact_value_from_target
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  PresentationSafety P ->
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
  intros [Hcov Hrecon Hclaim] Hlift' Hdescent'.
  exact (presentation_morphism_canonical_exact_value_reflected P Hrecon Hclaim
           Hlift' Hdescent').
Qed.

(** ** Part VIII: Probes *)

Example identity_presentation_morphism_safe_probe
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV) :
  PresentationSafety (identity_presentation_morphism I r).
Proof.
  apply identity_presentation_morphism_safe.
Qed.

Example compose_presentation_morphism_safe_probe
    {nU0 nV0 nW0 nU1 nV1 nW1 nU2 nV2 nW2 : nat}
    {I0 : LinearInstance nU0 nV0 nW0}
    {r0 : QVec nV0}
    {I1 : LinearInstance nU1 nV1 nW1}
    {r1 : QVec nV1}
    {I2 : LinearInstance nU2 nV2 nW2}
    {r2 : QVec nV2}
    (P : PresentationMorphism I0 r0 I1 r1)
    (Q : PresentationMorphism I1 r1 I2 r2)
    (HP : PresentationSafety P)
    (HQ : PresentationSafety Q) :
  PresentationSafety (compose_presentation_morphism P Q).
Proof.
  apply (compose_presentation_morphism_safe P Q HP HQ).
Qed.

Example presentation_isomorphism_safe_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  PresentationSafety (presentation_isomorphism_forward_morphism P).
Proof.
  apply presentation_isomorphism_safe.
Qed.

Example presentation_safe_classify_operational_verdict_invariant_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (Hsafety : PresentationSafety P) :
  classify_operational_verdict (inst_D I) r (inst_L I)
  =
  classify_operational_verdict (inst_D I') r' (inst_L I').
Proof.
  apply (presentation_safe_classify_operational_verdict_invariant P Hsafety).
Qed.
