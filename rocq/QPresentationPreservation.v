(** * Presentation Preservation

    A general presentation morphism [P : PresentationMorphism I r I' r']
    transports repairs and source kernel vectors forward along [pm_state],
    but unlike a presentation isomorphism it need not cover every target
    kernel direction. This file isolates that missing ingredient as
    [presentation_kernel_coverage] and shows what preserves automatically
    (realisability) versus what additionally requires coverage (descent
    exactness, and the exact sectors of the profile and verdict
    classifications built from it).

    Full reflection (target-to-source) and bundled verdict safety are out
    of scope here and are reserved for later units. *)

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

Open Scope Qc_scope.

(** ** Part I: Kernel coverage *)

Definition presentation_kernel_coverage
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    : Prop :=
  forall k' : QVec nU',
    kernel (inst_D I') k' ->
    exists k : QVec nU,
      kernel (inst_D I) k /\ lmap (pm_state P) k = k'.

Theorem identity_presentation_morphism_kernel_coverage
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV) :
  presentation_kernel_coverage (identity_presentation_morphism I r).
Proof.
  intros k' Hk'.
  exists k'.
  split.
  - exact Hk'.
  - reflexivity.
Qed.

Theorem compose_presentation_morphism_kernel_coverage
    {nU0 nV0 nW0 nU1 nV1 nW1 nU2 nV2 nW2 : nat}
    {I0 : LinearInstance nU0 nV0 nW0}
    {r0 : QVec nV0}
    {I1 : LinearInstance nU1 nV1 nW1}
    {r1 : QVec nV1}
    {I2 : LinearInstance nU2 nV2 nW2}
    {r2 : QVec nV2}
    (P : PresentationMorphism I0 r0 I1 r1)
    (Q : PresentationMorphism I1 r1 I2 r2) :
  presentation_kernel_coverage P ->
  presentation_kernel_coverage Q ->
  presentation_kernel_coverage (compose_presentation_morphism P Q).
Proof.
  intros HP HQ k2 Hk2.
  destruct (HQ k2 Hk2) as [k1 [Hk1 Hak1]].
  destruct (HP k1 Hk1) as [k0 [Hk0 Hak0]].
  exists k0.
  split.
  - exact Hk0.
  - change (lmap (pm_state Q) (lmap (pm_state P) k0) = k2).
    rewrite Hak0.
    exact Hak1.
Qed.

Theorem presentation_isomorphism_kernel_coverage
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  presentation_kernel_coverage (presentation_isomorphism_forward_morphism P).
Proof.
  intros k' Hk'.
  exists (lmap (iso_backward (pi_state P)) k').
  split.
  - exact (presentation_morphism_kernel_transport
             (presentation_isomorphism_reverse_morphism P) k' Hk').
  - change (lmap (iso_forward (pi_state P))
              (lmap (iso_backward (pi_state P)) k') = k').
    apply (iso_right_inverse (pi_state P) k').
Qed.

(** ** Part II: Automatic realisability preservation *)

Theorem presentation_morphism_lift_obstruction_zero_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  lift_obstruction_zero (inst_D I) r ->
  lift_obstruction_zero (inst_D I') r'.
Proof.
  intros [u Hu].
  exists (lmap (pm_state P) u).
  exact (presentation_morphism_repair_transport P u Hu).
Qed.

Theorem presentation_morphism_lift_obstructed_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  lift_obstructed (inst_D I') r' ->
  lift_obstructed (inst_D I) r.
Proof.
  unfold lift_obstructed.
  intros Hobs' Hzero.
  apply Hobs'.
  apply (presentation_morphism_lift_obstruction_zero_preserved P).
  exact Hzero.
Qed.

(** ** Part III: Descent exactness preservation under coverage *)

Theorem presentation_morphism_kernel_vanishing_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  QImagePreimage.vanishes_on_kernel (inst_D I) (inst_L I) ->
  QImagePreimage.vanishes_on_kernel (inst_D I') (inst_L I').
Proof.
  intros Hcoverage Hvan k' Hk'.
  destruct (Hcoverage k' Hk') as [k [Hk Hak]].
  pose proof (Hvan k Hk) as Hz.
  pose proof (presentation_morphism_claim_transport P k
    : lmap (inst_L I') (lmap (pm_state P) k)
      = lmap (pm_claim P) (lmap (inst_L I) k)) as Hct.
  rewrite Hak in Hct.
  rewrite Hz in Hct.
  rewrite Hct.
  apply (lmap_preserves_zero (pm_claim P)).
Qed.

Theorem presentation_morphism_precomposition_image_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  precomposition_image (inst_D I) (inst_L I) ->
  precomposition_image (inst_D I') (inst_L I').
Proof.
  intros Hcoverage Hprec.
  apply kernel_vanishing_implies_precomposition_image.
  apply (presentation_morphism_kernel_vanishing_preserved P Hcoverage).
  apply precomposition_image_implies_kernel_vanishing.
  exact Hprec.
Qed.

Theorem presentation_morphism_factorisation_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (M : QLinearMap nV nW) :
  presentation_kernel_coverage P ->
  same_lmap (inst_L I) (precompose (inst_D I) M) ->
  exists M' : QLinearMap nV' nW',
    same_lmap (inst_L I') (precompose (inst_D I') M').
Proof.
  intros Hcoverage HM.
  apply (presentation_morphism_precomposition_image_preserved P Hcoverage).
  exists M.
  exact HM.
Qed.

Theorem presentation_morphism_descent_obstruction_zero_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  descent_obstruction_zero (inst_D I) (inst_L I) ->
  descent_obstruction_zero (inst_D I') (inst_L I').
Proof.
  exact (presentation_morphism_precomposition_image_preserved P).
Qed.

Theorem presentation_morphism_descent_obstructed_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  descent_obstructed (inst_D I') (inst_L I') ->
  descent_obstructed (inst_D I) (inst_L I).
Proof.
  unfold descent_obstructed.
  intros Hcoverage Hobs' Hzero.
  apply Hobs'.
  apply (presentation_morphism_descent_obstruction_zero_preserved P Hcoverage).
  exact Hzero.
Qed.

(** ** Part IV: Exact profile-sector preservation *)

Theorem presentation_morphism_realisable_exact_condition_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  exactness_profile_condition (inst_D I) r (inst_L I) ProfileRealisableExact ->
  exactness_profile_condition (inst_D I') r' (inst_L I') ProfileRealisableExact.
Proof.
  intros Hcoverage [H1 H2].
  split.
  - apply (presentation_morphism_lift_obstruction_zero_preserved P). exact H1.
  - apply (presentation_morphism_descent_obstruction_zero_preserved P Hcoverage).
    exact H2.
Qed.

Theorem presentation_morphism_realisable_exact_witness_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  exactness_profile_witness (inst_D I) r (inst_L I) ProfileRealisableExact ->
  exactness_profile_witness (inst_D I') r' (inst_L I') ProfileRealisableExact.
Proof.
  intros Hcoverage H.
  inversion H as [u0 M Hr HM | | | ].
  destruct (presentation_morphism_factorisation_preserved P M Hcoverage HM)
    as [M' HM'].
  exact (WitnessProfileRealisableExact (inst_D I') r' (inst_L I')
           (lmap (pm_state P) u0) M'
           (presentation_morphism_repair_transport P u0 Hr)
           HM').
Qed.

(** ** Part V: Operational exact-sector preservation *)

Theorem presentation_morphism_operational_exact_condition_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  operational_verdict_condition (inst_D I) r (inst_L I) VerdictExact ->
  operational_verdict_condition (inst_D I') r' (inst_L I') VerdictExact.
Proof.
  intros Hcoverage [H1 H2].
  split.
  - apply (presentation_morphism_lift_obstruction_zero_preserved P). exact H1.
  - apply (presentation_morphism_descent_obstruction_zero_preserved P Hcoverage).
    exact H2.
Qed.

Theorem presentation_morphism_operational_exact_witness_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  operational_verdict_witness (inst_D I) r (inst_L I) VerdictExact ->
  operational_verdict_witness (inst_D I') r' (inst_L I') VerdictExact.
Proof.
  intros Hcoverage H.
  inversion H as [ | | u0 M Hr HM].
  destruct (presentation_morphism_factorisation_preserved P M Hcoverage HM)
    as [M' HM'].
  exact (WitnessExact (inst_D I') r' (inst_L I')
           (lmap (pm_state P) u0) M'
           (presentation_morphism_repair_transport P u0 Hr)
           HM').
Qed.

(** ** Part VI: Classifier-level consequences *)

Theorem presentation_morphism_classified_realisable_exact_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  classify_exactness_profile (inst_D I) r (inst_L I) = ProfileRealisableExact ->
  classify_exactness_profile (inst_D I') r' (inst_L I') = ProfileRealisableExact.
Proof.
  intros Hcoverage Heq.
  apply (classify_exactness_profile_realisable_exact_iff (inst_D I') r' (inst_L I')).
  apply (presentation_morphism_realisable_exact_condition_preserved P Hcoverage).
  apply (classify_exactness_profile_realisable_exact_iff (inst_D I) r (inst_L I)).
  exact Heq.
Qed.

Theorem presentation_morphism_classified_operational_exact_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
  classify_operational_verdict (inst_D I) r (inst_L I) = VerdictExact ->
  classify_operational_verdict (inst_D I') r' (inst_L I') = VerdictExact.
Proof.
  intros Hcoverage Heq.
  apply (classify_operational_verdict_exact_iff (inst_D I') r' (inst_L I')).
  apply (presentation_morphism_operational_exact_condition_preserved P Hcoverage).
  apply (classify_operational_verdict_exact_iff (inst_D I) r (inst_L I)).
  exact Heq.
Qed.

Theorem presentation_morphism_classified_operational_obstructed_reflected
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  classify_operational_verdict (inst_D I') r' (inst_L I') = VerdictObstructed ->
  classify_operational_verdict (inst_D I) r (inst_L I) = VerdictObstructed.
Proof.
  intro Heq.
  apply (classify_operational_verdict_obstructed_iff (inst_D I) r (inst_L I)).
  apply (presentation_morphism_lift_obstructed_reflected P).
  apply (classify_operational_verdict_obstructed_iff (inst_D I') r' (inst_L I')).
  exact Heq.
Qed.

(** ** Part VII: Forward exact-value transport *)

Definition presentation_value_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (x : QVec nW)
    : QVec nW' :=
  lmap (pm_claim P) x.

Theorem presentation_morphism_transported_repair_value
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (u0 : QVec nU)
    (x : QVec nW) :
  repair_fibre (inst_D I) r u0 ->
  exact_value (inst_D I) r (inst_L I) x ->
  lmap (inst_L I') (lmap (pm_state P) u0) = presentation_value_forward P x.
Proof.
  intros Hrepair Hexact.
  change (lmap (inst_L I') (lmap (pm_state P) u0) = lmap (pm_claim P) x).
  pose proof (presentation_morphism_claim_transport P u0
    : lmap (inst_L I') (lmap (pm_state P) u0)
      = lmap (pm_claim P) (lmap (inst_L I) u0)) as Hct.
  rewrite Hct.
  f_equal.
  apply (Hexact u0 Hrepair).
Qed.

Theorem presentation_morphism_exact_value_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (x : QVec nW) :
  presentation_kernel_coverage P ->
  lift_obstruction_zero (inst_D I) r ->
  descent_obstruction_zero (inst_D I) (inst_L I) ->
  exact_value (inst_D I) r (inst_L I) x ->
  exact_value (inst_D I') r' (inst_L I') (presentation_value_forward P x).
Proof.
  intros Hcoverage Hlift Hdescent Hx.
  destruct Hlift as [u0 Hu0].
  pose proof (presentation_morphism_descent_obstruction_zero_preserved P
                Hcoverage Hdescent) as Hdescent'.
  apply descent_obstruction_zero_iff_kernel_vanishing in Hdescent'.
  pose proof (presentation_morphism_repair_transport P u0 Hu0) as Hrepair'.
  pose proof (repair_value_is_exact (inst_D I') r' (inst_L I')
                (lmap (pm_state P) u0) Hdescent' Hrepair') as Hexact'.
  pose proof (presentation_morphism_transported_repair_value P u0 x Hu0 Hx)
    as Htrv.
  unfold repair_value in Hexact'.
  rewrite <- Htrv.
  exact Hexact'.
Qed.

Theorem presentation_morphism_canonical_exact_value_preserved
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r') :
  presentation_kernel_coverage P ->
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
  intros Hcoverage Hlift Hdescent.
  destruct (canonical_exact_value_exists_unique (inst_D I) r (inst_L I)
              Hlift Hdescent) as [x [Hx Hxuniq]].
  exists x.
  split.
  - exact Hx.
  - split.
    + exact (presentation_morphism_exact_value_preserved P x Hcoverage
               Hlift Hdescent Hx).
    + split.
      * intros y Hy. symmetry. exact (Hxuniq y Hy).
      * intros y' Hy'.
        pose proof (presentation_morphism_exact_value_preserved P x Hcoverage
                      Hlift Hdescent Hx) as Hexact_target.
        pose proof Hlift as [u0 Hu0].
        pose proof (presentation_morphism_repair_transport P u0 Hu0
          : repair_fibre (inst_D I') r' (lmap (pm_state P) u0)) as Hmem'.
        exact (exact_value_unique_on_nonempty_fibre (inst_D I') r' (inst_L I')
                 (lmap (pm_state P) u0) Hmem'
                 y' (presentation_value_forward P x) Hy'
                 Hexact_target).
Qed.

(** ** Part VIII: Probes *)

Example identity_presentation_morphism_kernel_coverage_probe
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV) :
  presentation_kernel_coverage (identity_presentation_morphism I r).
Proof.
  apply identity_presentation_morphism_kernel_coverage.
Qed.

Example presentation_morphism_lift_obstruction_zero_preserved_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (H : lift_obstruction_zero (inst_D I) r) :
  lift_obstruction_zero (inst_D I') r'.
Proof.
  apply (presentation_morphism_lift_obstruction_zero_preserved P).
  exact H.
Qed.

Example presentation_morphism_classified_operational_exact_preserved_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (Hcoverage : presentation_kernel_coverage P)
    (H : classify_operational_verdict (inst_D I) r (inst_L I) = VerdictExact) :
  classify_operational_verdict (inst_D I') r' (inst_L I') = VerdictExact.
Proof.
  apply (presentation_morphism_classified_operational_exact_preserved P Hcoverage).
  exact H.
Qed.

Example presentation_morphism_exact_value_preserved_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (x : QVec nW)
    (Hcoverage : presentation_kernel_coverage P)
    (Hlift : lift_obstruction_zero (inst_D I) r)
    (Hdescent : descent_obstruction_zero (inst_D I) (inst_L I))
    (Hx : exact_value (inst_D I) r (inst_L I) x) :
  exact_value (inst_D I') r' (inst_L I') (presentation_value_forward P x).
Proof.
  apply (presentation_morphism_exact_value_preserved P x Hcoverage
           Hlift Hdescent).
  exact Hx.
Qed.
