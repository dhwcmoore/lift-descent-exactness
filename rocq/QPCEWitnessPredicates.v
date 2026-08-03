(** * PCE Witness Predicates

    PCE's three admissible certificate variants — EXACT,
    UNDERDETERMINED, OBSTRUCTED — check exactly the algebraic equations
    formalised here, at the mathematical proposition level only. This
    file does not formalise admissibility ([QAdmissibilityGate] is not
    imported); it concerns only the witness predicates that apply once
    the gate has already succeeded. Unit 34 combines the two.

    [pce_exact_witness]'s primitive claimed-value equation is
    [lmap M r = x] (the factor map applied to the residue), not
    [lmap L u0 = x] (the claim map applied to a repair) — the latter is
    proved as [pce_exact_witness_repair_value], a derived consequence,
    reflecting the PCE boundary where [u0] proves repair existence,
    [M] proves claim descent, and [M r] computes the invariant value
    from the residue alone.

    [pce_obstructed_witness] takes no claim map: lifting obstruction is
    logically prior to and independent of whether any particular claim
    descends. Consequently an obstructed PCE witness identifies only
    the two-sector disjunction
    [ProfileObstructedButDescending \/ ProfileObstructedAndNonDescending]
    — never a specific sector — since no descent evidence is supplied. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QLinearFunctional.
From LiftDescent Require Import QSeparatorWitness.
From LiftDescent Require Import QGaugeWitness.
From LiftDescent Require Import QVerdictClassification.
From LiftDescent Require Import QExactnessProfile.
From LiftDescent Require Import QCanonicalValue.

Open Scope Qc_scope.

(** ** Part I: Exact witness predicate *)

Definition pce_exact_witness
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w)
    : Prop :=
  repair_fibre D r u0
  /\
  same_lmap L (precompose D M)
  /\
  lmap M r = x.

Theorem pce_exact_witness_repair_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w) :
  pce_exact_witness D r L x u0 M ->
  lmap L u0 = x.
Proof.
  intros [Hrepair [Hfact Hval]].
  rewrite (Hfact u0).
  change (lmap M (lmap D u0) = x).
  unfold repair_fibre in Hrepair.
  rewrite Hrepair.
  exact Hval.
Qed.

Theorem pce_exact_witness_exact_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w) :
  pce_exact_witness D r L x u0 M ->
  exact_value D r L x.
Proof.
  intros [_ [Hfact Hval]].
  rewrite <- Hval.
  change (exact_value D r L (factor_value M r)).
  apply (factor_value_is_exact D r L M Hfact).
Qed.

Theorem pce_exact_witness_operational
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w) :
  pce_exact_witness D r L x u0 M ->
  operational_verdict_witness D r L VerdictExact.
Proof.
  intros [Hrepair [Hfact _]].
  exact (WitnessExact D r L u0 M Hrepair Hfact).
Qed.

Theorem pce_exact_witness_profile
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w) :
  pce_exact_witness D r L x u0 M ->
  exactness_profile_witness D r L ProfileRealisableExact.
Proof.
  intros [Hrepair [Hfact _]].
  exact (WitnessProfileRealisableExact D r L u0 M Hrepair Hfact).
Qed.

Theorem pce_exact_witness_classified_operational
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w) :
  pce_exact_witness D r L x u0 M ->
  classify_operational_verdict D r L = VerdictExact.
Proof.
  intros [Hrepair [Hfact _]].
  apply (classify_operational_verdict_exact_iff D r L).
  split.
  - exists u0. exact Hrepair.
  - exists M. exact Hfact.
Qed.

Theorem pce_exact_witness_classified_profile
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w) :
  pce_exact_witness D r L x u0 M ->
  classify_exactness_profile D r L = ProfileRealisableExact.
Proof.
  intros [Hrepair [Hfact _]].
  apply (classify_exactness_profile_realisable_exact_iff D r L).
  split.
  - exists u0. exact Hrepair.
  - exists M. exact Hfact.
Qed.

Theorem operational_exact_witness_iff_pce_exact_witness_exists
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  operational_verdict_witness D r L VerdictExact
  <->
  exists (x : QVec w) (u0 : QVec u) (M : QLinearMap v w),
    pce_exact_witness D r L x u0 M.
Proof.
  split.
  - intro H.
    inversion H as [ | | u0 M Hrepair Hfact].
    exists (lmap M r), u0, M.
    split.
    + exact Hrepair.
    + split.
      * exact Hfact.
      * reflexivity.
  - intros [x [u0 [M Hpce]]].
    apply (pce_exact_witness_operational D r L x u0 M).
    exact Hpce.
Qed.

Theorem pce_exact_witness_at_value_iff_operational_exact_and_exact_value
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w) :
  (
    exists (u0 : QVec u) (M : QLinearMap v w),
      pce_exact_witness D r L x u0 M
  )
  <->
  (
    operational_verdict_witness D r L VerdictExact
    /\
    exact_value D r L x
  ).
Proof.
  split.
  - intros [u0 [M Hpce]].
    split.
    + apply (pce_exact_witness_operational D r L x u0 M). exact Hpce.
    + apply (pce_exact_witness_exact_value D r L x u0 M). exact Hpce.
  - intros [Hop Hxv].
    inversion Hop as [ | | u0 M Hrepair Hfact].
    exists u0, M.
    split.
    + exact Hrepair.
    + split.
      * exact Hfact.
      * pose proof (factor_value_is_exact D r L M Hfact) as Hfx.
        exact (exact_value_unique_on_nonempty_fibre D r L u0 Hrepair
                 (lmap M r) x Hfx Hxv).
Qed.

Theorem pce_exact_claimed_value_unique
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x1 x2 : QVec w)
    (u1 u2 : QVec u)
    (M1 M2 : QLinearMap v w) :
  pce_exact_witness D r L x1 u1 M1 ->
  pce_exact_witness D r L x2 u2 M2 ->
  x1 = x2.
Proof.
  intros H1 H2.
  pose proof (pce_exact_witness_exact_value D r L x1 u1 M1 H1) as Hx1.
  pose proof (pce_exact_witness_exact_value D r L x2 u2 M2 H2) as Hx2.
  destruct H1 as [Hrepair1 _].
  exact (exact_value_unique_on_nonempty_fibre D r L u1 Hrepair1 x1 x2 Hx1 Hx2).
Qed.

(** ** Part II: Underdetermined witness predicate *)

Definition pce_underdetermined_witness
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (u0 k : QVec u)
    : Prop :=
  repair_fibre D r u0
  /\
  gauge_witness D L k.

Theorem pce_underdetermined_witness_operational
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (u0 k : QVec u) :
  pce_underdetermined_witness D r L u0 k ->
  operational_verdict_witness D r L VerdictUnderdetermined.
Proof.
  intros [Hrepair Hgauge].
  exact (WitnessUnderdetermined D r L u0 k Hrepair Hgauge).
Qed.

Theorem pce_underdetermined_witness_profile
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (u0 k : QVec u) :
  pce_underdetermined_witness D r L u0 k ->
  exactness_profile_witness D r L ProfileRealisableUnderdetermined.
Proof.
  intros [Hrepair Hgauge].
  exact (WitnessProfileRealisableUnderdetermined D r L u0 k Hrepair Hgauge).
Qed.

Theorem pce_underdetermined_witness_exhibits_ambiguity
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (u0 k : QVec u) :
  pce_underdetermined_witness D r L u0 k ->
  repair_fibre D r (vadd u0 k)
  /\
  lmap L (vadd u0 k) <> lmap L u0.
Proof.
  intros [Hrepair Hgauge].
  exact (gauge_witness_exhibits_repair_ambiguity D L r u0 k Hrepair Hgauge).
Qed.

Theorem operational_underdetermined_witness_iff_pce_underdetermined_witness_exists
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  operational_verdict_witness D r L VerdictUnderdetermined
  <->
  exists u0 k : QVec u, pce_underdetermined_witness D r L u0 k.
Proof.
  split.
  - intro H.
    inversion H as [ | u0 k Hrepair Hgauge | ].
    exists u0, k.
    split; assumption.
  - intros [u0 [k Hpce]].
    apply (pce_underdetermined_witness_operational D r L u0 k).
    exact Hpce.
Qed.

Theorem pce_underdetermined_witness_exists_iff_condition
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  (
    exists u0 k : QVec u, pce_underdetermined_witness D r L u0 k
  )
  <->
  operational_verdict_condition D r L VerdictUnderdetermined.
Proof.
  split.
  - intro H.
    apply (operational_verdict_witness_iff_condition D r L VerdictUnderdetermined).
    apply (operational_underdetermined_witness_iff_pce_underdetermined_witness_exists D r L).
    exact H.
  - intro H.
    apply (operational_underdetermined_witness_iff_pce_underdetermined_witness_exists D r L).
    apply (operational_verdict_witness_iff_condition D r L VerdictUnderdetermined).
    exact H.
Qed.

Theorem pce_underdetermined_witness_exists_iff_classified_operational
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  (
    exists u0 k : QVec u, pce_underdetermined_witness D r L u0 k
  )
  <->
  classify_operational_verdict D r L = VerdictUnderdetermined.
Proof.
  rewrite (pce_underdetermined_witness_exists_iff_condition D r L).
  rewrite (classify_operational_verdict_underdetermined_iff D r L).
  split; intro H; exact H.
Qed.

Theorem pce_underdetermined_witness_exists_iff_classified_profile
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  (
    exists u0 k : QVec u, pce_underdetermined_witness D r L u0 k
  )
  <->
  classify_exactness_profile D r L = ProfileRealisableUnderdetermined.
Proof.
  rewrite (pce_underdetermined_witness_exists_iff_condition D r L).
  rewrite (classify_exactness_profile_realisable_underdetermined_iff D r L).
  split; intro H; exact H.
Qed.

(** ** Part III: Obstructed witness predicate *)

Definition pce_obstructed_witness
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (y : QLinearFunctional v)
    : Prop :=
  separator_witness D r y.

Theorem pce_obstructed_witness_iff_separator_witness
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (y : QLinearFunctional v) :
  pce_obstructed_witness D r y <-> separator_witness D r y.
Proof.
  split; intro H; exact H.
Qed.

Theorem pce_obstructed_witness_operational
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (y : QLinearFunctional v) :
  pce_obstructed_witness D r y ->
  operational_verdict_witness D r L VerdictObstructed.
Proof.
  intro Hy.
  exact (WitnessObstructed D r L y Hy).
Qed.

Theorem operational_obstructed_witness_iff_pce_obstructed_witness_exists
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  operational_verdict_witness D r L VerdictObstructed
  <->
  exists y : QLinearFunctional v, pce_obstructed_witness D r y.
Proof.
  split.
  - intro H.
    inversion H as [y Hy | | ].
    exists y. exact Hy.
  - intros [y Hy].
    apply (pce_obstructed_witness_operational D r L y).
    exact Hy.
Qed.

Theorem pce_obstructed_witness_exists_iff_condition
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  (
    exists y : QLinearFunctional v, pce_obstructed_witness D r y
  )
  <->
  operational_verdict_condition D r L VerdictObstructed.
Proof.
  split.
  - intro H.
    apply (operational_verdict_witness_iff_condition D r L VerdictObstructed).
    apply (operational_obstructed_witness_iff_pce_obstructed_witness_exists D r L).
    exact H.
  - intro H.
    apply (operational_obstructed_witness_iff_pce_obstructed_witness_exists D r L).
    apply (operational_verdict_witness_iff_condition D r L VerdictObstructed).
    exact H.
Qed.

Theorem pce_obstructed_witness_exists_iff_classified_operational
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  (
    exists y : QLinearFunctional v, pce_obstructed_witness D r y
  )
  <->
  classify_operational_verdict D r L = VerdictObstructed.
Proof.
  rewrite (pce_obstructed_witness_exists_iff_condition D r L).
  rewrite (classify_operational_verdict_obstructed_iff D r L).
  split; intro H; exact H.
Qed.

Theorem pce_obstructed_witness_profile_condition_disjunction
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (y : QLinearFunctional v) :
  pce_obstructed_witness D r y ->
  exactness_profile_condition D r L ProfileObstructedButDescending
  \/
  exactness_profile_condition D r L ProfileObstructedAndNonDescending.
Proof.
  intro Hy.
  pose proof (separator_witness_sound D r y Hy) as Hobs.
  destruct (exactness_profile_four_sector_partition D r L)
    as [[H1 H2] | [[H1 H2] | [[H1 H2] | [H1 H2]]]].
  - exfalso. apply Hobs. exact H1.
  - exfalso. apply Hobs. exact H1.
  - left. split; assumption.
  - right. split; assumption.
Qed.

Theorem pce_obstructed_witness_profile_classifier_disjunction
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (y : QLinearFunctional v) :
  pce_obstructed_witness D r y ->
  classify_exactness_profile D r L = ProfileObstructedButDescending
  \/
  classify_exactness_profile D r L = ProfileObstructedAndNonDescending.
Proof.
  intro Hy.
  destruct (pce_obstructed_witness_profile_condition_disjunction D r L y Hy) as [Hc | Hc].
  - left. apply (classify_exactness_profile_obstructed_but_descending_iff D r L). exact Hc.
  - right. apply (classify_exactness_profile_obstructed_and_non_descending_iff D r L). exact Hc.
Qed.

(** ** Part IV: Pairwise incompatibility *)

Theorem pce_exact_underdetermined_incompatible
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (ue ku : QVec u)
    (M : QLinearMap v w) :
  pce_exact_witness D r L x ue M ->
  pce_underdetermined_witness D r L ue ku ->
  False.
Proof.
  intros He Hu.
  pose proof (pce_exact_witness_operational D r L x ue M He) as HopE.
  pose proof (pce_underdetermined_witness_operational D r L ue ku Hu) as HopU.
  pose proof (operational_verdict_witness_unique D r L VerdictExact VerdictUnderdetermined
                HopE HopU) as Heq.
  discriminate Heq.
Qed.

Theorem pce_exact_obstructed_incompatible
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w)
    (y : QLinearFunctional v) :
  pce_exact_witness D r L x u0 M ->
  pce_obstructed_witness D r y ->
  False.
Proof.
  intros He Hy.
  pose proof (pce_exact_witness_operational D r L x u0 M He) as HopE.
  pose proof (pce_obstructed_witness_operational D r L y Hy) as HopO.
  pose proof (operational_verdict_witness_unique D r L VerdictExact VerdictObstructed
                HopE HopO) as Heq.
  discriminate Heq.
Qed.

Theorem pce_underdetermined_obstructed_incompatible
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (u0 k : QVec u)
    (y : QLinearFunctional v) :
  pce_underdetermined_witness D r L u0 k ->
  pce_obstructed_witness D r y ->
  False.
Proof.
  intros Hu Hy.
  pose proof (pce_underdetermined_witness_operational D r L u0 k Hu) as HopU.
  pose proof (pce_obstructed_witness_operational D r L y Hy) as HopO.
  pose proof (operational_verdict_witness_unique D r L VerdictUnderdetermined VerdictObstructed
                HopU HopO) as Heq.
  discriminate Heq.
Qed.

(** ** Part V: Algebraic witness trichotomy *)

Theorem pce_linear_witness_trichotomy
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  (
    exists y : QLinearFunctional v, pce_obstructed_witness D r y
  )
  \/
  (
    exists u0 k : QVec u, pce_underdetermined_witness D r L u0 k
  )
  \/
  (
    exists (x : QVec w) (u0 : QVec u) (M : QLinearMap v w),
      pce_exact_witness D r L x u0 M
  ).
Proof.
  destruct (classify_operational_verdict_witness D r L)
    as [y Hy | u0 k Hrepair Hgauge | u0 M Hrepair Hfact].
  - left. exists y. exact Hy.
  - right. left. exists u0, k. split; assumption.
  - right. right. exists (lmap M r), u0, M.
    split.
    + exact Hrepair.
    + split.
      * exact Hfact.
      * reflexivity.
Qed.

(** ** Part VI: Probes *)

Example pce_exact_witness_repair_value_probe
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w)
    (H : pce_exact_witness D r L x u0 M) :
  lmap L u0 = x.
Proof.
  exact (pce_exact_witness_repair_value D r L x u0 M H).
Qed.

Example pce_underdetermined_witness_ambiguity_probe
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (u0 k : QVec u)
    (H : pce_underdetermined_witness D r L u0 k) :
  repair_fibre D r (vadd u0 k)
  /\
  lmap L (vadd u0 k) <> lmap L u0.
Proof.
  exact (pce_underdetermined_witness_exhibits_ambiguity D r L u0 k H).
Qed.

Example pce_obstructed_witness_operational_probe
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (y : QLinearFunctional v)
    (H : pce_obstructed_witness D r y) :
  operational_verdict_witness D r L VerdictObstructed.
Proof.
  exact (pce_obstructed_witness_operational D r L y H).
Qed.

Example pce_linear_witness_trichotomy_probe
    {u v w : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  (
    exists y : QLinearFunctional v, pce_obstructed_witness D r y
  )
  \/
  (
    exists u0 k : QVec u, pce_underdetermined_witness D r L u0 k
  )
  \/
  (
    exists (x : QVec w) (u0 : QVec u) (M : QLinearMap v w),
      pce_exact_witness D r L x u0 M
  ).
Proof.
  apply pce_linear_witness_trichotomy.
Qed.
