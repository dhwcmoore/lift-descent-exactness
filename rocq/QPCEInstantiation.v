(** * PCE Instantiation

    This file composes Unit 32's abstract admissibility gate with
    Unit 33's three algebraic witness predicates into the complete PCE
    gated witness relation [pce_gated_witness], indexed by the existing
    two-level [admissibility_gated_verdict]. It proves this relation is
    sound unconditionally, complete under explicit gate completeness,
    agrees with the gate-first classifier [classify_after_admissibility],
    and yields a complete four-way witness partition.

    The architectural order is preserved throughout: negative gate
    evidence produces [GatedInadmissible] with no algebraic content;
    positive gate evidence, paired with exactly one Unit 33 witness,
    produces [GatedAdmissible] of the corresponding [operational_verdict].
    No theorem here unfolds [classify_operational_verdict],
    [classify_exactness_profile], or [classify_after_admissibility] —
    all classifier-level results route through the sealed condition,
    uniqueness, and characterisation theorems of Units 21, 22, 32, and
    33. Supplied witness data (gate witnesses, repairs, factor maps,
    gauge directions, separators, claimed values) is retained directly
    throughout; nothing is regenerated through completeness where a
    particular witness was already supplied. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QLinearFunctional.
From LiftDescent Require Import QVerdictClassification.
From LiftDescent Require Import QExactnessProfile.
From LiftDescent Require Import QCanonicalValue.
From LiftDescent Require Import QAdmissibilityGate.
From LiftDescent Require Import QPCEWitnessPredicates.

Open Scope Qc_scope.

(** ** Part I: Gated PCE witness relation *)

Inductive pce_gated_witness
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    : admissibility_gated_verdict -> Prop :=

| PCEGatedInadmissible :
    forall n : NegativeWitness,
      gate_negative_witness G e n ->
      pce_gated_witness G e D r L GatedInadmissible

| PCEGatedObstructed :
    forall (p : PositiveWitness) (y : QLinearFunctional v),
      gate_positive_witness G e p ->
      pce_obstructed_witness D r y ->
      pce_gated_witness G e D r L (GatedAdmissible VerdictObstructed)

| PCEGatedUnderdetermined :
    forall (p : PositiveWitness) (u0 k : QVec u),
      gate_positive_witness G e p ->
      pce_underdetermined_witness D r L u0 k ->
      pce_gated_witness G e D r L (GatedAdmissible VerdictUnderdetermined)

| PCEGatedExact :
    forall (p : PositiveWitness) (x : QVec w) (u0 : QVec u) (M : QLinearMap v w),
      gate_positive_witness G e p ->
      pce_exact_witness D r L x u0 M ->
      pce_gated_witness G e D r L (GatedAdmissible VerdictExact).

(** ** Part II: Shape of indexed witnesses *)

Theorem pce_gated_inadmissible_witness_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  pce_gated_witness G e D r L GatedInadmissible
  <->
  exists n : NegativeWitness, gate_negative_witness G e n.
Proof.
  split.
  - intro H.
    inversion H as [n Hn | | | ].
    exists n. exact Hn.
  - intros [n Hn].
    exact (PCEGatedInadmissible G e D r L n Hn).
Qed.

Theorem pce_gated_admissible_witness_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (verdict : operational_verdict) :
  pce_gated_witness G e D r L (GatedAdmissible verdict)
  <->
  exists p : PositiveWitness,
    gate_positive_witness G e p
    /\
    operational_verdict_witness D r L verdict.
Proof.
  destruct verdict.
  - split.
    + intro H.
      inversion H as [ | p y Hp Hy | | ].
      exists p.
      split.
      * exact Hp.
      * apply (pce_obstructed_witness_operational D r L y). exact Hy.
    + intros [p [Hp Hop]].
      apply (operational_obstructed_witness_iff_pce_obstructed_witness_exists D r L) in Hop.
      destruct Hop as [y Hy].
      exact (PCEGatedObstructed G e D r L p y Hp Hy).
  - split.
    + intro H.
      inversion H as [ | | p u0 k Hp Hu | ].
      exists p.
      split.
      * exact Hp.
      * apply (pce_underdetermined_witness_operational D r L u0 k). exact Hu.
    + intros [p [Hp Hop]].
      apply (operational_underdetermined_witness_iff_pce_underdetermined_witness_exists D r L)
        in Hop.
      destruct Hop as [u0 [k Hu]].
      exact (PCEGatedUnderdetermined G e D r L p u0 k Hp Hu).
  - split.
    + intro H.
      inversion H as [ | | | p x u0 M Hp He].
      exists p.
      split.
      * exact Hp.
      * apply (pce_exact_witness_operational D r L x u0 M). exact He.
    + intros [p [Hp Hop]].
      apply (operational_exact_witness_iff_pce_exact_witness_exists D r L) in Hop.
      destruct Hop as [x [u0 [M He]]].
      exact (PCEGatedExact G e D r L p x u0 M Hp He).
Qed.

(** ** Part III: Soundness and completeness *)

Theorem pce_gated_witness_sound
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (gated_verdict : admissibility_gated_verdict) :
  pce_gated_witness G e D r L gated_verdict ->
  gated_verdict_condition G e D r L gated_verdict.
Proof.
  intro H.
  destruct H as [n Hn | p y Hp Hy | p u0 k Hp Hu | p x u0 M Hp He].
  - exact (gate_negative_sound G e n Hn).
  - split.
    + exact (gate_positive_sound G e p Hp).
    + apply (operational_verdict_witness_iff_condition D r L VerdictObstructed).
      apply (pce_obstructed_witness_operational D r L y). exact Hy.
  - split.
    + exact (gate_positive_sound G e p Hp).
    + apply (operational_verdict_witness_iff_condition D r L VerdictUnderdetermined).
      apply (pce_underdetermined_witness_operational D r L u0 k). exact Hu.
  - split.
    + exact (gate_positive_sound G e p Hp).
    + apply (operational_verdict_witness_iff_condition D r L VerdictExact).
      apply (pce_exact_witness_operational D r L x u0 M). exact He.
Qed.

Theorem pce_gated_witness_complete
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (gated_verdict : admissibility_gated_verdict) :
  admissibility_gate_complete G ->
  gated_verdict_condition G e D r L gated_verdict ->
  pce_gated_witness G e D r L gated_verdict.
Proof.
  intros [Hpc Hnc] Hcond.
  destruct gated_verdict as [| verdict].
  - destruct (Hnc e Hcond) as [n Hn].
    exact (PCEGatedInadmissible G e D r L n Hn).
  - destruct Hcond as [Ha Hop].
    destruct (Hpc e Ha) as [p Hp].
    apply (pce_gated_admissible_witness_iff G e D r L verdict).
    exists p.
    split.
    + exact Hp.
    + apply (operational_verdict_witness_iff_condition D r L verdict).
      exact Hop.
Qed.

Theorem pce_gated_witness_iff_condition
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (gated_verdict : admissibility_gated_verdict) :
  admissibility_gate_complete G ->
  (
    pce_gated_witness G e D r L gated_verdict
    <->
    gated_verdict_condition G e D r L gated_verdict
  ).
Proof.
  intro Hcomplete.
  split.
  - apply pce_gated_witness_sound.
  - apply (pce_gated_witness_complete G e D r L gated_verdict Hcomplete).
Qed.

Theorem pce_gated_witness_verdict_unique
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (gated1 gated2 : admissibility_gated_verdict) :
  pce_gated_witness G e D r L gated1 ->
  pce_gated_witness G e D r L gated2 ->
  gated1 = gated2.
Proof.
  intros H1 H2.
  apply (gated_verdict_condition_unique G e D r L gated1 gated2).
  - apply (pce_gated_witness_sound G e D r L gated1). exact H1.
  - apply (pce_gated_witness_sound G e D r L gated2). exact H2.
Qed.

(** ** Part IV: Correspondence with the gate-first classifier *)

Theorem classify_after_admissibility_pce_gated_witness
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  admissibility_gate_complete G ->
  pce_gated_witness G e D r L
    (classify_after_admissibility G decide_gate e D r L).
Proof.
  intro Hcomplete.
  apply (pce_gated_witness_complete G e D r L
           (classify_after_admissibility G decide_gate e D r L) Hcomplete).
  apply classify_after_admissibility_condition.
Qed.

Theorem pce_gated_witness_iff_classified
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (gated_verdict : admissibility_gated_verdict) :
  admissibility_gate_complete G ->
  (
    pce_gated_witness G e D r L gated_verdict
    <->
    classify_after_admissibility G decide_gate e D r L = gated_verdict
  ).
Proof.
  intro Hcomplete.
  split.
  - intro H.
    apply (pce_gated_witness_verdict_unique G e D r L
             (classify_after_admissibility G decide_gate e D r L) gated_verdict).
    + apply (classify_after_admissibility_pce_gated_witness G decide_gate e D r L Hcomplete).
    + exact H.
  - intro Heq.
    rewrite <- Heq.
    apply (classify_after_admissibility_pce_gated_witness G decide_gate e D r L Hcomplete).
Qed.

Theorem pce_gated_witness_exists_unique
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  admissibility_gate_complete G ->
  exists! gated_verdict : admissibility_gated_verdict,
    pce_gated_witness G e D r L gated_verdict.
Proof.
  intro Hcomplete.
  exists (classify_after_admissibility G decide_gate e D r L).
  split.
  - apply (classify_after_admissibility_pce_gated_witness G decide_gate e D r L Hcomplete).
  - intros gated2 H2.
    apply (pce_gated_witness_verdict_unique G e D r L
             (classify_after_admissibility G decide_gate e D r L) gated2).
    + apply (classify_after_admissibility_pce_gated_witness G decide_gate e D r L Hcomplete).
    + exact H2.
Qed.

(** ** Part V: Four classifier characterisations *)

Theorem classify_after_admissibility_pce_inadmissible_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  admissibility_gate_complete G ->
  (
    classify_after_admissibility G decide_gate e D r L = GatedInadmissible
    <->
    exists n : NegativeWitness, gate_negative_witness G e n
  ).
Proof.
  intro Hcomplete.
  rewrite <- (pce_gated_witness_iff_classified G decide_gate e D r L GatedInadmissible Hcomplete).
  apply (pce_gated_inadmissible_witness_iff G e D r L).
Qed.

Theorem classify_after_admissibility_pce_obstructed_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  admissibility_gate_complete G ->
  (
    classify_after_admissibility G decide_gate e D r L
    = GatedAdmissible VerdictObstructed
    <->
    exists (p : PositiveWitness) (y : QLinearFunctional v),
      gate_positive_witness G e p /\ pce_obstructed_witness D r y
  ).
Proof.
  intro Hcomplete.
  split.
  - intro Heq.
    assert (Hg : pce_gated_witness G e D r L (GatedAdmissible VerdictObstructed)).
    { apply (pce_gated_witness_iff_classified G decide_gate e D r L
               (GatedAdmissible VerdictObstructed) Hcomplete).
      exact Heq. }
    apply (pce_gated_admissible_witness_iff G e D r L VerdictObstructed) in Hg.
    destruct Hg as [p [Hp Hop]].
    apply (operational_obstructed_witness_iff_pce_obstructed_witness_exists D r L) in Hop.
    destruct Hop as [y Hy].
    exists p, y.
    split; assumption.
  - intros [p [y [Hp Hy]]].
    apply (pce_gated_witness_iff_classified G decide_gate e D r L
             (GatedAdmissible VerdictObstructed) Hcomplete).
    apply (pce_gated_admissible_witness_iff G e D r L VerdictObstructed).
    exists p.
    split.
    + exact Hp.
    + apply (operational_obstructed_witness_iff_pce_obstructed_witness_exists D r L).
      exists y. exact Hy.
Qed.

Theorem classify_after_admissibility_pce_underdetermined_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  admissibility_gate_complete G ->
  (
    classify_after_admissibility G decide_gate e D r L
    = GatedAdmissible VerdictUnderdetermined
    <->
    exists (p : PositiveWitness) (u0 k : QVec u),
      gate_positive_witness G e p /\ pce_underdetermined_witness D r L u0 k
  ).
Proof.
  intro Hcomplete.
  split.
  - intro Heq.
    assert (Hg : pce_gated_witness G e D r L (GatedAdmissible VerdictUnderdetermined)).
    { apply (pce_gated_witness_iff_classified G decide_gate e D r L
               (GatedAdmissible VerdictUnderdetermined) Hcomplete).
      exact Heq. }
    apply (pce_gated_admissible_witness_iff G e D r L VerdictUnderdetermined) in Hg.
    destruct Hg as [p [Hp Hop]].
    apply (operational_underdetermined_witness_iff_pce_underdetermined_witness_exists D r L)
      in Hop.
    destruct Hop as [u0 [k Hu]].
    exists p, u0, k.
    split; assumption.
  - intros [p [u0 [k [Hp Hu]]]].
    apply (pce_gated_witness_iff_classified G decide_gate e D r L
             (GatedAdmissible VerdictUnderdetermined) Hcomplete).
    apply (pce_gated_admissible_witness_iff G e D r L VerdictUnderdetermined).
    exists p.
    split.
    + exact Hp.
    + apply (operational_underdetermined_witness_iff_pce_underdetermined_witness_exists D r L).
      exists u0, k. exact Hu.
Qed.

Theorem classify_after_admissibility_pce_exact_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  admissibility_gate_complete G ->
  (
    classify_after_admissibility G decide_gate e D r L
    = GatedAdmissible VerdictExact
    <->
    exists (p : PositiveWitness) (x : QVec w) (u0 : QVec u) (M : QLinearMap v w),
      gate_positive_witness G e p /\ pce_exact_witness D r L x u0 M
  ).
Proof.
  intro Hcomplete.
  split.
  - intro Heq.
    assert (Hg : pce_gated_witness G e D r L (GatedAdmissible VerdictExact)).
    { apply (pce_gated_witness_iff_classified G decide_gate e D r L
               (GatedAdmissible VerdictExact) Hcomplete).
      exact Heq. }
    apply (pce_gated_admissible_witness_iff G e D r L VerdictExact) in Hg.
    destruct Hg as [p [Hp Hop]].
    apply (operational_exact_witness_iff_pce_exact_witness_exists D r L) in Hop.
    destruct Hop as [x [u0 [M He]]].
    exists p, x, u0, M.
    split; assumption.
  - intros [p [x [u0 [M [Hp He]]]]].
    apply (pce_gated_witness_iff_classified G decide_gate e D r L
             (GatedAdmissible VerdictExact) Hcomplete).
    apply (pce_gated_admissible_witness_iff G e D r L VerdictExact).
    exists p.
    split.
    + exact Hp.
    + apply (operational_exact_witness_iff_pce_exact_witness_exists D r L).
      exists x, u0, M. exact He.
Qed.

(** ** Part VI: Direct classification from supplied evidence *)

Theorem pce_negative_witness_classified_inadmissible
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (n : NegativeWitness) :
  gate_negative_witness G e n ->
  classify_after_admissibility G decide_gate e D r L = GatedInadmissible.
Proof.
  intro Hn.
  exact (classify_after_admissibility_from_negative_witness G decide_gate e D r L n Hn).
Qed.

Theorem pce_positive_obstructed_witness_classified
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (p : PositiveWitness)
    (y : QLinearFunctional v) :
  gate_positive_witness G e p ->
  pce_obstructed_witness D r y ->
  classify_after_admissibility G decide_gate e D r L = GatedAdmissible VerdictObstructed.
Proof.
  intros Hp Hy.
  apply (classify_after_admissibility_admissible_iff G decide_gate e D r L VerdictObstructed).
  split.
  - exact (gate_positive_sound G e p Hp).
  - apply (pce_obstructed_witness_exists_iff_classified_operational D r L).
    exists y. exact Hy.
Qed.

Theorem pce_positive_underdetermined_witness_classified
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (p : PositiveWitness)
    (u0 k : QVec u) :
  gate_positive_witness G e p ->
  pce_underdetermined_witness D r L u0 k ->
  classify_after_admissibility G decide_gate e D r L = GatedAdmissible VerdictUnderdetermined.
Proof.
  intros Hp Hu.
  apply (classify_after_admissibility_admissible_iff G decide_gate e D r L VerdictUnderdetermined).
  split.
  - exact (gate_positive_sound G e p Hp).
  - apply (pce_underdetermined_witness_exists_iff_classified_operational D r L).
    exists u0, k. exact Hu.
Qed.

Theorem pce_positive_exact_witness_classified
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (p : PositiveWitness)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w) :
  gate_positive_witness G e p ->
  pce_exact_witness D r L x u0 M ->
  classify_after_admissibility G decide_gate e D r L = GatedAdmissible VerdictExact.
Proof.
  intros Hp He.
  apply (classify_after_admissibility_admissible_iff G decide_gate e D r L VerdictExact).
  split.
  - exact (gate_positive_sound G e p Hp).
  - apply (pce_exact_witness_classified_operational D r L x u0 M). exact He.
Qed.

(** ** Part VII: Full-profile interpretation *)

Theorem pce_gated_exact_profile
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  pce_gated_witness G e D r L (GatedAdmissible VerdictExact) ->
  exactness_profile_witness D r L ProfileRealisableExact.
Proof.
  intro H.
  inversion H as [ | | | p x u0 M Hp He].
  apply (pce_exact_witness_profile D r L x u0 M).
  exact He.
Qed.

Theorem pce_gated_underdetermined_profile
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  pce_gated_witness G e D r L (GatedAdmissible VerdictUnderdetermined) ->
  exactness_profile_witness D r L ProfileRealisableUnderdetermined.
Proof.
  intro H.
  inversion H as [ | | p u0 k Hp Hu | ].
  apply (pce_underdetermined_witness_profile D r L u0 k).
  exact Hu.
Qed.

Theorem pce_gated_obstructed_profile_condition_disjunction
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  pce_gated_witness G e D r L (GatedAdmissible VerdictObstructed) ->
  exactness_profile_condition D r L ProfileObstructedButDescending
  \/
  exactness_profile_condition D r L ProfileObstructedAndNonDescending.
Proof.
  intro H.
  inversion H as [ | p y Hp Hy | | ].
  apply (pce_obstructed_witness_profile_condition_disjunction D r L y).
  exact Hy.
Qed.

Theorem pce_gated_obstructed_profile_classifier_disjunction
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  pce_gated_witness G e D r L (GatedAdmissible VerdictObstructed) ->
  classify_exactness_profile D r L = ProfileObstructedButDescending
  \/
  classify_exactness_profile D r L = ProfileObstructedAndNonDescending.
Proof.
  intro H.
  inversion H as [ | p y Hp Hy | | ].
  apply (pce_obstructed_witness_profile_classifier_disjunction D r L y).
  exact Hy.
Qed.

(** ** Part VIII: Canonical exact value *)

Theorem pce_gated_exact_value_witnessed_unique
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  pce_gated_witness G e D r L (GatedAdmissible VerdictExact) ->
  exists (p : PositiveWitness) (x : QVec w) (u0 : QVec u) (M : QLinearMap v w),
    gate_positive_witness G e p
    /\
    pce_exact_witness D r L x u0 M
    /\
    lmap L u0 = x
    /\
    exact_value D r L x
    /\
    (forall x' : QVec w, exact_value D r L x' -> x' = x).
Proof.
  intro H.
  inversion H as [ | | | p x u0 M Hp He].
  pose proof (pce_exact_witness_repair_value D r L x u0 M He) as Hrv.
  pose proof (pce_exact_witness_exact_value D r L x u0 M He) as Hxv.
  pose proof He as [Hrepair _].
  exists p, x, u0, M.
  split.
  - exact Hp.
  - split.
    + exact He.
    + split.
      * exact Hrv.
      * split.
        -- exact Hxv.
        -- intros x' Hx'.
           symmetry.
           exact (exact_value_unique_on_nonempty_fibre D r L u0 Hrepair x x' Hxv Hx').
Qed.

(** ** Part IX: Complete four-way witness partition *)

Theorem pce_gated_four_way_witness_partition
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  admissibility_gate_complete G ->
  (
    exists n : NegativeWitness, gate_negative_witness G e n
  )
  \/
  (
    exists (p : PositiveWitness) (y : QLinearFunctional v),
      gate_positive_witness G e p /\ pce_obstructed_witness D r y
  )
  \/
  (
    exists (p : PositiveWitness) (u0 k : QVec u),
      gate_positive_witness G e p /\ pce_underdetermined_witness D r L u0 k
  )
  \/
  (
    exists (p : PositiveWitness) (x : QVec w) (u0 : QVec u) (M : QLinearMap v w),
      gate_positive_witness G e p /\ pce_exact_witness D r L x u0 M
  ).
Proof.
  intro Hcomplete.
  pose proof (classify_after_admissibility_pce_gated_witness G decide_gate e D r L Hcomplete)
    as Hg.
  destruct Hg as [n Hn | p y Hp Hy | p u0 k Hp Hu | p x u0 M Hp He].
  - left. exists n. exact Hn.
  - right. left. exists p, y. split; assumption.
  - right. right. left. exists p, u0, k. split; assumption.
  - right. right. right. exists p, x, u0, M. split; assumption.
Qed.

(** ** Part X: Probes *)

Example pce_gated_inadmissible_witness_probe
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (n : NegativeWitness)
    (Hn : gate_negative_witness G e n) :
  pce_gated_witness G e D r L GatedInadmissible.
Proof.
  exact (PCEGatedInadmissible G e D r L n Hn).
Qed.

Example pce_positive_exact_classification_probe
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (p : PositiveWitness)
    (x : QVec w)
    (u0 : QVec u)
    (M : QLinearMap v w)
    (Hp : gate_positive_witness G e p)
    (Hexact : pce_exact_witness D r L x u0 M) :
  classify_after_admissibility G decide_gate e D r L = GatedAdmissible VerdictExact.
Proof.
  exact (pce_positive_exact_witness_classified G decide_gate e D r L p x u0 M Hp Hexact).
Qed.

Example pce_gated_exact_value_probe
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (H : pce_gated_witness G e D r L (GatedAdmissible VerdictExact)) :
  exists (p : PositiveWitness) (x : QVec w) (u0 : QVec u) (M : QLinearMap v w),
    gate_positive_witness G e p
    /\
    pce_exact_witness D r L x u0 M
    /\
    lmap L u0 = x
    /\
    exact_value D r L x
    /\
    (forall x' : QVec w, exact_value D r L x' -> x' = x).
Proof.
  apply (pce_gated_exact_value_witnessed_unique G e D r L).
  exact H.
Qed.

Example pce_gated_four_way_partition_probe
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (complete_gate : admissibility_gate_complete G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  (
    exists n : NegativeWitness, gate_negative_witness G e n
  )
  \/
  (
    exists (p : PositiveWitness) (y : QLinearFunctional v),
      gate_positive_witness G e p /\ pce_obstructed_witness D r y
  )
  \/
  (
    exists (p : PositiveWitness) (u0 k : QVec u),
      gate_positive_witness G e p /\ pce_underdetermined_witness D r L u0 k
  )
  \/
  (
    exists (p : PositiveWitness) (x : QVec w) (u0 : QVec u) (M : QLinearMap v w),
      gate_positive_witness G e p /\ pce_exact_witness D r L x u0 M
  ).
Proof.
  apply (pce_gated_four_way_witness_partition G decide_gate e D r L).
  exact complete_gate.
Qed.
