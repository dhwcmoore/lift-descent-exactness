(** * Cochain/Lifting Instantiation

    ROC's finite rational cochain repair problem

    [C^0 --delta0--> C^1,  r : C^1]

    is exactly the lifting-only case of the core lift-descent theory: a
    ROC repair is a [repair_fibre] point, and a ROC cycle certificate —
    after currying its pairing with [C^1] into a [QLinearFunctional] —
    is exactly a [separator_witness]. This file does not import ROC,
    reuse its raw-[Q]/[Qeq]/tuple representation, or reproduce its
    concrete four-cycle instance; "ROC cycle" here always means a cycle
    already translated into a [QLinearFunctional nC1].

    The embedding uses the zero-dimensional claim space [W = 0] and the
    unique map [C^0 -> 0], since ROC's lifting-only formulation carries
    no independent claim output. Descent is then automatically exact,
    so only two of the four exactness-profile sectors and two of the
    three operational verdicts are reachable. [VerdictExact] in this
    embedding records only that a repair exists and that the vacuous
    zero-dimensional claim descends — it asserts no substantive ROC
    claim value. *)

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

Open Scope Qc_scope.

(** ** Part I: The zero-dimensional claim *)

Definition cochain_zero_claim_map
    (n : nat)
    : QLinearMap n 0.
Proof.
  refine {|
    lmap := fun _ => zero_vec 0;
    lmap_add := _;
    lmap_scale := _
  |}.
  - intros x y. reflexivity.
  - intros q x. reflexivity.
Defined.

Definition cochain_lifting_instance
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    : LinearInstance nC0 nC1 0 :=
  mkLinearInstance delta0 (cochain_zero_claim_map nC0).

(** ** Part II: ROC repair vocabulary *)

Definition roc_repair
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (b : QVec nC0)
    : Prop :=
  lmap delta0 b = r.

Definition roc_repairable
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    : Prop :=
  exists b : QVec nC0,
    roc_repair delta0 r b.

Definition roc_obstructed
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    : Prop :=
  ~ roc_repairable delta0 r.

(** ** Part III: ROC cycle-functional vocabulary *)

Definition roc_cycle
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (y : QLinearFunctional nC1)
    : Prop :=
  forall b : QVec nC0,
    lmap y (lmap delta0 b) = zero_vec 1.

Definition roc_cycle_separator
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (y : QLinearFunctional nC1)
    : Prop :=
  roc_cycle delta0 y
  /\
  lmap y r <> zero_vec 1.

(** ** Part IV: Automatic descent exactness *)

Theorem cochain_zero_claim_vanishes_on_kernel
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1) :
  QImagePreimage.vanishes_on_kernel delta0 (cochain_zero_claim_map nC0).
Proof.
  intros k Hk.
  reflexivity.
Qed.

Theorem cochain_zero_claim_factorises
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1) :
  same_lmap
    (cochain_zero_claim_map nC0)
    (precompose delta0 (cochain_zero_claim_map nC1)).
Proof.
  intro x.
  reflexivity.
Qed.

Theorem cochain_zero_claim_descent_obstruction_zero
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1) :
  descent_obstruction_zero delta0 (cochain_zero_claim_map nC0).
Proof.
  exists (cochain_zero_claim_map nC1).
  apply cochain_zero_claim_factorises.
Qed.

Theorem cochain_zero_claim_not_descent_obstructed
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1) :
  ~ descent_obstructed delta0 (cochain_zero_claim_map nC0).
Proof.
  unfold descent_obstructed.
  intro Hobs.
  apply Hobs.
  apply cochain_zero_claim_descent_obstruction_zero.
Qed.

Theorem cochain_zero_claim_no_gauge_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1) :
  ~ exists k : QVec nC0,
      gauge_witness delta0 (cochain_zero_claim_map nC0) k.
Proof.
  intros [k [Hk Hne]].
  apply Hne.
  reflexivity.
Qed.

(** ** Part V: Repair and lifting equivalence *)

Theorem roc_repair_iff_repair_fibre
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (b : QVec nC0) :
  roc_repair delta0 r b <-> repair_fibre delta0 r b.
Proof.
  split; intro H; exact H.
Qed.

Theorem roc_repairable_iff_lift_obstruction_zero
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  roc_repairable delta0 r <-> lift_obstruction_zero delta0 r.
Proof.
  split.
  - intros [b Hb]. exists b. exact Hb.
  - intros [b Hb]. exists b. exact Hb.
Qed.

Theorem roc_obstructed_iff_lift_obstructed
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  roc_obstructed delta0 r <-> lift_obstructed delta0 r.
Proof.
  unfold roc_obstructed, lift_obstructed.
  split.
  - intros H Hz.
    apply H.
    apply (roc_repairable_iff_lift_obstruction_zero delta0 r).
    exact Hz.
  - intros H Hr.
    apply H.
    apply (roc_repairable_iff_lift_obstruction_zero delta0 r).
    exact Hr.
Qed.

(** ** Part VI: Cycle and separator equivalence *)

Theorem roc_cycle_separator_iff_separator_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (y : QLinearFunctional nC1) :
  roc_cycle_separator delta0 r y <-> separator_witness delta0 r y.
Proof.
  unfold roc_cycle_separator, roc_cycle, separator_witness.
  split; intros [H1 H2]; split; assumption.
Qed.

Theorem roc_obstructed_iff_cycle_separator_exists
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  roc_obstructed delta0 r
  <->
  exists y : QLinearFunctional nC1, roc_cycle_separator delta0 r y.
Proof.
  rewrite (roc_obstructed_iff_lift_obstructed delta0 r).
  rewrite (lift_obstructed_iff_separator_witness delta0 r).
  split.
  - intros [y Hy]. exists y. apply (roc_cycle_separator_iff_separator_witness delta0 r y). exact Hy.
  - intros [y Hy]. exists y. apply (roc_cycle_separator_iff_separator_witness delta0 r y). exact Hy.
Qed.

(** ** Part VII: Four-sector profile collapse *)

Theorem cochain_lifting_profile_realisable_exact_iff
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  classify_exactness_profile delta0 r (cochain_zero_claim_map nC0)
  = ProfileRealisableExact
  <-> roc_repairable delta0 r.
Proof.
  rewrite (classify_exactness_profile_realisable_exact_iff delta0 r (cochain_zero_claim_map nC0)).
  split.
  - intros [H1 _]. apply (roc_repairable_iff_lift_obstruction_zero delta0 r). exact H1.
  - intro H. split.
    + apply (roc_repairable_iff_lift_obstruction_zero delta0 r). exact H.
    + apply cochain_zero_claim_descent_obstruction_zero.
Qed.

Theorem cochain_lifting_profile_obstructed_but_descending_iff
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  classify_exactness_profile delta0 r (cochain_zero_claim_map nC0)
  = ProfileObstructedButDescending
  <-> roc_obstructed delta0 r.
Proof.
  rewrite (classify_exactness_profile_obstructed_but_descending_iff delta0 r (cochain_zero_claim_map nC0)).
  split.
  - intros [H1 _]. apply (roc_obstructed_iff_lift_obstructed delta0 r). exact H1.
  - intro H. split.
    + apply (roc_obstructed_iff_lift_obstructed delta0 r). exact H.
    + apply cochain_zero_claim_descent_obstruction_zero.
Qed.

Theorem cochain_lifting_profile_not_realisable_underdetermined
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  classify_exactness_profile delta0 r (cochain_zero_claim_map nC0)
  <> ProfileRealisableUnderdetermined.
Proof.
  intro Heq.
  apply (classify_exactness_profile_realisable_underdetermined_iff delta0 r
           (cochain_zero_claim_map nC0)) in Heq.
  destruct Heq as [_ Hobs].
  apply (cochain_zero_claim_not_descent_obstructed delta0).
  exact Hobs.
Qed.

Theorem cochain_lifting_profile_not_obstructed_and_non_descending
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  classify_exactness_profile delta0 r (cochain_zero_claim_map nC0)
  <> ProfileObstructedAndNonDescending.
Proof.
  intro Heq.
  apply (classify_exactness_profile_obstructed_and_non_descending_iff delta0 r
           (cochain_zero_claim_map nC0)) in Heq.
  destruct Heq as [_ Hobs].
  apply (cochain_zero_claim_not_descent_obstructed delta0).
  exact Hobs.
Qed.

Theorem cochain_lifting_profile_dichotomy
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  classify_exactness_profile delta0 r (cochain_zero_claim_map nC0)
  = ProfileRealisableExact
  \/
  classify_exactness_profile delta0 r (cochain_zero_claim_map nC0)
  = ProfileObstructedButDescending.
Proof.
  destruct (exactness_profile_four_sector_partition delta0 r (cochain_zero_claim_map nC0))
    as [[H1 H2] | [[H1 H2] | [[H1 H2] | [H1 H2]]]].
  - left.
    apply (classify_exactness_profile_realisable_exact_iff delta0 r (cochain_zero_claim_map nC0)).
    split; assumption.
  - exfalso. apply (cochain_zero_claim_not_descent_obstructed delta0). exact H2.
  - right.
    apply (classify_exactness_profile_obstructed_but_descending_iff delta0 r
             (cochain_zero_claim_map nC0)).
    split; assumption.
  - exfalso. apply (cochain_zero_claim_not_descent_obstructed delta0). exact H2.
Qed.

(** ** Part VIII: Profile evidence correspondence *)

Theorem roc_repair_gives_realisable_exact_profile_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (b : QVec nC0) :
  roc_repair delta0 r b ->
  exactness_profile_witness delta0 r (cochain_zero_claim_map nC0) ProfileRealisableExact.
Proof.
  intro Hb.
  apply (WitnessProfileRealisableExact delta0 r (cochain_zero_claim_map nC0)
           b (cochain_zero_claim_map nC1)).
  - apply (roc_repair_iff_repair_fibre delta0 r b). exact Hb.
  - apply cochain_zero_claim_factorises.
Qed.

Theorem roc_cycle_separator_gives_obstructed_descending_profile_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (y : QLinearFunctional nC1) :
  roc_cycle_separator delta0 r y ->
  exactness_profile_witness delta0 r (cochain_zero_claim_map nC0) ProfileObstructedButDescending.
Proof.
  intro Hy.
  apply (WitnessProfileObstructedButDescending delta0 r (cochain_zero_claim_map nC0)
           y (cochain_zero_claim_map nC1)).
  - apply (roc_cycle_separator_iff_separator_witness delta0 r y). exact Hy.
  - apply cochain_zero_claim_factorises.
Qed.

Theorem roc_repairable_iff_realisable_exact_profile_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  roc_repairable delta0 r
  <->
  exactness_profile_witness delta0 r (cochain_zero_claim_map nC0) ProfileRealisableExact.
Proof.
  split.
  - intros [b Hb].
    apply (roc_repair_gives_realisable_exact_profile_witness delta0 r b).
    exact Hb.
  - intro H.
    apply (exactness_profile_witness_iff_condition delta0 r (cochain_zero_claim_map nC0)
             ProfileRealisableExact) in H.
    destruct H as [H1 _].
    apply (roc_repairable_iff_lift_obstruction_zero delta0 r).
    exact H1.
Qed.

Theorem roc_obstructed_iff_obstructed_descending_profile_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  roc_obstructed delta0 r
  <->
  exactness_profile_witness delta0 r (cochain_zero_claim_map nC0) ProfileObstructedButDescending.
Proof.
  split.
  - intro H.
    destruct (roc_obstructed_iff_cycle_separator_exists delta0 r) as [Hfwd _].
    destruct (Hfwd H) as [y Hy].
    apply (roc_cycle_separator_gives_obstructed_descending_profile_witness delta0 r y).
    exact Hy.
  - intro H.
    apply (exactness_profile_witness_iff_condition delta0 r (cochain_zero_claim_map nC0)
             ProfileObstructedButDescending) in H.
    destruct H as [H1 _].
    apply (roc_obstructed_iff_lift_obstructed delta0 r).
    exact H1.
Qed.

(** ** Part IX: Operational classifier collapse *)

Theorem cochain_lifting_verdict_exact_iff
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  classify_operational_verdict delta0 r (cochain_zero_claim_map nC0) = VerdictExact
  <-> roc_repairable delta0 r.
Proof.
  rewrite (classify_operational_verdict_exact_iff delta0 r (cochain_zero_claim_map nC0)).
  split.
  - intros [H1 _]. apply (roc_repairable_iff_lift_obstruction_zero delta0 r). exact H1.
  - intro H. split.
    + apply (roc_repairable_iff_lift_obstruction_zero delta0 r). exact H.
    + apply cochain_zero_claim_descent_obstruction_zero.
Qed.

Theorem cochain_lifting_verdict_obstructed_iff
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  classify_operational_verdict delta0 r (cochain_zero_claim_map nC0) = VerdictObstructed
  <-> roc_obstructed delta0 r.
Proof.
  rewrite (classify_operational_verdict_obstructed_iff delta0 r (cochain_zero_claim_map nC0)).
  rewrite (roc_obstructed_iff_lift_obstructed delta0 r).
  split; intro H; exact H.
Qed.

Theorem cochain_lifting_verdict_not_underdetermined
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  classify_operational_verdict delta0 r (cochain_zero_claim_map nC0) <> VerdictUnderdetermined.
Proof.
  intro Heq.
  apply (classify_operational_verdict_underdetermined_iff delta0 r
           (cochain_zero_claim_map nC0)) in Heq.
  destruct Heq as [_ Hobs].
  apply (cochain_zero_claim_not_descent_obstructed delta0).
  exact Hobs.
Qed.

Theorem cochain_lifting_verdict_dichotomy
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  classify_operational_verdict delta0 r (cochain_zero_claim_map nC0) = VerdictExact
  \/
  classify_operational_verdict delta0 r (cochain_zero_claim_map nC0) = VerdictObstructed.
Proof.
  destruct (operational_three_way_trichotomy delta0 r (cochain_zero_claim_map nC0))
    as [Hobs | [[H1 H2] | [H1 H2]]].
  - right.
    apply (classify_operational_verdict_obstructed_iff delta0 r (cochain_zero_claim_map nC0)).
    exact Hobs.
  - exfalso. apply (cochain_zero_claim_not_descent_obstructed delta0). exact H2.
  - left.
    apply (classify_operational_verdict_exact_iff delta0 r (cochain_zero_claim_map nC0)).
    split; assumption.
Qed.

(** ** Part X: Operational evidence correspondence *)

Theorem roc_repair_gives_operational_exact_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (b : QVec nC0) :
  roc_repair delta0 r b ->
  operational_verdict_witness delta0 r (cochain_zero_claim_map nC0) VerdictExact.
Proof.
  intro Hb.
  apply (WitnessExact delta0 r (cochain_zero_claim_map nC0)
           b (cochain_zero_claim_map nC1)).
  - apply (roc_repair_iff_repair_fibre delta0 r b). exact Hb.
  - apply cochain_zero_claim_factorises.
Qed.

Theorem roc_cycle_separator_gives_operational_obstructed_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (y : QLinearFunctional nC1) :
  roc_cycle_separator delta0 r y ->
  operational_verdict_witness delta0 r (cochain_zero_claim_map nC0) VerdictObstructed.
Proof.
  intro Hy.
  apply (WitnessObstructed delta0 r (cochain_zero_claim_map nC0) y).
  apply (roc_cycle_separator_iff_separator_witness delta0 r y).
  exact Hy.
Qed.

Theorem roc_repairable_iff_operational_exact_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  roc_repairable delta0 r
  <->
  operational_verdict_witness delta0 r (cochain_zero_claim_map nC0) VerdictExact.
Proof.
  split.
  - intros [b Hb].
    apply (roc_repair_gives_operational_exact_witness delta0 r b).
    exact Hb.
  - intro H.
    apply (operational_verdict_witness_iff_condition delta0 r (cochain_zero_claim_map nC0)
             VerdictExact) in H.
    destruct H as [H1 _].
    apply (roc_repairable_iff_lift_obstruction_zero delta0 r).
    exact H1.
Qed.

Theorem roc_obstructed_iff_operational_obstructed_witness
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  roc_obstructed delta0 r
  <->
  operational_verdict_witness delta0 r (cochain_zero_claim_map nC0) VerdictObstructed.
Proof.
  split.
  - intro H.
    destruct (roc_obstructed_iff_cycle_separator_exists delta0 r) as [Hfwd _].
    destruct (Hfwd H) as [y Hy].
    apply (roc_cycle_separator_gives_operational_obstructed_witness delta0 r y).
    exact Hy.
  - intro H.
    apply (operational_verdict_witness_iff_condition delta0 r (cochain_zero_claim_map nC0)
             VerdictObstructed) in H.
    apply (roc_obstructed_iff_lift_obstructed delta0 r).
    exact H.
Qed.

(** ** Part XI: Probes *)

Example cochain_zero_claim_map_application_probe
    {n : nat}
    (x : QVec n) :
  lmap (cochain_zero_claim_map n) x = zero_vec 0.
Proof.
  reflexivity.
Qed.

Example roc_repair_profile_witness_probe
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (b : QVec nC0)
    (Hb : roc_repair delta0 r b) :
  exactness_profile_witness delta0 r (cochain_zero_claim_map nC0) ProfileRealisableExact.
Proof.
  apply (roc_repair_gives_realisable_exact_profile_witness delta0 r b Hb).
Qed.

Example roc_cycle_separator_operational_witness_probe
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1)
    (y : QLinearFunctional nC1)
    (Hy : roc_cycle_separator delta0 r y) :
  operational_verdict_witness delta0 r (cochain_zero_claim_map nC0) VerdictObstructed.
Proof.
  apply (roc_cycle_separator_gives_operational_obstructed_witness delta0 r y Hy).
Qed.

Example cochain_lifting_classifiers_probe
    {nC0 nC1 : nat}
    (delta0 : QLinearMap nC0 nC1)
    (r : QVec nC1) :
  (
    classify_exactness_profile delta0 r (cochain_zero_claim_map nC0)
    = ProfileRealisableExact
    \/
    classify_exactness_profile delta0 r (cochain_zero_claim_map nC0)
    = ProfileObstructedButDescending
  )
  /\
  (
    classify_operational_verdict delta0 r (cochain_zero_claim_map nC0)
    = VerdictExact
    \/
    classify_operational_verdict delta0 r (cochain_zero_claim_map nC0)
    = VerdictObstructed
  ).
Proof.
  split.
  - apply cochain_lifting_profile_dichotomy.
  - apply cochain_lifting_verdict_dichotomy.
Qed.
