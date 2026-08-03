(** * Admissibility Gate

    PCE checks an admissibility witness before it checks any algebraic
    lift-descent witness. This file formalises that architecture in the
    abstract: an [AdmissibilityGate] over an arbitrary evidence type
    carries only a gate predicate and sound positive/negative witness
    relations — no completeness, no decidability, no evidence compiler,
    no domain policy. Completeness and decidability are strictly
    stronger properties and are therefore kept as separate hypotheses
    ([admissibility_gate_complete], [admissibility_gate_decidable]),
    supplied only where a concrete classification is actually requested.

    The gated verdict type [admissibility_gated_verdict] is deliberately
    two-level — [GatedInadmissible] or [GatedAdmissible] of the
    existing three-constructor [operational_verdict] — rather than a
    flat four-constructor enum. Inadmissibility is a gate on the
    evidence-to-instance construction, not a fourth intrinsic linear
    verdict: [operational_verdict] itself is not modified, and the
    [GatedInadmissible] branch of [gated_verdict_condition] asserts
    only gate failure, with no algebraic content.

    The gate-first classifier [classify_after_admissibility] runs the
    gate decision as its outermost match and calls
    [classify_operational_verdict] only in the positive branch — the
    core classifier is never bound or evaluated independently of the
    gate decision. *)

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QVerdictClassification.

Open Scope Qc_scope.

(** ** Part I: Abstract admissibility evidence *)

Record AdmissibilityGate
    (Evidence PositiveWitness NegativeWitness : Type)
    : Type :=
{
  gate_admissible :
    Evidence -> Prop;

  gate_positive_witness :
    Evidence -> PositiveWitness -> Prop;

  gate_negative_witness :
    Evidence -> NegativeWitness -> Prop;

  gate_positive_sound :
    forall (e : Evidence) (p : PositiveWitness),
      gate_positive_witness e p ->
      gate_admissible e;

  gate_negative_sound :
    forall (e : Evidence) (n : NegativeWitness),
      gate_negative_witness e n ->
      ~ gate_admissible e
}.

Arguments gate_admissible
  {Evidence PositiveWitness NegativeWitness} _ _.

Arguments gate_positive_witness
  {Evidence PositiveWitness NegativeWitness} _ _ _.

Arguments gate_negative_witness
  {Evidence PositiveWitness NegativeWitness} _ _ _.

Arguments gate_positive_sound
  {Evidence PositiveWitness NegativeWitness} _ _ _ _.

Arguments gate_negative_sound
  {Evidence PositiveWitness NegativeWitness} _ _ _ _.

(** ** Part II: Optional completeness and decidability *)

Definition admissibility_gate_positive_complete
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    : Prop :=
  forall e : Evidence,
    gate_admissible G e ->
    exists p : PositiveWitness,
      gate_positive_witness G e p.

Definition admissibility_gate_negative_complete
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    : Prop :=
  forall e : Evidence,
    ~ gate_admissible G e ->
    exists n : NegativeWitness,
      gate_negative_witness G e n.

Definition admissibility_gate_complete
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    : Prop :=
  admissibility_gate_positive_complete G
  /\
  admissibility_gate_negative_complete G.

Definition admissibility_gate_decidable
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    : Type :=
  forall e : Evidence,
    {gate_admissible G e}
    +
    {~ gate_admissible G e}.

(** ** Part III: The two-level verdict type *)

Inductive admissibility_gated_verdict : Type :=
| GatedInadmissible
| GatedAdmissible
    (verdict : operational_verdict).

Definition gated_verdict_condition
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (gated_verdict : admissibility_gated_verdict)
    : Prop :=
  match gated_verdict with
  | GatedInadmissible =>
      ~ gate_admissible G e

  | GatedAdmissible verdict =>
      gate_admissible G e
      /\
      operational_verdict_condition D r L verdict
  end.

(** ** Part IV: Gate-first classification *)

Definition classify_after_admissibility
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    : admissibility_gated_verdict :=
  match decide_gate e with
  | left _ =>
      GatedAdmissible
        (classify_operational_verdict D r L)

  | right _ =>
      GatedInadmissible
  end.

(** ** Part V: Gate-witness consistency and completeness *)

Theorem admissibility_witnesses_incompatible
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (p : PositiveWitness)
    (n : NegativeWitness) :
  gate_positive_witness G e p ->
  gate_negative_witness G e n ->
  False.
Proof.
  intros Hp Hn.
  apply (gate_negative_sound G e n Hn).
  apply (gate_positive_sound G e p Hp).
Qed.

Theorem admissible_iff_positive_witness_exists
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence) :
  admissibility_gate_positive_complete G ->
  (
    gate_admissible G e
    <->
    exists p : PositiveWitness,
      gate_positive_witness G e p
  ).
Proof.
  intro Hcomplete.
  split.
  - intro Ha. apply (Hcomplete e Ha).
  - intros [p Hp]. apply (gate_positive_sound G e p Hp).
Qed.

Theorem inadmissible_iff_negative_witness_exists
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence) :
  admissibility_gate_negative_complete G ->
  (
    ~ gate_admissible G e
    <->
    exists n : NegativeWitness,
      gate_negative_witness G e n
  ).
Proof.
  intro Hcomplete.
  split.
  - intro Hna. apply (Hcomplete e Hna).
  - intros [n Hn]. apply (gate_negative_sound G e n Hn).
Qed.

Theorem admissibility_witness_dichotomy
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence) :
  admissibility_gate_complete G ->
  admissibility_gate_decidable G ->
  (
    exists p : PositiveWitness,
      gate_positive_witness G e p
  )
  \/
  (
    exists n : NegativeWitness,
      gate_negative_witness G e n
  ).
Proof.
  intros [Hpc Hnc] decide_gate.
  destruct (decide_gate e) as [Ha | Hna].
  - left. apply (Hpc e Ha).
  - right. apply (Hnc e Hna).
Qed.

Theorem admissibility_witness_dichotomy_exclusive
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence) :
  ~
  (
    (
      exists p : PositiveWitness,
        gate_positive_witness G e p
    )
    /\
    (
      exists n : NegativeWitness,
        gate_negative_witness G e n
    )
  ).
Proof.
  intros [[p Hp] [n Hn]].
  apply (admissibility_witnesses_incompatible G e p n Hp Hn).
Qed.

(** ** Part VI: Semantic shape of gated outcomes *)

Theorem gated_inadmissible_condition_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  gated_verdict_condition G e D r L GatedInadmissible
  <->
  ~ gate_admissible G e.
Proof.
  split; intro H; exact H.
Qed.

Theorem gated_admissible_condition_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (verdict : operational_verdict) :
  gated_verdict_condition G e D r L (GatedAdmissible verdict)
  <->
  (
    gate_admissible G e
    /\
    operational_verdict_condition D r L verdict
  ).
Proof.
  split; intro H; exact H.
Qed.

Theorem gated_verdict_condition_unique
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (gated1 gated2 : admissibility_gated_verdict) :
  gated_verdict_condition G e D r L gated1 ->
  gated_verdict_condition G e D r L gated2 ->
  gated1 = gated2.
Proof.
  destruct gated1 as [| verdict1]; destruct gated2 as [| verdict2]; simpl.
  - intros _ _. reflexivity.
  - intros Hna Hcond2. exfalso. apply Hna. destruct Hcond2 as [Ha _]. exact Ha.
  - intros Hcond1 Hna. exfalso. apply Hna. destruct Hcond1 as [Ha _]. exact Ha.
  - intros Hcond1 Hcond2.
    destruct Hcond1 as [_ Hc1].
    destruct Hcond2 as [_ Hc2].
    f_equal.
    exact (operational_verdict_condition_unique D r L verdict1 verdict2 Hc1 Hc2).
Qed.

(** ** Part VII: Classifier correctness and characterisation *)

Theorem classify_after_admissibility_condition
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  gated_verdict_condition G e D r L
    (classify_after_admissibility G decide_gate e D r L).
Proof.
  unfold classify_after_admissibility.
  destruct (decide_gate e) as [Ha | Hna].
  - split.
    + exact Ha.
    + apply classify_operational_verdict_condition.
  - exact Hna.
Qed.

Theorem classify_after_admissibility_inadmissible_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_after_admissibility G decide_gate e D r L
  = GatedInadmissible
  <->
  ~ gate_admissible G e.
Proof.
  split.
  - intro Heq.
    pose proof (classify_after_admissibility_condition G decide_gate e D r L) as Hc.
    rewrite Heq in Hc.
    exact Hc.
  - intro Hna.
    apply (gated_verdict_condition_unique G e D r L
             (classify_after_admissibility G decide_gate e D r L)
             GatedInadmissible).
    + apply classify_after_admissibility_condition.
    + exact Hna.
Qed.

Theorem classify_after_admissibility_admissible_iff
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (verdict : operational_verdict) :
  classify_after_admissibility G decide_gate e D r L
  = GatedAdmissible verdict
  <->
  (
    gate_admissible G e
    /\
    classify_operational_verdict D r L = verdict
  ).
Proof.
  split.
  - intro Heq.
    pose proof (classify_after_admissibility_condition G decide_gate e D r L) as Hc.
    rewrite Heq in Hc.
    destruct Hc as [Ha Hcond].
    split.
    + exact Ha.
    + apply (operational_verdict_condition_unique D r L
               (classify_operational_verdict D r L) verdict).
      * apply classify_operational_verdict_condition.
      * exact Hcond.
  - intros [Ha Heqv].
    apply (gated_verdict_condition_unique G e D r L
             (classify_after_admissibility G decide_gate e D r L)
             (GatedAdmissible verdict)).
    + apply classify_after_admissibility_condition.
    + split.
      * exact Ha.
      * rewrite <- Heqv. apply classify_operational_verdict_condition.
Qed.

Theorem classify_after_admissibility_from_positive_witness
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (p : PositiveWitness) :
  gate_positive_witness G e p ->
  classify_after_admissibility G decide_gate e D r L
  = GatedAdmissible
      (classify_operational_verdict D r L).
Proof.
  intro Hp.
  apply (classify_after_admissibility_admissible_iff G decide_gate e D r L
           (classify_operational_verdict D r L)).
  split.
  - apply (gate_positive_sound G e p Hp).
  - reflexivity.
Qed.

Theorem classify_after_admissibility_from_negative_witness
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
  classify_after_admissibility G decide_gate e D r L
  = GatedInadmissible.
Proof.
  intro Hn.
  apply (classify_after_admissibility_inadmissible_iff G decide_gate e D r L).
  apply (gate_negative_sound G e n Hn).
Qed.

Theorem classify_after_admissibility_exists_unique
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  exists! gated_verdict : admissibility_gated_verdict,
    gated_verdict_condition G e D r L gated_verdict.
Proof.
  exists (classify_after_admissibility G decide_gate e D r L).
  split.
  - apply classify_after_admissibility_condition.
  - intros gated2 Hcond2.
    apply (gated_verdict_condition_unique G e D r L
             (classify_after_admissibility G decide_gate e D r L) gated2).
    + apply classify_after_admissibility_condition.
    + exact Hcond2.
Qed.

Theorem classify_after_admissibility_four_way
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_after_admissibility G decide_gate e D r L
  = GatedInadmissible
  \/
  classify_after_admissibility G decide_gate e D r L
  = GatedAdmissible VerdictObstructed
  \/
  classify_after_admissibility G decide_gate e D r L
  = GatedAdmissible VerdictUnderdetermined
  \/
  classify_after_admissibility G decide_gate e D r L
  = GatedAdmissible VerdictExact.
Proof.
  destruct (classify_after_admissibility G decide_gate e D r L) as [| verdict].
  - left. reflexivity.
  - destruct verdict.
    + right. left. reflexivity.
    + right. right. left. reflexivity.
    + right. right. right. reflexivity.
Qed.

(** ** Part VIII: Probes *)

Example admissibility_witnesses_incompatible_probe
    {Evidence PositiveWitness NegativeWitness : Type}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (e : Evidence)
    (p : PositiveWitness)
    (n : NegativeWitness)
    (Hp : gate_positive_witness G e p)
    (Hn : gate_negative_witness G e n) :
  False.
Proof.
  exact (admissibility_witnesses_incompatible G e p n Hp Hn).
Qed.

Example positive_witness_classification_probe
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (p : PositiveWitness)
    (Hp : gate_positive_witness G e p) :
  classify_after_admissibility G decide_gate e D r L
  = GatedAdmissible
      (classify_operational_verdict D r L).
Proof.
  exact (classify_after_admissibility_from_positive_witness
           G decide_gate e D r L p Hp).
Qed.

Example negative_witness_classification_probe
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w)
    (n : NegativeWitness)
    (Hn : gate_negative_witness G e n) :
  classify_after_admissibility G decide_gate e D r L
  = GatedInadmissible.
Proof.
  exact (classify_after_admissibility_from_negative_witness
           G decide_gate e D r L n Hn).
Qed.

Example gated_classifier_four_way_probe
    {Evidence PositiveWitness NegativeWitness : Type}
    {u v w : nat}
    (G : AdmissibilityGate Evidence PositiveWitness NegativeWitness)
    (decide_gate : admissibility_gate_decidable G)
    (e : Evidence)
    (D : QLinearMap u v)
    (r : QVec v)
    (L : QLinearMap u w) :
  classify_after_admissibility G decide_gate e D r L
  = GatedInadmissible
  \/
  classify_after_admissibility G decide_gate e D r L
  = GatedAdmissible VerdictObstructed
  \/
  classify_after_admissibility G decide_gate e D r L
  = GatedAdmissible VerdictUnderdetermined
  \/
  classify_after_admissibility G decide_gate e D r L
  = GatedAdmissible VerdictExact.
Proof.
  apply classify_after_admissibility_four_way.
Qed.
