(** * The abstract evidence adapter

    Unit 35 packaged one complete algebraic classification request. This
    module introduces the partial map that produces such a package from
    evidence, together with the relation under which a successful
    production is judged sound:

    [[
      alpha : E -> option PackedLinearInstance
    ]]

    The evidence type is abstract. Nothing here knows what evidence is,
    how it was parsed, or what domain it came from.

    ** What a successful adaptation means

    [adapt A e = Some I] means the adapter produced the packed instance
    [I] from the evidence [e]. The field [adapt_sound] then yields
    [represents A e I], stated in terms of the relation that adapter
    itself declares.

    ** What an unsuccessful adaptation means

    [adapt A e = None] means only that this adapter did not produce a
    packed instance. It carries no further content. In particular it is
    not a statement that

    - the evidence is inadmissible,
    - an algebraic obstruction is present,
    - the verdict is [VerdictObstructed],
    - no adequate representation of that evidence exists at all,
    - or the evidence is false, incomplete, or defective.

    Construction failure and policy rejection are different events, and
    keeping them apart is the reason this module stays independent of
    the gate. Relating the two is deliberately left to Unit 37, and even
    there the correspondence is optional rather than forced.

    ** What [represents] does not claim

    This development never says what [represents] means. The relation is
    supplied by a concrete adapter specification, which thereby takes
    responsibility for it. Accordingly [adapt_sound] establishes nothing
    about

    - sensor accuracy or calibration,
    - physical truth,
    - completeness of the evidence,
    - uniqueness or correctness of the chosen model,
    - correctness of parsing or ingestion,
    - or real-world safety.

    It states exactly one thing: a result the adapter returned satisfies
    the relation that same adapter declared. Assurance obtained this way
    is relative to that declaration and to nothing else.

    ** Independence from the gate and the classifier

    This module imports only Unit 35. It mentions no gate, no witness,
    no verdict, and no classification. That keeps the dependency running
    one way — evidence, then optional package, then gating, then the
    proof-carrying exactness layer — and stops the algebraic theory from
    appearing to certify that concrete evidence was represented
    faithfully.
*)

From LiftDescent Require Import QPackedLinearInstance.

(** ** The adapter *)

Record EvidenceAdapter (Evidence : Type) : Type := {
  adapt :
    Evidence -> option PackedLinearInstance;

  represents :
    Evidence -> PackedLinearInstance -> Prop;

  adapt_sound :
    forall (e : Evidence) (I : PackedLinearInstance),
      adapt e = Some I ->
      represents e I
}.

Arguments adapt {Evidence} _ _.
Arguments represents {Evidence} _ _ _.
Arguments adapt_sound {Evidence} _ _ _ _.
