(** * The packed linear instance

    This module opens the Phase 7 adapter development. It introduces the
    dependent package an evidence-to-instance adapter is allowed to
    return, and nothing else:

    [[
      PackedLinearInstance  ~  (u, v, w, (D, L), r)
    ]]

    It proves no algebra. Every lemma below is a projection identity,
    established by reduction or by destructing a record.

    ** Why the dimensions are fields rather than parameters

    [LinearInstance nU nV nW] takes its three dimensions as *parameters*,
    so they must be fixed before the instance is mentioned. That is right
    for the theory developed in Units 1 to 34, where the dimensions are
    given and the question is what holds of a presentation at those
    dimensions.

    An adapter cannot work that way. It is handed one piece of evidence
    and must choose the dimensions *from* that evidence — a different
    network, a different observation count, a different claim arity. So
    the dimensions have to be part of the returned value, not of its
    type. That is the only reason this record exists.

    It does not introduce a second representation of vectors, scalars,
    linear maps, or instances: the presentation itself is carried as an
    ordinary [LinearInstance] field, and [packed_D] and [packed_L] are
    definitions that read through it rather than duplicate fields.

    ** Why the residue is a field here but not in [LinearInstance]

    [LinearInstance] deliberately excludes [r], because there the same
    presentation [(D, L)] is queried against a varying residue, and
    folding [r] into the record would misrepresent a query as part of the
    presentation. That reasoning is unchanged and is not contradicted
    here.

    A packed instance is a different object: it is not a presentation
    awaiting queries, it is the single classification request an adapter
    has already committed to. The adapter chose [r] when it read the
    evidence, and the gated classification that follows must be applied
    to that residue and no other. Carrying [r] alongside is exactly what
    stops the classified residue from drifting away from the constructed
    presentation.

    ** What this module does not say

    Nothing here mentions evidence, admissibility, adapters, or
    representation. [PackedLinearInstance] is only the shape of an
    adapter's successful output. Whether any particular evidence is
    faithfully represented by such a package is a declared relation
    supplied later, by the adapter, and is never established by this
    development.
*)

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.

(** ** The packed instance *)

Record PackedLinearInstance : Type := mkPackedLinearInstance {
  packed_dim_U : nat;
  packed_dim_V : nat;
  packed_dim_W : nat;

  packed_linear_instance :
    LinearInstance packed_dim_U packed_dim_V packed_dim_W;

  packed_r :
    QVec packed_dim_V
}.

(** ** Derived maps

    Read through the contained [LinearInstance] rather than storing the
    two maps again. *)

Definition packed_D
    (I : PackedLinearInstance)
    : QLinearMap (packed_dim_U I) (packed_dim_V I) :=
  inst_D (packed_linear_instance I).

Definition packed_L
    (I : PackedLinearInstance)
    : QLinearMap (packed_dim_U I) (packed_dim_W I) :=
  inst_L (packed_linear_instance I).

(** ** Packing

    The one way to build a packed instance from an already-dimensioned
    presentation together with the residue to be classified. *)

Definition pack_instance
    {u v w : nat}
    (I : LinearInstance u v w)
    (r : QVec v)
    : PackedLinearInstance :=
  mkPackedLinearInstance u v w I r.

(** ** Projection identities

    These fix the packing conventions, so that a later unit cannot
    silently transpose the residue and the presentation, or read a claim
    map where a presentation map was meant. *)

Lemma pack_instance_linear_roundtrip
    {u v w : nat}
    (I : LinearInstance u v w)
    (r : QVec v) :
  packed_linear_instance (pack_instance I r) = I.
Proof. reflexivity. Qed.

Lemma pack_instance_residue
    {u v w : nat}
    (I : LinearInstance u v w)
    (r : QVec v) :
  packed_r (pack_instance I r) = r.
Proof. reflexivity. Qed.

Lemma pack_instance_D
    {u v w : nat}
    (I : LinearInstance u v w)
    (r : QVec v) :
  packed_D (pack_instance I r) = inst_D I.
Proof. reflexivity. Qed.

Lemma pack_instance_L
    {u v w : nat}
    (I : LinearInstance u v w)
    (r : QVec v) :
  packed_L (pack_instance I r) = inst_L I.
Proof. reflexivity. Qed.

(** The converse reconstruction: a packed instance is recovered by
    repacking its own presentation and residue, so the record carries no
    information beyond those two together with its dimensions. *)

Lemma packed_instance_eta
    (I : PackedLinearInstance) :
  pack_instance
    (packed_linear_instance I)
    (packed_r I)
  = I.
Proof. destruct I. reflexivity. Qed.
