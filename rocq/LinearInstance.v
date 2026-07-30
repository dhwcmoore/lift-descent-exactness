(** * The linear instance and its primitive fibre vocabulary

    This module introduces the primitive data and predicates later
    repair-fibre and claim-fibre theorems (R0, R1) will be stated over:

    [[
      F_r     = u0 + ker D
      L(F_r)  = L(u0) + L(ker D)
    ]]

    It proves nothing about them yet — that is the next unit's job. This
    unit only has to make those two statements *expressible*.

    ** Why a record for the instance

    [LinearInstance nU nV nW] bundles a repair/domain space [nU], a
    residual/constraint space [nV], a claim/codomain space [nW], a
    presentation map [inst_D : QLinearMap nU nV], and a claim map
    [inst_L : QLinearMap nU nW] — the [(U, V, W, D, L)] of the founding
    documents, reusing [QVec]/[QLinearMap] from Commit Unit 1 rather than
    introducing a second representation of vectors, scalars, or linear
    maps.

    The presented residue [r] is deliberately *not* a field of this
    record. It is the argument the later fibre statements are asked
    about ([repair_fibre D r]), not a fixed part of the algebraic
    structure: the same [(D, L)] pair is queried against a varying [r].
    Folding [r] into the record would misrepresent it as part of the
    presentation rather than a query against the presentation.

    ** Why subsets are [QVec n -> Prop]

    [kernel], [repair_fibre], [translate], and [image_set] each need
    only a membership condition. A predicate states exactly that,
    without prematurely committing to lists, finite enumerations, a
    dedicated subset type, bases, ranks, quotients, or decidable
    equality — none of which the affine-fibre identities above require.
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.

(** ** The linear instance *)

Record LinearInstance (nU nV nW : nat) := mkLinearInstance {
  inst_D : QLinearMap nU nV;
  inst_L : QLinearMap nU nW;
}.

Arguments inst_D {nU nV nW}.
Arguments inst_L {nU nV nW}.
Arguments mkLinearInstance {nU nV nW}.

(** ** Kernel

    [ker T = { k : T k = 0 }]. Needed because both R0's displacement
    space and R1's ambiguity space are stated as [ker D] applied to
    [D] and (via [image_set]) to [L]. *)

Definition kernel {n m : nat} (T : QLinearMap n m) : QVec n -> Prop :=
  fun k => lmap T k = zero_vec m.

(** ** Repair fibre

    [repair_fibre T r = T^{-1}(r)], the set of repairs realising a given
    residual [r] through [T]. This is [F_r] itself when [T] is [inst_D]
    and [r] the presented residue. *)

Definition repair_fibre {n m : nat} (T : QLinearMap n m) (r : QVec m) : QVec n -> Prop :=
  fun u => lmap T u = r.

(** ** Translation of a subset

    Needed to state R0's affine normal form [F_r = u0 + ker D] itself:
    its right-hand side is the translate of [ker D] by a repair [u0]. *)

Definition translate {n : nat} (u0 : QVec n) (S : QVec n -> Prop) : QVec n -> Prop :=
  fun u => exists s : QVec n, S s /\ u = vadd u0 s.

(** ** Image of a subset under a linear map

    Needed to state R1's claim-value set [L(F_r)] and ambiguity space
    [L(ker D)]. In this vocabulary, R1 reads:
    [image_set L (repair_fibre D r) = translate (lmap L u0) (image_set L (kernel D))]. *)

Definition image_set {n m : nat} (T : QLinearMap n m) (S : QVec n -> Prop) : QVec m -> Prop :=
  fun w => exists u : QVec n, S u /\ lmap T u = w.

(** ** Equality of subsets

    [QVec n -> Prop] is a function type, so Leibniz equality between two
    subsets would require functional extensionality — not derivable in
    Coq's base logic — to prove from pointwise agreement, exactly the
    situation [QVector.v] avoided for vectors by choosing [Vector.t] over
    finite functions (see that file's representation note). Subsets have
    no such alternative representation available here, so instead of an
    axiom, [same_set] states the equality Phase 1 actually needs: two
    subsets agree on every point. This is what [repair_fibre_translate]
    below concludes with, and it is exactly what a later proof can
    [destruct]/[apply] without ever invoking extensionality. *)

Definition same_set {n : nat} (S T : QVec n -> Prop) : Prop :=
  forall u : QVec n, S u <-> T u.

(** ** R0: the repair-fibre translation theorem

    [F_r = u0 + ker D], stated for an arbitrary linear map [D] rather
    than a full [LinearInstance] — the stronger, more reusable result,
    later instantiable at [inst_D]. *)

Theorem repair_fibre_translate
    {n m : nat}
    (D : QLinearMap n m)
    (r : QVec m)
    (u0 : QVec n)
    (Hu0 : lmap D u0 = r) :
  same_set (repair_fibre D r) (translate u0 (kernel D)).
Proof.
  unfold same_set, repair_fibre, translate, kernel.
  intros u.
  split.
  - intros Hu.
    exists (vsub u u0).
    split.
    + rewrite (lmap_preserves_sub D u u0).
      rewrite Hu, Hu0.
      rewrite vsub_def.
      apply vadd_opp_r.
    + rewrite vsub_def.
      rewrite <- vadd_assoc.
      rewrite (vadd_comm u0 u).
      rewrite vadd_assoc.
      rewrite vadd_opp_r.
      symmetry.
      apply vadd_0_r.
  - intros [k [Hk Hu]].
    rewrite Hu.
    rewrite (lmap_add D u0 k).
    rewrite Hu0, Hk.
    apply vadd_0_r.
Qed.
