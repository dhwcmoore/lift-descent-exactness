(** * Linear maps between rational vector spaces

    A [QLinearMap n m] is a map [QVec n -> QVec m] together with proofs
    that it preserves vector addition and scalar multiplication.

    ** Why [lmap_zero] is not a record field

    A map preserving addition and scalar multiplication automatically
    preserves zero: [zero_vec n = vscale 0 x] for any [x] (by
    [vscale_0_l]), so [lmap (zero_vec n) = lmap (vscale 0 x) =
    vscale 0 (lmap x) = zero_vec m] follows from [lmap_scale] alone.
    Including [lmap_zero] as a third record field, alongside [lmap_add]
    and [lmap_scale], would make the record carry a redundant hypothesis
    and would cost one extra proof obligation at every construction site
    for no independent content. It is proved below as [lmap_preserves_zero]
    instead, immediately after the record, so "preservation of zero" is
    still available by name for every [QLinearMap] — just as a derived
    fact rather than an assumed one. Negation- and subtraction-preservation
    are derived the same way, as the Phase 1 specification requires.
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.

Open Scope Qc_scope.

(** ** The linear-map record *)

Record QLinearMap (n m : nat) := mkQLinearMap {
  lmap :> QVec n -> QVec m;
  lmap_add : forall x y : QVec n, lmap (vadd x y) = vadd (lmap x) (lmap y);
  lmap_scale : forall (q : Qc) (x : QVec n), lmap (vscale q x) = vscale q (lmap x);
}.

Arguments lmap {n m}.
Arguments lmap_add {n m}.
Arguments lmap_scale {n m}.

(** ** Derived preservation lemmas *)

(** The proof below instantiates [vscale_0_l] at [x := zero_vec n], but
    this is not a choice of a distinguished or otherwise special
    inhabitant of [QVec n]: [vscale_0_l] already holds for *every*
    [x : QVec n] (proved once, in [QVector.v], for arbitrary [x], with no
    reference to [QLinearMap] at all), so instantiating it at [zero_vec n]
    specifically is exactly as valid — and no more circular — than
    instantiating it at any other vector. [QVec n] is inhabited for every
    [n] regardless (e.g. by [zero_vec n] itself), so no existence
    assumption is smuggled in either. *)
Lemma lmap_preserves_zero {n m : nat} (T : QLinearMap n m) :
  lmap T (zero_vec n) = zero_vec m.
Proof.
  rewrite <- (vscale_0_l (zero_vec n)).
  rewrite (lmap_scale T 0 (zero_vec n)).
  apply vscale_0_l.
Qed.

Lemma lmap_preserves_neg {n m : nat} (T : QLinearMap n m) (x : QVec n) :
  lmap T (vneg x) = vneg (lmap T x).
Proof.
  rewrite <- (vscale_neg_1 x).
  rewrite (lmap_scale T (- (1)) x).
  apply vscale_neg_1.
Qed.

Lemma lmap_preserves_sub {n m : nat} (T : QLinearMap n m) (x y : QVec n) :
  lmap T (vsub x y) = vsub (lmap T x) (lmap T y).
Proof.
  rewrite vsub_def.
  rewrite (lmap_add T x (vneg y)).
  rewrite (lmap_preserves_neg T y).
  symmetry.
  apply vsub_def.
Qed.
