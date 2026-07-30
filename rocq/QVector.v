(** * Rational vectors

    This module fixes the representation of [U], [V], [W] as
    finite-dimensional rational vector spaces, [QVec n], for the entire
    Phase 1 development and everything built on it.

    Two representation choices are made here, both explained below because
    later phases (repair fibres, claim fibres, and eventually cokernel and
    presentation-morphism theory) depend on their consequences.

    ** Choice 1: scalars are [Qc], not raw [Q]

    Coq's [QArith.QArith_base.Q] represents a rational as a numerator over
    a denominator with no canonical-form requirement: [1#2] and [2#4] are
    distinct [Q] values under Leibniz equality [=], even though they denote
    the same rational number. [Q]'s ring/field structure (e.g.
    [Qplus_comm]) is stated for the *setoid* equality [==], not [=]. Using
    raw [Q] as the scalar type would force every vector-level equality in
    this development — including the sequel's [u = u0 + k] and
    [w = L u0 + L k] — to be restated with a custom setoid instead of [=],
    and every rewrite to go through [setoid_rewrite]. That is a large,
    silent deviation from the plain-equality theorem statements the rest
    of Phase 1 is written against.

    [QArith.Qcanon.Qc] avoids this: it is [Q] refined by a canonical-form
    side condition ([Qcmake this canon : Qred this = this]), so each
    rational number has exactly one [Qc] representative and Leibniz
    equality on [Qc] coincides with equality of the rational numbers
    themselves. Its ring/field instance ([Qcfield]) is registered for [=],
    not a separate [==]. [Qc] therefore lets every later theorem use plain
    [=] at face value, with [ring]/[field] available directly on that
    equality.

    ** Choice 2: vectors are [Vector.t Qc n], not functions or lists

    Three alternatives were considered:

    - [Fin.t n -> Qc] (finite functions): two functions are Leibniz-equal
      only via functional extensionality, which is not derivable in Coq's
      base logic and would have to be assumed as an axiom. Every additive
      or scalar law proved below, and every set-equality in the repair-
      and claim-fibre theorems that follow, would then rest on that axiom.
    - [list Qc] with a side condition [length l = n]: equality of two such
      dependent pairs needs proof-irrelevance of the length component. It
      is derivable (nat has decidable equality, so [Eqdep_dec] applies),
      but it adds a layer of indirection for no benefit here, and the type
      no longer statically distinguishes vectors of different dimension.
    - matrices with one column: unnecessary generality — [D] and [L] are
      kept as abstract linear maps in Phase 1 (see [QLinearMap.v]), not
      matrices, so there is no reason to model vectors via matrices yet.

    [Vector.t Qc n] is an ordinary inductive type (built from [nil] and
    [cons]), so Leibniz equality between two vectors is provable by
    structural induction with no extra axioms, and the standard library's
    [VectorSpec.eq_nth_iff] already proves — as an ordinary theorem, not an
    axiom — that two vectors are equal iff they agree at every index. That
    is exactly the extensionality principle the fibre theorems need, and
    it comes for free from the representation instead of being assumed.
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.
Import VectorNotations.

Open Scope Qc_scope.

(** ** The vector type *)

Definition QVec (n : nat) := Vector.t Qc n.

Definition zero_vec (n : nat) : QVec n := Vector.const 0 n.

Definition vadd {n : nat} (x y : QVec n) : QVec n := Vector.map2 Qcplus x y.
Definition vneg {n : nat} (x : QVec n) : QVec n := Vector.map Qcopp x.
Definition vsub {n : nat} (x y : QVec n) : QVec n := vadd x (vneg y).
Definition vscale {n : nat} (q : Qc) (x : QVec n) : QVec n := Vector.map (Qcmult q) x.

Declare Scope qvec_scope.
Delimit Scope qvec_scope with qvec.
Notation "x +v y" := (vadd x y) (at level 50, left associativity) : qvec_scope.
Notation "-v x" := (vneg x) (at level 35, right associativity) : qvec_scope.
Notation "x -v y" := (vsub x y) (at level 50, left associativity) : qvec_scope.
Notation "q *v x" := (vscale q x) (at level 40, left associativity) : qvec_scope.
Open Scope qvec_scope.

(** ** Extensionality

    The one principle every algebraic law below is proved through: two
    vectors are equal iff they agree at every index. This is a proved
    theorem ([Vector.eq_nth_iff]), not an assumption. *)

Lemma vec_ext {n : nat} (x y : QVec n) :
  (forall i : Fin.t n, Vector.nth x i = Vector.nth y i) -> x = y.
Proof.
  intros H.
  apply Vector.eq_nth_iff.
  intros p1 p2 ->.
  apply H.
Qed.

(** ** Pointwise unfolding lemmas

    Each operation reduces to the corresponding [Qc] operation at every
    index. These are the only facts the algebraic laws below need about
    how [vadd], [vneg], [vscale], and [zero_vec] are built. *)

Lemma vadd_nth {n : nat} (x y : QVec n) (i : Fin.t n) :
  Vector.nth (vadd x y) i = Vector.nth x i + Vector.nth y i.
Proof. unfold vadd. apply (Vector.nth_map2 Qcplus x y i i i eq_refl eq_refl). Qed.

Lemma vneg_nth {n : nat} (x : QVec n) (i : Fin.t n) :
  Vector.nth (vneg x) i = - Vector.nth x i.
Proof. unfold vneg. apply (Vector.nth_map Qcopp x i i eq_refl). Qed.

Lemma vscale_nth {n : nat} (q : Qc) (x : QVec n) (i : Fin.t n) :
  Vector.nth (vscale q x) i = q * Vector.nth x i.
Proof. unfold vscale. apply (Vector.nth_map (Qcmult q) x i i eq_refl). Qed.

Lemma zero_vec_nth {n : nat} (i : Fin.t n) :
  Vector.nth (zero_vec n) i = 0.
Proof. unfold zero_vec. apply Vector.const_nth. Qed.

Lemma vsub_nth {n : nat} (x y : QVec n) (i : Fin.t n) :
  Vector.nth (vsub x y) i = Vector.nth x i - Vector.nth y i.
Proof. unfold vsub. rewrite vadd_nth, vneg_nth. ring. Qed.

(** ** Additive structure *)

Lemma vadd_comm {n : nat} (x y : QVec n) : vadd x y = vadd y x.
Proof. apply vec_ext; intros i. rewrite !vadd_nth. ring. Qed.

Lemma vadd_assoc {n : nat} (x y z : QVec n) :
  vadd (vadd x y) z = vadd x (vadd y z).
Proof. apply vec_ext; intros i. rewrite !vadd_nth. ring. Qed.

Lemma vadd_0_l {n : nat} (x : QVec n) : vadd (zero_vec n) x = x.
Proof. apply vec_ext; intros i. rewrite vadd_nth, zero_vec_nth. ring. Qed.

Lemma vadd_0_r {n : nat} (x : QVec n) : vadd x (zero_vec n) = x.
Proof. apply vec_ext; intros i. rewrite vadd_nth, zero_vec_nth. ring. Qed.

Lemma vadd_opp_r {n : nat} (x : QVec n) : vadd x (vneg x) = zero_vec n.
Proof. apply vec_ext; intros i. rewrite vadd_nth, vneg_nth, zero_vec_nth. ring. Qed.

Lemma vadd_opp_l {n : nat} (x : QVec n) : vadd (vneg x) x = zero_vec n.
Proof. apply vec_ext; intros i. rewrite vadd_nth, vneg_nth, zero_vec_nth. ring. Qed.

Lemma vneg_involutive {n : nat} (x : QVec n) : vneg (vneg x) = x.
Proof. apply vec_ext; intros i. rewrite !vneg_nth. ring. Qed.

Lemma vsub_def {n : nat} (x y : QVec n) : vsub x y = vadd x (vneg y).
Proof. reflexivity. Qed.

(** ** Scalar structure *)

Lemma vscale_1_l {n : nat} (x : QVec n) : vscale 1 x = x.
Proof. apply vec_ext; intros i. rewrite vscale_nth. ring. Qed.

Lemma vscale_0_l {n : nat} (x : QVec n) : vscale 0 x = zero_vec n.
Proof. apply vec_ext; intros i. rewrite vscale_nth, zero_vec_nth. ring. Qed.

Lemma vscale_assoc {n : nat} (p q : Qc) (x : QVec n) :
  vscale p (vscale q x) = vscale (p * q) x.
Proof. apply vec_ext; intros i. rewrite !vscale_nth. ring. Qed.

Lemma vscale_add_distr_l {n : nat} (q : Qc) (x y : QVec n) :
  vscale q (vadd x y) = vadd (vscale q x) (vscale q y).
Proof. apply vec_ext; intros i. rewrite vscale_nth, !vadd_nth, !vscale_nth. ring. Qed.

Lemma vscale_add_distr_r {n : nat} (p q : Qc) (x : QVec n) :
  vscale (p + q) x = vadd (vscale p x) (vscale q x).
Proof. apply vec_ext; intros i. rewrite vadd_nth, !vscale_nth. ring. Qed.

Lemma vscale_neg_1 {n : nat} (x : QVec n) : vscale (- (1)) x = vneg x.
Proof. apply vec_ext; intros i. rewrite vscale_nth, vneg_nth. ring. Qed.
