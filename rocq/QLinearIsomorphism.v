(** * Generic rational linear isomorphisms

    Phase 5 will repeatedly need invertible changes of coordinates on
    the repair space [U], the residual space [V], and the claim space
    [W] — carrying instances [(D, r, L)] to isomorphic instances
    [(D', r', L')] and transporting witnesses along the way. Rather
    than reprove identity, composition, injectivity, surjectivity, and
    zero-reflection facts separately for each of the three spaces in
    each later unit, this unit establishes them once, generically, for
    an arbitrary pair of finite rational coordinate spaces.

    Map identities and composition laws are stated with [same_lmap]
    (pointwise function equality), never as Leibniz equality of
    [QLinearMap] records — records carry [lmap_add]/[lmap_scale] proof
    fields, and comparing them by [=] would compare those proofs too,
    reintroducing exactly the proof-sensitive equality this project
    has avoided at every unit since [QLinearMap.v] itself.

    An isomorphism's two inverse laws are stored as plain pointwise
    vector equalities ([iso_left_inverse], [iso_right_inverse]) rather
    than as [same_lmap] statements relating a composite to an
    identity. This gives direct rewrite rules at vector applications
    — every proof below needs only [rewrite] at a specific point, not
    an extensional composition lemma unfolded first — and the
    corresponding [same_lmap] statement for the composite is
    immediate from [compose_lmap]'s definitional reduction whenever it
    is later wanted. Injectivity, surjectivity, and zero/nonzero
    reflection are consequently derived theorems, not extra record
    fields: each follows in a few lines from the two inverse laws
    already stored, so keeping them as fields would only duplicate
    proof obligations at every construction site (the same reasoning
    [QLinearMap.v] already gives for omitting [lmap_zero]).

    [compose_lmap F G] means [G] after [F] — apply [F] first, then
    [G] — matching the order the two arguments are written, not
    conventional right-to-left function-composition notation. It is a
    transparent alias of the existing [precompose] from
    [QObstruction.v], reused rather than reconstructed; that module is
    imported solely for [same_lmap] and [precompose] themselves, and
    none of its lifting- or descent-obstruction predicates are used,
    named, or reachable from anything in this file.

    The [QLinearIsomorphism] record carries no proof that its two
    dimensions are equal. Finite-dimensional isomorphic rational
    coordinate spaces do have equal dimensions, but proving that fact
    needs rank or dimension infrastructure this unit does not build,
    and Phase 5's transport constructions never need it: an
    isomorphism's two carried maps already fix both dimensions
    explicitly in the record's own index.

    This unit supplies infrastructure only. It does NOT introduce
    presentation morphisms, commuting squares, repair/residue/claim
    transport, kernel or image transport, quotient or cokernel
    constructions, a category framework, a matrix representation, or
    any classifier or verdict statement — and it does not itself
    establish R9. Those begin in Unit 25b and later. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QObstruction.

Open Scope Qc_scope.

(** ** Part I: Generic identity and composition *)

(** The identity map [x |-> x]; both linearity fields close by
    reflexivity, with no vector extensionality needed. *)
Definition identity_lmap (n : nat) : QLinearMap n n.
Proof.
  refine {| lmap := fun x => x; lmap_add := _; lmap_scale := _ |}.
  - intros x y. reflexivity.
  - intros a x. reflexivity.
Defined.

(** [compose_lmap F G] means [G] after [F]: apply [F], then [G]. A
    transparent alias of [precompose], not a second composition
    construction. *)
Definition compose_lmap
    {n m p : nat}
    (F : QLinearMap n m)
    (G : QLinearMap m p)
    : QLinearMap n p :=
  precompose F G.

(** ** Part II: Generic extensional-equality infrastructure *)

Lemma same_lmap_refl {n m : nat} (F : QLinearMap n m) : same_lmap F F.
Proof. intro x. reflexivity. Qed.

Lemma same_lmap_sym
    {n m : nat} (F G : QLinearMap n m) :
  same_lmap F G -> same_lmap G F.
Proof. intros H x. symmetry. apply H. Qed.

Lemma same_lmap_trans
    {n m : nat} (F G H : QLinearMap n m) :
  same_lmap F G -> same_lmap G H -> same_lmap F H.
Proof. intros H1 H2 x. rewrite (H1 x). apply H2. Qed.

Lemma compose_lmap_same_inner
    {n m p : nat}
    (F F' : QLinearMap n m)
    (G : QLinearMap m p) :
  same_lmap F F' ->
  same_lmap (compose_lmap F G) (compose_lmap F' G).
Proof.
  intros HF x.
  change (lmap G (lmap F x) = lmap G (lmap F' x)).
  rewrite (HF x).
  reflexivity.
Qed.

Lemma compose_lmap_same_outer
    {n m p : nat}
    (F : QLinearMap n m)
    (G G' : QLinearMap m p) :
  same_lmap G G' ->
  same_lmap (compose_lmap F G) (compose_lmap F G').
Proof.
  intros HG x.
  change (lmap G (lmap F x) = lmap G' (lmap F x)).
  apply HG.
Qed.

Lemma compose_lmap_same
    {n m p : nat}
    (F F' : QLinearMap n m)
    (G G' : QLinearMap m p) :
  same_lmap F F' ->
  same_lmap G G' ->
  same_lmap (compose_lmap F G) (compose_lmap F' G').
Proof.
  intros HF HG.
  apply (same_lmap_trans
           (compose_lmap F G) (compose_lmap F' G) (compose_lmap F' G')).
  - apply (compose_lmap_same_inner F F' G HF).
  - apply (compose_lmap_same_outer F' G G' HG).
Qed.

Lemma compose_lmap_id_left
    {n m : nat} (F : QLinearMap n m) :
  same_lmap (compose_lmap F (identity_lmap m)) F.
Proof.
  intro x.
  change (lmap (identity_lmap m) (lmap F x) = lmap F x).
  reflexivity.
Qed.

Lemma compose_lmap_id_right
    {n m : nat} (F : QLinearMap n m) :
  same_lmap (compose_lmap (identity_lmap n) F) F.
Proof.
  intro x.
  change (lmap F (lmap (identity_lmap n) x) = lmap F x).
  reflexivity.
Qed.

Lemma compose_lmap_assoc
    {n m p q : nat}
    (F : QLinearMap n m)
    (G : QLinearMap m p)
    (H : QLinearMap p q) :
  same_lmap
    (compose_lmap (compose_lmap F G) H)
    (compose_lmap F (compose_lmap G H)).
Proof.
  intro x.
  change (lmap H (lmap G (lmap F x)) = lmap H (lmap G (lmap F x))).
  reflexivity.
Qed.

(** ** Part III: The linear-isomorphism record *)

Record QLinearIsomorphism (n m : nat) := mkQLinearIsomorphism {
  iso_forward : QLinearMap n m;
  iso_backward : QLinearMap m n;

  iso_left_inverse :
    forall x : QVec n,
      lmap iso_backward (lmap iso_forward x) = x;

  iso_right_inverse :
    forall y : QVec m,
      lmap iso_forward (lmap iso_backward y) = y;
}.

Arguments iso_forward {n m}.
Arguments iso_backward {n m}.
Arguments iso_left_inverse {n m}.
Arguments iso_right_inverse {n m}.

(** ** Part IV: Isomorphism constructions *)

Definition inverse_linear_isomorphism
    {n m : nat}
    (F : QLinearIsomorphism n m)
    : QLinearIsomorphism m n :=
  {|
    iso_forward := iso_backward F;
    iso_backward := iso_forward F;
    iso_left_inverse := iso_right_inverse F;
    iso_right_inverse := iso_left_inverse F;
  |}.

Definition identity_linear_isomorphism
    (n : nat)
    : QLinearIsomorphism n n :=
  {|
    iso_forward := identity_lmap n;
    iso_backward := identity_lmap n;
    iso_left_inverse := fun x => eq_refl;
    iso_right_inverse := fun y => eq_refl;
  |}.

Definition compose_linear_isomorphism
    {n m p : nat}
    (F : QLinearIsomorphism n m)
    (G : QLinearIsomorphism m p)
    : QLinearIsomorphism n p.
Proof.
  refine {|
    iso_forward := compose_lmap (iso_forward F) (iso_forward G);
    iso_backward := compose_lmap (iso_backward G) (iso_backward F);
    iso_left_inverse := _;
    iso_right_inverse := _;
  |}.
  - intro x.
    change
      (lmap (iso_backward F)
        (lmap (iso_backward G)
          (lmap (iso_forward G) (lmap (iso_forward F) x)))
       = x).
    rewrite (iso_left_inverse G (lmap (iso_forward F) x)).
    apply (iso_left_inverse F x).
  - intro z.
    change
      (lmap (iso_forward G)
        (lmap (iso_forward F)
          (lmap (iso_backward F) (lmap (iso_backward G) z)))
       = z).
    rewrite (iso_right_inverse F (lmap (iso_backward G) z)).
    apply (iso_right_inverse G z).
Defined.

(** ** Part V: Component exposure theorems *)

Lemma inverse_linear_isomorphism_forward_same
    {n m : nat} (F : QLinearIsomorphism n m) :
  same_lmap
    (iso_forward (inverse_linear_isomorphism F))
    (iso_backward F).
Proof. intro x. reflexivity. Qed.

Lemma inverse_linear_isomorphism_backward_same
    {n m : nat} (F : QLinearIsomorphism n m) :
  same_lmap
    (iso_backward (inverse_linear_isomorphism F))
    (iso_forward F).
Proof. intro x. reflexivity. Qed.

Lemma identity_linear_isomorphism_forward_same
    (n : nat) :
  same_lmap
    (iso_forward (identity_linear_isomorphism n))
    (identity_lmap n).
Proof. intro x. reflexivity. Qed.

Lemma identity_linear_isomorphism_backward_same
    (n : nat) :
  same_lmap
    (iso_backward (identity_linear_isomorphism n))
    (identity_lmap n).
Proof. intro x. reflexivity. Qed.

Lemma compose_linear_isomorphism_forward_same
    {n m p : nat}
    (F : QLinearIsomorphism n m)
    (G : QLinearIsomorphism m p) :
  same_lmap
    (iso_forward (compose_linear_isomorphism F G))
    (compose_lmap (iso_forward F) (iso_forward G)).
Proof. intro x. reflexivity. Qed.

Lemma compose_linear_isomorphism_backward_same
    {n m p : nat}
    (F : QLinearIsomorphism n m)
    (G : QLinearIsomorphism m p) :
  same_lmap
    (iso_backward (compose_linear_isomorphism F G))
    (compose_lmap (iso_backward G) (iso_backward F)).
Proof. intro x. reflexivity. Qed.

(** ** Part VI: Injectivity and surjectivity *)

Theorem linear_isomorphism_forward_injective
    {n m : nat}
    (F : QLinearIsomorphism n m)
    (x1 x2 : QVec n) :
  lmap (iso_forward F) x1 = lmap (iso_forward F) x2 -> x1 = x2.
Proof.
  intro Heq.
  rewrite <- (iso_left_inverse F x1).
  rewrite <- (iso_left_inverse F x2).
  rewrite Heq.
  reflexivity.
Qed.

Theorem linear_isomorphism_backward_injective
    {n m : nat}
    (F : QLinearIsomorphism n m)
    (y1 y2 : QVec m) :
  lmap (iso_backward F) y1 = lmap (iso_backward F) y2 -> y1 = y2.
Proof.
  intro Heq.
  rewrite <- (iso_right_inverse F y1).
  rewrite <- (iso_right_inverse F y2).
  rewrite Heq.
  reflexivity.
Qed.

Theorem linear_isomorphism_forward_surjective
    {n m : nat} (F : QLinearIsomorphism n m) :
  forall y : QVec m, exists x : QVec n, lmap (iso_forward F) x = y.
Proof.
  intro y.
  exists (lmap (iso_backward F) y).
  apply (iso_right_inverse F y).
Qed.

Theorem linear_isomorphism_backward_surjective
    {n m : nat} (F : QLinearIsomorphism n m) :
  forall x : QVec n, exists y : QVec m, lmap (iso_backward F) y = x.
Proof.
  intro x.
  exists (lmap (iso_forward F) x).
  apply (iso_left_inverse F x).
Qed.

(** ** Part VII: Zero preservation and reflection *)

Theorem linear_isomorphism_forward_zero_iff
    {n m : nat}
    (F : QLinearIsomorphism n m)
    (x : QVec n) :
  lmap (iso_forward F) x = zero_vec m
  <->
  x = zero_vec n.
Proof.
  split.
  - intro Heq.
    rewrite <- (iso_left_inverse F x).
    rewrite Heq.
    apply (lmap_preserves_zero (iso_backward F)).
  - intro Heq.
    rewrite Heq.
    apply (lmap_preserves_zero (iso_forward F)).
Qed.

Theorem linear_isomorphism_backward_zero_iff
    {n m : nat}
    (F : QLinearIsomorphism n m)
    (y : QVec m) :
  lmap (iso_backward F) y = zero_vec n
  <->
  y = zero_vec m.
Proof.
  split.
  - intro Heq.
    rewrite <- (iso_right_inverse F y).
    rewrite Heq.
    apply (lmap_preserves_zero (iso_forward F)).
  - intro Heq.
    rewrite Heq.
    apply (lmap_preserves_zero (iso_backward F)).
Qed.

(** ** Part VIII: Nonzero preservation and reflection *)

Theorem linear_isomorphism_forward_nonzero_iff
    {n m : nat}
    (F : QLinearIsomorphism n m)
    (x : QVec n) :
  lmap (iso_forward F) x <> zero_vec m
  <->
  x <> zero_vec n.
Proof.
  split.
  - intros Hne Heq.
    apply Hne.
    rewrite Heq.
    apply (lmap_preserves_zero (iso_forward F)).
  - intros Hne Heq.
    apply Hne.
    apply (linear_isomorphism_forward_zero_iff F x).
    exact Heq.
Qed.

Theorem linear_isomorphism_backward_nonzero_iff
    {n m : nat}
    (F : QLinearIsomorphism n m)
    (y : QVec m) :
  lmap (iso_backward F) y <> zero_vec n
  <->
  y <> zero_vec m.
Proof.
  split.
  - intros Hne Heq.
    apply Hne.
    rewrite Heq.
    apply (lmap_preserves_zero (iso_backward F)).
  - intros Hne Heq.
    apply Hne.
    apply (linear_isomorphism_backward_zero_iff F y).
    exact Heq.
Qed.

(** ** Part IX: Concrete probes *)

Example identity_lmap_application_probe
    {n : nat} (x : QVec n) :
  lmap (identity_lmap n) x = x.
Proof. reflexivity. Qed.

Example compose_lmap_application_probe
    {n m p : nat}
    (F : QLinearMap n m)
    (G : QLinearMap m p)
    (x : QVec n) :
  lmap (compose_lmap F G) x = lmap G (lmap F x).
Proof. reflexivity. Qed.

Example identity_linear_isomorphism_inverse_probe
    {n : nat} (x : QVec n) :
  lmap
    (iso_backward (identity_linear_isomorphism n))
    (lmap (iso_forward (identity_linear_isomorphism n)) x)
  = x.
Proof. reflexivity. Qed.

Example linear_isomorphism_zero_reflection_probe
    {n m : nat}
    (F : QLinearIsomorphism n m)
    (x : QVec n) :
  lmap (iso_forward F) x = zero_vec m -> x = zero_vec n.
Proof.
  apply (linear_isomorphism_forward_zero_iff F x).
Qed.
