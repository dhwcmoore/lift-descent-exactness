(** * Transport of the lifting obstruction under a presentation isomorphism

    The repository already represents the lifting-obstruction class of
    a residue [r : V] through the image residual
    [R_D(y) = y - P_D(y) : V -> V] ([image_residual_map D]), which
    vanishes exactly on [im D]. This unit shows that an invertible
    presentation change [(D, r) -> (D', r')], carried by [b :
    QLinearIsomorphism V V'] within a [PresentationIsomorphism],
    transports this representation faithfully: the represented
    obstruction space [im R_D] is isomorphic to [im R_{D'}], the
    represented class of [r] maps to the represented class of [r'],
    and [r in im D] exactly when [r' in im D'].

    The residual is chosen through an independent elimination for each
    of [D] and [D']; an arbitrary [b] therefore need not carry the
    complement selected for [D] to the complement selected for [D'].
    The correct forward transport is consequently [z |-> R_{D'}(b z)],
    not the raw naturality equation [b (R_D y) = R_{D'}(b y)] — that
    equation is false in general and is never stated here. What does
    hold, and is what every later theorem in this file is built from,
    is the weaker but correct identity [R_{D'}(b (R_D y)) = R_{D'}(b
    y)]: applying a residual before transporting changes only the
    representative by an image element, which the next residual
    absorbs.

    [QSubspaceLinearIsomorphism] is the minimal record needed to state
    "the two representative subspaces are isomorphic" without turning
    subspace elements into dependent pairs, mirroring [QSubspace.v]'s
    own reasons for representing a subspace by a predicate rather than
    a subtype. Its inverse laws are required only on members of the
    designated subspace, exactly as [QLinearMapFrom]'s own laws are.

    This unit completes only the lifting half of R9 — the invariance
    of [lift_obstruction_zero]/[lift_obstructed], the induced
    isomorphism of representative obstruction spaces, and transport of
    separator witnesses in both directions. It does not transport
    [ker D], restricted descent maps, gauge witnesses, factor maps, or
    descent-obstruction status (Unit 26b), and it does not itself
    combine both halves into R9 or mention profile, verdict, or
    canonical-value theorems (Unit 27). *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QSubspaceMap.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QImageExtension.
From LiftDescent Require Import QLinearFunctional.
From LiftDescent Require Import QSeparatorWitness.
From LiftDescent Require Import QLinearIsomorphism.
From LiftDescent Require Import QPresentationMorphism.

Open Scope Qc_scope.

(** ** Part I: A minimal subspace-isomorphism representation *)

Record QSubspaceLinearIsomorphism
    {n m : nat}
    (S : QSubspace n)
    (T : QSubspace m)
    : Type := mkQSubspaceLinearIsomorphism {

  subiso_forward :
    QLinearMapFrom n m S;

  subiso_backward :
    QLinearMapFrom m n T;

  subiso_forward_mem :
    forall x : QVec n,
      subspace_mem S x ->
      subspace_mem T (from_map subiso_forward x);

  subiso_backward_mem :
    forall y : QVec m,
      subspace_mem T y ->
      subspace_mem S (from_map subiso_backward y);

  subiso_left_inverse :
    forall x : QVec n,
      subspace_mem S x ->
      from_map subiso_backward
        (from_map subiso_forward x)
      =
      x;

  subiso_right_inverse :
    forall y : QVec m,
      subspace_mem T y ->
      from_map subiso_forward
        (from_map subiso_backward y)
      =
      y
}.

Arguments subiso_forward {n m S T}.
Arguments subiso_backward {n m S T}.
Arguments subiso_forward_mem {n m S T}.
Arguments subiso_backward_mem {n m S T}.
Arguments subiso_left_inverse {n m S T}.
Arguments subiso_right_inverse {n m S T}.

(** ** Part II: The represented lifting-obstruction space *)

Definition lifting_obstruction_subspace
    {u v : nat}
    (D : QLinearMap u v)
    : QSubspace v :=
  image_subspace (image_residual_map D).

Definition lifting_obstruction_representative
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v)
    : QVec v :=
  lmap (image_residual_map D) r.

(** ** Part III: Residual algebra *)

Theorem image_residual_add_image
    {u v : nat}
    (D : QLinearMap u v)
    (y q : QVec v) :
  linear_image D q ->
  lmap (image_residual_map D) (vadd y q) = lmap (image_residual_map D) y.
Proof.
  intro Hq.
  rewrite (lmap_add (image_residual_map D) y q).
  rewrite (image_residual_on_image D q Hq).
  apply vadd_0_r.
Qed.

Theorem image_residual_idempotent
    {u v : nat}
    (D : QLinearMap u v)
    (y : QVec v) :
  lmap (image_residual_map D) (lmap (image_residual_map D) y)
  = lmap (image_residual_map D) y.
Proof.
  destruct (linear_map_image_projection_in_image D y) as [x Hx].
  assert (Hneg : linear_image D (vneg (lmap (linear_map_image_projection D) y))).
  { exists (vneg x).
    rewrite (lmap_preserves_neg D x).
    rewrite Hx.
    reflexivity. }
  transitivity
    (lmap (image_residual_map D)
      (vadd y (vneg (lmap (linear_map_image_projection D) y)))).
  - f_equal.
  - exact (image_residual_add_image D y
             (vneg (lmap (linear_map_image_projection D) y)) Hneg).
Qed.

Theorem image_residual_fixes_lifting_obstruction_subspace
    {u v : nat}
    (D : QLinearMap u v)
    (z : QVec v) :
  subspace_mem (lifting_obstruction_subspace D) z ->
  lmap (image_residual_map D) z = z.
Proof.
  intros [y Hy].
  rewrite <- Hy.
  apply image_residual_idempotent.
Qed.

Theorem lifting_obstruction_representative_mem
    {u v : nat}
    (D : QLinearMap u v)
    (r : QVec v) :
  subspace_mem
    (lifting_obstruction_subspace D)
    (lifting_obstruction_representative D r).
Proof.
  exists r.
  reflexivity.
Qed.

(** ** Part IV: Transport of image membership *)

Theorem presentation_isomorphism_image_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y : QVec nV) :
  linear_image (inst_D I) y ->
  linear_image (inst_D I') (lmap (iso_forward (pi_residual P)) y).
Proof.
  intros [x Hx].
  exists (lmap (iso_forward (pi_state P)) x).
  transitivity (lmap (iso_forward (pi_residual P)) (lmap (inst_D I) x)).
  - exact (presentation_morphism_D_transport (presentation_isomorphism_forward_morphism P) x).
  - f_equal. exact Hx.
Qed.

Theorem presentation_isomorphism_image_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y' : QVec nV') :
  linear_image (inst_D I') y' ->
  linear_image (inst_D I) (lmap (iso_backward (pi_residual P)) y').
Proof.
  intro Hy'.
  exact (presentation_isomorphism_image_forward (inverse_presentation_isomorphism P) y' Hy').
Qed.

Theorem presentation_isomorphism_image_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y : QVec nV) :
  linear_image (inst_D I) y
  <->
  linear_image (inst_D I') (lmap (iso_forward (pi_residual P)) y).
Proof.
  split.
  - apply (presentation_isomorphism_image_forward P y).
  - intro Hy'.
    pose proof (presentation_isomorphism_image_backward P
                  (lmap (iso_forward (pi_residual P)) y) Hy') as H.
    rewrite (iso_left_inverse (pi_residual P) y) in H.
    exact H.
Qed.

(** ** Part V: Residual transport modulo image *)

Theorem presentation_isomorphism_residual_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y : QVec nV) :
  lmap
    (image_residual_map (inst_D I'))
    (lmap
      (iso_forward (pi_residual P))
      (lmap (image_residual_map (inst_D I)) y))
  =
  lmap
    (image_residual_map (inst_D I'))
    (lmap (iso_forward (pi_residual P)) y).
Proof.
  pose (Py := lmap (linear_map_image_projection (inst_D I)) y).
  destruct (linear_map_image_projection_in_image (inst_D I) y) as [x Hx].
  assert (HmemNeg : linear_image (inst_D I) (vneg Py)).
  { exists (vneg x).
    rewrite (lmap_preserves_neg (inst_D I) x).
    unfold Py. rewrite Hx. reflexivity. }
  assert (HmemNeg' :
    linear_image (inst_D I') (lmap (iso_forward (pi_residual P)) (vneg Py))).
  { exact (presentation_isomorphism_image_forward P (vneg Py) HmemNeg). }
  transitivity
    (lmap (image_residual_map (inst_D I'))
      (lmap (iso_forward (pi_residual P)) (vadd y (vneg Py)))).
  - f_equal.
  - transitivity
      (lmap (image_residual_map (inst_D I'))
        (vadd
          (lmap (iso_forward (pi_residual P)) y)
          (lmap (iso_forward (pi_residual P)) (vneg Py)))).
    + f_equal.
      apply (lmap_add (iso_forward (pi_residual P)) y (vneg Py)).
    + exact (image_residual_add_image (inst_D I')
               (lmap (iso_forward (pi_residual P)) y)
               (lmap (iso_forward (pi_residual P)) (vneg Py))
               HmemNeg').
Qed.

Theorem presentation_isomorphism_residual_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y' : QVec nV') :
  lmap
    (image_residual_map (inst_D I))
    (lmap
      (iso_backward (pi_residual P))
      (lmap (image_residual_map (inst_D I')) y'))
  =
  lmap
    (image_residual_map (inst_D I))
    (lmap (iso_backward (pi_residual P)) y').
Proof.
  exact (presentation_isomorphism_residual_forward
           (inverse_presentation_isomorphism P) y').
Qed.

(** ** Part VI: Invariance of the lifting obstruction *)

Theorem presentation_isomorphism_lift_obstruction_zero_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  lift_obstruction_zero (inst_D I) r
  <->
  lift_obstruction_zero (inst_D I') r'.
Proof.
  split.
  - intros [u Hu].
    exists (lmap (pm_state (presentation_isomorphism_forward_morphism P)) u).
    apply (presentation_morphism_repair_transport
             (presentation_isomorphism_forward_morphism P) u).
    exact Hu.
  - intros [u' Hu'].
    exists (lmap (pm_state (presentation_isomorphism_reverse_morphism P)) u').
    apply (presentation_morphism_repair_transport
             (presentation_isomorphism_reverse_morphism P) u').
    exact Hu'.
Qed.

Theorem presentation_isomorphism_lift_obstructed_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  lift_obstructed (inst_D I) r
  <->
  lift_obstructed (inst_D I') r'.
Proof.
  unfold lift_obstructed.
  split.
  - intros Hn Hz.
    apply Hn.
    apply (presentation_isomorphism_lift_obstruction_zero_iff P).
    exact Hz.
  - intros Hn Hz.
    apply Hn.
    apply (presentation_isomorphism_lift_obstruction_zero_iff P).
    exact Hz.
Qed.

(** ** Part VII: The induced maps on representative spaces *)

Definition lifting_obstruction_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    :
    QLinearMapFrom
      nV
      nV'
      (lifting_obstruction_subspace (inst_D I))
    :=
  restrict_domain
    (lifting_obstruction_subspace (inst_D I))
    (compose_lmap
      (iso_forward (pi_residual P))
      (image_residual_map (inst_D I'))).

Definition lifting_obstruction_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    :
    QLinearMapFrom
      nV'
      nV
      (lifting_obstruction_subspace (inst_D I'))
    :=
  restrict_domain
    (lifting_obstruction_subspace (inst_D I'))
    (compose_lmap
      (iso_backward (pi_residual P))
      (image_residual_map (inst_D I))).

Theorem lifting_obstruction_transport_forward_mem
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (z : QVec nV) :
  subspace_mem
    (lifting_obstruction_subspace (inst_D I))
    z
  ->
  subspace_mem
    (lifting_obstruction_subspace (inst_D I'))
    (from_map
      (lifting_obstruction_transport_forward P)
      z).
Proof.
  intro Hz.
  exists (lmap (iso_forward (pi_residual P)) z).
  reflexivity.
Qed.

Theorem lifting_obstruction_transport_backward_mem
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (z' : QVec nV') :
  subspace_mem
    (lifting_obstruction_subspace (inst_D I'))
    z'
  ->
  subspace_mem
    (lifting_obstruction_subspace (inst_D I))
    (from_map
      (lifting_obstruction_transport_backward P)
      z').
Proof.
  intro Hz'.
  exists (lmap (iso_backward (pi_residual P)) z').
  reflexivity.
Qed.

Theorem lifting_obstruction_transport_left_inverse
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (z : QVec nV) :
  subspace_mem
    (lifting_obstruction_subspace (inst_D I))
    z
  ->
  from_map
    (lifting_obstruction_transport_backward P)
    (from_map
      (lifting_obstruction_transport_forward P)
      z)
  =
  z.
Proof.
  intro Hz.
  change
    (lmap (image_residual_map (inst_D I))
      (lmap (iso_backward (pi_residual P))
        (lmap (image_residual_map (inst_D I'))
          (lmap (iso_forward (pi_residual P)) z)))
    = z).
  transitivity
    (lmap (image_residual_map (inst_D I))
      (lmap (iso_backward (pi_residual P))
        (lmap (iso_forward (pi_residual P)) z))).
  - exact (presentation_isomorphism_residual_backward P
             (lmap (iso_forward (pi_residual P)) z)).
  - transitivity (lmap (image_residual_map (inst_D I)) z).
    + f_equal. apply (iso_left_inverse (pi_residual P) z).
    + apply (image_residual_fixes_lifting_obstruction_subspace (inst_D I) z Hz).
Qed.

Theorem lifting_obstruction_transport_right_inverse
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (z' : QVec nV') :
  subspace_mem
    (lifting_obstruction_subspace (inst_D I'))
    z'
  ->
  from_map
    (lifting_obstruction_transport_forward P)
    (from_map
      (lifting_obstruction_transport_backward P)
      z')
  =
  z'.
Proof.
  intro Hz'.
  change
    (lmap (image_residual_map (inst_D I'))
      (lmap (iso_forward (pi_residual P))
        (lmap (image_residual_map (inst_D I))
          (lmap (iso_backward (pi_residual P)) z')))
    = z').
  transitivity
    (lmap (image_residual_map (inst_D I'))
      (lmap (iso_forward (pi_residual P))
        (lmap (iso_backward (pi_residual P)) z'))).
  - exact (presentation_isomorphism_residual_forward P
             (lmap (iso_backward (pi_residual P)) z')).
  - transitivity (lmap (image_residual_map (inst_D I')) z').
    + f_equal. apply (iso_right_inverse (pi_residual P) z').
    + apply (image_residual_fixes_lifting_obstruction_subspace (inst_D I') z' Hz').
Qed.

Definition lifting_obstruction_space_isomorphism
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    :
    QSubspaceLinearIsomorphism
      (lifting_obstruction_subspace (inst_D I))
      (lifting_obstruction_subspace (inst_D I')) :=
  {|
    subiso_forward := lifting_obstruction_transport_forward P;
    subiso_backward := lifting_obstruction_transport_backward P;
    subiso_forward_mem := lifting_obstruction_transport_forward_mem P;
    subiso_backward_mem := lifting_obstruction_transport_backward_mem P;
    subiso_left_inverse := lifting_obstruction_transport_left_inverse P;
    subiso_right_inverse := lifting_obstruction_transport_right_inverse P;
  |}.

(** ** Part VIII: Transport of the represented residue class *)

Theorem lifting_obstruction_representative_transport
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  from_map
    (lifting_obstruction_transport_forward P)
    (lifting_obstruction_representative
      (inst_D I)
      r)
  =
  lifting_obstruction_representative
    (inst_D I')
    r'.
Proof.
  change
    (lmap (image_residual_map (inst_D I'))
      (lmap (iso_forward (pi_residual P))
        (lmap (image_residual_map (inst_D I)) r))
    = lmap (image_residual_map (inst_D I')) r').
  transitivity
    (lmap (image_residual_map (inst_D I')) (lmap (iso_forward (pi_residual P)) r)).
  - exact (presentation_isomorphism_residual_forward P r).
  - f_equal. exact (pi_residue_preserved P).
Qed.

(** ** Part IX: Separator transport *)

Definition separator_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y : QLinearFunctional nV)
    : QLinearFunctional nV' :=
  compose_lmap
    (iso_backward (pi_residual P))
    y.

Definition separator_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y' : QLinearFunctional nV')
    : QLinearFunctional nV :=
  compose_lmap
    (iso_forward (pi_residual P))
    y'.

Theorem separator_transport_forward_witness
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y : QLinearFunctional nV) :
  separator_witness (inst_D I) r y ->
  separator_witness
    (inst_D I')
    r'
    (separator_transport_forward P y).
Proof.
  intros [Hann Hdet].
  split.
  - intro x'.
    change
      (lmap y (lmap (iso_backward (pi_residual P)) (lmap (inst_D I') x')) = zero_vec 1).
    pose proof (presentation_isomorphism_reverse_D_square P x'
      : lmap (iso_backward (pi_residual P)) (lmap (inst_D I') x')
        = lmap (inst_D I) (lmap (iso_backward (pi_state P)) x')) as Hrevx.
    rewrite Hrevx.
    apply Hann.
  - change (lmap y (lmap (iso_backward (pi_residual P)) r') <> zero_vec 1).
    pose proof (presentation_isomorphism_reverse_residue P
      : lmap (iso_backward (pi_residual P)) r' = r) as Hrr.
    rewrite Hrr.
    exact Hdet.
Qed.

Theorem separator_transport_backward_witness
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y' : QLinearFunctional nV') :
  separator_witness (inst_D I') r' y' ->
  separator_witness
    (inst_D I)
    r
    (separator_transport_backward P y').
Proof.
  intros [Hann' Hdet'].
  split.
  - intro x.
    change
      (lmap y' (lmap (iso_forward (pi_residual P)) (lmap (inst_D I) x)) = zero_vec 1).
    pose proof (pi_D_square P x
      : lmap (iso_forward (pi_residual P)) (lmap (inst_D I) x)
        = lmap (inst_D I') (lmap (iso_forward (pi_state P)) x)) as Hsq.
    rewrite Hsq.
    apply Hann'.
  - change (lmap y' (lmap (iso_forward (pi_residual P)) r) <> zero_vec 1).
    pose proof (pi_residue_preserved P
      : lmap (iso_forward (pi_residual P)) r = r') as Hrp.
    rewrite Hrp.
    exact Hdet'.
Qed.

(** ** Part X: Concrete probes *)

Example image_residual_idempotent_probe
    {u v : nat}
    (D : QLinearMap u v)
    (y : QVec v) :
  lmap
    (image_residual_map D)
    (lmap (image_residual_map D) y)
  =
  lmap (image_residual_map D) y.
Proof.
  apply image_residual_idempotent.
Qed.

Example lifting_obstruction_forward_mem_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (z : QVec nV)
    (Hz :
      subspace_mem
        (lifting_obstruction_subspace (inst_D I))
        z) :
  subspace_mem
    (lifting_obstruction_subspace (inst_D I'))
    (from_map
      (lifting_obstruction_transport_forward P)
      z).
Proof.
  apply lifting_obstruction_transport_forward_mem.
  exact Hz.
Qed.

Example lifting_obstruction_representative_transport_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  from_map
    (lifting_obstruction_transport_forward P)
    (lifting_obstruction_representative
      (inst_D I)
      r)
  =
  lifting_obstruction_representative
    (inst_D I')
    r'.
Proof.
  apply lifting_obstruction_representative_transport.
Qed.

Example separator_transport_forward_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (y : QLinearFunctional nV)
    (Hy : separator_witness (inst_D I) r y) :
  separator_witness
    (inst_D I')
    r'
    (separator_transport_forward P y).
Proof.
  apply separator_transport_forward_witness.
  exact Hy.
Qed.
