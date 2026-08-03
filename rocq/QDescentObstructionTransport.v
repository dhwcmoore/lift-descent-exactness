(** * Transport of the descent obstruction under a presentation isomorphism

    The kernel of [D] is already represented as a predicate subspace,
    [kernel_subspace D], and the restricted descent-defect map [L|_ker
    D] as a [QLinearMapFrom] — [descent_defect_map D L :=
    restrict_domain (kernel_subspace D) L] — reusing exactly the
    infrastructure [QSubspaceMap.v] built for this purpose, rather
    than turning kernel elements into a dependent subtype or writing a
    second kernel predicate. A presentation isomorphism's state
    component [a : U ~= U'] restricts, on those same grounds, to an
    isomorphism [ker D ~= ker D'] represented with Unit 26a's already
    generic [QSubspaceLinearIsomorphism] record — no new
    subspace-isomorphism type is needed here.

    Equality of two maps restricted to a common subspace is stated
    with [same_from_map], never as Leibniz equality of
    [QLinearMapFrom] records (which would compare their
    [from_add]/[from_scale] proof fields), continuing exactly the
    equality discipline [QPresentationMorphism.v] and
    [QLiftObstructionTransport.v] already established for [same_lmap].

    An arbitrary ambient factor map [M : V -> W] with [L = M D]
    transports to [M' := c M b^{-1} : V' -> W'], and this is proved to
    be *a* valid target factor witness, not *the* factor witness: this
    unit does not, and given the existing theory cannot, claim
    uniqueness of ambient factor maps — only the intrinsic map on
    [im D] is unique, and that fact is untouched here.

    This unit completes only the descent half of R9: kernel-space
    isomorphism, transport of an arbitrary map defined on the kernel
    (hence of the actual restricted descent-defect map), kernel
    vanishing invariance, ambient-factor-map transport, invariance of
    [descent_obstruction_zero]/[descent_obstructed], and transport of
    an already-supplied gauge witness in both directions — it does not
    rerun the constructive gauge search from [QGaugeWitness.v]. It
    does not combine this with Unit 26a's lifting-half results into a
    full profile or verdict invariance theorem, and it does not
    mention canonical exact values; both belong to Unit 27. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QSubspaceMap.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QImagePreimage.
From LiftDescent Require Import QDescentFactorisation.
From LiftDescent Require Import QGaugeWitness.
From LiftDescent Require Import QLinearIsomorphism.
From LiftDescent Require Import QPresentationMorphism.
From LiftDescent Require Import QLiftObstructionTransport.

Open Scope Qc_scope.

(** ** Part I: The restricted descent-defect map *)

Definition descent_defect_map
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : QLinearMapFrom u w (kernel_subspace D) :=
  restrict_domain (kernel_subspace D) L.

(** ** Part II: Isomorphism of kernel spaces *)

Definition kernel_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    : QLinearMapFrom nU nU' (kernel_subspace (inst_D I)) :=
  restrict_domain (kernel_subspace (inst_D I)) (iso_forward (pi_state P)).

Definition kernel_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    : QLinearMapFrom nU' nU (kernel_subspace (inst_D I')) :=
  restrict_domain (kernel_subspace (inst_D I')) (iso_backward (pi_state P)).

Theorem kernel_transport_forward_mem
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k : QVec nU) :
  subspace_mem (kernel_subspace (inst_D I)) k ->
  subspace_mem
    (kernel_subspace (inst_D I'))
    (from_map (kernel_transport_forward P) k).
Proof.
  intro Hk.
  exact (presentation_morphism_kernel_transport
           (presentation_isomorphism_forward_morphism P) k Hk).
Qed.

Theorem kernel_transport_backward_mem
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k' : QVec nU') :
  subspace_mem (kernel_subspace (inst_D I')) k' ->
  subspace_mem
    (kernel_subspace (inst_D I))
    (from_map (kernel_transport_backward P) k').
Proof.
  intro Hk'.
  exact (presentation_morphism_kernel_transport
           (presentation_isomorphism_reverse_morphism P) k' Hk').
Qed.

Theorem kernel_transport_left_inverse
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k : QVec nU) :
  subspace_mem (kernel_subspace (inst_D I)) k ->
  from_map
    (kernel_transport_backward P)
    (from_map (kernel_transport_forward P) k)
  = k.
Proof.
  intro Hk.
  change
    (lmap (iso_backward (pi_state P)) (lmap (iso_forward (pi_state P)) k) = k).
  apply (iso_left_inverse (pi_state P) k).
Qed.

Theorem kernel_transport_right_inverse
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k' : QVec nU') :
  subspace_mem (kernel_subspace (inst_D I')) k' ->
  from_map
    (kernel_transport_forward P)
    (from_map (kernel_transport_backward P) k')
  = k'.
Proof.
  intro Hk'.
  change
    (lmap (iso_forward (pi_state P)) (lmap (iso_backward (pi_state P)) k') = k').
  apply (iso_right_inverse (pi_state P) k').
Qed.

Theorem presentation_isomorphism_kernel_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k : QVec nU) :
  kernel (inst_D I) k
  <->
  kernel (inst_D I') (lmap (iso_forward (pi_state P)) k).
Proof.
  split.
  - apply (kernel_transport_forward_mem P k).
  - intro Hk'.
    pose proof (kernel_transport_backward_mem P
                  (lmap (iso_forward (pi_state P)) k) Hk') as H.
    change
      (kernel (inst_D I)
        (lmap (iso_backward (pi_state P)) (lmap (iso_forward (pi_state P)) k)))
      in H.
    rewrite (iso_left_inverse (pi_state P) k) in H.
    exact H.
Qed.

Definition kernel_space_isomorphism
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    : QSubspaceLinearIsomorphism
        (kernel_subspace (inst_D I))
        (kernel_subspace (inst_D I')) :=
  {|
    subiso_forward := kernel_transport_forward P;
    subiso_backward := kernel_transport_backward P;
    subiso_forward_mem := kernel_transport_forward_mem P;
    subiso_backward_mem := kernel_transport_backward_mem P;
    subiso_left_inverse := kernel_transport_left_inverse P;
    subiso_right_inverse := kernel_transport_right_inverse P;
  |}.

(** ** Part III: Transport of arbitrary maps defined on the kernel *)

Definition restricted_kernel_map_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (T : QLinearMapFrom nU nW (kernel_subspace (inst_D I)))
    : QLinearMapFrom nU' nW' (kernel_subspace (inst_D I')).
Proof.
  refine {|
    from_map := fun k' =>
      lmap (iso_forward (pi_claim P))
        (from_map T (lmap (iso_backward (pi_state P)) k'));
    from_add := _;
    from_scale := _;
  |}.
  - intros k1' k2' Hk1' Hk2'.
    pose proof (kernel_transport_backward_mem P k1' Hk1'
      : subspace_mem (kernel_subspace (inst_D I))
          (lmap (iso_backward (pi_state P)) k1')) as Hmem1.
    pose proof (kernel_transport_backward_mem P k2' Hk2'
      : subspace_mem (kernel_subspace (inst_D I))
          (lmap (iso_backward (pi_state P)) k2')) as Hmem2.
    transitivity
      (lmap (iso_forward (pi_claim P))
        (vadd
          (from_map T (lmap (iso_backward (pi_state P)) k1'))
          (from_map T (lmap (iso_backward (pi_state P)) k2')))).
    + f_equal.
      transitivity
        (from_map T
          (vadd
            (lmap (iso_backward (pi_state P)) k1')
            (lmap (iso_backward (pi_state P)) k2'))).
      * f_equal. apply (lmap_add (iso_backward (pi_state P)) k1' k2').
      * apply (from_add T _ _ Hmem1 Hmem2).
    + apply (lmap_add (iso_forward (pi_claim P)) _ _).
  - intros a k' Hk'.
    pose proof (kernel_transport_backward_mem P k' Hk'
      : subspace_mem (kernel_subspace (inst_D I))
          (lmap (iso_backward (pi_state P)) k')) as Hmem.
    transitivity
      (lmap (iso_forward (pi_claim P))
        (vscale a (from_map T (lmap (iso_backward (pi_state P)) k')))).
    + f_equal.
      transitivity
        (from_map T (vscale a (lmap (iso_backward (pi_state P)) k'))).
      * f_equal. apply (lmap_scale (iso_backward (pi_state P)) a k').
      * apply (from_scale T a _ Hmem).
    + apply (lmap_scale (iso_forward (pi_claim P)) a _).
Defined.

Definition restricted_kernel_map_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (T' : QLinearMapFrom nU' nW' (kernel_subspace (inst_D I')))
    : QLinearMapFrom nU nW (kernel_subspace (inst_D I)) :=
  restricted_kernel_map_transport_forward
    (inverse_presentation_isomorphism P) T'.

Theorem restricted_kernel_map_transport_left_inverse
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (T : QLinearMapFrom nU nW (kernel_subspace (inst_D I))) :
  same_from_map
    (restricted_kernel_map_transport_backward P
      (restricted_kernel_map_transport_forward P T))
    T.
Proof.
  intros k Hk.
  change
    (lmap (iso_backward (pi_claim P))
      (lmap (iso_forward (pi_claim P))
        (from_map T
          (lmap (iso_backward (pi_state P))
            (lmap (iso_forward (pi_state P)) k))))
     = from_map T k).
  rewrite (iso_left_inverse (pi_state P) k).
  apply (iso_left_inverse (pi_claim P) (from_map T k)).
Qed.

Theorem restricted_kernel_map_transport_right_inverse
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (T' : QLinearMapFrom nU' nW' (kernel_subspace (inst_D I'))) :
  same_from_map
    (restricted_kernel_map_transport_forward P
      (restricted_kernel_map_transport_backward P T'))
    T'.
Proof.
  intros k' Hk'.
  change
    (lmap (iso_forward (pi_claim P))
      (lmap (iso_backward (pi_claim P))
        (from_map T'
          (lmap (iso_forward (pi_state P))
            (lmap (iso_backward (pi_state P)) k'))))
     = from_map T' k').
  rewrite (iso_right_inverse (pi_state P) k').
  apply (iso_right_inverse (pi_claim P) (from_map T' k')).
Qed.

(** ** Part IV: Transport of the actual descent-defect map *)

Theorem descent_defect_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  same_from_map
    (restricted_kernel_map_transport_forward P
      (descent_defect_map (inst_D I) (inst_L I)))
    (descent_defect_map (inst_D I') (inst_L I')).
Proof.
  intros k' Hk'.
  change
    (lmap (iso_forward (pi_claim P))
      (lmap (inst_L I) (lmap (iso_backward (pi_state P)) k'))
     = lmap (inst_L I') k').
  pose proof (pi_L_square P (lmap (iso_backward (pi_state P)) k')
    : lmap (iso_forward (pi_claim P))
        (lmap (inst_L I) (lmap (iso_backward (pi_state P)) k'))
      = lmap (inst_L I')
          (lmap (iso_forward (pi_state P))
            (lmap (iso_backward (pi_state P)) k'))) as Hsq.
  rewrite Hsq.
  rewrite (iso_right_inverse (pi_state P) k').
  reflexivity.
Qed.

Theorem descent_defect_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  same_from_map
    (restricted_kernel_map_transport_backward P
      (descent_defect_map (inst_D I') (inst_L I')))
    (descent_defect_map (inst_D I) (inst_L I)).
Proof.
  exact (descent_defect_transport_forward (inverse_presentation_isomorphism P)).
Qed.

(** ** Part V: Kernel-vanishing and descent-obstruction invariance *)

Theorem presentation_isomorphism_kernel_vanishing_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  QImagePreimage.vanishes_on_kernel (inst_D I) (inst_L I)
  <->
  QImagePreimage.vanishes_on_kernel (inst_D I') (inst_L I').
Proof.
  split.
  - intros Hvan k' Hk'.
    pose proof (kernel_transport_backward_mem P k' Hk'
      : kernel (inst_D I) (lmap (iso_backward (pi_state P)) k')) as Hmem.
    pose proof (Hvan (lmap (iso_backward (pi_state P)) k') Hmem) as Hz.
    pose proof (descent_defect_transport_forward P k' Hk') as Htrk.
    change
      (lmap (iso_forward (pi_claim P))
        (lmap (inst_L I) (lmap (iso_backward (pi_state P)) k'))
       = lmap (inst_L I') k')
      in Htrk.
    rewrite Hz in Htrk.
    rewrite <- Htrk.
    apply (lmap_preserves_zero (iso_forward (pi_claim P))).
  - intros Hvan' k Hk.
    pose proof (kernel_transport_forward_mem P k Hk
      : kernel (inst_D I') (lmap (iso_forward (pi_state P)) k)) as Hmem'.
    pose proof (Hvan' (lmap (iso_forward (pi_state P)) k) Hmem') as Hz'.
    pose proof (descent_defect_transport_forward P
                  (lmap (iso_forward (pi_state P)) k) Hmem') as Htrk'.
    change
      (lmap (iso_forward (pi_claim P))
        (lmap (inst_L I)
          (lmap (iso_backward (pi_state P)) (lmap (iso_forward (pi_state P)) k)))
       = lmap (inst_L I') (lmap (iso_forward (pi_state P)) k))
      in Htrk'.
    rewrite (iso_left_inverse (pi_state P) k) in Htrk'.
    rewrite Hz' in Htrk'.
    apply (linear_isomorphism_forward_zero_iff (pi_claim P) (lmap (inst_L I) k)).
    exact Htrk'.
Qed.

(** ** Part VI: Transport of ambient factor maps *)

Definition factor_map_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (M : QLinearMap nV nW)
    : QLinearMap nV' nW' :=
  compose_lmap
    (compose_lmap (iso_backward (pi_residual P)) M)
    (iso_forward (pi_claim P)).

Definition factor_map_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (M' : QLinearMap nV' nW')
    : QLinearMap nV nW :=
  factor_map_transport_forward (inverse_presentation_isomorphism P) M'.

Theorem factor_map_transport_forward_factorises
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (M : QLinearMap nV nW) :
  same_lmap (inst_L I) (precompose (inst_D I) M) ->
  same_lmap
    (inst_L I')
    (precompose (inst_D I') (factor_map_transport_forward P M)).
Proof.
  intros HM u'.
  change
    (lmap (inst_L I') u'
     = lmap (iso_forward (pi_claim P))
         (lmap M (lmap (iso_backward (pi_residual P)) (lmap (inst_D I') u')))).
  pose proof (presentation_isomorphism_reverse_D_square P u'
    : lmap (iso_backward (pi_residual P)) (lmap (inst_D I') u')
      = lmap (inst_D I) (lmap (iso_backward (pi_state P)) u')) as Hrev.
  rewrite Hrev.
  pose proof (HM (lmap (iso_backward (pi_state P)) u')
    : lmap (inst_L I) (lmap (iso_backward (pi_state P)) u')
      = lmap M (lmap (inst_D I) (lmap (iso_backward (pi_state P)) u'))) as HMv.
  rewrite <- HMv.
  pose proof (pi_L_square P (lmap (iso_backward (pi_state P)) u')
    : lmap (iso_forward (pi_claim P))
        (lmap (inst_L I) (lmap (iso_backward (pi_state P)) u'))
      = lmap (inst_L I')
          (lmap (iso_forward (pi_state P))
            (lmap (iso_backward (pi_state P)) u'))) as Hsq.
  rewrite Hsq.
  rewrite (iso_right_inverse (pi_state P) u').
  reflexivity.
Qed.

Theorem factor_map_transport_backward_factorises
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (M' : QLinearMap nV' nW') :
  same_lmap (inst_L I') (precompose (inst_D I') M') ->
  same_lmap
    (inst_L I)
    (precompose (inst_D I) (factor_map_transport_backward P M')).
Proof.
  intro HM'.
  exact (factor_map_transport_forward_factorises
           (inverse_presentation_isomorphism P) M' HM').
Qed.

Theorem presentation_isomorphism_precomposition_image_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  precomposition_image (inst_D I) (inst_L I)
  <->
  precomposition_image (inst_D I') (inst_L I').
Proof.
  split.
  - intros [M HM].
    exists (factor_map_transport_forward P M).
    exact (factor_map_transport_forward_factorises P M HM).
  - intros [M' HM'].
    exists (factor_map_transport_backward P M').
    exact (factor_map_transport_backward_factorises P M' HM').
Qed.

Theorem presentation_isomorphism_descent_obstruction_zero_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  descent_obstruction_zero (inst_D I) (inst_L I)
  <->
  descent_obstruction_zero (inst_D I') (inst_L I').
Proof.
  exact (presentation_isomorphism_precomposition_image_iff P).
Qed.

Theorem presentation_isomorphism_descent_obstructed_iff
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  descent_obstructed (inst_D I) (inst_L I)
  <->
  descent_obstructed (inst_D I') (inst_L I').
Proof.
  unfold descent_obstructed.
  split.
  - intros Hn Hz.
    apply Hn.
    apply (presentation_isomorphism_descent_obstruction_zero_iff P).
    exact Hz.
  - intros Hn Hz.
    apply Hn.
    apply (presentation_isomorphism_descent_obstruction_zero_iff P).
    exact Hz.
Qed.

(** ** Part VII: Gauge-witness transport *)

Definition gauge_transport_forward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k : QVec nU)
    : QVec nU' :=
  lmap (iso_forward (pi_state P)) k.

Definition gauge_transport_backward
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k' : QVec nU')
    : QVec nU :=
  lmap (iso_backward (pi_state P)) k'.

Theorem gauge_transport_forward_witness
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k : QVec nU) :
  gauge_witness (inst_D I) (inst_L I) k ->
  gauge_witness (inst_D I') (inst_L I') (gauge_transport_forward P k).
Proof.
  intros [Hk Hne].
  split.
  - exact (kernel_transport_forward_mem P k Hk).
  - change (lmap (inst_L I') (lmap (iso_forward (pi_state P)) k) <> zero_vec nW').
    pose proof (presentation_morphism_claim_transport
                   (presentation_isomorphism_forward_morphism P) k
      : lmap (inst_L I') (lmap (iso_forward (pi_state P)) k)
        = lmap (iso_forward (pi_claim P)) (lmap (inst_L I) k)) as Hct.
    rewrite Hct.
    apply (linear_isomorphism_forward_nonzero_iff (pi_claim P) (lmap (inst_L I) k)).
    exact Hne.
Qed.

Theorem gauge_transport_backward_witness
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k' : QVec nU') :
  gauge_witness (inst_D I') (inst_L I') k' ->
  gauge_witness (inst_D I) (inst_L I) (gauge_transport_backward P k').
Proof.
  exact (gauge_transport_forward_witness (inverse_presentation_isomorphism P) k').
Qed.

(** ** Part VIII: Concrete probes *)

Example kernel_transport_forward_application_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k : QVec nU) :
  from_map (kernel_transport_forward P) k
  = lmap (iso_forward (pi_state P)) k.
Proof.
  reflexivity.
Qed.

Example descent_defect_transport_forward_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  same_from_map
    (restricted_kernel_map_transport_forward P
      (descent_defect_map (inst_D I) (inst_L I)))
    (descent_defect_map (inst_D I') (inst_L I')).
Proof.
  apply descent_defect_transport_forward.
Qed.

Example factor_map_transport_forward_application_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (M : QLinearMap nV nW)
    (y' : QVec nV') :
  lmap (factor_map_transport_forward P M) y'
  = lmap
      (iso_forward (pi_claim P))
      (lmap M (lmap (iso_backward (pi_residual P)) y')).
Proof.
  reflexivity.
Qed.

Example gauge_transport_forward_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (k : QVec nU)
    (Hk : gauge_witness (inst_D I) (inst_L I) k) :
  gauge_witness (inst_D I') (inst_L I') (gauge_transport_forward P k).
Proof.
  apply gauge_transport_forward_witness.
  exact Hk.
Qed.
