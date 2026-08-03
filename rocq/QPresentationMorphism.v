(** * Presentation morphisms between lift-descent instances

    A presentation morphism transforms one complete instance
    [(I, r) = (U, V, W, D, r, L)] into another, [(I', r')], via three
    linear maps [a : U -> U'], [b : V -> V'], [c : W -> W'] that
    preserve the repair equation, the distinguished residue, and the
    interpretation of claims:

    [[
      b D = D' a,    b r = r',    c L = L' a.
    ]]

    The residue [r] is deliberately not a field of [LinearInstance]
    (see [LinearInstance.v]'s own note on why): the same presentation
    [(D, L)] is queried against a varying residue, so a morphism
    between complete instances is indexed by [I], [r], [I'], [r']
    separately, not by a new record bundling all three together. This
    unit does not touch [LinearInstance.v], and does not introduce any
    competing instance wrapper.

    Compatibility is stated with [same_lmap] — pointwise function
    equality — exactly as [QLinearIsomorphism.v] does for its own
    identity and associativity laws, and for the same reason:
    [QLinearMap] records carry [lmap_add]/[lmap_scale] proof fields,
    so Leibniz equality between them would compare those proofs too.
    [compose_lmap F G] retains Unit 25a's fixed convention: apply [F]
    first, then [G], so [compose_lmap D b] reads as [b after D] and
    [compose_lmap a D'] reads as [D' after a] — the commuting squares
    above are written accordingly.

    [PresentationIsomorphism] stores only the three forward
    compatibility equations, not their reverse counterparts. The
    reverse square [b^{-1} D' = D a^{-1}], the reverse residue
    equation [b^{-1} r' = r], and the reverse claim square
    [c^{-1} L' = L a^{-1}] are all derived below from the forward
    equations together with the [iso_left_inverse]/[iso_right_inverse]
    laws Unit 25a's [QLinearIsomorphism] already supplies — storing
    them as additional fields would duplicate proof obligations that
    are already fully determined by the forward data.

    This unit supplies morphism algebra and elementary witness-level
    transport (repairs, kernel vectors) only. It does not transport
    obstruction spaces, separator witnesses, gauge witnesses, or
    factor maps, and it does not itself establish R9 — those begin in
    Units 26a, 26b, and 27. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QLinearIsomorphism.

Open Scope Qc_scope.

(** ** Part I: Presentation morphisms *)

Record PresentationMorphism
    {nU nV nW nU' nV' nW' : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV)
    (I' : LinearInstance nU' nV' nW')
    (r' : QVec nV')
    : Type := mkPresentationMorphism {

  pm_state :
    QLinearMap nU nU';

  pm_residual :
    QLinearMap nV nV';

  pm_claim :
    QLinearMap nW nW';

  pm_D_square :
    same_lmap
      (compose_lmap (inst_D I) pm_residual)
      (compose_lmap pm_state (inst_D I'));

  pm_residue_preserved :
    lmap pm_residual r = r';

  pm_L_square :
    same_lmap
      (compose_lmap (inst_L I) pm_claim)
      (compose_lmap pm_state (inst_L I'))
}.

Arguments pm_state {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pm_residual {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pm_claim {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pm_D_square {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pm_residue_preserved {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pm_L_square {nU nV nW nU' nV' nW' I r I' r'}.

Definition identity_presentation_morphism
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV)
    : PresentationMorphism I r I r.
Proof.
  refine {|
    pm_state := identity_lmap nU;
    pm_residual := identity_lmap nV;
    pm_claim := identity_lmap nW;
    pm_D_square := _;
    pm_residue_preserved := _;
    pm_L_square := _;
  |}.
  - intro u. reflexivity.
  - reflexivity.
  - intro u. reflexivity.
Defined.

Definition compose_presentation_morphism
    {nU0 nV0 nW0 nU1 nV1 nW1 nU2 nV2 nW2 : nat}
    {I0 : LinearInstance nU0 nV0 nW0}
    {r0 : QVec nV0}
    {I1 : LinearInstance nU1 nV1 nW1}
    {r1 : QVec nV1}
    {I2 : LinearInstance nU2 nV2 nW2}
    {r2 : QVec nV2}
    (P : PresentationMorphism I0 r0 I1 r1)
    (Q : PresentationMorphism I1 r1 I2 r2)
    : PresentationMorphism I0 r0 I2 r2.
Proof.
  refine {|
    pm_state := compose_lmap (pm_state P) (pm_state Q);
    pm_residual := compose_lmap (pm_residual P) (pm_residual Q);
    pm_claim := compose_lmap (pm_claim P) (pm_claim Q);
    pm_D_square := _;
    pm_residue_preserved := _;
    pm_L_square := _;
  |}.
  - intro u.
    transitivity
      (lmap (pm_residual Q) (lmap (inst_D I1) (lmap (pm_state P) u))).
    + exact (f_equal (lmap (pm_residual Q)) (pm_D_square P u)).
    + exact (pm_D_square Q (lmap (pm_state P) u)).
  - transitivity (lmap (pm_residual Q) r1).
    + exact (f_equal (lmap (pm_residual Q)) (pm_residue_preserved P)).
    + exact (pm_residue_preserved Q).
  - intro u.
    transitivity
      (lmap (pm_claim Q) (lmap (inst_L I1) (lmap (pm_state P) u))).
    + exact (f_equal (lmap (pm_claim Q)) (pm_L_square P u)).
    + exact (pm_L_square Q (lmap (pm_state P) u)).
Defined.

(** ** Part II: Pointwise transport equations *)

Theorem presentation_morphism_D_transport
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (u : QVec nU) :
  lmap (inst_D I') (lmap (pm_state P) u)
  = lmap (pm_residual P) (lmap (inst_D I) u).
Proof.
  symmetry.
  exact (pm_D_square P u).
Qed.

Theorem presentation_morphism_claim_transport
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (u : QVec nU) :
  lmap (inst_L I') (lmap (pm_state P) u)
  = lmap (pm_claim P) (lmap (inst_L I) u).
Proof.
  symmetry.
  exact (pm_L_square P u).
Qed.

(** ** Part III: Elementary forward transport *)

Theorem presentation_morphism_repair_transport
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (u : QVec nU) :
  repair_fibre (inst_D I) r u ->
  repair_fibre (inst_D I') r' (lmap (pm_state P) u).
Proof.
  intro Hu.
  unfold repair_fibre in *.
  rewrite (presentation_morphism_D_transport P u).
  rewrite Hu.
  exact (pm_residue_preserved P).
Qed.

Theorem presentation_morphism_kernel_transport
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (k : QVec nU) :
  kernel (inst_D I) k ->
  kernel (inst_D I') (lmap (pm_state P) k).
Proof.
  intro Hk.
  unfold kernel in *.
  rewrite (presentation_morphism_D_transport P k).
  rewrite Hk.
  apply (lmap_preserves_zero (pm_residual P)).
Qed.

(** ** Part IV: Presentation isomorphisms *)

Record PresentationIsomorphism
    {nU nV nW nU' nV' nW' : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV)
    (I' : LinearInstance nU' nV' nW')
    (r' : QVec nV')
    : Type := mkPresentationIsomorphism {

  pi_state :
    QLinearIsomorphism nU nU';

  pi_residual :
    QLinearIsomorphism nV nV';

  pi_claim :
    QLinearIsomorphism nW nW';

  pi_D_square :
    same_lmap
      (compose_lmap
        (inst_D I)
        (iso_forward pi_residual))
      (compose_lmap
        (iso_forward pi_state)
        (inst_D I'));

  pi_residue_preserved :
    lmap (iso_forward pi_residual) r = r';

  pi_L_square :
    same_lmap
      (compose_lmap
        (inst_L I)
        (iso_forward pi_claim))
      (compose_lmap
        (iso_forward pi_state)
        (inst_L I'))
}.

Arguments pi_state {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pi_residual {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pi_claim {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pi_D_square {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pi_residue_preserved {nU nV nW nU' nV' nW' I r I' r'}.
Arguments pi_L_square {nU nV nW nU' nV' nW' I r I' r'}.

Definition presentation_isomorphism_forward_morphism
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    : PresentationMorphism I r I' r' :=
  {|
    pm_state := iso_forward (pi_state P);
    pm_residual := iso_forward (pi_residual P);
    pm_claim := iso_forward (pi_claim P);
    pm_D_square := pi_D_square P;
    pm_residue_preserved := pi_residue_preserved P;
    pm_L_square := pi_L_square P;
  |}.

(** ** Part V: Derived reverse compatibility *)

Theorem presentation_isomorphism_reverse_D_square
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  same_lmap
    (compose_lmap
      (inst_D I')
      (iso_backward (pi_residual P)))
    (compose_lmap
      (iso_backward (pi_state P))
      (inst_D I)).
Proof.
  intro u'.
  set (v := lmap (iso_backward (pi_state P)) u').
  pose proof (iso_right_inverse (pi_state P) u'
    : lmap (iso_forward (pi_state P)) v = u') as Hfwd.
  pose proof (pi_D_square P v
    : lmap (iso_forward (pi_residual P)) (lmap (inst_D I) v)
      = lmap (inst_D I') (lmap (iso_forward (pi_state P)) v)) as Hsquare.
  rewrite Hfwd in Hsquare.
  pose proof (iso_left_inverse (pi_residual P) (lmap (inst_D I) v)
    : lmap (iso_backward (pi_residual P))
        (lmap (iso_forward (pi_residual P)) (lmap (inst_D I) v))
      = lmap (inst_D I) v) as Hback.
  rewrite Hsquare in Hback.
  exact Hback.
Qed.

Theorem presentation_isomorphism_reverse_residue
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  lmap (iso_backward (pi_residual P)) r' = r.
Proof.
  pose proof (pi_residue_preserved P
    : lmap (iso_forward (pi_residual P)) r = r') as Hr.
  transitivity
    (lmap (iso_backward (pi_residual P))
      (lmap (iso_forward (pi_residual P)) r)).
  - f_equal. symmetry. exact Hr.
  - apply (iso_left_inverse (pi_residual P)).
Qed.

Theorem presentation_isomorphism_reverse_L_square
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r') :
  same_lmap
    (compose_lmap
      (inst_L I')
      (iso_backward (pi_claim P)))
    (compose_lmap
      (iso_backward (pi_state P))
      (inst_L I)).
Proof.
  intro u'.
  set (v := lmap (iso_backward (pi_state P)) u').
  pose proof (iso_right_inverse (pi_state P) u'
    : lmap (iso_forward (pi_state P)) v = u') as Hfwd.
  pose proof (pi_L_square P v
    : lmap (iso_forward (pi_claim P)) (lmap (inst_L I) v)
      = lmap (inst_L I') (lmap (iso_forward (pi_state P)) v)) as Hsquare.
  rewrite Hfwd in Hsquare.
  pose proof (iso_left_inverse (pi_claim P) (lmap (inst_L I) v)
    : lmap (iso_backward (pi_claim P))
        (lmap (iso_forward (pi_claim P)) (lmap (inst_L I) v))
      = lmap (inst_L I) v) as Hback.
  rewrite Hsquare in Hback.
  exact Hback.
Qed.

(** ** Part VI: Inverse and reverse constructions *)

Definition inverse_presentation_isomorphism
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    : PresentationIsomorphism I' r' I r :=
  {|
    pi_state := inverse_linear_isomorphism (pi_state P);
    pi_residual := inverse_linear_isomorphism (pi_residual P);
    pi_claim := inverse_linear_isomorphism (pi_claim P);
    pi_D_square := presentation_isomorphism_reverse_D_square P;
    pi_residue_preserved := presentation_isomorphism_reverse_residue P;
    pi_L_square := presentation_isomorphism_reverse_L_square P;
  |}.

Definition presentation_isomorphism_reverse_morphism
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    : PresentationMorphism I' r' I r :=
  presentation_isomorphism_forward_morphism
    (inverse_presentation_isomorphism P).

(** ** Part VII: Identity and composition of presentation isomorphisms *)

Definition identity_presentation_isomorphism
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV)
    : PresentationIsomorphism I r I r.
Proof.
  refine {|
    pi_state := identity_linear_isomorphism nU;
    pi_residual := identity_linear_isomorphism nV;
    pi_claim := identity_linear_isomorphism nW;
    pi_D_square := _;
    pi_residue_preserved := _;
    pi_L_square := _;
  |}.
  - intro u. reflexivity.
  - reflexivity.
  - intro u. reflexivity.
Defined.

Definition compose_presentation_isomorphism
    {nU0 nV0 nW0 nU1 nV1 nW1 nU2 nV2 nW2 : nat}
    {I0 : LinearInstance nU0 nV0 nW0}
    {r0 : QVec nV0}
    {I1 : LinearInstance nU1 nV1 nW1}
    {r1 : QVec nV1}
    {I2 : LinearInstance nU2 nV2 nW2}
    {r2 : QVec nV2}
    (P : PresentationIsomorphism I0 r0 I1 r1)
    (Q : PresentationIsomorphism I1 r1 I2 r2)
    : PresentationIsomorphism I0 r0 I2 r2.
Proof.
  refine {|
    pi_state := compose_linear_isomorphism (pi_state P) (pi_state Q);
    pi_residual := compose_linear_isomorphism (pi_residual P) (pi_residual Q);
    pi_claim := compose_linear_isomorphism (pi_claim P) (pi_claim Q);
    pi_D_square := _;
    pi_residue_preserved := _;
    pi_L_square := _;
  |}.
  - intro u.
    transitivity
      (lmap (iso_forward (pi_residual Q))
        (lmap (inst_D I1) (lmap (iso_forward (pi_state P)) u))).
    + exact (f_equal (lmap (iso_forward (pi_residual Q))) (pi_D_square P u)).
    + exact (pi_D_square Q (lmap (iso_forward (pi_state P)) u)).
  - transitivity (lmap (iso_forward (pi_residual Q)) r1).
    + exact (f_equal (lmap (iso_forward (pi_residual Q))) (pi_residue_preserved P)).
    + exact (pi_residue_preserved Q).
  - intro u.
    transitivity
      (lmap (iso_forward (pi_claim Q))
        (lmap (inst_L I1) (lmap (iso_forward (pi_state P)) u))).
    + exact (f_equal (lmap (iso_forward (pi_claim Q))) (pi_L_square P u)).
    + exact (pi_L_square Q (lmap (iso_forward (pi_state P)) u)).
Defined.

(** ** Part VIII: Concrete probes *)

Example identity_presentation_morphism_state_probe
    {nU nV nW : nat}
    (I : LinearInstance nU nV nW)
    (r : QVec nV)
    (u : QVec nU) :
  lmap (pm_state (identity_presentation_morphism I r)) u = u.
Proof. reflexivity. Qed.

Example compose_presentation_morphism_state_probe
    {nU0 nV0 nW0 nU1 nV1 nW1 nU2 nV2 nW2 : nat}
    {I0 : LinearInstance nU0 nV0 nW0}
    {r0 : QVec nV0}
    {I1 : LinearInstance nU1 nV1 nW1}
    {r1 : QVec nV1}
    {I2 : LinearInstance nU2 nV2 nW2}
    {r2 : QVec nV2}
    (P : PresentationMorphism I0 r0 I1 r1)
    (Q : PresentationMorphism I1 r1 I2 r2)
    (u : QVec nU0) :
  lmap (pm_state (compose_presentation_morphism P Q)) u
  = lmap (pm_state Q) (lmap (pm_state P) u).
Proof. reflexivity. Qed.

Example presentation_morphism_repair_transport_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationMorphism I r I' r')
    (u : QVec nU)
    (Hu : repair_fibre (inst_D I) r u) :
  repair_fibre (inst_D I') r' (lmap (pm_state P) u).
Proof.
  apply presentation_morphism_repair_transport.
  exact Hu.
Qed.

Example inverse_presentation_isomorphism_state_probe
    {nU nV nW nU' nV' nW' : nat}
    {I : LinearInstance nU nV nW}
    {r : QVec nV}
    {I' : LinearInstance nU' nV' nW'}
    {r' : QVec nV'}
    (P : PresentationIsomorphism I r I' r')
    (u' : QVec nU') :
  lmap
    (iso_forward (pi_state (inverse_presentation_isomorphism P)))
    u'
  = lmap (iso_backward (pi_state P)) u'.
Proof. reflexivity. Qed.
