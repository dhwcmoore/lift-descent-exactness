(** * Constructive gauge-witness extraction and R5

    Unit 20a constructed the kernel projection [K_D] and its finite
    family of projected standard-basis generators [g_i = K_D(e_i)].
    The first portion of Unit 20b ([QKernelSpanning.v]) proved that
    those generators span exactly [ker D], and reduced universal
    vanishing of a linear functional [L] on all of [ker D] to finitely
    many generator checks
    ([kernel_zero_iff_kernel_generators_zero]).

    What remains is a single constructive step: turning failure of
    that finite universal check into a particular generator index. The
    scalars are [Qc], whose equality is decidable
    ([Qc_eq_dec]), so a finite [QVec w]-valued family (indexed by
    [Fin.t u], itself finite) either vanishes everywhere or has some
    entry that does not — and a witnessing index can be produced by
    finite structural search, with no non-constructive step anywhere
    in the argument.

    The generator located this way lies in [ker D] by construction
    (Unit 20a's [kernel_generator_in_kernel]), and its non-vanishing
    image under [L] makes it exactly the gauge witness R5 asks for: a
    kernel direction whose claim value moves. Soundness (every gauge
    witness defeats kernel vanishing, hence obstructs descent) and this
    constructive completeness (every descent obstruction produces a
    gauge witness) together give the R5 equivalence, connected to the
    repository's [descent_obstructed] predicate through the existing
    R2 bridge [descent_obstructed_iff_not_kernel_vanishing] — reused,
    not reproved.

    This unit does NOT prove or construct: a basis of [ker D]; linear
    independence of the kernel generators; minimality of the generator
    family; rank-nullity; the dimension of [ker D]; a normalised gauge
    witness; a unique or canonical gauge witness; the first non-zero
    generator under a specified ordering; a Boolean or extracted
    executable search interface; a basis of the ambiguity space
    [L(ker D)]; the dimension of [L(ker D)]; a quotient representation
    of the descent cokernel; separator witnesses; verdict
    classification; verdict exclusivity or completeness; the
    four-sector exactness profile; canonical exact values; the
    universal exact quotient; realisability-obstruction-class or
    presented-claim-equivalence instantiation; certificate,
    serialisation, JSON, command-line, or executable semantics; or any
    generalisation beyond finite rational coordinate spaces. The
    generator index this unit's search happens to return is not
    claimed to be canonical or independent of the underlying
    elimination order — only that it is a genuine witness. *)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.

From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QImagePreimage.
From LiftDescent Require Import QDescentFactorisation.
From LiftDescent Require Import QKernelProjection.
From LiftDescent Require Import QKernelSpanning.

Open Scope Qc_scope.

(** ** Part I: Gauge-witness predicate and finite generator images *)

Definition gauge_witness
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (k : QVec u)
    : Prop :=
  kernel D k /\
  lmap L k <> zero_vec w.

Definition gauge_generator_images
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    : Vector.t (QVec w) u :=
  Vector.map
    (fun k => lmap L k)
    (kernel_generators D).

Theorem gauge_generator_images_nth
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (i : Fin.t u) :
  Vector.nth (gauge_generator_images D L) i =
  lmap L (kernel_generator D i).
Proof.
  unfold gauge_generator_images.
  rewrite (Vector.nth_map _ _ i i eq_refl).
  rewrite (kernel_generators_nth D i).
  reflexivity.
Qed.

(** ** Part II: Constructive finite extraction

    [qvec_zero_dec] decides equality of a finite [Qc] vector with
    [zero_vec], by structural recursion using [Qc_eq_dec] at each
    coordinate — no non-constructive decision procedure. It is local to
    this file because it is a proof-engineering step, not a public
    interface: the public search result is
    [finite_vector_family_not_all_zero_has_nonzero] below. *)

Let qvec_zero_dec {p : nat} (x : QVec p) : {x = zero_vec p} + {x <> zero_vec p}.
Proof.
  induction x as [| a p' x' IH].
  - left. apply vec_ext. intro i. inversion i.
  - destruct (Qc_eq_dec a 0) as [Ha | Ha].
    + destruct IH as [IH | IH].
      * left. apply vec_ext. intro i.
        pattern i. apply Fin.caseS'.
        -- simpl. exact Ha.
        -- intro j. simpl. rewrite zero_vec_nth, IH. apply zero_vec_nth.
      * right. intro Heq. apply IH. apply vec_ext. intro i.
        assert (Hi : Vector.nth (Vector.cons Qc a p' x') (Fin.FS i)
                     = Vector.nth (zero_vec (S p')) (Fin.FS i))
          by (rewrite Heq; reflexivity).
        simpl in Hi. exact Hi.
    + right. intro Heq. apply Ha.
      assert (Hi : Vector.nth (Vector.cons Qc a p' x') Fin.F1
                   = Vector.nth (zero_vec (S p')) Fin.F1)
        by (rewrite Heq; reflexivity).
      simpl in Hi. exact Hi.
Qed.

Lemma finite_vector_family_not_all_zero_has_nonzero
    {p n : nat}
    (vectors : Vector.t (QVec p) n) :
  ~ (forall i : Fin.t n,
       Vector.nth vectors i = zero_vec p) ->
  exists i : Fin.t n,
    Vector.nth vectors i <> zero_vec p.
Proof.
  induction vectors as [| head n' tail IH].
  - intro Hcontra. exfalso. apply Hcontra. intro i. inversion i.
  - intro Hcontra.
    destruct (qvec_zero_dec head) as [Hz | Hnz].
    + assert (Htail : ~ forall i : Fin.t n', Vector.nth tail i = zero_vec p).
      { intro Htail_all.
        apply Hcontra.
        intro i.
        pattern i. apply Fin.caseS'.
        - simpl. exact Hz.
        - intro j. simpl. apply Htail_all. }
      destruct (IH Htail) as [j Hj].
      exists (Fin.FS j). simpl. exact Hj.
    + exists Fin.F1. simpl. exact Hnz.
Qed.

Theorem not_kernel_generators_zero_has_nonzero_generator
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  ~ (forall i : Fin.t u,
       lmap L (kernel_generator D i) = zero_vec w) ->
  exists i : Fin.t u,
    lmap L (kernel_generator D i) <> zero_vec w.
Proof.
  intro Hnot.
  assert (Hnot' : ~ forall i : Fin.t u,
                     Vector.nth (gauge_generator_images D L) i = zero_vec w).
  { intro Hall. apply Hnot. intro i.
    rewrite <- (gauge_generator_images_nth D L i). apply Hall. }
  destruct (finite_vector_family_not_all_zero_has_nonzero
              (gauge_generator_images D L) Hnot') as [i Hi].
  exists i. rewrite (gauge_generator_images_nth D L i) in Hi. exact Hi.
Qed.

Theorem nonzero_generator_image_implies_nonzero_generator
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (i : Fin.t u) :
  lmap L (kernel_generator D i) <> zero_vec w ->
  kernel_generator D i <> zero_vec u.
Proof.
  intros Hne Heq.
  apply Hne.
  rewrite Heq.
  apply lmap_preserves_zero.
Qed.

Theorem nonzero_kernel_generator_of_not_kernel_vanishing
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  ~ QImagePreimage.vanishes_on_kernel D L ->
  exists i : Fin.t u,
    kernel_generator D i <> zero_vec u /\
    gauge_witness D L (kernel_generator D i).
Proof.
  intro Hnot.
  assert (Hnot_generators :
            ~ forall i : Fin.t u, lmap L (kernel_generator D i) = zero_vec w).
  { intro Hall.
    apply Hnot.
    unfold QImagePreimage.vanishes_on_kernel.
    apply (kernel_zero_iff_kernel_generators_zero D L).
    exact Hall. }
  destruct (not_kernel_generators_zero_has_nonzero_generator D L Hnot_generators)
    as [i Hi].
  exists i.
  split.
  - apply (nonzero_generator_image_implies_nonzero_generator D L i Hi).
  - split.
    + apply kernel_generator_in_kernel.
    + exact Hi.
Qed.

(** ** Part III: Gauge-witness soundness and completeness *)

Theorem gauge_witness_not_kernel_vanishing
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (k : QVec u) :
  gauge_witness D L k ->
  ~ QImagePreimage.vanishes_on_kernel D L.
Proof.
  intros [Hk Hne] Hvan.
  apply Hne.
  apply Hvan.
  exact Hk.
Qed.

Theorem gauge_witness_sound
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (k : QVec u) :
  gauge_witness D L k ->
  descent_obstructed D L.
Proof.
  intro Hgw.
  apply (descent_obstructed_iff_not_kernel_vanishing D L).
  apply (gauge_witness_not_kernel_vanishing D L k).
  exact Hgw.
Qed.

Theorem gauge_witness_complete_from_not_kernel_vanishing
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  ~ QImagePreimage.vanishes_on_kernel D L ->
  exists k : QVec u,
    gauge_witness D L k.
Proof.
  intro Hnot.
  destruct (nonzero_kernel_generator_of_not_kernel_vanishing D L Hnot)
    as [i [_ Hgw]].
  exists (kernel_generator D i).
  exact Hgw.
Qed.

Theorem gauge_witness_complete
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  descent_obstructed D L ->
  exists k : QVec u,
    gauge_witness D L k.
Proof.
  intro Hobs.
  apply gauge_witness_complete_from_not_kernel_vanishing.
  apply (descent_obstructed_iff_not_kernel_vanishing D L).
  exact Hobs.
Qed.

(** ** Part IV: R5 equivalences *)

Theorem not_kernel_vanishing_iff_gauge_witness
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  ~ QImagePreimage.vanishes_on_kernel D L
  <->
  exists k : QVec u,
    gauge_witness D L k.
Proof.
  split.
  - apply gauge_witness_complete_from_not_kernel_vanishing.
  - intros [k Hk]. apply (gauge_witness_not_kernel_vanishing D L k). exact Hk.
Qed.

Theorem descent_obstructed_iff_gauge_witness
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w) :
  descent_obstructed D L
  <->
  exists k : QVec u,
    gauge_witness D L k.
Proof.
  split.
  - apply gauge_witness_complete.
  - intros [k Hk]. apply (gauge_witness_sound D L k). exact Hk.
Qed.

(** ** Part V: Mathematical meaning of the witness *)

Theorem gauge_witness_nonzero
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (k : QVec u) :
  gauge_witness D L k ->
  k <> zero_vec u.
Proof.
  intros [_ Hne] Heq.
  apply Hne.
  rewrite Heq.
  apply lmap_preserves_zero.
Qed.

Theorem gauge_witness_preserves_residue
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (k : QVec u) :
  gauge_witness D L k ->
  forall x : QVec u,
    lmap D (vadd x k) = lmap D x.
Proof.
  intros [Hk _] x.
  rewrite (lmap_add D x k).
  rewrite Hk.
  apply vadd_0_r.
Qed.

Theorem gauge_witness_changes_claim
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (k : QVec u) :
  gauge_witness D L k ->
  forall x : QVec u,
    lmap L (vadd x k) <> lmap L x.
Proof.
  intros [_ Hne] x Heq.
  apply Hne.
  apply vec_ext. intro i.
  assert (Hi : Vector.nth (lmap L (vadd x k)) i = Vector.nth (lmap L x) i)
    by (rewrite Heq; reflexivity).
  rewrite (lmap_add L x k) in Hi.
  rewrite vadd_nth in Hi.
  rewrite zero_vec_nth.
  assert (Hb : Vector.nth (lmap L x) i + Vector.nth (lmap L k) i
               - Vector.nth (lmap L x) i = 0) by (rewrite Hi; ring).
  rewrite <- Hb. ring.
Qed.

Theorem gauge_witness_exhibits_repair_ambiguity
    {u v w : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u w)
    (r : QVec v)
    (u0 k : QVec u) :
  repair_fibre D r u0 ->
  gauge_witness D L k ->
  repair_fibre D r (vadd u0 k) /\
  lmap L (vadd u0 k) <> lmap L u0.
Proof.
  intros Hr0 Hgw.
  split.
  - unfold repair_fibre in *.
    rewrite (gauge_witness_preserves_residue D L k Hgw u0).
    exact Hr0.
  - apply (gauge_witness_changes_claim D L k Hgw u0).
Qed.

(** ** Part VI: Concrete probes *)

(** *** 1. Zero-dimensional domain: no [Fin.t 0] index is fabricated. *)

Example probe_dim0_domain_no_gauge_witness
    {v w : nat}
    (D : QLinearMap 0 v)
    (L : QLinearMap 0 w) :
  ~ exists k : QVec 0, gauge_witness D L k.
Proof.
  intros [k [_ Hne]].
  apply Hne.
  assert (Hk : k = zero_vec 0) by (apply vec_ext; intro i; inversion i).
  rewrite Hk.
  apply lmap_preserves_zero.
Qed.

(** *** 2. Zero observation map, identity claim: [D(e_0) = 0], and
    [L(e_0) = e_0 <> 0]. *)

Example probe_zero_map_identity_claim_gauge_witness :
  gauge_witness QImagePreimage.zero_D18 QImagePreimage.id_D18
    (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc))).
Proof.
  split.
  - unfold kernel. vm_compute. reflexivity.
  - vm_compute. discriminate.
Qed.

(** *** 3. Identity observation map: [ker id_D18 = {0}], via the
    existing kernel-projection results rather than
    [identity_matrix_apply], so no additional import is needed. *)

Example probe_identity_no_gauge_witness
    (L : QLinearMap 2 2) :
  ~ exists k : QVec 2, gauge_witness QImagePreimage.id_D18 L k.
Proof.
  intros [k [Hk Hne]].
  apply Hne.
  assert (Hzero : k = zero_vec 2).
  { rewrite <- (kernel_projection_fixes_kernel QImagePreimage.id_D18 k Hk).
    apply probe_identity_projection_is_zero. }
  rewrite Hzero.
  apply lmap_preserves_zero.
Qed.

(** *** 4. Proper projection, exact claim: [L_map] already vanishes on
    [ker proj_D]. *)

Example probe_proper_projection_exact_claim_no_gauge_witness :
  ~ exists k : QVec 2,
      gauge_witness QImagePreimage.proj_D QImagePreimage.L_map k.
Proof.
  intros [k Hk].
  apply (gauge_witness_not_kernel_vanishing
           QImagePreimage.proj_D QImagePreimage.L_map k Hk).
  apply QImagePreimage.probe_proj_kernel_vanishing.
Qed.

(** *** 5a. Proper projection, ambiguous claim: the explicit kernel
    witness [(0,1)] is already a gauge witness. *)

Example probe_proper_projection_explicit_gauge_witness :
  gauge_witness QImagePreimage.proj_D QImagePreimage.Lp_map
    QImagePreimage.kernel_witness.
Proof.
  split.
  - apply QImagePreimage.probe_kernel_witness_in_kernel.
  - vm_compute. discriminate.
Qed.

(** *** 5b. Proper projection, ambiguous claim: the same case,
    reached instead by the new finite constructive search, not by
    supplying the known witness directly. *)

Example probe_proper_projection_generator_extraction :
  exists i : Fin.t 2,
    kernel_generator QImagePreimage.proj_D i <> zero_vec 2 /\
    gauge_witness QImagePreimage.proj_D QImagePreimage.Lp_map
      (kernel_generator QImagePreimage.proj_D i).
Proof.
  apply nonzero_kernel_generator_of_not_kernel_vanishing.
  apply QImagePreimage.probe_Lp_not_kernel_vanishing.
Qed.

(** *** 6. Zero-dimensional claim space: no non-zero image is
    possible. *)

Example probe_dim0_claim_no_gauge_witness
    {u v : nat}
    (D : QLinearMap u v)
    (L : QLinearMap u 0) :
  ~ exists k : QVec u, gauge_witness D L k.
Proof.
  intros [k [_ Hne]].
  apply Hne.
  apply vec_ext. intro i. inversion i.
Qed.
