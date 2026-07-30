(** * Matrix realisation, identity, and composition

    Unit 11 established that every [QLinearMap] has a correct
    column-oriented matrix representation, [matrix_of_lmap], with
    [matrix_apply (matrix_of_lmap T) x = lmap T x]. This unit proves the
    converse direction — every [QMatrix] realises a [QLinearMap] — and
    the basic algebra ([identity_matrix], [matrix_compose]) that later
    row-operation and elimination units will need. It performs no
    elimination itself.
*)

From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.
Import VectorNotations.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QObstruction.
From LiftDescent Require Import QFiniteCoordinates.

Open Scope Qc_scope.

(** ** 1. Matrix application is linear *)

Theorem matrix_apply_zero {m n : nat} (A : QMatrix m n) :
  matrix_apply A (zero_vec n) = zero_vec m.
Proof.
  unfold matrix_apply.
  induction A as [| a n' A' IH].
  - reflexivity.
  - simpl. rewrite vscale_0_l. rewrite IH. apply vadd_0_l.
Qed.

(** [qsum_add], [map_nth_map2_vadd], and [vsum_add] are the Qc-level,
    per-column, and whole-sum forms of "sum distributes over pointwise
    addition" — needed because [vsum]/[qsum] have no [ring]-style
    automation of their own; each is proved once by structural
    induction and reused. [map2_vscale_vadd_distrib] is the pointwise
    fact [vscale (x_i + y_i) A_i = vadd (vscale x_i A_i) (vscale y_i A_i)]
    (from [vscale_add_distr_r]) lifted to whole columns, needed to
    connect [matrix_apply A (vadd x y)] to the two separate
    applications. *)

Lemma qsum_add {n : nat} (u v : Vector.t Qc n) :
  qsum (Vector.map2 Qcplus u v) = qsum u + qsum v.
Proof.
  induction u as [| a n' u' IH] in v |- *.
  - revert v. apply Vector.case0. reflexivity.
  - apply (Vector.caseS' v).
    intros b v'.
    simpl.
    rewrite IH.
    ring.
Qed.

Lemma map_nth_map2_vadd {m n : nat} (U V : Vector.t (QVec m) n) (k : Fin.t m) :
  Vector.map (fun w => Vector.nth w k) (Vector.map2 vadd U V)
  = Vector.map2 Qcplus (Vector.map (fun w => Vector.nth w k) U)
      (Vector.map (fun w => Vector.nth w k) V).
Proof.
  induction U as [| u n' U' IH] in V |- *.
  - revert V. apply Vector.case0. reflexivity.
  - apply (Vector.caseS' V).
    intros v V'.
    simpl.
    rewrite vadd_nth.
    rewrite IH.
    reflexivity.
Qed.

Lemma vsum_add {m n : nat} (U V : Vector.t (QVec m) n) :
  vsum (Vector.map2 vadd U V) = vadd (vsum U) (vsum V).
Proof.
  apply vec_ext.
  intros k.
  rewrite vadd_nth.
  rewrite !vsum_nth.
  rewrite map_nth_map2_vadd.
  apply qsum_add.
Qed.

Lemma map2_vscale_vadd_distrib {m n : nat} (x y : QVec n) (A : QMatrix m n) :
  Vector.map2 vscale (vadd x y) A
  = Vector.map2 vadd (Vector.map2 vscale x A) (Vector.map2 vscale y A).
Proof.
  induction x as [| hx n' x' IH] in y, A |- *.
  - revert A.
    apply (Vector.case0 (A := QVec m)).
    revert y.
    apply (Vector.case0 (A := Qc)).
    reflexivity.
  - apply (Vector.caseS' y).
    intros hy y'.
    apply (Vector.caseS' A).
    intros ha A'.
    simpl.
    rewrite vscale_add_distr_r.
    rewrite IH.
    reflexivity.
Qed.

Theorem matrix_apply_add {m n : nat} (A : QMatrix m n) (x y : QVec n) :
  matrix_apply A (vadd x y) = vadd (matrix_apply A x) (matrix_apply A y).
Proof.
  unfold matrix_apply.
  rewrite map2_vscale_vadd_distrib.
  apply vsum_add.
Qed.

(** Same pattern as above, for scalar multiplication: [qsum_scale],
    [map_nth_map_vscale], and [vsum_scale] are "sum distributes over a
    uniform scaling"; [map2_vscale_assoc_distrib] lifts
    [vscale (a * x_i) A_i = vscale a (vscale x_i A_i)] (from
    [vscale_assoc]) to whole columns. *)

Lemma qsum_scale {n : nat} (a : Qc) (u : Vector.t Qc n) :
  qsum (Vector.map (Qcmult a) u) = a * qsum u.
Proof.
  induction u as [| x n' u' IH].
  - simpl. ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma map_nth_map_vscale {m n : nat} (a : Qc) (V : Vector.t (QVec m) n) (k : Fin.t m) :
  Vector.map (fun w => Vector.nth w k) (Vector.map (vscale a) V)
  = Vector.map (Qcmult a) (Vector.map (fun w => Vector.nth w k) V).
Proof.
  induction V as [| v n' V' IH].
  - reflexivity.
  - simpl. rewrite vscale_nth. rewrite IH. reflexivity.
Qed.

Lemma vsum_scale {m n : nat} (a : Qc) (V : Vector.t (QVec m) n) :
  vsum (Vector.map (vscale a) V) = vscale a (vsum V).
Proof.
  apply vec_ext.
  intros k.
  rewrite vscale_nth.
  rewrite !vsum_nth.
  rewrite map_nth_map_vscale.
  apply qsum_scale.
Qed.

Lemma map2_vscale_assoc_distrib {m n : nat} (a : Qc) (x : QVec n) (A : QMatrix m n) :
  Vector.map2 vscale (vscale a x) A = Vector.map (vscale a) (Vector.map2 vscale x A).
Proof.
  induction x as [| hx n' x' IH] in A |- *.
  - revert A. apply (Vector.case0 (A := QVec m)). reflexivity.
  - apply (Vector.caseS' A).
    intros ha A'.
    simpl.
    rewrite vscale_assoc.
    rewrite IH.
    reflexivity.
Qed.

Theorem matrix_apply_scale {m n : nat} (A : QMatrix m n) (a : Qc) (x : QVec n) :
  matrix_apply A (vscale a x) = vscale a (matrix_apply A x).
Proof.
  unfold matrix_apply.
  rewrite map2_vscale_assoc_distrib.
  apply vsum_scale.
Qed.

(** ** 2. Realising a matrix as a linear map

    Underlying function is exactly [matrix_apply A]; the two record
    laws are exactly [matrix_apply_add A] and [matrix_apply_scale A]. *)

Definition linear_map_of_matrix {m n : nat} (A : QMatrix m n) : QLinearMap n m :=
  {|
    lmap := matrix_apply A;
    lmap_add := matrix_apply_add A;
    lmap_scale := matrix_apply_scale A;
  |}.

(** ** 3. Matrix application selects a column

    [standard_basis_sym] and [matrix_column_eq] adapt [qsum_select_fun]
    (Unit 11) from the specific "identity-like" basis matrix to an
    arbitrary [A]. *)

Lemma standard_basis_sym {n : nat} (i j : Fin.t n) :
  Vector.nth (standard_basis i) j = Vector.nth (standard_basis j) i.
Proof.
  destruct (Fin.eq_dec i j) as [Heq | Hneq].
  - subst. reflexivity.
  - rewrite (standard_basis_nth_neq j i (fun H => Hneq (eq_sym H))).
    rewrite (standard_basis_nth_neq i j Hneq).
    reflexivity.
Qed.

Lemma matrix_column_eq {m n : nat} (A : QMatrix m n) (x : QVec n) (k : Fin.t m) :
  Vector.map (fun v => Vector.nth v k) (Vector.map2 vscale x A)
  = Vector.map (fun j => Vector.nth x j * Vector.nth (Vector.nth A j) k) (all_positions n).
Proof.
  apply vec_ext.
  intros idx.
  rewrite (Vector.nth_map _ _ idx idx eq_refl).
  rewrite (Vector.nth_map2 _ _ _ idx idx idx eq_refl eq_refl).
  rewrite vscale_nth.
  rewrite (Vector.nth_map _ _ idx idx eq_refl).
  rewrite (all_positions_nth n idx).
  reflexivity.
Qed.

Theorem matrix_apply_standard_basis {m n : nat} (A : QMatrix m n) (i : Fin.t n) :
  matrix_apply A (standard_basis i) = Vector.nth A i.
Proof.
  unfold matrix_apply.
  apply vec_ext.
  intros k.
  rewrite vsum_nth.
  rewrite matrix_column_eq.
  rewrite (Vector.map_ext _ _
             (fun j => Vector.nth (standard_basis i) j * Vector.nth (Vector.nth A j) k)
             (fun j => Vector.nth (Vector.nth A j) k * Vector.nth (standard_basis j) i)).
  - apply (qsum_select_fun i (fun j => Vector.nth (Vector.nth A j) k)).
  - intros a.
    rewrite standard_basis_sym.
    ring.
Qed.

(** ** 4. Extraction and realisation are mutually inverse *)

Theorem matrix_of_linear_map_of_matrix {m n : nat} (A : QMatrix m n) :
  matrix_of_lmap (linear_map_of_matrix A) = A.
Proof.
  unfold matrix_of_lmap.
  apply Vector.eq_nth_iff.
  intros p q ->.
  rewrite (Vector.nth_map _ _ q q eq_refl).
  change (matrix_apply A (standard_basis (Vector.nth (all_positions n) q)) = Vector.nth A q).
  rewrite (all_positions_nth n q).
  apply matrix_apply_standard_basis.
Qed.

Theorem linear_map_of_matrix_of_lmap {n m : nat} (T : QLinearMap n m) :
  same_lmap (linear_map_of_matrix (matrix_of_lmap T)) T.
Proof.
  unfold same_lmap.
  intros x.
  apply matrix_of_lmap_correct.
Qed.

(** ** 5. The identity matrix *)

Definition identity_matrix (n : nat) : QMatrix n n :=
  Vector.map standard_basis (all_positions n).

Theorem identity_matrix_apply {n : nat} (x : QVec n) :
  matrix_apply (identity_matrix n) x = x.
Proof.
  unfold matrix_apply, identity_matrix.
  symmetry.
  apply coordinate_expansion.
Qed.

(** ** 6. Column-oriented composition

    [matrix_compose A B]'s columns are [A] applied to [B]'s columns:
    "apply [B], then apply [A]". *)

Definition matrix_compose {p m n : nat} (A : QMatrix p m) (B : QMatrix m n) : QMatrix p n :=
  Vector.map (matrix_apply A) B.

Theorem matrix_compose_apply {p m n : nat} (A : QMatrix p m) (B : QMatrix m n) (x : QVec n) :
  matrix_apply (matrix_compose A B) x = matrix_apply A (matrix_apply B x).
Proof.
  unfold matrix_compose.
  unfold matrix_apply at 1.
  change (vsum (Vector.map2 vscale x (Vector.map (lmap (linear_map_of_matrix A)) B))
          = matrix_apply A (matrix_apply B x)).
  rewrite <- (map_lmap_map2_vscale (linear_map_of_matrix A) x B).
  rewrite <- (lmap_preserves_vsum (linear_map_of_matrix A) (Vector.map2 vscale x B)).
  reflexivity.
Qed.

(** ** 7. Identity laws *)

Theorem matrix_compose_identity_left {m n : nat} (A : QMatrix m n) :
  matrix_compose (identity_matrix m) A = A.
Proof.
  unfold matrix_compose.
  rewrite (Vector.map_ext _ _ (matrix_apply (identity_matrix m)) (fun v => v) identity_matrix_apply).
  apply Vector.map_id.
Qed.

Lemma map_nth_all_positions {X : Type} {n : nat} (v : Vector.t X n) :
  Vector.map (Vector.nth v) (all_positions n) = v.
Proof.
  apply Vector.eq_nth_iff.
  intros p q ->.
  rewrite (Vector.nth_map _ _ q q eq_refl).
  rewrite (all_positions_nth n q).
  reflexivity.
Qed.

Theorem matrix_compose_identity_right {m n : nat} (A : QMatrix m n) :
  matrix_compose A (identity_matrix n) = A.
Proof.
  unfold matrix_compose, identity_matrix.
  rewrite (Vector.map_map _ _ _ standard_basis (matrix_apply A)).
  rewrite (Vector.map_ext _ _
             (fun i => matrix_apply A (standard_basis i))
             (Vector.nth A)
             (matrix_apply_standard_basis A)).
  apply map_nth_all_positions.
Qed.
