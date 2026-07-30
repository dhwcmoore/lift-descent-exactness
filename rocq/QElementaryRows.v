From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.
Import VectorNotations.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QFiniteCoordinates.
From LiftDescent Require Import QMatrixAlgebra.

Open Scope Qc_scope.

Definition swap_entries {n : nat} (i j : Fin.t n) (x : QVec n) : QVec n :=
  Vector.replace (Vector.replace x i (Vector.nth x j)) j (Vector.nth x i).

Definition scale_entry {n : nat} (i : Fin.t n) (a : Qc) (x : QVec n) : QVec n :=
  Vector.replace x i (a * Vector.nth x i).

Definition add_scaled_entry {n : nat} (target source : Fin.t n) (a : Qc) (x : QVec n) : QVec n :=
  Vector.replace x target (Vector.nth x target + a * Vector.nth x source).

Lemma swap_entries_nth_i {n : nat} (i j : Fin.t n) (x : QVec n) :
  Vector.nth (swap_entries i j x) i = Vector.nth x j.
Proof.
  unfold swap_entries.
  destruct (Fin.eq_dec i j) as [Heq | Hneq].
  - subst. apply Vector.nth_replace_eq.
  - rewrite (Vector.nth_replace_neq _ _ i j Hneq).
    apply Vector.nth_replace_eq.
Qed.

Lemma swap_entries_nth_j {n : nat} (i j : Fin.t n) (x : QVec n) :
  Vector.nth (swap_entries i j x) j = Vector.nth x i.
Proof.
  unfold swap_entries.
  apply Vector.nth_replace_eq.
Qed.

Lemma swap_entries_nth_other {n : nat} (i j k : Fin.t n) (x : QVec n) :
  k <> i -> k <> j -> Vector.nth (swap_entries i j x) k = Vector.nth x k.
Proof.
  intros Hki Hkj.
  unfold swap_entries.
  rewrite (Vector.nth_replace_neq _ _ k j Hkj).
  rewrite (Vector.nth_replace_neq _ _ k i Hki).
  reflexivity.
Qed.

Lemma scale_entry_nth_eq {n : nat} (i : Fin.t n) (a : Qc) (x : QVec n) :
  Vector.nth (scale_entry i a x) i = a * Vector.nth x i.
Proof. unfold scale_entry. apply Vector.nth_replace_eq. Qed.

Lemma scale_entry_nth_neq {n : nat} (i k : Fin.t n) (a : Qc) (x : QVec n) :
  k <> i -> Vector.nth (scale_entry i a x) k = Vector.nth x k.
Proof. intros Hki. unfold scale_entry. apply (Vector.nth_replace_neq _ _ k i Hki). Qed.

Lemma add_scaled_entry_nth_target {n : nat} (target source : Fin.t n) (a : Qc) (x : QVec n) :
  Vector.nth (add_scaled_entry target source a x) target
  = Vector.nth x target + a * Vector.nth x source.
Proof. unfold add_scaled_entry. apply Vector.nth_replace_eq. Qed.

Lemma add_scaled_entry_nth_neq {n : nat} (target source k : Fin.t n) (a : Qc) (x : QVec n) :
  k <> target -> Vector.nth (add_scaled_entry target source a x) k = Vector.nth x k.
Proof. intros Hk. unfold add_scaled_entry. apply (Vector.nth_replace_neq _ _ k target Hk). Qed.

Lemma swap_entries_add {n : nat} (i j : Fin.t n) (x y : QVec n) :
  swap_entries i j (vadd x y) = vadd (swap_entries i j x) (swap_entries i j y).
Proof.
  apply vec_ext.
  intros k.
  rewrite vadd_nth.
  destruct (Fin.eq_dec k i) as [Hki | Hki].
  - subst k.
    rewrite !swap_entries_nth_i.
    apply vadd_nth.
  - destruct (Fin.eq_dec k j) as [Hkj | Hkj].
    + subst k.
      rewrite !swap_entries_nth_j.
      apply vadd_nth.
    + rewrite (swap_entries_nth_other i j k x Hki Hkj).
      rewrite (swap_entries_nth_other i j k y Hki Hkj).
      rewrite (swap_entries_nth_other i j k (vadd x y) Hki Hkj).
      apply vadd_nth.
Qed.

Lemma swap_entries_scale {n : nat} (i j : Fin.t n) (a : Qc) (x : QVec n) :
  swap_entries i j (vscale a x) = vscale a (swap_entries i j x).
Proof.
  apply vec_ext.
  intros k.
  rewrite vscale_nth.
  destruct (Fin.eq_dec k i) as [Hki | Hki].
  - subst k.
    rewrite !swap_entries_nth_i.
    apply vscale_nth.
  - destruct (Fin.eq_dec k j) as [Hkj | Hkj].
    + subst k.
      rewrite !swap_entries_nth_j.
      apply vscale_nth.
    + rewrite (swap_entries_nth_other i j k x Hki Hkj).
      rewrite (swap_entries_nth_other i j k (vscale a x) Hki Hkj).
      apply vscale_nth.
Qed.

Definition swap_entries_lmap {n : nat} (i j : Fin.t n) : QLinearMap n n :=
  {|
    lmap := swap_entries i j;
    lmap_add := swap_entries_add i j;
    lmap_scale := swap_entries_scale i j;
  |}.

Lemma scale_entry_add {n : nat} (i : Fin.t n) (a : Qc) (x y : QVec n) :
  scale_entry i a (vadd x y) = vadd (scale_entry i a x) (scale_entry i a y).
Proof.
  apply vec_ext.
  intros k.
  rewrite vadd_nth.
  destruct (Fin.eq_dec k i) as [Hki | Hki].
  - subst k.
    rewrite scale_entry_nth_eq, scale_entry_nth_eq, scale_entry_nth_eq.
    rewrite vadd_nth.
    ring.
  - rewrite (scale_entry_nth_neq i k a x Hki).
    rewrite (scale_entry_nth_neq i k a y Hki).
    rewrite (scale_entry_nth_neq i k a (vadd x y) Hki).
    apply vadd_nth.
Qed.

Lemma scale_entry_scale {n : nat} (i : Fin.t n) (a b : Qc) (x : QVec n) :
  scale_entry i a (vscale b x) = vscale b (scale_entry i a x).
Proof.
  apply vec_ext.
  intros k.
  rewrite vscale_nth.
  destruct (Fin.eq_dec k i) as [Hki | Hki].
  - subst k.
    rewrite scale_entry_nth_eq, scale_entry_nth_eq.
    rewrite vscale_nth.
    ring.
  - rewrite (scale_entry_nth_neq i k a x Hki).
    rewrite (scale_entry_nth_neq i k a (vscale b x) Hki).
    apply vscale_nth.
Qed.

Definition scale_entry_lmap {n : nat} (i : Fin.t n) (a : Qc) : QLinearMap n n :=
  {|
    lmap := scale_entry i a;
    lmap_add := scale_entry_add i a;
    lmap_scale := scale_entry_scale i a;
  |}.

Lemma add_scaled_entry_add {n : nat} (target source : Fin.t n) (a : Qc) (x y : QVec n) :
  add_scaled_entry target source a (vadd x y)
  = vadd (add_scaled_entry target source a x) (add_scaled_entry target source a y).
Proof.
  apply vec_ext.
  intros k.
  rewrite vadd_nth.
  destruct (Fin.eq_dec k target) as [Hkt | Hkt].
  - subst k.
    rewrite add_scaled_entry_nth_target, add_scaled_entry_nth_target, add_scaled_entry_nth_target.
    rewrite !vadd_nth.
    ring.
  - rewrite (add_scaled_entry_nth_neq target source k a x Hkt).
    rewrite (add_scaled_entry_nth_neq target source k a y Hkt).
    rewrite (add_scaled_entry_nth_neq target source k a (vadd x y) Hkt).
    apply vadd_nth.
Qed.

Lemma add_scaled_entry_scale {n : nat} (target source : Fin.t n) (a b : Qc) (x : QVec n) :
  add_scaled_entry target source a (vscale b x)
  = vscale b (add_scaled_entry target source a x).
Proof.
  apply vec_ext.
  intros k.
  rewrite vscale_nth.
  destruct (Fin.eq_dec k target) as [Hkt | Hkt].
  - subst k.
    rewrite add_scaled_entry_nth_target, add_scaled_entry_nth_target.
    rewrite !vscale_nth.
    ring.
  - rewrite (add_scaled_entry_nth_neq target source k a x Hkt).
    rewrite (add_scaled_entry_nth_neq target source k a (vscale b x) Hkt).
    apply vscale_nth.
Qed.

Definition add_scaled_entry_lmap {n : nat} (target source : Fin.t n) (a : Qc) : QLinearMap n n :=
  {|
    lmap := add_scaled_entry target source a;
    lmap_add := add_scaled_entry_add target source a;
    lmap_scale := add_scaled_entry_scale target source a;
  |}.

Definition row_swap_matrix {n : nat} (i j : Fin.t n) : QMatrix n n :=
  matrix_of_lmap (swap_entries_lmap i j).

Definition row_scale_matrix {n : nat} (i : Fin.t n) (a : Qc) : QMatrix n n :=
  matrix_of_lmap (scale_entry_lmap i a).

Definition row_add_matrix {n : nat} (target source : Fin.t n) (a : Qc) : QMatrix n n :=
  matrix_of_lmap (add_scaled_entry_lmap target source a).

Theorem row_swap_matrix_apply {n : nat} (i j : Fin.t n) (x : QVec n) :
  matrix_apply (row_swap_matrix i j) x = swap_entries i j x.
Proof. unfold row_swap_matrix. apply matrix_of_lmap_correct. Qed.

Theorem row_scale_matrix_apply {n : nat} (i : Fin.t n) (a : Qc) (x : QVec n) :
  matrix_apply (row_scale_matrix i a) x = scale_entry i a x.
Proof. unfold row_scale_matrix. apply matrix_of_lmap_correct. Qed.

Theorem row_add_matrix_apply {n : nat} (target source : Fin.t n) (a : Qc) (x : QVec n) :
  matrix_apply (row_add_matrix target source a) x = add_scaled_entry target source a x.
Proof. unfold row_add_matrix. apply matrix_of_lmap_correct. Qed.

Theorem row_swap_matrix_left_action {n m : nat} (i j : Fin.t n) (A : QMatrix n m) :
  matrix_compose (row_swap_matrix i j) A = Vector.map (swap_entries i j) A.
Proof.
  unfold matrix_compose.
  apply (Vector.map_ext _ _ (matrix_apply (row_swap_matrix i j)) (swap_entries i j)
           (row_swap_matrix_apply i j)).
Qed.

Theorem row_scale_matrix_left_action {n m : nat} (i : Fin.t n) (a : Qc) (A : QMatrix n m) :
  matrix_compose (row_scale_matrix i a) A = Vector.map (scale_entry i a) A.
Proof.
  unfold matrix_compose.
  apply (Vector.map_ext _ _ (matrix_apply (row_scale_matrix i a)) (scale_entry i a)
           (row_scale_matrix_apply i a)).
Qed.

Theorem row_add_matrix_left_action {n m : nat} (target source : Fin.t n) (a : Qc) (A : QMatrix n m) :
  matrix_compose (row_add_matrix target source a) A
  = Vector.map (add_scaled_entry target source a) A.
Proof.
  unfold matrix_compose.
  apply (Vector.map_ext _ _ (matrix_apply (row_add_matrix target source a))
           (add_scaled_entry target source a) (row_add_matrix_apply target source a)).
Qed.

Theorem matrix_eq_of_apply_eq {m n : nat} (A B : QMatrix m n)
    (H : forall x : QVec n, matrix_apply A x = matrix_apply B x) :
  A = B.
Proof.
  apply Vector.eq_nth_iff.
  intros p q ->.
  rewrite <- (matrix_apply_standard_basis A q).
  rewrite <- (matrix_apply_standard_basis B q).
  apply H.
Qed.

Definition matrix_inverse_pair {n : nat} (A B : QMatrix n n) : Prop :=
  matrix_compose A B = identity_matrix n /\ matrix_compose B A = identity_matrix n.

Theorem swap_entries_involutive {n : nat} (i j : Fin.t n) (x : QVec n) :
  swap_entries i j (swap_entries i j x) = x.
Proof.
  apply vec_ext.
  intros k.
  destruct (Fin.eq_dec k i) as [Hki | Hki].
  - subst k.
    rewrite swap_entries_nth_i.
    apply swap_entries_nth_j.
  - destruct (Fin.eq_dec k j) as [Hkj | Hkj].
    + subst k.
      rewrite swap_entries_nth_j.
      apply swap_entries_nth_i.
    + rewrite (swap_entries_nth_other i j k (swap_entries i j x) Hki Hkj).
      apply (swap_entries_nth_other i j k x Hki Hkj).
Qed.

Theorem scale_entry_inverse {n : nat} (i : Fin.t n) (a : Qc) (Ha : a <> 0) (x : QVec n) :
  scale_entry i (Qcinv a) (scale_entry i a x) = x.
Proof.
  apply vec_ext.
  intros k.
  destruct (Fin.eq_dec k i) as [Hki | Hki].
  - subst k.
    rewrite scale_entry_nth_eq, scale_entry_nth_eq.
    field.
    exact Ha.
  - rewrite (scale_entry_nth_neq i k (Qcinv a) (scale_entry i a x) Hki).
    apply (scale_entry_nth_neq i k a x Hki).
Qed.

Theorem scale_entry_inverse' {n : nat} (i : Fin.t n) (a : Qc) (Ha : a <> 0) (x : QVec n) :
  scale_entry i a (scale_entry i (Qcinv a) x) = x.
Proof.
  apply vec_ext.
  intros k.
  destruct (Fin.eq_dec k i) as [Hki | Hki].
  - subst k.
    rewrite scale_entry_nth_eq, scale_entry_nth_eq.
    field.
    exact Ha.
  - rewrite (scale_entry_nth_neq i k a (scale_entry i (Qcinv a) x) Hki).
    apply (scale_entry_nth_neq i k (Qcinv a) x Hki).
Qed.

Theorem add_scaled_entry_inverse {n : nat} (target source : Fin.t n) (a : Qc)
    (Hdistinct : target <> source) (x : QVec n) :
  add_scaled_entry target source (-a) (add_scaled_entry target source a x) = x.
Proof.
  apply vec_ext.
  intros k.
  destruct (Fin.eq_dec k target) as [Hkt | Hkt].
  - subst k.
    rewrite add_scaled_entry_nth_target.
    rewrite add_scaled_entry_nth_target.
    rewrite (add_scaled_entry_nth_neq target source source a x (fun H => Hdistinct (eq_sym H))).
    ring.
  - rewrite (add_scaled_entry_nth_neq target source k (-a) (add_scaled_entry target source a x) Hkt).
    apply (add_scaled_entry_nth_neq target source k a x Hkt).
Qed.

Theorem add_scaled_entry_inverse' {n : nat} (target source : Fin.t n) (a : Qc)
    (Hdistinct : target <> source) (x : QVec n) :
  add_scaled_entry target source a (add_scaled_entry target source (-a) x) = x.
Proof.
  pose proof (add_scaled_entry_inverse target source (-a) Hdistinct x) as H.
  rewrite Qcopp_involutive in H.
  exact H.
Qed.

Theorem row_swap_matrix_inverse {n : nat} (i j : Fin.t n) :
  matrix_inverse_pair (row_swap_matrix i j) (row_swap_matrix i j).
Proof.
  split; apply matrix_eq_of_apply_eq; intros x;
    rewrite matrix_compose_apply, !row_swap_matrix_apply, swap_entries_involutive;
    symmetry; apply identity_matrix_apply.
Qed.

Theorem row_scale_matrix_inverse {n : nat} (i : Fin.t n) (a : Qc) (Ha : a <> 0) :
  matrix_inverse_pair (row_scale_matrix i a) (row_scale_matrix i (Qcinv a)).
Proof.
  split; apply matrix_eq_of_apply_eq; intros x;
    rewrite matrix_compose_apply, !row_scale_matrix_apply.
  - rewrite (scale_entry_inverse' i a Ha x).
    symmetry. apply identity_matrix_apply.
  - rewrite (scale_entry_inverse i a Ha x).
    symmetry. apply identity_matrix_apply.
Qed.

Theorem row_add_matrix_inverse {n : nat} (target source : Fin.t n) (a : Qc)
    (Hdistinct : target <> source) :
  matrix_inverse_pair (row_add_matrix target source a) (row_add_matrix target source (-a)).
Proof.
  split; apply matrix_eq_of_apply_eq; intros x;
    rewrite matrix_compose_apply, !row_add_matrix_apply.
  - rewrite (add_scaled_entry_inverse' target source a Hdistinct x).
    symmetry. apply identity_matrix_apply.
  - rewrite (add_scaled_entry_inverse target source a Hdistinct x).
    symmetry. apply identity_matrix_apply.
Qed.
