From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Import Vector.
Import VectorNotations.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.

Open Scope Qc_scope.

Fixpoint qsum {n : nat} (v : Vector.t Qc n) : Qc :=
  match v with
  | [] => 0
  | x :: rest => x + qsum rest
  end.

Fixpoint vsum {m n : nat} (v : Vector.t (QVec m) n) : QVec m :=
  match v with
  | [] => zero_vec m
  | x :: rest => vadd x (vsum rest)
  end.

Definition standard_basis {n : nat} (i : Fin.t n) : QVec n :=
  Vector.replace (zero_vec n) i 1.

Lemma standard_basis_nth_eq {n : nat} (i : Fin.t n) :
  Vector.nth (standard_basis i) i = 1.
Proof.
  apply Vector.nth_replace_eq.
Qed.

Lemma standard_basis_nth_neq {n : nat} (i j : Fin.t n) :
  i <> j -> Vector.nth (standard_basis j) i = 0.
Proof.
  intros Hij.
  unfold standard_basis.
  rewrite (Vector.nth_replace_neq _ _ i j Hij).
  apply zero_vec_nth.
Qed.

Theorem vsum_nth {m n : nat} (V : Vector.t (QVec m) n) (k : Fin.t m) :
  Vector.nth (vsum V) k = qsum (Vector.map (fun v => Vector.nth v k) V).
Proof.
  induction V as [| x n' V' IH].
  - simpl. apply zero_vec_nth.
  - simpl. rewrite vadd_nth. rewrite IH. reflexivity.
Qed.

Theorem lmap_preserves_vsum {n m k : nat} (T : QLinearMap n m) (V : Vector.t (QVec n) k) :
  lmap T (vsum V) = vsum (Vector.map (lmap T) V).
Proof.
  induction V as [| x k' V' IH].
  - simpl. apply lmap_preserves_zero.
  - simpl. rewrite (lmap_add T x (vsum V')). rewrite IH. reflexivity.
Qed.

Fixpoint all_positions (n : nat) : Vector.t (Fin.t n) n :=
  match n with
  | O => []
  | S n' => Fin.F1 :: Vector.map Fin.FS (all_positions n')
  end.

Lemma all_positions_nth (n : nat) (i : Fin.t n) :
  Vector.nth (all_positions n) i = i.
Proof.
  induction i as [n' | n' i' IH].
  - simpl. reflexivity.
  - simpl. rewrite (Vector.nth_map Fin.FS (all_positions n') i' i' eq_refl).
    rewrite IH. reflexivity.
Qed.

Lemma qsum_map_zero {A : Type} {n : nat} (w : Vector.t A n) :
  qsum (Vector.map (fun _ : A => 0) w) = 0.
Proof.
  induction w as [| a n' w' IH].
  - reflexivity.
  - simpl. rewrite IH. ring.
Qed.

Lemma standard_basis_FS_nth {n' : nat} (j k' : Fin.t n') :
  Vector.nth (standard_basis (Fin.FS j)) (Fin.FS k') = Vector.nth (standard_basis j) k'.
Proof.
  destruct (Fin.eq_dec j k') as [Heq | Hneq].
  - subst j. rewrite (standard_basis_nth_eq (Fin.FS k')). rewrite (standard_basis_nth_eq k').
    reflexivity.
  - assert (Hneq' : Fin.FS k' <> Fin.FS j).
    { intro H. apply Hneq. apply Fin.FS_inj in H. symmetry. exact H. }
    rewrite (standard_basis_nth_neq (Fin.FS k') (Fin.FS j) Hneq').
    rewrite (standard_basis_nth_neq k' j (fun H => Hneq (eq_sym H))).
    reflexivity.
Qed.

Lemma qsum_select_fun {n : nat} (k : Fin.t n) (f : Fin.t n -> Qc) :
  qsum (Vector.map (fun j => f j * Vector.nth (standard_basis j) k) (all_positions n)) = f k.
Proof.
  induction k as [n' | n' k' IH] in f |- *.
  - simpl.
    rewrite (Vector.map_map _ _ _ Fin.FS
               (fun j => f j * Vector.nth (standard_basis j) Fin.F1)).
    simpl.
    rewrite (Vector.map_ext _ _ (fun x => f (Fin.FS x) * Q2Qc 0) (fun _ : Fin.t n' => 0)).
    + rewrite qsum_map_zero. ring.
    + intros a. ring.
  - simpl.
    rewrite (Vector.map_map _ _ _ Fin.FS
               (fun j => f j * Vector.nth (standard_basis j) (Fin.FS k'))).
    rewrite zero_vec_nth.
    rewrite (Vector.map_ext _ _
               (fun x => f (Fin.FS x) * Vector.nth (standard_basis (Fin.FS x)) (Fin.FS k'))
               (fun x => f (Fin.FS x) * Vector.nth (standard_basis x) k')).
    + rewrite (IH (fun j => f (Fin.FS j))).
      ring.
    + intros a. rewrite standard_basis_FS_nth. reflexivity.
Qed.

Lemma qsum_select {n : nat} (x : QVec n) (k : Fin.t n) :
  qsum (Vector.map (fun j => Vector.nth x j * Vector.nth (standard_basis j) k) (all_positions n))
  = Vector.nth x k.
Proof.
  apply (qsum_select_fun k (Vector.nth x)).
Qed.

Lemma coordinate_column_eq {n : nat} (x : QVec n) (k : Fin.t n) :
  Vector.map (fun v => Vector.nth v k)
    (Vector.map2 vscale x (Vector.map standard_basis (all_positions n)))
  = Vector.map (fun j => Vector.nth x j * Vector.nth (standard_basis j) k) (all_positions n).
Proof.
  apply vec_ext.
  intros i.
  rewrite (Vector.nth_map _ _ i i eq_refl).
  rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl).
  rewrite vscale_nth.
  rewrite (Vector.nth_map _ _ i i eq_refl).
  rewrite (Vector.nth_map _ _ i i eq_refl).
  rewrite (all_positions_nth n i).
  reflexivity.
Qed.

Theorem coordinate_expansion {n : nat} (x : QVec n) :
  x = vsum (Vector.map2 vscale x (Vector.map standard_basis (all_positions n))).
Proof.
  apply vec_ext.
  intros k.
  rewrite vsum_nth.
  rewrite coordinate_column_eq.
  symmetry.
  apply qsum_select.
Qed.

Lemma map_lmap_map2_vscale {n m k : nat} (T : QLinearMap n m)
    (s : Vector.t Qc k) (V : Vector.t (QVec n) k) :
  Vector.map (lmap T) (Vector.map2 vscale s V) = Vector.map2 vscale s (Vector.map (lmap T) V).
Proof.
  induction s as [| a k' s' IH] in V |- *.
  - revert V. apply Vector.case0. reflexivity.
  - apply (Vector.caseS' V).
    intros v V'.
    simpl.
    rewrite (lmap_scale T a v).
    rewrite IH.
    reflexivity.
Qed.

Definition QMatrix (m n : nat) := Vector.t (QVec m) n.

Definition matrix_apply {m n : nat} (M : QMatrix m n) (x : QVec n) : QVec m :=
  vsum (Vector.map2 vscale x M).

Definition matrix_of_lmap {n m : nat} (T : QLinearMap n m) : QMatrix m n :=
  Vector.map (fun i => lmap T (standard_basis i)) (all_positions n).

Theorem matrix_of_lmap_correct {n m : nat} (T : QLinearMap n m) (x : QVec n) :
  matrix_apply (matrix_of_lmap T) x = lmap T x.
Proof.
  unfold matrix_apply, matrix_of_lmap.
  rewrite (coordinate_expansion x) at 2.
  rewrite (lmap_preserves_vsum T).
  rewrite map_lmap_map2_vscale.
  rewrite (Vector.map_map _ _ _ standard_basis (lmap T)).
  reflexivity.
Qed.
