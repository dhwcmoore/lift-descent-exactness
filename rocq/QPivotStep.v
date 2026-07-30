(** * One certified Gauss-Jordan pivot step

    Unit 14 certified that any finite, valid sequence of elementary row
    operations is an invertible linear transformation preserving and
    reflecting linear systems. This unit uses that machinery to
    formalise a single complete pivot transformation: search a column
    over an explicit list of candidate rows for a nonzero entry, move
    it into the designated pivot row, normalise it to [1], clear the
    rest of that column, and package the exact row-operation
    certificate that produced the result.

    This unit isolates and verifies exactly one pivot step. It does not
    search across columns, does not recurse, and does not build an
    elimination state, echelon predicate, or termination measure — all
    of that is Unit 16's responsibility. It also does not claim that
    columns other than [pivot_col] are preserved: a Gauss-Jordan pivot
    step transforms every column of the matrix, and preservation of
    previously-completed pivot columns needs an invariant (that the
    remaining candidate rows are already zero there) that belongs to
    the recursive elimination unit, not this one. *)

From Coq Require Import List.
From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Vector.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QFiniteCoordinates.
From LiftDescent Require Import QMatrixAlgebra.
From LiftDescent Require Import QElementaryRows.
From LiftDescent Require Import QRowOperationSequence.

Import ListNotations.

Open Scope Qc_scope.

(** ** 1. Matrix-entry access

    [matrix_entry A row col] reads the coordinate at [row] of the
    [col]-th column of [A], using the existing column-oriented
    [QMatrix] representation ([QMatrix m n = Vector.t (QVec m) n]) —
    no second matrix representation is introduced. *)

Definition matrix_entry
    {m n : nat}
    (A : QMatrix m n)
    (row : Fin.t m)
    (col : Fin.t n)
    : Qc :=
  Vector.nth (Vector.nth A col) row.

(** ** 2. Row enumeration as standard lists *)

Definition all_rows
    (m : nat)
    : list (Fin.t m) :=
  Vector.to_list (all_positions m).

Definition rows_except
    {m : nat}
    (pivot : Fin.t m)
    : list (Fin.t m) :=
  remove Fin.eq_dec pivot (all_rows m).

(** Every [Fin.t m] index occurs in [all_rows m]: [all_positions_nth]
    (Unit 11) says [Vector.nth (all_positions m) i = i], so [i] is the
    vector's value at position [i], hence [Vector.In] it, hence (via
    the standard bridge [to_list_In]) a member of the list. *)

Lemma all_rows_complete (m : nat) (i : Fin.t m) :
  In i (all_rows m).
Proof.
  unfold all_rows.
  apply (proj1 (Vector.to_list_In (Fin.t m) i m (all_positions m))).
  rewrite <- (all_positions_nth m i).
  apply Vector.In_nth.
Qed.

(** [all_positions m] has no duplicate values, hence neither does
    [all_rows m]: by induction on the [Fixpoint] definition of
    [all_positions] (Unit 11), using that [Fin.FS] is injective and
    never produces [Fin.F1]. Both facts are small, standard-bridge
    helpers not already present in the stdlib under this exact shape. *)

Lemma NoDup_map_injective {A B : Type} (f : A -> B)
    (Hinj : forall x y, f x = f y -> x = y)
    (l : list A) :
  NoDup l -> NoDup (map f l).
Proof.
  induction l as [| a l' IH].
  - intros _. simpl. constructor.
  - intro H. apply NoDup_cons_iff in H. destruct H as [Hnotin Hnodup].
    simpl. apply NoDup_cons.
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Heq Hinx]].
      apply Hinj in Heq. subst x. exact (Hnotin Hinx).
    + apply IH. exact Hnodup.
Qed.

Lemma not_In_F1_map_FS {n' : nat} (l : list (Fin.t n')) :
  ~ In Fin.F1 (map Fin.FS l).
Proof.
  intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Heq _]].
  discriminate Heq.
Qed.

Lemma all_rows_nodup (m : nat) : NoDup (all_rows m).
Proof.
  unfold all_rows.
  induction m as [| m' IH].
  - simpl. constructor.
  - simpl.
    rewrite (Vector.to_list_cons (Fin.t (S m')) Fin.F1 m' (Vector.map Fin.FS (all_positions m'))).
    rewrite (Vector.to_list_map (Fin.t m') (Fin.t (S m')) Fin.FS m' (all_positions m')).
    apply NoDup_cons.
    + apply not_In_F1_map_FS.
    + apply (NoDup_map_injective Fin.FS Fin.FS_inj).
      exact IH.
Qed.

(** [pivot] does not occur in [rows_except pivot], every index
    unequal to [pivot] does, and [rows_except pivot] has no
    duplicates — all direct from the standard [remove]/[NoDup]
    bridges above and [all_rows_complete]/[all_rows_nodup]. *)

Lemma rows_except_notin {m : nat} (pivot : Fin.t m) :
  ~ In pivot (rows_except pivot).
Proof.
  unfold rows_except.
  apply remove_In.
Qed.

Lemma rows_except_complete {m : nat} (pivot row : Fin.t m) :
  row <> pivot ->
  In row (rows_except pivot).
Proof.
  intro Hne.
  unfold rows_except.
  apply in_in_remove.
  - exact Hne.
  - apply all_rows_complete.
Qed.

Lemma NoDup_remove_general {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (l : list A) (x : A) :
  NoDup l -> NoDup (remove eq_dec x l).
Proof.
  induction l as [| a l' IH].
  - intro H. simpl. exact H.
  - intro H. apply NoDup_cons_iff in H. destruct H as [Hnotin Hnodup].
    simpl. destruct (eq_dec x a) as [Heq | Hneq].
    + apply IH. exact Hnodup.
    + apply NoDup_cons.
      * intro Hin. apply Hnotin.
        exact (proj1 (in_remove eq_dec l' a x Hin)).
      * apply IH. exact Hnodup.
Qed.

Lemma rows_except_nodup {m : nat} (pivot : Fin.t m) :
  NoDup (rows_except pivot).
Proof.
  unfold rows_except.
  apply NoDup_remove_general.
  apply all_rows_nodup.
Qed.

(** ** 3. Constructive nonzero-entry search over an explicit candidate
    list, using [Qc]'s own decidable equality — no conversion to raw
    [Q], no classical search. *)

Fixpoint find_nonzero_row
    {m n : nat}
    (A : QMatrix m n)
    (col : Fin.t n)
    (candidates : list (Fin.t m))
    : option (Fin.t m) :=
  match candidates with
  | [] =>
      None
  | row :: rest =>
      if Qc_eq_dec (matrix_entry A row col) 0
      then find_nonzero_row A col rest
      else Some row
  end.

Theorem find_nonzero_row_some
    {m n : nat} (A : QMatrix m n) (col : Fin.t n)
    (candidates : list (Fin.t m)) (row : Fin.t m) :
  find_nonzero_row A col candidates = Some row ->
  In row candidates /\
  matrix_entry A row col <> 0.
Proof.
  induction candidates as [| r rest IH].
  - simpl. discriminate.
  - simpl. destruct (Qc_eq_dec (matrix_entry A r col) 0) as [Heq | Hneq].
    + intro H. destruct (IH H) as [Hin Hne].
      split.
      * right. exact Hin.
      * exact Hne.
    + intro H. injection H as H. subst r.
      split.
      * left. reflexivity.
      * exact Hneq.
Qed.

Theorem find_nonzero_row_none
    {m n : nat} (A : QMatrix m n) (col : Fin.t n)
    (candidates : list (Fin.t m)) :
  find_nonzero_row A col candidates = None ->
  forall row,
    In row candidates ->
    matrix_entry A row col = 0.
Proof.
  induction candidates as [| r rest IH].
  - intros _ row Hin. destruct Hin.
  - simpl. destruct (Qc_eq_dec (matrix_entry A r col) 0) as [Heq | Hneq].
    + intros Hfind row Hin.
      destruct Hin as [Heqr | Hin].
      * subst row. exact Heq.
      * exact (IH Hfind row Hin).
    + discriminate.
Qed.

Theorem find_nonzero_row_none_of_zero
    {m n : nat} (A : QMatrix m n) (col : Fin.t n)
    (candidates : list (Fin.t m)) :
  (forall row, In row candidates -> matrix_entry A row col = 0) ->
  find_nonzero_row A col candidates = None.
Proof.
  induction candidates as [| r rest IH].
  - intros _. reflexivity.
  - intro Hall.
    simpl.
    assert (Hr : matrix_entry A r col = 0).
    { apply Hall. left. reflexivity. }
    destruct (Qc_eq_dec (matrix_entry A r col) 0) as [_ | Hneq].
    + apply IH. intros row Hin. apply Hall. right. exact Hin.
    + exfalso. apply Hneq. exact Hr.
Qed.

(** ** 4. Pivot normalisation: swap the selected row into the pivot
    row, then scale the pivot row so the pivot entry becomes [1]. The
    swap occurs first, the scaling second — matching Unit 14's
    head-first execution convention. *)

Definition pivot_coefficient
    {m n : nat}
    (A : QMatrix m n)
    (source_row : Fin.t m)
    (pivot_col : Fin.t n)
    : Qc :=
  matrix_entry A source_row pivot_col.

Definition pivot_normalise_operations
    {m n : nat}
    (A : QMatrix m n)
    (pivot_row source_row : Fin.t m)
    (pivot_col : Fin.t n)
    : list (RowOperation m) :=
  [
    RowSwap source_row pivot_row;
    RowScale pivot_row
      (Qcinv
        (pivot_coefficient
          A source_row pivot_col))
  ].

Definition pivot_normalised_matrix
    {m n : nat}
    (A : QMatrix m n)
    (pivot_row source_row : Fin.t m)
    (pivot_col : Fin.t n)
    : QMatrix m n :=
  matrix_compose
    (row_operation_sequence_matrix
       (pivot_normalise_operations
          A pivot_row source_row pivot_col))
    A.

Theorem pivot_normalise_operations_valid
    {m n : nat} (A : QMatrix m n)
    (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n) :
  pivot_coefficient A source_row pivot_col <> 0 ->
  row_operation_sequence_valid
    (pivot_normalise_operations A pivot_row source_row pivot_col).
Proof.
  intro Hne.
  unfold row_operation_sequence_valid, pivot_normalise_operations.
  constructor.
  - exact I.
  - constructor.
    + apply (inverse_row_operation_valid
               (RowScale pivot_row (pivot_coefficient A source_row pivot_col))).
      exact Hne.
    + constructor.
Qed.

(** The complete pivot column after normalisation: the original column
    with the source and pivot rows swapped, then the pivot coordinate
    scaled — exactly the two operations of [pivot_normalise_operations]
    applied in order, via [row_operation_sequence_left_action]. This
    remains correct, with no special case, when [source_row =
    pivot_row]: [swap_entries] is already proved self-inverse-safe at
    equal indices in Unit 13. *)

Theorem pivot_normalise_column
    {m n : nat} (A : QMatrix m n)
    (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n) :
  Vector.nth
    (pivot_normalised_matrix A pivot_row source_row pivot_col)
    pivot_col
  =
  scale_entry pivot_row
    (Qcinv (pivot_coefficient A source_row pivot_col))
    (swap_entries source_row pivot_row (Vector.nth A pivot_col)).
Proof.
  unfold pivot_normalised_matrix.
  rewrite (row_operation_sequence_left_action
             (pivot_normalise_operations A pivot_row source_row pivot_col) A).
  rewrite (Vector.nth_map _ _ pivot_col pivot_col eq_refl).
  unfold pivot_normalise_operations.
  reflexivity.
Qed.

Theorem pivot_normalise_operations_pivot_entry
    {m n : nat} (A : QMatrix m n)
    (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n) :
  pivot_coefficient A source_row pivot_col <> 0 ->
  matrix_entry
    (pivot_normalised_matrix A pivot_row source_row pivot_col)
    pivot_row pivot_col
  = 1.
Proof.
  intro Hne.
  unfold matrix_entry.
  rewrite pivot_normalise_column.
  rewrite scale_entry_nth_eq.
  rewrite swap_entries_nth_j.
  unfold pivot_coefficient, matrix_entry in Hne |- *.
  field.
  exact Hne.
Qed.

(** ** 5. Clearing the rest of the pivot column

    For a vector [column] whose [pivot_row] coordinate is already
    [1], add the appropriate multiple of the pivot row to every other
    row so that row's coordinate becomes [0]. Every target row is
    distinct (from [rows_except]'s exclusion of [pivot_row]), and the
    coefficient for each is read once from the original [column], not
    recomputed mid-sequence. *)

Definition clear_pivot_column_operations
    {m : nat}
    (pivot_row : Fin.t m)
    (column : QVec m)
    : list (RowOperation m) :=
  map
    (fun row =>
       RowAdd
         row
         pivot_row
         (- Vector.nth column row))
    (rows_except pivot_row).

Theorem clear_pivot_column_operations_valid
    {m : nat} (pivot_row : Fin.t m) (column : QVec m) :
  row_operation_sequence_valid
    (clear_pivot_column_operations pivot_row column).
Proof.
  unfold row_operation_sequence_valid, clear_pivot_column_operations.
  apply Forall_forall.
  intros op Hin.
  apply in_map_iff in Hin.
  destruct Hin as [row [Heq Hin_row]].
  subst op.
  simpl.
  unfold rows_except in Hin_row.
  exact (proj2 (in_remove Fin.eq_dec (all_rows m) row pivot_row Hin_row)).
Qed.

(** A coordinate never targeted by any operation in the clearing
    sequence is left unchanged by it — needed both to show the pivot
    coordinate survives the whole sequence (instantiating [row] at
    [pivot_row], via [rows_except_notin]) and, inside the main
    induction below, to show that an already-processed row's zeroed
    value is not disturbed by later, differently-targeted operations. *)

Lemma run_clear_ops_untouched
    {m : nat} (pivot_row : Fin.t m) (rows : list (Fin.t m))
    (column x : QVec m) (row : Fin.t m) :
  ~ In row rows ->
  Vector.nth
    (run_row_operations
       (map (fun r => RowAdd r pivot_row (- Vector.nth column r)) rows) x)
    row
  = Vector.nth x row.
Proof.
  induction rows as [| r rest IH] in x |- *.
  - intros _. reflexivity.
  - intro Hnotin.
    assert (Hr : row <> r).
    { intro Heq. apply Hnotin. subst row. left. reflexivity. }
    assert (Hrest : ~ In row rest).
    { intro Hin. apply Hnotin. right. exact Hin. }
    simpl.
    rewrite (IH (add_scaled_entry r pivot_row (- Vector.nth column r) x) Hrest).
    apply (add_scaled_entry_nth_neq r pivot_row row (- Vector.nth column r) x Hr).
Qed.

(** The main clearing induction: given that [x]'s pivot coordinate is
    already [1] and [x] agrees with [column] on every row still to be
    processed, running the (remaining) clearing operations zeroes every
    one of those rows in the final result. Processing [rows] one at a
    time, each row's own operation reads [x]'s (== [column]'s, by the
    agreement hypothesis) current value there and the pivot's current
    value ([1], by [run_clear_ops_untouched] applied to the rest of the
    list, which never re-targets an already-consumed row since
    [rows_except] has no duplicates). *)

Lemma run_clear_ops_result
    {m : nat} (pivot_row : Fin.t m) (rows : list (Fin.t m))
    (column : QVec m) :
  ~ In pivot_row rows ->
  NoDup rows ->
  forall x : QVec m,
    Vector.nth x pivot_row = 1 ->
    (forall row, In row rows -> Vector.nth x row = Vector.nth column row) ->
    forall row, In row rows ->
      Vector.nth
        (run_row_operations
           (map (fun r => RowAdd r pivot_row (- Vector.nth column r)) rows) x)
        row
      = 0.
Proof.
  induction rows as [| r rest IH].
  - intros _ _ x _ _ row Hin. destruct Hin.
  - intros Hnotin Hnodup x Hx_pivot Hx_rows row Hin.
    assert (Hr_ne_pivot : r <> pivot_row).
    { intro Heq. apply Hnotin. left. exact Heq. }
    assert (Hpivot_ne_r : pivot_row <> r).
    { intro Heq. apply Hr_ne_pivot. symmetry. exact Heq. }
    assert (Hnotin_rest : ~ In pivot_row rest).
    { intro Hin'. apply Hnotin. right. exact Hin'. }
    apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as [Hr_notin_rest Hnodup_rest].
    simpl.
    set (x' := add_scaled_entry r pivot_row (- Vector.nth column r) x).
    destruct Hin as [Heq | Hin_rest].
    + subst row.
      rewrite (run_clear_ops_untouched pivot_row rest column x' r Hr_notin_rest).
      unfold x'.
      rewrite (add_scaled_entry_nth_target r pivot_row (- Vector.nth column r) x).
      rewrite Hx_pivot.
      assert (Hxr : Vector.nth x r = Vector.nth column r).
      { apply Hx_rows. left. reflexivity. }
      rewrite Hxr.
      ring.
    + apply (IH Hnotin_rest Hnodup_rest x').
      * unfold x'.
        rewrite (add_scaled_entry_nth_neq r pivot_row pivot_row
                   (- Vector.nth column r) x Hpivot_ne_r).
        exact Hx_pivot.
      * intros row' Hin'.
        unfold x'.
        assert (Hrow'_ne_r : row' <> r).
        { intro Heq. subst row'. exact (Hr_notin_rest Hin'). }
        rewrite (add_scaled_entry_nth_neq r pivot_row row'
                   (- Vector.nth column r) x Hrow'_ne_r).
        apply Hx_rows. right. exact Hin'.
      * exact Hin_rest.
Qed.

Theorem clear_pivot_column_apply
    {m : nat} (pivot_row : Fin.t m) (column : QVec m) :
  Vector.nth column pivot_row = 1 ->
  run_row_operations
    (clear_pivot_column_operations pivot_row column)
    column
  =
  standard_basis pivot_row.
Proof.
  intro Hpivot1.
  apply vec_ext.
  intro k.
  unfold clear_pivot_column_operations.
  destruct (Fin.eq_dec k pivot_row) as [Heq | Hneq].
  - subst k.
    rewrite (run_clear_ops_untouched pivot_row (rows_except pivot_row) column column
               pivot_row (rows_except_notin pivot_row)).
    rewrite Hpivot1.
    symmetry.
    apply standard_basis_nth_eq.
  - rewrite (run_clear_ops_result pivot_row (rows_except pivot_row) column
               (rows_except_notin pivot_row) (rows_except_nodup pivot_row)
               column Hpivot1 (fun row _ => eq_refl) k
               (rows_except_complete pivot_row k Hneq)).
    symmetry.
    apply (standard_basis_nth_neq k pivot_row Hneq).
Qed.

(** ** 6. The complete pivot operation sequence: normalise, then clear.
    [B] below is the normalised matrix; the clearing coefficients are
    read from its (already-normalised) pivot column, exactly as
    documented for [clear_pivot_column_operations]. *)

Definition pivot_operations
    {m n : nat}
    (A : QMatrix m n)
    (pivot_row source_row : Fin.t m)
    (pivot_col : Fin.t n)
    : list (RowOperation m) :=
  let normalise :=
    pivot_normalise_operations
      A pivot_row source_row pivot_col in
  let B :=
    pivot_normalised_matrix
      A pivot_row source_row pivot_col in
  normalise ++
  clear_pivot_column_operations
    pivot_row
    (Vector.nth B pivot_col).

Definition pivot_output_matrix
    {m n : nat}
    (A : QMatrix m n)
    (pivot_row source_row : Fin.t m)
    (pivot_col : Fin.t n)
    : QMatrix m n :=
  matrix_compose
    (row_operation_sequence_matrix
       (pivot_operations
          A pivot_row source_row pivot_col))
    A.

Theorem pivot_operations_valid
    {m n : nat} (A : QMatrix m n)
    (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n) :
  pivot_coefficient A source_row pivot_col <> 0 ->
  row_operation_sequence_valid
    (pivot_operations A pivot_row source_row pivot_col).
Proof.
  intro Hne.
  unfold row_operation_sequence_valid, pivot_operations.
  apply Forall_app.
  split.
  - apply (pivot_normalise_operations_valid A pivot_row source_row pivot_col Hne).
  - apply clear_pivot_column_operations_valid.
Qed.

Theorem pivot_output_matrix_relation
    {m n : nat} (A : QMatrix m n)
    (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n) :
  pivot_output_matrix
    A pivot_row source_row pivot_col
  =
  matrix_compose
    (row_operation_sequence_matrix
       (pivot_operations
          A pivot_row source_row pivot_col))
    A.
Proof. reflexivity. Qed.

(** [run_row_operations] under list append: not among Unit 14's central
    declarations (which worked at the matrix level via
    [row_operation_sequence_matrix_append]), but immediate by
    structural induction on the head-first [Fixpoint], and needed here
    because [pivot_operations] is built with [++]. *)

Lemma run_row_operations_app
    {n : nat} (ops1 ops2 : list (RowOperation n)) (x : QVec n) :
  run_row_operations (ops1 ++ ops2) x
  = run_row_operations ops2 (run_row_operations ops1 x).
Proof.
  induction ops1 as [| op1 rest1 IH] in x |- *.
  - reflexivity.
  - simpl. apply IH.
Qed.

Theorem pivot_output_column
    {m n : nat} (A : QMatrix m n)
    (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n) :
  pivot_coefficient A source_row pivot_col <> 0 ->
  Vector.nth
    (pivot_output_matrix A pivot_row source_row pivot_col)
    pivot_col
  =
  standard_basis pivot_row.
Proof.
  intro Hne.
  unfold pivot_output_matrix, pivot_operations.
  rewrite (row_operation_sequence_left_action
             (pivot_normalise_operations A pivot_row source_row pivot_col ++
              clear_pivot_column_operations pivot_row
                (Vector.nth
                   (pivot_normalised_matrix A pivot_row source_row pivot_col)
                   pivot_col))
             A).
  rewrite (Vector.nth_map _ _ pivot_col pivot_col eq_refl).
  rewrite run_row_operations_app.
  assert (Hnorm :
    run_row_operations
      (pivot_normalise_operations A pivot_row source_row pivot_col)
      (Vector.nth A pivot_col)
    = Vector.nth
        (pivot_normalised_matrix A pivot_row source_row pivot_col)
        pivot_col).
  { unfold pivot_normalise_operations. simpl. symmetry. apply pivot_normalise_column. }
  rewrite Hnorm.
  apply clear_pivot_column_apply.
  apply pivot_normalise_operations_pivot_entry.
  exact Hne.
Qed.

Theorem pivot_output_entry_pivot
    {m n : nat} (A : QMatrix m n)
    (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n) :
  pivot_coefficient A source_row pivot_col <> 0 ->
  matrix_entry
    (pivot_output_matrix A pivot_row source_row pivot_col)
    pivot_row pivot_col
  = 1.
Proof.
  intro Hne.
  unfold matrix_entry.
  rewrite (pivot_output_column A pivot_row source_row pivot_col Hne).
  apply standard_basis_nth_eq.
Qed.

Theorem pivot_output_entry_other
    {m n : nat} (A : QMatrix m n)
    (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n) (row : Fin.t m) :
  pivot_coefficient A source_row pivot_col <> 0 ->
  row <> pivot_row ->
  matrix_entry
    (pivot_output_matrix A pivot_row source_row pivot_col)
    row pivot_col
  = 0.
Proof.
  intros Hne Hrow.
  unfold matrix_entry.
  rewrite (pivot_output_column A pivot_row source_row pivot_col Hne).
  apply (standard_basis_nth_neq row pivot_row Hrow).
Qed.

(** ** 7. Action on arbitrary columns

    The accumulated pivot-sequence matrix applies the whole sequence
    to every column, not just [pivot_col] — this is what Unit 16 will
    use, together with a not-yet-existing invariant, to reason about
    already-completed pivot columns. No such invariant is built here;
    this theorem makes no claim that other columns are unchanged. *)

Theorem pivot_output_column_action
    {m n : nat} (A : QMatrix m n)
    (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n) :
  forall col,
    Vector.nth
      (pivot_output_matrix A pivot_row source_row pivot_col)
      col
    =
    run_row_operations
      (pivot_operations A pivot_row source_row pivot_col)
      (Vector.nth A col).
Proof.
  intro col.
  unfold pivot_output_matrix.
  rewrite (row_operation_sequence_left_action
             (pivot_operations A pivot_row source_row pivot_col) A).
  apply (Vector.nth_map _ _ col col eq_refl).
Qed.

(** ** 8. The computational pivot step

    [PivotStepData] carries no proofs; the certificate is entirely
    external and theorem-based, as required. *)

Record PivotStepData
    (m n : nat)
    : Type := {
  pivot_step_source :
    Fin.t m;
  pivot_step_operations :
    list (RowOperation m);
  pivot_step_output :
    QMatrix m n
}.

Arguments pivot_step_source {m n}.
Arguments pivot_step_operations {m n}.
Arguments pivot_step_output {m n}.

Definition pivot_step
    {m n : nat}
    (A : QMatrix m n)
    (pivot_row : Fin.t m)
    (pivot_col : Fin.t n)
    (candidates : list (Fin.t m))
    : option (PivotStepData m n) :=
  match
    find_nonzero_row A pivot_col candidates
  with
  | None =>
      None
  | Some source_row =>
      Some {|
        pivot_step_source :=
          source_row;
        pivot_step_operations :=
          pivot_operations
            A pivot_row source_row pivot_col;
        pivot_step_output :=
          pivot_output_matrix
            A pivot_row source_row pivot_col
      |}
  end.

(** ** 9. Pivot-step correctness *)

Theorem pivot_step_none
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) :
  pivot_step A pivot_row pivot_col candidates = None ->
  forall row,
    In row candidates ->
    matrix_entry A row pivot_col = 0.
Proof.
  unfold pivot_step.
  destruct (find_nonzero_row A pivot_col candidates) eqn:Hfind.
  - discriminate.
  - intros _.
    apply (find_nonzero_row_none A pivot_col candidates Hfind).
Qed.

Theorem pivot_step_some_source
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n) :
  pivot_step A pivot_row pivot_col candidates = Some result ->
  In
    (pivot_step_source result)
    candidates /\
  matrix_entry
    A
    (pivot_step_source result)
    pivot_col
  <>
  0.
Proof.
  unfold pivot_step.
  destruct (find_nonzero_row A pivot_col candidates) eqn:Hfind.
  - intro H. injection H as H. subst result. simpl.
    apply (find_nonzero_row_some A pivot_col candidates t Hfind).
  - discriminate.
Qed.

Theorem pivot_step_some_operations
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n) :
  pivot_step A pivot_row pivot_col candidates = Some result ->
  pivot_step_operations result =
  pivot_operations
    A
    pivot_row
    (pivot_step_source result)
    pivot_col.
Proof.
  unfold pivot_step.
  destruct (find_nonzero_row A pivot_col candidates) eqn:Hfind.
  - intro H. injection H as H. subst result. reflexivity.
  - discriminate.
Qed.

Theorem pivot_step_some_output
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n) :
  pivot_step A pivot_row pivot_col candidates = Some result ->
  pivot_step_output result =
  pivot_output_matrix
    A
    pivot_row
    (pivot_step_source result)
    pivot_col.
Proof.
  unfold pivot_step.
  destruct (find_nonzero_row A pivot_col candidates) eqn:Hfind.
  - intro H. injection H as H. subst result. reflexivity.
  - discriminate.
Qed.

Theorem pivot_step_some_valid
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n) :
  pivot_step A pivot_row pivot_col candidates = Some result ->
  row_operation_sequence_valid
    (pivot_step_operations result).
Proof.
  intro H.
  rewrite (pivot_step_some_operations A pivot_row pivot_col candidates result H).
  apply pivot_operations_valid.
  apply (proj2 (pivot_step_some_source A pivot_row pivot_col candidates result H)).
Qed.

Theorem pivot_step_some_relation
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n) :
  pivot_step A pivot_row pivot_col candidates = Some result ->
  pivot_step_output result =
  matrix_compose
    (row_operation_sequence_matrix
       (pivot_step_operations result))
    A.
Proof.
  intro H.
  rewrite (pivot_step_some_output A pivot_row pivot_col candidates result H).
  rewrite (pivot_step_some_operations A pivot_row pivot_col candidates result H).
  apply pivot_output_matrix_relation.
Qed.

Theorem pivot_step_some_column
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n) :
  pivot_step A pivot_row pivot_col candidates = Some result ->
  Vector.nth
    (pivot_step_output result)
    pivot_col
  =
  standard_basis pivot_row.
Proof.
  intro H.
  rewrite (pivot_step_some_output A pivot_row pivot_col candidates result H).
  apply pivot_output_column.
  apply (proj2 (pivot_step_some_source A pivot_row pivot_col candidates result H)).
Qed.

(** ** 10. Inverse certificate and system preservation/reflection *)

Theorem pivot_step_some_inverse_pair
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n) :
  pivot_step A pivot_row pivot_col candidates = Some result ->
  matrix_inverse_pair
    (row_operation_sequence_matrix
       (pivot_step_operations result))
    (row_operation_sequence_matrix
       (inverse_row_operation_sequence
          (pivot_step_operations result))).
Proof.
  intro H.
  apply row_operation_sequence_inverse_pair.
  apply (pivot_step_some_valid A pivot_row pivot_col candidates result H).
Qed.

Theorem pivot_step_equation_iff
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n)
    (b : QVec m) (x : QVec n) :
  pivot_step A pivot_row pivot_col candidates = Some result ->
  (matrix_apply A x = b <->
   matrix_apply
     (pivot_step_output result)
     x
   =
   run_row_operations
     (pivot_step_operations result)
     b).
Proof.
  intro H.
  rewrite (pivot_step_some_relation A pivot_row pivot_col candidates result H).
  rewrite (run_row_operations_matrix (pivot_step_operations result) b).
  apply row_operation_sequence_equation_iff.
  apply (pivot_step_some_valid A pivot_row pivot_col candidates result H).
Qed.
