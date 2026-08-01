(** * Correctness of the recursive elimination structure

    Unit 16a assembled an executable, deterministic recursion over
    Unit 15's certified single-pivot primitive, but proved nothing
    about what the resulting state means. This unit closes that gap
    at exactly three layers:

    1. execution correctness — the state's current matrix is exactly
       the accumulated row-operation sequence applied to the original
       matrix ([elimination_state_correct], [run_elimination_correct]);
    2. completed-pivot-column preservation — every pivot column
       recorded in the trace remains an exact unit column at its
       recorded pivot row in the final matrix
       ([completed_pivots_hold], [run_elimination_completed_pivots]);
    3. whole-run system preservation and reflection — the original
       and accumulated-sequence-transformed linear systems are
       equivalent ([run_elimination_solution_iff]).

    This unit does NOT prove: standard row-echelon form; reduced
    row-echelon form; increasing pivot-row order; increasing
    leading-entry order; that entries away from the proved unit
    columns vanish; that the number of recorded pivots equals rank;
    that skipped columns are linearly dependent on earlier columns;
    maximality of the selected pivot set; uniqueness or canonicity of
    the final matrix; independence from the row-search order;
    determinant preservation; numerical stability; asymptotic
    efficiency; that the trace is checkable without replaying the
    operations; a decision procedure for arbitrary propositions; or
    any generalisation beyond this finite rational setting.

    The strongest structural conclusion this unit reaches is: every
    successful pivot recorded by the deterministic run remains an
    exact unit column at its recorded pivot row in the final matrix —
    nothing about the shape, order, or completeness of that set of
    pivots. *)

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
From LiftDescent Require Import QPivotStep.
From LiftDescent Require Import QEliminationStructure.

Import ListNotations.

Open Scope Qc_scope.

(** ** 1. Execution correctness

    Unit 16a's [EliminationState] deliberately does not store the
    original matrix, so this is an external relation, not a state
    field. [run_row_operations] (Unit 14) acts on a [QVec], not a
    [QMatrix]; the canonical matrix-level lifting of a sequence,
    established throughout Units 14-15, is [matrix_compose
    (row_operation_sequence_matrix ops) A] — exactly the form
    [pivot_output_matrix] and [pivot_step_some_relation] already use.
    This is therefore the "canonical existing formulation" rather than
    a literal transcription of the vector-level [run_row_operations]
    pseudocode. *)

Definition elimination_state_correct
    {m n : nat}
    (original : QMatrix m n)
    (state : EliminationState m n)
    : Prop :=
  elimination_matrix state
  = matrix_compose
      (row_operation_sequence_matrix (elimination_operations state))
      original.

Theorem initial_elimination_state_correct
    {m n : nat} (A : QMatrix m n) :
  elimination_state_correct A (initial_elimination_state A).
Proof.
  unfold elimination_state_correct, initial_elimination_state.
  simpl.
  symmetry.
  apply matrix_compose_identity_left.
Qed.

Theorem elimination_step_preserves_correctness
    {m n : nat} (col : Fin.t n) (original : QMatrix m n) (state : EliminationState m n) :
  elimination_state_correct original state ->
  elimination_state_correct original (elimination_step col state).
Proof.
  intro Hcorrect.
  unfold elimination_step.
  destruct
    (first_nonzero_available_row
       (elimination_matrix state) col (elimination_available_rows state))
    as [row |] eqn:Hfind.
  - destruct
      (pivot_step
         (elimination_matrix state) row col (elimination_available_rows state))
      as [result |] eqn:Hpivot.
    + unfold elimination_state_correct in Hcorrect |- *.
      simpl.
      rewrite
        (row_operation_sequence_matrix_append
           (elimination_operations state) (pivot_step_operations result)).
      rewrite <-
        (matrix_compose_assoc
           (row_operation_sequence_matrix (pivot_step_operations result))
           (row_operation_sequence_matrix (elimination_operations state))
           original).
      rewrite <- Hcorrect.
      apply
        (pivot_step_some_relation
           (elimination_matrix state) row col
           (elimination_available_rows state) result Hpivot).
    + exact Hcorrect.
  - exact Hcorrect.
Qed.

Theorem eliminate_columns_preserves_correctness
    {m n : nat} (columns : list (Fin.t n)) (original : QMatrix m n) (state : EliminationState m n) :
  elimination_state_correct original state ->
  elimination_state_correct original (eliminate_columns columns state).
Proof.
  induction columns as [| col rest IH] in state |- *.
  - intro H. exact H.
  - intro H.
    simpl.
    apply IH.
    apply elimination_step_preserves_correctness.
    exact H.
Qed.

Theorem run_elimination_correct
    {m n : nat} (A : QMatrix m n) :
  elimination_state_correct A (run_elimination A).
Proof.
  unfold run_elimination.
  apply eliminate_columns_preserves_correctness.
  apply initial_elimination_state_correct.
Qed.

(** ** 2. Completed pivot descriptors and the unit-column predicate

    [CompletedPivot] stores no matrix, no operation sequence, and no
    proof — exactly a position pair. [is_unit_column_at] is stated as
    whole-column equality to [standard_basis] (Unit 11's existing
    basis-vector representation), not reinvented pointwise: this
    reuses the exact conclusion shape already produced by
    [pivot_output_column]/[pivot_step_some_column], so the Unit 15
    bridge theorem below is a one-line wrapper rather than a
    re-derivation, and pointwise facts ([standard_basis_nth_eq],
    [standard_basis_nth_neq]) remain available whenever needed by
    unfolding. *)

Record CompletedPivot
    (m n : nat)
    : Type := {
  completed_pivot_column :
    Fin.t n;
  completed_pivot_row :
    Fin.t m
}.

Arguments completed_pivot_column {m n}.
Arguments completed_pivot_row {m n}.

Definition is_unit_column_at
    {m n : nat}
    (A : QMatrix m n)
    (column : Fin.t n)
    (pivot_row : Fin.t m)
    : Prop :=
  Vector.nth A column = standard_basis pivot_row.

(** ** 3. The Unit 15 bridge theorem *)

Theorem pivot_step_establishes_unit_column
    {m n : nat} (A : QMatrix m n) (pivot_row : Fin.t m) (pivot_col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n) :
  pivot_step A pivot_row pivot_col candidates = Some result ->
  is_unit_column_at (pivot_step_output result) pivot_col pivot_row.
Proof.
  intro H.
  unfold is_unit_column_at.
  apply (pivot_step_some_column A pivot_row pivot_col candidates result H).
Qed.

(** ** 4. Preservation of a distinct unit column by a later pivot

    Two helpers isolate why a later pivot cannot disturb an already-
    established unit column at a row distinct from both the pivot row
    and the source row it swaps in: normalisation (swap then scale)
    only ever touches the pivot and source coordinates, both zero in
    the untouched unit column; clearing only ever adds a multiple of
    the (always-zero-there) pivot coordinate to other rows, a no-op
    everywhere once that coordinate is zero. *)

Lemma run_normalise_ops_distinct_unchanged
    {m n : nat} (A : QMatrix m n) (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n)
    (earlier_row : Fin.t m) :
  earlier_row <> pivot_row ->
  earlier_row <> source_row ->
  run_row_operations
    (pivot_normalise_operations A pivot_row source_row pivot_col)
    (standard_basis earlier_row)
  = standard_basis earlier_row.
Proof.
  intros Hne1 Hne2.
  unfold pivot_normalise_operations.
  simpl.
  assert (Hswap :
    swap_entries source_row pivot_row (standard_basis earlier_row)
    = standard_basis earlier_row).
  { apply vec_ext. intro k.
    destruct (Fin.eq_dec k source_row) as [Heq | Hneq1].
    - subst k.
      rewrite swap_entries_nth_i.
      rewrite (standard_basis_nth_neq pivot_row earlier_row (fun H => Hne1 (eq_sym H))).
      symmetry.
      apply (standard_basis_nth_neq source_row earlier_row (fun H => Hne2 (eq_sym H))).
    - destruct (Fin.eq_dec k pivot_row) as [Heq2 | Hneq2].
      + subst k.
        rewrite swap_entries_nth_j.
        rewrite (standard_basis_nth_neq source_row earlier_row (fun H => Hne2 (eq_sym H))).
        symmetry.
        apply (standard_basis_nth_neq pivot_row earlier_row (fun H => Hne1 (eq_sym H))).
      + rewrite (swap_entries_nth_other source_row pivot_row k (standard_basis earlier_row) Hneq1 Hneq2).
        reflexivity. }
  rewrite Hswap.
  apply vec_ext. intro k.
  destruct (Fin.eq_dec k pivot_row) as [Heq | Hneq].
  - subst k.
    rewrite scale_entry_nth_eq.
    rewrite (standard_basis_nth_neq pivot_row earlier_row (fun H => Hne1 (eq_sym H))).
    ring.
  - rewrite
      (scale_entry_nth_neq pivot_row k
         (Qcinv (pivot_coefficient A source_row pivot_col))
         (standard_basis earlier_row) Hneq).
    reflexivity.
Qed.

Lemma run_clear_ops_zero_pivot_unchanged
    {m : nat} (pivot_row : Fin.t m) (column : QVec m) (rows : list (Fin.t m)) :
  ~ In pivot_row rows ->
  forall x : QVec m,
    Vector.nth x pivot_row = 0 ->
    run_row_operations
      (map (fun r => RowAdd r pivot_row (- Vector.nth column r)) rows) x
    = x.
Proof.
  induction rows as [| r rest IH].
  - intros _ x _. reflexivity.
  - intros Hnotin x Hzero.
    assert (Hr_ne : r <> pivot_row).
    { intro Heq. apply Hnotin. left. exact Heq. }
    assert (Hnotin_rest : ~ In pivot_row rest).
    { intro Hin. apply Hnotin. right. exact Hin. }
    simpl.
    assert (Hxeq : add_scaled_entry r pivot_row (- Vector.nth column r) x = x).
    { apply vec_ext. intro k.
      destruct (Fin.eq_dec k r) as [Heq | Hneq].
      - subst k.
        rewrite add_scaled_entry_nth_target.
        rewrite Hzero.
        ring.
      - rewrite (add_scaled_entry_nth_neq r pivot_row k (- Vector.nth column r) x Hneq).
        reflexivity. }
    rewrite Hxeq.
    apply (IH Hnotin_rest x Hzero).
Qed.

Theorem pivot_step_preserves_distinct_unit_column
    {m n : nat} (A : QMatrix m n) (pivot_row source_row : Fin.t m) (pivot_col : Fin.t n)
    (earlier_column : Fin.t n) (earlier_row : Fin.t m) :
  earlier_row <> pivot_row ->
  earlier_row <> source_row ->
  is_unit_column_at A earlier_column earlier_row ->
  is_unit_column_at
    (pivot_output_matrix A pivot_row source_row pivot_col)
    earlier_column earlier_row.
Proof.
  intros Hne1 Hne2 Hunit.
  unfold is_unit_column_at in Hunit |- *.
  rewrite (pivot_output_column_action A pivot_row source_row pivot_col earlier_column).
  rewrite Hunit.
  unfold pivot_operations.
  rewrite run_row_operations_app.
  rewrite (run_normalise_ops_distinct_unchanged A pivot_row source_row pivot_col earlier_row Hne1 Hne2).
  apply run_clear_ops_zero_pivot_unchanged.
  - apply rows_except_notin.
  - apply (standard_basis_nth_neq pivot_row earlier_row (fun H => Hne1 (eq_sym H))).
Qed.

(** ** 5. Recorded pivot rows are unavailable

    The narrow invariant needed to know a later pivot's selected row
    is distinct from any earlier recorded pivot row: every row that
    ever appears in a [PivotColumn] trace entry is absent from the
    *current* available-row list. Since a later pivot's selected row
    is, by construction, drawn from the current available list (via
    [first_nonzero_available_row]/[pivot_step]'s search), this rules
    out re-selecting any previously recorded row. *)

Definition recorded_pivot_rows_unavailable
    {m n : nat}
    (state : EliminationState m n)
    : Prop :=
  forall col row,
    In (PivotColumn col row) (elimination_trace state) ->
    ~ In row (elimination_available_rows state).

Theorem initial_recorded_pivot_rows_unavailable
    {m n : nat} (A : QMatrix m n) :
  recorded_pivot_rows_unavailable (initial_elimination_state A).
Proof.
  unfold recorded_pivot_rows_unavailable, initial_elimination_state.
  simpl.
  intros col row Hin.
  destruct Hin.
Qed.

Theorem elimination_step_preserves_recorded_pivot_rows_unavailable
    {m n : nat} (col : Fin.t n) (state : EliminationState m n) :
  recorded_pivot_rows_unavailable state ->
  recorded_pivot_rows_unavailable (elimination_step col state).
Proof.
  intro Hinv.
  unfold elimination_step.
  destruct
    (first_nonzero_available_row
       (elimination_matrix state) col (elimination_available_rows state))
    as [row |] eqn:Hfind.
  - destruct
      (pivot_step
         (elimination_matrix state) row col (elimination_available_rows state))
      as [result |] eqn:Hpivot.
    + unfold recorded_pivot_rows_unavailable.
      simpl.
      intros col' row' Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * assert (Hold : ~ In row' (elimination_available_rows state)) by exact (Hinv col' row' Hin).
        intro Hnew.
        apply Hold.
        exact (proj1 (in_remove Fin.eq_dec (elimination_available_rows state) row' row Hnew)).
      * destruct Hin as [Heq | []].
        injection Heq as Heqcol Heqrow.
        subst col' row'.
        apply remove_In.
    + unfold recorded_pivot_rows_unavailable.
      simpl.
      intros col' row' Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * exact (Hinv col' row' Hin).
      * destruct Hin as [Heq | []]. discriminate Heq.
  - unfold recorded_pivot_rows_unavailable.
    simpl.
    intros col' row' Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + exact (Hinv col' row' Hin).
    + destruct Hin as [Heq | []]. discriminate Heq.
Qed.

Theorem eliminate_columns_preserves_recorded_pivot_rows_unavailable
    {m n : nat} (columns : list (Fin.t n)) (state : EliminationState m n) :
  recorded_pivot_rows_unavailable state ->
  recorded_pivot_rows_unavailable (eliminate_columns columns state).
Proof.
  induction columns as [| col rest IH] in state |- *.
  - intro H. exact H.
  - intro H.
    simpl.
    apply IH.
    apply elimination_step_preserves_recorded_pivot_rows_unavailable.
    exact H.
Qed.

(** ** 6. Extracting completed pivots from the trace *)

Fixpoint completed_pivots
    {m n : nat}
    (trace : list (EliminationTraceEntry m n))
    : list (CompletedPivot m n) :=
  match trace with
  | [] => []
  | SkipColumn _ :: rest => completed_pivots rest
  | PivotColumn col row :: rest =>
      {| completed_pivot_column := col; completed_pivot_row := row |}
      :: completed_pivots rest
  end.

Lemma completed_pivots_app
    {m n : nat} (t1 t2 : list (EliminationTraceEntry m n)) :
  completed_pivots (t1 ++ t2) = completed_pivots t1 ++ completed_pivots t2.
Proof.
  induction t1 as [| e rest IH].
  - reflexivity.
  - destruct e as [c | c r]; simpl; rewrite IH; reflexivity.
Qed.

Lemma completed_pivots_in_trace
    {m n : nat} (trace : list (EliminationTraceEntry m n)) (pivot : CompletedPivot m n) :
  In pivot (completed_pivots trace) ->
  In (PivotColumn (completed_pivot_column pivot) (completed_pivot_row pivot)) trace.
Proof.
  induction trace as [| e rest IH].
  - intro H. destruct H.
  - destruct e as [c | c r]; simpl.
    + intro H. right. apply IH. exact H.
    + intro H. destruct H as [Heq | H].
      * left. rewrite <- Heq. reflexivity.
      * right. apply IH. exact H.
Qed.

(** ** 7. The completed-pivot invariant

    Deliberately silent on order, on skipped columns, and on anything
    beyond the exact unit-column claim already established per
    recorded pivot. *)

Definition completed_pivots_hold
    {m n : nat}
    (state : EliminationState m n)
    : Prop :=
  forall pivot,
    In pivot (completed_pivots (elimination_trace state)) ->
    is_unit_column_at
      (elimination_matrix state)
      (completed_pivot_column pivot)
      (completed_pivot_row pivot).

Theorem initial_completed_pivots_hold
    {m n : nat} (A : QMatrix m n) :
  completed_pivots_hold (initial_elimination_state A).
Proof.
  unfold completed_pivots_hold, initial_elimination_state.
  simpl.
  intros pivot Hin.
  destruct Hin.
Qed.

Theorem elimination_step_preserves_completed_pivots
    {m n : nat} (col : Fin.t n) (state : EliminationState m n) :
  completed_pivots_hold state ->
  recorded_pivot_rows_unavailable state ->
  completed_pivots_hold (elimination_step col state).
Proof.
  intros Hhold Hunavail.
  unfold elimination_step.
  destruct
    (first_nonzero_available_row
       (elimination_matrix state) col (elimination_available_rows state))
    as [row |] eqn:Hfind.
  - destruct
      (pivot_step
         (elimination_matrix state) row col (elimination_available_rows state))
      as [result |] eqn:Hpivot.
    + unfold completed_pivots_hold.
      simpl.
      intros pivot Hin.
      rewrite completed_pivots_app in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin_earlier | Hin_new].
      * assert (Htrace : In (PivotColumn (completed_pivot_column pivot) (completed_pivot_row pivot))
                            (elimination_trace state)).
        { apply completed_pivots_in_trace. exact Hin_earlier. }
        pose proof (Hunavail (completed_pivot_column pivot) (completed_pivot_row pivot) Htrace) as Hrow_unavail.
        assert (Hne_row : completed_pivot_row pivot <> row).
        { intro Heq. apply Hrow_unavail. rewrite Heq.
          exact (proj1 (find_nonzero_row_some (elimination_matrix state) col
                          (elimination_available_rows state) row Hfind)). }
        assert (Hne_source : completed_pivot_row pivot <> pivot_step_source result).
        { intro Heq. apply Hrow_unavail. rewrite Heq.
          exact (proj1 (pivot_step_some_source (elimination_matrix state) row col
                          (elimination_available_rows state) result Hpivot)). }
        rewrite (pivot_step_some_output (elimination_matrix state) row col
                   (elimination_available_rows state) result Hpivot).
        apply pivot_step_preserves_distinct_unit_column.
        -- exact Hne_row.
        -- exact Hne_source.
        -- apply Hhold. exact Hin_earlier.
      * simpl in Hin_new.
        destruct Hin_new as [Heq | []].
        rewrite <- Heq.
        simpl.
        apply (pivot_step_establishes_unit_column (elimination_matrix state) row col
                 (elimination_available_rows state) result Hpivot).
    + unfold completed_pivots_hold.
      simpl.
      intros pivot Hin.
      rewrite completed_pivots_app in Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * apply Hhold. exact Hin.
      * simpl in Hin. destruct Hin.
  - unfold completed_pivots_hold.
    simpl.
    intros pivot Hin.
    rewrite completed_pivots_app in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply Hhold. exact Hin.
    + simpl in Hin. destruct Hin.
Qed.

Theorem eliminate_columns_preserves_completed_pivots
    {m n : nat} (columns : list (Fin.t n)) (state : EliminationState m n) :
  completed_pivots_hold state ->
  recorded_pivot_rows_unavailable state ->
  completed_pivots_hold (eliminate_columns columns state) /\
  recorded_pivot_rows_unavailable (eliminate_columns columns state).
Proof.
  induction columns as [| col rest IH] in state |- *.
  - intros Hhold Hunavail. split; assumption.
  - intros Hhold Hunavail.
    apply IH.
    + apply elimination_step_preserves_completed_pivots; assumption.
    + apply elimination_step_preserves_recorded_pivot_rows_unavailable; assumption.
Qed.

Theorem run_elimination_completed_pivots
    {m n : nat} (A : QMatrix m n) :
  completed_pivots_hold (run_elimination A).
Proof.
  unfold run_elimination.
  apply
    (proj1
       (eliminate_columns_preserves_completed_pivots
          (all_columns n) (initial_elimination_state A)
          (initial_completed_pivots_hold A)
          (initial_recorded_pivot_rows_unavailable A))).
Qed.

(** ** 8. Accumulated-sequence validity and invertibility

    Direct reuse of Unit 14's own sequence theory — no new inverse-
    sequence algorithm is introduced. *)

Theorem elimination_step_preserves_sequence_valid
    {m n : nat} (col : Fin.t n) (state : EliminationState m n) :
  row_operation_sequence_valid (elimination_operations state) ->
  row_operation_sequence_valid (elimination_operations (elimination_step col state)).
Proof.
  intro Hvalid.
  unfold elimination_step.
  destruct
    (first_nonzero_available_row
       (elimination_matrix state) col (elimination_available_rows state))
    as [row |] eqn:Hfind.
  - destruct
      (pivot_step
         (elimination_matrix state) row col (elimination_available_rows state))
      as [result |] eqn:Hpivot.
    + simpl.
      unfold row_operation_sequence_valid.
      apply Forall_app.
      split.
      * exact Hvalid.
      * apply
          (pivot_step_some_valid
             (elimination_matrix state) row col
             (elimination_available_rows state) result Hpivot).
    + exact Hvalid.
  - exact Hvalid.
Qed.

Theorem eliminate_columns_preserves_sequence_valid
    {m n : nat} (columns : list (Fin.t n)) (state : EliminationState m n) :
  row_operation_sequence_valid (elimination_operations state) ->
  row_operation_sequence_valid (elimination_operations (eliminate_columns columns state)).
Proof.
  induction columns as [| col rest IH] in state |- *.
  - intro H. exact H.
  - intro H.
    simpl.
    apply IH.
    apply elimination_step_preserves_sequence_valid.
    exact H.
Qed.

Theorem run_elimination_sequence_valid
    {m n : nat} (A : QMatrix m n) :
  row_operation_sequence_valid (elimination_operations (run_elimination A)).
Proof.
  unfold run_elimination.
  apply eliminate_columns_preserves_sequence_valid.
  unfold initial_elimination_state.
  simpl.
  unfold row_operation_sequence_valid.
  constructor.
Qed.

Theorem run_elimination_sequence_invertible
    {m n : nat} (A : QMatrix m n) :
  matrix_inverse_pair
    (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
    (row_operation_sequence_matrix
       (inverse_row_operation_sequence (elimination_operations (run_elimination A)))).
Proof.
  apply row_operation_sequence_inverse_pair.
  apply run_elimination_sequence_valid.
Qed.

(** ** 9. Whole-run linear-system preservation and reflection

    Stated in the project's existing form, [matrix_apply A x = b], with
    the right-hand side transformed by the same accumulated sequence —
    not silently omitted. Assembled from [run_elimination_correct] and
    Unit 14's [row_operation_sequence_equation_iff]; no equation
    semantics is rebuilt. *)

Theorem run_elimination_solution_iff
    {m n : nat} (A : QMatrix m n) (b : QVec m) (x : QVec n) :
  matrix_apply A x = b <->
  matrix_apply (elimination_matrix (run_elimination A)) x
  = matrix_apply
      (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
      b.
Proof.
  rewrite (run_elimination_correct A).
  apply row_operation_sequence_equation_iff.
  apply run_elimination_sequence_valid.
Qed.

Theorem run_elimination_preserves_solutions
    {m n : nat} (A : QMatrix m n) (b : QVec m) (x : QVec n) :
  matrix_apply A x = b ->
  matrix_apply (elimination_matrix (run_elimination A)) x
  = matrix_apply
      (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
      b.
Proof. apply run_elimination_solution_iff. Qed.

Theorem run_elimination_reflects_solutions
    {m n : nat} (A : QMatrix m n) (b : QVec m) (x : QVec n) :
  matrix_apply (elimination_matrix (run_elimination A)) x
  = matrix_apply
      (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
      b ->
  matrix_apply A x = b.
Proof. apply run_elimination_solution_iff. Qed.

(** ** 10. The final collecting theorem

    Exactly the three established layers — nothing about echelon
    shape, rank, uniqueness, or canonicity. *)

Theorem run_elimination_correctness
    {m n : nat} (A : QMatrix m n) :
  elimination_state_correct A (run_elimination A) /\
  completed_pivots_hold (run_elimination A) /\
  (forall (b : QVec m) (x : QVec n),
     matrix_apply A x = b <->
     matrix_apply (elimination_matrix (run_elimination A)) x
     = matrix_apply
         (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
         b).
Proof.
  split.
  - apply run_elimination_correct.
  - split.
    + apply run_elimination_completed_pivots.
    + intros b x. apply run_elimination_solution_iff.
Qed.

(** ** 11. Concrete proof probes over the Unit 16a example matrices *)

(** *** 11.1. Zero matrix *)

Example probe_correctness_zero_matrix :
  elimination_state_correct zero_mat2 (run_elimination zero_mat2).
Proof. apply run_elimination_correct. Qed.

Example probe_completed_pivots_zero_matrix :
  completed_pivots (elimination_trace (run_elimination zero_mat2)) = [].
Proof. vm_compute. reflexivity. Qed.

Example probe_final_matrix_zero_matrix :
  elimination_matrix (run_elimination zero_mat2) = zero_mat2.
Proof. vm_compute. reflexivity. Qed.

(** *** 11.2. Immediate pivot *)

Example probe_immediate_pivot_unit_column :
  is_unit_column_at (elimination_matrix (run_elimination piv2_mat)) Fin.F1 Fin.F1.
Proof.
  apply (run_elimination_completed_pivots piv2_mat
           {| completed_pivot_column := Fin.F1; completed_pivot_row := Fin.F1 |}).
  vm_compute. left. reflexivity.
Qed.

Example probe_immediate_pivot_system_iff (b : QVec 2) (x : QVec 2) :
  matrix_apply piv2_mat x = b <->
  matrix_apply (elimination_matrix (run_elimination piv2_mat)) x
  = matrix_apply
      (row_operation_sequence_matrix (elimination_operations (run_elimination piv2_mat)))
      b.
Proof. apply run_elimination_solution_iff. Qed.

(** *** 11.3. Search past a zero row: the pivot column is a unit column
    at the later selected row, not the first row. *)

Example probe_search_past_zero_unit_column :
  is_unit_column_at
    (elimination_matrix (run_elimination past_zero_mat))
    Fin.F1 (Fin.FS Fin.F1).
Proof.
  apply (run_elimination_completed_pivots past_zero_mat
           {| completed_pivot_column := Fin.F1; completed_pivot_row := Fin.FS Fin.F1 |}).
  vm_compute. left. reflexivity.
Qed.

(** *** 11.4. Singular matrix: the successful pivot survives the later
    skipped column. (No unit-column claim is made, or makeable, for
    the skipped column itself — there is deliberately no theorem to
    that effect.) *)

Example probe_singular_pivot_survives_skip :
  is_unit_column_at (elimination_matrix (run_elimination sing_mat)) Fin.F1 Fin.F1.
Proof.
  apply (run_elimination_completed_pivots sing_mat
           {| completed_pivot_column := Fin.F1; completed_pivot_row := Fin.F1 |}).
  vm_compute. left. reflexivity.
Qed.

(** *** 11.5. Wide matrix: both recorded pivots survive the skipped
    third column. *)

Example probe_wide_pivot1_survives :
  is_unit_column_at (elimination_matrix (run_elimination wide_mat)) Fin.F1 Fin.F1.
Proof.
  apply (run_elimination_completed_pivots wide_mat
           {| completed_pivot_column := Fin.F1; completed_pivot_row := Fin.F1 |}).
  vm_compute. left. reflexivity.
Qed.

Example probe_wide_pivot2_survives :
  is_unit_column_at
    (elimination_matrix (run_elimination wide_mat))
    (Fin.FS Fin.F1) (Fin.FS Fin.F1).
Proof.
  apply (run_elimination_completed_pivots wide_mat
           {| completed_pivot_column := Fin.FS Fin.F1; completed_pivot_row := Fin.FS Fin.F1 |}).
  vm_compute. right. left. reflexivity.
Qed.

(** *** 11.6. Tall matrix: both recorded pivots hold while one row
    remains available. *)

Example probe_tall_pivot1_holds :
  is_unit_column_at (elimination_matrix (run_elimination tall_mat)) Fin.F1 Fin.F1.
Proof.
  apply (run_elimination_completed_pivots tall_mat
           {| completed_pivot_column := Fin.F1; completed_pivot_row := Fin.F1 |}).
  vm_compute. left. reflexivity.
Qed.

Example probe_tall_pivot2_holds :
  is_unit_column_at
    (elimination_matrix (run_elimination tall_mat))
    (Fin.FS Fin.F1) (Fin.FS Fin.F1).
Proof.
  apply (run_elimination_completed_pivots tall_mat
           {| completed_pivot_column := Fin.FS Fin.F1; completed_pivot_row := Fin.FS Fin.F1 |}).
  vm_compute. right. left. reflexivity.
Qed.

(** *** 11.7. Zero-dimensional boundaries *)

Example probe_correctness_dim_0_0 :
  elimination_state_correct mat_0_0 (run_elimination mat_0_0).
Proof. apply run_elimination_correct. Qed.

Example probe_completed_pivots_hold_dim_0_0 :
  completed_pivots_hold (run_elimination mat_0_0).
Proof. apply run_elimination_completed_pivots. Qed.

Example probe_correctness_dim_0_1 :
  elimination_state_correct mat_0_1 (run_elimination mat_0_1).
Proof. apply run_elimination_correct. Qed.

Example probe_completed_pivots_hold_dim_0_1 :
  completed_pivots_hold (run_elimination mat_0_1).
Proof. apply run_elimination_completed_pivots. Qed.

Example probe_correctness_dim_2_0 :
  elimination_state_correct mat_2_0 (run_elimination mat_2_0).
Proof. apply run_elimination_correct. Qed.

Example probe_completed_pivots_hold_dim_2_0 :
  completed_pivots_hold (run_elimination mat_2_0).
Proof. apply run_elimination_completed_pivots. Qed.

(** *** 11.8. Determinism: reused as a premise, per Unit 16a's own
    determinism results — no new determinism proof is introduced. *)

Example probe_determinism_correctness_consistent :
  elimination_state_correct piv2_mat (run_elimination piv2_mat) /\
  elimination_state_correct piv2_mat (run_elimination piv2_mat).
Proof. split; apply run_elimination_correct. Qed.
