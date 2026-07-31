(** * The executable recursive elimination structure

    Unit 15 certified one complete Gauss-Jordan pivot step
    ([pivot_step]) together with its exact operation-sequence
    certificate. This unit assembles repeated calls to that certified
    primitive into an executable, deterministic recursive machine: a
    state carrying the current matrix, the accumulated row-operation
    sequence, the rows still available for future pivots, and an
    operational trace of what happened at each processed column.

    Unit 16a proves only what is needed to make the machine
    executable and to demonstrate its behaviour on concrete examples.
    It does NOT prove:

    1. that the accumulated operation sequence transforms the
       original matrix into the stored current matrix;
    2. that accumulated operations are globally invertible as a
       composed transformation, beyond whatever [matrix_inverse_pair]
       facts already exist per operation/sequence in Units 14-15;
    3. that earlier pivot columns are preserved by later pivot steps;
    4. that the output is in row-echelon form;
    5. that the output is in reduced row-echelon form;
    6. that the selected pivot rows or columns characterise matrix
       rank;
    7. that the output is canonical;
    8. that elimination preserves or reflects solutions of a linear
       system;
    9. that the final matrix is equivalent to the input under the
       full matrix relation;
    10. that the trace is a proof certificate;
    11. that pivot selection is numerically stable;
    12. that this is an efficient asymptotic implementation.

    All of the above are Unit 16b's obligations. This file is
    deliberately an executable state machine and nothing stronger.

    Pivot placement design: [elimination_step] uses the *found* row
    itself as the destination [pivot_row] passed to [pivot_step] (a
    "self-pivot" — no row is relocated to a fixed slot position by
    row index). This keeps the machine a direct, undecorated assembly
    of the certified Unit 15 primitive; it makes no claim about
    producing a staircase/echelon row order, which is exactly the
    kind of claim reserved for Unit 16b (or later). *)

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

Import ListNotations.

Open Scope Qc_scope.

(** ** 1. Deterministic column enumeration

    Exactly [all_rows]'s definition (Unit 15), applied to the column
    count instead of the row count. Not reused directly under the
    name [all_rows] because that name is specifically documented as
    enumerating *rows*; a distinct, equally thin [all_columns]
    definition keeps the two roles textually unambiguous, and the
    unit's required declaration list names it explicitly. *)

Definition all_columns
    (n : nat)
    : list (Fin.t n) :=
  Vector.to_list (all_positions n).

(** ** 2. The operational trace *)

Inductive EliminationTraceEntry
    (m n : nat)
    : Type :=
| SkipColumn :
    Fin.t n ->
    EliminationTraceEntry m n
| PivotColumn :
    Fin.t n ->
    Fin.t m ->
    EliminationTraceEntry m n.

Arguments SkipColumn {m n}.
Arguments PivotColumn {m n}.

(** ** 3. The elimination state

    No proof fields: not that the current matrix equals the
    accumulated sequence applied to the original matrix (Unit 16b's
    first theorem), not reduced-row-echelon-form, not
    completed-column preservation. *)

Record EliminationState
    (m n : nat)
    : Type := {
  elimination_matrix :
    QMatrix m n;
  elimination_operations :
    list (RowOperation m);
  elimination_available_rows :
    list (Fin.t m);
  elimination_trace :
    list (EliminationTraceEntry m n)
}.

Arguments elimination_matrix {m n}.
Arguments elimination_operations {m n}.
Arguments elimination_available_rows {m n}.
Arguments elimination_trace {m n}.

(** ** 4. The initial state

    The empty list is the actual neutral element of the existing
    row-operation-sequence representation: [row_operation_sequence_matrix
    [] = identity_matrix n] is literally the base case of that
    [Fixpoint] (Unit 14) — no separate identity-sequence definition is
    introduced. Available rows start as every row exactly once, in
    [all_rows]'s deterministic order (Unit 15, itself built on
    [all_positions], Unit 11). *)

Definition initial_elimination_state
    {m n : nat}
    (A : QMatrix m n)
    : EliminationState m n :=
  {|
    elimination_matrix := A;
    elimination_operations := [];
    elimination_available_rows := all_rows m;
    elimination_trace := []
  |}.

(** ** 5. Deterministic pivot-row search

    A thin alias for Unit 15's own [find_nonzero_row]: the same
    search algorithm [pivot_step] itself uses internally, not a
    second, independently-invented search. Its evidence
    ([find_nonzero_row_some], [find_nonzero_row_none]) is available on
    demand and is not eagerly repackaged into a sigma type here, since
    this unit proves no invariant that would consume it — that is
    Unit 16b's task. *)

Definition first_nonzero_available_row
    {m n : nat}
    (A : QMatrix m n)
    (col : Fin.t n)
    (available : list (Fin.t m))
    : option (Fin.t m) :=
  find_nonzero_row A col available.

(** ** 6. One-column transition

    On a search failure, the state is returned unchanged except for
    an appended skip entry. On a search success, the found row is
    used as its own destination pivot row (self-pivot; see the file
    header), [pivot_step] is invoked exactly as Unit 15 supplies it,
    and its output matrix and operation sequence are taken verbatim —
    never reconstructed or recomputed. The defensive inner [None]
    branch (reachable only if [pivot_step]'s internal search somehow
    disagreed with [first_nonzero_available_row]'s, which cannot
    happen since both call the identical [find_nonzero_row] on
    identical arguments) is handled as a skip purely to keep the
    function total without a dependent proof obligation — Unit 16a
    proves no theorem that depends on this branch being unreachable. *)

Definition elimination_step
    {m n : nat}
    (col : Fin.t n)
    (state : EliminationState m n)
    : EliminationState m n :=
  match
    first_nonzero_available_row
      (elimination_matrix state) col
      (elimination_available_rows state)
  with
  | None =>
      {|
        elimination_matrix := elimination_matrix state;
        elimination_operations := elimination_operations state;
        elimination_available_rows := elimination_available_rows state;
        elimination_trace :=
          elimination_trace state ++ [SkipColumn col]
      |}
  | Some row =>
      match
        pivot_step
          (elimination_matrix state) row col
          (elimination_available_rows state)
      with
      | None =>
          {|
            elimination_matrix := elimination_matrix state;
            elimination_operations := elimination_operations state;
            elimination_available_rows := elimination_available_rows state;
            elimination_trace :=
              elimination_trace state ++ [SkipColumn col]
          |}
      | Some result =>
          {|
            elimination_matrix := pivot_step_output result;
            elimination_operations :=
              elimination_operations state ++ pivot_step_operations result;
            elimination_available_rows :=
              remove Fin.eq_dec row (elimination_available_rows state);
            elimination_trace :=
              elimination_trace state ++ [PivotColumn col row]
          |}
      end
  end.

(** ** 7. Structural recursion over the remaining columns

    Structural on the [list (Fin.t n)] argument alone: each recursive
    call consumes exactly one list cell, regardless of the matrix's
    values, of whether a pivot was found, or of the state. Termination
    therefore does not depend on matrix rank, on any numerical
    property of the entries, or on any measure computed from the
    state — it is exactly Coq's ordinary structural-recursion
    guardedness check on [columns]. *)

Fixpoint eliminate_columns
    {m n : nat}
    (columns : list (Fin.t n))
    (state : EliminationState m n)
    : EliminationState m n :=
  match columns with
  | [] =>
      state
  | col :: rest =>
      eliminate_columns rest (elimination_step col state)
  end.

(** ** 8. The top-level runner *)

Definition run_elimination
    {m n : nat}
    (A : QMatrix m n)
    : EliminationState m n :=
  eliminate_columns (all_columns n) (initial_elimination_state A).

(** ** 9. Lightweight structural/computational lemmas *)

Lemma eliminate_columns_nil
    {m n : nat} (state : EliminationState m n) :
  eliminate_columns [] state = state.
Proof. reflexivity. Qed.

Lemma eliminate_columns_cons
    {m n : nat} (col : Fin.t n) (rest : list (Fin.t n))
    (state : EliminationState m n) :
  eliminate_columns (col :: rest) state
  = eliminate_columns rest (elimination_step col state).
Proof. reflexivity. Qed.

Lemma initial_trace_empty
    {m n : nat} (A : QMatrix m n) :
  elimination_trace (initial_elimination_state A) = [].
Proof. reflexivity. Qed.

Lemma initial_available_rows
    {m n : nat} (A : QMatrix m n) :
  elimination_available_rows (initial_elimination_state A) = all_rows m.
Proof. reflexivity. Qed.

Lemma skip_step_matrix_unchanged
    {m n : nat} (col : Fin.t n) (state : EliminationState m n) :
  first_nonzero_available_row
    (elimination_matrix state) col
    (elimination_available_rows state) = None ->
  elimination_matrix (elimination_step col state) = elimination_matrix state.
Proof.
  intro H. unfold elimination_step. rewrite H. reflexivity.
Qed.

Lemma skip_step_operations_unchanged
    {m n : nat} (col : Fin.t n) (state : EliminationState m n) :
  first_nonzero_available_row
    (elimination_matrix state) col
    (elimination_available_rows state) = None ->
  elimination_operations (elimination_step col state) = elimination_operations state.
Proof.
  intro H. unfold elimination_step. rewrite H. reflexivity.
Qed.

(** ** 10. Concrete execution probes

    These are permanent, executable demonstrations of the machine's
    behaviour — not temporary review artefacts — matching this unit's
    purpose item 6 ("concrete executable examples demonstrating
    pivot, skip, singular, rectangular and zero-dimensional
    behaviour"). Vector literals are built with explicit
    [Vector.cons]/[Vector.nil] rather than bracket notation, since
    importing [VectorNotations] would shadow [List]'s bare [In]/[nil]/
    [cons] used throughout this file (the same issue documented in
    Unit 15's probes) — confined avoidance, not a broadened interface. *)

(** *** 10.1. Zero matrix: every column is skipped *)

Definition zero_col2 : QVec 2 := Vector.cons Qc 0 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Definition zero_mat2 : QMatrix 2 2 :=
  Vector.cons (QVec 2) zero_col2 1 (Vector.cons (QVec 2) zero_col2 0 (Vector.nil (QVec 2))).

Example probe_zero_matrix_trace :
  elimination_trace (run_elimination zero_mat2)
  = [SkipColumn Fin.F1; SkipColumn (Fin.FS Fin.F1)].
Proof. vm_compute. reflexivity. Qed.

Example probe_zero_matrix_unchanged :
  elimination_matrix (run_elimination zero_mat2) = zero_mat2.
Proof. vm_compute. reflexivity. Qed.

Example probe_zero_matrix_no_operations :
  elimination_operations (run_elimination zero_mat2) = [].
Proof. vm_compute. reflexivity. Qed.

Example probe_zero_matrix_available_unchanged :
  elimination_available_rows (run_elimination zero_mat2) = all_rows 2.
Proof. vm_compute. reflexivity. Qed.

(** *** 10.2. One immediate pivot *)

Definition piv2_col0 : QVec 2 := Vector.cons Qc (1+1) 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Definition piv2_col1 : QVec 2 := Vector.cons Qc 0 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Definition piv2_mat : QMatrix 2 2 :=
  Vector.cons (QVec 2) piv2_col0 1 (Vector.cons (QVec 2) piv2_col1 0 (Vector.nil (QVec 2))).

Example probe_immediate_pivot_trace :
  elimination_trace (run_elimination piv2_mat)
  = [PivotColumn Fin.F1 Fin.F1; SkipColumn (Fin.FS Fin.F1)].
Proof. vm_compute. reflexivity. Qed.

Example probe_immediate_pivot_available :
  elimination_available_rows (run_elimination piv2_mat) = [Fin.FS Fin.F1].
Proof. vm_compute. reflexivity. Qed.

(** *** 10.3. Search past a zero row *)

Definition past_zero_col0 : QVec 2 := Vector.cons Qc 0 1 (Vector.cons Qc (1+1+1) 0 (Vector.nil Qc)).
Definition past_zero_mat : QMatrix 2 1 :=
  Vector.cons (QVec 2) past_zero_col0 0 (Vector.nil (QVec 2)).

Example probe_search_past_zero_row_trace :
  elimination_trace (run_elimination past_zero_mat)
  = [PivotColumn Fin.F1 (Fin.FS Fin.F1)].
Proof. vm_compute. reflexivity. Qed.

(** *** 10.4. Singular matrix: one pivotable, one forced skip *)

Definition sing_col0 : QVec 2 := Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Definition sing_col1 : QVec 2 := Vector.cons Qc (1+1) 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Definition sing_mat : QMatrix 2 2 :=
  Vector.cons (QVec 2) sing_col0 1 (Vector.cons (QVec 2) sing_col1 0 (Vector.nil (QVec 2))).

Example probe_singular_matrix_trace :
  elimination_trace (run_elimination sing_mat)
  = [PivotColumn Fin.F1 Fin.F1; SkipColumn (Fin.FS Fin.F1)].
Proof. vm_compute. reflexivity. Qed.

(** *** 10.5. More columns than rows *)

Definition wide_col0 : QVec 2 := Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc)).
Definition wide_col1 : QVec 2 := Vector.cons Qc 0 1 (Vector.cons Qc 1 0 (Vector.nil Qc)).
Definition wide_col2 : QVec 2 := Vector.cons Qc 1 1 (Vector.cons Qc 1 0 (Vector.nil Qc)).
Definition wide_mat : QMatrix 2 3 :=
  Vector.cons (QVec 2) wide_col0 2
    (Vector.cons (QVec 2) wide_col1 1
      (Vector.cons (QVec 2) wide_col2 0 (Vector.nil (QVec 2)))).

Example probe_wide_matrix_trace :
  elimination_trace (run_elimination wide_mat)
  = [ PivotColumn Fin.F1 Fin.F1
    ; PivotColumn (Fin.FS Fin.F1) (Fin.FS Fin.F1)
    ; SkipColumn (Fin.FS (Fin.FS Fin.F1)) ].
Proof. vm_compute. reflexivity. Qed.

Example probe_wide_matrix_available_empty :
  elimination_available_rows (run_elimination wide_mat) = [].
Proof. vm_compute. reflexivity. Qed.

(** *** 10.6. More rows than columns *)

Definition tall_col0 : QVec 3 :=
  Vector.cons Qc 1 2 (Vector.cons Qc 0 1 (Vector.cons Qc 0 0 (Vector.nil Qc))).
Definition tall_col1 : QVec 3 :=
  Vector.cons Qc 0 2 (Vector.cons Qc 1 1 (Vector.cons Qc 0 0 (Vector.nil Qc))).
Definition tall_mat : QMatrix 3 2 :=
  Vector.cons (QVec 3) tall_col0 1 (Vector.cons (QVec 3) tall_col1 0 (Vector.nil (QVec 3))).

Example probe_tall_matrix_available_unused_row :
  elimination_available_rows (run_elimination tall_mat) = [Fin.FS (Fin.FS Fin.F1)].
Proof. vm_compute. reflexivity. Qed.

Example probe_tall_matrix_trace :
  elimination_trace (run_elimination tall_mat)
  = [ PivotColumn Fin.F1 Fin.F1
    ; PivotColumn (Fin.FS Fin.F1) (Fin.FS Fin.F1) ].
Proof. vm_compute. reflexivity. Qed.

(** *** 10.7. Zero-dimensional boundaries *)

Definition mat_0_0 : QMatrix 0 0 := Vector.nil (QVec 0).

Example probe_dim_0_0_trace :
  elimination_trace (run_elimination mat_0_0) = [].
Proof. vm_compute. reflexivity. Qed.

Definition mat_0_1 : QMatrix 0 1 :=
  Vector.cons (QVec 0) (Vector.nil Qc) 0 (Vector.nil (QVec 0)).

Example probe_dim_0_1_trace :
  elimination_trace (run_elimination mat_0_1) = [SkipColumn Fin.F1].
Proof. vm_compute. reflexivity. Qed.

Definition mat_2_0 : QMatrix 2 0 := Vector.nil (QVec 2).

Example probe_dim_2_0_trace :
  elimination_trace (run_elimination mat_2_0) = [].
Proof. vm_compute. reflexivity. Qed.

Example probe_dim_2_0_available :
  elimination_available_rows (run_elimination mat_2_0) = all_rows 2.
Proof. vm_compute. reflexivity. Qed.

(** *** 10.8. Determinism: two independent evaluations of the same
    input reduce to the same result. *)

Example probe_determinism_run_1 :
  elimination_trace (run_elimination piv2_mat)
  = [PivotColumn Fin.F1 Fin.F1; SkipColumn (Fin.FS Fin.F1)].
Proof. vm_compute. reflexivity. Qed.

Example probe_determinism_run_2 :
  elimination_trace (run_elimination piv2_mat)
  = [PivotColumn Fin.F1 Fin.F1; SkipColumn (Fin.FS Fin.F1)].
Proof. vm_compute. reflexivity. Qed.

Example probe_determinism_matrix_eq :
  elimination_matrix (run_elimination piv2_mat)
  = elimination_matrix (run_elimination piv2_mat).
Proof. reflexivity. Qed.
