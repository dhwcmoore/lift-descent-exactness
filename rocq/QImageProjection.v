(** * An elimination-derived explicit projection onto a matrix's image

    Units 16a-16b certified an executable recursive elimination
    machine and proved three things about it: the stored matrix is
    exactly the accumulated row-operation sequence applied to the
    original; every recorded pivot column is an exact unit column at
    its recorded row; and the accumulated sequence preserves and
    reflects the represented linear system. This unit uses exactly
    that machinery, and nothing about row-echelon shape (which was
    never proved and is not needed), to construct an explicit,
    constructive linear projection of the ambient codomain [QVec m]
    onto [image_subspace] of a matrix.

    The construction: run elimination on [A], obtaining an invertible
    row-operation matrix [P] with [P A] canonical on the pivot
    columns; project ambient coordinates onto the *pivot rows* of the
    transformed space; conjugate that coordinate projection by [P]
    and its certified inverse. The result is algebraic and
    elimination-order-dependent — not orthogonal, not canonical, not
    claimed unique.

    This unit does NOT prove: row-echelon form; reduced row-echelon
    form; rank-nullity; that the pivot count equals rank; a canonical
    basis of the image; independence from pivot-search order;
    orthogonal projection; norm minimisation; numerical stability;
    determinant formulas; uniqueness of the projection or of a
    complementary subspace; ambient extension of arbitrary subspace
    maps; factorisation of any map through this construction; the
    final lift/descent obstruction equivalences; or any generalisation
    beyond finite rational coordinate spaces. *)

From Coq Require Import List.
From Coq Require Import QArith.
From Coq Require Import Qcanon.
From Coq Require Vector.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import LinearInstance.
From LiftDescent Require Import QSubspace.
From LiftDescent Require Import QFiniteCoordinates.
From LiftDescent Require Import QMatrixAlgebra.
From LiftDescent Require Import QElementaryRows.
From LiftDescent Require Import QRowOperationSequence.
From LiftDescent Require Import QPivotStep.
From LiftDescent Require Import QEliminationStructure.
From LiftDescent Require Import QEliminationCorrectness.

Import ListNotations.

Open Scope Qc_scope.

(** ** 1. Pivot rows, extracted from [completed_pivots] (Unit 16b) —
    no second recursive trace traversal. *)

Definition pivot_rows
    {m n : nat}
    (trace : list (EliminationTraceEntry m n))
    : list (Fin.t m) :=
  map completed_pivot_row (completed_pivots trace).

(** ** 2. Support on a row list *)

Definition supported_on
    {m : nat}
    (rows : list (Fin.t m))
    (v : QVec m)
    : Prop :=
  forall row,
    ~ In row rows ->
    Vector.nth v row = 0.

(** ** 3. Support closure helpers *)

Lemma supported_on_zero
    {m : nat} (rows : list (Fin.t m)) :
  supported_on rows (zero_vec m).
Proof.
  unfold supported_on. intros row _. apply zero_vec_nth.
Qed.

Lemma supported_on_vadd
    {m : nat} (rows : list (Fin.t m)) (u v : QVec m) :
  supported_on rows u -> supported_on rows v -> supported_on rows (vadd u v).
Proof.
  unfold supported_on. intros Hu Hv row Hnotin.
  rewrite vadd_nth, (Hu row Hnotin), (Hv row Hnotin). ring.
Qed.

Lemma supported_on_vscale
    {m : nat} (rows : list (Fin.t m)) (a : Qc) (v : QVec m) :
  supported_on rows v -> supported_on rows (vscale a v).
Proof.
  unfold supported_on. intros Hv row Hnotin.
  rewrite vscale_nth, (Hv row Hnotin). ring.
Qed.

Lemma supported_on_vsub
    {m : nat} (rows : list (Fin.t m)) (u v : QVec m) :
  supported_on rows u -> supported_on rows v -> supported_on rows (vsub u v).
Proof.
  unfold supported_on. intros Hu Hv row Hnotin.
  rewrite vsub_nth, (Hu row Hnotin), (Hv row Hnotin). ring.
Qed.

Lemma supported_on_vsum
    {m k : nat} (rows : list (Fin.t m)) (V : Vector.t (QVec m) k) :
  (forall i : Fin.t k, supported_on rows (Vector.nth V i)) ->
  supported_on rows (vsum V).
Proof.
  induction V as [| v k' V' IH].
  - intros _. apply supported_on_zero.
  - intro H.
    simpl.
    apply supported_on_vadd.
    + exact (H Fin.F1).
    + apply IH. intro i. exact (H (Fin.FS i)).
Qed.

Lemma supported_on_standard_basis
    {m : nat} (rows : list (Fin.t m)) (row : Fin.t m) :
  In row rows -> supported_on rows (standard_basis row).
Proof.
  unfold supported_on. intros Hin k Hnotin.
  apply (standard_basis_nth_neq k row).
  intro Heq. subst k. exact (Hnotin Hin).
Qed.

(** ** 4. Pivot rows are pairwise distinct

    Immediate from Unit 16b's [recorded_pivot_rows_unavailable]: a
    newly selected row is drawn from the current available list, so it
    cannot coincide with any already-recorded pivot row. No numerical
    matrix property is used. *)

Lemma pivot_rows_app
    {m n : nat} (t1 t2 : list (EliminationTraceEntry m n)) :
  pivot_rows (t1 ++ t2) = pivot_rows t1 ++ pivot_rows t2.
Proof.
  unfold pivot_rows. rewrite completed_pivots_app. apply map_app.
Qed.

Lemma pivot_rows_in_trace
    {m n : nat} (trace : list (EliminationTraceEntry m n)) (row : Fin.t m) :
  In row (pivot_rows trace) -> exists col, In (PivotColumn col row) trace.
Proof.
  unfold pivot_rows. intro H.
  apply in_map_iff in H.
  destruct H as [pivot [Heq Hin]].
  exists (completed_pivot_column pivot).
  rewrite <- Heq.
  apply completed_pivots_in_trace.
  exact Hin.
Qed.

Lemma pivot_rows_unavailable
    {m n : nat} (state : EliminationState m n) :
  recorded_pivot_rows_unavailable state ->
  forall row,
    In row (pivot_rows (elimination_trace state)) ->
    ~ In row (elimination_available_rows state).
Proof.
  intros Hunavail row Hin.
  destruct (pivot_rows_in_trace (elimination_trace state) row Hin) as [col Hcol].
  exact (Hunavail col row Hcol).
Qed.

Lemma NoDup_snoc
    {A : Type} (l : list A) (x : A) :
  NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  induction l as [| a l' IH].
  - intros _ _. apply NoDup_cons.
    + intro H. destruct H.
    + constructor.
  - intros Hnodup Hnotin.
    apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as [Ha Hl'].
    simpl.
    apply NoDup_cons.
    + intro Hin.
      apply in_app_or in Hin.
      destruct Hin as [Hin | Hin].
      * exact (Ha Hin).
      * simpl in Hin. destruct Hin as [Heq | []].
        apply Hnotin. left. symmetry. exact Heq.
    + apply IH.
      * exact Hl'.
      * intro Hin. apply Hnotin. right. exact Hin.
Qed.

Lemma pivot_rows_skip_unchanged
    {m n : nat} (trace : list (EliminationTraceEntry m n)) (col : Fin.t n) :
  pivot_rows (trace ++ [SkipColumn col]) = pivot_rows trace.
Proof.
  rewrite pivot_rows_app.
  simpl.
  apply app_nil_r.
Qed.

Theorem elimination_step_preserves_pivot_rows_nodup
    {m n : nat} (col : Fin.t n) (state : EliminationState m n) :
  NoDup (pivot_rows (elimination_trace state)) ->
  recorded_pivot_rows_unavailable state ->
  NoDup (pivot_rows (elimination_trace (elimination_step col state))).
Proof.
  intros Hnodup Hunavail.
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
      rewrite pivot_rows_app.
      simpl.
      assert (Hrow_avail : In row (elimination_available_rows state)).
      { exact (proj1 (find_nonzero_row_some (elimination_matrix state) col
                        (elimination_available_rows state) row Hfind)). }
      assert (Hnotin : ~ In row (pivot_rows (elimination_trace state))).
      { intro Hin.
        destruct (pivot_rows_in_trace (elimination_trace state) row Hin) as [c Hc].
        exact (Hunavail c row Hc Hrow_avail). }
      apply NoDup_snoc.
      * exact Hnodup.
      * exact Hnotin.
    + simpl. rewrite pivot_rows_skip_unchanged. exact Hnodup.
  - simpl. rewrite pivot_rows_skip_unchanged. exact Hnodup.
Qed.

Theorem eliminate_columns_preserves_pivot_rows_nodup
    {m n : nat} (columns : list (Fin.t n)) (state : EliminationState m n) :
  NoDup (pivot_rows (elimination_trace state)) ->
  recorded_pivot_rows_unavailable state ->
  NoDup (pivot_rows (elimination_trace (eliminate_columns columns state))).
Proof.
  induction columns as [| col rest IH] in state |- *.
  - intros H _. exact H.
  - intros Hnodup Hunavail.
    apply IH.
    + apply elimination_step_preserves_pivot_rows_nodup; assumption.
    + apply elimination_step_preserves_recorded_pivot_rows_unavailable; assumption.
Qed.

Theorem run_elimination_pivot_rows_nodup
    {m n : nat} (A : QMatrix m n) :
  NoDup (pivot_rows (elimination_trace (run_elimination A))).
Proof.
  unfold run_elimination.
  apply eliminate_columns_preserves_pivot_rows_nodup.
  - unfold initial_elimination_state, pivot_rows. simpl. constructor.
  - apply initial_recorded_pivot_rows_unavailable.
Qed.

(** ** 5. Final-column support

    [elimination_step] always calls [pivot_step] with the *found* row
    as its own destination (Unit 16a's self-pivot design). This small
    fact makes that syntactically explicit, letting the lemmas below
    use a single zero-hypothesis rather than Unit 16b's more general
    two-hypothesis form (kept general there since it does not assume
    self-pivoting; here we specifically reuse the exact call
    [elimination_step] makes). *)

Lemma pivot_step_self_source
    {m n : nat} (A : QMatrix m n) (row : Fin.t m) (col : Fin.t n)
    (candidates : list (Fin.t m)) (result : PivotStepData m n) :
  first_nonzero_available_row A col candidates = Some row ->
  pivot_step A row col candidates = Some result ->
  pivot_step_source result = row.
Proof.
  unfold first_nonzero_available_row, pivot_step.
  intro Hfind. rewrite Hfind. intro H. injection H as H. subst result. reflexivity.
Qed.

(** Reuses Unit 16b's [run_clear_ops_zero_pivot_unchanged] directly for
    the clearing half; only the normalisation half needs a fresh
    (simpler, single-hypothesis) proof, since here [pivot_row =
    source_row]. *)

Lemma run_normalise_ops_zero_at_unchanged
    {m n : nat} (A : QMatrix m n) (q : Fin.t m) (pivot_col : Fin.t n) (v : QVec m) :
  Vector.nth v q = 0 ->
  run_row_operations (pivot_normalise_operations A q q pivot_col) v = v.
Proof.
  intro Hzero.
  unfold pivot_normalise_operations.
  simpl.
  assert (Hswap : swap_entries q q v = v).
  { apply vec_ext. intro k.
    destruct (Fin.eq_dec k q) as [Heq | Hneq].
    - subst k. apply swap_entries_nth_i.
    - apply (swap_entries_nth_other q q k v Hneq Hneq). }
  rewrite Hswap.
  apply vec_ext. intro k.
  destruct (Fin.eq_dec k q) as [Heq | Hneq].
  - subst k. rewrite scale_entry_nth_eq, Hzero. ring.
  - rewrite (scale_entry_nth_neq q k (Qcinv (pivot_coefficient A q pivot_col)) v Hneq).
    reflexivity.
Qed.

Lemma run_pivot_operations_zero_at_unchanged
    {m n : nat} (A : QMatrix m n) (q : Fin.t m) (col : Fin.t n) (v : QVec m) :
  Vector.nth v q = 0 ->
  run_row_operations (pivot_operations A q q col) v = v.
Proof.
  intro Hzero.
  unfold pivot_operations.
  rewrite run_row_operations_app.
  rewrite (run_normalise_ops_zero_at_unchanged A q col v Hzero).
  apply run_clear_ops_zero_pivot_unchanged.
  - apply rows_except_notin.
  - exact Hzero.
Qed.

(** A column is "locked" once its current value is supported on the
    currently recorded pivot rows — the exact conclusion
    [pivot_step_establishes_unit_column]/[find_nonzero_row_none] give
    a column immediately after it is processed. *)

Definition column_locked
    {m n : nat} (state : EliminationState m n) (col : Fin.t n) : Prop :=
  supported_on
    (pivot_rows (elimination_trace state))
    (Vector.nth (elimination_matrix state) col).

Lemma pivot_rows_pivot_grown
    {m n : nat} (trace : list (EliminationTraceEntry m n)) (col : Fin.t n) (row : Fin.t m) :
  pivot_rows (trace ++ [PivotColumn col row]) = pivot_rows trace ++ [row].
Proof.
  rewrite pivot_rows_app. reflexivity.
Qed.

(** Once locked, a column stays locked no matter which other column is
    processed next: a later pivot's row is drawn from the available
    list, hence (by [pivot_rows_unavailable]) is not among the
    recorded pivot rows, hence the locked column's value is already
    zero there, hence [run_pivot_operations_zero_at_unchanged] applies
    and the whole row-operation sequence is a no-op on it; and the
    target support set only grows, so the (unchanged) value remains
    supported. A skip changes nothing relevant. *)

Theorem elimination_step_preserves_column_locked
    {m n : nat} (col col' : Fin.t n) (state : EliminationState m n) :
  recorded_pivot_rows_unavailable state ->
  column_locked state col ->
  column_locked (elimination_step col' state) col.
Proof.
  intros Hunavail Hlocked.
  unfold elimination_step.
  destruct
    (first_nonzero_available_row
       (elimination_matrix state) col' (elimination_available_rows state))
    as [q |] eqn:Hfind.
  - destruct
      (pivot_step
         (elimination_matrix state) q col' (elimination_available_rows state))
      as [result |] eqn:Hpivot.
    + unfold column_locked. simpl.
      rewrite pivot_rows_pivot_grown.
      rewrite (pivot_step_some_output (elimination_matrix state) q col'
                 (elimination_available_rows state) result Hpivot).
      rewrite (pivot_step_self_source (elimination_matrix state) q col'
                 (elimination_available_rows state) result Hfind Hpivot).
      rewrite (pivot_output_column_action (elimination_matrix state) q q col' col).
      assert (Hqavail : In q (elimination_available_rows state)).
      { exact (proj1 (find_nonzero_row_some (elimination_matrix state) col'
                        (elimination_available_rows state) q Hfind)). }
      assert (Hqnotpivot : ~ In q (pivot_rows (elimination_trace state))).
      { intro Hin. exact (pivot_rows_unavailable state Hunavail q Hin Hqavail). }
      assert (Hzero : Vector.nth (Vector.nth (elimination_matrix state) col) q = 0).
      { apply Hlocked. exact Hqnotpivot. }
      rewrite (run_pivot_operations_zero_at_unchanged (elimination_matrix state) q col'
                 (Vector.nth (elimination_matrix state) col) Hzero).
      unfold supported_on. intros row Hrow.
      apply Hlocked.
      intro Hin. apply Hrow. apply in_or_app. left. exact Hin.
    + unfold column_locked. simpl.
      rewrite pivot_rows_skip_unchanged.
      exact Hlocked.
  - unfold column_locked. simpl.
    rewrite pivot_rows_skip_unchanged.
    exact Hlocked.
Qed.

(** ** 6. Every row is either recorded or still available

    The complement fact needed to turn [find_nonzero_row_none]'s
    "zero on every candidate" into "zero outside the recorded pivot
    rows" for a just-skipped column. *)

Definition rows_accounted
    {m n : nat} (state : EliminationState m n) : Prop :=
  forall row : Fin.t m,
    In row (pivot_rows (elimination_trace state)) \/
    In row (elimination_available_rows state).

Theorem initial_rows_accounted
    {m n : nat} (A : QMatrix m n) :
  rows_accounted (initial_elimination_state A).
Proof.
  unfold rows_accounted, initial_elimination_state.
  simpl.
  intro row. right. apply all_rows_complete.
Qed.

Theorem elimination_step_preserves_rows_accounted
    {m n : nat} (col : Fin.t n) (state : EliminationState m n) :
  rows_accounted state -> rows_accounted (elimination_step col state).
Proof.
  intro Hacc.
  unfold elimination_step.
  destruct
    (first_nonzero_available_row
       (elimination_matrix state) col (elimination_available_rows state))
    as [q |] eqn:Hfind.
  - destruct
      (pivot_step
         (elimination_matrix state) q col (elimination_available_rows state))
      as [result |] eqn:Hpivot.
    + unfold rows_accounted. simpl.
      rewrite pivot_rows_pivot_grown.
      intro row.
      destruct (Hacc row) as [Hin | Hin].
      * left. apply in_or_app. left. exact Hin.
      * destruct (Fin.eq_dec row q) as [Heq | Hneq].
        -- subst row. left. apply in_or_app. right. left. reflexivity.
        -- right. exact (in_in_remove Fin.eq_dec (elimination_available_rows state) Hneq Hin).
    + unfold rows_accounted. simpl.
      rewrite pivot_rows_skip_unchanged.
      exact Hacc.
  - unfold rows_accounted. simpl.
    rewrite pivot_rows_skip_unchanged.
    exact Hacc.
Qed.

Theorem eliminate_columns_preserves_rows_accounted
    {m n : nat} (columns : list (Fin.t n)) (state : EliminationState m n) :
  rows_accounted state -> rows_accounted (eliminate_columns columns state).
Proof.
  induction columns as [| c rest IH] in state |- *.
  - intro H. exact H.
  - intro H. simpl. apply IH. apply elimination_step_preserves_rows_accounted. exact H.
Qed.

Theorem run_elimination_rows_accounted
    {m n : nat} (A : QMatrix m n) :
  rows_accounted (run_elimination A).
Proof.
  unfold run_elimination.
  apply eliminate_columns_preserves_rows_accounted.
  apply initial_rows_accounted.
Qed.

(** ** 7. Every processed column is locked immediately

    Combines [pivot_output_entry_other] (pivot branch) with
    [find_nonzero_row_none] plus [rows_accounted] (skip branch, both
    the outer search failure and the defensive inner one). *)

Theorem elimination_step_locks_processed_column
    {m n : nat} (col : Fin.t n) (state : EliminationState m n) :
  rows_accounted state ->
  column_locked (elimination_step col state) col.
Proof.
  intro Hacc.
  unfold elimination_step, column_locked.
  destruct
    (first_nonzero_available_row
       (elimination_matrix state) col (elimination_available_rows state))
    as [q |] eqn:Hfind.
  - destruct
      (pivot_step
         (elimination_matrix state) q col (elimination_available_rows state))
      as [result |] eqn:Hpivot.
    + simpl.
      rewrite (pivot_step_some_output (elimination_matrix state) q col
                 (elimination_available_rows state) result Hpivot).
      rewrite pivot_rows_pivot_grown.
      unfold supported_on. intros row Hrow.
      assert (Hne : row <> q).
      { intro Heq. subst row. apply Hrow. apply in_or_app. right. left. reflexivity. }
      change
        (matrix_entry
           (pivot_output_matrix (elimination_matrix state) q (pivot_step_source result) col)
           row col = 0).
      apply pivot_output_entry_other.
      * exact (proj2 (pivot_step_some_source (elimination_matrix state) q col
                        (elimination_available_rows state) result Hpivot)).
      * exact Hne.
    + exfalso.
      unfold first_nonzero_available_row in Hfind.
      unfold pivot_step in Hpivot.
      rewrite Hfind in Hpivot.
      discriminate Hpivot.
  - simpl.
    rewrite pivot_rows_skip_unchanged.
    unfold supported_on. intros row Hrow.
    destruct (Hacc row) as [Hin | Hin].
    + exfalso. apply Hrow. exact Hin.
    + change (matrix_entry (elimination_matrix state) row col = 0).
      apply (find_nonzero_row_none (elimination_matrix state) col
               (elimination_available_rows state) Hfind row Hin).
Qed.

(** ** 8. The central structural theorem: every final column is
    supported on the final pivot rows *)

Lemma eliminate_columns_app
    {m n : nat} (l1 l2 : list (Fin.t n)) (state : EliminationState m n) :
  eliminate_columns (l1 ++ l2) state = eliminate_columns l2 (eliminate_columns l1 state).
Proof.
  induction l1 as [| c rest IH] in state |- *.
  - reflexivity.
  - simpl. apply IH.
Qed.

Theorem eliminate_columns_preserves_column_locked
    {m n : nat} (columns : list (Fin.t n)) (col : Fin.t n) (state : EliminationState m n) :
  recorded_pivot_rows_unavailable state ->
  column_locked state col ->
  column_locked (eliminate_columns columns state) col.
Proof.
  induction columns as [| c rest IH] in state |- *.
  - intros _ Hlocked. exact Hlocked.
  - intros Hunavail Hlocked.
    simpl.
    apply IH.
    + apply elimination_step_preserves_recorded_pivot_rows_unavailable. exact Hunavail.
    + apply elimination_step_preserves_column_locked; assumption.
Qed.

Lemma all_columns_complete (n : nat) (col : Fin.t n) : In col (all_columns n).
Proof.
  unfold all_columns.
  apply (proj1 (Vector.to_list_In (Fin.t n) col n (all_positions n))).
  rewrite <- (all_positions_nth n col).
  apply Vector.In_nth.
Qed.

Theorem run_elimination_column_supported
    {m n : nat} (A : QMatrix m n) (col : Fin.t n) :
  supported_on
    (pivot_rows (elimination_trace (run_elimination A)))
    (Vector.nth (elimination_matrix (run_elimination A)) col).
Proof.
  unfold run_elimination.
  destruct (in_split col (all_columns n) (all_columns_complete n col)) as [prefix [suffix Heq]].
  rewrite Heq.
  rewrite eliminate_columns_app.
  change (eliminate_columns (col :: suffix) (eliminate_columns prefix (initial_elimination_state A)))
    with (eliminate_columns suffix
            (elimination_step col (eliminate_columns prefix (initial_elimination_state A)))).
  apply eliminate_columns_preserves_column_locked.
  - apply elimination_step_preserves_recorded_pivot_rows_unavailable.
    apply eliminate_columns_preserves_recorded_pivot_rows_unavailable.
    apply initial_recorded_pivot_rows_unavailable.
  - apply elimination_step_locks_processed_column.
    apply eliminate_columns_preserves_rows_accounted.
    apply initial_rows_accounted.
Qed.

(** ** 9. The coordinate projection

    Retains coordinates in a supplied row list, zeroes every other
    coordinate. Built via [Vector.map] over [all_positions m] (Unit
    11) rather than [Vector.replace]-threading, since the natural
    proof obligations here are pointwise. *)

Definition coordinate_projection_fun
    {m : nat} (rows : list (Fin.t m)) (v : QVec m) : QVec m :=
  Vector.map (fun i => if in_dec Fin.eq_dec i rows then Vector.nth v i else 0) (all_positions m).

Lemma coordinate_projection_fun_nth
    {m : nat} (rows : list (Fin.t m)) (v : QVec m) (i : Fin.t m) :
  Vector.nth (coordinate_projection_fun rows v) i
  = if in_dec Fin.eq_dec i rows then Vector.nth v i else 0.
Proof.
  unfold coordinate_projection_fun.
  rewrite (Vector.nth_map _ _ i i eq_refl).
  rewrite (all_positions_nth m i).
  reflexivity.
Qed.

Theorem coordinate_projection_on_member
    {m : nat} (rows : list (Fin.t m)) (v : QVec m) (i : Fin.t m) :
  In i rows -> Vector.nth (coordinate_projection_fun rows v) i = Vector.nth v i.
Proof.
  intro Hin.
  rewrite coordinate_projection_fun_nth.
  destruct (in_dec Fin.eq_dec i rows) as [_ | Hnotin].
  - reflexivity.
  - exfalso. exact (Hnotin Hin).
Qed.

Theorem coordinate_projection_off_member
    {m : nat} (rows : list (Fin.t m)) (v : QVec m) (i : Fin.t m) :
  ~ In i rows -> Vector.nth (coordinate_projection_fun rows v) i = 0.
Proof.
  intro Hnotin.
  rewrite coordinate_projection_fun_nth.
  destruct (in_dec Fin.eq_dec i rows) as [Hin | _].
  - exfalso. exact (Hnotin Hin).
  - reflexivity.
Qed.

Lemma coordinate_projection_fun_add
    {m : nat} (rows : list (Fin.t m)) (u v : QVec m) :
  coordinate_projection_fun rows (vadd u v)
  = vadd (coordinate_projection_fun rows u) (coordinate_projection_fun rows v).
Proof.
  apply vec_ext. intro i.
  rewrite vadd_nth, !coordinate_projection_fun_nth, vadd_nth.
  destruct (in_dec Fin.eq_dec i rows); ring.
Qed.

Lemma coordinate_projection_fun_scale
    {m : nat} (rows : list (Fin.t m)) (a : Qc) (v : QVec m) :
  coordinate_projection_fun rows (vscale a v)
  = vscale a (coordinate_projection_fun rows v).
Proof.
  apply vec_ext. intro i.
  rewrite vscale_nth, !coordinate_projection_fun_nth, vscale_nth.
  destruct (in_dec Fin.eq_dec i rows); ring.
Qed.

(** [coordinate_projection_linear] is not a separate theorem: linearity
    is exactly the two record fields below, per the project's own
    convention (Unit 1) — a separate restatement would be a duplicate. *)

Definition coordinate_projection
    {m : nat} (rows : list (Fin.t m)) : QLinearMap m m :=
  {|
    lmap := coordinate_projection_fun rows;
    lmap_add := coordinate_projection_fun_add rows;
    lmap_scale := coordinate_projection_fun_scale rows;
  |}.

Theorem coordinate_projection_fixes_supported
    {m : nat} (rows : list (Fin.t m)) (v : QVec m) :
  supported_on rows v -> lmap (coordinate_projection rows) v = v.
Proof.
  intro Hsupp.
  apply vec_ext. intro i.
  simpl lmap.
  rewrite coordinate_projection_fun_nth.
  destruct (in_dec Fin.eq_dec i rows) as [Hin | Hnotin].
  - reflexivity.
  - symmetry. apply Hsupp. exact Hnotin.
Qed.

Theorem coordinate_projection_output_supported
    {m : nat} (rows : list (Fin.t m)) (v : QVec m) :
  supported_on rows (lmap (coordinate_projection rows) v).
Proof.
  unfold supported_on. intros row Hnotin.
  simpl lmap.
  apply coordinate_projection_off_member.
  exact Hnotin.
Qed.

Theorem coordinate_projection_idempotent
    {m : nat} (rows : list (Fin.t m)) (v : QVec m) :
  lmap (coordinate_projection rows) (lmap (coordinate_projection rows) v)
  = lmap (coordinate_projection rows) v.
Proof.
  apply coordinate_projection_fixes_supported.
  apply coordinate_projection_output_supported.
Qed.

(** ** 10. The pivot-coordinate subspace *)

Definition pivot_coordinate_subspace
    {m : nat} (rows : list (Fin.t m)) : QSubspace m.
Proof.
  refine {|
    subspace_mem := supported_on rows;
    subspace_zero := supported_on_zero rows;
    subspace_add := supported_on_vadd rows;
    subspace_scale := supported_on_vscale rows;
  |}.
Defined.

(** ** 11. Forward inclusion: the final image is supported on the
    final pivot rows *)

Theorem final_image_supported
    {m n : nat} (A : QMatrix m n) (y : QVec m) :
  linear_image (linear_map_of_matrix (elimination_matrix (run_elimination A))) y ->
  supported_on (pivot_rows (elimination_trace (run_elimination A))) y.
Proof.
  intros [u Hu].
  rewrite <- Hu.
  simpl lmap.
  unfold matrix_apply.
  apply supported_on_vsum.
  intro i.
  rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl).
  apply supported_on_vscale.
  apply run_elimination_column_supported.
Qed.

(** ** 12. Reverse inclusion: every vector supported on the final pivot
    rows is in the final image, reconstructed from the recorded pivot
    columns. *)

Fixpoint pivot_preimage
    {m n : nat} (pivots : list (CompletedPivot m n)) (y : QVec m) : QVec n :=
  match pivots with
  | [] => zero_vec n
  | p :: rest =>
      vadd
        (vscale (Vector.nth y (completed_pivot_row p)) (standard_basis (completed_pivot_column p)))
        (pivot_preimage rest y)
  end.

Lemma pivot_preimage_ext
    {m n : nat} (L : list (CompletedPivot m n)) (y y' : QVec m) :
  (forall p, In p L -> Vector.nth y (completed_pivot_row p) = Vector.nth y' (completed_pivot_row p)) ->
  pivot_preimage L y = pivot_preimage L y'.
Proof.
  induction L as [| p rest IH].
  - intros _. reflexivity.
  - intro Heq.
    simpl.
    rewrite (Heq p (or_introl eq_refl)).
    rewrite (IH (fun p' Hp' => Heq p' (or_intror Hp'))).
    reflexivity.
Qed.

(** Handles zero pivots (empty [L]), rectangular matrices (no shape
    assumption anywhere), arbitrary trace order (only membership in
    [L] is used, never position), and distinct-but-not-increasing
    pivot rows ([NoDup] is exactly what blocks double-counting a row's
    contribution — this is where it is needed). *)

Lemma matrix_apply_pivot_preimage
    {m n : nat} (B : QMatrix m n) (L : list (CompletedPivot m n)) :
  (forall p, In p L -> is_unit_column_at B (completed_pivot_column p) (completed_pivot_row p)) ->
  NoDup (map completed_pivot_row L) ->
  forall y : QVec m,
    supported_on (map completed_pivot_row L) y ->
    matrix_apply B (pivot_preimage L y) = y.
Proof.
  induction L as [| p rest IH].
  - intros _ _ y Hy.
    simpl.
    rewrite matrix_apply_zero.
    apply vec_ext. intro i.
    rewrite zero_vec_nth.
    symmetry. apply Hy. intro H. destruct H.
  - intros Hunit Hnodup y Hy.
    apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as [Hp_notin Hnodup_rest].
    simpl.
    rewrite matrix_apply_add.
    rewrite matrix_apply_scale.
    rewrite (matrix_apply_standard_basis B (completed_pivot_column p)).
    unfold is_unit_column_at in Hunit.
    rewrite (Hunit p (or_introl eq_refl)).
    set (y_rest := vsub y (vscale (Vector.nth y (completed_pivot_row p)) (standard_basis (completed_pivot_row p)))).
    assert (Hy_rest_support : supported_on (map completed_pivot_row rest) y_rest).
    { unfold supported_on. intros row Hnotin.
      unfold y_rest. rewrite vsub_nth, vscale_nth.
      destruct (Fin.eq_dec row (completed_pivot_row p)) as [Heq | Hneq].
      - subst row. rewrite standard_basis_nth_eq. ring.
      - rewrite (standard_basis_nth_neq row (completed_pivot_row p) Hneq).
        assert (Hnotin_full : ~ In row (completed_pivot_row p :: map completed_pivot_row rest)).
        { intro H. destruct H as [Heq' | Hin'].
          - apply Hneq. symmetry. exact Heq'.
          - exact (Hnotin Hin'). }
        rewrite (Hy row Hnotin_full).
        ring. }
    assert (Heq_pre : pivot_preimage rest y = pivot_preimage rest y_rest).
    { apply pivot_preimage_ext. intros p' Hp'.
      unfold y_rest. rewrite vsub_nth, vscale_nth.
      assert (Hne : completed_pivot_row p' <> completed_pivot_row p).
      { intro Heq. apply Hp_notin. rewrite <- Heq. apply in_map. exact Hp'. }
      rewrite (standard_basis_nth_neq (completed_pivot_row p') (completed_pivot_row p) Hne).
      ring. }
    rewrite Heq_pre.
    rewrite (IH (fun p' Hp' => Hunit p' (or_intror Hp')) Hnodup_rest y_rest Hy_rest_support).
    apply vec_ext. intro k.
    unfold y_rest.
    rewrite vadd_nth, vsub_nth.
    ring.
Qed.

Theorem supported_in_final_image
    {m n : nat} (A : QMatrix m n) (y : QVec m) :
  supported_on (pivot_rows (elimination_trace (run_elimination A))) y ->
  linear_image (linear_map_of_matrix (elimination_matrix (run_elimination A))) y.
Proof.
  intro Hy.
  exists (pivot_preimage (completed_pivots (elimination_trace (run_elimination A))) y).
  simpl lmap.
  apply matrix_apply_pivot_preimage.
  - intros p Hp. apply run_elimination_completed_pivots. exact Hp.
  - apply run_elimination_pivot_rows_nodup.
  - exact Hy.
Qed.

(** ** 13. Final-image characterisation *)

Theorem final_image_iff_supported
    {m n : nat} (A : QMatrix m n) :
  same_set
    (linear_image (linear_map_of_matrix (elimination_matrix (run_elimination A))))
    (supported_on (pivot_rows (elimination_trace (run_elimination A)))).
Proof.
  unfold same_set. intro y.
  split.
  - apply final_image_supported.
  - apply supported_in_final_image.
Qed.

(** ** 14. The transformed-space retraction *)

Theorem final_coordinate_projection_in_image
    {m n : nat} (A : QMatrix m n) (v : QVec m) :
  linear_image
    (linear_map_of_matrix (elimination_matrix (run_elimination A)))
    (lmap (coordinate_projection (pivot_rows (elimination_trace (run_elimination A)))) v).
Proof.
  apply supported_in_final_image.
  apply coordinate_projection_output_supported.
Qed.

Theorem final_coordinate_projection_fixes_image
    {m n : nat} (A : QMatrix m n) (y : QVec m) :
  linear_image (linear_map_of_matrix (elimination_matrix (run_elimination A))) y ->
  lmap (coordinate_projection (pivot_rows (elimination_trace (run_elimination A)))) y = y.
Proof.
  intro Hy.
  apply coordinate_projection_fixes_supported.
  apply final_image_supported.
  exact Hy.
Qed.

(** ** 15. The ambient image projection: conjugate the coordinate
    projection by the certified accumulated transformation and its
    certified inverse. *)

Definition image_projection_fun
    {m n : nat} (A : QMatrix m n) (y : QVec m) : QVec m :=
  matrix_apply
    (row_operation_sequence_matrix
       (inverse_row_operation_sequence (elimination_operations (run_elimination A))))
    (lmap
       (coordinate_projection (pivot_rows (elimination_trace (run_elimination A))))
       (matrix_apply
          (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
          y)).

Lemma image_projection_fun_add
    {m n : nat} (A : QMatrix m n) (u v : QVec m) :
  image_projection_fun A (vadd u v)
  = vadd (image_projection_fun A u) (image_projection_fun A v).
Proof.
  unfold image_projection_fun.
  rewrite matrix_apply_add.
  rewrite (lmap_add (coordinate_projection (pivot_rows (elimination_trace (run_elimination A))))).
  rewrite matrix_apply_add.
  reflexivity.
Qed.

Lemma image_projection_fun_scale
    {m n : nat} (A : QMatrix m n) (a : Qc) (v : QVec m) :
  image_projection_fun A (vscale a v) = vscale a (image_projection_fun A v).
Proof.
  unfold image_projection_fun.
  rewrite matrix_apply_scale.
  rewrite (lmap_scale (coordinate_projection (pivot_rows (elimination_trace (run_elimination A))))).
  rewrite matrix_apply_scale.
  reflexivity.
Qed.

Definition image_projection
    {m n : nat} (A : QMatrix m n) : QLinearMap m m :=
  {|
    lmap := image_projection_fun A;
    lmap_add := image_projection_fun_add A;
    lmap_scale := image_projection_fun_scale A;
  |}.

Theorem image_projection_in_image
    {m n : nat} (A : QMatrix m n) (y : QVec m) :
  linear_image (linear_map_of_matrix A) (lmap (image_projection A) y).
Proof.
  unfold image_projection. simpl lmap. unfold image_projection_fun.
  destruct
    (final_coordinate_projection_in_image A
       (matrix_apply
          (row_operation_sequence_matrix (elimination_operations (run_elimination A)))
          y))
    as [x Hx].
  simpl lmap in Hx.
  exists x.
  simpl lmap.
  rewrite <- Hx.
  rewrite (run_elimination_correct A).
  rewrite matrix_compose_apply.
  rewrite <- matrix_compose_apply.
  destruct
    (row_operation_sequence_inverse_pair
       (elimination_operations (run_elimination A))
       (run_elimination_sequence_valid A))
    as [_ H2].
  rewrite H2.
  symmetry.
  apply identity_matrix_apply.
Qed.

Theorem image_projection_fixes_image
    {m n : nat} (A : QMatrix m n) (y : QVec m) :
  linear_image (linear_map_of_matrix A) y ->
  lmap (image_projection A) y = y.
Proof.
  intros [x Hx].
  unfold image_projection. simpl lmap. unfold image_projection_fun.
  assert (HPy :
    matrix_apply
      (row_operation_sequence_matrix (elimination_operations (run_elimination A))) y
    = matrix_apply (elimination_matrix (run_elimination A)) x).
  { rewrite <- Hx. simpl lmap.
    rewrite (run_elimination_correct A) at 1.
    symmetry.
    apply matrix_compose_apply. }
  rewrite HPy.
  assert (Hin : linear_image (linear_map_of_matrix (elimination_matrix (run_elimination A)))
                  (matrix_apply (elimination_matrix (run_elimination A)) x)).
  { exists x. reflexivity. }
  rewrite (final_coordinate_projection_fixes_image A
             (matrix_apply (elimination_matrix (run_elimination A)) x) Hin).
  rewrite <- HPy.
  rewrite <- matrix_compose_apply.
  destruct
    (row_operation_sequence_inverse_pair
       (elimination_operations (run_elimination A))
       (run_elimination_sequence_valid A))
    as [_ H2].
  rewrite H2.
  apply identity_matrix_apply.
Qed.

Theorem image_projection_idempotent
    {m n : nat} (A : QMatrix m n) (y : QVec m) :
  lmap (image_projection A) (lmap (image_projection A) y) = lmap (image_projection A) y.
Proof.
  apply image_projection_fixes_image.
  apply image_projection_in_image.
Qed.

Theorem image_projection_image
    {m n : nat} (A : QMatrix m n) :
  same_set (linear_image (image_projection A)) (linear_image (linear_map_of_matrix A)).
Proof.
  unfold same_set. intro v.
  split.
  - intros [y Hy]. rewrite <- Hy. apply image_projection_in_image.
  - intro Hv. exists v. apply image_projection_fixes_image. exact Hv.
Qed.

(** ** 16. Concrete probes over the Unit 16a example matrices *)

(** *** 16.1. Zero matrix: everything collapses to the zero map *)

Example probe_zero_pivot_rows_empty :
  pivot_rows (elimination_trace (run_elimination zero_mat2)) = [].
Proof. vm_compute. reflexivity. Qed.

Example probe_zero_coordinate_projection_is_zero (v : QVec 2) :
  lmap (coordinate_projection (pivot_rows (elimination_trace (run_elimination zero_mat2)))) v
  = zero_vec 2.
Proof.
  rewrite probe_zero_pivot_rows_empty.
  apply vec_ext. intro i.
  simpl lmap.
  rewrite (coordinate_projection_off_member [] v i (fun H => H)).
  symmetry. apply zero_vec_nth.
Qed.

Example probe_zero_image_projection_is_zero (y : QVec 2) :
  lmap (image_projection zero_mat2) y = zero_vec 2.
Proof.
  unfold image_projection. simpl lmap. unfold image_projection_fun.
  rewrite probe_zero_coordinate_projection_is_zero.
  apply vec_ext. intro i.
  rewrite matrix_apply_zero.
  reflexivity.
Qed.

Example probe_zero_projection_output_in_image (y : QVec 2) :
  linear_image (linear_map_of_matrix zero_mat2) (lmap (image_projection zero_mat2) y).
Proof. apply image_projection_in_image. Qed.

Example probe_zero_projection_fixes_zero :
  lmap (image_projection zero_mat2) (zero_vec 2) = zero_vec 2.
Proof.
  apply image_projection_fixes_image.
  exists (zero_vec 2). apply matrix_apply_zero.
Qed.

(** *** 16.2. Immediate pivot *)

Example probe_immediate_pivot_row_recorded :
  In Fin.F1 (pivot_rows (elimination_trace (run_elimination piv2_mat))).
Proof. vm_compute. left. reflexivity. Qed.

Example probe_immediate_pivot_fixes_image (y : QVec 2) :
  linear_image (linear_map_of_matrix piv2_mat) y ->
  lmap (image_projection piv2_mat) y = y.
Proof. apply image_projection_fixes_image. Qed.

(** *** 16.3. Search past a zero row: locked at the later row, not the
    first *)

Example probe_search_past_zero_row_recorded :
  In (Fin.FS Fin.F1) (pivot_rows (elimination_trace (run_elimination past_zero_mat))).
Proof. vm_compute. left. reflexivity. Qed.

Example probe_search_past_zero_row_not_first :
  ~ In Fin.F1 (pivot_rows (elimination_trace (run_elimination past_zero_mat))).
Proof. vm_compute. intros [H | []]. discriminate H. Qed.

(** *** 16.4. Singular matrix *)

Example probe_singular_one_pivot_row :
  pivot_rows (elimination_trace (run_elimination sing_mat)) = [Fin.F1].
Proof. vm_compute. reflexivity. Qed.

Example probe_singular_skipped_column_supported :
  supported_on
    (pivot_rows (elimination_trace (run_elimination sing_mat)))
    (Vector.nth (elimination_matrix (run_elimination sing_mat)) (Fin.FS Fin.F1)).
Proof. apply run_elimination_column_supported. Qed.

Example probe_singular_idempotent (y : QVec 2) :
  lmap (image_projection sing_mat) (lmap (image_projection sing_mat) y)
  = lmap (image_projection sing_mat) y.
Proof. apply image_projection_idempotent. Qed.

(** *** 16.5. Wide matrix *)

Example probe_wide_all_columns_supported (col : Fin.t 3) :
  supported_on
    (pivot_rows (elimination_trace (run_elimination wide_mat)))
    (Vector.nth (elimination_matrix (run_elimination wide_mat)) col).
Proof. apply run_elimination_column_supported. Qed.

Example probe_wide_third_column_in_image :
  linear_image
    (linear_map_of_matrix (elimination_matrix (run_elimination wide_mat)))
    (Vector.nth (elimination_matrix (run_elimination wide_mat)) (Fin.FS (Fin.FS Fin.F1))).
Proof.
  exists (standard_basis (Fin.FS (Fin.FS Fin.F1))).
  simpl lmap.
  apply matrix_apply_standard_basis.
Qed.

Example probe_wide_projection_fixes_image (y : QVec 2) :
  linear_image (linear_map_of_matrix wide_mat) y ->
  lmap (image_projection wide_mat) y = y.
Proof. apply image_projection_fixes_image. Qed.

(** *** 16.6. Tall matrix *)

Example probe_tall_unused_row_removed (v : QVec 3) :
  Vector.nth
    (lmap (coordinate_projection (pivot_rows (elimination_trace (run_elimination tall_mat)))) v)
    (Fin.FS (Fin.FS Fin.F1))
  = 0.
Proof.
  simpl lmap.
  apply coordinate_projection_off_member.
  vm_compute. intros [H | [H | []]]; discriminate H.
Qed.

Example probe_tall_projection_fixes_image (y : QVec 3) :
  linear_image (linear_map_of_matrix tall_mat) y ->
  lmap (image_projection tall_mat) y = y.
Proof. apply image_projection_fixes_image. Qed.

(** *** 16.7. Zero-dimensional boundaries *)

Example probe_dim_0_0_projection_in_image (y : QVec 0) :
  linear_image (linear_map_of_matrix mat_0_0) (lmap (image_projection mat_0_0) y).
Proof. apply image_projection_in_image. Qed.

Example probe_dim_0_1_projection_in_image (y : QVec 0) :
  linear_image (linear_map_of_matrix mat_0_1) (lmap (image_projection mat_0_1) y).
Proof. apply image_projection_in_image. Qed.

Example probe_dim_2_0_pivot_rows_empty :
  pivot_rows (elimination_trace (run_elimination mat_2_0)) = [].
Proof. vm_compute. reflexivity. Qed.

Example probe_dim_2_0_projection_is_zero (y : QVec 2) :
  lmap (image_projection mat_2_0) y = zero_vec 2.
Proof.
  destruct (image_projection_in_image mat_2_0 y) as [u Hu].
  rewrite <- Hu.
  clear Hu.
  assert (Hu0 : u = Vector.nil Qc).
  { revert u. apply Vector.case0. reflexivity. }
  rewrite Hu0.
  simpl lmap.
  unfold matrix_apply, mat_2_0.
  reflexivity.
Qed.

(** *** 16.8. Nontrivial conjugation: [piv2_mat]'s accumulated matrix
    is not the identity (its pivot coefficient is [1+1], forcing a
    genuine [Qcinv (1+1)] scaling), so [image_projection] here is a
    true conjugation, not merely the raw coordinate mask. *)

Example probe_nontrivial_conjugation :
  row_operation_sequence_matrix (elimination_operations (run_elimination piv2_mat))
  <> identity_matrix 2.
Proof.
  intro Heq.
  assert (Hentry :
    matrix_entry
      (row_operation_sequence_matrix (elimination_operations (run_elimination piv2_mat)))
      Fin.F1 Fin.F1
    = matrix_entry (identity_matrix 2) Fin.F1 Fin.F1).
  { rewrite Heq. reflexivity. }
  vm_compute in Hentry.
  discriminate Hentry.
Qed.
