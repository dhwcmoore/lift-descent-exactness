(** * Certified finite sequences of elementary row operations

    Unit 13 gave individual elementary row transformations
    ([swap_entries], [scale_entry], [add_scaled_entry]), their matrix
    realisations, and their explicit two-sided matrix inverses. This
    unit packages elementary operations as finite data ([RowOperation]),
    executes finite lists of them, accumulates one matrix per sequence,
    and proves that the accumulated forward and inverse matrices form a
    two-sided [matrix_inverse_pair] — hence that valid sequences
    preserve and reflect linear systems ([Ax = b]).

    Execution is head-first: for [ops = [op1; op2]], [run_row_operations
    ops x] applies [op1] first, then [op2]. The accumulated matrix must
    agree with this: [row_operation_sequence_matrix [op1; op2]] is
    [matrix_compose (row_operation_matrix op2) (row_operation_matrix
    op1)], i.e. "apply op1's matrix, then op2's matrix" under
    [matrix_compose]'s "apply the second argument, then the first"
    convention (Unit 12). The inverse sequence reverses operation order
    and inverts each operation, matching how two-sided inverses compose.

    This unit does not search for pivots, build echelon forms, or
    perform elimination — it only certifies that *any* valid finite
    sequence of elementary operations is an invertible linear
    transformation that preserves solution sets. *)

From Coq Require Import List.
From Coq Require Import QArith.
From Coq Require Import Qcanon.
From LiftDescent Require Import QVector.
From LiftDescent Require Import QLinearMap.
From LiftDescent Require Import QFiniteCoordinates.
From LiftDescent Require Import QMatrixAlgebra.
From LiftDescent Require Import QElementaryRows.

Import ListNotations.

Open Scope Qc_scope.

(** ** 1. Row operations as finite data *)

Inductive RowOperation (n : nat) : Type :=
| RowSwap :
    Fin.t n ->
    Fin.t n ->
    RowOperation n
| RowScale :
    Fin.t n ->
    Qc ->
    RowOperation n
| RowAdd :
    Fin.t n ->
    Fin.t n ->
    Qc ->
    RowOperation n.

Arguments RowSwap {n} i j.
Arguments RowScale {n} i a.
Arguments RowAdd {n} target source a.

(** ** 2. Validity, kept as a separate proposition, not baked into the
    constructor *)

Definition row_operation_valid
    {n : nat}
    (op : RowOperation n)
    : Prop :=
  match op with
  | RowSwap _ _ =>
      True
  | RowScale _ a =>
      a <> 0
  | RowAdd target source _ =>
      target <> source
  end.

(** ** 3. Executing a single operation *)

Definition apply_row_operation
    {n : nat}
    (op : RowOperation n)
    (x : QVec n)
    : QVec n :=
  match op with
  | RowSwap i j =>
      swap_entries i j x
  | RowScale i a =>
      scale_entry i a x
  | RowAdd target source a =>
      add_scaled_entry target source a x
  end.

(** ** 4. The matrix of a single operation *)

Definition row_operation_matrix
    {n : nat}
    (op : RowOperation n)
    : QMatrix n n :=
  match op with
  | RowSwap i j =>
      row_swap_matrix i j
  | RowScale i a =>
      row_scale_matrix i a
  | RowAdd target source a =>
      row_add_matrix target source a
  end.

(** ** 5. The inverse of a single operation *)

Definition inverse_row_operation
    {n : nat}
    (op : RowOperation n)
    : RowOperation n :=
  match op with
  | RowSwap i j =>
      RowSwap i j
  | RowScale i a =>
      RowScale i (Qcinv a)
  | RowAdd target source a =>
      RowAdd target source (-a)
  end.

(** ** 6. Sequence validity, as an ordinary [Forall] *)

Definition row_operation_sequence_valid
    {n : nat}
    (ops : list (RowOperation n))
    : Prop :=
  Forall row_operation_valid ops.

(** ** 7. Head-first sequence execution: for [[op1; op2]], [op1] runs
    first, then [op2]. *)

Fixpoint run_row_operations
    {n : nat}
    (ops : list (RowOperation n))
    (x : QVec n)
    : QVec n :=
  match ops with
  | [] =>
      x
  | op :: rest =>
      run_row_operations
        rest
        (apply_row_operation op x)
  end.

(** ** 8. The accumulated sequence matrix, oriented to match head-first
    execution: [row_operation_matrix op] is applied first (innermost),
    [row_operation_sequence_matrix rest] afterwards (outermost). For
    [[op1; op2]] the accumulated matrix therefore represents
    [E_op2 * E_op1]. *)

Fixpoint row_operation_sequence_matrix
    {n : nat}
    (ops : list (RowOperation n))
    : QMatrix n n :=
  match ops with
  | [] =>
      identity_matrix n
  | op :: rest =>
      matrix_compose
        (row_operation_sequence_matrix rest)
        (row_operation_matrix op)
  end.

(** ** 9. The inverse sequence: invert each operation, then reverse
    order, since two-sided inverses of a composite compose in reverse. *)

Definition inverse_row_operation_sequence
    {n : nat}
    (ops : list (RowOperation n))
    : list (RowOperation n) :=
  map inverse_row_operation (rev ops).

(** ** 10. A single operation's matrix acts exactly as the operation
    itself. *)

Theorem row_operation_matrix_apply
    {n : nat}
    (op : RowOperation n)
    (x : QVec n) :
  matrix_apply
    (row_operation_matrix op)
    x
  =
  apply_row_operation op x.
Proof.
  destruct op as [i j | i a | target source a].
  - apply row_swap_matrix_apply.
  - apply row_scale_matrix_apply.
  - apply row_add_matrix_apply.
Qed.

(** ** 11. The inverse of a valid operation is valid. *)

Theorem inverse_row_operation_valid
    {n : nat}
    (op : RowOperation n) :
  row_operation_valid op ->
  row_operation_valid
    (inverse_row_operation op).
Proof.
  destruct op as [i j | i a | target source a]; simpl.
  - intros _. exact I.
  - intros Ha Hzero.
    apply Ha.
    pose proof (Qcmult_inv_r a Ha) as Hinv.
    rewrite Hzero in Hinv.
    rewrite Qcmult_0_r in Hinv.
    discriminate Hinv.
  - intro H. exact H.
Qed.

(** ** 12. A single valid operation's matrix and its inverse's matrix
    form a two-sided inverse pair — reusing Unit 13's theorems directly. *)

Theorem row_operation_inverse_pair
    {n : nat}
    (op : RowOperation n) :
  row_operation_valid op ->
  matrix_inverse_pair
    (row_operation_matrix op)
    (row_operation_matrix
       (inverse_row_operation op)).
Proof.
  destruct op as [i j | i a | target source a]; simpl.
  - intros _. apply row_swap_matrix_inverse.
  - intro Ha. apply row_scale_matrix_inverse. exact Ha.
  - intro Hd. apply row_add_matrix_inverse. exact Hd.
Qed.

(** ** 13. Associativity of matrix composition, from [matrix_apply]
    composing associatively. *)

Theorem matrix_compose_assoc
    {q p m n : nat}
    (A : QMatrix q p)
    (B : QMatrix p m)
    (C : QMatrix m n) :
  matrix_compose A
    (matrix_compose B C)
  =
  matrix_compose
    (matrix_compose A B)
    C.
Proof.
  apply matrix_eq_of_apply_eq.
  intros x.
  rewrite !matrix_compose_apply.
  reflexivity.
Qed.

(** ** 14. The identity matrix is its own inverse pair. *)

Theorem matrix_inverse_pair_identity
    (n : nat) :
  matrix_inverse_pair
    (identity_matrix n)
    (identity_matrix n).
Proof.
  split; apply matrix_compose_identity_left.
Qed.

(** ** 15. Inverse pairs compose, in the orientation forced by
    "apply [A] first, then [B]" composing to [B ∘ A], whose inverse is
    "apply [Binv] first, then [Ainv]", i.e. [Ainv ∘ Binv]. *)

Theorem matrix_inverse_pair_compose
    {n : nat}
    (A Ainv B Binv : QMatrix n n) :
  matrix_inverse_pair A Ainv ->
  matrix_inverse_pair B Binv ->
  matrix_inverse_pair
    (matrix_compose B A)
    (matrix_compose Ainv Binv).
Proof.
  intros [HA1 HA2] [HB1 HB2].
  split.
  - rewrite <- (matrix_compose_assoc B A (matrix_compose Ainv Binv)).
    rewrite (matrix_compose_assoc A Ainv Binv).
    rewrite HA1.
    rewrite matrix_compose_identity_left.
    exact HB1.
  - rewrite <- (matrix_compose_assoc Ainv Binv (matrix_compose B A)).
    rewrite (matrix_compose_assoc Binv B A).
    rewrite HB2.
    rewrite matrix_compose_identity_left.
    exact HA2.
Qed.

(** ** 16. A one-operation sequence's matrix is exactly that operation's
    matrix — needed to unfold [inverse_row_operation_sequence] on a
    cons via the append law below. *)

Lemma row_operation_sequence_matrix_singleton
    {n : nat}
    (op : RowOperation n) :
  row_operation_sequence_matrix [op] = row_operation_matrix op.
Proof.
  simpl.
  apply matrix_compose_identity_left.
Qed.

(** ** 17. The sequence-matrix append law, matching "[ops1] first, then
    [ops2]". *)

Theorem row_operation_sequence_matrix_append
    {n : nat}
    (ops1 ops2 : list (RowOperation n)) :
  row_operation_sequence_matrix
    (ops1 ++ ops2)
  =
  matrix_compose
    (row_operation_sequence_matrix ops2)
    (row_operation_sequence_matrix ops1).
Proof.
  induction ops1 as [| op1 rest1 IH].
  - simpl.
    symmetry.
    apply matrix_compose_identity_right.
  - simpl.
    rewrite IH.
    symmetry.
    apply matrix_compose_assoc.
Qed.

(** ** 18. Execution equals accumulated-matrix application. *)

Theorem run_row_operations_matrix
    {n : nat}
    (ops : list (RowOperation n))
    (x : QVec n) :
  run_row_operations ops x =
  matrix_apply
    (row_operation_sequence_matrix ops)
    x.
Proof.
  induction ops as [| op rest IH] in x |- *.
  - simpl.
    symmetry.
    apply identity_matrix_apply.
  - simpl.
    rewrite IH.
    rewrite matrix_compose_apply.
    rewrite row_operation_matrix_apply.
    reflexivity.
Qed.

(** ** 19. Left action on an arbitrary matrix: the accumulated sequence
    matrix applies the whole sequence to every column. Not a "column
    operation" — the representation stores columns, but each column's
    coordinates are transformed row-wise, exactly as in Unit 13. *)

Theorem row_operation_sequence_left_action
    {n m : nat}
    (ops : list (RowOperation n))
    (A : QMatrix n m) :
  matrix_compose
    (row_operation_sequence_matrix ops)
    A
  =
  Vector.map
    (run_row_operations ops)
    A.
Proof.
  unfold matrix_compose.
  apply (Vector.map_ext _ _
           (matrix_apply (row_operation_sequence_matrix ops))
           (run_row_operations ops)
           (fun x => eq_sym (run_row_operations_matrix ops x))).
Qed.

(** ** 20. The inverse sequence of a valid sequence is valid. *)

Theorem inverse_row_operation_sequence_valid
    {n : nat}
    (ops : list (RowOperation n)) :
  row_operation_sequence_valid ops ->
  row_operation_sequence_valid
    (inverse_row_operation_sequence ops).
Proof.
  unfold row_operation_sequence_valid, inverse_row_operation_sequence.
  intro H.
  apply Forall_map.
  apply Forall_rev.
  eapply Forall_impl.
  - apply inverse_row_operation_valid.
  - exact H.
Qed.

(** ** 21. A valid sequence's accumulated matrix and its inverse
    sequence's accumulated matrix form a two-sided inverse pair. *)

Theorem row_operation_sequence_inverse_pair
    {n : nat}
    (ops : list (RowOperation n)) :
  row_operation_sequence_valid ops ->
  matrix_inverse_pair
    (row_operation_sequence_matrix ops)
    (row_operation_sequence_matrix
       (inverse_row_operation_sequence ops)).
Proof.
  induction ops as [| op rest IH].
  - intros _.
    apply matrix_inverse_pair_identity.
  - intro H.
    apply Forall_cons_iff in H.
    destruct H as [Hop Hrest].
    assert (Heq :
      inverse_row_operation_sequence (op :: rest)
      = inverse_row_operation_sequence rest ++ [inverse_row_operation op]).
    { unfold inverse_row_operation_sequence.
      simpl.
      rewrite map_app.
      reflexivity. }
    rewrite Heq.
    rewrite row_operation_sequence_matrix_append.
    rewrite row_operation_sequence_matrix_singleton.
    simpl row_operation_sequence_matrix at 1.
    apply matrix_inverse_pair_compose.
    + apply row_operation_inverse_pair. exact Hop.
    + apply IH. exact Hrest.
Qed.

(** ** 22. Generic equation preservation and reflection under any
    explicit matrix inverse pair. *)

Theorem matrix_inverse_pair_equation_iff
    {n m : nat}
    (E Einv : QMatrix n n)
    (A : QMatrix n m)
    (b : QVec n)
    (x : QVec m) :
  matrix_inverse_pair E Einv ->
  (matrix_apply A x = b <->
   matrix_apply
     (matrix_compose E A)
     x
   =
   matrix_apply E b).
Proof.
  intros [HE1 HE2].
  split.
  - intro Heq.
    rewrite matrix_compose_apply.
    f_equal.
    exact Heq.
  - intro Heq.
    assert (Heq' : matrix_apply Einv (matrix_apply (matrix_compose E A) x)
                   = matrix_apply Einv (matrix_apply E b)).
    { f_equal. exact Heq. }
    rewrite (matrix_compose_apply E A x) in Heq'.
    rewrite <- (matrix_compose_apply Einv E (matrix_apply A x)) in Heq'.
    rewrite <- (matrix_compose_apply Einv E b) in Heq'.
    rewrite HE2 in Heq'.
    rewrite (identity_matrix_apply (matrix_apply A x)) in Heq'.
    rewrite (identity_matrix_apply b) in Heq'.
    exact Heq'.
Qed.

(** ** 23. Sequence-level equation preservation and reflection: a direct
    application of the sequence inverse pair to the generic equation
    theorem, for every valid operation sequence. *)

Theorem row_operation_sequence_equation_iff
    {n m : nat}
    (ops : list (RowOperation n))
    (A : QMatrix n m)
    (b : QVec n)
    (x : QVec m) :
  row_operation_sequence_valid ops ->
  (matrix_apply A x = b <->
   matrix_apply
     (matrix_compose
        (row_operation_sequence_matrix ops)
        A)
     x
   =
   matrix_apply
     (row_operation_sequence_matrix ops)
     b).
Proof.
  intro Hvalid.
  eapply matrix_inverse_pair_equation_iff.
  apply row_operation_sequence_inverse_pair.
  exact Hvalid.
Qed.
