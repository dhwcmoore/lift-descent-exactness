# ROC Instantiation

`regional-obstruction-calculus` instantiates the **lifting half** of the
theory developed in this repository.

## The construction

For a finite regional presentation, take

$$U = C^0, \qquad V = C^1, \qquad D = \delta^0,$$

and let $r \in C^1$ be the regional discrepancy. Then

$$[r] \in C^1 / \mathrm{im}\,\delta^0$$

is exactly the ROC obstruction class (see
[`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md#2-the-first-obstruction-does-the-residue-lift)).
A cycle separator is a dual witness detecting that class, matching R4 in
[`THEOREM_LADDER.md`](THEOREM_LADDER.md).

ROC supplies:

- a method for constructing $D$;
- a regional meaning for $r$;
- cochain and quotient structure;
- refinement maps;
- transport conditions;
- presentation invariance results.

## Extending to the descent half

Once a claim map $L : C^0 \to W$ is added, the same regional presentation
also instantiates the descent half of the theory (Sections 3–4 of
[`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md)), which ROC alone does
not need but this repository's theory accommodates without modification.

## Dependency direction

The mathematical dependency direction is from this repository to ROC:
this repository develops and formally verifies the mathematics that
ROC's regional and cochain instances instantiate. There is no dependency
from this repository back onto ROC's codebase.

The formal instantiation theorems connecting the two are complete, in
[`rocq/QCochainInstantiation.v`](../rocq/QCochainInstantiation.v) — see
also [`FOUNDATION.md`](FOUNDATION.md#why-a-third-repository-and-why-it-is-not-a-merger)
and the diagram in the top-level [`README.md`](../README.md#relationship-to-roc-and-pce).
This does not verify ROC's production implementation; see
[`NON_CLAIMS.md`](NON_CLAIMS.md).
