# PCE Instantiation

`proof-carrying-exactness` takes $(D, r, L)$ as an already constructed
rational instance. Its certificate witnesses correspond exactly to the
core mathematical witnesses of this theory:

| PCE witness | Mathematical role |
|---|---|
| repair $u$ | lift of $r$ through $D$ |
| separator $y$ | witness that $[r] \neq 0$ |
| gauge direction $k$ | witness that $L\vert_{\ker D} \neq 0$ |
| factorisation matrix $M$ | extension of the descended claim |
| claimed value $x$ | canonical value $Lu = Mr$ |

See [`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md) for the definitions
these correspond to, and R3–R5 in [`THEOREM_LADDER.md`](THEOREM_LADDER.md)
for the underlying theorems.

## What PCE adds beyond the mathematics

PCE adds serialisation, digests, closed schemas, resource limits,
untrusted generation, independent checking, and evidence policies. These
are assurance mechanisms built around the mathematics — they are not the
mathematics itself, and they do not belong in this repository (see
[`NON_CLAIMS.md`](NON_CLAIMS.md)).

## `INADMISSIBLE`

PCE's `INADMISSIBLE` verdict corresponds to the admissibility gate
described in [`NON_CLAIMS.md`](NON_CLAIMS.md#where-inadmissible-belongs):
a property of how $e \to (U, V, W, D, r, L)$ was constructed, checked
before the linear theory's three-way classification ever applies.

## Dependency direction

The intended mathematical dependency direction is from this repository
to PCE: this repository is intended to develop and formally verify the
mathematics that PCE's witness forms turn into independently checkable
certificates. There is no dependency from this repository back onto
PCE's codebase, and formal instantiation theorems connecting the two are
scheduled for Phase 6 (see
[`FUTURE_GENERALISATIONS.md`](FUTURE_GENERALISATIONS.md#development-phases)) —
see also [`FOUNDATION.md`](FOUNDATION.md#why-a-third-repository-and-why-it-is-not-a-merger)
and the diagram in the top-level [`README.md`](../README.md#relation-to-roc-and-pce).
