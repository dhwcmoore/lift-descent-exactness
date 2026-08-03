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
formalised in [`rocq/QAdmissibilityGate.v`](../rocq/QAdmissibilityGate.v)
(see [`NON_CLAIMS.md`](NON_CLAIMS.md#where-inadmissible-belongs)):
a property of how $e \to (U, V, W, D, r, L)$ was constructed, checked
before the linear theory's three-way classification ever applies. The
composed result, proved in
[`rocq/QPCEInstantiation.v`](../rocq/QPCEInstantiation.v), is the nested
outcome `GatedInadmissible` or `GatedAdmissible` of one of Obstructed,
Underdetermined, Exact — never a flat four-constructor verdict.

## Dependency direction

The mathematical dependency direction is from this repository to PCE:
this repository develops and formally verifies the mathematics that
PCE's witness forms turn into independently checkable certificates.
There is no dependency from this repository back onto PCE's codebase.

The formal instantiation theorems connecting the two are complete, in
[`rocq/QPCEWitnessPredicates.v`](../rocq/QPCEWitnessPredicates.v) and
[`rocq/QPCEInstantiation.v`](../rocq/QPCEInstantiation.v) — see also
[`FOUNDATION.md`](FOUNDATION.md#why-a-third-repository-and-why-it-is-not-a-merger)
and the diagram in the top-level [`README.md`](../README.md#relationship-to-roc-and-pce).
This does not verify PCE's production implementation; see
[`NON_CLAIMS.md`](NON_CLAIMS.md).
