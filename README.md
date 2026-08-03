# Lift-Descent Exactness

A constructive Rocq development of two independent obstruction questions for a finite rational linear presentation:

1. **Can a presented residue be lifted?**
2. **Does a declared claim descend through the presentation?**

The repository isolates the common mathematics underlying [`regional-obstruction-calculus`](https://github.com/dhwcmoore/regional-obstruction-calculus) and [`proof-carrying-exactness`](https://github.com/dhwcmoore/proof-carrying-exactness), while remaining independent of both codebases.

It formalises repair fibres, lifting and descent obstructions, constructive witnesses, exactness profiles, canonical values, universal exact quotients, presentation transport, and the mathematical ROC and PCE instantiations.

## Status

**Phases 1-6 are formally complete.**

The Rocq development currently contains 41 source files and proves:

* repair-fibre and claim-fibre normal forms;
* constructive descent factorisation;
* sound and complete obstruction witnesses;
* the operational three-way verdict classification;
* the four-sector exactness profile;
* canonical exact-value existence and uniqueness;
* the universal exact quotient;
* invariance under invertible presentation changes;
* separate preservation and reflection conditions for noninvertible transformations;
* ROC as the cochain and lifting-only instantiation;
* PCE's exact, underdetermined, and obstructed witness predicates;
* an abstract admissibility gate composed with the three-way linear classification.

The project is checked with compilation, `coqchk`, an admitted-proof scan, a project-axiom scan, and a declaration inventory.

## The mathematical instance

The starting point is a finite-dimensional rational linear instance

[
\mathcal I=(U,V,W,D,r,L),
]

where

[
D:U\to V,
\qquad
r\in V,
\qquad
L:U\to W.
]

Interpretively:

* (U) is a space of possible repairs, states, explanations, or reconstructions;
* (V) is a space of presented constraints or residues;
* (D) records how a candidate state meets those constraints;
* (r) is the residue that must be realised;
* (L) is a declared claim or output computed from a candidate state.

The theory does not require these interpretations. Its theorems concern the exact algebraic presentation itself.

## Two independent obstruction axes

### 1. Lifting

A repair is a vector (u\in U) satisfying

[
Du=r.
]

The repair fibre is

[
F_r={u\in U\mid Du=r}.
]

The lifting question is whether (F_r) is inhabited, equivalently whether

[
r\in\operatorname{im}D.
]

When no repair exists, the residue has a nonzero obstruction class in

[
\operatorname{coker}D.
]

Constructively, obstruction is witnessed by a linear functional

[
y:V\to\mathbb Q
]

such that

[
yD=0,
\qquad
y(r)\neq0.
]

### 2. Descent

Even when repairs exist, different repairs can yield different claim values.

The claim descends precisely when it is constant on every repair fibre. This is equivalent to

[
L(\ker D)=0,
]

or, equivalently,

[
\ker D\subseteq\ker L.
]

In finite-dimensional rational vector spaces, this is also equivalent to the existence of a factor map

[
M:V\to W
]

such that

[
L=M\circ D.
]

Failure of descent is witnessed by a gauge direction (k\in U) satisfying

[
Dk=0,
\qquad
Lk\neq0.
]

For any repair (u_0), both (u_0) and (u_0+k) realise the same residue, but

[
L(u_0+k)\neq L(u_0).
]

The lifting and descent questions are logically independent.

## The exactness profile

The complete mathematical profile has four sectors.

| Profile                           |          Lifting |                    Descent |
| ---------------------------------- | ----------------: | --------------------------: |
| **Realisable Exact**              |    repair exists |             claim descends |
| **Realisable Underdetermined**    |    repair exists |     claim does not descend |
| **Obstructed but Descending**     | no repair exists |    claim map would descend |
| **Obstructed and Non-Descending** | no repair exists | claim map does not descend |

The profile retains information about both obstruction axes even when the lifting obstruction is already nonzero.

## The operational verdict

For operational use, the four-sector profile collapses to three verdicts.

| Verdict             | Mathematical condition                                 |
| -------------------- | -------------------------------------------------------- |
| **Obstructed**      | no (u) satisfies (Du=r)                                |
| **Underdetermined** | a repair exists, but (L) varies across repairs         |
| **Exact**           | a repair exists and (L) is constant across all repairs |

The two lifting-obstructed profile sectors both produce the operational verdict **Obstructed**.

The Rocq development proves constructively that exactly one of these three operational verdicts holds for every finite rational instance.

## Canonical exact value

In the exact sector, choose any repair (u_0) and any factor map (M) satisfying

[
Du_0=r,
\qquad
L=M\circ D.
]

Then

[
L(u_0)=M(r).
]

Although neither the repair nor the factor map need be unique, their resulting value is unique.

There exists exactly one (x\in W) such that

[
Lu=x
]

for every repair (u\in F_r). Every repair and every valid factor map calculate that same value:

[
x=Lu=M(r).
]

This is the repository's central exact-value result: a canonical value constituted by nonunique witnesses.

## Universal exact quotient

When descent fails, the ambiguity is not merely a Boolean defect.

Let

[
A_{D,L}=L(\ker D)\subseteq W.
]

The quotient claim

[
\pi L:U\to W/A_{D,L}
]

is exact with respect to (D): every gauge-dependent change in the original claim is removed.

The development proves the corresponding universal property. Any quotient of (W) through which the claim becomes exact factors uniquely through

[
W/A_{D,L}.
]

Thus underdetermination has a canonical exact remainder rather than only a negative verdict.

## Presentation morphisms

The repository distinguishes invertible transport from noninvertible transformation.

### Invertible changes

Linear isomorphisms of the state, residue, and claim coordinates transport:

* lifting witnesses;
* descent witnesses;
* obstruction witnesses;
* gauge witnesses;
* exactness profiles;
* operational verdicts.

The relevant obstruction spaces before and after transport are isomorphic, not literally identical.

### Noninvertible changes

For noninvertible presentation transformations, preservation and reflection are separate properties.

The development proves explicit conditions for:

* preservation of realisability;
* reflection of realisability;
* preservation of claim descent;
* reflection of claim descent;
* preservation and reflection of verdict information.

No general preservation theorem is asserted without its required hypotheses.

## ROC instantiation

[`regional-obstruction-calculus`](https://github.com/dhwcmoore/regional-obstruction-calculus) instantiates the lifting half of the theory.

For a finite cochain presentation, take

[
U=C^0,
\qquad
V=C^1,
\qquad
D=\delta^0,
]

with regional discrepancy (r\in C^1).

Then a ROC repair is exactly a solution of

[
\delta^0 b=r,
]

and a translated ROC cycle separator is exactly a lifting-obstruction witness.

The formal instantiation uses a zero-dimensional claim space

[
W=0.
]

Descent is consequently automatic, and only two operational outcomes remain:

* **Exact**, meaning that a cochain repair exists;
* **Obstructed**, meaning that a separator proves no repair exists.

In this embedding, **Exact** asserts repairability plus a vacuous zero-dimensional claim. It does not assert a substantive application-level value.

The core repository does not import the ROC codebase or verify ROC's production implementation.

## PCE instantiation

[`proof-carrying-exactness`](https://github.com/dhwcmoore/proof-carrying-exactness) uses witness forms corresponding to the core mathematical witnesses.

### Exact witness

[
Du=r,
\qquad
L=M\circ D,
\qquad
M(r)=x.
]

The development derives

[
L(u)=x
]

and proves that (x) is the unique exact value.

### Underdetermined witness

[
Du=r,
\qquad
Dk=0,
\qquad
Lk\neq0.
]

The development derives a second repair (u+k) with a different claim value.

### Obstructed witness

[
yD=0,
\qquad
y(r)\neq0.
]

This is exactly the separator witness for failure of lifting.

## Admissibility is a gate, not a fourth linear verdict

PCE also has an `INADMISSIBLE` outcome. This repository keeps it structurally separate from the linear verdicts.

The architecture is:

[
e
\xrightarrow{\text{admissibility gate}}
\begin{cases}
\text{inadmissible},\
\text{admissible with a linear instance}.
\end{cases}
]

Only an admissible evidence package proceeds to the linear classification:

[
\text{Obstructed},
\quad
\text{Underdetermined},
\quad
\text{Exact}.
]

The formal gated result therefore has the nested form

```text
GatedInadmissible
or
GatedAdmissible VerdictObstructed
or
GatedAdmissible VerdictUnderdetermined
or
GatedAdmissible VerdictExact
```

This is deliberately not a flat four-constructor linear verdict.

The admissibility gate is abstract. The core development proves sound composition with positive and negative gate witnesses, but does not define a domain-specific admissibility policy.

## What is proved

The formal development establishes, over finite rational coordinate spaces:

* repair-fibre and claim-fibre structure;
* the lifting obstruction;
* intrinsic and ambient claim descent;
* constructive image preimages and factorisation;
* separator-witness soundness and completeness;
* gauge-witness soundness and completeness;
* verdict exclusivity and completeness;
* four-sector profile completeness;
* canonical exact-value existence and uniqueness;
* universal exact quotient;
* isomorphic transport;
* noninvertible preservation and reflection;
* the cochain lifting instantiation;
* the abstract admissibility gate;
* PCE witness-predicate correspondence;
* the complete gated PCE witness classification.

## What is not proved

The repository does **not** prove that a physical, geometric, evidential, or computational process has been represented correctly by

[
(U,V,W,D,r,L).
]

It takes the algebraic presentation as its starting point.

In particular, it does not formalise or verify:

* sensors or tracking systems;
* regional geometry;
* PDE discretisations;
* application-specific evidence semantics;
* production parsers or serialisers;
* JSON certificate formats;
* cryptographic digests;
* provenance policies;
* command-line tools;
* Python verifier implementations;
* generator implementations;
* commercial or deployment claims.

Those belong to domain adapters and applied repositories.

This boundary is essential: exact algebraic reasoning does not by itself certify that the algebraic presentation is relevant to, or faithful to, the concrete process being modelled.

See [`docs/NON_CLAIMS.md`](docs/NON_CLAIMS.md).

## Formal development

The Rocq source is organised by mathematical dependency.

```text
rocq/
├── QVector.v
├── QLinearMap.v
├── QSubspace.v
├── LinearInstance.v
├── QSubspaceMap.v
├── QExactSequence.v
├── QObstruction.v
├── QDescentBasics.v
├── QIntrinsicDescent.v
├── QFiniteCoordinates.v
├── QMatrixAlgebra.v
├── QElementaryRows.v
├── QRowOperationSequence.v
├── QPivotStep.v
├── QEliminationStructure.v
├── QEliminationCorrectness.v
├── QImageProjection.v
├── QImageExtension.v
├── QImagePreimage.v
├── QDescentFactorisation.v
├── QLinearFunctional.v
├── QSeparatorWitness.v
├── QKernelProjection.v
├── QKernelSpanning.v
├── QGaugeWitness.v
├── QVerdictClassification.v
├── QExactnessProfile.v
├── QUniversalExactQuotient.v
├── QCanonicalValue.v
├── QLinearIsomorphism.v
├── QPresentationMorphism.v
├── QLiftObstructionTransport.v
├── QDescentObstructionTransport.v
├── QIsomorphicTransport.v
├── QPresentationPreservation.v
├── QPresentationReflection.v
├── QPresentationSafety.v
├── QCochainInstantiation.v
├── QAdmissibilityGate.v
├── QPCEWitnessPredicates.v
└── QPCEInstantiation.v
```

The development uses canonical rationals and ordinary Leibniz equality. It does not add project axioms or admitted theorems.

## Building and checking

The project requires a Rocq/Coq installation providing:

```text
coq_makefile
coqc
coqchk
```

Run the complete verification pipeline with:

```bash
make check
```

This performs:

1. an `Admitted` scan;
2. a project-defined `Axiom`, `Parameter`, and `Conjecture` scan;
3. compilation of the complete Rocq development;
4. `coqchk` validation;
5. declaration-inventory checking.

To build only:

```bash
make
```

To remove generated build files:

```bash
make clean
```

## Documentation

The founding documents explain the mathematical and architectural programme:

* [`docs/FOUNDATION.md`](docs/FOUNDATION.md) - charter and basic commitments;
* [`docs/MATHEMATICAL_SCOPE.md`](docs/MATHEMATICAL_SCOPE.md) - full mathematical object and obstruction structure;
* [`docs/NON_CLAIMS.md`](docs/NON_CLAIMS.md) - representation and implementation boundaries;
* [`docs/THEOREM_LADDER.md`](docs/THEOREM_LADDER.md) - central theorem sequence;
* [`docs/PRESENTATION_MORPHISMS.md`](docs/PRESENTATION_MORPHISMS.md) - invertible and noninvertible transformations;
* [`docs/ROC_INSTANTIATION.md`](docs/ROC_INSTANTIATION.md) - ROC's lifting interpretation;
* [`docs/PCE_INSTANTIATION.md`](docs/PCE_INSTANTIATION.md) - PCE witness interpretation;
* [`docs/FUTURE_GENERALISATIONS.md`](docs/FUTURE_GENERALISATIONS.md) - wider abstraction beyond finite rational vector spaces.

The Rocq files are the formal mathematical source of truth.

## Relationship to ROC and PCE

```text
                    lift-descent-exactness
                       /             \
                      /               \
 regional-obstruction-calculus   proof-carrying-exactness
```

The dependency direction is conceptual and one-way:

* this repository proves the common linear mathematics;
* ROC supplies regional and cochain constructions;
* PCE supplies certificate formats, independent verification, and application-facing assurance machinery.

This repository does not inherit either applied codebase and has no circular dependency on them.

## Future direction

The next mathematical question is which parts of the finite rational development survive in wider settings, including:

* modules over a ring;
* abelian categories;
* exact categories;
* regular categories;
* indexed or fibred settings.

Generalisation should preserve the distinction between:

* intrinsic descent through (\operatorname{im}D);
* ambient extension to all of (V).

The second uses finite-dimensional vector-space extension and cannot simply be assumed in a wider category.

## License

AGPL-3.0-or-later. See [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
