# Future Generalisations and Development Phases

## Development phases

**Phase 0 — Founding documents.** Charter, exact definitions, non-claims,
theorem ladder, relation to ROC and PCE. No implementation migration.
*(This is the current state of the repository.)*

**Phase 1 — Repair and claim fibres.** Formalise $F_r = u_0 + \ker D$ and
$L(F_r) = L(u_0) + L(\ker D)$ (R0, R1) as the first central theorems, in
`rocq/`.

**Phase 2 — Descent structure.** Define $\widetilde D : U \to \mathrm{im}\,D$;
prove the descent exact sequence and the induced isomorphism
$\mathrm{coker}\,D_W^{*} \cong \mathrm{Hom}(\ker D, W)$ (R2);
define both obstruction classes $[r] \in \mathrm{coker}\,D$ and
$[L] \in \mathrm{coker}\,D_W^{*}$. This phase must precede Phase 3:
the witness and classification theorems below are stated in terms of
these obstruction classes.

**Phase 3 — Witness theorems and classification.** Prove soundness and
completeness of separators (R4) and gauge directions (R5); prove the
operational three-way classification (R6) and exactness profile
completeness (R7). No JSON yet — that is application territory (see
[`NON_CLAIMS.md`](NON_CLAIMS.md#what-should-not-go-into-this-repository)).

**Phase 4 — Canonical value and universal exact quotient.** Prove that
$x = Lu = Mr$ is independent of all witness choices (R3), and prove the
universal property of $W / A_{D,L}$ (R8).

**Phase 5 — Presentation morphisms and transport.** Formalise isomorphic
transport (R9), then separate preservation from reflection for
noninvertible maps (R10); see
[`PRESENTATION_MORPHISMS.md`](PRESENTATION_MORPHISMS.md).

**Phase 6 — Instantiations.** Formalise the mathematical correspondence
between ROC's cochain objects, PCE's verdict-specific witness
predicates, and the core lift-descent classification. This phase does
not by itself verify the production implementations of either
repository — see [`ROC_INSTANTIATION.md`](ROC_INSTANTIATION.md) and
[`PCE_INSTANTIATION.md`](PCE_INSTANTIATION.md).

**Phase 7 — Wider abstraction.** Only then consider modules over a ring
and abelian categories.

## Why generalisation waits

The right starting point is finite-dimensional vector spaces over
$\mathbb{Q}$ (see [`FOUNDATION.md`](FOUNDATION.md#starting-point-finite-dimensional-mathbbq-vector-spaces)).
Generalisation should be a response to a theorem forcing the question —
for example, R2's use of finite-dimensional extension (see
[`THEOREM_LADDER.md`](THEOREM_LADDER.md#r2--descent-exact-sequence-and-factorisation-equivalence))
is exactly the kind of step that may not survive unchanged in a module or
abelian-category setting, and is a natural place Phase 7 will need to
revisit.

Candidate settings for Phase 7, in roughly increasing generality:

- modules over a ring;
- abelian categories;
- exact categories;
- regular categories;
- fibred or indexed settings.

## Repository layout at completion

```text
lift-descent-exactness/
├── README.md
├── LICENSE
├── NOTICE
├── Makefile
├── docs/
│   ├── FOUNDATION.md
│   ├── MATHEMATICAL_SCOPE.md
│   ├── NON_CLAIMS.md
│   ├── THEOREM_LADDER.md
│   ├── ROC_INSTANTIATION.md
│   ├── PCE_INSTANTIATION.md
│   ├── PRESENTATION_MORPHISMS.md
│   └── FUTURE_GENERALISATIONS.md
├── rocq/
│   ├── LinearInstance.v
│   ├── RepairFiber.v
│   ├── LiftObstruction.v
│   ├── ClaimFiber.v
│   ├── AmbiguitySpace.v
│   ├── ClaimDescent.v
│   ├── CanonicalValue.v
│   ├── ExactnessProfile.v
│   ├── DualWitnesses.v
│   ├── VerdictExclusivity.v
│   ├── VerdictCompleteness.v
│   ├── PresentationMorphisms.v
│   ├── IsomorphicTransport.v
│   ├── Preservation.v
│   ├── Reflection.v
│   ├── CochainInstantiation.v
│   └── PCEInstantiation.v
├── reference/
│   ├── linear_instance.py
│   ├── exactness_profile.py
│   └── witnesses.py
├── examples/
│   ├── obstructed.json
│   ├── underdetermined.json
│   ├── exact.json
│   └── partially_exact.json
└── tests/
```

The Python code in `reference/` is a reference executable semantics; the
Rocq development in `rocq/` is the mathematical source of truth.
