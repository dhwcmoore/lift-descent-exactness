# lift-descent-exactness

The general mathematics of two independent obstruction axes for a linear
presentation: **can a presented residue be lifted**, and **does a declared
claim descend** through that presentation.

This repository is not a merger of
[`regional-obstruction-calculus`](https://github.com/dhwcmoore/regional-obstruction-calculus)
(ROC) and [`proof-carrying-exactness`](https://github.com/dhwcmoore/proof-carrying-exactness)
(PCE). It extracts the mathematical situation both of those repositories
instantiate, strips away regions, sensors, PDEs, certificate formats, and
provenance policy, and studies the resulting linear-algebra object on its
own terms. ROC and PCE become instantiations of this theory, not its
ancestors — see [`docs/ROC_INSTANTIATION.md`](docs/ROC_INSTANTIATION.md) and
[`docs/PCE_INSTANTIATION.md`](docs/PCE_INSTANTIATION.md).

## The object of study

Finite-dimensional vector spaces $U, V, W$ over $\mathbb{Q}$, a linear map
$D : U \to V$, a presented residue $r \in V$, and a declared claim map
$L : U \to W$:

$$\mathcal{I} = (U, V, W, D, r, L).$$

Two independent questions:

1. **Lift** — can $r$ be realised, i.e. does $Du = r$ have a solution?
2. **Descent** — is the claim $L$ constant across every solution, i.e. does
   $L$ factor through $D$?

The first defect lives in $\operatorname{coker} D$; the second in
$\operatorname{coker} D_W^{*}$, where $D_W^{*}(M) = M \circ D$. Full
definitions are in [`docs/MATHEMATICAL_SCOPE.md`](docs/MATHEMATICAL_SCOPE.md).

## The three verdicts

| Verdict | Condition |
|---|---|
| **Obstructed** | $[r] \neq 0$ in $\operatorname{coker} D$ — no repair exists |
| **Underdetermined** | $[r] = 0$ but $L(\ker D) \neq 0$ — repairs exist but disagree on the claim |
| **Exact** | $[r] = 0$ and $L(\ker D) = 0$ — the claim is constant across every repair |

`INADMISSIBLE` is deliberately excluded from this trichotomy — see
[`docs/NON_CLAIMS.md`](docs/NON_CLAIMS.md). It belongs to a later evidence/adapter
theory that gates how $(U, V, W, D, r, L)$ gets constructed in the first
place, not to the linear theory itself.

## The central theorem

When both defects vanish, there exist $u \in U$ with $Du = r$ and
$M : V \to W$ with $MD = L$, and the value

$$x = M(r) = L(u)$$

is independent of every choice of $u$ and $M$ — a canonical exact value
constituted by nonunique witnesses. See
[`docs/MATHEMATICAL_SCOPE.md`](docs/MATHEMATICAL_SCOPE.md), Section 6, for
the informal argument, and [`docs/THEOREM_LADDER.md`](docs/THEOREM_LADDER.md),
R3, for the planned formal theorem.

## Repository layout

This is a fresh repository with a deliberately small trusted foundation —
it does not inherit the ROC or PCE codebases. Current status: **Phase 0
(founding documents)**.

```text
lift-descent-exactness/
├── README.md
├── LICENSE
├── NOTICE
├── docs/
│   ├── FOUNDATION.md            — charter and central definitions
│   ├── MATHEMATICAL_SCOPE.md    — the object of study, in full
│   ├── NON_CLAIMS.md            — what this repository does not prove
│   ├── THEOREM_LADDER.md        — R0–R10, the initial theorem sequence
│   ├── PRESENTATION_MORPHISMS.md — morphisms between instances
│   ├── ROC_INSTANTIATION.md     — how ROC instantiates the lift half
│   ├── PCE_INSTANTIATION.md     — how PCE instantiates both halves
│   └── FUTURE_GENERALISATIONS.md — phases 1–8, modules/abelian categories
├── rocq/        — (Phase 1+) Rocq development, mathematical source of truth
├── reference/   — (Phase 3+) reference executable semantics in Python
├── examples/    — (Phase 3+) worked instances for each verdict
└── tests/
```

`rocq/`, `reference/`, `examples/`, and `tests/` are not populated yet;
Phase 0 is founding documents only, per
[`docs/FUTURE_GENERALISATIONS.md`](docs/FUTURE_GENERALISATIONS.md#development-phases).

## Relation to ROC and PCE

```text
                 lift-descent-exactness
                    /             \
                   /               \
regional-obstruction-calculus   proof-carrying-exactness
```

The intended mathematical dependency direction is from
`lift-descent-exactness` to the ROC and PCE instantiations: this
repository is intended to develop and formally verify the mathematics
that ROC's regional and cochain instances, and PCE's independently
checkable certificates, both instantiate. At Phase 0 this relationship
is architectural — stated in the founding documents, not yet backed by
Rocq proofs — with formal instantiation theorems scheduled for Phase 6
(see [`docs/FUTURE_GENERALISATIONS.md`](docs/FUTURE_GENERALISATIONS.md#development-phases)).
The dependency direction is one-way — no circular dependency.

## License

AGPL-3.0, matching `regional-obstruction-calculus` and
`proof-carrying-exactness`. See [`LICENSE`](LICENSE).
