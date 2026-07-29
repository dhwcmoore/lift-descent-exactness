# Foundation

## Charter

This repository develops the mathematics of lift, obstruction, claim
descent, and exact value constitution for finite-dimensional linear
presentations. Given a linear map $D : U \to V$, a presented residue
$r \in V$, and a claim map $L : U \to W$, it distinguishes failure of
realisation from failure of claim determination. The first defect is
represented by the class of $r$ in $\mathrm{coker}\,D$; the second by
the restriction of $L$ to $\ker D$, equivalently by the failure of $L$ to
factor through $D$. When both defects vanish, the claim has a canonical
value independent of all choices of repair and factorisation witness.

## Central non-claim

This repository does not prove that any physical, geometric, evidential,
or computational system has been represented correctly by $D$, $r$, and
$L$. This repository takes an exact algebraic presentation as its
starting point and develops the consequences that follow from it. At
Phase 0 those consequences are stated as a theorem programme; formal
proofs are not yet present. (Expanded in [`NON_CLAIMS.md`](NON_CLAIMS.md).)

## Why a third repository, and why it is not a merger

`regional-obstruction-calculus` (ROC) answers one question: can a
presented residue be lifted through a coboundary map? `proof-carrying-exactness`
(PCE) adds a second, independent question: does a declared claim survive
that lift regardless of which repair is chosen? Both questions are
instances of the same underlying linear-algebra situation, but neither
repository states that situation on its own terms — ROC because it never
needed a claim map, PCE because it wraps the mathematics in certificate
formats, digests, and application-specific evidence.

Merging the two codebases would preserve their accidental historical
shape — which grew from regions, sensors, and provenance policy — rather
than expose the mathematics underneath it. Instead, this repository states
the common object directly:

$$\mathcal{I} = (U, V, W, D, r, L)$$

and builds its theory from first principles: repair fibres, cokernel
obstruction classes, ambiguity spaces, canonical values, and morphisms
between instances. ROC and PCE are then *instantiations* of this theory,
not its parents. See [`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md) for
the full object, [`ROC_INSTANTIATION.md`](ROC_INSTANTIATION.md) and
[`PCE_INSTANTIATION.md`](PCE_INSTANTIATION.md) for how each existing
repository realises it.

## Starting point: finite-dimensional $\mathbb{Q}$-vector spaces

The theory begins in finite-dimensional vector spaces over $\mathbb{Q}$,
not in arbitrary category theory. That setting already contains kernels,
images, cokernels, dual separators, exact rational arithmetic,
factorisations, affine fibres, quotient spaces, coordinate
transformations, and executable witnesses — everything the first theorem
ladder needs. Only after that ladder is stable does it make sense to ask
which results survive in modules over a ring, abelian categories, exact
categories, regular categories, or fibred/indexed settings (see
[`FUTURE_GENERALISATIONS.md`](FUTURE_GENERALISATIONS.md)). Generalisation
is a response to a theorem forcing the question, not a starting posture.

## The two independent axes

**Existence axis.** $r \in \mathrm{im}\,D$ or $r \notin \mathrm{im}\,D$
— can the concrete situation be reconciled at all within the declared
algebra?

**Determination axis.** $L(\ker D) = 0$ or $L(\ker D) \neq 0$ — does the
claimed value survive the freedom remaining in that reconciliation?

$$\boxed{\text{coherence is not exactness}}$$

$$\boxed{\text{exactness is invariance across all coherent realisations}}$$
