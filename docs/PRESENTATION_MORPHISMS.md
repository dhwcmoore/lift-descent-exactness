# Presentation Morphisms

## Definition

The next major abstraction is not arbitrary category theory. It is a
precise notion of morphism between linear exactness instances.

Let $\mathcal{I} = (U, V, W, D, r, L)$ and
$\mathcal{I}' = (U', V', W', D', r', L')$. A **presentation morphism**
consists of linear maps

$$a : U \to U', \qquad b : V \to V', \qquad c : W \to W'$$

satisfying

$$bD = D'a, \qquad b(r) = r', \qquad cL = L'a.$$

This says: underlying assignments are translated by $a$; residues by
$b$; claims by $c$; the two structural squares commute.

For invertible $a, b, c$, all verdicts are invariant (R9, in
[`THEOREM_LADDER.md`](THEOREM_LADDER.md)). For noninvertible maps,
preservation and reflection separate.

## Two independent reflection obligations

ROC already discovered that preservation is not reflection. This
repository generalises that to two independent reflection questions.

**Reconciliation reflection.** Does $b(r) \in \mathrm{im}\,D'$ imply
$r \in \mathrm{im}\,D$? This reflects zero in the residue
obstruction quotient.

**Exactness reflection.** Does $L'(\ker D') = 0$ imply $L(\ker D) = 0$?
This reflects zero in the ambiguity/descent obstruction.

A presentation transformation is fully verdict-safe only when it handles
both. This is the natural generalisation of ROC's refinement programme
after PCE — see R10 in [`THEOREM_LADDER.md`](THEOREM_LADDER.md).
