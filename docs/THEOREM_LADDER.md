# Theorem Ladder

The initial sequence of results for the linear theory. Statements only —
the proofs are complete in the Rocq development (`rocq/`; see
[`FUTURE_GENERALISATIONS.md`](FUTURE_GENERALISATIONS.md) for the phase
in which each result was formalised). Definitions referenced here are in
[`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md). The mathematical
correspondences with ROC and PCE that build on this ladder are stated
separately in [`ROC_INSTANTIATION.md`](ROC_INSTANTIATION.md) and
[`PCE_INSTANTIATION.md`](PCE_INSTANTIATION.md).

## R0 — Repair-fibre normal form

If $Du_0 = r$, then

$$F_r = u_0 + \ker D.$$

## R1 — Claim-fibre normal form

If $F_r \neq \varnothing$, then

$$L(F_r) = L(u_0) + L(\ker D).$$

## R2 — Descent exact sequence and factorisation equivalence

Let $\rho : \mathrm{Hom}(U, W) \to \mathrm{Hom}(\ker D, W)$,
$\rho(L) = L|_{\ker D}$. The sequence

$$\mathrm{Hom}(V, W) \xrightarrow{D_W^{*}} \mathrm{Hom}(U, W) \xrightarrow{\rho} \mathrm{Hom}(\ker D, W) \longrightarrow 0$$

is exact, inducing a canonical isomorphism
$\mathrm{coker}\,D_W^{*} \cong \mathrm{Hom}(\ker D, W)$,
$[L] \mapsto L|_{\ker D}$ (see
[`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md#the-descent-exact-sequence)).

Consequently the following are equivalent:

- $L(\ker D) = 0$;
- $\ker D \subseteq \ker L$;
- $[L] = 0$ in $\mathrm{coker}\,D_W^{*}$;
- there exists a unique $\overline{L} : \mathrm{im}\,D \to W$ such
  that $L = \overline{L} \circ \widetilde{D}$, where
  $\widetilde D : U \to \mathrm{im}\,D$, $\widetilde D(u) = D(u)$
  (see [`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md#7-the-intrinsic-factorisation-is-not-the-matrix-m));
- there exists an ambient extension $M : V \to W$ such that $L = MD$.

The final equivalence uses finite-dimensional vector-space extension and
should be labelled as such — it does not survive unchanged into every
generalisation (see [`FUTURE_GENERALISATIONS.md`](FUTURE_GENERALISATIONS.md)).

## R3 — Canonical value

If $F_r \neq \varnothing$ and $L(\ker D) = 0$, there exists a unique
$x \in W$ such that $Lu = x$ for every $u \in F_r$.

## R4 — Obstruction certificate

$r \notin \mathrm{im}\,D$ if and only if there exists $y \in V^{*}$
such that $yD = 0$, $y(r) \neq 0$.

## R5 — Underdetermination certificate

$L(\ker D) \neq 0$ if and only if there exists $k \in U$ such that
$Dk = 0$, $Lk \neq 0$.

## R6 — Operational three-way classification

Exactly one of Obstructed, Underdetermined, Exact holds for every
$(D, r, L)$. This verdict is the collapse of the four-sector exactness
profile (see
[`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md#profile-versus-verdict))
that reports both sectors with $[r] \neq 0$ as Obstructed.

## R7 — Exactness profile completeness

The pair $([r], [L]) \in \mathrm{coker}\,D \times \mathrm{coker}\,D_W^{*}$
completely determines the verdict, and — unlike the collapsed verdict of
R6 — retains the descent defect $[L]$ even when $[r] \neq 0$ (see
[`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md#profile-versus-verdict)).
Equivalently, by the isomorphism of R2, the pair
$([r], L|_{\ker D}) \in \mathrm{coker}\,D \times \mathrm{Hom}(\ker D, W)$.

## R8 — Universal exact quotient

The quotient claim $\pi L : U \to W / A_{D,L}$ descends through $D$. For
every $q : W \to Q$ such that $qL$ descends through $D$, there exists a
unique $\overline q : W / A_{D,L} \to Q$ satisfying $q = \overline q \circ \pi$
(see [`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md#8-the-ambiguity-object-is-richer-than-a-binary-verdict)).

## R9 — Isomorphic transport

Invertible changes of state, residue, and claim coordinates induce
isomorphisms on the lifting and descent obstruction spaces
($\mathrm{coker}\,D$ and $\mathrm{coker}\,D_W^{*}$ before and
after the change are not literally the same space). Under these induced
isomorphisms, the exactness profile and its witnesses are transported,
and the operational verdict is invariant.

## R10 — Noninvertible preservation and reflection

Identify exact conditions under which a presentation map preserves
realisability, reflects realisability, preserves claim exactness, and
reflects claim exactness. This generalises ROC's N0 and E0 results to
both obstruction axes — see
[`PRESENTATION_MORPHISMS.md`](PRESENTATION_MORPHISMS.md).
