# Theorem Ladder

The sequence of results for the linear theory. Statements only — the
proofs of R0-R12 are complete in the Rocq development (`rocq/`; see
[`FUTURE_GENERALISATIONS.md`](FUTURE_GENERALISATIONS.md) for the phase
in which each result was formalised). Definitions referenced here are in
[`MATHEMATICAL_SCOPE.md`](MATHEMATICAL_SCOPE.md). R11 and R12 are the
mathematical correspondences with ROC and PCE, detailed further in
[`ROC_INSTANTIATION.md`](ROC_INSTANTIATION.md) and
[`PCE_INSTANTIATION.md`](PCE_INSTANTIATION.md). R13-R16 are **planned
for Phase 7** and are not yet proved; see
[`FUTURE_GENERALISATIONS.md`](FUTURE_GENERALISATIONS.md).

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

## R11 — ROC cochain/lifting instantiation

For a finite cochain presentation $U = C^0$, $V = C^1$, $D = \delta^0$,
with the zero-dimensional claim space $W = 0$:

$$\text{ROC repairable}(\delta^0, r) \iff \text{lifting-obstruction zero}(\delta^0, r),$$

$$\text{ROC cycle separator}(\delta^0, r, y) \iff \text{separator witness}(\delta^0, r, y).$$

Descent is automatic for the zero claim, so only two operational
outcomes remain: Exact (a cochain repair exists) and Obstructed (a
separator proves none exists) — see
[`ROC_INSTANTIATION.md`](ROC_INSTANTIATION.md).

## R12 — Admissibility-gated PCE witness instantiation

An abstract admissibility gate on evidence $e$, composed with PCE's
three algebraic witness forms (exact, underdetermined, obstructed —
matching R3-R5), yields the nested classification

$$\text{GatedInadmissible} \quad\text{or}\quad \text{GatedAdmissible}(v)$$

for $v$ one of Obstructed, Underdetermined, Exact — never a flat
four-constructor verdict. In the exact case the claimed value is the
unique canonical value of R3 — see
[`PCE_INSTANTIATION.md`](PCE_INSTANTIATION.md).

## Phase 7 (planned)

The following results are proposed, not proved. They are stated here to
fix the intended shape of the Phase 7 ladder before any implementation
begins — see [`FUTURE_GENERALISATIONS.md`](FUTURE_GENERALISATIONS.md).

## R13 — Packed evidence-to-instance construction *(planned, Phase 7)*

A dependent package representing a finite rational instance whose
dimensions are part of the value, together with a partial adapter

$$\alpha : E \to \operatorname{option}(\operatorname{PackedInstance}).$$

`Some I` would mean the adapter accepted the evidence and constructed
$I$; `None` would mean the adapter rejected the evidence before linear
classification. `None` must not be interpreted as an algebraic
obstruction.

## R14 — Adapter-gate coherence *(planned, Phase 7)*

$$\operatorname{Admissible}(e) \iff \exists I,\ \alpha(e) = \operatorname{Some}(I).$$

Positive gate witnesses would imply successful construction; negative
gate witnesses would imply rejection.

## R15 — Accepted-evidence classification *(planned, Phase 7)*

If $\alpha(e) = \operatorname{Some}(I)$ under valid positive gate
evidence, the R12 gated classification would apply to $I$ and yield
exactly one of GatedAdmissible VerdictObstructed, GatedAdmissible
VerdictUnderdetermined, GatedAdmissible VerdictExact — never
GatedInadmissible. A negative gate witness would yield GatedInadmissible
without constructing or classifying any instance.

## R16 — Adapter-relative assurance *(planned, Phase 7)*

$$\alpha(e) = \operatorname{Some}(I) \Longrightarrow \operatorname{Represents}(e, I),$$

relative to a declared $\operatorname{Represents}$ relation. This must
not be read as proving physical truth, sensor calibration, evidence
completeness, unique model correctness, or real-world safety.
