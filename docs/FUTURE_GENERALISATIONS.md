# Future Generalisations and Development Phases

## Development phases

**Phases 1-6 are complete.** The Rocq development (`rocq/`) contains 41
source files proving every result described below; see the top-level
[`README.md`](../README.md#status) for the current inventory and
[`THEOREM_LADDER.md`](THEOREM_LADDER.md) for the R0-R12 statements.
**Phase 7 — evidence-to-instance adapters — is planned next.** Wider
abstraction has moved to Phase 8; see "Why generalisation waits" below.

**Phase 0 — Founding documents.** Charter, exact definitions, non-claims,
theorem ladder, relation to ROC and PCE. No implementation migration.
*(Complete.)*

**Phase 1 — Repair and claim fibres.** Formalise $F_r = u_0 + \ker D$ and
$L(F_r) = L(u_0) + L(\ker D)$ (R0, R1) as the first central theorems, in
`rocq/`. *(Complete.)*

**Phase 2 — Descent structure.** Define $\widetilde D : U \to \mathrm{im}\,D$;
prove the descent exact sequence and the induced isomorphism
$\mathrm{coker}\,D_W^{*} \cong \mathrm{Hom}(\ker D, W)$ (R2);
define both obstruction classes $[r] \in \mathrm{coker}\,D$ and
$[L] \in \mathrm{coker}\,D_W^{*}$. This phase must precede Phase 3:
the witness and classification theorems below are stated in terms of
these obstruction classes. *(Complete.)*

**Phase 3 — Witness theorems and classification.** Prove soundness and
completeness of separators (R4) and gauge directions (R5); prove the
operational three-way classification (R6) and exactness profile
completeness (R7). No JSON yet — that is application territory (see
[`NON_CLAIMS.md`](NON_CLAIMS.md#what-should-not-go-into-this-repository)).
*(Complete.)*

**Phase 4 — Canonical value and universal exact quotient.** Prove that
$x = Lu = Mr$ is independent of all witness choices (R3), and prove the
universal property of $W / A_{D,L}$ (R8). *(Complete.)*

**Phase 5 — Presentation morphisms and transport.** Formalise isomorphic
transport (R9), then separate preservation from reflection for
noninvertible maps (R10); see
[`PRESENTATION_MORPHISMS.md`](PRESENTATION_MORPHISMS.md). *(Complete.)*

**Phase 6 — Instantiations.** Formalise the mathematical correspondence
between ROC's cochain objects, PCE's verdict-specific witness
predicates, and the core lift-descent classification, together with an
abstract admissibility gate composed with the three-way linear
classification. This phase does not by itself verify the production
implementations of either repository — see
[`ROC_INSTANTIATION.md`](ROC_INSTANTIATION.md) and
[`PCE_INSTANTIATION.md`](PCE_INSTANTIATION.md). *(Complete.)*

**Phase 7 — Evidence-to-instance adapters and public demonstrator.**
Formalise the partial, auditable passage

$$e \xrightarrow{\alpha} (U, V, W, D, r, L),$$

its coherence with `AdmissibilityGate`, and the resulting classification
of accepted evidence (R13-R16; see
[`THEOREM_LADDER.md`](THEOREM_LADDER.md)). The abstract adapter theory
belongs in this repository. A concrete public demonstrator, built on
multi-receiver distributed timing observations, is proposed as a
separate sibling repository — not as code or data in this one.
*(Planned — not yet implemented.)*

### Phase 7 unit sequence (planned)

```text
Unit 35  QPackedLinearInstance.v
Unit 36  QEvidenceAdapter.v
Unit 37  QAdapterAdmissibility.v
Unit 38  QAdapterPCEComposition.v
```

None of these units exists yet. This list records the proposed sequence
only; it authorises no implementation.

**Phase 8 — Wider abstraction.** Only after Phase 7 consider modules
over a ring and abelian categories. *(Future — not started.)*

## Why generalisation waits

The right starting point is finite-dimensional vector spaces over
$\mathbb{Q}$ (see [`FOUNDATION.md`](FOUNDATION.md#starting-point-finite-dimensional-mathbbq-vector-spaces)).
Generalisation should be a response to a theorem forcing the question —
for example, R2's use of finite-dimensional extension (see
[`THEOREM_LADDER.md`](THEOREM_LADDER.md#r2--descent-exact-sequence-and-factorisation-equivalence))
is exactly the kind of step that may not survive unchanged in a module or
abelian-category setting, and is a natural place Phase 8 will need to
revisit.

Candidate settings for Phase 8, in roughly increasing generality:

- modules over a ring;
- abelian categories;
- exact categories;
- regular categories;
- fibred or indexed settings.

## Repository layout as of Phase 6 completion

The `rocq/` tree actually built differs from the module-by-module sketch
originally planned here: theorems were grouped and named by the unit
sequence that proved them rather than by the one-file-per-concept split
below. The current, accurate 41-file listing is in the top-level
[`README.md`](../README.md#formal-development); that listing is the
authoritative one and is not duplicated here to avoid drift.

`reference/`, `examples/`, and `tests/` — a Python reference semantics
and JSON example instances — were part of the original Phase 3+ plan but
were never populated. Phase 6 confirmed that this repository's scope is
the Rocq formalisation only; executable reference semantics, certificate
formats, and worked examples belong to the applied repositories (ROC,
PCE) that instantiate this theory, not to this one (see
[`NON_CLAIMS.md`](NON_CLAIMS.md#what-should-not-go-into-this-repository)).
Those three directories remain unbuilt and are not planned for Phase 7.

The Rocq development in `rocq/` is the sole mathematical source of
truth.
