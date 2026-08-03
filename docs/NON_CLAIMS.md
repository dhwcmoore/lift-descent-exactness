# Non-Claims

## The central non-claim

This repository does not prove that any physical, geometric, evidential,
or computational system has been represented correctly by $D$, $r$, and
$L$. This repository takes an exact algebraic presentation as its
starting point and develops the consequences that follow from it. Those
consequences are now formally proved in the Rocq development (`rocq/`);
see [`THEOREM_LADDER.md`](THEOREM_LADDER.md). Whether a regional layout, sensor comparison, PDE
discretisation, or other domain presentation is faithfully captured by
$(U, V, W, D, r, L)$ is a question for ROC where its regional
construction applies, for a domain-specific adapter, or for another
repository that explicitly constructs the instance — not for this one.
PCE currently begins at an already constructed algebraic instance and
should not be cited as verifying this adapter boundary.

## Where `INADMISSIBLE` belongs

`INADMISSIBLE` is not a fourth verdict alongside Obstructed,
Underdetermined, and Exact. Admissibility is a gate on the *construction*
of the mathematical instance, not a property the linear theory can see
once the instance already exists.

Typography follows this distinction deliberately: the mathematical
verdicts are written as Title Case prose — Obstructed, Underdetermined,
Exact — while `INADMISSIBLE` and other implementation-level PCE verdict
literals are written as backticked all-caps code, since they belong to
PCE's concrete enum rather than to the linear theory's vocabulary.

The clean architecture:

$$e \xrightarrow{\text{adapter}} (U, V, W, D, r, L),$$

where $e$ is domain evidence. This admissibility structure is now
formalised abstractly in [`rocq/QAdmissibilityGate.v`](../rocq/QAdmissibilityGate.v)
as:

- a type of evidence packages $E$;
- a predicate $\mathrm{Admissible} : E \to \mathrm{Prop}$;
- a type of positive witnesses and a type of negative witnesses;
- soundness of each witness type with respect to $\mathrm{Admissible}$.

Deliberately absent: a compiler $\alpha : E \to \mathrm{Instance}$. The
gate takes evidence $e$ and the algebraic instance $(D, r, L)$ as
independent parameters and proves soundness of their composition; it
does not itself certify that a particular $(D, r, L)$ was correctly
constructed from $e$ — that remains a domain-adapter question, outside
this repository.

The core linear theory proves

$$\mathrm{Admissible}(e) \Rightarrow \text{one of Obstructed, Underdetermined, Exact}$$

in [`rocq/QPCEInstantiation.v`](../rocq/QPCEInstantiation.v). It does not
decide what admissibility means for every domain. That keeps geometry
and algebra distinct.

## What should not go into this repository

- Stone Soup
- tracking
- sensor objects
- PDEs
- JSON certificate formats
- SHA-256 digests
- command-line interfaces
- provenance graph rules
- application adapters
- commercial use cases
- domain-specific admissibility policies

These belong in applied repositories — ROC, PCE, and their downstream
consumers — not in the linear theory itself.

## What this repository does contain

- the abstract mathematical instance $(U, V, W, D, r, L)$
- repair fibres
- cokernel obstruction classes
- ambiguity spaces
- claim fibres
- factorisation through $\mathrm{im}\,D$
- canonical exact values
- dual certificates
- verdict exclusivity and completeness
- presentation morphisms
- invariance under invertible transformations
- preservation and reflection under noninvertible transformations
- cochain instantiations
- a formal connection to ROC
- a formal connection to PCE

## This repository does not inherit the ROC or PCE codebases

Do not copy ROC into it and then add PCE — that would preserve the
accidental historical shape of the work rather than expose its
mathematics. This is a fresh repository with a deliberately small trusted
foundation. ROC and PCE are instantiations, not parents whose entire
contents are inherited. See [`FOUNDATION.md`](FOUNDATION.md#why-a-third-repository-and-why-it-is-not-a-merger).
