# Mathematical responsibilities and evidence

The paper establishes a reduction from infinite packings to small nonobtuse
triangle clusters. The code proves the specified finite-dimensional exclusions.
These statements are linked by actual contact charts, domain bounds, symmetry
conventions, and strict rejection predicates, not by the names of functions alone.

## The implemented mathematical inputs

The eight principal assertions have stable names NKQNXUN, RWWHLQT, BXZBPJW,
JQMRXTH, KUGAKIK, HUQEJAT, QPJDYDB and FHBGHHY. The calculation index gives the
printed lemma number, assumptions, all terminal cases, and commands for each.
Additional entries cover the triangle estimates, dimer reductions, squeezing signs
and derivative paths. Seven-letter comments provide navigation without adding
printed labels or changing theorem numbering.

The exceptional peripheral in JQMRXTH is allowed area below `aK+2*epsM_I`;
the pair target is not weakened. The midpoint/slider branches for RWWHLQT retain
all three isosceles equalities and both nonshared length-1.8 endpoints. The contact
fill routines retain all applicable critical-point candidates and treat an
intersection as empty only when disjointness is established.

The squeezing argument uses two logically different range calculations. The four
new sign searches establish the finite slope signs and supporting-side assertions
under the lemma’s full area cap `acrit+epsN`. The existing squeezing search then
establishes the area-decrease disjunction, which implies the reciprocal inequality
on those branches. See SQUEEZING.md and the code commentary for the vector signs
and all five relative rotations per pointer case.

The exact identity `area(T0)+area(T1)=2*acrit+sigma*t^2` proves the final one-parameter
minimum analytically. The recentered numerical convexity calculation is optional
corroboration. The 0.007 triple-contact allowance is stronger than the paper’s 0.008
and is retained. The 1.2 debug diagnostic is not cited as a proof of the 1.237 bound.
The historical one127 diagnostic is not a required theorem premise.

## What is trusted

The MITM commentary proves a retention invariant conditional on valid enclosures:
a feasible compatible cluster on or below the target retains at least one common
key; lower-area bounds cannot exclude it; upper cuts are combined in the conservative
direction; and subdivision covers closed parents. Success requires exhaustion,
not merely small boxes. This is a mathematical account of the algorithm, not a
machine-checked proof of the implementation.

The external interval backend is trusted for directed rounding and whole-interval
transcendental ranges. The OCaml bytecode runtime/compiler and the geometric chart
implementations are likewise part of the trusted computation. Contract tests,
independent polygon fixtures, symbolic identities, and finite exhaustive pruning
models provide additional checks. They are not represented as universal proofs of
all inverse-domain branches or primitive floating-point behavior.

## Evidence types

`evidence/prior-executions.json` contains verified source-specific prior executions,
including the enlarged domains and all four squeezing-sign cases. Public copies of
these logs omit personal absolute paths; both original and public log hashes are
recorded. They explain provenance and costs. They are not imported as current-release
passes. Mathematical-source token comparisons record that the integrated numerical
modules differ from those tested files only in comments/spacing.

`verification/CONFIRMATION.md` is generated from runs of this exact assembled release.
It requires all selected proof/test records, exit statuses, markers, log digests,
and consistent source/environment fingerprints. Its separate Wolfram entry requires
a complete 161-check source-matching export. An archive containing the generated
confirmation can be created with `confirm.py --bundle` after those conditions hold.

The fixed mathematical exposition does not depend on a mutable statement that a
future run has already happened. The generated record supplies that statement when
supported by the execution evidence.
