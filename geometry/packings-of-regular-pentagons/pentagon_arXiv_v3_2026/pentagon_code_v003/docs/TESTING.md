# Function-contract tests

## Why these tests exist

An interval exclusion can be sound while retaining unnecessary candidates, but it
must never discard a valid candidate. The suite tests that one-sided contract rather
than demanding exact geometric classification from every coarse interval box.
Every test is named and reports its inputs or fixture purpose. The tests execute
the actual release functions, not copied versions of their rejection predicates.

At PACKAGE_ROOT, **in Linux/Ubuntu-WSL Bash**:

```bash
python3 run.py --tests --extended
```

Add `--copy-report windows-downloads` on WSL for an optional report copy. The default
short selection runs 153 ordinary unit checks plus 71 squeezing-sign checks. The
extended stage repeats the 153 ordinary checks and adds three seeded generated
groups: 156 reported checks, not 156 new independent theorems. Numerical assertions
inside generated groups are counted separately from top-level named groups in logs.
The report records exact source versions and seeds. A failed test blocks proof jobs.

## Contracts and independent references

| Layer | Tests and meaning |
|---|---|
| Interval adapter, `pent.ml` | Exact dyadic arithmetic; rational constants; strict comparisons; common-endpoint retention; square-root domain errors requesting subdivision rather than success; splits covering the original box. |
| Pair/contact geometry, `pet.ml`, `banana.ml` | Periodization, contact fixtures, curve/inverse samples, actual triangle reconstruction, lower-area bounds, and independent polygon/determinant diagnostics. |
| Automatic differentiation | Value/first/second derivative rules on independently known polynomials and trigonometric expressions; both original first- and second-order test bindings retained. |
| MITM keys and cuts | Boundary-key overlap, lower-area minima and upper allowable-cut maxima, duplicate-key behavior, finite satisfiable and impossible models checked by exhaustive enumeration. |
| Domain regressions | All three equality endpoints and both 1.8 endpoints in the real pseudo2 filter; exceptional-peripheral cap `aK+2*epsM_I` in the real initializer. |
| Squeezing signs | Four pointer-direction cases, symmetry/rotation fixtures, actual center/contact vectors, supporting-side sign tests, overlap-only exclusions and no-false-success behavior. |

The test named `fillout2C.ice-ray-witness` distinguishes the reconstructed full-area
enclosure from `areamin_acute`, whose output is a **lower bound** evaluated at side
lower endpoints. A lower-bound interval is not required to overlap the exact area.
An absent witness still fails the reconstruction test.

Tests labeled C013/C014/C015 retain stable regression names. They refer respectively
to the exceptional-peripheral cap, the complete equality/1.8 boundary set, and
independent extrema candidates in the contact enclosure. Their mathematical purpose
is explained here and in the source; no private review history is needed.

## Finite exhaustive tests are deliberately two-sided

The MITM fixtures include an actual feasible combination at the target. It must
survive all tested pruning rounds. Testing only impossible problems would allow a
broken implementation that deletes everything to pass. Independent enumeration is
used only on small finite fixtures where it is transparent. This tests the pruning
implementation, not all possible real pentagon geometries.

## Supplementary symbolic/numerical checks

The Wolfram suite checks exact algebraic constants, elementary bounds, endpoint
formulas, contact identities, and the geometric shear formula. Its catalogue marks
whether a check is a paper assertion, a supporting identity, an implementation check,
or a numerical diagnostic. It does not replace the OCaml interval searches.

The Python suite checks the execution controller and completion-record validation
using **synthetic child processes**, not simulated mathematical passes. At the
package root in Bash, it can be run separately:

```bash
python3 -m unittest discover -s tests/python -v
```

## Trust boundary

Passing finite tests does not prove every inverse-contact or interval-enclosure
contract on a continuum. The mathematical commentary explains the formulas and
retention invariant; the directed arithmetic backend, compiler/runtime, and coordinate
implementations are trusted components. A failure is preserved and reported, not
fixed automatically by changing a threshold, tolerating a negative interval, or
catching an unexpected exception as an empty domain.

## Optional independent algebraic checker

`python3 scripts/verify_exact_identities.py` checks 56 selected identities/margins
using SymPy and exact outward rational intervals for radicals. It requires the
optional Python SymPy package and is not imported by the standard runner. Its
reference expressions are in `tests/reference/paper_bounds.json`; results are saved
under verification/. This optional check does not replace the Wolfram suite or
enter the required OCaml completion count.
