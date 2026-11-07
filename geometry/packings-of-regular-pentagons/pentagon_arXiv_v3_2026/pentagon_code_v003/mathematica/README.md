# Wolfram paper checks

## Context and purpose

This folder belongs to code v003 and manuscript `paper/pentagon_v005.tex`. The
package checks small numerical bounds and exact identities used in the paper, plus
clearly identified implementation examples and numerical diagnostics. It is not
the interval proof engine. There are **161 checks in six sections**; every named
check is documented in [the catalogue](../docs/WOLFRAM_CHECKS.md), including the exact
assertion, reason it is useful, printed paper reference, and its logical role.

Loading `PentagonChecks.wl` defines the package but does not launch the checks, close
your kernel, or require notebook plots. Paths are based on the selected package file,
not the notebook’s working directory. Keep this entire extracted distribution
intact: the metadata and manuscript are used for documentation and source identity.

## Mathematica notebook or desktop kernel (Windows, Linux, or macOS)

Use a fresh kernel. Evaluate the following as **Wolfram Language input cells**, not
in Bash. The file dialog lets you select `mathematica/PentagonChecks.wl` wherever you
extracted the package; canceling the dialog should not be followed by the next cells.

```wolfram
packageFile = SystemDialogInput["FileOpen"];
```

After selecting the correct file, evaluate:

```wolfram
Get[packageFile];
report = PentagonChecks`RunChecks[];
output = FileNameJoin[{DirectoryName[DirectoryName[packageFile]],
   "verification", "paper-checks.json"}];
PentagonChecks`ExportReport[output, report]
```

The exported file is in `verification/` at the package root. A notebook saved in
another directory works identically. Do not copy only the `.wl` file away from
its metadata and manuscript. No private home or Downloads directory is assumed.

To inspect the purpose of the checks without running them:

```wolfram
PentagonChecks`AvailableSections[]
PentagonChecks`DescribeChecks["constants"]
```

To run just one section while studying it:

```wolfram
PentagonChecks`RunChecks["Sections" -> {"gamma"}]
```

A partial run is clearly labeled and is not accepted as the complete 161-check
confirmation. The full report remains available as ``PentagonChecks`$LastReport``.

## Command line with wolframscript

In **Linux Bash**, at PACKAGE_ROOT (the folder with `run.py`), run:

```bash
wolframscript -file mathematica/run_checks.wls --output verification/paper-checks.json
```

In **Windows PowerShell**, at that same extracted package root, with wolframscript
installed and available on PATH, the equivalent command is:

```powershell
wolframscript -file .\mathematica\run_checks.wls --output .\verification\paper-checks.json
```

For a standalone review of a section, add `--section constants` (repeat for several).
A normal full run exits zero only if the complete selected expected set evaluated
to `True`. Unexpected messages, timeouts, unevaluated conditions, false results,
missing metadata, and duplicate or absent checks do not become successes.

## The six sections

| Section | Checks | Mathematical task |
|---|---:|---|
| `constants` | 16 | Radical identities, normalization/density, decimal rounding, and correction constants. |
| `triangle-bounds` | 45 | Explicit side/radius area inequalities used by the geometric reductions; basic triangle-formula fixtures. |
| `obtuse-endpoints` | 27 | Cyclic/right quadrilateral endpoints, four certified interval cells, trapezoid derivatives. |
| `gamma` | 35 | Exact shear-area identity, derivatives and symmetry; pinwheel slice identities and rational parameter examples. |
| `contact-identities` | 8 | Slider/midpoint/reflection identities and independent area formulas. |
| `diagnostics` | 30 | Seeded numerical determinant comparisons and rigid-motion invariance; not continuum proofs. |

Constants and bounds are exact rationals/algebraic numbers until a diagnostic
explicitly requests numerical evaluation. A rounded decimal is tested against its
half-unit rounding interval. The four `case4.cell-lower-bound` checks use monotonicity
from the paper and exact endpoint differences to bound whole cells; they are not
four arbitrary samples. Each generated ID is listed separately in the catalogue.

## Incorporate the result into the release confirmation

After exporting the full report, open **Ubuntu/Linux Bash at PACKAGE_ROOT**:

```bash
python3 confirm.py --wolfram verification/paper-checks.json --check
```

The source-hash check deliberately rejects a report from another copy/version of the
paper or package. If the report was exported elsewhere, supply its actual path.
`--check` returns a nonzero exit status until both required sets are complete.
A valid Wolfram report is retained even when the OCaml set is not yet complete.
To import it and inspect the separate statuses without requiring combined completion,
omit `--check` from this command.

The package documents its operations using the Wolfram `BeginPackage`, `Get`,
`$InputFileName`, `FileHash`, `TimeConstrained`, and `Export` interfaces:
https://reference.wolfram.com/language/
