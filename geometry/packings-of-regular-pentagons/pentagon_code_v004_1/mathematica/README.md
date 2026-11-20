# PentagonChecks — a standalone Mathematica component

## What to copy to the Mathematica machine

Copy **this entire `mathematica` folder**, to any location and under any folder
name. There is no required parent directory. Its executable/data dependencies
are exactly these three files, kept side by side:

```text
PentagonChecks.wl       mathematical definitions, checks, reporting API
checks_catalog.json    descriptions, assertions, references, and roles of all checks
expected_checks.json   the complete set of expected IDs, grouped by section
```

`run_checks.wls` is the optional command-line entry point. It calls the library;
the library does not load or hash it. You do not need that file for notebook use.

No LaTeX, PDF, label map, Python, OCaml, project installation, network connection,
or directory from another computer is needed. A licensed Mathematica/Wolfram
kernel is required. The two JSON files are explicit inputs, not optional files.
`README.md` and `CHECKS.md` are human documentation and are not runtime inputs.

There are **161 checks in six sections**. They evaluate exact identities, small
area bounds, and separately labeled numerical examples. They do not read or
verify the prose of a `.tex` file. [CHECKS.md](CHECKS.md) explains what each check
asserts and why it is relevant to the paper. Printed paper references are
navigation metadata, not files loaded by the program.

## Notebook route (Windows, macOS, or Linux)

Use a fresh kernel. The following are **Wolfram Language input cells in Mathematica**,
not shell commands. In the first cell, select **`PentagonChecks.wl`**, not a `.tex`
file. Canceling a dialog means stop before evaluating the following cells.

```wolfram
packageFile = SystemDialogInput["FileOpen"];
If[StringQ[packageFile], Get[packageFile]]
```

After a successful load, run:

```wolfram
report = PentagonChecks`RunChecks[];
```

Choose an output file explicitly. It can be on your Desktop, a USB drive, or any
other writable folder. Choose a new filename: an existing report is not overwritten.

```wolfram
output = SystemDialogInput["FileSave", "paper-checks.json"];
If[StringQ[output], PentagonChecks`ExportReport[output, report]]
```

Only the exported JSON needs to return to the main project computer. There is no
need to copy the manuscript in the opposite direction. The report also remains
available in ``PentagonChecks`$LastReport`` during this kernel session.

For a first-time reader wishing to inspect the catalogue before calculating:

```wolfram
PentagonChecks`ComponentFiles[]
PentagonChecks`AvailableSections[]
PentagonChecks`DescribeChecks["constants"]
```

For study of one section, `RunChecks["Sections" -> {"gamma"}]` is supported.
Such a partial report is not a complete 161-check confirmation.

## Command-line route

**Bash on Linux/macOS**, from any directory (replace the two example paths):

```bash
wolframscript -file "/path/to/check-folder/run_checks.wls" \
  --output "/path/to/output/paper-checks.json"
```

**Windows PowerShell**, from any directory:

```powershell
wolframscript -file "D:\Research\check-folder\run_checks.wls" --output "D:\Results\paper-checks.json"
```

`--output` is mandatory. The runner never invents a `verification/` directory in
a parent folder. `--section NAME` can be repeated; no section option means all six.
Use `--help` to see the invocation without loading or running the package.

## Report identity and dependencies

A schema-2 report hashes the three runtime files above, with **local relative names**.
Moving or renaming their containing directory does not change the identity.
Changing an input during a run causes source validation to fail, not to become
a successful result. Export preserves the original result objects; it does not
relabel an old result as a new execution.

The report identifies the suite, kernel, options, sections, expected IDs, individual
outcomes, and execution time. It has no mandatory `Manuscript` field and never calls
`FileHash` on a manuscript or label map. Associating the report with a particular
article belongs to the main project's confirmation step, on the other computer.

## Back on the main project computer

Copy the JSON to the main project's `verification/paper-checks.json` (preserve any
older report under a different name), or leave it elsewhere and give its path.
In **Ubuntu/Linux Bash at PACKAGE_ROOT**, where `confirm.py` lives:

```bash
python3 confirm.py --wolfram "/actual/path/paper-checks.json" --check
```

The modular reporting update must be installed on that computer. The old v004
checker expects the old, manuscript-coupled report format. The updated checker
accepts both schema-2 component reports and **explicitly identified** earlier
v003/v004 reports for the same mathematical checks. An earlier JSON is not edited;
its use is marked `APPROVED_LEGACY_EQUIVALENCE`, with its original release and
manuscript metadata retained. Unknown programs, missing IDs, duplicates, failures,
and partial runs remain unacceptable.

## Section guide

| Section | Checks | Task |
|---|---:|---|
| constants | 16 | Radical identities, normalization, density, rounding, correction constants. |
| triangle-bounds | 45 | Side/radius area inequalities and triangle-formula fixtures. |
| obtuse-endpoints | 27 | Cyclic/right quadrilateral endpoints, certified cells, trapezoid derivatives. |
| gamma | 35 | Exact shear-area identity, derivatives, symmetry, pinwheel slice identities. |
| contact-identities | 8 | Slider/midpoint/reflection identities and independent area formulas. |
| diagnostics | 30 | Seeded determinant and rigid-motion examples; not continuum proofs. |

No formulas, thresholds, seeds, default precision or test conditions changed in
this reporting revision. The mathematical block is byte-identical to v004.

Wolfram interfaces used: `Get`, `$InputFileName`, `FileHash`, `SystemDialogInput`,
`TimeConstrained`, and JSON `Import`/`Export` with the explicit `RawJSON` format.
