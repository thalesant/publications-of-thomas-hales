# Component boundaries and report portability

## The three independent responsibilities

| Component | Inputs | Output | Explicitly not required |
|---|---|---|---|
| Mathematica checks | The three declared runtime files in `mathematica/` and a Wolfram kernel | A schema-2 JSON execution report, saved at the chosen path | Manuscript, PDF, label map, OCaml, Python, project root |
| OCaml calculations | `registry.json`, `run.py`, `scripts/driver.py`, `scripts/worker.ml`, `scripts/report_paths.py`, `ocaml/*.ml`, `tests/ocaml/*.ml`, and the recorded toolchain | Logs, source/environment fingerprint, result rows | Mathematica files or manuscript as mathematical inputs |
| Project assembly / confirmation | Both reports, declared source identities, and `verification/association.json` | `verification/status.json`, `CONFIRMATION.md`, optional verified ZIP | Re-executing either component merely to copy a report |

The `.tex` file is not parsed or used by either numerical calculation. It is
identified at **assembly time** so a published archive says which article it
accompanies. The association does not prove that arbitrary new prose follows from
unchanged calculations. A mathematical manuscript change still needs mathematical
review, and the association manifest must then be updated deliberately.

The full project keeps its established directories. No supplement directory,
second job registry, or alternative long-calculation launcher is introduced.
The Mathematica folder may be distributed by itself; the documentation in it is
self-contained. `run.py` remains the single OCaml entry point.

## Identity is not the same as execution

The OCaml computation inventory no longer includes Mathematica, manuscript,
documentation-builder, release-name or confirmation-checker files. Therefore a
Wolfram-reporting edit or a corrected manuscript typo cannot invalidate an unchanged
OCaml computation. Changes to the numerical modules, adapter, production worker,
job registry, driver, selected source set, or environment still invalidate it.

`provenance/report-compatibility.json` records one narrow transition: the exact
source inventory shipped in v004 is recognized, and all current numerical inputs
must still match it. Every inherited log is checked using its **original**
source/environment fingerprint, exit status, markers, and digest. Original log,
result, inventory and timing files are never rewritten. Only same-component,
same-environment records can be combined. This is not arbitrary acceptance of
prior releases.

For Wolfram, both v003 and v004 contain the same mathematical block. The
compatibility record names their exact four-file test programs and the exact
current component; it records the unchanged mathematical block. It permits a
complete earlier report to establish completion of those unchanged tests. It does
not claim the new reporting wrapper was executed at that earlier time.

An edited old `SourceSHA256` is never required. A false or missing check, unknown
program hash, duplicate ID, partial section set, or bad count is rejected even
when all mathematical formulas are otherwise familiar.

## Current report format

Schema-2 Wolfram reports use:

```text
ReportSchema: 2
Component: PentagonChecks
SuiteVersion: 1
IdentityScope: component-local-files
SourceSHA256: {PentagonChecks.wl: ..., checks_catalog.json: ...,
               expected_checks.json: ...}
```

They also record kernel, options, UTC time, individual results, and summaries.
There are no absolute input paths and no manuscript hash. Output paths are chosen
by the user and do not affect the computation's identity.

The combined status records separate `ocaml`, `wolfram`, and `association` sections.
Wolfram evidence is `CURRENT_COMPONENT` or `APPROVED_LEGACY_EQUIVALENCE`. The latter
retains the original release/manuscript tags; a manuscript tag is historical metadata,
not a current dependency. Required OCaml jobs remain **77**, Wolfram checks **161**.

## Running v005 after v004.1

Extract v005 in its own directory. The revised pinwheel domain and the two
additional assertions require fresh OCaml execution. From the directory
containing run.py, run the following commands in Linux or Ubuntu Bash.

```bash
python3 run.py --all --diagnostics
python3 confirm.py --check
```

The supplied Mathematica report retains its original execution identity.
The package checks that report and the v008 manuscript association separately.

## Testing boundaries

Python tests cover a copied standalone folder, relocated reports, old/new schemas,
source changes, forged summaries, incomplete check sets, missing assembly data,
legacy log integrity, record bundling, and the updater's refusal cases. These are
controller/contract tests, not executions of the Wolfram mathematical suite. The
new Wolfram wrapper still requires a real-kernel run to claim its execution.
