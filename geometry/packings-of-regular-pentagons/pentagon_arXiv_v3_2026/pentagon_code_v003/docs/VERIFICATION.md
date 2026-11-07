# Source-specific confirmation of completion

## What is being confirmed?

The required OCaml set has **70 proof jobs and three test stages**: `unit`,
`extended`, and `squeeze_sign_tests`. Four optional diagnostics are not theorem
premises. The supplementary Wolfram set has **161 named checks**, all six sections.
A combined confirmation requires both complete sets. The OCaml and Wolfram roles
remain distinct even though one document records both.

`confirm.py` reads the logs; it does not run calculations. It regenerates
`verification/status.json` (machine-readable) and `verification/CONFIRMATION.md`
(reader-readable). Do not edit these files to mark a test passed. The record is
an execution summary with consistency checks, not a formally verified certificate
or a cryptographic signature attesting who ran the code.

## Steps, with context

**In Linux/Ubuntu-WSL Bash, at the extracted package root containing `run.py`:**

```bash
python3 run.py --all --diagnostics
```

On WSL append `--copy-report windows-downloads` for a convenient Windows copy.
Repeated commands reuse matching completed jobs. The controller refreshes the
confirmation after each batch, including partial runs. Until all required records
exist, its generated status gives the actual count rather than claiming completion.

**In Wolfram Language**, follow `mathematica/README.md` to run every section and
export `verification/paper-checks.json`. The export records SHA-256 identities of
the suite, metadata, manuscript, and label map.

**Back in Bash at the package root:**

```bash
python3 confirm.py --wolfram verification/paper-checks.json --check
```

The supplied relative filename is the standard output location. A report exported
elsewhere can instead be passed by its actual path. The importer rejects missing
checks, duplicate IDs, partial-section runs, false results, and source mismatches.
A kernel already used for another paper should be restarted or cleared before
loading this package; its functions use their own package context.

## Checks performed on the records

For OCaml, the verifier matches the complete source inventory, reconstructs the
source/environment fingerprint, checks each saved log’s SHA-256, requires process
exit 0, and requires both the exact job-completion line and the retained bytecode
stack marker. It rejects explicit test or runtime errors even if a success marker
appeared earlier. Different runtime fingerprints are not combined to fill missing
jobs. The latest valid record for a job in a particular environment takes precedence.

For Wolfram, the named check set must equal the complete expected set, each Boolean
result must be `True`, all summary counts must agree, and the recorded source hashes
must match the present files. An old hand-reported success is not imported as a
machine-checked record for changed sources.

The prior logs under `evidence/` document tested implementations and measured costs.
They are never used to fill a missing job in the current release confirmation.
This permits publication of clear, stable mathematical documentation while the
source-specific execution status is updated automatically by actual runs.

## Export a distribution containing completion evidence

After the combined check succeeds, in Bash at the package root:

```bash
python3 confirm.py --bundle ../pentagon_verified.zip
```

Choose an unused output filename. The bundle includes the paper, code, documentation,
confirmation and the contributing run folders; it omits unrelated failed-run history
and transient build files. After moving or extracting the resulting ZIP, run:

```bash
python3 confirm.py --check
```

The reader need not have the original computer or its absolute folder paths to
validate the packaged logs against the packaged sources. Reproducing the calculation
itself additionally requires the compiler/libraries; see environment/README.md.

## Limits of this record

A complete execution establishes that the program exhausted its encoded domains
under the documented enclosure, coordinate, and arithmetic contracts. Unit tests
are finite evidence for implementation behavior; numerical samples are not uniform
inequality proofs. The paper supplies the geometric reductions. The commentary
states the pruning invariant and the arithmetic assumptions. This division is part
of the method, not an invitation to infer a missing proof from a green status word.

Run reports retain actual local toolchain and filesystem paths as execution provenance.
The packaged confirmation does not require those directories to exist on the reader’s
machine. Review report metadata before public redistribution; changing hashed records
invalidates their integrity checks. No passwords or unrelated user documents are collected.
