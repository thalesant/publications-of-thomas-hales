# Confirmation of independent execution records

The required set is **77 OCaml stages** (73 calculation/auxiliary jobs and four
contract-test stages) plus **161 Wolfram checks**. Four optional OCaml diagnostics
do not replace required stages. The confirmation is a source-specific execution
record, not a formal proof certificate or an authenticated human signature.

## Workflow and context

The OCaml code runs in **Ubuntu/Linux Bash**, including WSL, at **PACKAGE_ROOT**:
the folder with `run.py`, `registry.json` and `ocaml/`. It produces files in `runs/`.
The Mathematica checks can run anywhere on any machine with a Wolfram kernel.
Only the independent `mathematica/` folder is needed there; see its
[guide](../mathematica/README.md). Copy just its exported JSON back.

With a complete JSON at `verification/paper-checks.json`, use **Bash at PACKAGE_ROOT**:

```bash
python3 confirm.py --check
```

Or import a report from an explicitly named location:

```bash
python3 confirm.py --wolfram "/actual/path/paper-checks.json" --check
```

No calculation is launched. A validated copy is stored as `verification/wolfram-report.json`
without editing its content. `--check` succeeds when the OCaml and Wolfram components
are complete and the separate manuscript association matches. Expected output:

```text
OCaml: COMPLETE (77/77)
Wolfram: PASS
Manuscript association: MATCH
```

A report from the exact earlier v003/v004 suite is supported through the checked
compatibility record, with evidence mode `APPROVED_LEGACY_EQUIVALENCE`. This is reuse
of an earlier execution of unchanged mathematical checks, not a new execution.
Unknown versions or partial reports are rejected. Keep the original JSON unchanged.

## What is validated

**OCaml:** the numerical source component; source/environment fingerprint; selected
job set; process exit; job and stack markers; log digest; and absence of recorded
errors. Changed numerical sources require new execution. A known v004 inventory is
accepted only when the entire current numerical component still matches. Every old
record is validated with its original fingerprint. Different environments cannot
fill one another's missing jobs. A later failure supersedes an earlier pass.

**Wolfram:** three component-local source hashes; all 161 unique expected check IDs;
all six sections in order; every individual `Passed` result; and summary counts.
It never compares a remote-machine manuscript file. Earlier supported source
identities are explicitly listed, not inferred from a filename or a "PASS" string.

**Assembly:** `verification/association.json` identifies the article, label map and
claim map that the release associates with these components. It is checked here,
not on the Mathematica computer. A manuscript edit affects this association, not
the underlying validity of unchanged numerical results. Updating the association
for a mathematically changed paper requires review of that correspondence.

The source manifest `MANIFEST.json` and `SHA256SUMS` cover fixed distributed files;
`python3 scripts/check_release.py` checks those. Mutable logs and confirmation
outputs are checked by `confirm.py`. Neither tool silently rewrites source hashes
to conceal a mismatch.

## Existing v004 runs and resumption

Install the coordinated reporting update only after active OCaml processes have
finished. Their complete logs remain valid. For a partial run, rebuild the mutable
checkpoint cache from verified old logs using:

```bash
python3 confirm.py --prepare-resume
```

Then invoke `run.py` as before. This does not edit historical reports or run any
mathematical work; it prevents unchanged completed jobs from being repeated merely
because the former inventory included unrelated files. See [MODULARITY.md](MODULARITY.md)
for the exact acceptance and dependency boundaries.

## Produce a verified archive

After successful confirmation, **Bash at PACKAGE_ROOT**:

```bash
python3 confirm.py --bundle ../pentagon_verified.zip
```

Use an unused name. The bundle contains the current manuscript/code/docs, unchanged
Wolfram report, compatibility/association records, and contributing original run
folders under `verification/run-records/`. Old failed/unrelated runs and temporary
build files are omitted. After relocating the archive, `python3 confirm.py --check`
revalidates its local files rather than trusting original absolute paths.

Preserve actual toolchain metadata in execution evidence and review it before
public distribution. Never manually change report `Passed` fields, hashes,
versions or timestamps. The mathematical conclusions still rely on the geometric
reductions and documented interval contracts; these checks do not mechanically
prove the article's prose.
