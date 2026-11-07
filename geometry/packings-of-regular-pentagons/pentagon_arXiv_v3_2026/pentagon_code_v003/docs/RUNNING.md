# Running the interval calculations

## Context for a first-time or returning reader

**Package:** code v003, containing manuscript v005. **Shell:** Bash on Linux or
Ubuntu under WSL 2. **Working directory:** the extracted folder containing `run.py`,
`registry.json`, `ocaml/`, and `tests/`. We call it PACKAGE_ROOT. Commands below
are issued there, not in `ocaml/`, `docs/`, an OCaml interactive session, or PowerShell.

Find the extracted folder using your file manager. In Bash, change to its actual
Linux path; the following path is a placeholder, not a directory to create:

```bash
cd "/actual/path/to/the/extracted/package"
pwd
ls run.py registry.json ocaml/loader.ml
```

On WSL, a Windows drive such as `D:\Research\Pentagon` is normally visible as
`/mnt/d/Research/Pentagon`. A Linux home folder is accessible from File Explorer
via WSL’s Linux view, or by running `explorer.exe .` in that folder. Prefer the
Linux filesystem for computation and retain only a report copy on the Windows side.
All paths in the code are resolved from the script/package, not a fixed user home.

## Preview before execution

At PACKAGE_ROOT, in Bash:

```bash
python3 run.py --all --list
python3 run.py --claim 6.5 --list
```

The first lists all required proof and test stages; the second shows the direct
calculations for Lemma 6.5 (squeezing). A printed lemma number is an alias for its
label. Section selection uses the distinct `--section` option. The preview writes
no results and launches no OCaml process.

## Useful selections

These are alternative commands, not a sequence that must all be executed.

| Purpose | Command in Bash at PACKAGE_ROOT |
|---|---|
| Short function checks | `python3 run.py --tests` |
| Include seeded generated tests | `python3 run.py --tests --extended` |
| One named calculation | `python3 run.py --job mitm_precluster6_case1` |
| All direct calculations for a paper claim | `python3 run.py --claim calc:pseudo-area3` |
| The same claim by source ID | `python3 run.py --claim JQMRXTH` |
| The same claim by printed lemma number | `python3 run.py --claim 5.5` |
| All calculations associated with a paper section | `python3 run.py --section 5` |
| Squeezing subsection | `python3 run.py --section 6.3` |
| All required OCaml proof jobs and tests | `python3 run.py --all` |
| Include optional consistency/historical diagnostics | `python3 run.py --all --diagnostics` |

`--job`, `--claim`, and `--section` can be repeated. Selection is a union; a job is
not duplicated. Claim selection includes direct computational inputs and prerequisite
function tests, **not** every earlier lemma in its transitive mathematical proof.
Use `--all` for the release-wide confirmation. Unknown or empty selections are errors.
The calculation index states the domain and target for every association.

`--changed` is retained for comparing the domain/enclosure revisions with the archived
baseline. It selects 17 affected proof jobs and their tests; it is not a substitute
for the complete `--all` confirmation.

## Environment and resources

The runner invokes `opam exec` with switch `pentagon-4.14.4`. Change the switch
explicitly with `--switch NAME`; no compiler or package is installed automatically.
The proof runs as OCaml bytecode, with the original stack setting of 16,777,216
machine words. This setting is checked before and after every stage.

The defaults are four independent processes, at most 4 GiB address space per process,
an 8 GiB admission reserve, and 72 hours wall time per job. Each process has its own
MITM hash tables. The controller accounts for future growth of active processes
before admitting another. Swap is not counted as available admission memory.
These limits are operational safeguards, not mathematical tolerances. They cannot
turn an unresolved calculation into a successful exclusion.

For an 8 GiB Linux allocation, a conservative serial command is:

```bash
python3 run.py --all --jobs 1 --memory-gib 4 --reserve-gib 2
```

The controller refuses to launch if the actual memory headroom does not satisfy the
chosen budget. Four 4 GiB workers plus the default 8 GiB reserve require at least
24 GiB of usable headroom at admission; a 32 GiB Linux/WSL allocation is comfortable.
A 24-core processor does not justify 24 simultaneous 2–3 GiB hash-table calculations.

`--timeout 0` explicitly disables the wall-time cap. `--timeout 259200` specifies
72 hours. A timeout, stack exhaustion, memory exhaustion, or width-exhaustion error
is an incomplete computation, never a counterexample automatically and never a pass.

## Progress, stopping, and resumption

The console reports RUN/PASS/FAILED/TIMEOUT/CACHED_PASS, current worker count, and
heartbeats. Detailed compiler warnings and progress output remain in individual logs.
First Ctrl+C: stop admitting jobs and let active jobs finish. Second Ctrl+C: cancel
active jobs and save available records. Keep the terminal open. Disable automatic
sleep/restart for a long run; turning off the display is harmless.

Repeat the same command to resume. A cached success is reused only for matching
source and installed-environment fingerprints and an intact successful log.
No checkpoint exists inside a geometric subdivision. Do not edit sources, rebuild
metadata, change packages, or run another copy of the driver against the same
results directory during an active batch. `--rerun` explicitly ignores checkpoints.

## Reports and optional Windows copying

By default all output goes under `PACKAGE_ROOT/runs/`. The terminal prints the exact
report ZIP path. An output directory can be chosen explicitly with `--work`; use
that same directory with `confirm.py --work` when validating its results.

On WSL, add `--copy-report windows-downloads` to any run command to discover and use
the current Windows Downloads folder. Alternatively give an actual Linux-visible
path, for example `--copy-report "/mnt/d/Research/Reports"`. This is an output
copy destination, **not** a source-code location. Failure to make the optional copy
does not erase the original report. In Bash at PACKAGE_ROOT, `explorer.exe runs`
opens the local results through Windows Explorer.

Upload/share the entire report ZIP for diagnosis, not copied log fragments. It
contains exact commands, selected jobs, source identities, environment data, logs,
resources and summary. New reports preserve old results rather than overwriting them.

## Duration: observations, not predictions

The 2016 paper reports approximately 60 hours of serial computation on an Intel
quad-core 2.6 GHz machine with 3.76 GB memory. In the recorded 2026 baseline on an
Intel Core Ultra 9 285 under Ubuntu/WSL, the general six-dimensional three-triangle
job took about 6 h 36 min wall time; the largest observed individual resident peak
in that concurrent baseline was about 2.58 GiB. These are prior measured examples,
not bounds for another compiler, backend, machine, or revised domain. Raw timings
are in `evidence/original-baseline-timings.json` and source-specific prior reports.
