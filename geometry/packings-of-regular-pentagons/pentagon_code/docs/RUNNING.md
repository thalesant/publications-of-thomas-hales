# Running the verification

## Context

Use Linux Bash or Ubuntu Bash under WSL 2. Every command in this guide is issued
at **PACKAGE_ROOT**, the extracted directory containing `run.py`, `registry.json`,
and `ocaml/loader.ml`. See the root README for entering it. No Downloads pathname
or private user directory is required. `run.py` also locates its source root from
its own path, but relative output arguments are interpreted from the calling shell.

Install the environment once as described in [INSTALL.md](INSTALL.md). A working
`pentagon-4.14.4` switch is reusable. Other named switches containing that compiler
can be selected with `--switch NAME`; a compiler change is not made automatically.

## Preview or select work

```bash
python3 run.py --all --diagnostics --list
python3 run.py --all --diagnostics
```

The first command prints the ordered plan only: it does not query opam, calculate,
or write a run. The second starts the complete run. On WSL append
`--copy-report windows-downloads` to copy its ZIP to the Windows known Downloads
folder. On Linux an explicit existing destination can be supplied instead.

Select one named job, a paper claim, or a section:

```bash
python3 run.py --job mitm_calc_pent3_6D_postcluster
python3 run.py --claim HUQEJAT
python3 run.py --claim 'Lemma 5.4'
python3 run.py --claim calc:pseudo-area
python3 run.py --section B.4.3
python3 run.py --section 6.6
```

Append `--list` to any selection to inspect it before executing. Repeat `--job`,
`--claim`, or `--section` to take a union; duplicate selections run once. The index
lists valid seven-letter identifiers and labels. A claim selection gives its direct
computations, not every earlier lemma it uses. `--all` is the complete proof-job
selection. It includes the pin-T pair exclusion and the LJ1 face calculation.
The geometric MITM control is a prerequisite test, not an exclusion theorem.

For function tests alone:

```bash
python3 run.py --tests --extended
```

Default invocation without options runs deterministic, contact-sign, and geometric
control tests, not the long proof jobs. Every mathematical calculation is preceded
by all four test stages (unit, extended, contact-sign, geometric MITM). Tests already
completed on identical sources and environment may be reused.

## Scheduling and parallelism

The default order is **longest estimated job first**, after prerequisite tests.
Times recorded in `evidence/timings.json` are copied into `registry.json` as scheduling
hints. The first proof job is `mitm_calc_pent3_6D_postcluster`; the other long MITM
searches are started before short exclusions. Jobs are independent OS processes.
Within a job, the original algorithm, operation order, domains, and thresholds are
unchanged. No individual search is internally parallelized.

The default `--jobs auto` chooses the smaller of 8, available CPUs, and the number
of full 4 GiB process budgets fitting in visible RAM after an 8 GiB reserve. Live
memory admission additionally reserves possible growth of already active children.
A 31 GiB system therefore selects five workers, not four; a 40 GiB-or-larger system
with enough available CPUs can select eight. Other applications may reduce admission.
Swap is not part of the budget. WSL/cgroup limits, rather than host marketing totals,
control the visible resources.

Explicit controls, still in Bash at PACKAGE_ROOT:

```bash
python3 run.py --all --diagnostics --jobs 6
python3 run.py --all --diagnostics --jobs 4 --reserve-gib 8
```

`--jobs N` sets only a worker ceiling; live memory checks are never bypassed. The
per-process address-space ceiling is `--memory-gib 4`, not preallocated RAM.
`--reserve-gib 8` reserves additional headroom. On a smaller machine these values
must fit before any process can start; for example one worker, 4 GiB/process and
2 GiB reserve require at least 6 GiB visible RAM and corresponding free headroom.
Do not reduce the process ceiling just to force more simultaneous memory-heavy jobs.

`--order registry` is available for reproducibility investigations; the default
longest-first order is intended to reduce elapsed time. The longest job's historical
wall time was roughly six hours; other large searches took tens of minutes to
roughly two hours. These are measurements from earlier machines/runs, not deadlines
or speedup promises. Total time also depends on memory bandwidth and contention.

## Limits, interruption, and resumption

The default `--timeout 259200` is a **72-hour wall limit per process**. `--timeout 0`
disables that limit. Neither timeout nor out-of-memory is a false mathematical
inequality; both are incomplete executions. Logs have a 64 MiB per-process cap.
The original bytecode stack setting, 16,777,216 words, is checked in every process.

Keep the terminal open and prevent sleep/restart during a long run. First Ctrl+C
stops launching new jobs and waits for active ones to finish; a second cancels them.
Rerunning the same command reuses only successful intact source/environment-matching
checkpoints. A cancelled calculation has no internal checkpoint and starts again.
`--rerun` deliberately ignores successful checkpoints; do not use it for resumption.
A new extracted release starts fresh because no checkpoints or past run folders
are shipped. Do not copy old `runs/` into it to fabricate a new confirmation.

## Output and interpretation

Each invocation creates `runs/TIMESTAMP-ID/` with logs, results, source snapshots,
selected jobs, resource settings, and the actual compiler/library fingerprints.
It also creates one report ZIP under `runs/`. Optional `--copy-report` sends an
additional copy to the chosen destination even after executed-stage failures.
The report shows PASSED/CACHED_PASS, FAILED, BLOCKED, TIMEOUT, INTERRUPTED, or NOT_RUN;
a file merely loading is never a completed calculation.

`verification/CONFIRMATION.md` is refreshed from all source-matching records in the
same environment. The 77 required stages include the three extra estimates and the
geometric control; there is no second supplementary confirmation. Mathematica has
its own matching report. See [VERIFICATION.md](VERIFICATION.md) for combining them.
