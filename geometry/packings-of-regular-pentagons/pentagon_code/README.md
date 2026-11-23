# Packings of regular pentagons — verification project

**Current article:** [manuscript v008](paper/pentagon_v008.pdf).  
**Computational distribution:** code v005 (`pentagon_code_v005`).

This repository contains the paper, its interval-arithmetic calculations, supporting
Wolfram checks, figure sources, and mathematical documentation. All OCaml calculations,
including the pin-T estimates, the LJ1 face derivative, and the geometric
meet-in-the-middle control, use **one runner and one confirmation system**.
There is no separate supplement to install or run.

## Context for a first visit or a return to the project

The paper reduces the packing problem to geometric inequalities. OCaml interval
searches verify specified parameter domains; Mathematica checks exact identities,
small bounds, and explicitly classified numerical examples. The two have different
mathematical roles. A run's completion is recorded in
[`verification/CONFIRMATION.md`](verification/CONFIRMATION.md); it is not inferred
from the mere presence of this repository or from a previous version's results.

Start by reading the paper, then use the [paper-to-code index](docs/index.html)
(offline HTML) or [Markdown index](docs/CALCULATIONS.md) to find a lemma, section,
source label, seven-letter computation identifier, or named job. The
[mathematical commentary](docs/code_commentary.pdf) explains how the geometry
becomes code. The [2016-to-v007 table](docs/pentagon_changes_2016v2_to_v007.md)
locates changes for readers familiar with the original article.

## One complete OCaml run

**Shell:** Linux Bash, including Ubuntu Bash in WSL 2 on Windows. These are not
PowerShell, Python-prompt, or OCaml-prompt commands. **Working directory:** the
extracted repository folder containing `run.py`, `registry.json`, and `ocaml/`.
We call this folder **PACKAGE_ROOT**. Its absolute location is your choice.

First enter that folder. Replace the following placeholder, rather than typing it
literally:

```bash
cd "/actual/path/to/your/extracted/project"
ls run.py registry.json ocaml/loader.ml
```

A new installation needs the tools in [INSTALL.md](docs/INSTALL.md). An existing
OCaml `pentagon-4.14.4` switch with the CRlibm dependencies can be reused; no upgrade
is requested. From PACKAGE_ROOT in the same Bash terminal:

```bash
python3 scripts/check_release.py
python3 run.py --all --diagnostics
```

**Windows/WSL convenience:** the following is the same complete run, with a copy of
its single report ZIP sent to the Windows Downloads folder automatically:

```bash
python3 run.py --all --diagnostics --copy-report windows-downloads
```

Choose one of these two run commands, not both. Programs run from this repository;
Downloads is only an optional output-copy destination.

There are **77 required stages: 73 calculation/auxiliary jobs and four test stages**.
`--diagnostics` adds four optional historical or consistency checks, for **81 stages**.
The four short prerequisites run first. Eligible calculations then start in
**descending recorded runtime order**, beginning with `mitm_calc_pent3_6D_postcluster`.
A finite list of known runtimes is a scheduling hint, not a time or proof bound.

The default `--jobs auto` chooses up to **eight independent processes**, subject to
CPU availability and a RAM budget of 4 GiB per process plus 8 GiB reserve. A system
with 24 available processing units and 31 GiB visible RAM therefore selects **five**
workers; live memory checks may admit fewer. Swap is not counted as available RAM.
An explicit `--jobs N` changes the worker ceiling, not the memory safety checks.
The longest single calculation remains serial internally.

Results and checkpoints are written only under `runs/`; no previous-run checkpoint
is supplied in this distribution. A repeated command resumes matching completed
jobs. First Ctrl+C stops new starts and lets active jobs finish; a second cancels
them. Interrupted jobs restart at their beginning. Keep the machine awake and the
terminal open. See [RUNNING.md](docs/RUNNING.md) for limits, selection, and reports.

## Mathematica and the combined confirmation

Read [mathematica/README.md](mathematica/README.md). It gives a notebook file-dialog
route that does not depend on the notebook's directory, plus a command-line route.
The complete 161-check Mathematica report from the preceding release has been carried forward byte for byte. The component and required checks are unchanged, and the confirmation program validates the original report. A fresh Mathematica run is optional.
Every check is explained in [WOLFRAM_CHECKS.md](docs/WOLFRAM_CHECKS.md).

Back in **Ubuntu/Linux Bash at PACKAGE_ROOT**, after the OCaml run finishes:

```bash
python3 confirm.py --check
python3 confirm.py --bundle ../pentagon_verified.zip
```

The checker automatically validates/imports `verification/paper-checks.json`.
Use `--wolfram /actual/path/report.json` only for a report stored elsewhere.
These commands do **not** launch calculations. The bundle command refuses
incomplete or mismatched records and refuses to overwrite an existing ZIP.
Choose a new output name for a later bundle.

A complete confirmation reads **OCaml COMPLETE (77/77)**, **Wolfram PASS**, and **Manuscript association MATCH**. The association is checked on this project computer, not while running Mathematica.
The verified archive contains the matching logs and can be moved and checked by
another reader. See [VERIFICATION.md](docs/VERIFICATION.md) for the exact checks.

## Directory map

| Location | Purpose |
|---|---|
| `paper/` | The current v008 source, PDF, bibliography, compiled label map, and build driver. No older manuscript copies. |
| `ocaml/` | The production geometry, interval adapter, search engines, extra contact bounds, loader, and job dispatch. |
| `tests/` | OCaml contract/positive-control checks, Python controller tests, and reference fixtures. |
| `mathematica/` | The self-contained Wolfram checking package and its described check catalogue. |
| `scripts/`, `run.py`, `confirm.py` | Common execution, resource control, documentation generation, and confirmation. |
| `registry.json` | Complete job list, source calls, paper locators, and scheduling estimates. |
| `docs/` | Current indices, commentary, guides, and the compact 2016-to-v007 change table. |
| `figures/` | Figure constructions and a gallery for the current paper. |
| `environment/` | Installation, pinned public dependency identities, and environment archival. |
| `evidence/` | Source-identified historical timing summaries, used for scheduling, never as new passes. |
| `provenance/` | File-level integration history, mathematical-source preservation, and preparation checks. |
| `runs/` | New local executions, logs, checkpoints, and reports. |
| `verification/` | Generated current-source OCaml/Wolfram confirmation and exported evidence. |

The manuscript and mathematical implementation bodies are not changed by run
scheduling. The release history is in [CHANGELOG.md](CHANGELOG.md), and exact
unchanged/moved/changed paths are recorded in [the v005 file comparison](provenance/v005-file-changes.json).
License scopes and third-party notices are in [LICENSE.md](LICENSE.md).

## Changes from v004.1

Manuscript v008 treats limiting contacts, gives the fixed-edge reduction and uses Lemma 5.10 at a tie in squeezing. The pinwheel jobs now cover the full angle triangle. Two elementary side bounds are checked at their points of use. The original 77 required stages and four diagnostics are retained. The [release history](CHANGELOG.md) identifies the mathematical changes. The OCaml status is pending a run on these sources.
