# Packings of regular pentagons — verification companion

**Distribution:** code v003 · **manuscript:** `paper/pentagon_v005.tex` · 6 November 2026.

This repository accompanies the proof of the density bound
\((5-\sqrt5)/3\) for congruent regular pentagons. The paper reduces the global
packing problem to explicit finite-dimensional exclusions. OCaml executes those
interval searches; Wolfram Language checks the paper’s exact identities, small
numerical bounds, and selected diagnostic examples. These are complementary tasks.

**Start here as a new reader:** open [the paper](paper/pentagon_v005.pdf), then
[the mathematical code commentary](docs/code_commentary.pdf). To locate a
particular lemma, open [the searchable calculation index](docs/index.html).
A [Markdown version](docs/CALCULATIONS.md) is available for browsing on GitHub.
It connects printed lemma/section numbers, TeX labels, and seven-letter source
identifiers to the assumptions, functions, and commands. The index works offline.

## Run the verification

The following commands are for **Bash on Linux**, including **Ubuntu under Windows
Subsystem for Linux (WSL 2)**. They are not PowerShell, an OCaml prompt, or a
Mathematica input cell. First extract the ZIP, then open a terminal in the folder
containing `run.py`, `registry.json`, `ocaml/`, and this README. That folder is called
**PACKAGE_ROOT** throughout these instructions. It can have any name and location.

Install the compiler and libraries once using [INSTALL.md](docs/INSTALL.md).
An existing `pentagon-4.14.4` opam switch can be reused; the runner never upgrades it.
Then, in Bash **at PACKAGE_ROOT**, run:

```bash
python3 run.py --all --diagnostics
```

This performs 70 proof jobs, three required test stages, and four explicitly
optional diagnostics. Test stages run first; proof jobs cannot start after a
failed selected test. Up to four independent calculations run concurrently.
Results and the report ZIP are saved under `PACKAGE_ROOT/runs/`.

**On WSL**, the following equivalent command also copies the report to your Windows
Downloads folder. It discovers that folder through Windows rather than assuming
an account name or drive layout:

```bash
python3 run.py --all --diagnostics --copy-report windows-downloads
```

A report is created for a successful or unsuccessful batch. The full original stays
in `runs/` even if the optional copy is unavailable. Keep the terminal open and
prevent the operating system from sleeping or restarting during a long calculation.

Run the supplementary Wolfram checks separately, using the command-line or notebook
instructions in [mathematica/README.md](mathematica/README.md). Each of the 161 checks
has an explicit mathematical assertion and explanation in
[the Wolfram check catalogue](docs/WOLFRAM_CHECKS.md).

## Record and publish completion

There is no manually maintained “all passed” sentence. After a run, the controller
updates `verification/CONFIRMATION.md` and `verification/status.json` from the actual
logs. After the Wolfram suite exports `verification/paper-checks.json`, import it
in Bash at PACKAGE_ROOT:

```bash
python3 confirm.py --wolfram verification/paper-checks.json --check
```

This command succeeds only when **all required OCaml jobs** and **all 161 Wolfram
checks** have matching complete records for these exact source files. It checks
log digests and exit markers and does not combine different OCaml environments.
To create a new distribution ZIP containing the resulting confirmation and its
supporting execution records, run, at PACKAGE_ROOT:

```bash
python3 confirm.py --bundle ../pentagon_verified.zip
```

The destination is an example output path relative to PACKAGE_ROOT; select another
unused name as needed. It never overwrites an existing archive. After extraction
elsewhere, `python3 confirm.py --check` revalidates the packaged records. See
[VERIFICATION.md](docs/VERIFICATION.md) for the precise meaning of completion.

## Context when returning later

The **code version and paper version are separate**. This folder is the complete
code-v003 distribution; its paper is v005. `run.py` is the ordinary runner.
Earlier standalone batch/supplement launchers are not required. The default command
`python3 run.py` runs short contract tests, not the long proof suite.
`--list` previews a selection without launching anything. Matching successes are
reused when you repeat a command. Checkpoints are between jobs, not inside an
interrupted subdivision.

| Goal | Read |
|---|---|
| Install tools on Linux/WSL | [Installation](docs/INSTALL.md) |
| Select a job, lemma, or section; manage resources | [Running calculations](docs/RUNNING.md) |
| Understand geometry, intervals, and pruning | [Code commentary](docs/code_commentary.pdf) |
| Understand function tests and diagnostics | [Testing](docs/TESTING.md) |
| Understand every Wolfram assertion | [Check catalogue](docs/WOLFRAM_CHECKS.md) |
| Reproduce figures or build the manuscript | [Figures](figures/README.md), [paper](paper/README.md) |
| Archive libraries and reproduce the environment | [Environment preservation](environment/README.md) |
| Interpret evidence and confirmation | [Method and assurance](docs/METHOD_AND_ASSURANCE.md) |

No source file requires knowledge of a private discussion, a personal directory
layout, or unpublished handwritten notes. Dependency licenses and attributions are
listed in [LICENSE.md](LICENSE.md).

## Check the downloaded files

At PACKAGE_ROOT in Linux/Ubuntu Bash, `sha256sum -c SHA256SUMS` checks the
fixed distributed files. `MANIFEST.json` records the same file identities.
Generated run folders and generated confirmation/Wolfram reports are excluded
from this delivery manifest; `confirm.py` checks their own source-specific
identities separately. Rebuilding PDFs or editing sources changes their checksums.
