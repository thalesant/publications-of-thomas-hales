# Execution guide for this distribution

The final distribution uses a complete verification command rather than a patch
workflow. Start with [RUNNING.md](RUNNING.md) for shell and directory context, and
[VERIFICATION.md](VERIFICATION.md) for recording completion. All commands are run in
Linux/Ubuntu-WSL Bash from the extracted folder containing run.py and registry.json.

Full verification: `python3 run.py --all --diagnostics`.
On WSL: `python3 run.py --all --diagnostics --copy-report windows-downloads`.

The source-specific earlier domain/enclosure and squeezing results are preserved in
evidence/. A full run of this assembled release includes all 70 proof jobs, three
required test stages and (with --diagnostics) four optional diagnostic jobs. No old
standalone hotfix or batch-launcher file is required.

The supplementary Wolfram sequence and its mathematical check catalogue are in
[../mathematica/README.md](../mathematica/README.md). Completion is generated from
actual logs; it is not recorded by editing this guide.
