# Project assembly and generated records

- `association.json` is the fixed association between the current manuscript,
  label/claim maps and independent calculation components. It is not sent to the
  Mathematica machine and is not an input to its tests.
- `paper-checks.json` is a full report copied from wherever Mathematica was run.
- `wolfram-report.json` is an unchanged validated copy of that report.
- `status.json` and `CONFIRMATION.md` are generated from checked evidence.

In **Ubuntu/Linux Bash at PACKAGE_ROOT** (where `confirm.py` lives):

```bash
python3 confirm.py --check
python3 confirm.py --bundle ../pentagon_verified.zip
```

The standard `paper-checks.json` is imported automatically. For another location,
use `--wolfram /actual/path/report.json`. The commands do not launch mathematics.
A complete confirmation needs 77 OCaml stages, 161 Wolfram checks, and a matching
assembly association. Known v003/v004 Wolfram reports are usable without editing
or recomputing them; their legacy-equivalence status is explicit.

See `../docs/VERIFICATION.md` and `../docs/MODULARITY.md` for the validation rules.

The published v006 run is archived in `run-records/20261122T195446Z-4bfabe/`. The plan, results, original log digests, environment and all 81 job logs are included. The current assembly association identifies the v010 manuscript.
