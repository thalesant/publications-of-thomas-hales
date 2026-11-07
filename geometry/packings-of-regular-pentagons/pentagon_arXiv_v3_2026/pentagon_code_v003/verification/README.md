# Generated completion record

The numerical algorithms do not read this directory as proof input. The controller
and `confirm.py` write the current source-specific record here after inspecting actual
run logs. `CONFIRMATION.md` is the human-readable summary; `status.json` is the full
machine-readable inventory. The Wolfram export is imported as `wolfram-report.json`.

At PACKAGE_ROOT in Linux/Ubuntu-WSL Bash:

    python3 run.py --all --diagnostics
    python3 confirm.py --wolfram verification/paper-checks.json --check

The second command follows the Wolfram execution/export described in
`../mathematica/README.md`. It must succeed before `confirm.py --bundle OUTPUT.zip`
will make a verified distribution. Neither a missing run nor an old source’s pass
is treated as a current confirmation. See `../docs/VERIFICATION.md` for details.
