# Local executions

`python3 run.py ...` creates timestamped directories, checkpoints, and one report ZIP
here. The distribution intentionally contains no past runs or successful checkpoints.
Run the complete suite from the package root; see ../docs/RUNNING.md.

Do not delete this directory during an active run. First Ctrl+C drains active work;
a second cancels it. Repeat the same command to resume completed matching jobs.
The verified bundle exports contributing records under verification/run-records/.
