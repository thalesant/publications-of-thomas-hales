# Prior execution evidence

This directory preserves verified, source-specific executions preceding the integrated
v003 distribution. The enlarged-domain/enclosure jobs and the four squeezing-sign
calculations returned successfully, with the supplied log and source checksums verified.
`prior-executions.json` records their identities and outcomes. Copies of the log text
have personal absolute path/launch lines removed; original and distributed log hashes
are distinguished in the metadata. These are historical execution records, not inputs
or certificates consumed by the mathematical algorithms.

The final numerical module tokens are compared with the tested snapshots in
`../provenance/mathematical-source-equivalence.json`. Changes to public comments do
not change those tokens. The integrated loader, selection and reporting nevertheless
receive their own source identity. Therefore no prior log here is silently imported
as a v003 completion. Run the distributed commands and use `confirm.py` to construct
a complete current-source record.

`original-baseline-timings.json` contains measured examples from the earlier full
MITM baseline. They help plan computation; they are not promises of runtime or
assertions that a newer domain was tested by an older run.
