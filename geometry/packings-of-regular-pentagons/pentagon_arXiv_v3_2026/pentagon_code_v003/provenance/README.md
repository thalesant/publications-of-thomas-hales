# Source identities and construction record

This directory records how the distribution relates to its supplied inputs without
requiring readers to reconstruct a private conversation. The mathematical sources
have exact identities; prior execution records apply only to those identities.

- `input-identities.json`: authoritative manuscript, original release and execution
  report archive hashes; stable seven-letter navigation identifiers.
- `paper-changes.md` and `label-comparison.json`: manuscript cleanup scope and printed
  numbering preservation.
- `tested-source-hashes.json` and `mathematical-source-equivalence.json`: tested
  numerical file identities and noncomment-token equality of the integrated versions.
- `wolfram-condition-preservation.json`: exact check-condition preservation while
  adding human-readable metadata and portable report export.
- `source_baseline.json`, `original-file-inventory.json`, `removed_or_moved.json`:
  historical source inventory, retained notices and disposition of old development
  files. These records do not reinstate obsolete executables as dependencies.

The current distribution manifest identifies its files. The dynamic verification
record is separate and is regenerated from actual executions; it is not populated
from these provenance statements alone.
