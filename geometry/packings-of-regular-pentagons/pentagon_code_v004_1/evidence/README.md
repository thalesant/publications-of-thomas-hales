# Historical timing evidence

`timings.json` records observed wall times, log digests, and input archive identities
from successful earlier executions. It contains no personal paths or account names.
Its sole runtime role is to supply longest-first scheduling estimates via the registry.
It is not a source of cached passes and is never imported into the new confirmation.

A current-source full run produces its own logs under runs/ and its checked record
under verification/. Preserve the final verified ZIP to share those logs. Historical
archives remain external to this clean distribution rather than duplicating obsolete
sources, old manuscripts, and private machine paths here.
