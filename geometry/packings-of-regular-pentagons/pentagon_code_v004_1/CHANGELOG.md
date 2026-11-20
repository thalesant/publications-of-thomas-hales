# Manuscript v008 and code v005 — 19 November 2026

Parent: `pentagon_code_v004_1` at Git commit `29250f012a54cf659010291cef8f907438f4d392`. The package uses the same layout, job names, and run and confirmation commands.

- The pinwheel calculations for Lemmas 4.9, 4.11 and 5.4 retain the full angle domain. Earlier OCaml executions are not passes on v005. The two added side-bound assertions accompany the existing isosceles and two-triangle calculations.
- Section 3 treats limiting contacts. Section 6 gives the signed condition in stage 2, the fixed-edge peripheral reduction, and the outgoing motion at a vertex in stage 3. The existing Lemma 5.10 calculation covers a tie on the subcritical side. Its central triangle may be supercritical. The appendix gives the corresponding reductions and parameter cutoffs.
- The Mathematica component and its original 161-check execution report are preserved byte for byte. Confirmation checks the new manuscript association separately. See `verification/CONFIRMATION.md` for the actual run status.
- The paper, bibliography outputs, gallery and offline HTML indices are included in the archive. File changes relative to the parent distribution are listed in `provenance/v005-file-changes.json`. Earlier provenance records describe their original releases.

# Modular reporting revision 1 (code v004.1)

- Made `mathematica/` independently deployable: only three runtime files are read.
- Removed manuscript and parent-project hashing from the Wolfram runtime.
- Made output selection explicit; no implicit parent `verification/` path.
- Separated numerical OCaml source identity from Mathematica, manuscript and publishing metadata.
- Added explicit checked compatibility for original v004 OCaml records and v003/v004 Wolfram reports; original records remain unchanged.
- Added assembly-time `verification/association.json` and negative/relocation tests.
- Kept every OCaml numerical file, registry, driver, mathematical Wolfram condition and manuscript unchanged.

# Changelog

## Code v004 / manuscript v007 — 14 November 2026

- One current `paper/` directory: the approved v007 artifacts replace v005; no
  nested version folders or copies of the obsolete local-bound proof.
- Integrate the executed pin-T bounds and LJ1 face derivative in `ocaml/review_jobs.ml`,
  and the geometric MITM control in `tests/ocaml/positive_control.ml`. One registry,
  worker and confirmation scope: 77 required stages, plus four optional diagnostics.
- Preserve the original numerical module bodies, interval adapter, domains, and
  target inequalities. Loading/dispatch and documentation are updated explicitly.
- Run short tests first, then schedule the longest recorded jobs first. Automatic
  concurrency is up to eight with CPU/RAM limits and conservative live admission.
- Load/install `interval_crlibm` directly rather than the unused Intel meta-backend.
  Existing working switches remain usable; none is upgraded by the runner.
- Automatically validate/import the standard Mathematica report at confirmation.
- Flatten documentation, regenerate all maps/commentary for v007, and remove old
  patch launchers, source snapshots, duplicated records, and the withdrawn figure.
- Ship no run checkpoints. Current-source completion is generated after the fresh
  full run; historical measurements determine scheduling only.

# Distribution history

## Code v003 / manuscript v005 — 6 November 2026

- Publish the cleaned v004g manuscript as v005, preserving all 169 printed label
  numbers; remove editorial review material and add source-only navigation codes.
- Integrate the successfully executed four-case squeezing-sign implementation and
  its 71 contract checks, without changing its numerical expressions.
- Retain the tested v002 mathematical modules and both test repairs. The revised
  exceptional-peripheral and boundary domains and contact-enclosure corrections
  are included; token comparisons against executed source snapshots are recorded.
- Give each calculation printed-paper references, stable labels and comment codes;
  distinguish proof searches, function tests and optional diagnostics.
- Document all 161 Wolfram checks and make loading/export independent of a notebook
  working directory. Mathematical test conditions are unchanged.
- Add automatic source-specific completion validation and verified ZIP export.
- Replace development-oriented instructions with first-reader installation, execution,
  resource, result and preservation guides. No personal directory is embedded.

## Code v002

Separated mathematical definitions from long calculations, introduced the shared
runner and contract suite, enlarged the C013/C014 terminal domains, and retained
all 25 MITM entry points. Earlier source hashes and verified execution records are
preserved in provenance/ and evidence/ rather than treated as new v003 results.
