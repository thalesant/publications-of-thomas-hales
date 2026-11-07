# Preserve the numerical environment

## First installation versus exact reproduction

`install.sh` gives a version-pinned starting environment for a 64-bit Linux system.
It creates the compiler switch only if absent and never upgrades a working switch.
The normal run records the exact compiler, packages, interval files and runtime
options it actually used. The default switch name is `pentagon-4.14.4`; its name
is not itself proof of the contents.

The historical successful development installation used a locally pinned interval
checkout. A fresh installation of interval 1.6 is not claimed to have identical
bytes to that checkout. Running the source-specific suite and retaining its report
establishes the result for the installation actually used. The proof loader selects
the CRlibm backend explicitly even though the interval meta-package also installs
the Intel backend. Never substitute the graphics arithmetic or native-compiler
optimizations without a separate validation.

## Archive source, not only package names

An opam switch export records package metadata but does not preserve a local source
checkout that later disappears. Preserve the exact dependency sources, their licenses,
compiler/package export, and execution reports. `dependency-sources.json` identifies
published archives and their SHA-256 values. Store archives alongside this release
when making a long-term snapshot, subject to their license notices.

For an existing locally downloaded interval source, in **Linux/Ubuntu Bash at
PACKAGE_ROOT**, replace the placeholder by the actual checkout containing
`interval_crlibm.opam` and run:

```bash
python3 environment/freeze.py \
  --interval-source "/actual/path/to/ocaml-interval-source" \
  --switch pentagon-4.14.4 --fetch-crlibm
```

The output is a uniquely dated directory under `environment/archives/`. The source
checkout is read, not edited. The optional `--fetch-crlibm` uses opam to retrieve the
specified CRlibm source; omit it if working offline and preserve an existing archive
separately. Do not pass your project’s `ocaml/` folder: it is not the interval library.
Read the printed result and retain the entire snapshot with its manifest.

When archiving the published package source on a fresh machine, `opam source
interval.1.6 --dir=PATH` provides a checkout that can be inspected and preserved.
The exact installation procedures and target platform remain recorded with the
source; a container image alone is not a portable substitute for processor semantics.

Official package sources: https://opam.ocaml.org/packages/interval/ and
https://opam.ocaml.org/packages/crlibm/.
