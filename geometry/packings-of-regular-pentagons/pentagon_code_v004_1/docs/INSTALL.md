# Installation

## Context and supported route

The verification processes run in **64-bit x86 Linux**, including Ubuntu under
WSL 2 on an Intel or AMD Windows computer. Run the commands below in **Linux/Ubuntu
Bash**, not PowerShell and not an OCaml prompt. The published interval backend is
architecture-specific; no ARM/native-Windows arithmetic equivalence is asserted here.

Use the extracted folder containing `run.py` and `registry.json` as PACKAGE_ROOT.
For long runs, put it on the Linux filesystem rather than a network/synchronized
Windows folder when possible. Paths with spaces are supported; quote them.
No particular username or absolute folder is required.

## Existing working environment

A previously working `pentagon-4.14.4` opam switch can be used unchanged. The runner
selects it with `opam exec`, so no shell environment activation is needed. This
release still uses OCaml 4.14.4 and `Interval_crlibm.I` with the same compatibility
adapter. The definition loader directly requires the `interval_crlibm` package;
it no longer loads the optional Intel-transcendental backend through `interval.top`.

Check selection without running a proof:

```bash
opam exec --switch=pentagon-4.14.4 -- ocamlc -version
opam exec --switch=pentagon-4.14.4 -- ocamlfind query interval_crlibm
python3 run.py --all --list
```

No package upgrade should be performed merely to repeat a recorded calculation.
The runner records installed-file hashes as well as package version names.

## A new Ubuntu installation

Install Python 3 (3.10 or later), a C compiler/build tools, opam, and required
system build dependencies. For Ubuntu, in Bash with administrator privileges:

```bash
sudo apt update
sudo apt install build-essential pkg-config m4 autoconf unzip python3 opam
```

Use a supported opam release with its published security fixes. Distribution
packages can lag; follow the official opam installation instructions if the
installed version reports that an upgrade is needed. Initialize opam once:

```bash
opam init
```

At PACKAGE_ROOT, create the pinned switch:

```bash
bash environment/install.sh
```

It creates OCaml 4.14.4 and installs `interval_crlibm.1.6`, `crlibm.0.5.1`, and
`ocamlfind.1.9.8`. Their dependencies are resolved by opam and recorded on execution.
The script **does not modify a switch that already exists**. An existing incomplete
switch requires inspection rather than an automatic overwrite. A named alternative
can be created with `bash environment/install.sh NAME`, then used with
`python3 run.py --switch NAME ...`.

Only the CRlibm interval package and its base dependency are requested. The optional
`interval_intel` stubs that caused the reported GCC 15 C23-name conflict are not
needed by the loader, so the `interval` meta-package is not installed here. This
is a dependency-loading change, not a replacement of the mathematical backend.

## Other tools

Mathematica/Wolfram is separate from OCaml. It can run on another machine from the
same distribution; see [mathematica/README.md](../mathematica/README.md). It is not
needed to run OCaml. No undocumented Wolfram notebook state is required.

Precompiled manuscript/commentary PDFs are supplied. Rebuilding them requires TeX
with the packages named in their preambles (AMS, TikZ/PGF, natbib, fonts, listings,
and hyperref among them). On Ubuntu, a sufficiently complete TeX Live installation
provides these. `bash paper/build.sh` builds the manuscript; `make docs` rebuilds the
indices and commentary. TeX is not a dependency of the interval searches.

## Memory and duration

Defaults reserve 8 GiB beyond each active process's 4 GiB address-space budget.
Automatic concurrency is up to eight, limited by CPUs, visible/cgroup memory, and
live available memory. With 31 GiB visible RAM this selects five. Smaller machines
can explicitly reduce the reserve and worker count; see [RUNNING.md](RUNNING.md).
The longest historical job took roughly six hours. Keep the terminal open and
prevent automatic sleep/restart. Time and memory limits are operational controls,
not mathematical thresholds.

## Public references and preservation

- opam installation: https://opam.ocaml.org/doc/Install.html
- CRlibm interval package/dependencies: https://opam.ocaml.org/packages/interval_crlibm/
- Interval meta-package (including the unused Intel backend): https://opam.ocaml.org/packages/interval/
- OCaml 4.14 toplevel: https://ocaml.org/manual/4.14/toplevel.html

Versioned archive URLs and hashes are in `environment/dependency-sources.json`.
Preserve exact sources and notices, not only a package name or local development
pin. See [environment/README.md](../environment/README.md) for archival commands.
