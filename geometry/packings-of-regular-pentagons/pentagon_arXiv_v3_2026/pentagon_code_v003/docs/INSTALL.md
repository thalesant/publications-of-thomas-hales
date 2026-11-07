# Installation for a mathematician

## Scope

The interval programs use OCaml 4.14.4 bytecode and the CRlibm-backed interval
library. Python 3.10 or later controls execution and reporting using its standard
library. A Wolfram Language kernel is needed only for the supplementary paper
checks. TeX is needed only to rebuild PDFs; ready-made PDFs are included.

The documented execution environment is 64-bit Linux, including Ubuntu 24.04 on
WSL 2. The Python controller uses Linux process groups, resource limits, and memory
accounting; it is not a native Windows command-line program. The Wolfram package
can be used in the native Windows Mathematica application independently.

## Windows: open Ubuntu, not PowerShell, for the calculations

In PowerShell, `wsl --list --verbose` shows installed distributions. An existing
Ubuntu WSL 2 installation need not be reinstalled. A new installation can be made
from an administrator PowerShell with `wsl --install -d Ubuntu`; follow Windows’
setup/restart instructions. Thereafter open Ubuntu from Start or Windows Terminal.
The remaining commands in this section are **Ubuntu Bash**, not PowerShell.

Extract this entire distribution into a new folder, preferably within the Linux
filesystem. The folder with `run.py` and `registry.json` is PACKAGE_ROOT. Do not
merge it into an older `code_v000` directory. Its absolute path is not fixed.

## Ubuntu tools

In Ubuntu Bash:

```bash
sudo apt update
sudo apt install build-essential opam git curl ca-certificates m4 pkg-config unzip rsync bubblewrap python3
opam --version
```

The Ubuntu package may provide an older opam executable. Follow the official opam
installation page if the repository warns that it lacks security fixes; updating
package definitions with `opam update` does not upgrade the opam executable.
The recorded working setup used opam 2.6.1. An explicit official-installer route is:

```bash
curl -fsSL https://opam.ocaml.org/install.sh -o "$HOME/install-opam.sh"
sh "$HOME/install-opam.sh" --version 2.6.1 --backup
hash -r
opam --version
```

Inspect downloaded installation scripts according to your normal security practice.
Do not run opam itself as root. If opam has not yet been initialized, run:

```bash
opam init --bare --no-setup -y
```

Then change to PACKAGE_ROOT and run:

```bash
bash environment/install.sh
```

This creates a named switch with OCaml 4.14.4 and pins the package versions listed
in `environment/install.sh`: interval 1.6, CRlibm binding 0.5.1, and ocamlfind 1.9.8.
It refuses to replace an existing switch. The interval meta-package installs both
backends, but **the proof loader explicitly selects `Interval_crlibm.I`**, not the
Intel transcendental implementation. The released adapter handles the historical
operation names and the documented square-root domain exception convention.

An existing working `pentagon-4.14.4` switch, including a locally pinned interval
source, can be used unchanged. Its exact installed files and versions are captured
in every run. An installed package number alone is not the identity of a development
checkout. The fresh-install recipe and the archived development installation are
therefore not described as byte-identical environments.

## Check the installation before a long run

At PACKAGE_ROOT in Ubuntu/Linux Bash:

```bash
python3 run.py --tests --extended
```

This runs the actual OCaml contract tests and the squeezing supplement tests.
Missing tools, an interface mismatch, zero tests, or an unsuccessful load gives a
nonzero result. The complete command `python3 run.py --all --diagnostics` includes
these tests automatically and gates the long calculations on success.

No shell startup edit or manual `eval "$(opam env ...)"` is required: the controller
selects the switch explicitly. On a different switch, supply `--switch NAME`.
Native compilation is not used as an optimization; floating-point rewrites can
matter to directed rounding and would require separate validation.

## Optional PDF tools

To rebuild the paper, commentary and figures, install a TeX distribution containing
AMS classes, TikZ/PGF, newtx, inconsolata, hyperref, listings and the packages in the
included preambles. Then, at PACKAGE_ROOT, run:

```bash
python3 scripts/build_docs.py --compile --figures
```

The supplied bibliography output allows rebuilding without BibTeX. If references
are edited, regenerate it conventionally with BibTeX and compile again.

## Official references

- opam installation: https://opam.ocaml.org/doc/Install.html
- opam switch/exec: https://opam.ocaml.org/doc/man/opam-switch.html and https://opam.ocaml.org/doc/man/opam-exec.html
- interval 1.6: https://opam.ocaml.org/packages/interval/interval.1.6/
- interval project and backend distinction: https://github.com/Chris00/ocaml-interval
- WSL installation/files: https://learn.microsoft.com/en-us/windows/wsl/install and https://learn.microsoft.com/en-us/windows/wsl/filesystems

Source archive URLs and SHA-256 identities are recorded in
`environment/dependency-sources.json`; retain source archives for long-term use.
