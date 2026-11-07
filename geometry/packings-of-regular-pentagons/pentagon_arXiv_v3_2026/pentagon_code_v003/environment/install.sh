#!/usr/bin/env bash
# A fresh, version-pinned verification environment. Never upgrades an existing switch.
set -euo pipefail
switch="${1:-pentagon-4.14.4}"
command -v opam >/dev/null || { echo 'Install and initialize opam first; see docs/INSTALL.md.' >&2; exit 2; }
if opam switch list --short | grep -Fxq "$switch"; then
  printf 'Switch %s already exists. It was NOT modified. Run the tests using that switch.\n' "$switch"
  exit 0
fi
opam switch create "$switch" ocaml-base-compiler.4.14.4 --jobs=4 -y
opam install --switch="$switch" interval.1.6 crlibm.0.5.1 ocamlfind.1.9.8 --jobs=4 -y
printf '\nCreated %s. Run python3 run.py --tests --switch %s.\n' "$switch" "$switch"
