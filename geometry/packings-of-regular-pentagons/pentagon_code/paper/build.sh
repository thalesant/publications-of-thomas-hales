#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
pdflatex -interaction=nonstopmode -halt-on-error header_v008.tex
if command -v bibtex >/dev/null 2>&1; then
  bibtex header_v008
elif command -v bibtex.original >/dev/null 2>&1; then
  bibtex.original header_v008
else
  printf '%s\n' 'BibTeX is unavailable; using the supplied unchanged bibliography output.'
  test -f header_v008.bbl
fi
pdflatex -interaction=nonstopmode -halt-on-error header_v008.tex
pdflatex -interaction=nonstopmode -halt-on-error header_v008.tex
cp header_v008.pdf pentagon_v008.pdf
printf '\nCreated: %s/pentagon_v008.pdf\n' "$PWD"
