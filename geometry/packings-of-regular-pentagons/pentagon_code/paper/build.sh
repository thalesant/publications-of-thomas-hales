#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
pdflatex -interaction=nonstopmode -halt-on-error header_v010.tex
if command -v bibtex >/dev/null 2>&1; then
  bibtex header_v010
elif command -v bibtex.original >/dev/null 2>&1; then
  bibtex.original header_v010
else
  printf '%s\n' 'BibTeX is unavailable; using the supplied unchanged bibliography output.'
  test -f header_v010.bbl
fi
pdflatex -interaction=nonstopmode -halt-on-error header_v010.tex
pdflatex -interaction=nonstopmode -halt-on-error header_v010.tex
cp header_v010.pdf pentagon_v010.pdf
printf '\nCreated: %s/pentagon_v010.pdf\n' "$PWD"
