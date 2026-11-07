# Manuscript v005

`pentagon_v005.tex` is the article fragment; **compile `header_v005.tex`**, which
supplies the document class, packages, macros, title and bibliography. The PDF
`pentagon_v005.pdf` is supplied for reading without a TeX installation.

From **Linux/Ubuntu Bash**, change into this `paper` directory and run:

```bash
pdflatex -interaction=nonstopmode -halt-on-error header_v005.tex
pdflatex -interaction=nonstopmode -halt-on-error header_v005.tex
pdflatex -interaction=nonstopmode -halt-on-error header_v005.tex
```

Use BibTeX conventionally if bibliography entries are changed. The supplied
`header_v005.bbl` permits rebuilding the distributed bibliography without BibTeX.
From PACKAGE_ROOT, `python3 scripts/build_docs.py --compile --figures` also rebuilds
the numbered code index, commentary and figure gallery.

The manuscript retains the mathematical text of the supplied v004g revision.
Editorial review blocks and superseded commented passages are removed. The local
changes are listed in `../provenance/paper-changes.md`. All 169 existing theorem,
equation, section and figure label numbers match the compiled parent. Additional
seven-letter navigation keys appear only in TeX comments, not in the PDF or counters.

Find the supporting calculation through `../docs/index.html`, by printed lemma
number, existing TeX label, or seven-letter code. The compilation uses the fixed
release date, so rebuilding later does not silently change that date.

Changing the manuscript changes the source identity recorded by the Wolfram suite
and release confirmation. Rebuild references and rerun the applicable checks for a
new version; do not edit a confirmation file by hand.
