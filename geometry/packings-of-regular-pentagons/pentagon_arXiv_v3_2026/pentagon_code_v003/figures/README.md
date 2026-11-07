# Figure sources and reproduction

The files `figure_*.tex` are the 28 active TikZ constructions in the supplied paper.
They preserve its existing coordinates, captions and labels, including rounded
coordinates used solely for illustration. `manifest.json` gives the paper number,
source line and SHA-256 of each complete construction. No plot optimizer is rerun
or used as a proof premise.

In **Linux/Ubuntu Bash**, at PACKAGE_ROOT:

```bash
python3 scripts/extract_figures.py
python3 scripts/build_docs.py --compile --figures
```

The first command only extracts active constructions from `paper/pentagon_v005.tex`;
the second builds the paper, commentary and standalone gallery. A TeX distribution
with the packages in the preambles is required. The precompiled `gallery.pdf` can
be opened directly. Its figures retain the paper’s numbering; the constants table
is in the article and is not a TikZ gallery item.

`PentagonFigures.wl` supplies optional definition-only Wolfram drawing helpers and
the translational Gamma family. These are illustration helpers, not interval code.
The old graphics-only unrounded interval backend is neither included nor loaded by
any proof process. The historical inventory is in provenance/.
