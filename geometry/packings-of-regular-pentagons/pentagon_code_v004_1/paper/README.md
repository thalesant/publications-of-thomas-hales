# Current manuscript: v007

Read `pentagon_v007.pdf`. Edit `pentagon_v007.tex`; compile the driver
`header_v007.tex`, not the body file by itself. The bibliography is `pentagon.bib`;
a matching compiled `header_v007.bbl` is supplied.

From PACKAGE_ROOT (the directory containing run.py), in Linux/Ubuntu Bash:

```bash
bash paper/build.sh
```

The script changes to this folder itself. It runs pdfLaTeX and BibTeX when available,
then writes `pentagon_v007.pdf`. The packaged manuscript, driver, bibliography,
PDF, and label map are the exact approved v007 artifacts. Source and printed label
numbers have not been changed to consolidate the code.

`label-map.json` gives the 168 retained labels and their printed numbers/pages.
`scripts/build_docs.py` uses it for the code index. Seven-letter comments in the
article provide invisible source locators; the matching code is indexed by printed
number, TeX label, and those locators. There are no older manuscript copies or
nested version folders here.

The compact revision table is [../docs/pentagon_changes_2016v2_to_v007.md](../docs/pentagon_changes_2016v2_to_v007.md).
Building/editing can change fixed-file hashes; do not regenerate the manifest merely
to hide an unexplained mismatch. Numerical verification identifies the manuscript
and label map to which it refers.
