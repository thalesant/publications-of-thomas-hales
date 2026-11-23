# Current manuscript: v010

Read `pentagon_v010.pdf`. Edit `pentagon_v010.tex`; compile the driver
`header_v010.tex`, not the body file by itself. The bibliography is `pentagon.bib`;
a matching compiled `header_v010.bbl` is supplied.

From PACKAGE_ROOT (the directory containing run.py), in Linux/Ubuntu Bash:

```bash
bash paper/build.sh
```

The script changes to this folder itself. It runs pdfLaTeX and BibTeX when available,
then writes `pentagon_v010.pdf`.
