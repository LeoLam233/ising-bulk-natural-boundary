# Author-identified ANISO C001 edition

This 38-page PDF is derived from the frozen 38-page C001 TeX. The only source edits add Dehao Lin's documented affiliation, ORCID and contact, the date 24 October 2026, and descriptive PDF metadata. The title and complete document body, including every proof paragraph, equation, reference and `\maketitle` command, remain byte-identical from `\begin{document}` onward.

[PDF](manuscript.pdf) · [TeX](manuscript.tex) · [Exact diff](EDITORIAL.diff) · [SHA-256 identities](EDITORIAL.json) · [Compilation and visual QA](PDF_QA.json)

The edition was compiled with pdfLaTeX in three passes. The PDF engine differs from the frozen edition's engine, so PDF byte identity is not expected. TeX body identity is checked independently. Underfull bibliography lines inherited from the unchanged source are recorded in the QA receipt; there are no unresolved references or overfull boxes.

For a rebuild, use a new temporary output directory and run `pdflatex -interaction=nonstopmode -halt-on-error -file-line-error -output-directory=YOUR_BUILD_DIRECTORY paper/aniso/publication/manuscript.tex` three times from the repository root. Preserve the checked-in PDF while reproducing it. The exact source/body and PDF hashes are in `EDITORIAL.json`.

Later prose editing belongs to [a separate three-manuscript editorial PR](../../../docs/aniso/EDITORIAL_FOLLOWUP_SCOPE.md). The frozen audit edition and historical research-original remain separately available.
