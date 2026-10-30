# Standalone build and rendered PDF QA

The supplied eight final PDFs and TeX files are unchanged. Each TeX was copied to a separate build directory and compiled three times with `pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error -file-line-error manuscript.tex`. All eight succeeded with matching page counts, no unresolved references, missing glyphs or overfull boxes. The common epstopdf shell-escape warning does not affect these standalone sources.

| Paper | Supplied pages | Rebuilt pages | Result |
|---|---:|---:|---|
| ANISO_PSER | 53 | 53 | build succeeded |
| ANISO_Reader | 41 | 41 | build succeeded |
| HT_PSER | 22 | 22 | build succeeded |
| HT_Reader | 35 | 35 | build succeeded |
| JOINT_PSER | 55 | 55 | build succeeded |
| JOINT_Reader | 59 | 59 | build succeeded |
| LT_PSER | 23 | 23 | build succeeded |
| LT_Reader | 46 | 46 | build succeeded |

All 334 supplied PDF pages were rendered and inspected in contact sheets. The thirteen corrected passages and representative normalization/closure pages were also inspected at larger scale where notation mattered. Author Dehao Lin and exactly one visible ChatGPT disclosure were independently found in every final PDF; PDF author/title metadata were checked.

Every page was also compared with the independently rebuilt rendering. The PDFs are not byte-identical: TeX versions/font rendering and Unicode CMaps differ (notably summation-symbol text extraction). Maximum reported per-page mean absolute grayscale/pixel difference is below 0.42 on the 0–255 scale. This is supporting layout evidence, not proof of formula equivalence. The 13 semantic corrections were checked from rendered notation plus actual formulas.

Detailed build commands, warnings, page-level text hashes and raster comparisons are in EVIDENCE/BUILD_RECEIPTS.json and EVIDENCE/PDF_RENDER_COMPARISON.json. The publication files are the supplied final PDFs, not the regenerated PDFs.
