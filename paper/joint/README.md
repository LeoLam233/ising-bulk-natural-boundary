# JOINT manuscript editions

- [Frozen mathematical authority](frozen/manuscript.pdf) · [exact TeX](frozen/manuscript.tex): 59 pages, 21 October 2026.
- [Author-metadata publication edition](publication/manuscript.pdf) · [TeX](publication/manuscript.tex): Dehao Lin, School of Physics, Sun Yat-sen University, ORCID 0009-0001-4551-8490; publication metadata dated 25 October 2026.
- [Literal editorial diff](publication/EDITORIAL.diff) · [body and file hashes](publication/EDITORIAL.json) · [compilation and page QA](publication/PDF_QA.json).

Only `\author`, `\date` and `\hypersetup` in the TeX preamble change. The entire byte substring from `\begin{document}` is identical. A metadata-induced pagination change is recorded in QA rather than repaired by changing the mathematical body.

Frozen PDF SHA-256: `868c0eda262821292f860fa75662afd8f3bc13b215a9e8aadee735ba7dfc4eb7`.
Frozen TeX SHA-256: `4d4567b2620799e187a9441d321b66079d8635600cb76f503d72fd31cf01e76e`.

[Result entrance](../../joint/README.md) · [Build](../../docs/joint/BUILD_AND_VERIFY.md) · [Citation](../../joint/CITATION.cff)
