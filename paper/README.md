# Manuscript versions and builds

The current development manuscript is **v0.1-rc5** under [next/](next/manuscript.pdf), with [TeX](next/manuscript.tex), [labels/pages](next/LABEL_INDEX.json) and [build identity](next/BUILD.json). It pairs with Lean v0.3.0-rc1. All 65 previous label numbers remain; equation (B.1) and Corollary 9.4 are added.

With an existing pdflatex, from the repository root:

```sh
python scripts/build_candidate_paper.py
```

The builder uses a new .local directory, resolves final references and layout diagnostics, checks label numbers, and updates only candidate generated files. PDF bytes can vary with engines/fonts/timestamps. [Visual QA](../release/next/PDF_QA.json) is separate from compilation.

The original manuscript TeX, PDF and index in this directory remain the frozen **rc4 editorial artifact**. Its PDF SHA-256 `107f09155e1ce46d65b5f8070ce33d3d9eddb177120413883d91b4f9c12202e4` differs from tagged rc4 `624429bb0f2c211fec26cbc9e7608add65eb26a133a6af57259830b5fabd7693`. [Versions](../docs/VERSIONS.md) · [original crosswalk](../provenance/RC4_IDENTITY_2026-10-16.md).

The old Tectonic `scripts/build_paper.py` builds frozen sources and the old rc4/v0.2.1 brief. It is not the candidate builder. Historical build receipts and manifest are unchanged.
