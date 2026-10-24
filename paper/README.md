# Manuscripts: three results

- **ANISO C001:** [publication PDF](aniso/publication/manuscript.pdf), [frozen 38-page audit](aniso/frozen/manuscript.pdf), [separate 39-page research-original](aniso/research-original/manuscript.pdf), [edition identities](aniso/README.md), [citation](../anisotropic/CITATION.cff).
- **HT-1.0 / Lean 1747:** [publication PDF](ht/publication/manuscript.pdf), [frozen audit PDF](ht/frozen/manuscript.pdf), [edition explanation](ht/publication/README.md), [citation](../high-temperature/CITATION.cff).
- **LT v0.1-rc6 / Lean v0.3.0-rc2:** [paper/next PDF](next/manuscript.pdf), [LT index](lt/README.md), [citation](../low-temperature/CITATION.cff).

[Separate three-reader-edition follow-up](../docs/aniso/EDITORIAL_FOLLOWUP_SCOPE.md). Existing papers and version records remain in place. The LT build/history record follows.

---

# Manuscript versions and builds

The current development manuscript is **v0.1-rc6** under [next/](next/manuscript.pdf), with [TeX](next/manuscript.tex), [labels/pages](next/LABEL_INDEX.json) and [build identity](next/BUILD.json). It pairs with Lean v0.3.0-rc2. All 67 verified rc5 label numbers remain; Proposition F.1 is added. It proves the complete-amplitude conversion, with arXiv/journal equation numbering distinguished.

With an existing pdflatex, from the repository root:

```sh
python scripts/build_candidate_paper.py
```

The builder uses a new .local directory, resolves final references and layout diagnostics, checks label numbers, and updates only candidate generated files. PDF bytes can vary with engines/fonts/timestamps. [Visual QA](../release/next/PDF_QA.json) is separate from compilation.

For the accepted artifact, run `python scripts/verify_candidate.py` before rebuilding. Recompile in a separate checkout: the builder updates the PDF and BUILD record, while the accepted QA, validation and manifest still identify the checked-in PDF. Render and inspect the rebuilt PDF, record its new identity in QA and validation, then refresh the candidate inventory and rerun the consistency verifier. Updating hashes alone does not establish visual or mathematical acceptance. Source edits additionally require the matching Lean snapshot and source/verification identities to be updated through the [validation workflow](../lean/README.md).

The original manuscript TeX, PDF and index in this directory remain the frozen **rc4 editorial artifact**. Its PDF SHA-256 `107f09155e1ce46d65b5f8070ce33d3d9eddb177120413883d91b4f9c12202e4` differs from tagged rc4 `624429bb0f2c211fec26cbc9e7608add65eb26a133a6af57259830b5fabd7693`. [Versions](../docs/VERSIONS.md) · [original crosswalk](../provenance/RC4_IDENTITY_2026-10-16.md).

The old Tectonic `scripts/build_paper.py` builds frozen sources and the old rc4/v0.2.1 brief. It is not the candidate builder. Historical build receipts and manifest are unchanged.

The verified rc5 manuscript and matching Lean v0.3.0-rc1 records remain at [`dd977048`](https://github.com/LeoLam233/ising-bulk-natural-boundary/tree/dd977048c2380e775d83b97ae1fba354c04c349a). Their PDF and source identities are preserved in [the amplitude baseline](../provenance/AMPLITUDE_BASELINE.json). The old versioned reports are read in that immutable tree.
