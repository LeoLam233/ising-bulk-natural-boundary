# Manuscripts: four reviewed Reader editions

**Independent HT22 PSER:** [22-page PDF](ht/pser/manuscript.pdf) · [TeX](ht/pser/manuscript.tex) · [exact clarifications](ht/pser/MATHEMATICAL_ERRATA.md) · [independent Lean route](../lean/IsingBulk/HT22/Final/Target.lean). This is a distinct proof alongside Original HT and its recommended Reader.


The **LT22 PSER proof** is an independent low-temperature route: [frozen 22-page PDF](../paper/lt/pser/manuscript.pdf) · [TeX](../paper/lt/pser/manuscript.tex) · [Preferred22 theorem](../lean/IsingBulk/Preferred22/FullTheorem.lean) · [scope and correspondence](../docs/lt22/PROOF_MAP.md) · [reproduce](../docs/lt22/BUILD_AND_VERIFY.md).

| Low-temperature edition | Paper | Formal route |
|---|---|---|
| Original paper (canonical LT) | [PDF](../paper/next/manuscript.pdf) · [TeX](../paper/next/manuscript.tex) | [Original LT Lean](../lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| Reader paper (editorial edition of Original) | [PDF](../paper/lt/reader/manuscript.pdf) · [TeX](../paper/lt/reader/manuscript.tex) | [Original LT Lean](../lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| PSER paper (LT22, distinct proof) | [22-page PDF](../paper/lt/pser/manuscript.pdf) · [TeX](../paper/lt/pser/manuscript.tex) | [Independent Preferred22 Lean](../lean/IsingBulk/Preferred22/FullTheorem.lean) |

LT22 preserves the October 25 audited source bytes: 333 new modules, 153 identical inherited modules, unchanged Lean 4.34.1 and nine dependency pins. The exact root is `IsingBulk.Preferred22.preferred_full_target : IsingBulk.Preferred22.PreferredFullTarget`, with zero root premises; Yang and Palmer–Tracy inputs are antecedents only within the physical identification clause. [Identity and prior audit](../provenance/lt22/PRIOR_ACCEPTANCE.json) · [LT22 citation](../low-temperature/lt22/CITATION.cff). The records below retain their historical version-specific scope. HT22, ANISO F002 and JOINT F001 are separate future publication tasks; this LT22 addition makes no completion or publication claim for them.

**Recommended public reading:** each complete Reader PDF and TeX is linked below, separately from the exact canonical/frozen mathematical authority.

| Mathematical result | Reviewed Reader | Mathematical original | Version details |
|---|---|---|---|
| Joint natural boundaries with two independent complex couplings | [PDF](joint/reader/manuscript.pdf) · [TeX](joint/reader/manuscript.tex) | [Original](joint/frozen/manuscript.pdf) | [Edition index](joint/README.md) |
| Fixed-ratio anisotropic natural boundaries | [PDF](aniso/reader/manuscript.pdf) · [TeX](aniso/reader/manuscript.tex) | [Original](aniso/frozen/manuscript.pdf) | [Edition index](aniso/README.md) |
| Isotropic high-temperature bulk susceptibility | [PDF](ht/reader/manuscript.pdf) · [TeX](ht/reader/manuscript.tex) | [Original](ht/frozen/manuscript.pdf) | [Edition index](ht/README.md) |
| Isotropic low-temperature connected bulk susceptibility | [PDF](lt/reader/manuscript.pdf) · [TeX](lt/reader/manuscript.tex) | [Original](next/manuscript.pdf) | [Edition index](lt/README.md) |

These editorial editions retain the original mathematical content and Lean correspondence; the source theorem identities are listed in the [repository map](../REPOSITORY_MAP.md). Prior author-metadata publication versions and detailed historical records remain available.

The following historical build notes concern the canonical low-temperature development manuscript, not the Reader edition.

---

## Historical low-temperature manuscript versions and builds

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
