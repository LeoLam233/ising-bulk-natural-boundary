# Low-temperature connected bulk susceptibility — manuscript editions

The **LT22 PSER proof** is an independent low-temperature route: [frozen 22-page PDF](../../paper/lt/pser/manuscript.pdf) · [TeX](../../paper/lt/pser/manuscript.tex) · [Preferred22 theorem](../../lean/IsingBulk/Preferred22/FullTheorem.lean) · [scope and correspondence](../../docs/lt22/PROOF_MAP.md) · [reproduce](../../docs/lt22/BUILD_AND_VERIFY.md).

| Low-temperature edition | Paper | Formal route |
|---|---|---|
| Original paper (canonical LT) | [PDF](../../paper/next/manuscript.pdf) · [TeX](../../paper/next/manuscript.tex) | [Original LT Lean](../../lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| Reader paper (editorial edition of Original) | [PDF](../../paper/lt/reader/manuscript.pdf) · [TeX](../../paper/lt/reader/manuscript.tex) | [Original LT Lean](../../lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| PSER paper (LT22, distinct proof) | [22-page PDF](../../paper/lt/pser/manuscript.pdf) · [TeX](../../paper/lt/pser/manuscript.tex) | [Independent Preferred22 Lean](../../lean/IsingBulk/Preferred22/FullTheorem.lean) |

LT22 preserves the October 25 audited source bytes: 333 new modules, 153 identical inherited modules, unchanged Lean 4.34.1 and nine dependency pins. The exact root is `IsingBulk.Preferred22.preferred_full_target : IsingBulk.Preferred22.PreferredFullTarget`, with zero root premises; Yang and Palmer–Tracy inputs are antecedents only within the physical identification clause. [Identity and prior audit](../../provenance/lt22/PRIOR_ACCEPTANCE.json) · [LT22 citation](../../low-temperature/lt22/CITATION.cff). The records below retain their historical version-specific scope. HT22, ANISO F002 and JOINT F001 are separate future publication tasks; this LT22 addition makes no completion or publication claim for them.

- **Recommended:** [complete Reader PDF](reader/manuscript.pdf) · [TeX](reader/manuscript.tex), 49 pages · [edition identity](reader/README.md).
- **Canonical mathematical authority:** [v0.1-rc6 PDF](../next/manuscript.pdf) · [TeX](../next/manuscript.tex), 47 pages.
- **Historical versions:** [paper index](../README.md) · [version ledger](../../docs/VERSIONS.md).
- [Lean source and build](../../lean/README.md) · [Reader–Lean correspondence](reader/LEAN_CORRESPONDENCE.md).

The old `paper/next/` and frozen paths are preserved for reproducibility, while Reader is the default public reading edition.
