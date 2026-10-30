[Current eight-paper collection](../papers/README.md) · [Exact formalization status](eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md).

The records below retain their version-specific historical scope. Current editions are under papers/; older article links resolve to the archive.

# Evidence, reproducibility and citation guide

The **LT22 PSER proof** is an independent low-temperature route: [frozen 22-page PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/pser/manuscript.pdf) · [TeX](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/pser/manuscript.tex) · [Preferred22 theorem](../lean/IsingBulk/Preferred22/FullTheorem.lean) · [scope and correspondence](../docs/lt22/PROOF_MAP.md) · [reproduce](../docs/lt22/BUILD_AND_VERIFY.md).

| Low-temperature edition | Paper | Formal route |
|---|---|---|
| Original paper (canonical LT) | [PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/next/manuscript.pdf) · [TeX](../archive/manuscripts/pre-eight-2026-10-30/paper/next/manuscript.tex) | [Original LT Lean](../lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| Reader paper (editorial edition of Original) | [PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/reader/manuscript.pdf) · [TeX](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/reader/manuscript.tex) | [Original LT Lean](../lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| PSER paper (LT22, distinct proof) | [22-page PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/pser/manuscript.pdf) · [TeX](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/pser/manuscript.tex) | [Independent Preferred22 Lean](../lean/IsingBulk/Preferred22/FullTheorem.lean) |

LT22 preserves the October 25 audited source bytes: 333 new modules, 153 identical inherited modules, unchanged Lean 4.34.1 and nine dependency pins. The exact root is `IsingBulk.Preferred22.preferred_full_target : IsingBulk.Preferred22.PreferredFullTarget`, with zero root premises; Yang and Palmer–Tracy inputs are antecedents only within the physical identification clause. [Identity and prior audit](../provenance/lt22/PRIOR_ACCEPTANCE.json) · [LT22 citation](../low-temperature/lt22/CITATION.cff). The records below retain their historical version-specific scope. HT22, ANISO F002 and JOINT F001 are separate future publication tasks; this LT22 addition makes no completion or publication claim for them.

This page is a **navigation index** for the existing evidence. It does not replace mathematical proofs, certify historical audits, or expand any Lean theorem's formal scope.

## Reading and verifying a particular result

| Purpose | Where to begin |
|---|---|
| Read the full paper | [Four reviewed Reader editions](../archive/manuscripts/pre-eight-2026-10-30/paper/README.md), each with PDF and TeX |
| Identify the exact mathematical baseline | [Repository theorem map](../REPOSITORY_MAP.md) and [version ledger](VERSIONS.md) |
| See which claims are in the actual Lean endpoint | [Joint](joint/PROOF_MAP.md), [anisotropic](aniso/PROOF_MAP.md), [high-temperature](ht/PROOF_MAP.md), and [low-temperature theorem source](../lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| Identify physical premises | [Joint physical inputs](joint/PHYSICAL_INPUTS.md), [anisotropic physical inputs](aniso/PHYSICAL_INPUTS.md), and [high-temperature theorem correspondence](ht/PROOF_MAP.md) |
| Rebuild and check proof sources | [Joint](joint/BUILD_AND_VERIFY.md), [anisotropic](aniso/BUILD_AND_VERIFY.md), [high-temperature](ht/BUILD_AND_VERIFY.md), and [low-temperature](../lean/README.md) |
| Understand automatic vs manual verification | [Proof CI routing](PROOF_CI_ROUTING.md) and [GitHub Actions](../.github/workflows) |

The complete Reader papers have independently checked editorial correspondence to their governing originals and Lean source declarations. The Reader correspondence records distinguish explicit physical premises and manuscript-only calculations from the terminal formal theorem. The Reader editing pass did not change the Lean source.

## Where the records live

| Location | Contents and interpretation |
|---|---|
| [`archive/manuscripts/pre-eight-2026-10-30/paper/`](../archive/manuscripts/pre-eight-2026-10-30/paper/README.md) | Complete Reader TeX/PDF pairs and the exact original, frozen or earlier metadata-only paper editions. Do not treat two editorial editions as identical files. |
| [`lean/`](../lean/README.md) | Formal source, roots, audits, pinned dependencies and historical source snapshots. Read the exact theorem declaration and its dependency route. |
| [`docs/`](../docs) | Per-result proof maps, physical interfaces, version identities, verification instructions and explanatory records. |
| [`provenance/`](../provenance) | Frozen input identities, source crosswalks, changes and model-specific provenance. These establish which bytes and versions are being discussed. |
| [`audits/`](../audits/README.md) | Primarily historical low-temperature audit records and versioned review views, with links to later results. A review verdict applies only to its stated input and checks. |
| [`release/`](../release) | Historical release and validation receipts, especially from the low-temperature development. For published result-specific assets, also use [GitHub Releases](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases). |
| [`research-history/`](../research-history/README.md) | Research chronology, superseded attempts, repairs, and their precise historical limits. |
| [`reproduction/`](../reproduction/README.md) | CR0/MR1 exploratory reconstructions and receiver assessments. Several recorded attempts are explicitly partial; they are not alternative certifications of the complete theorem. |
| [`checks/`](../checks/README.md) | Finite numerical and symbolic diagnostics, source scripts, and fixtures. Passing them does not prove an infinite-series estimate. |
| [`verification/`](../verification/joint) | Joint publication-closure source templates and negative/positive control fixtures, supplementary to the actual Lean proof sources. |
| [`scripts/`](../scripts) | Build, source-identity and reproducibility scripts. Inspect each script's exact input contract and version. |

For the later research results, see the [anisotropic audit availability record](aniso/AUDIT_EVIDENCE.md) and [joint audit availability record](joint/AUDIT_EVIDENCE.md). Those pages distinguish reported AI reviews, available and missing archives, and newly executed CI receipts. An archive mentioned by hash is not necessarily hosted in GitHub.

## What the verification establishes

A **source/hash check** confirms identity, not mathematical validity. A **clean Lean build and fresh kernel replay** confirm acceptance of the specified formal declarations under the indicated dependencies, not the separate external physical premises or sharper manuscript-only assertions. The [original/frozen manuscripts](../archive/manuscripts/pre-eight-2026-10-30/paper/README.md) govern their own mathematical text. Historical AI audit conclusions are evidence of the checks reported for those exact versions and are not human peer review.

The joint four-result workflow's [recorded successful run](https://github.com/LeoLam233/ising-bulk-natural-boundary/actions/runs/40318560582) is an example of executable source-clean/strict/fresh-replay verification. Later navigation-only edits do not change its proof-source identity. For any new proof-source revision, use the applicable workflow and record its **new** execution identity.

## How to cite the work

The repository-level [`CITATION.cff`](../CITATION.cff) describes the **software repository and combined formal development**. For a particular mathematical paper, use the corresponding result-specific article citation:

| Mathematical paper | Citation metadata | Recommended complete paper |
|---|---|---|
| Joint natural boundaries with two independent complex couplings | [Article citation](../joint/CITATION.cff) | [Reader PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/joint/reader/manuscript.pdf) |
| Fixed-ratio anisotropic natural boundaries | [Article citation](../anisotropic/CITATION.cff) | [Reader PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/aniso/reader/manuscript.pdf) |
| Isotropic high-temperature bulk susceptibility | [Article citation](../high-temperature/CITATION.cff) | [Reader PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/ht/reader/manuscript.pdf) |
| Isotropic low-temperature connected bulk susceptibility | [Article citation](../low-temperature/CITATION.cff) | [Reader PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/reader/manuscript.pdf) |

Individual citation files retain their exact historical version strings, titles, and release metadata. The later Reader edition is a separate exposition-improved presentation: when a citation needs to identify the exact text consulted, include the Reader path and current commit or the frozen manuscript's version/hash as appropriate. The code license is [MIT](../LICENSE); author-created manuscripts and documentation have a separate [CC BY 4.0 license](../LICENSE-DOCUMENTATION.md).
