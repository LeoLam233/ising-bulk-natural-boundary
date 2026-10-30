# Natural boundaries of the square-lattice Ising susceptibility

The **HT22 PSER proof** is a distinct independent high-temperature proof: [frozen 22-page PDF](paper/ht/pser/manuscript.pdf) · [TeX](paper/ht/pser/manuscript.tex) · [fourteen-field theorem](lean/IsingBulk/HT22/Final/Target.lean) · [correspondence](docs/ht22/PROOF_MAP.md) · [reproduce](docs/ht22/BUILD_AND_VERIFY.md).

| High-temperature edition | Paper | Formal route |
|---|---|---|
| Original HT (33 pages) | [PDF](paper/ht/frozen/manuscript.pdf) · [TeX](paper/ht/frozen/manuscript.tex) | [Original HT Lean 1747](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) |
| Reader (editorial edition of Original HT) | [PDF](paper/ht/reader/manuscript.pdf) · [TeX](paper/ht/reader/manuscript.tex) | Same Original HT Lean route |
| PSER HT22 (distinct independent proof) | [22-page PDF](paper/ht/pser/manuscript.pdf) · [TeX](paper/ht/pser/manuscript.tex) | [Independent HT22 Lean](lean/IsingBulk/HT22/Final/Target.lean) |

`IsingBulk.HT22.ht22_full_target : IsingBulk.HT22.HT22FullTarget` has zero root premises and fourteen proved fields. Physical interpretation uses exactly `PhysicalScope.PublishedRealHTSpinFormFactors corr` as an antecedent: onsite spin-square and real sitewise odd form factors. No Gibbs-state construction is claimed. [Physical scope](docs/ht22/PHYSICAL_INPUTS.md) · [Audit identities](docs/ht22/AUDIT_EVIDENCE.md) · [HT22 citation](high-temperature/ht22/CITATION.cff). Original HT and its recommended Reader, LT22 and all earlier releases retain their own identities.


The **LT22 PSER proof** is an independent low-temperature route: [frozen 22-page PDF](paper/lt/pser/manuscript.pdf) · [TeX](paper/lt/pser/manuscript.tex) · [Preferred22 theorem](lean/IsingBulk/Preferred22/FullTheorem.lean) · [scope and correspondence](docs/lt22/PROOF_MAP.md) · [reproduce](docs/lt22/BUILD_AND_VERIFY.md).

| Low-temperature edition | Paper | Formal route |
|---|---|---|
| Original paper (canonical LT) | [PDF](paper/next/manuscript.pdf) · [TeX](paper/next/manuscript.tex) | [Original LT Lean](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| Reader paper (editorial edition of Original) | [PDF](paper/lt/reader/manuscript.pdf) · [TeX](paper/lt/reader/manuscript.tex) | [Original LT Lean](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| PSER paper (LT22, distinct proof) | [22-page PDF](paper/lt/pser/manuscript.pdf) · [TeX](paper/lt/pser/manuscript.tex) | [Independent Preferred22 Lean](lean/IsingBulk/Preferred22/FullTheorem.lean) |

LT22 preserves the October 25 audited source bytes: 333 new modules, 153 identical inherited modules, unchanged Lean 4.34.1 and nine dependency pins. The exact root is `IsingBulk.Preferred22.preferred_full_target : IsingBulk.Preferred22.PreferredFullTarget`, with zero root premises; Yang and Palmer–Tracy inputs are antecedents only within the physical identification clause. [Identity and prior audit](provenance/lt22/PRIOR_ACCEPTANCE.json) · [LT22 citation](low-temperature/lt22/CITATION.cff). The records below retain their historical version-specific scope. The LT22 paragraph records that release’s scope. HT22 is now presented separately above; ANISO F002 and JOINT F001 remain future publication tasks.

This repository presents four mathematical developments on the **complete zero-field bulk susceptibility** of the infinite square-lattice Ising model, accompanied by Lean formalizations. The results range from separate isotropic low- and high-temperature proofs to fixed positive anisotropy ratios and a parent theorem in two independent complex couplings.

**Recommended starting point: the four complete, independently reviewed Reader editions.** They improve the exposition while preserving the governing mathematical statements, hypotheses and proof mechanisms. The original manuscripts and the corresponding fixed Lean source declarations remain available for exact comparison.

## Papers

| Mathematical result | Recommended reading | Governing original | Lean formalization |
|---|---|---|---|
| **Joint natural boundaries with two independent complex couplings** | [Reader PDF](paper/joint/reader/manuscript.pdf) · [TeX](paper/joint/reader/manuscript.tex) | [Frozen 59-page manuscript](paper/joint/frozen/manuscript.pdf) | [Lean theorem](lean/IsingBulk/Joint/Final/FullConclusion.lean) |
| **Fixed-ratio anisotropic natural boundaries** | [Reader PDF](paper/aniso/reader/manuscript.pdf) · [TeX](paper/aniso/reader/manuscript.tex) | [Frozen 38-page manuscript](paper/aniso/frozen/manuscript.pdf) | [Lean theorem](lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) |
| **Isotropic high-temperature bulk susceptibility** | [Reader PDF](paper/ht/reader/manuscript.pdf) · [TeX](paper/ht/reader/manuscript.tex) | [Frozen original manuscript](paper/ht/frozen/manuscript.pdf) | [Lean theorem](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) |
| **Isotropic low-temperature connected bulk susceptibility** | [Reader PDF](paper/lt/reader/manuscript.pdf) · [TeX](paper/lt/reader/manuscript.tex) | [Canonical v0.1-rc6 manuscript](paper/next/manuscript.pdf) | [Lean theorem](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |

## Scope of the four results

### Joint natural boundaries with two independent complex couplings

The two-complex-variable parent theorem treats full high- and low-temperature bulk susceptibilities, their positive-ratio restrictions and isotropic descendants, and quantitative boundary obstructions. Its common real physical inputs are explicit premises.

[Result and scope](joint/README.md) · [Build and verification](docs/joint/BUILD_AND_VERIFY.md) · [Citation](joint/CITATION.cff)

### Fixed-ratio anisotropic natural boundaries

For every fixed finite positive coupling ratio, the full high- and low-temperature susceptibilities have the stated natural boundaries on their lens and epigraph domains. The field-derivative conventions and physical premises remain distinct and explicit.

[Result and scope](anisotropic/README.md) · [Build and verification](docs/aniso/BUILD_AND_VERIFY.md) · [Citation](anisotropic/CITATION.cff)

### Isotropic high-temperature bulk susceptibility

The disordered-phase theorem covers the complete odd-particle series, onsite contribution and all lattice sites. The unit circle is a natural boundary; the published real-temperature angular representation is an explicit physical premise.

[Result and scope](high-temperature/README.md) · [Build and verification](docs/ht/BUILD_AND_VERIFY.md) · [Citation](high-temperature/CITATION.cff)

### Isotropic low-temperature connected bulk susceptibility

The ordered pure-phase theorem covers the complete positive even-particle series and all lattice sites, subtracting spontaneous magnetization squared. Its physical interface and independent original proof remain separately documented.

[Result and scope](low-temperature/README.md) · [Build and verification](lean/README.md) · [Citation](low-temperature/CITATION.cff)

## Mathematical relationship, editions and reproducibility

The two-variable parent establishes its own positive-ratio and isotropic descendants by internal arguments. The fixed-ratio theorem treats both physical phases, while the earlier direct isotropic high- and low-temperature proofs remain separate developments with distinct observables and particle expansions.

For isotropic couplings, s = sinh(2βJ); fixed-ratio anisotropy continues z = 2βJ with the ratio held fixed. External physical correlation/Gibbs premises and any sharper statements established only in a manuscript are identified in the corresponding scope and proof documents; they are not silently described as literal Lean exports.

**Reader** means the independently checked, exposition-improved complete paper. **Original/frozen** identifies its mathematical authority; some earlier **publication** editions changed only author/date metadata. Historical labels such as C001, C002 and HT-1.0 belong in the [version records](docs/VERSIONS.md), not in the main paper titles.

[Paper editions](paper/README.md) · [Repository and theorem map](REPOSITORY_MAP.md) · [Evidence, reproducibility and citations](docs/EVIDENCE_AND_REPRODUCIBILITY.md) · [中文首页](README.zh.md) · [Authorship](AUTHORSHIP.md) · [MIT code license](LICENSE) · [CC BY 4.0 document license](LICENSE-DOCUMENTATION.md)
