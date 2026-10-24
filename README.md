# Natural boundaries of the square-lattice Ising susceptibility

**Three research results · distinct physical observables and theorem endpoints · one shared Lean library**

This repository presents the complete bulk susceptibility on the infinite square lattice: separate isotropic low-temperature and high-temperature proofs, and a fixed-ratio anisotropic result covering both phases. Every result retains its own manuscript, physical inputs, citation and reproducible Lean endpoint.

- **ANISO C001:** [manuscript](paper/aniso/publication/manuscript.pdf) · [Lean endpoint](lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) · [build](docs/aniso/BUILD_AND_VERIFY.md) · [citation](anisotropic/CITATION.cff).
- **Isotropic HT:** [manuscript](paper/ht/publication/manuscript.pdf) · [Lean endpoint](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) · [build](docs/ht/BUILD_AND_VERIFY.md) · [citation](high-temperature/CITATION.cff).
- **Isotropic LT:** [manuscript](paper/next/manuscript.pdf) · [Lean endpoint](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) · [build](lean/README.md) · [citation](low-temperature/CITATION.cff).

## Fixed-ratio anisotropic result — ANISO C001

Every finite `J > 0`, `lam > 0`; all lattice sites and infinite odd/even particle orders. Natural boundaries at every finite point of the correct HT lens/LT epigraph frontiers, plus HT bilateral and LT plus-state right-sided uniform-field responses. The explicit real-spin and Gibbs-field inputs are [specified here](docs/aniso/PHYSICAL_INPUTS.md).

[Explore ANISO](anisotropic/README.md) · [Manuscript](paper/aniso/publication/manuscript.pdf) · [Lean: `IsingBulk.Anisotropic.full_uniform_field_conclusion`](lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) · [Build](docs/aniso/BUILD_AND_VERIFY.md) · [Citation](anisotropic/CITATION.cff)

## Isotropic high-temperature result — HT-1.0 / Lean 1747

Complete disordered-phase susceptibility for `0 < s < 1`, with every odd-particle order and the unit circle approached from inside. The physical-germ theorem explicitly takes the published real-temperature full-bulk angular representation.

[Explore HT](high-temperature/README.md) · [Manuscript](paper/ht/publication/manuscript.pdf) · [Lean: `IsingBulk.HT.Final.publishedPhysicalSusceptibility_germ_natural_boundary`](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) · [Build](docs/ht/BUILD_AND_VERIFY.md) · [Citation](high-temperature/CITATION.cff)

## Isotropic low-temperature result — manuscript v0.1-rc6 / Lean v0.3.0-rc2

Connected ordered pure-phase susceptibility for `s > 1`, with every positive even-particle order, spontaneous magnetization squared subtracted, and the unit circle approached from outside. Physical identification retains the documented E1/E2 interface.

[Explore LT](low-temperature/README.md) · [Manuscript](paper/next/manuscript.pdf) · [Lean: `IsingBulk.Final.theorem_nb_physical`](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) · [Build](lean/README.md) · [Citation](low-temperature/CITATION.cff)

Here `s = sinh(2βJ)` in the isotropic results; ANISO fixes the coupling ratio before continuing `z = 2βJ` into the complex plane. The [repository map](REPOSITORY_MAP.md) and [version index](docs/VERSIONS.md) distinguish the shared mathematics, frozen sources and publication editions. Existing LT/HT paths, releases and historical records are retained.

The ANISO [frozen 38-page audit edition](paper/aniso/frozen/manuscript.pdf) and [separate 39-page research-original](paper/aniso/research-original/manuscript.pdf) remain available. Its initial publication edition changes only preamble metadata; [later editorial work](docs/aniso/EDITORIAL_FOLLOWUP_SCOPE.md) has a separate scope. [Audit provenance](docs/aniso/AUDIT_EVIDENCE.md) and current execution receipts distinguish reported investigations from actual publication gates.

[中文首页](README.zh.md) · [Authorship and provenance](AUTHORSHIP.md) · [MIT source license](LICENSE) · [CC BY 4.0 author-document license](LICENSE-DOCUMENTATION.md)
