# Ising susceptibility: eight mathematical papers

[Read the current eight-paper collection](papers/README.md) · [中文](README.zh.md) · [Repository map](REPOSITORY_MAP.md)

The collection contains two distinct proofs for each of four subjects: low-temperature susceptibility, high-temperature susceptibility, fixed-ratio anisotropic susceptibility, and susceptibility in two independent complex coupling variables. Each paper studies the full bulk response, with its physical normalization and published-real input interfaces. Article titles, authorship and the visible ChatGPT disclosures are preserved.

The [current index](papers/README.md) gives every scholarly title and PDF/TeX link. The original fixed-ratio proof legitimately imports the original low- and high-temperature normalized equal-coupling theorems. Its alternative proves that case internally. Both two-complex-variable proofs establish the joint, positive-ratio-slice and isotropic conclusions through their own curve-level arguments.

Seven of the eight routes have completed Lean proofs at their [precise theorem and field scope](docs/eight-papers/LEAN_CORRESPONDENCE.md). The real-cycle anisotropic alternative (ANISO-PSER F002) ends at [`IsingBulk.AnisoF002.full_uniform_field_conclusion`](lean/IsingBulk/AnisoF002/C03/FullUniformFieldConclusion.lean). Its natural-boundary fields require positive couplings; real susceptibility identification and field response use the explicit `PublishedRealSpinFormFactors` and `PublishedRealGibbsFields` interfaces. See the [F002 audit and scope](docs/aniso-f002/PUBLICATION.md) and the [eight-route status](docs/eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md). The two-complex-variable endpoint/transport alternative (JOINT-PSER) remains `NOT_SEPARATELY_FORMALIZED`.

The [Lean tree](lean/) contains the additive F002 integration alongside the unchanged earlier proof sources, toolchain, dependency pins and prior audit records. For old manuscript paths, see the [archive crosswalk](archive/manuscripts/pre-eight-2026-10-30/README.md).

Historical manuscripts are preserved once in the [secondary archive](archive/manuscripts/pre-eight-2026-10-30/README.md). Immutable commit/tag URLs keep their old layouts; deleted moving-main file paths have no automatic GitHub redirect.

The [build and CI guide](docs/PROOF_CI_ROUTING.md) gives the commands for historical verification, standalone TeX builds, and F002 compilation and replay.

## Low-temperature susceptibility

- **A natural boundary for the low-temperature bulk square-lattice Ising susceptibility** (Original proof): [PDF](papers/low-temperature/original-proof/manuscript.pdf) · [TeX](papers/low-temperature/original-proof/manuscript.tex).
- **The full low-temperature Ising susceptibility: a regular-coordinate proof of the natural boundary** (Alternative regular-coordinate proof): [PDF](papers/low-temperature/alternative-proof/manuscript.pdf) · [TeX](papers/low-temperature/alternative-proof/manuscript.tex).
## High-temperature susceptibility

- **High-temperature bulk Ising susceptibility: a natural-boundary proof** (Original proof): [PDF](papers/high-temperature/original-proof/manuscript.pdf) · [TeX](papers/high-temperature/original-proof/manuscript.tex).
- **The complete high-temperature Ising susceptibility: a constrained-coordinate proof of the natural boundary** (Alternative constrained-coordinate proof): [PDF](papers/high-temperature/alternative-proof/manuscript.pdf) · [TeX](papers/high-temperature/alternative-proof/manuscript.tex).
## Fixed-ratio anisotropic susceptibility

- **Natural boundaries of the full bulk susceptibility for the fixed-ratio anisotropic square-lattice Ising model** (Original proof): [PDF](papers/fixed-ratio-anisotropy/original-proof/manuscript.pdf) · [TeX](papers/fixed-ratio-anisotropy/original-proof/manuscript.tex).
- **Natural boundaries of anisotropic Ising susceptibility via real-cycle pole estimates** (Alternative real-cycle proof): [PDF](papers/fixed-ratio-anisotropy/alternative-proof/manuscript.pdf) · [TeX](papers/fixed-ratio-anisotropy/alternative-proof/manuscript.tex).
## Susceptibility in two independent complex coupling variables

- **Natural boundaries of the full square-lattice Ising susceptibility in two complex coupling variables: Spectral domains and physical-slice restrictions** (Original proof): [PDF](papers/two-complex-couplings/original-proof/manuscript.pdf) · [TeX](papers/two-complex-couplings/original-proof/manuscript.tex).
- **Natural boundaries of the full square-lattice Ising susceptibility in two complex coupling variables: Endpoint geometry and constrained transport** (Alternative endpoint/transport proof): [PDF](papers/two-complex-couplings/alternative-proof/manuscript.pdf) · [TeX](papers/two-complex-couplings/alternative-proof/manuscript.tex).
