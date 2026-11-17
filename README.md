# Ising susceptibility: eight mathematical papers

[Read the current eight-paper collection](papers/README.md) · [中文](README.zh.md) · [Repository map](REPOSITORY_MAP.md) · [Authorship and AI disclosure](AUTHORSHIP.md)

The collection contains two proofs each for low-temperature susceptibility, high-temperature susceptibility, fixed-ratio anisotropic susceptibility, and susceptibility in two independent complex coupling variables. Each paper treats the full bulk susceptibility in its physical normalization.

At equal coupling, the original fixed-ratio proof applies the two original normalized isotropic natural-boundary theorems. The real-cycle alternative proves the equal-coupling case within the paper. Both two-variable proofs establish joint natural boundaries, prove natural boundaries on the temperature slice for each finite positive ratio, and derive the isotropic disk and exterior germs.

Seven of the eight routes have completed Lean formalizations with explicit hypotheses and fields. The two-variable endpoint/transport proof (JOINT-PSER) has status `NOT_SEPARATELY_FORMALIZED`. [Theorem correspondence](docs/eight-papers/LEAN_CORRESPONDENCE.md) · [Eight-route status](docs/eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md).

The real-cycle anisotropic proof (ANISO-PSER F002) culminates in `IsingBulk.AnisoF002.full_uniform_field_conclusion`. Its analytic natural-boundary fields assume positive couplings. Its real-temperature identification and energy-field response use `PublishedRealSpinFormFactors` and `PublishedRealGibbsFields` as explicit inputs. [Lean theorem](lean/IsingBulk/AnisoF002/C03/FullUniformFieldConclusion.lean) · [F002 scope and audit](docs/aniso-f002/PUBLICATION.md).

[Lean sources](lean/) · [Historical manuscripts and path map](archive/manuscripts/pre-eight-2026-10-30/README.md)

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
