# Ising susceptibility: eight mathematical papers

[Read the current eight-paper collection](papers/README.md) · [中文](README.zh.md) · [Repository map](REPOSITORY_MAP.md)

The collection contains two distinct proofs for each of four subjects: low-temperature susceptibility, high-temperature susceptibility, fixed-ratio anisotropic susceptibility, and susceptibility in two independent complex coupling variables. Each paper studies the full bulk response, with its physical normalization and published-real input interfaces. Article titles, authorship and the visible ChatGPT disclosures are preserved.

The [current index](papers/README.md) gives every scholarly title and PDF/TeX link. The original fixed-ratio proof legitimately imports the original low- and high-temperature normalized equal-coupling theorems. Its alternative proves that case internally. Both two-complex-variable proofs establish the joint, positive-ratio-slice and isotropic conclusions through their own curve-level arguments.

Six proof routes have completed formal developments at their [precise theorem/field scope](docs/eight-papers/LEAN_CORRESPONDENCE.md). The real-cycle anisotropic alternative remains PARTIAL; the endpoint/transport two-complex-variable alternative is NOT_SEPARATELY_FORMALIZED. See the [eight-route status](docs/eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md), [scope matrix](docs/eight-papers/SIX_PAPER_LEAN_SCOPE_MATRIX.csv), and [independent preservation audit](docs/eight-papers/EIGHT_PAPER_MATH_PRESERVATION_REPORT.md).

The active formal code remains in [lean/](lean/). All formal source, toolchain, dependency pins and prior audit records are byte-identical to the pinned pre-migration base. Historical source metadata and technical README snapshots under lean/ keep their original paths; resolve those through the [archive crosswalk](archive/manuscripts/pre-eight-2026-10-30/README.md), not as current reading entrances.

Historical manuscripts are preserved once in the [secondary archive](archive/manuscripts/pre-eight-2026-10-30/README.md). Immutable commit/tag URLs keep their old layouts; deleted moving-main file paths have no automatic GitHub redirect.

For editorial verification run `python scripts/verify_eight_papers.py --historical-checks`. Rebuild all current TeX in a separate directory with `python scripts/build_current_papers.py --output PATH`. These commands preserve every published manuscript byte. Existing formal acceptance commands remain available, with hash-checked historical-path routing for their original verifier cores.

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
