# Fixed-ratio anisotropic susceptibility

Two distinct proofs of the full bulk susceptibility theorem.

- **Natural boundaries of the full bulk susceptibility for the fixed-ratio anisotropic square-lattice Ising model** — Original proof: [PDF](original-proof/manuscript.pdf) · [TeX](original-proof/manuscript.tex).
- **Natural boundaries of anisotropic Ising susceptibility via real-cycle pole estimates** — Alternative real-cycle proof: [PDF](alternative-proof/manuscript.pdf) · [TeX](alternative-proof/manuscript.tex).

[All eight papers](../README.md) · [Exact theorem and Lean scope](../../docs/eight-papers/LEAN_CORRESPONDENCE.md) · [Eight-route formalization status](../../docs/eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md).

The original proof uses the original low- and high-temperature normalized natural-boundary theorems at equal couplings, through exact coefficient and covering identities. The alternative real-cycle proof handles equal couplings internally. Its completed Lean terminal is [`IsingBulk.AnisoF002.full_uniform_field_conclusion`](../../lean/IsingBulk/AnisoF002/C03/FullUniformFieldConclusion.lean). The [F002 publication record](../../docs/aniso-f002/PUBLICATION.md) gives the exact analytic fields, the published-real hypotheses, and the final audit entry.
