# High-temperature natural boundary

**Disordered phase · complete square-lattice bulk magnetic susceptibility**

This is the **high-temperature proof**, a distinct mathematical development within the [two-proof Ising repository](../README.md). It concerns the zero-field, isotropic, infinite square-lattice Ising model at positive coupling (J).

For (s=\sinh(2\beta J)), the physical high-temperature interval is (0<s<1). The theorem constructs the holomorphic continuation of the complete physical susceptibility germ throughout **(|s|<1)** and proves that **every point of (|s|=1)** is a natural-boundary point.

The observable includes **all lattice sites** and the **complete infinite sum over positive odd-particle form factors**. Its physical normalization includes the inverse-temperature factor (eta). The permitted external physical input is the exact published real-temperature angular form-factor representation; the complex-analytic noncancellation and natural-boundary theorem are proved in Lean.

## Read the high-temperature proof

| Resource | Location |
|---|---|
| Mathematical manuscript, frozen reviewed edition | [High-temperature manuscript PDF](../paper/ht/frozen/manuscript.pdf) · [TeX](../paper/ht/frozen/manuscript.tex) |
| Lean proof development | [High-temperature Lean source](../lean/IsingBulk/HT/) |
| **Final Lean theorem** | [`publishedPhysicalSusceptibility_germ_natural_boundary`](../lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) |
| Separate build and kernel-replay entry points | [`IsingBulkHT.lean`](../lean/IsingBulkHT.lean) · [`AuditHT.lean`](../lean/AuditHT.lean) |
| Mathematical and formalization correspondence | [Proof guide](../docs/ht/PROOF_MAP.md) · [Reproduction instructions](../docs/ht/BUILD_AND_VERIFY.md) |
| Independent mathematical/Lean audit results | [Verification and scope](../docs/ht/README.md) |

The version `HT-1.0 / Lean 1747` has passed source-identical clean builds and official fresh kernel replays, followed by separate Pro and Codex adversarial investigations with `EXHAUSTED` outcomes. These AI audit records do not constitute human peer review.

## Relation to the other proof

The [low-temperature proof](../low-temperature/README.md) studies **the connected susceptibility in an ordered pure phase** and uses the complete **even-particle** expansion instead. The high-temperature theorem is not inferred from low-temperature duality and does not use the low-temperature final natural-boundary theorem; both developments reuse the same underlying mathematical library.

[中文说明](README.zh.md) · [Repository home](../README.md)

## Publication and citation

The author-identified [publication manuscript PDF](../paper/ht/publication/manuscript.pdf)
and [TeX](../paper/ht/publication/manuscript.tex) are a separately identified editorial
edition. The [frozen audited manuscript](../paper/ht/frozen/manuscript.pdf) remains
unchanged; [the editorial record](../paper/ht/publication/README.md) identifies every change.
Cite the [high-temperature result](CITATION.cff) separately from the
[low-temperature result](../low-temperature/CITATION.cff).

Lean code: [MIT](../LICENSE). Author-created manuscript and documentation:
[CC BY 4.0](../LICENSE-DOCUMENTATION.md).

[Publication identities, exact verification and independent audit attachments](PUBLICATION.md).
