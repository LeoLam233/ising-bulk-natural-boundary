# Fixed-ratio anisotropic Ising susceptibility

**ANISO C001 · every finite positive coupling ratio · both temperature phases**

For horizontal coupling `J > 0` and fixed vertical-to-horizontal ratio `lam > 0`, this result treats the complete bulk susceptibility of the infinite square lattice. The high-temperature observable sums every odd-particle order. The low-temperature observable is the connected plus-phase susceptibility, with spontaneous magnetization squared subtracted, and sums every positive even-particle order. Every lattice separation is retained.

[Read the manuscript](../paper/aniso/publication/manuscript.pdf) · [Exact Lean endpoint](../lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) · [Build and verify](../docs/aniso/BUILD_AND_VERIFY.md) · [Cite ANISO](CITATION.cff) · [中文](README.zh.md)

## The result

With `z = 2βJ`, the correct high-temperature complex domain is a bounded lens, and the low-temperature domain is a right-hand epigraph. For each fixed `lam`, the complete normalized covariance sums and their energy-field normalizations are analytic on their respective domains and have no local analytic extension across **any finite point of the corresponding frontier**. The isotropic value `lam = 1` uses exact full-sum correspondence with the existing LT/HT theorems.

The terminal theorem is `IsingBulk.Anisotropic.full_uniform_field_conclusion`. In addition to the natural boundaries and full-site summability/physical identification, it gives the bilateral high-temperature derivative at zero uniform field and the right-sided low-temperature plus-state derivative. The explicit real-physics inputs are `PublishedRealSpinFormFactors` and `PublishedRealGibbsFields`; their precise content and physical interpretation are in the [physical interface](../docs/aniso/PHYSICAL_INPUTS.md).

## Read and reproduce

- [Proof map and actual theorem type](../docs/aniso/PROOF_MAP.md)
- [Paper editions: frozen 38-page audit, 38-page publication, historical 39-page original](../paper/aniso/README.md)
- [Source identity and hashes](../docs/aniso/VERSION_IDENTITY.md)
- [Build, strict audits and fresh kernel replay](../docs/aniso/BUILD_AND_VERIFY.md)
- [Audit provenance and evidence availability](../docs/aniso/AUDIT_EVIDENCE.md)
- [Publication record](PUBLICATION.md)

The 762 ANISO modules, two frozen roots and additive Lake configuration come byte for byte from the supplied C001 inner archive. Shared LT/HT source is reused in place. The [publication closure audit](../lean/AuditAnisotropicClosure.lean) and publication tooling are separate additions.

Author: **Dehao Lin**, School of Physics, Sun Yat-sen University; [ORCID 0009-0001-4551-8490](https://orcid.org/0009-0001-4551-8490); lindh9@mail2.sysu.edu.cn. Source: [MIT](../LICENSE). Author documents: [CC BY 4.0](../LICENSE-DOCUMENTATION.md).
