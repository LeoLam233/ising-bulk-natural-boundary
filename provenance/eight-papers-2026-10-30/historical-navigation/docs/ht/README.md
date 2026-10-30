# HT-1.0 · Lean 1747

**Object.** The complete zero-field, isotropic, infinite-square-lattice high-temperature bulk susceptibility, from the real physical interval `0 < s < 1` with `s = sinh(2 β J)`, `J > 0`. The normalized function is the entire lattice correlation sum, with all positive **odd** form-factor orders, and the physical susceptibility retains the factor `β = arsinh(s)/(2J)`.

**Mathematical theorem.** The physical high-temperature germ has an analytic representative on `|s| < 1` and cannot be continued holomorphically across any point of `|s| = 1`.

**Lean theorem.** `IsingBulk.HT.Final.publishedPhysicalSusceptibility_germ_natural_boundary` in [`PublishedPhysicalTheorem.lean`](../../lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean).

**External physical interface.** `PublishedAngularSusceptibilityRepresentation` is the exact published **real-temperature** full-bulk odd-particle angular representation. FIRST, TAIL, contour identities, series convergence, disk analyticity and the natural-boundary conclusion are proved internally; the endpoint does not depend on the LT final natural-boundary theorem.

## Navigation

- [Audited, unchanged HT-1.0 mathematical manuscript](../../paper/ht/frozen/manuscript.pdf)
- [Production HT Lean modules](../../lean/IsingBulk/HT/)
- [Building and verifying HT independently](BUILD_AND_VERIFY.md)
- [Proof routes and paper/Lean comparison](PROOF_MAP.md)
- [Source identity and release notes](VERSION_IDENTITY.md)
- [LT companion proof](../lt/README.md)

## Recorded verification

The frozen 1747 project completed a clean build, official fresh kernel replay and internal audits. Two later independent AI investigations (a Pro/coordinated run and a Codex/coordinated run) reported `EXHAUSTED` after compiled-source, theorem-type and mathematical correspondence checks. The Codex run reported four separate project builds and official fresh replays. The full execution artifacts and hash manifests should be attached to a version-specific GitHub Release rather than committed into this proof source tree.
