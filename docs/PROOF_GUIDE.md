# Reading manuscript v0.1-rc5 and Lean v0.3.0-rc1

[Candidate PDF](../paper/next/manuscript.pdf) · [Current labels/pages](../paper/next/LABEL_INDEX.json) · [Version identities](VERSIONS.md). All 65 previous mathematical label numbers remain unchanged.

| Stage | Manuscript | Actual interface |
|---|---|---|
| Physical identification | §2, Appendix F | E1/E2, real low-temperature data and local inverse-temperature sheets. |
| Dense first-order family | Theorem 3.1 | First even Nickel order and exact non-Nickel facts below it. |
| Whole first singularity | Theorem 4.4, Lemma 4.3 | Actual residues, nonzero coefficient, bounded lower derivatives and compatible remainder. |
| Internal lower orders | Unnumbered argument before Theorem 4.4 | NonNickelGeometry → generic complement IBP → NonNickelRadialBounds → lower-order endpoints. No E3. |
| Selected contour | Proposition 6.1 | Actual protected `c/N` disk and `1+C/N` pair bound, already present in baseline Lean. |
| Entire higher tail | Theorem 9.1, §§5–8, Appendices C–E/G | Existing complete contour and all-j absolute-tail assembly. |
| Final composition | Theorem 9.2, Corollary 9.3 | Canonical NB endpoints with lower-order and tail estimates discharged internally. |
| Regularity | Corollary 9.4 | Genuine selected-point real Ck obstruction formalized; quantitative prime covering manuscript-only. |
| Closed amplitude | Appendix B (B.1), Appendix F | Factorial evaluation manuscript-only; existing formal nonvanishing retained. |

```mermaid
flowchart TD
 A[Selected prime arithmetic] --> L[Internal lower-order bounds]
 A --> F[Whole first singularity]
 A --> T[Absolute all-j higher tail]
 P[Exact FKS contours and pair/Lie estimates] --> T
 L --> N[Bulk noncancellation]
 F --> N
 T --> N
 N --> B[Normalized natural boundary and selected Ck obstruction]
 E[E1/E2 real physical identification] --> H[Physical natural boundary]
 B --> H
```

For E3, read the coordinate balances and `ActiveCombination.nickel_of_productX_pos` / `zero_of_nonNickel`. The single-product case matters: the other coordinates are +1, hence it too yields a Nickel equation. The analytic core retains actual smooth weights, denominators, half-line exponentials, generated IBP coefficient derivatives, derivative interchange, finite torus refinement and radius locality. The radius is selected at the evaluation point and held fixed while differentiating. The stronger published neighborhood-uniform proposition is not claimed as an internally proved substitute.

For Proposition 6.1, hold the branch root at its complex-disk value and move only the compact radial-center root. Its denominator stays uniformly separated from the closed lower disk. Existing actual root-image theorems cover transition supports and strict same-group contraction. The weaker downstream square-root inflation remains a valid budget.

For the amplitude, distinguish `L_beta` (one chart's kth complex derivative) from `A_chart` (its radial singular-power coefficient). Offsite/full-site totals have multiplicities two/four. Inverse angle and principal power in the review comparison are specified, not inferred from its cosine equation.

For regularity, an agreeing real smooth extension on a neighborhood is stronger than a boundary trace. The formal proof restricts complex Fréchet derivatives to real scalars; it does not assume a smooth extension is holomorphic. The finite prime precedes point-dependent constants and limits.

Historical W1/W2 repairs and CR0/MR1 failures retain their [original scope](VERSIONS.md). [Coverage](../lean/COVERAGE.md), [mathematical changes](UPGRADE_v0.3.0-rc1.md), and [validation](../release/next/VALIDATION.json) govern this candidate.
