# HT manuscript-to-Lean map

| Mathematical step | HT-1.0 source | Lean namespace / entry |
|---|---|---|
| Exact published real-temperature angular representation | §2, (2.1)–(2.2) | `IsingBulk.HT.Final.PublishedAngularInput` |
| Physical coefficients and full lattice sum | §2 | `IsingBulk.HT.Contour.PhysicalAngular`, `PhysicalLatticeSummation`, `PhysicalAngularIdentification` |
| Odd prime selection and nonzero FIRST coefficient | §§3–5 | `IsingBulk.HT.First` (positive/negative first families) |
| Signed weighted contour deformation, including current | §6 | `IsingBulk.HT.Contour.SignedRetraction` |
| High-order Lie and coarea analysis | §§7–9, Appendix A | `IsingBulk.HT.Lie`, and reusable `IsingBulk.First` / `IsingBulk.Tail` bridge lemmas |
| Unbounded positive odd-particle tail, including onsite | §10 | `IsingBulk.HT.Tail.FullOddTailAssembly` |
| Full-series noncancellation | §10 | `IsingBulk.HT.Final.PositiveFullNoncancellation`, `NegativeFullNoncancellation` |
| Disk analyticity, inverse temperature, whole-circle obstruction | Theorem 1.1 | `IsingBulk.HT.Final.InteriorFullGerm`, `PublishedPhysicalTheorem` |

The frozen Lean implementation includes multiple proven bounds. On one actual coarea route it retains a *spectator-coordinate* collision exponent `N(N-1) - (2j+1)`, while another proved route has the manuscript's `N² - 2j - 4` budget. The weaker exponent remains strictly positive and closes the same infinite tail after summation. The published top-level theorem is unchanged by this choice of internal route.

The actual HT root imports `IsingBulk.HT` modules and reusable mathematics, **not** the LT natural-boundary theorem. Existing LT source modules are untouched, and the additional 35 bridge modules remain under their frozen module names to retain reproducibility.
