# Original-session failure and repair ledger

This table records **27 distinct error types, failures of proposed estimates, or missing proof obligations** documented in the *original* Codex session. It is **not** a count of independent full attempts, nor the number of issues identified during all later adversarial audits. A proposed repair in these old notes was an **initial-session candidate**, not necessarily a certified theorem. For the archival source see [original-session retrospective, Section 34](original-session/ising_project_complete_history_2026-10-10.md).

| ID | Original shortcut, assertion or plan | Why it failed or remained unproved | Recorded response |
|---|---|---|---|
| F01 | Dense singularities of individual terms imply natural boundary for whole sum | Infinite-order cancellation or nonuniform limit possible | Require nonzero first carrier plus differentiated uniform tail |
| F02 | All higher-order Nickel amplitudes decrease | Near-critical prime channels show growth | Withdraw generalization; return to exact integrals |
| F03 | Fixed-N local expansions can be summed | Neighborhoods, remainders and neighboring singular points vary with N | Seek simultaneous N/epsilon majorants |
| F04 | Estimate original integrand by worst pointwise absolute value | Mixed branch configuration incurs inverse epsilon powers | Use deformation and transported derivatives |
| F05 | Multiply worst-case bounds for every pair | Loses Pfaffian, matching, angular integration and collision suppression | Retain exact complete-pair algebra and weighted L2 |
| F06 | Bound only the safely deformed final contour | Scanning currents and crossed residues remain | Retain exact residues, Stokes currents or IBP on original contour |
| F07 | Shrink transition zone to remove cutoff costs | Cutoff derivatives and Jacobians can cancel volume gain | Explicit full transition and designated anchors |
| F08 | Reflect upper inward deformation to lower branch | Lower compact test sends continuation root outside disk | Analyze upper and lower geometry separately |
| F09 | Reuse half-disk pair bound in complex parameter disk | Roots and pairs leave favorable half-disk/slightly exceed one | Quantify analytic perturbation and group contraction |
| F10 | Rechoose principal root at final contour | Can silently change analytic sheet | Track continuation from original contour |
| F11 | Negative outward shift supplies linear attenuation gain | First-order gain may vanish | Use pre-existing absolute attenuation |
| F12 | O(delta) correction preserves quadratic variance gain | Error dominates a smaller shape-quadratic benefit | Exact curvature/monotonicity estimates |
| F13 | Split positive/negative sides before IBP | Artificial branch boundary term may be singular | Differentiate on a smooth common contour first |
| F14 | Max shell radius bounds derivatives of every variable | One variable may stay at epsilon branch scale | Explicitly withdrawn; transport root movement |
| F15 | Small coupling P makes every high derivative small | Branch derivatives amplify and defeat naive perturbative control | Exact rank-one field or Stokes retraction |
| F16 | Complex-modulus maximum-pair cutoff is holomorphic | Depends on complex conjugates | Real-angle rational weights plus jet induction |
| F17 | Weak extremal pair Jacobian is sufficient | Fails to absorb minimum-angle branch measure | Prove stronger extremal Jacobian |
| F18 | Tail compact-R coarea controls first carrier | At N=N0 radial exponent reaches -1/-2 | Separate first-carrier physical mean-residue method |
| F19 | Gaussian vanishing-cycle model nonzero means physical coefficient nonzero | Unknown physical intersection number; other charts possible | Actual physical contours, ordered-chart phase and classification |
| F20 | Factor-two amplitude ratio proves two saddles | Conflates normalization, onsite grouping and paths | Withdraw inference; compare complex densities |
| F21 | Joint absolute dominated convergence for first mean-angle/shape scaling | Moving Z-pole ridge prevents integrability | Integrate mean-angle Y-residue before shape limit |
| F22 | Endpoint-adjacent branch compact set has strict q<1 | Exact pair modulus equals one at endpoints | Fixed exclusion gap and ordered constants |
| F23 | Non-root-of-unity gives N-independent separation from one | Powers may approach one arbitrarily closely | Resultant exponential gap and N-dependent microcore |
| F24 | Near-equality constants are only exp(O(N²)) | O(N²) pairs can each cost exp(O(N)) | Budget exp(CN³) before choosing exponential radius |
| F25 | Finite-cylinder dense singularities pass into plane limit | Zero-particle term and disappearing jump/near-boundary limit | Subtract tunneling term; demand quantitative jump/transfer |
| F26 | First-order overlap check controls all k derivatives | Higher cutoff jets can leave supports or change costs | Finite-order pole+jet induction and support ledger |
| F27 | Internal fresh rederivation equals outside certification | Model/session correlations and hidden common assumptions remain | Label outcome provisional; request genuinely independent review |

## Representative falsifiable regressions

- **Mixed scales (F14):** A configuration with `u_1=R >> epsilon` and `u_2=0` defeats a proposed `1/R` bound on branch derivatives; see archival `PLUS_BRANCH_NARROW_TAIL.md`.
- **Complex-disk leak (F09):** Recorded root and pair magnitudes around `1.0000003` and `1.0000093` falsify a universal modulus-at-most-one shortcut in that geometry; see `DYADIC_COMPLEX_DISK_AUDIT.md` and `dyadic_complex_probe.py`.
- **Endpoint equality (F22):** Complete pair moduli at branch/endpoint combinations can be exactly one; see `PAIR_COMPACTNESS_ENDPOINT_EQUALITY_AUDIT.md`.
- **N-cubed constants (F24):** Exponential slope loss per pair compounded over quadratically many pairs invalidates an automatic exp(O(N²)) claim; see `NONRESONANT_BRANCH_HOSTILE_AUDIT.md`, later `TWO_NONZERO_G3_FRESH_COAREA_PROOF.md`.

Some rows represent **disproved intermediate inequalities** (for instance F09, F14, F22), while others represent **a missing proof bridge or insufficient argument** (for instance F01, F03, F19, F25). Do not report all as rigorous counterexamples. Historical code and calculations are diagnostic, not continuous-domain proofs.

## What happened *after* the initial session

For **new** defects or repairs in later manuscript versions, consult the independent [audit-version ledger](../audits/VERSION_LEDGER.md), [W1 repair record](../provenance/W1_REPAIR_AUDIT.md), [W2 repair record](../provenance/W2_REPAIR_AUDIT.md), and [v0.2.1 Lean remediation](../REMEDIATION_v0.2.1.md). These are deliberately **not** merged into the 27 original-session categories. An historical `repair` is not presumed valid merely because a later version passed an AI audit or Lean replay.
