# W1 repair record — v0.1-rc3-unreleased

Prepared 30 September 2026 from repository commit `47f95a386d329ae6a3e377fecceafde78ea0886c` (v0.1-rc2). This is an unreleased local candidate. The rc2 artifacts and historical audit/release records retain their identities.

## Independently rechecked interfaces

A fresh AI analytic review confirmed four substantive gaps or incorrect intermediate statements in the rc2 W1 proof. Prior AI audit verdicts were treated as leads, not premises. The revision adopts:

1. **Lemma 7.1:** an explicit partition of every named small-lambda Stokes current, including cutoff-derivative supports and the upper compact anchor. There is no all-branch current sector.
2. **Proposition 7.6:** the pointwise product of branch slopes costs exp(O(N²)), and its combined collision coefficient has logarithm `(A+4)N³/2 + N² log N/2 + O_j(N²)`. The positive cubic coefficient is fixed before B; the negative `−BN(N²−2j−4)` term dominates it. Finite small-N constants are epsilon-independent.
3. **Lemma 7.2:** suppression after at most j changed factors follows by counting the remaining same-group pairs. The lower-variable count is N for K and N−1 for Stokes. No factor is divided out. Pair jets are bounded in regular branch/compact coordinates, not uniformly in raw branch angles.
4. **Lemma 7.4 and Proposition 8.1:** a lambda-uniform branch normal form, proved with Q=epsilon+tau*t before comparing it to epsilon+t. This permits the real branch-center displacement and gives the mixed Jacobian and negative-branch attenuation bounds.

The revision also replaces the microcore monotone-arm assertion by the direct square-root-kernel integral, expands the final C_j dependencies in Appendix E, and makes the finite simultaneous epsilon0 conditions explicit. Numbered theorem/lemma/proposition and equation identifiers are preserved. The observable, central theorem statements, selected family, derivative range and particle windows are unchanged.

## Corrections to proposed repairs

The review rejected an interpretation that deletes factors by dividing the full-product estimate; removed factors can vanish. It corrected a missing linear term when counting N−1 lower variables in Stokes. A literal quadrant assertion for the deformed branch center was replaced by a controlled cone perturbation. Numerical root calculations do not certify the proposed decimal resultant exponent; no such decimal is used in the manuscript.

## Evidence and limits

The analytic review re-derived pair compactness at endpoints and the double branch, the remaining-pair count, slope/collision costs, the deformed geometry, the direct kernel integral and the constant order. Scoped symbolic and finite numerical checks were executed separately. Finite grids do not establish continuous-domain bounds, and high precision is not interval certification. The old reconstruction outcomes remain historical.

This is AI hostile audit and computational regression, with correlated-error risk. It is not independent human review, peer review or proof-assistant certification. The review does not newly certify the entire natural-boundary theorem, its external physical premises, or novelty. Build, page-index and finite-check receipts are in [candidate validation](../release/W1_CANDIDATE_VALIDATION.json).
