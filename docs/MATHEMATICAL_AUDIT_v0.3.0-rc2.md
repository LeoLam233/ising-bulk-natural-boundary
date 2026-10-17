# Scoped adversarial audit of the complete-amplitude conversion

The proposed equality between the unscaled printed scalar and the complete susceptibility amplitude fails by a magnitude factor four on the selected family. The replacement result in Proposition F.1 survives the internal checks described here:

`A_full=4R_N(-theta_*)=-4iR_N(theta_*)`, with the stated principal powers and the physical exterior germ. This is a conversion, not an assumption of equality. The natural-boundary proof and original nonvanishing argument are unchanged.

This audit applies to manuscript rc6 / Lean v0.3.0-rc2. It is an AI internal audit of the changed normalization result, not an independent human certification of the entire retained bulk proof. The verified predecessor and its original reports remain at `dd977048`. [Mathematical derivation and source access](AMPLITUDE_IDENTIFICATION_v0.3.0-rc2.md), [version identities](VERSIONS.md), and [executed validation](../release/next/VALIDATION.json) separate those scopes.

## Claim inventory and dependency cut set

| Claim | Exact scope | Verdict |
|---|---|---|
| A0 | The single printed right-hand side, with any angle sign/power branch allowed by the displayed cosine relation, is already the complete selected-family normalized full-site amplitude. | KILLED: its magnitude is one quarter of the complete coefficient. |
| A1 | The specified exterior coefficient is four times the inverse-angle principal scalar, with the positive-angle conversion `-4i`. | STRONG INTERNAL RESULT within the selected distinct nonzero-angle family. |
| A2 | The lower double-contour, full offsite lattice, full-site, normalized physical and physical amplitudes have the factors in Proposition F.1. | SURVIVES INTERNAL HOSTILE AUDIT. |
| A3 | Integrating the existing kth radial derivative asymptotic gives the stated first fractional power modulo a finite radial Taylor polynomial. | SURVIVES INTERNAL HOSTILE AUDIT. No convergent full Taylor expansion is asserted. |

The smallest load-bearing cut set is the full observable normalization, root branch, constrained shape measure, scalar phase, complete chart sum, and radial-coordinate conversion. A missing factor, an unassigned square root, or an incomplete same-order sum at any one node would defeat A1/A2. Compilation cannot decide these literature/convention questions.

## Attacks and closure

**Observable mismatch.** The review's low-temperature (45) has the magnetization factor outside its particle sum. Its cited Orrick et al. integral has the full torus and the exact factorial/measures/pair factors used here. Boukraa et al. gives the same integral with explicitly matched variables, including the numerator `2w` in its one-body factor. This excludes treating the review's full observable as a quarter-torus or single-chart definition. An independent N=2 quadrature agrees with the published elliptic expression at three real low-temperature values to more than 75 digits; that diagnostic corroborates the literal all-N formula match and does not replace it.

**Wrong square root or continuation side.** The exterior upper-quadrant ray has `Im S>0`. The root `1/(W+sqrt(W-1)sqrt(W+1))` is continued from the physical positive real root, cannot cross `|z|=1` in that half-plane, and has negative imaginary part. Its limit fixes `gamma=i beta`. This proves the phase convention; a finite root sample is only a check. Inverse temperature and magnetization have separately stated physical branches.

**Hidden Jacobian/factorial.** The constrained measure has `tau_N=-sum(tau_i)`. Its `1/sqrt(N)` hyperplane conversion is already in the Gaussian angular constant. The direct angular prefactor is `2pi K_beta`, including the numerator two and all one-body and squared-pair phases. The product phase is exactly one for even N. Particle permutations fix an all-equal center and do not supply another factorial.

**Missing signed charts or cancellations.** Both signs of each of the two distinct angles satisfy the periodic constraint. Reversal preserves the real measure; exchanging the angles leaves (B.1) unchanged. All four contributions therefore agree in phase. The complete sum is independently fixed by `C_N^std=f00^(N)+2T_N`, the proved two-chart asymptotic for T_N and the bounded onsite derivatives. Thus the result does not depend on an unproved assertion that an angular complement contributes nothing. Exact cyclotomic enumeration at p=11 verifies one full finite instance; the general completeness uses the stated analytic/prime-family results.

**Branch changes as a putative missing factor.** The exponents are real half-integers and H is positive. All branches of the displayed powers have equal magnitude. Angle reversal changes phase, not the factor-four magnitude discrepancy. Substitution into the Hermite-evaluated coefficient gives `A_chart/R_N(theta_*)=-i` and `A_chart/R_N(-theta_*)=1` analytically. A second normal-form derivation uses polynomial division and a continued arctangent rather than the differentiated beta period, and obtains the same phase and magnitude. These are independent local coefficient routes sharing the explicitly retained finite-jet/remainder bounds; they are not two independent reconstructions of the entire bulk proof.

**Local-variable and integration constants.** The review's low-temperature variable is `delta=epsilon/(1+epsilon)`, with first derivative one. It cannot absorb a phase or multiplicity. The kth radial derivative is integrable at zero, so lower endpoint derivatives exist. The integral Taylor remainder gives the fractional coefficient `B sqrt(pi)/Gamma(k+1/2)` and controls the little-o. Constants of integration are precisely the radial polynomial terms. A general coordinate change carries its explicit continued Jacobian power.

**Physical normalization.** The full offsite normalized particle coefficient is `2T_N`, while T_N denotes the lower double-contour coefficient. The onsite subtraction is smooth here. The normalized physical bulk multiplies by M² and physical chi multiplies by beta_phys M². The already established lower-order and all-j tail bounds make product-rule terms of lower derivative order negligible. No high-temperature `1/s` factor is imported into this even low-temperature comparison.

## Residual ledger and evidence provenance

| Residual | Decisive evidence | Status |
|---|---|---|
| R1: same observable | PRIMARY SOURCE: journal review (45), its cited Orrick et al. (1.10), (3.13), (3.17)–(3.20); Boukraa et al. (4)–(9). AUDITOR RE-DERIVED variable substitution and full prefactor. | CLOSED-PASS |
| R2: branch/phase/volume | AUDITOR RE-DERIVED root continuation, implicit derivatives, Hermite measure, beta-period substitution and direct radial arctangent. TOOL-EXECUTED exact identities and phase samples. | CLOSED-PASS |
| R3: complete same-order sum | Retained proved FIRST/onsite identity plus signed angular calculation. TOOL-EXECUTED exact p=11 enumeration. | CLOSED-PASS |
| R4: radial function/physical conversion | AUDITOR RE-DERIVED integral Taylor remainder, unit first-order coordinate change and physical analytic factors. | CLOSED-PASS |
| R5: literal unscaled equality | Four equal chart coefficients and unchanged power magnitudes. | CLOSED-FAIL |

The general mathematical conversion has no remaining actionable internal residual. The original Nickel 1999/2000 publisher text could not be read: normal retrieval returned a challenge page, including in the browser. No challenge was solved, and no intended original-paper convention or error is attributed. This is a historical-attribution access limit, not an unresolved node in the proved comparison of the inspected scalar and its cited full observable. No claim covers degenerate endpoints, odd orders, other continuation sheets, or exhaustive priority.

Nine exact symbolic identities, one exact finite cyclotomic enumeration, three 90-digit quadratures and specified phase/root samples were actually executed. Their raw streams and result files are in the current validation archive. The broader six historical diagnostics and rc5 mathematical scripts are rerun separately. Lean acceptance checks the retained formal theorems against the new source identity; Proposition F.1, the factorial identity and radial Taylor reconstruction are explicitly manuscript-only.

```text
AI THEORETICAL-PHYSICS ADVERSARIAL AUDIT A1v2

ORIGINATING RUN STATUS:
NOT APPLICABLE

AUDITED CLAIM SET:
A0 unscaled complete-amplitude identification; A1 four-chart conversion; A2 observable/physical factors; A3 radial Taylor reconstruction

CENTRAL CLAIM VERDICT:
KILLED

AUDIT COMPLETENESS:
INTERNALLY EXHAUSTED

STRONGEST SURVIVING RESULT:
On the selected physical exterior germ, A_full=4R_N(-theta_*)=-4iR_N(theta_*), with the exact offsite/full-site/physical factors and the stated branches.

STRONGEST SURVIVING RESULT CLASS:
SPECIALIST STRUCTURAL

FAILED-RUN MAJOR BYPRODUCT SURVIVED:
NOT APPLICABLE

LOAD-BEARING CUT SET:
Full observable; physical root; constrained measure; scalar phase; signed chart sum; radial coordinate and Taylor remainder.

FIRST FATAL OR LOAD-BEARING RISK:
The printed scalar does not include the fourfold complete chart sum in the specified conventions.

FATAL FLAWS FOUND:
A0 misses a magnitude factor four. This does not invalidate the retained natural-boundary proof or nonvanishing argument.

UNRESOLVED LOAD-BEARING RISKS:
NONE for A1-A3 within their stated scope.

HIGHEST-PRIORITY AUDIT RESIDUAL:
NONE

AUDIT RESIDUAL STATUS:
NONE

HARD STOP CLASS:
NONE

BRIDGE ATTEMPTS ON BLOCKED RESIDUAL:
NOT APPLICABLE to the completed mathematical comparison. Historical access failures are separately recorded without attributing an original Nickel convention.

UNTRIED ACTIONABLE AUDIT STEP:
NONE

SOURCE-SCOPE STATUS:
SCOPE MATCHED

PHYSICAL ADMISSIBILITY:
VERIFIED INTERNALLY

EVIDENCE PROVENANCE FOR DECISIVE NODES:
Directly inspected primary review and integral sources; auditor-derived branch, phase, measure and radial identities; tool-executed symbolic/finite/precision checks; retained stated analytic remainder and tail results.

INDEPENDENT RE-DERIVATIONS:
Direct angular normal form and radial arctangent versus the retained double-contour mean residue and differentiated beta period; N=2 full angular integral versus the published elliptic representation.

COMPUTATIONAL REPRODUCTION:
EXACT FINITE CERTIFICATE

ASYMPTOTIC / PERTURBATIVE CONTROL:
CONTROLLED ASYMPTOTIC

FIXED-THEORY VS FAMILY-OF-THEORIES STATUS:
FIXED THEORY ESTABLISHED

SAME-ORDER COMPLETENESS STATUS:
ESTABLISHED

NOVELTY STATUS:
NOVELTY NOT CLEARED

SIGNIFICANCE STATUS:
NOT PAPER CORE

REPAIR NEEDED FOR ORIGINAL CLAIM:
Replace the unscaled complete-amplitude equality by the four-chart sum and specify the physical branch and local coordinate.

EXTERNAL VALIDATION:
NOT PERFORMED

NEXT STEP AFTER INTERNAL AUDIT CLOSURE:
Independent expert review of the scoped normalization result and retained bulk candidate.
```
