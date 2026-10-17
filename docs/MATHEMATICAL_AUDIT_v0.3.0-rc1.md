# Internal mathematical audit of the upgrade

**Verdict:** the implemented improvements survive the internal attacks described below. E3 is removed from the actual canonical formal chain. The physical conclusion remains conditional on E1/E2. This is an audit by the implementing AI, not an independent external certification of the entire pre-existing natural-boundary proof.

Scope: manuscript v0.1-rc5 / Lean v0.3.0-rc1, mathematical source commit `a79c2f5701111b5234bbc0ff8481e75aec8c21d0`, with exact later verification inputs in [VALIDATION](../release/next/VALIDATION.json). The clean final sequence completed on 16 October 2026 at 20:19:27 UTC (17 October in Hong Kong). Its compiled axiom traversal covers 9,225 safe project declarations; the official fresh kernel replay passed. These facts verify formal executions, not the truth of an informal correspondence merely by compilation.

## Claim inventory and decisive attacks

| Claim | Attempt to break it | Result and scope |
|---|---|---|
| C0: actual lower even orders can be bounded internally | Include every active-factor combination, especially one product coefficient only; keep the literal offsite integral and its numerator; check radius/derivative quantifiers and finite common thresholds. | Closed. `nonNickel_active_separated` and the generalized complement IBP prove `nonNickel_fixed_radius_radial_bound`; actual lower-order and final endpoints use this route. |
| C1: branch–compact `1+C/N` on the protected disk | Move the branch by its square-root modulus, cross support transitions, let the perturbed compact root leave the disk, approach denominator zeros. | Closed. Keep the actual disk-point branch root fixed and move only the compact radial-center root. Baseline Lean already attaches this stronger bound to the actual supports/disk. |
| C2: factorial evaluation of the same single-chart amplitude | Recompute the mean-coordinate Jacobian, hyperplane polar exponent, powers of two, beta/gamma cancellation, angle sign and derivative-versus-function coefficient. | Closed for the specified identities. Gaussian moment determinants and an independent direct N=2 integral corroborate the derivation. No unconditional identification of the review's complete printed observable is claimed. |
| C3: agreeing smooth extensions are impossible on every arc | Avoid the false implication “real smooth implies holomorphic”; check finite prime selection, both axis gaps, symmetry and physical prefactors. | Closed with an analytic all-arc proof and actual selected-point real Ck formal counterpart. Finite-prime geometry and the physical quantitative arc statement are manuscript-only. |
| R0: exact uniform finite constant `80*pi^2` | Test the largest permitted finite prime at an arc near the real axis, with exact rational error control. | Rejected as a covering shortcut for this family. The adopted finite bound is different; the leading 80 is only asymptotic. |

### C0: the smallest load-bearing cut set

The critical analytic bridge is not a new predicate saying that lower orders are bounded. It is an estimate on `doubleFormFactor N r`, followed by the existing radius-locality interface to the actual exterior form factor.

The geometry was derived from the original active vectors. Pair coefficients vanish by the imaginary-coordinate balances on the unit torus. A positive product coefficient forces strictly lower coordinates with positive dispersion weights. With both products positive, strict ratio injectivity forces constant tuples, whose products are one. With just one product positive, the other coordinates must be +1: the -1 alternative contradicts the positive dispersion level. That case also yields an Nth-root Nickel equation. If neither product is present, dispersion-only coefficients vanish because `0<S<2` excludes two real unit coordinates. Non-Nickel therefore makes every nonnegative zero combination trivial, supplying a convex separator.

The generalized analytic core keeps the source contours, smooth angular partition, damped auxiliary exponentials, inactive factors and all generated coefficient derivatives. For ell active variables and j parameter derivatives, q=ell+j+1 IBP steps leave an integrable radial `R^-2 dR` tail. Small R is bounded separately. A finite torus cover supplies the bound for weight one. No differentiation through an epsilon-dependent radius occurs: choose r at the evaluation point, differentiate the fixed-r analytic function in a genuine neighborhood, and then use radius independence. Finite order/derivative windows share the minimum of finitely many positive thresholds.

Prime arithmetic supplies the required non-Nickel facts for each lower even N. The separate onsite bound and exact full-site identity are preserved. The replacement estimates the offsite object directly, so a factor-of-two transfer cannot hide a different observable.

The compiled `InternalRegularity.lean` traversal checks types **and** proof values of FIRST, normalized NB and physical NB. It bans E3 and the published full-site transfer route, and requires the internal separator, global complement bound and radial bound to be reachable. A counterfixture with an unused E3 hypothesis on an otherwise valid NB wrapper was rejected with the required diagnostic and unchanged input identities. Thus the standard axiom union is not being mistaken for a check of explicit hypotheses. Exact final endpoint applications retain the original conclusions and domains.

The method is a reconstruction of an acknowledged precedent, [Tracy–Widom 2014](https://www.math.ucdavis.edu/~tracy/selectedPapers/2010s/CV100.pdf), not a claim of discovering nonstationary integration by parts. Only the radial consequence needed by the canonical proof is reconstructed; the stronger published neighborhood-uniform theorem is not silently asserted.

### C1: denominator and support stress test

For a compact center root z0 in the lower closed unit disk away from ±1, compactness gives g>0 such that either `|z0|<=1-g` or `Im(z0)<=-g`. For every branch w in that half-disk, `|1-z0*w|>=g`. In the imaginary-gap case the exact square identity

```text
|z0|^2 |1-z0*w|^2
 = (|z0|^2 Re(w)-Re(z0))^2 + (|z0|^2 Im(w)+Im(z0))^2
```

gives the bound. Compact motion `|z-z0|<=L/N` leaves the other denominator at least g/2. The exact Schur difference then costs at most `4L/(g^2 N)`. This permits z to leave the unit disk. It does not require a branch-motion Lipschitz bound. Actual branch membership follows from the positive W-imaginary margin, including transition supports. `selected_actual_pair_bounds`, its indexed pair motion and root-image attachments were inspected; a free abstract Schur inequality alone was not treated as that attachment.

Three exact polynomial identities and 5,000 seeded samples in a larger half-disk domain passed. The samples are diagnostic, whereas the all-support attachment is formal. Downstream estimates already allowing a weaker inflation remain valid.

### C2: independent normalization calculation

Hermite orthogonality gives the Gaussian Vandermonde integral `(2*pi)^(N/2) product(m!,m=1..N)`. The orthogonal mean coordinate contributes `sqrt(2*pi)` and the coordinate measure on the zero-sum hyperplane differs from Euclidean measure by `sqrt(N)`. Its radial exponent is `N^2-2`; its Gaussian radial integral is `2^(a0-1) Gamma(a0)`. This recovers exactly the C_N used by the existing shape integral, rather than assigning a new normalization to it.

Substitution into the beta period cancels `k!`, `Gamma(a0)` and the angle-dependent powers of sin(beta). The remaining powers of two give `product(m!/2^m,m=1..N-1)`. The continuation contributes `exp(i*pi*a0/2)`, while differentiation contributes `(-1)^k exp(-i*k*theta)`. These are the factors in (B.1). An independently executed N=2 direct integral uses tau=(t,-t), its actual Jacobian and Vandermonde `4t^2`; it agrees with the reduced beta integral to relative error below 1.3e-81.

For the original radial power, `A_chart=L_beta exp(i*k*theta) sqrt(pi)/Gamma(a0)`. Since k is odd for even N, the principal-power expression R copied from the review obeys `A_chart=R(-theta)=-i R(theta)`. The source read was [arXiv:1203.1456v1](https://arxiv.org/pdf/1203.1456), 7 March 2012, (67)–(70), printed p.12. The publisher page could not be fetched. Its cosine equation does not choose the angle sign, continuation of the half-integral power, or total-chart convention. The review's whole printed amplitude is consequently not equated to the internal total by a multiplicity guess.

Internal totals are separately justified: offsite two charts, full-site four, then the actual magnetization and inverse-temperature factors for the physical observable. The original positive-period nonvanishing proof remains. Exact moment determinants at N=2,4,6,10,22,26 and 80-digit comparisons at N=22,26,34,58 passed; neither finite list proves the general formula. The Hermite derivation is manuscript-only.

### C3 and R0: regularity and finite covering

A genuine real Ck extension supplies continuous kth real Fréchet derivatives on a neighborhood. Agreement on the exterior identifies their evaluation with the kth complex derivative of the holomorphic bulk there. Its norm is bounded approaching the boundary, contradicting the established nonzero square-root-scaled limit. The formal proof uses restriction of scalars; it never infers complex analyticity of the extension.

For finite p, adjacent admissible angles have interior gaps below 3h/2, initial argument at most `sqrt(5/2)h`, and final distance to pi/2 at most 5h/4. Sign/conjugation images therefore have every circular gap at most `sqrt(10)h`. Prime choice precedes the point-dependent constants. Bertrand gives the finite ceiling in Corollary 9.4. The optional PNT argument supplies a leading 80 with an o(1), not an exact finite ceiling.

The obstruction to the proposed shortcut is an exact rational calculation: Machin bounds for pi and alternating Taylor bounds show that an arc of length 8/5 around +1 misses every p=11 selected image, whereas the proposed ceiling lies strictly between k(11)=241 and k(13)=337. The minimum positive selected angle at p=11 is the (1,2) pair, so this is not just a numerical sample of an incomplete family. This certificate rejects that covering inference; it does not refute a possible stronger theorem using another method. The general adopted geometry is analytic; checks for 91 primes through 499 are corroboration only.

## Residual register

| Item | Classification | Disposition |
|---|---|---|
| Actual lower-order observable, fixed-radius derivatives and canonical reachability | CLOSED | Analytic construction, formal proofs, type/body traversal and unused-premise rejection. |
| Schur support/disk attachment | CLOSED | Existing actual formal pair theorem plus the independently checked difference proof. |
| Hyperplane Jacobian, beta period and internal chart multiplicities | CLOSED | Displayed derivations and independent low-dimensional/exact algebra checks; old nonvanishing retained. |
| Exact finite 80 shortcut | CLOSED-FAIL | Rejected; absent from adopted claim. |
| Selected-point real regularity obstruction | CLOSED | Actual canonical formal endpoint, with TAIL internally discharged. |
| All-arc finite geometry / factorial export | CLOSED at stated manuscript scope | Analytic proofs completed; no Lean export advertised. |
| Review's complete printed amplitude convention | OPEN-BLOCKED for a stronger, unclaimed identity | Source sign/power/multiplicity is not specified; matching it would require additional source evidence. It is not used by the proof. |
| Physical E1/E2; dependency-cache/kernel trust | Retained explicit boundaries | Not new unproved internal lemmas. No fresh probabilistic reconstruction or second kernel is claimed. |
| Whole unchanged baseline analytic correspondence | Retained baseline scope | Fresh full build/replay, but no assertion of a new independent human rederivation of every old estimate. |
| Human review / exhaustive priority | Not performed | No independent certification or novelty claim is made. |

The separate [repository consistency audit](CONSISTENCY_AUDIT_v0.3.0-rc1.md) reconciles versions and evidence. Raw executed commands, outputs and failed attempts are retained in the validation archive. The labels below apply to this bounded upgrade claim set and its stated retained assumptions.

```text
AI THEORETICAL-PHYSICS ADVERSARIAL AUDIT A1v2

ORIGINATING RUN STATUS:
NOT APPLICABLE

AUDITED CLAIM SET:
C0 internal lower-order replacement; C1 protected-disk Schur improvement;
C2 specified single-chart factorial/phase identities; C3 real regularity;
R0 proposed exact finite covering constant.

CENTRAL CLAIM VERDICT:
SURVIVES INTERNAL HOSTILE AUDIT

AUDIT COMPLETENESS:
INTERNALLY EXHAUSTED

STRONGEST SURVIVING RESULT:
Canonical FIRST and both natural-boundary endpoints use the internally proved
actual lower-order contour bounds and have no transitive E3 dependency.
The physical endpoint retains E1/E2.

STRONGEST SURVIVING RESULT CLASS:
SPECIALIST STRUCTURAL

FAILED-RUN MAJOR BYPRODUCT SURVIVED:
NOT APPLICABLE

LOAD-BEARING CUT SET:
Non-Nickel active-vector classification; source IBP integrability;
fixed-radius locality; actual canonical composition; phase/Jacobian;
real-derivative restriction; finite-prime axis gaps.

FIRST FATAL OR LOAD-BEARING RISK:
The single-product active combination and the fixed-radius derivative interface.
Both were closed before finalization.

FATAL FLAWS FOUND:
The proposed uniform finite 80*pi^2 covering shortcut fails. It was rejected.
No fatal flaw was found in the adopted upgrade claims.

UNRESOLVED LOAD-BEARING RISKS:
No newly introduced unproved internal lemma. E1/E2 and the explicitly retained
baseline/kernel/cache trust boundaries remain; this is not an independent
certification of the complete unchanged baseline analytic proof.

HIGHEST-PRIORITY AUDIT RESIDUAL:
NONE

AUDIT RESIDUAL STATUS:
CLOSED-PASS

HARD STOP CLASS:
NONE

BRIDGE ATTEMPTS ON BLOCKED RESIDUAL:
NOT APPLICABLE

UNTRIED ACTIONABLE AUDIT STEP:
NONE

SOURCE-SCOPE STATUS:
SCOPE MATCHED

PHYSICAL ADMISSIBILITY:
PARTIAL

EVIDENCE PROVENANCE FOR DECISIVE NODES:
Actual manuscript derivations and compiled project declarations;
exact type/body dependency controls; executed clean build, axiom traversal,
18 endpoint checks and official fresh kernel replay; exact finite algebra
and rational certificate; separately identified numerical corroboration.

INDEPENDENT RE-DERIVATIONS:
Original active-vector balances; compact-only Schur displacement;
Hermite/mean/hyperplane normalization; direct N=2 shape integral;
real Ck obstruction; finite-prime axis geometry.

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
NOT ASSESSED

REPAIR NEEDED FOR ORIGINAL CLAIM:
NONE

EXTERNAL VALIDATION:
NOT PERFORMED

NEXT STEP AFTER INTERNAL AUDIT CLOSURE:
Independent specialist review of the candidate, with the retained physical
premises and manuscript-only exports explicit.
```
