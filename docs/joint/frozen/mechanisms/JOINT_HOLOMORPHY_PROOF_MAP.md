# JOINT holomorphy and physical-family proof map

Current author integration map, 2026-10-23. This records the mathematical source
correspondence and actual theorem premises. It is not an independent audit,
clean-build receipt, or final verification verdict. Individual development
checks use `coordination/COMPILE_ONE.sh` with Lean 4.34.1 and the copied/shared
development objects. The final source-clean validation remains separate.

## 1. Literal independent-coupling objects

`FormFactors/ComplexContours` defines the full double-contour coefficient for
`Coupling = ℂ × ℂ`, with independent doubled couplings, `S = sinh z`,
`T = sinh w`, `A = cosh z cosh w`, and `p = S*T`. Its multiplier is the literal
full-lattice `(1+X)(1+Y)/(XY(1-X)(1-Y))`, with factorial normalization. The exact
onsite-plus-twice-offsite identity does not omit coordinate axes.

`ContourAnnulus`, `LocalAnnulus`, `KernelBound`, `AnnularHolomorphy`,
`ContourContinuity`, `RadiusIndependence`, `FullLatticeContour`, and `ContourNorm`
prove the geometric annulus, local common contour, contour independence, actual
full-lattice exchange, and absolute summability. A total fallback in the radius
definition supplies no theorem premise; the required annulus is proved on the
actual spectral complement.

`Normalized` defines the actual complete functions with integer powers:
HT has `highPrefactor * Σ p^n * coefficient(2*n+1)`, and LT has
`lowPrefactor * Σ p^(n+1) * coefficient(2*n+2)`. The prefactors are the explicit
principal fourth roots of `1-p^2` and `1-p⁻²`, respectively. Their branches and
positive-real identities follow from the proved modulus geometry. No global
square root of `p` is assumed and no zero-particle vacuum term is inserted.

## 2. Joint holomorphy, all mixed jets, and compact normal convergence

`JointAnalytic`, `CompactIntegral`, and `FiniteHolomorphy` prove genuine complex
Fréchet smoothness of each actual finite coefficient, rather than separate
slice analyticity. `NormalEnvelope`, `NormalSeries`, `NormalJets`, and
`NormalConvergence` provide the Cauchy/Hadamard particle envelopes and the actual
termwise infinite-series calculus. `CurveJets` additionally exports scalar
analytic-curve/analytic-amplitude `HasSum` identities for every iterated derivative.

`CompactNormal` is the load-bearing source for `Final/NormalConclusion`:

- `highNormalizedBulk_differentiableOn` and the low counterpart;
- `highNormalizedBulk_all_mixed_derivatives` and the low counterpart;
- `highNormalizedBulk_compact_normal_majorant` and the low counterpart;
- `highNormalizedBulk_uniform_jets_on_compact` and the low counterpart.

The majorants are literal nonnegative summable bounds on every normalized
particle term's fixed-order full mixed Fréchet derivative, uniformly on any
compact subset of the actual domain. Uniform partial-sum convergence is an
additional conclusion, not a substitute for normal convergence. The theorem
includes the physical prefactors and the whole HT domain, including its axes.

`CompactIntegralJets` proves the explicit all-order integral/Fréchet-jet
identity from genuine joint analyticity. It takes no supplied derivative
exchange or jet oracle.

## 3. Real physical realization, exact restrictions, and axes

`PhysicalField/RealFamily` uses one common correlation family on independent
positive real pairs for every finite positive ratio. Its only external inputs
are the real site form-factor identities and concrete real Gibbs-field data;
there is no susceptibility summability, field derivative, joint continuation,
or boundary assertion in those predicates. The source ledger is
`coordination/JOINT_REAL_SOURCE_LEDGER.md`.

`PhysicalField/Identification` identifies the same actual joint full functions
with the full lattice covariance sums. LT subtracts magnetization squared at
EVERY site and retains onsite `1-M²`. HT field differentiation is two-sided;
LT uses the plus-state right derivative. The physical energy-field factor is
`β=x/(2J)` on real rays, not a global parameter on the isotropic exterior.

`Restriction` and `NormalizedRestriction` prove exact fixed-ratio coefficient,
branch, and complete-function identities. `AxisRemovability` proves
`highNormalizedBulk (z,0)=exp z` on the central strip, including origin value 1.
The double-contour definitions never divide by `S`.

`HolomorphicIdentity` proves true several-variable uniqueness from ordinary
complex differentiability, using local scalar lines and connected propagation,
including uniqueness from an independent-real rectangle. `HighPunctured`
proves the required punctured-high preconnectedness. These support the actual
contour-to-angular identification in `RegularEdges/PhysicalAngular` and
`PhysicalIdentity`; that bridge is not a continuation premise.

## 4. Actual symmetries

`Swap` proves exact axis exchange of finite coefficients and complete normalized
sums by double-contour Fubini. `Conjugation` proves full-bulk Schwarz reflection
using the common real physical family and the preceding joint uniqueness.

`ParticleConjugation` separately proves
`unscaledFullCoefficient_conjugate_high` and `_low` for all positive particle
numbers on the entire actual domains, including HT axes, together with
`highPrefactor_conjugate` and `lowPrefactor_conjugate`. This particlewise proof
uses the exact real angular restriction and conjugation of actual angle
integrals, followed by real-plane uniqueness. It needs NO published-spin-family
premise and is consumed by the actual mixed-jet orientation transport.

## 5. Actual complex-ratio coordinates and complete weighted tails

`ComplexRatio`, `ComplexRatioFamilies`, and `ComplexRatioBounds` prove the actual
analytic coordinate map `(z,λ) ↦ (z,λz)`, the augmented-edge implicit inverse,
and a common product polydisk with varying COMPLEX λ. The nonzero z-derivative
is the natural transverse hypothesis, not an assumed inverse-family existence.

`CompositionJets`, `ParametricCoefficientTails`, `WeightedFamilyTails`, and
`ActualFamilyTails` attach full mixed derivatives to the literal weighted contour
coefficients of these families. One radius precedes all derivative orders;
each order has summable all-tail majorants. The weight-absorbing square root is
constructed locally and cancels from the final statement. The exact contour /
angular identity is an ambient neighborhood identity, so it transfers jets.
`ComplexRatioNumerators` is an additional numerator-only convenience export,
not the full-particle endpoint used for the final ratio conclusion.

## 6. Arbitrary complex parameter spaces: true ambient mixed tails

`CompactFamilyMixedTails` and `GenericCompactMixedTails` prove
`compact_joint_parametric_coefficient_mixed_tails H A` for arbitrary complex
normed `E`, compact centers `Q`, and jointly analytic
`H : ℂ × E → NumeratorParameter` and `A : ℂ × E → ℂ`. The center assumptions are
`H.first(0,η)=0`, positive imaginary part of the B coordinate, and nonzero S.
One scalar radius precedes all orders; each order bounds the full ambient
mixed jets of `A(q) * independentAngularCoefficient(2*j+3+k,b,H(q))` by a
summable particle majorant whenever the ACTUAL first coordinate is inward.
No finite-dimensional or local-compactness assumption on E is used.

The actual edge coordinate is retained away from Q. An identity known only on
a possibly thin compact Q is never differentiated in ambient parameter
directions. `Transverse/FamilyIndependentIdentity` supplies genuine ambient
physical particle identities, and `FamilyPhysicalMixedTails` consumes the
generic estimate. The actual ratio construction already has joint
normalization on a genuine open polydisk.

## 7. Positive regular-edge compact-family scaled leading limits

The complete `RegularEdges/FamilyLeading*` chain comprises Scaling, Dominated,
Cutoff, JointLimits, Local, Uniform, ActualLocal, Complement, Full, LowerSupport,
LowerLocal, LowerFull, and Prefactor. It retains the genuinely varying
`B(u,η), S(u,η)` throughout. Joint `(t,η)` dominated convergence and compactness,
not pointwise convergence alone, yield a common epsilon-delta radius before η.

`even_compact_family_fullCoefficient_uniform_limit` and its odd counterpart
concern the literal full angular coefficient, with factorial/angular
normalization and the complete onsite resolvent. The shared
`FamilyFiniteCoefficients` and `FamilyFiniteDecomposition` inputs prove the
actual derivative exchange and common local/complement decomposition.
`compact_family_lowerFullCoefficient_uniform_limit` gives every lower
first-resonant derivative's uniform scaled zero limit.

`compact_family_prefactor_scaled_limit` and
`compact_family_prefactor_lower_scaled_limit` handle arbitrary external jointly
analytic prefactors of the complete scalar sum, using the exact finite Leibniz
formula and all lower derivative limits. They are consumed by the complete
parity and actual physical family leading modules, not only by finite terms.

## 8. Actual complete physical ratio leading-plus-mixed endpoints

`ActualFamilyLeadingData`, `ActualFamilyLeadingTails`, `ActualFamilyLeading`,
`ActualFamilyLeadingPackage`, and the five `ActualFamilyLeadingNegative*`
modules prove the three strongest existential exports:

- `exists_positive_high_ratio_family_leading_and_mixed_tails`;
- `exists_positive_low_ratio_family_leading_and_mixed_tails`;
- `exists_negative_even_low_ratio_family_leading_and_mixed_tails`.

They construct the actual IFT family from the original boundary point and its
nonzero slice derivative, then choose ONE closed complex-λ disk for the actual
same-domain side, first-resonant arithmetic, uniformly nonzero physical leading
amplitude, uniform scaled COMPLETE-bulk derivatives including all lower
Leibniz terms, uniform divergence, and every mixed differentiated literal
weighted full-contour tail. These are exactly the three fields consumed by
`Final/RatioFamilyConclusion`.

The positive coordinate is `C-B-b`. Negative-even LT uses raw `C+B-b` and the
exact model `-B, i*S`, retaining the π-shift phase. It is not confused with the
scaled negative-odd coordinate `(C+B-b)/B`. `ComplexRatioPhysicalSide` and
`ComplexRatioNegativeSide` derive nearby frontier centers and same-domain sides.
`Transverse/FamilyPhysicalLeading` and `FamilyNegativeEvenLeading` provide the
complete physical leading results used in this specialization.

## 9. Negative compact-family Stokes / localization / transport chain

All 26 `Negative/FamilyCycle*` modules are implemented and individually checked:
Scalar, Quadratic, Homotopy, DensityAnalytic, ResidueAnalytic, Bounds,
ResidueBounds, CapIntegrability, Stokes, IntegralTransport, AnnularResidue,
AnnularIntegral, RealAnnular, RealContinuity, Comparison, Localization,
PhaseDisk, RealPole, PoleIntegral, InnerRemainder, InnerIntegral, ShiftedPole,
WitnessRemainder, CenteredRemainder, KernelTaylor, and Transport.

Main exports: `compact_family_normalized_cap_integrable`,
`compact_family_centered_kernel_taylor`, and `compact_family_central_transport`.
Their inputs are compactness, joint scalar analyticity, nonzero central B, and
common exact projected/correction witness radii. The witness construction is
proved in the separate negative normal-form chain; no Stokes comparison,
remainder estimate, cap integrability, or exchange target is assumed here.
The coth remainder R0 is independent of η. Common constants precede η and
particle/jet indices; the cutoff-dependent K also precedes η. The final bound
uses the literal centered kernel, transformed cap and actual Jacobian, with
exact annular, genuine Stokes, and same-R0 remainder errors. The negative
all-index and physical-family assemblies consume these exports.

## 10. Integration and evidence boundaries

The full contract assembly is `Final/FullConclusion`, not the intentionally
qualitative `CoreConclusion` alone. Geometry, collars, selected same-face
density, full boundary closure, arbitrary-family normalization/orientation, R,
I, and Riemann-domain consequences have their own author maps and source owners.
This map does not replace their proofs or the final isolated validation.

The bounded author source/type check against J/R/I is recorded in
`HOLOMORPHY_AUTHOR_INTEGRATION_CHECK.txt`. The selected logical callers of
`Final/RatioFamilyConclusion` and `Final/NormalConclusion` are recorded in
`HOLOMORPHY_REQUIRED_PROOF_DEPENDENCIES.txt`,
`HOLOMORPHY_REQUIRED_PROOF_CALLER_EVIDENCE.txt`, and the machine-readable
`HOLOMORPHY_REQUIRED_NAMES.txt`. Unused convenience wrappers are excluded from
that selected required list. The 72-name probe establishes name resolution
only, not a logical-closure or validation verdict.

Current lightweight source/object inventory and the bounded module-level
integration checks are recorded in `LIGHTWEIGHT_BUILD_READINESS.json` and
`BOUNDED_READINESS_RECOMPILE.json`. These are development readiness records.
Historical failed-attempt logs remain distinguishable from successful strict
records; no protected baseline source has been modified by this ownership.
