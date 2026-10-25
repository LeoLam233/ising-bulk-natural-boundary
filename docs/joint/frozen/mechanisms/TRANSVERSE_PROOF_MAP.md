# JOINT regular edges, transverse curves, and complex-family estimates

## Scope and notation

This is a current manuscript-to-declaration-to-premise map for JOINT Theorem
1.1(3)–(4), Sections 4 and 5, and their use in the Section 7 restriction argument.
It records mathematical interfaces and development compilation evidence, not a
whole-project audit verdict. Paths below are relative to
`project/lean/IsingBulk/Joint/`; declarations are in `IsingBulk.Joint` or the
indicated `RegularEdges`, `Transverse`, `Negative`, and `FormFactors` namespace.
All sources discussed here are additive; the ANISO baseline is not modified.

`Coupling = ℂ × ℂ` stores the doubled physical coordinates `(z,w)=(2Kx,2Ky)`.
The actual joint functions are `S=sinh z`, `T=sinh w`,
`A=cosh z*cosh w`, `p=S*T`, `transferC=A/S`, and `transferB=T/S`.
The positive raw edge coordinate is `positiveParameter b K=C-B-b`.
The negative-even raw coordinate is `negativeParameter b K=C+B-b`.
The negative-odd coordinate is `Negative.edgeParameter b K=(C+B-b)/B`.
These last two coordinates are deliberately distinct.

The complete physical objects are `FormFactors.unscaledFullCoefficient N`,
`highNormalizedBulk`, and `lowNormalizedBulk`, not independently defined slice
functions. `Transverse.highFullParticle m K` is literally
`highPrefactor K * p K^m * unscaledFullCoefficient (2*m+1) K`;
`lowFullParticle m K` is literally
`lowPrefactor K * p K^(m+1) * unscaledFullCoefficient (2*m+2) K`.
Their full-site contour construction retains the onsite term and the entire
lattice resolvent. The low function is the original nonzero-even, plus-connected
physical series, with the physical magnetization subtraction supplied by the
common real-spin interface in the physical-identification modules.

## 1. Actual contour-to-angular identification: Section 3 to Sections 4–5

- `RegularEdges/PhysicalAngular.lean` proves joint finite-order Fréchet
  smoothness of the actual angular coefficient and its real positive-pair
  equality with the full double-contour coefficient.
- `RegularEdges/PhysicalIdentity.lean` exports
  `fullCoefficient_eq_physicalAngular_high n hK hS` and
  `fullCoefficient_eq_physicalAngular_low n hK`.
  The first applies on the actual high domain with `S≠0`; the second applies on
  the actual low domain. The high exclusion is the angular chart singularity,
  not an exclusion from the underlying contour-defined physical function.
- The bridge proves an open real-plane germ by two scalar identity arguments,
  then propagates using genuine joint holomorphy on the connected actual
  domains. It uses the proved connectedness of `highDomain ∩ {S≠0}` and
  `lowDomain`. It does not infer joint equality from separately defined ray
  continuations or assume an angular identity as a new physical premise.
- `RegularEdges/NormalFormIdentity.lean` identifies the complete physical
  angular density and coefficient with the positive variable-`B` edge model.
  `RegularEdges/NegativeEvenIdentity.lean` proves the actual π-shift with its
  particle sign `(-1)^choose(N,2)` and the exact even-parity absorption into
  the scale `i*S`; `physicalAngular_eq_negative_even_model` is the attachment.
- `RegularEdges/BoundaryPrefactors.lean` proves analyticity of the physical
  high/low prefactors at the relevant domain closure when `p²≠1`, as well as
  their required nonvanishing. No analytic-prefactor hypothesis is left in the
  actual physical endpoint.

Thus subsequent full-sum obstructions concern the original contour-defined
bulk functions with their original normalization, not a formal angular proxy.

## 2. Genuine geometry and every nonramified curve: Proposition 4.3

`Transverse/TransferFace.lean`, `LocalSide.lean`, and `NegativeLocalSide.lean`
use the literal unsquared spectral parallelogram, a local transfer-coordinate
half-ball, and actual spectral-complement component identities to identify the
physical side. `ConstantAnisotropy.lean` constructs a genuine holomorphic-chart
transversal from the genuine local inverse of `(C,B)`, with constant `B` and
normal derivative one. `CurveCoordinates.lean` separately normalizes an
arbitrary nonramified scalar curve; it never freezes its actual varying `B`.

`GeometricTransversality.lean` defines
`edgeEquation a b K=A K-S K*a-T K*b` and
`IsNonramifiedJointTransversal c z` by nonzero derivative for every actual
endpoint defining equation at `c z`. The theorem
`nonramified_iff_edge_deriv` reduces this to the usual derivative of any one
genuine edge equation when the regular real coefficients are unique.
`positive_deriv`, `negative_deriv`, `.swap`, and `.reflected` prove the exact
coordinate conversions and invariances.

The load-bearing complete-sum curve endpoints are:

- `PositiveObstruction.lean`: `positive_high_curve_no_extension` and
  `positive_low_curve_no_extension` for the actual bulk functions.
- `NegativeEvenObstruction.lean`: `negative_even_low_curve_no_extension`.
- `Negative/TransverseObstruction.lean`:
  `transverse_negative_high_no_extension_of_edge_deriv`, using the distinct
  negative-odd full boundary-jet radius-zero mechanism.
- `AllOrientations.lean`:
  `prime_regular_high_curve_no_holomorphic_extension` and
  `prime_regular_low_curve_no_holomorphic_extension`.

The last two take an actual analytic curve, actual boundary membership,
`IsPrimeRegularJointEdge`, and literal nonramified transversality. They reject
ordinary holomorphic extension on `c ⁻¹' highDomain` or `c ⁻¹' lowDomain`.
Positive and negative endpoints, swapped axes, and conjugate orientations are
all included. The all-orientation bulk-reflection route takes the shared
`PublishedRealSpinFamily corrH corrL`; it does not take a natural-boundary,
full-tail, angular-equality, or continuation premise.

`AmbientObstruction.lean` and `AllOrientationAmbient.lean` use only the valid
direction “an ambient holomorphic extension pulls back to a scalar extension,”
together with an internally constructed obstructed transversal.
`Final/JointBoundary.lean` then combines actual prime-regular boundary density
and actual local collars to prove `high_holomorphic_natural_boundary` and
`low_holomorphic_natural_boundary` at every finite boundary point, with
connected-component local agreement and ordinary `DifferentiableOn ℂ`
holomorphy. This does not assert singularity throughout the interior of the
spectral set. Slice nonextension is obtained from the curve obstruction, never
from ambient nonextension alone; the decoupled-axis counterexample is respected.

## 3. Independent common complex polydisks: Lemmas 4.1–4.2

The independent parameter is `NumeratorParameter = ℂ × (ℂ × ℂ)`, written
`(u,B,V)` here so the model scale `V` is not confused with the physical `S`.
The admissible upper domain is `Im u>0`, `Im B>0`, and `V≠0`.

- `ComplexPolydisk.lean` proves the common root domain, strict root-Schur
  contraction, and cancelled-pair bounds on a genuine complex product
  polydisk. `UniformNumerator.lean` supplies compact denominator control and
  all-particle matched-Pfaffian Gaussian pair bounds; reciprocal-angle limits
  are handled by radial regularization.
- `UniformFullNumerator.lean`, `MixedCauchy.lean`, and `CompactMixedJets.lean`
  include the one-body factors and all mixed numerator derivatives.
- `CompactRootJets.lean` supplies common compact-family root polydisks,
  quantitative quadratic root gaps and all mixed root jets.
- `MixedResolventJets.reciprocal_product_gap_mixed_jets` is valid for a genuinely
  arbitrary complex normed parameter domain. `CompactFullJets` includes the
  entire lattice resolvent, not merely the numerator, while retaining the
  quadratic-gap weight needed for angular integration.
- `CompactFullTails.compact_full_tail_summable_mixed_jets` proves summable
  integrated majorants for every particle `n=2*j+3+l` at mixed order `j`.
- `IndependentCoefficientJets.independentAngularCoefficient_mixed_jets`
  identifies the actual mixed coefficient derivative with the differentiated
  full integral, preserving the factorial and angular probability-measure
  normalization. The compact integral differentiation theorem is proved in
  `FormFactors/CompactIntegralJets.lean`, not assumed as a jet oracle.
- `compact_actual_coefficient_summable_mixed_jets` bounds these ACTUAL
  coefficient derivatives. `compact_actual_jets_finite_tail_split` also proves
  summability and the exact whole-series split into every `n<2*j+3` and the
  complete remaining tail.

Quantifier order: for fixed `|b|<1` and compact admissible `K⊂ℂ²` of `(B,V)`,
there is ONE `δ>0` before every derivative order `j`. For each `j` there is a
nonnegative summable `G_j(l)` controlling the full operator norm of the actual
`j`th Fréchet derivative at every point of every radius-`δ` ball about `(0,v)`,
`v∈K`, on its upper side. The bound therefore controls all mixed directions.
Constants may depend on the selected phase and compact family; no uniformity
across primes or unbounded singular orders is asserted.

## 4. Whole-parity noncancellation, including every finite order

`AngularCoefficient.lean`, `FullDifferentiatedTail.lean`, and
`FullSeriesJets.lean` establish the actual full coefficient derivative,
complete tail bounds and differentiated `HasSum` identities.
`PositiveFullSum.paritySeries_first_limit`, its odd/even first-singularity
wrappers, and `WeightedFullSum.lean` give the scalar nonextension mechanism
for nonconstant analytic `B,V`, including all integer particle weights and
arbitrary analytic nonzero outer prefactors.

The compact-family argument does NOT substitute a large-particle estimate for
the finite-order noncancellation proof. Its four parts are proved separately:

1. Lower nonresonant particles: `FamilyFiniteCoefficients` exports
   `compact_family_nonresonant_coefficient_bound` under
   `continuedRoot(b)^(n+1)≠1`, on one common upper complex disk.
2. The first resonant particle: `FamilyLeadingActualLocal` proves the genuine
   joint-filter dominated integral limit; `FamilyLeadingFull` adds the actual
   complement/decomposition and exports
   `compact_family_fullCoefficient_uniform_limit` for the complete coefficient.
   `FamilyLeadingLowerFull` proves uniform zero limits at every lower derivative
   order, rather than treating these as bounded without proof.
3. Finite higher particles: `compact_family_higher_coefficient_bound` uses
   `n≥1` and `2*(j+1)≤n*(n+1)` to obtain common bounds at `u=i*t²`.
   `FamilyFiniteSums` also supplies finite simultaneous bounds. The main parity
   proof directly uses the individual nonresonant/higher bounds.
4. The entire infinite tail: `FamilyTailJets` supplies actual varying-family
   coefficient derivative majorants; `FamilySeriesJets` proves the exact
   differentiated `HasSum` including its finite prefix; `FamilySeriesLimit`
   combines the finite block and the complete summable tail uniformly.

`FamilyParityLeading.compact_family_parity_derivative_uniform_limit` assembles
all four parts. `FamilyPrimeLeading` discharges the model integrability,
period-continuity, resonance and degree conditions for the selected parities.
For odd first particle `N=2*q+1`, `q≥1`, the first derivative order satisfies
`2*k+1=(2*q+1)^2`, with scaling `t²` at `u=i*t²`. For even first particle
`N=2*q+2`, the degree is `2*(k+1)=(2*q+2)^2`, with scaling `t`.

`CompactLeadingAmplitude.lean` proves the exact center identity for arbitrary
NONCONSTANT `B,V`, continuity of the actual leading amplitude through the
true collision/beta or rational period formula, and a positive common lower
bound for its norm on compact admissible families. `UniformNoncancellation`
converts the uniform limit into a common lower bound and common derivative
divergence past every real `M`. No positivity of complex summands is assumed.
`FamilyLeadingPrefactor` and `FamilyPrefactoredParity` perform the complete
Leibniz attachment, using the proved zero limits of every lower derivative.

## 5. Literal physical families and genuine ambient mixed derivatives

`FamilyParticleRoot.lean` constructs the single canonical positive particle
root `R=S*sqrt(B)` with `R²=p`, analyticity and nonvanishing on `S≠0, Im B>0`.
`FamilyNegativeEvenIdentity.lean` uses the canonical negative root
`R=i*S*sqrt(-B)`, again with `R²=p`, and the model scale `i*S/R`.
There are no memberwise square-root choices or extra global branch premises.

`FamilyPositiveSide.lean` and `FamilyNegativeEvenSide.lean` derive actual
common physical-side tubes from the compact center geometry and normalized
edge germs. `FamilyPhysicalIdentity`, `FamilyParticleIdentity`, and
`FamilyNegativeEvenIdentity` attach the full parity series and individual
particles exactly, retaining prefactors, powers of `p`, and the π-shift phase.

`FamilyIndependentIdentity.lean` is crucial for all mixed derivatives:
`positivePhysicalParameter` and `negativeEvenPhysicalParameter` use the ACTUAL
edge function of the ambient coupling as their first coordinate. The physical
particle identity is proved without any normalization premise.
`FormFactors/GenericCompactMixedTails.compact_joint_parametric_coefficient_mixed_tails`
then differentiates the actual analytic substitution and external amplitude.
`FamilyPhysicalMixedTails` transfers the identity in an OPEN ambient physical
neighborhood before differentiating. Equality of normalized fibers only for
`eta∈Q`, where `Q` may have empty interior, is never differentiated as an
identity in ambient parameter directions.

The three assembled normalized-family endpoints in
`Transverse/FamilyQuantitativeEndpoint.lean` are:

- `positive_high_compact_family_quantitative`;
- `positive_low_compact_family_quantitative`;
- `negative_even_low_compact_family_quantitative`.

Inputs: arbitrary complex normed parameter space `E`, compact `Q`, joint curve
analyticity at `(0,eta)`, actual center frontier membership, `S≠0`, `p²≠1`,
the appropriate strict `B` sign, fixed selected `b`, and normalized edge germs.
Conclusions: a common physical analytic tube, exact same-domain side, positive
common norm bound on the actual leading amplitude, every lower scaled
full-bulk derivative tending uniformly to zero, the first full-bulk scaled
limit tending uniformly to that nonzero amplitude, common divergence past any
`M`, and complete summable mixed physical particle tails.

The physical tail index is `m=j+2+l`, `l≥0`, for both literal `highFullParticle`
and `lowFullParticle`; ONE radius precedes all `j,eta,u,l`. The finitely many
preceding particles are fully present in the separate whole-bulk limit proof.
`FamilyWeightedTails` and `FamilyPhysicalTails` also expose scalar derivative
versions, but the final quantitative package uses the stronger ambient mixed
version. `FamilyEstimateStatements` merely names the proved RESULT
propositions; none is a substitute estimate hypothesis.

## 6. Arbitrary original families: common joint IFT and recovery

The exact-normalization input of the preceding intermediate theorem is
eliminated by `FamilyNormalizationLocal.lean` and `FamilyNormalization.lean`.
For arbitrary complete complex normed `E`, joint analytic `f:ℂ×E→ℂ` at
`(0,eta₀)`, `f(0,eta₀)=0`, and nonzero scalar transverse derivative, the actual
augmented map `(z,eta)↦(f(z,eta),eta)` has an invertible computed triangular
Fréchet derivative. The power-series inverse theorem constructs
`FamilyNormalization f eta₀` on a common product disk.

The structure contains an actual jointly analytic inverse, a positive common
radius, and BOTH identities:
`f(inverse(u,eta),eta)=u` and `inverse(f(z,eta),eta)=z`.
Selected centers with `f(0,eta)=0` are fixed. `normalizedFamily curve` is the
literal composition `curve(inverse(u,eta),eta)`.
`FamilyNormalizationAttachment.exists_familyNormalization_with_analytic_centers`
shrinks the constructed radius so joint analyticity of the original curve at
all nearby parameter centers follows from its one base `AnalyticAt` assumption.

`FamilyArbitraryQuantitative.lean` exports
`positive_high_arbitrary_family_quantitative`,
`positive_low_arbitrary_family_quantitative`, and
`negative_even_low_arbitrary_family_quantitative`.
They construct this normalization from original curve analyticity, literal edge
zero, nonzero transverse derivative and branch admissibility. Their conclusions
explicitly recover the ORIGINAL family through the edge coordinate, then give
the complete physical estimates for EVERY compact admissible parameter subset
of the constructed parameter disk. There is no normalized-germ premise and no
additional familywise analyticity premise. The estimates are expressed in the
constructed regular-edge coordinate, with exact original-family recovery;
this is not a claim that nonlinear reparameterization leaves derivative values
unchanged.

This is the local common-polydisk scope of JOINT Theorem 1.1(4) and Section 7,
not a global inverse glued over arbitrary disconnected compact parameter sets.
The corresponding final Prop bundle is `JointArbitraryPositiveFamilyConclusion`,
proved by `joint_arbitrary_positive_family_conclusion` in
`Transverse/FamilyArbitraryConclusion.lean`.

## 7. Negative odd: complete boundary jets and actual mixed inward tails

The negative odd obstruction is a zero radius of the COMPLETE boundary Taylor
series, not a singularity of one fixed particle. The local coordinate is the
scaled `t=(C+B-b)/B`, with `Im B<0`; the physical side is `Im(B*t)>0`, containing
the common inward ray `t=-epsilon`.

The quantitative support modules and their precise roles are:

- `Negative/FamilyRootGap`: common quadratic boundary gap, odd polynomial
  product gap, actual independent-polydisk root Lipschitz control and full odd
  product gap on `a/N³`.
- `FamilyAnalyticControl`, `FamilyFullControl`, `FamilyAllParticleCauchy`:
  complete full-resolvent integrand bounds and mixed Cauchy jets on those balls,
  with sharp factorial scalar transverse bounds. Constants precede the family
  member, particle index and derivative order.
- `FamilyBoundaryIdentity` and `FamilyCompleteBoundaryJets`:
  actual weighted shifted-density germ, exact differentiated full integral and
  `compact_actual_odd_boundary_cauchy`, without a derivative-exchange oracle.
- `FamilyAllJetMajorant`: `compact_actual_odd_boundary_summable_majorants`
  and `compact_actual_odd_normalized_cauchy`. The latter bounds the actual
  `negativePaperParticleCoefficient` by `D*N²*(N³/a)^j`; finite initial
  indices are explicitly included.
- `FamilyBoundaryGaps`, `FamilyGapControl`, `FamilyGapCauchy`:
  common outer and selected nonresonant gaps with full varying-family
  integrand control on `a/N` disks.
- `FamilyRestrictedJets`, `FamilyOuterCauchy`, `FamilyNonresonantCauchy`:
  exact restricted-region derivative identities and common Cauchy/Gaussian
  bounds for the actual outer integrals and nonresonant coefficients.

Their center inputs are joint curve/amplitude analyticity over compact `Q`,
nonzero physical `S` and amplitude, the actual equation `A+T=b*S`, and strict
`Im(-T/S)>0`. They do not assume the required bounds or sum identities.
The negative-family mechanism map separately records the increasing-dimensional
pole, symmetric normal form, constrained Jacobian, full Vandermonde density,
complex cycle transport, Gamma/beta evaluation, all winding suppression and
middle/high range assembly that consume these interfaces.

`FamilyUpperJetMajorant` and `IndependentCoefficientJets` prove the independent
negative full coefficient's actual integrated mixed derivatives and summable
majorants. `FamilyInteriorTails` gives the common scalar inward envelopes.
`FamilyInteriorMixedTails.compact_actual_negative_interior_mixed_tails`
strengthens this to all ambient derivatives of
`W(q)*amp(q)^N*continuedAngularCoefficient (N-1) (curve q)`, including an arbitrary
analytic outer prefactor and the ACTUAL upper edge coordinate.

`FamilyPhysicalMixedTails` removes the auxiliary amplitude from the literal HT
particle estimate using the canonical root and physical prefactor.
`compact_negative_high_physical_mixed_tails_on_common_tube` derives the actual
high-domain equivalence `Im(B*t)>0` and full all-order mixed particle tails on
one radius. Its final bundle is `JointNegativeMixedFamilyConclusion`, proved
by `joint_negative_mixed_family_conclusion` in `Negative/FamilyMixedConclusion`.

The negative full-function attachment is
`compact_negative_high_physical_obstruction` in `FamilyPhysicalConclusion`:
it contains the common actual inward high-domain tube, uniform convergence of
all complete weighted boundary derivatives, and uniform convergence of all
literal normalized-bulk derivatives to the exact physical-unit Leibniz
convolution of the complete boundary sum. `FamilyArbitraryPhysical` and
`FamilyArbitraryConclusion` apply the constructed generic IFT to arbitrary
original negative-odd families and package both the physical obstruction and
literal mixed tails, with explicit original-family recovery. No square-root
family or exact-normalization germ is a hypothesis of that arbitrary-family
endpoint.

## 8. Completed orientation transport and actual complex-ratio specialization

`SymmetryTransport` and `AllOrientations` handle the qualitative every-curve
claims. Quantitative transport is separately established, not inferred from
qualitative nonextension:

- `AnalyticReflection` constructs the reflected multilinear power series,
  proving joint analyticity of reflection in both source and value.
- `FamilyOrientations` transports actual bulk scalar jets and uniform scaled
  limits under axis exchange and Schwarz reflection of BOTH curve and complex
  family parameter. The approach path, scale and amplitude are conjugated
  exactly; compact parameter sets and reflected disks retain their radius.
- `MixedReflection` proves exact all-mixed Fréchet map and operator-norm
  reflection under finite `ContDiffAt`, suitable for the actual integrals.
- `FamilyParticleSymmetry` proves `highFullParticle_swap`,
  `lowFullParticle_swap`, `highFullParticle_conjugate`,
  `lowFullParticle_conjugate`, and genuine finite-order joint smoothness on
  the actual domains. `FormFactors/ParticleConjugation` supplies exact full
  contour-coefficient and physical-prefactor reflection, including HT axes,
  with NO real-spin premise.
- `FamilyMixedOrientation` and `FamilyMixedOrientationConclusion` instantiate
  actual physical particle transport and preserve the SAME mixed-tail
  envelopes and common radius. The final theorem is
  `joint_mixed_family_orientation_conclusion`.

`FormFactors/ComplexRatio*` constructs the actual complex-ratio local family,
not just real-ray variation. `ActualFamilyLeading*`, the positive and negative
physical-side modules, and the same-polydisk package theorems attach the actual
HT, positive LT, and negative-even LT leading limits together with complete
mixed physical tails. `Negative/FamilyRatioPhysicalConclusion` supplies the
negative-odd counterpart. These specialized families coexist with, and do not
replace, the arbitrary-family IFT attachment above. The equal-coupling
collinear case is handled by the separate actual isotropic proof and exact
identification elsewhere in the project, not by extrapolating a generic chart.

## 9. Final interfaces, premise discipline, and reproduction

The principal final interfaces for this mechanism are:

- `joint_positive_family_conclusion` in `Final/PositiveFamilyConclusion`:
  the three normalized actual physical quantitative endpoints.
- `joint_arbitrary_positive_family_conclusion` in
  `Transverse/FamilyArbitraryConclusion`: constructed arbitrary-family chart
  and the three complete physical estimate packages.
- `joint_negative_mixed_family_conclusion` in `Negative/FamilyMixedConclusion`;
  `joint_arbitrary_negative_family_conclusion` in
  `Negative/FamilyArbitraryConclusion` supplies the arbitrary negative-odd
  physical obstruction together with mixed tails.
- `joint_family_orientation_conclusion` and
  `joint_mixed_family_orientation_conclusion`: actual scalar-limit and full
  mixed-tail symmetry transport, respectively.
- The actual every-curve and every-boundary declarations listed in Section 2.

The older `joint_transverse_compact_family_endpoint` remains a valid conjunction
of pointwise every-curve nonextension with independent compact mixed estimates
and an exact finite-prefix split. It is NOT used as a substitute for the stronger
whole-family leading-limit and arbitrary-normalization interfaces above.

No desired nonextension, full-sum identity, mixed-tail envelope, uniform leading
limit, physical-side `MapsTo`, or inverse chart is introduced as an external
premise. The allowed real physical-spin interface is visible where physical
bulk reflection/identification uses it. Analytic-at-center, actual boundary,
noncriticality, branch sign, compactness and literal nonramification assumptions
are mathematical admissibility inputs and are retained explicitly.

All listed mechanism sources have been compiled in development by the pinned
`coordination/COMPILE_ONE.sh IsingBulk/Joint/.../File.lean` route from the project
root: Lean 4.34.1, `lakefile.joint.toml`, one compiler worker, warnings as errors,
and timestamped logs in `coordination/compile_logs/`. The sources introduce no
new axioms, `sorry`, or `admit`. The targeted declaration checks in
`TRANSVERSE_ENDPOINT_AXIOMS.lean/.log` report only `propext`, `Classical.choice`,
and `Quot.sound`; explicit hypotheses are documented above rather than inferred
from that axiom list.

`TRANSVERSE_REQUIRED_PROOF_DEPENDENCIES.txt` contains 30 exact load-bearing
names; its JSON/Markdown companions give direct source-caller evidence and
identify unused convenience wrappers. `TRANSVERSE_REQUIRED_NAMES_CHECK.lean`
strictly checks that those names exist. These are author-side development
records, not a proof-term closure scan. The final conjunction must actually
reach the required mechanisms; final integration, fresh validation and the
whole-contract review are separate project steps.
