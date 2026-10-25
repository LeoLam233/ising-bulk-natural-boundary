# JOINT negative-odd edge: current manuscript, declaration and premise map

Current source integration, 23 October 2026, 16:03 UTC. This is an author
implementation map, not an independent audit or a clean/fresh verification
receipt. The modules below passed the pinned strict development compiler.
Protected LT/HT/ANISO baseline source bytes are unchanged.

Paths below are relative to `project/lean/IsingBulk/Joint/` unless explicitly
marked as baseline. Negative declarations use namespace
`IsingBulk.Joint.Negative`; the file name is not an additional Lean namespace.
Exact fully qualified required names and declaration/caller line evidence are
in `NEGATIVE_REQUIRED_PROOF_DEPENDENCIES.{txt,json,md}`.

## 1. Manuscript clause and literal objects

The target is the negative-odd part of JOINT Theorem 1.1(4), Section 5 and
Section 7.1, including local complex-parameter compact-family uniformity. The
actual ratio specialization additionally implements Lemma 7.1. Scalar curve
nonextension supplies the actual transverse obstruction used in the positive-
ratio restriction proof; ambient nonextension is never substituted for a
restriction obstruction. The equal-coupling mechanism remains separate.

The chart is the actual independent-coupling chart
`B=transferB=T/S`, `C=transferC=A/S`, with scaled negative edge
`t=(C+B-b)/B`. In the chosen orientation `Im B(0)<0`; the actual physical side
is `Im(B(t,eta)*t)>0`, containing the common inward ray `t=-epsilon`.
The anisotropy is the actual holomorphic function B(t,eta), including its
moving-center values B(tau_N,eta), never B frozen at zero.

`continuedAngularCoefficient` is the complete continued angular coefficient.
`negativePaperCoefficient` is the full odd boundary Taylor coefficient sum,
not one selected particle coefficient. `weightedPhysicalHigh` is exactly
`amp * sum_m p^m * unscaledFullCoefficient(2*m+1)`. Its exact relation to the
literal normalized physical response is
`weightedPhysicalHigh = (amp/highPrefactor) * highNormalizedBulk`.
All odd particle orders are retained, and the latter is the joint full-site
physical susceptibility already constructed by the common physical interface.

## 2. Public endpoints and their actual premises

| Source and declaration | Inputs that remain | Conclusion |
|---|---|---|
| `Negative/TransverseObstruction.lean`: `transverse_negative_high_no_extension_of_edge_deriv` | Actual analytic scalar curve at an arbitrary basepoint, selected regular high boundary geometry, prime phase, zero unscaled edge and its nonzero derivative | Nonextension of the literal full `highNormalizedBulk` along every such nonramified curve. |
| `Negative/FamilyObstruction.lean`: `compact_normalized_negative_family_obstruction` | Compact Q; actual jointly analytic curve and amplitude; S≠0; Im B<0; fixed prime phase; natural normalized-edge and amp²=p fiber germs | `CompactNegativeCoefficientObstruction`: actual complete Taylor radius zero, common selected-growth constants/thresholds, and uniform failure of every geometric coefficient bound. |
| `Negative/FamilyPhysicalConclusion.lean`: `compact_negative_high_physical_obstruction` | The same normalized actual family data, plus actual center frontier membership and p²≠1 | `CompactNegativePhysicalObstruction`: coefficient obstruction, common physical inward tube, uniform full weighted boundary jets and uniform literal normalized physical boundary jets. |
| `Negative/FamilyPhysicalMixedTails.lean`: `compact_negative_high_physical_mixed_tails_on_common_tube` | Actual normalized joint curve, compact Q and regular high-boundary data | One common actual physical side tube before every derivative order, and summable envelopes for all ambient mixed derivatives of literal full HT particle tails. No amplitude or square-root premise. |
| `Negative/FamilyArbitraryPhysical.lean`: `arbitrary_negative_high_family_estimates` | ORIGINAL joint analytic curve at (0,eta0), S≠0 and Im B<0 there, fixed prime phase, original scaled-edge zero and nonzero transverse derivative | Constructs one joint normalization N before any compact Q; explicitly recovers the original family; every compact admissible Q inside its parameter disk receives the complete physical obstruction and literal mixed tails. No amplitude-existence, exact-normalization or estimate premise remains for the original family. |
| `Negative/FamilyRatioPhysicalConclusion.lean`: `exists_negative_high_ratio_physical_obstruction` | Original actual ratio point in closure(highDomain), p²≠1, S≠0, Im B<0, fixed prime phase, scaled-edge zero and nonzero z derivative | Constructs the actual complex-ratio family and a positive closed complex-lambda disk, proves all nearby centers are on the noncritical physical frontier, and proves the complete physical family obstruction. |

The generic dominance lemmas have an explicit INTERNAL `HasCoefficientRanges`
interface. `compact_normalized_negative_family_ranges` proves that interface
from actual analytic/physical family data, and `FamilyObstruction.lean:47–68`
passes the derived result to radius, selected-growth and uniform-unboundedness
lemmas. No range, model error, transport, coefficient bound, derivative exchange,
Taylor radius or joint-uniformity assertion is an external premise.

For a compact parameter set, radii and scalar constants precede the family
member and particle dimension. Eventual order statements are `eventually j,
forall eta in Q`, not `forall eta, eventually j`. Fixed-order derivative
majorants may depend on j; the common inward radius precedes j. The selected
integer j_N may depend on eta, as permitted in Section 5.10. No uniformity
through Im B=0 or over the selected primes is asserted.

## 3. Increasing-dimensional pole, exact normal form and full density

| Paper mechanism | Actual declarations and module chain | Premise discharge and scope |
|---|---|---|
| Section 5.10 common analytic neighborhoods | `CompactFamilies`, `CompactAnalyticBounds`, `FamilyScalar`, `FamilyFactors`, `FamilyIdentities`, `FamilyPoleCenter` | Joint analyticity and compactness produce common scalar disks, bounds, fixed jets, removable identities and pole-center control. |
| Section 5.3 actual pole | `FamilyPole.compact_family_dimension_uniform_pole`; `FamilyPoleSelection`, `FamilyPoleLipschitz` | Common radii/constants before eta and dimension; unique actual pole, nonzero parameter slope, analytic equation, permutation symmetry, linear displacement and zero-mean average-square displacement. |
| Sections 5.4–5.5 symmetric normal form | `FamilyProjectedInverse`, `FamilyProjectedWitness`, `FamilyMeanField`, `FamilyCorrectionInverse.compact_family_correction_witness` | Constructs the actual projected/corrected symmetric inverse with common radii and derivative bounds. The actual cap proof uses its exact-energy identity, not a postulated quadratic approximation. |
| Exact quadratic energy used by the cap | Baseline `Anisotropic.NegativeNormalForm.UniformCorrectionWitness.exact_energy`, reached via `Negative/FamilyCapNormalization.lean:111` and baseline `NegativeCycles/NormalizedCapIdentity.lean:59` | Reuses the exact witness theorem on the newly constructed common-family witness. |
| Collision-safe analytic factors | `FamilyHadamard`, `FamilyAngularDerivative`, `FamilyQuadratic`, `FamilyPairSlope`, `FamilyRootPairBounds`, `FamilyRootCenterControl`, `FamilyMeanEnergy`, `FamilyCorrectedPair`, `FamilyCoincidence` | Actual removable pair factors and refined coincidence estimates, valid on every collision hyperplane. No division by a vanishing incomplete Vandermonde. |
| Complete squared Vandermonde | `FamilyVandermonde.compact_family_vandermonde_log`; `FamilyVandermondeDensity` | Exact complex logarithm of the COMPLETE squared inverse Vandermonde and common growing-energy exponential/error bound. |
| Actual constrained Jacobian and regular residue | `FamilyDensityScalar`, `FamilyDensityPair`, `FamilyDensitySlope`, `FamilyDensityEnvelope`, `FamilyDensityActual`, `FamilyDensityFull.compact_family_full_density_envelope`, `FamilyDensityLog` | Includes moving-center phase, one-body factors, every squared pair factor, pole slope, actual scalar residue and selected witness's constrained Jacobian. Constants precede eta and dimension. |
| Jacobian method actually used | Baseline `Anisotropic.NegativeNormalForm.UniformCorrectionWitness.constrainedJacobian_energy_envelope`, called at `Negative/FamilyDensityFull.lean:45–46` | The selected common-family witness is used directly. Standalone family Jacobian wrappers are not substituted as proof-dependency evidence. |

The convenience exports `compact_family_canonical_normal_form`,
`compact_family_exact_normal_form`, and the standalone
`compact_family_constrainedJacobian_*` wrappers exist, but are not mandatory
reachability tests. The actual full proof uses the common correction witness,
its baseline exact-energy theorem, and its baseline Jacobian method directly.

## 4. Actual complex cycle and Gamma-beta integration

| Paper mechanism | Actual declarations and module chain | Actual content |
|---|---|---|
| Sections 5.5–5.6 residue and complex homotopy | `FamilyCycleScalar`, `FamilyCycleDensityAnalytic`, `FamilyCycleResidueAnalytic`, `FamilyCycleQuadratic`, `FamilyCycleHomotopy`, `FamilyCycleBounds` | Common true residue analyticity, actual-pole quadratic comparison, full homotopy pole sector and complete Gaussian numerator bound. |
| Integrability and Stokes | `FamilyCycleCapIntegrability.compact_family_normalized_cap_integrable`; `FamilyCycleStokes.compact_family_residue_caps_transport` | Actual normalized cap integrability and genuine constrained-cylinder Stokes identity, with common constants. |
| Localized central transport | `FamilyCycleIntegralTransport`, `FamilyCycleComparison`, `FamilyCycleTransport.compact_family_central_transport` | Transports the literal centered kernel integral to the transformed residue cap. Every cutoff-dependent constant precedes eta, particle and jet indices. |
| Exact analytic remainder | `FamilyCycleRemainder*`, `FamilyCycleKernelTaylor.compact_family_centered_kernel_taylor` | One eta-independent coth remainder R0, common c/N remainder control, and exact integrated all-order centered Taylor decomposition. |
| Section 5.7 density error against beta kernel | `FamilyDensityBeta.compact_family_density_beta_bound`; `FamilyDensityBetaUniform` | Integrates the complete actual density error against the true complex kernel, with common cutoff and order range j≥8N². Calls baseline `complexDensityError_beta_bound`. |
| Exact central complex period | `FamilyCentralResidue.compact_family_central_residue_sequence`; `FamilyNormalizedModel.compact_family_normalized_model_error` | Retains actual physical center, B(tau_N,eta), root and complex Hessian. Calls baseline `regularResidue_complex_period_eq_model`, then the exact complex radial Gamma-beta integral. |
| Uniform period and tail control | `FamilyHessianBounds`, `FamilyPeriodLoss`, `FamilyBetaAbsorption`, `FamilyModelTail` | Common Hessian bounds, exact complex-period loss and beta-tail absorption, with eventual particle thresholds before eta. |
| First windings and central error | `FamilyCentralCap`, `FamilyCentralWinding`, `FamilyCentralGaussian`, `FamilyCentralFixedCutoff` | Actual transformed cap, exact complex Gamma-beta model, fixed physical cutoff and uniform Gaussian error. |

Actual proof-call spines, not import paths:

- `FamilyObstruction:47` → `FamilyCurveRanges:67` →
  `FamilyCoefficientRanges:46` → `FamilyMiddleParticle:51` →
  `FamilyCentralFixedCutoff:29` → `FamilyCentralGaussian:32` →
  `FamilyCentralWinding:36,39` → `FamilyCentralCap:38,40,41` →
  `FamilyNormalizedModel:41,43` and `FamilyCapNormalization:111`.
- `FamilyWindingFactory:20` → `FamilyCorrectionInverse:15` →
  `FamilyMeanField:20` → `FamilyProjectedWitness:12` →
  `FamilyProjectedInverse:33` → `FamilyPoleLipschitz:22` →
  `FamilyPoleSelection:19` → `compact_family_dimension_uniform_pole`.
- `FamilyCycleTransport:36` → `FamilyCycleComparison:32` →
  `FamilyCycleIntegralTransport:31` → `FamilyCycleStokes:83`, which invokes
  the genuine baseline constrained-cylinder cap-transport theorem.
- `FamilyCentralResidue:57` → baseline `PhysicalComplexPeriod:38` →
  `ComplexShapePeriod:45,27` → `ComplexRadialPeriod:62`
  (`complexRadialBeta_order`). The period is not replaced by a real-Hessian
  integral or an absolute-value surrogate.

## 5. Every winding and every particle range

| Paper mechanism | Actual declarations and module chain | Exhaustion of ranges |
|---|---|---|
| Higher winding geometry and numerator | `FamilyWindingEnergy`, `FamilyWindingSlope`, `FamilyWindingNumerator`, `FamilyWindingResidue`, `FamilyWindingIntegrand`, `FamilyWindingBetaIntegrand`, `FamilyWindingFactory`, `FamilyWindingWitness` | Actual winding poles, complete squared Vandermonde and physical residues with common energy/slope bounds. |
| Whole winding sums | `FamilyWindingLogBounds`, `FamilyWindingOverhead`, `FamilyWindingBounds`, `FamilyWindingSums.compact_family_noncentral_winding_sum`, `compact_family_all_winding_high_sum` | All higher windings in the middle range and every winding in the high range, including their entropy factors. |
| Exact full integral partition | `FamilyLocalDensity`, `FamilyWindingIntegral`, `FamilyIntegralPartition`, `FamilyWindingDecomposition`, `FamilyWindingSubsetDecomposition`, `FamilyResidueDecomposition`, `FamilyCentralKernelDecomposition`, `FamilyRemainderSum` | Exact physical integral partitions/residue identities, the same R0 and uniform all-index analytic remainder sums. |
| All-index boundary Cauchy control | `FamilyRootGap`, `FamilyAllParticleCauchy`, `FamilyCompleteBoundaryJets`, `FamilyAllJetMajorant.compact_actual_odd_normalized_cauchy` | True complete-resolvent boundary jets and common summable majorants. The growing-low particle range is included. |
| Nonresonant and outer ranges | `FamilyNonresonantCauchy.compact_actual_nonresonant_gaussian`; `FamilyOuterCauchy.compact_actual_outer_gaussian` | Every nonresonant particle and the actual outer angular region, not merely fixed particles or a whole-period shortcut. |
| Resonant middle and high ranges | `FamilyMiddleParticle.compact_family_middle_particle_bound`; `FamilyHighParticle.compact_family_high_particle_bound` | Complete particle estimates assembled from the actual common cycle and all-winding bounds. |
| Internal range interface | `FamilyCoefficientRanges.compact_family_negative_paper_ranges`; `FamilyCurveData`; `FamilyCurveRanges.compact_normalized_negative_family_ranges` | Derives the common full `HasCoefficientRanges` interface for the actual complete coefficients. Every low/nonresonant/outer/middle/high input is discharged internally. |
| Sections 5.8–5.9 discrete selection | `FamilyDominanceData`, `FamilyDominanceScalar`, `FamilyDominancePrefactor`, `FamilyDominanceConcavity`, `FamilyDominanceCrossing`, `FamilyDominanceCentered`, `FamilyDominanceMiddle*`, `FamilyDominanceResonant*`, `FamilyDominanceOuterRanges`, `FamilyDominanceAssembly` | Common exact scalar data, discrete concavity and integer crossing; every other resonant particle in the entire eligible middle range is controlled at the SAME selected order as the complementary ranges. Complex phases remain arbitrary. |
| Complete noncancellation and radius | `compact_family_complete_coefficient_selected_growth`, `compact_family_complete_coefficient_radius_zero`, `compact_family_complete_coefficient_uniform_unbounded` | Actual complete coefficient lower bound, radius zero and common failure of every geometric bound. `FamilyObstruction.lean:63–68` calls these with the internally proved range interface. |

The detailed exact dominance interfaces are also recorded in
`JOINT_FAMILY_DOMINANCE_PROOF_MAP.md`. They are mathematical internal lemmas,
not additional published real-physics inputs.

## 6. Uniform attachment to the literal complete physical function

1. `FamilyChartIdentity.compact_family_analytic_identity` promotes natural
   fiber identities to one common exact disk. `FamilyHighTube` derives the
   actual physical high-side tube and common inward negative ray.
2. `RegularEdges.fullCoefficient_eq_physicalAngular_high` is the proved actual
   full contour/angular identity. `FamilyPhysicalSum.negative_high_weighted_particle_eq`
   uses it; `FormFactors.high_particleSeries_mul_comp_hasSum_iteratedDeriv`
   supplies actual full-series derivative exchange. No equality or derivative
   exchange is assumed as a target-like premise.
3. `FamilyInteriorTails.compact_actual_negative_interior_tails` gives a common
   inward radius before j and a summable complete-resolvent derivative envelope
   for every large particle. `FamilyFiniteJets` and `FamilyFinitePrefixes`
   prove true joint finite-term jet continuity from the actual compact angular
   integral, not a collection of unrelated scalar limits.
4. `FamilySeriesLimit.uniform_tsum_of_common_tail` proves uniform Tannery.
   `FamilyPhysicalJets.compact_negative_high_weighted_boundary_jets` uses the
   common tail and finite-term limits to identify every weighted full physical
   boundary derivative uniformly in eta.
5. `FamilyNormalizedJets.compact_negative_high_normalized_boundary_jets`
   identifies every derivative of literal `highNormalizedBulk`, uniformly,
   with `normalizedHighBoundaryJet`: the exact finite Leibniz convolution of
   the physical unit with the complete weighted boundary-jet sum.
6. `IndependentCoefficientJets`, `FamilyInteriorMixedTails` and
   `FamilyPhysicalMixedTails` additionally control every ambient mixed
   derivative of the literal physical particle tail on the common actual side.
   The physical identity holds on an open ambient germ before differentiation;
   no off-Q fiber identity is incorrectly differentiated in a parameter direction.

The explicit formal-series zero-radius assertion concerns the analytically
weighted actual full coefficients. The literal normalized physical function
has the proved uniform boundary jets and genuine no-extension theorem. Division
by the nonvanishing physical analytic unit transfers nonextension, as in
Section 5.10. No separate zero-radius theorem for the normalized Leibniz-
convolution coefficient series is claimed.

## 7. Arbitrary nonramified families, actual ratio families and orientations

`Transverse.familyEdgeMap_local_inverse` proves the genuine joint IFT for
`(z,eta) ↦ (f(z,eta),eta)` using its actual triangular Fréchet derivative.
`exists_familyNormalization` constructs one common product-disk radius and a
jointly analytic inverse preserving eta, with BOTH inverse identities.
`exists_familyNormalization_with_analytic_centers` shrinks that disk inside
the original curve's analytic-center neighborhood. `FamilyNormalization.original_recovered`
retains the original curve exactly.

`arbitrary_negative_high_family_estimates` constructs this N before Q and
uses `N.right_inv_germ` to DERIVE the normalized edge identity. For every
compact Q in the constructed parameter disk, only actual selected-center
admissibility remains: edge-zero, frontier high, S≠0, p²≠1 and Im B<0.
The amplitude is constructed internally as the canonical analytic root described
below. Its conclusions include all coefficient, physical-jet and mixed-tail
estimates. The local scope is precisely the manuscript's common-polydisk scope;
no global inverse over a disconnected parameter domain is asserted.

For ratios, `FormFactors.negative_high_complex_ratio_family` constructs the
actual `(z(u,lambda),lambda*z(u,lambda))` family on a common complex polydisk.
`negative_ratio_common_high_centers` derives all nearby actual frontier and
noncritical center conditions. `exists_negative_high_ratio_physical_obstruction`
then applies the full physical bundle on a smaller positive closed lambda disk.
No nearby-center frontier, physical-side map or family existence is a premise.

Orientation transport acts on literal physical functions and actual complete
particle jets. The current scalar orientation bundle includes
`uniform_swap_approach` and `uniform_reflected_approach`, using common physical
membership/continuity along the approach. The mixed bundle includes
`tails_swap_on` and `tails_reflected_on` on arbitrary joint sets W⊆ℂ×E.
Thus the eta-dependent side Im(B(u,eta)*u)>0 is retained, not forced into a
parameter-independent half-disk. The same common radii/envelopes are transported.

## 8. Canonical-root sign discipline

The arbitrary negative-odd attachment uses
`Transverse.negativeEvenParticleRoot K = i*S(K)*sqrt(-transferB(K))`.
Despite its historical name, `negativeEvenParticleRoot_sq` proves square=p
without a parity restriction (`Transverse/FamilyNegativeEvenIdentity.lean:17–23`).
Its nonvanishing and genuine joint analyticity on Im B<0 are proved at lines
25–44 and used in `Negative/FamilyArbitraryPhysical.lean:69–75`.

This root is NOT equated to `S*sqrt(B)`. `negative_high_weighted_particle_eq`
(`FamilyPhysicalSum.lean:24–35`) is valid for ANY a with a²=p. Under a→−a,
every odd term and the entire weighted physical sum change by the same minus
sign. The reverse physical multiplier highPrefactor/a changes sign too, so
the literal normalized response is unchanged. Every term of its finite
Leibniz boundary-jet convolution contains both signs, which cancel.
Norm growth and zero radius of the weighted coefficients are unaffected.
No particle-dependent odd phase is discarded.

## 9. Actual final proof integration and validation boundary

`Final/FullConclusion.lean` is present. Its proof of
`IsingBulk.Joint.full_joint_conclusion` actually calls:

- `joint_negative_family_conclusion` (line 38);
- `joint_negative_mixed_family_conclusion` (line 39);
- the scalar and mixed orientation conclusions (lines 41–42);
- `joint_family_normalization_conclusion` (line 43);
- `joint_arbitrary_negative_family_conclusion` (line 45).

The arbitrary-negative path is
`joint_arbitrary_negative_family_conclusion` →
`arbitrary_negative_high_family_estimates` →
`exists_familyNormalization_with_analytic_centers` →
`exists_familyNormalization` → `familyEdgeMap_local_inverse`.
It also actually calls original-family recovery, the complete physical
obstruction and literal mixed-tail theorem. These are proof calls, not imports.
The 44-name required-dependency list and JSON caller evidence distinguish
actually used witness methods from merely imported convenience exports.
The frozen heavy-worker closure check must enforce the list against the final
source identity; this source map is not a substitute for that check.

The sharp auxiliary crossing expansion
`j_N=N²(log N+½ log log N-c*(eta)+o(1))` and its sharp coefficient-root
equivalent are not claimed by the coarser selected-growth declarations. The
proved common crossing intervals, complete noncancellation and supergeometric
growth establish the required compact-family obstruction.

Strict development compilation uses Lean 4.34.1 with warnings as errors:
`coordination/COMPILE_ONE.sh IsingBulk/Joint/Negative/NAME.lean` from the task
workspace. Cached development compilation and the recorded endpoint axiom
inspection are not clean builds, full proof-closure checks, fresh independent
kernel replay, or any of the required three independent whole-proof audits.
Those root-owned validation obligations remain separate. This map supplies no
audit verdict and does not certify final acceptance of the J AND R AND I contract.
