# Auxiliary source scope after absolute-tail assembly

Date: 2026-10-06. Workspace: `ising_continuation_20261006`.

This is a read-only source-correspondence review recorded during proof
development, not a formal adversarial audit or a new verification gate. It
examines the remaining-work language in `CLAIM_LEDGER.tsv` for
`lem:contraction` and `lem:originaldisk`. It does not change either ledger
status, claim that every raw manuscript clause has been exported as a Lean
theorem, or infer such closure merely from compilation of the final wrapper.
No Lean execution was performed for this review.

All paths below are relative to this workspace. Declaration names are the
stable references; line references describe the source inspected on this date.

## Finding and exact distinction

The actual final FKS route has the internally proved disk, pair, deleted-pair,
finite-jet, summability and asymptotic consequences it uses. Neither ledger
concern is an additional estimate premise of the selected absolute-tail
theorem. In particular, the old intermediate-sector finite-jet attachment
blocker is superseded for this route.

This is different from a verbatim, jointly quantified export of every clause
of the two raw auxiliary lemmas. The reviewed source does not present a single
common-constant theorem containing all of `lem:originaldisk`'s conclusions.
Also, the original-K pair and deleted-pair endpoints use the undeformed
lambda-zero contour, whereas the named-current endpoints cover the full
lambda interval. A broader assertion about deformed K supports at every lambda
is not claimed here. These distinctions must remain visible if the manuscript
auxiliary labels are described clause by clause.

## Manuscript contracts

The immutable manuscript is `source_snapshot/manuscript.tex`.

- Lines 736–739, equations `eq:FKS` and `eq:current`, define
  `K_N = integral psi U_(0,s)` and the current as the integral of the named
  weighted density over `0 <= lambda <= 1`. Thus the exact decomposition needs
  K on the undeformed contour and currents on the whole homotopy interval.
  Lines 777–780 explicitly keep parameter differentiation before the moving
  current split.
- Lines 1036–1057, `lem:contraction`, state radial-center complete-pair
  suppression on K and named-current supports, full-lambda and occupancy
  uniformity, three-group strict/slack bounds, surviving-product suppression
  after deleting at most j pairs, and bounded fixed pair jets in regular
  branch and compact coordinates. They expressly do not assert uniform raw
  branch-angle jets.
- Lines 1223–1233, `lem:originaldisk`, state a fixed c-epsilon disk, holomorphy
  of the original/K/current densities, separate linear Y and Z gaps, Gaussian
  pair suppression on K/current supports, and C^N integrated one-body and
  Jacobian costs uniform in N and lambda.
- Lines 1276–1288 explain why the branch majorant is independent of the
  coupled occupancy and hence can be integrated as a product. Lines 1306–1309
  explicitly exclude an unrestricted-original-torus Gaussian pair claim.

## Original disk: actual source route and quantifiers

Fix `d : LocalBranchData` and
`d.c₀ < Real.sin d.theta / 2`. The following are proved theorems, not setup
fields supplied by the final theorem's caller.

### Disk and holomorphy

- `IsingBulk/Tail/OriginalDiskGlobalFactors.lean:8`,
  `original_disk_trace_margin`, chooses positive disk and epsilon constants
  before epsilon, the complex parameter and every angular variable. It places
  the entire closed c-epsilon disk in the genuine damping domain.
- `IsingBulk/Tail/SelectorDerivativeDistribution.lean:13`,
  `weighted_homotopy_slice_analytic`, proves analyticity on that damping domain
  for every fixed nonnegative lambda and every continuous angular weight.
  Its proof constructs analyticity of the literal continued density using
  `continuedContourDensity_analyticAt`, the actual positive dispersion and
  nonvanishing Y/Z factors. The declarations `selected_and_lower_analytic`
  at line 59 and
  `IsingBulk/Tail/OriginalCurrentCauchyTransfer.lean:11`,
  `actualCurrentSlice_analytic_on_damping`, attach the actual K and current
  integrals. No density-holomorphy certificate is an external premise.

### Complete pairs, one-body integrals and Jacobian

- `IsingBulk/Tail/OriginalCompletePairProduct.lean:81`,
  `original_actual_source_pair_product`, chooses an eta cap; after eta, it
  chooses alpha/disk/epsilon caps, a positive exponential base and a positive
  Gaussian rate. These precede alpha, N, epsilon, angles and s. The result is
  for the literal `angleTuple` and `globalRoot` on the closed support of
  `angularSelector`, throughout the c-epsilon disk. K is at lambda zero.
- `IsingBulk/Tail/OriginalCurrentCompletePair.lean:16`,
  `original_current_actual_complete_pair_product`, chooses eta, then
  alpha/tau caps, then c/e/B/kappa after alpha/tau. These constants precede
  N, epsilon, lambda, the named current index, angles and s. The estimate holds
  for every N >= 1 and every lambda in [0,1] on the named current's closed
  support. The tuple is the actual `deformedPoint`, including its coupled
  occupancy; occupancy is not supplied as a fixed independent parameter.
- `IsingBulk/Tail/OriginalResidueL1.lean:35`,
  `original_residue_l1_oneperiod`, supplies a uniform original one-period L1
  residue bound throughout a fixed c-epsilon disk. It retains both integrable
  branch singularities.
- `IsingBulk/Tail/OriginalCurrentOneBody.lean:15`,
  `original_current_actual_onebody_bound`, supplies a product-integrable
  coordinate majorant for actual named-current supports, uniformly for
  N >= 1 and lambda in [0,1]. Its constants precede N, epsilon, lambda, angles,
  the named index and s. The majorant depends on each angle and epsilon, not
  on treating the coupled occupancy as constant during integration.
- `IsingBulk/Tail/SelectorJacobianBounds.lean:62`,
  `constructed_selector_jacobian_bound`, supplies the constructed selector's
  actual Jacobian cost. `OriginalCurrentEnvelope.lean` combines this with the
  actual current multiplier and the preceding bounds.

### Separate linear gaps versus the exported combined gap

`IsingBulk/Tail/OriginalCurrentGlobalFactors.lean:56`,
`original_current_global_factors`, exports the inverse-product numerator
bound and

`G * epsilon^2 <= norm ((1-Z) * (1-Y))`.

This combined bound is exactly sufficient for the density envelope. It should
not be described as a theorem whose conclusion literally states the two
separate manuscript inequalities. However, the proof at lines 119–131 already
establishes, with positive constants fixed before N/epsilon/lambda,

`norm Z <= exp (-a * epsilon)` and `norm Y <= exp (-c * epsilon)`.

The exported theorem
`IsingBulk/Tail/ProtectedSourceRoots.lean:126`,
`exponential_attenuation_linear_gap`, then gives

`a * exp (-a) * epsilon <= norm (1-Z)` and
`c * exp (-c) * epsilon <= norm (1-Y)`.

Taking the smaller positive coefficient gives the manuscript's common linear
gap constant. This explains the mathematical content available in the existing
proof; this review has not added a theorem exporting that combined package.

### Endpoints actually consumed downstream

`IsingBulk/Tail/OriginalLowerIntegralBound.lean:12`,
`original_lower_integral_gaussian_bound`, and
`IsingBulk/Tail/OriginalCurrentEnvelope.lean:16`,
`original_current_complete_envelope`, explicitly combine the preceding
constants by minima and the actual integrals by their source identities.

`IsingBulk/Tail/OriginalLowerCauchy.lean:13`,
`original_lower_derivative_gaussian_bound`, chooses c/e/C/K/kappa before every
derivative order j, particle number N >= 2 and epsilon. It bounds the actual K
derivative by a factorial/Cauchy factor times
`C^N * epsilon^(-j-2) * exp (-kappa * N^2)`.

`IsingBulk/Tail/OriginalCurrentCauchy.lean:13`,
`original_current_small_integral_gaussian_bound`, similarly chooses constants
before j, N >= 1, epsilon and the cutoff in [0,1]. Its conclusion includes
interval integrability and the norm of the actual integral of
`differentiatedCurrentSlice` over `0..cut`. The endpoint is chosen after
differentiation; no moving cutoff is differentiated.

`IsingBulk/Tail/HighKSBound.lean:21`, `actual_highKS_gaussian_bound`, combines
these actual source quantities. `IsingBulk/Tail/HighKSTail.lean:104`,
`actual_highKS_epsilon_tail_finite_j`, then chooses one D for every j below a
fixed finite ceiling. No raw `lem:originaldisk` proposition or desired highKS
bound is introduced as an assumption.

## Contraction and finite jets: attachments now present

### Surviving products, without division

`IsingBulk/Tail/MixedDeletedPairSource.lean:189`,
`original_actual_source_deleted_pairs`, and line 227,
`original_current_actual_source_deleted_pairs`, prove the literal product of
pair norms over the ordered pairs outside a deleted finite set E. For
`E.card <= j`, the bound is `(B j)^N * exp (-kappa * N^2)`.
The positive kappa and geometric/epsilon/disk thresholds precede j; the base
`B j` is permitted to depend on the finite number of deleted pairs. The current
statement covers the full lambda interval and actual coupled tuple.

These proofs invoke three-group counting on the remaining pairs. They never
divide a complete product by a deleted factor. Zeros therefore create no
division issue. Their individual strict/slack estimates come from internally
proved branch bounds and actual compact/cross tuple transfer.

### Mixed and left sectors

- `IsingBulk/Tail/MixedActualPairFamily.lean:10`,
  `mixed_actual_sector_pair_family`, identifies the active-coordinate pair
  with the literal canceled pair, proves analyticity, and bounds all jets up
  to the requested finite order with constants chosen before N and the
  varying source variables. It retains cutoff-jet supports. Its small-current
  domain includes `lambda * tau < t₀`; it is not advertised as an unrestricted
  full-lambda jet theorem.
- `IsingBulk/Tail/MixedGaussianAmplitudeJets.lean:109` and line 176,
  `mixed_current_regular_amplitude_jets` and
  `mixed_original_regular_amplitude_jets`, instantiate the generic
  changed-factor product bound with those actual pair jets and the actual
  deleted-pair estimates. They yield the Gaussian finite-jet amplitude bound.
- `MixedSourceJetFamily.lean`, `MixedOriginalPointwise.lean` and
  `MixedCurrentPointwise.lean` attach the source coefficients, recurrence and
  real weights. `LeftCompactOriginalPointwise.lean:13`,
  `left_compact_original_pointwise`, and
  `LeftCompactCurrentPointwise.lean:12`, `left_compact_current_pointwise`, also
  consume those proved amplitude jets. The integrated mixed/left endpoint is
  `MixedLeftAsymptotic.mixed_left_sector_sum_littleO`.

### Compact-right and all-branch sectors

- `IsingBulk/Tail/PeriodicGaussianPairs.lean` transfers the literal deleted
  products to all angular representatives while retaining actual source
  support.
- `IsingBulk/Tail/CompactCompletePairJets.lean:63`,
  `actual_compact_complete_pair_uniform_jets`, and
  `CompactGaussianNumeratorJets.actual_compact_regular_numerator_deleted_jets`
  attach the real smooth changed-factor argument.
- `IsingBulk/Tail/UniformCompactGaussianJets.lean:12` and line 58,
  `original_compact_sector_gaussian_jets_uniform` and
  `current_compact_sector_gaussian_jets_uniform`, instantiate the surviving
  product bounds and include source weights. Their selector thresholds and
  Gaussian rate precede the compact interval and finite derivative order.
  Their local source-margin restrictions are subsequently enforced in the
  window proof. They reach `CompactRightClosure.compact_right_sector_sum_littleO`.
- `IsingBulk/Tail/RegularPairNeighborhood.lean:35`,
  `branchCompletePair_finite_jets`, and
  `AllBranchExteriorPairJets.lean:11`,
  `allBranchExterior_complete_pair_jets`, provide the regular branch-coordinate
  route. They do not claim uniform raw branch-angle jets.

Thus the required finite-jet consequences are attached to the source sectors;
they are not merely an unused generic helper awaiting instantiation.

## Why the final assembly does not externalize a desired estimate

`IsingBulk/Tail/CommonAllSectorParameters.lean:103`,
`common_all_sector_parameters`, constructs its structure from the proved
sector endpoints at the fixed selected prime point and finite derivative
ceiling. Its fields are conclusions of that construction. In particular it
constructs one selector, cutoff exponent and particle threshold, and a
positive source-summability radius before every permitted j, epsilon and cut.

`ExactSectorNormDomination.originalKSNorm_le_sectors` derives the finite norm
comparison from the actual integral identities. Its reusable current-zero
premise is discharged by `constructed_current_all_branch_derivatives_zero`
in the common parameter structure. The actual integrated small-current
norms remain attached to `0..epsilon^beta`.

`IntermediateWindowAssembly.common_intermediateKSNormWindow_radialSeriesSmall`
uses that comparison and the proved sector sums, retaining both eventual
summability and little-o. `AbsoluteTailAssembly.common_absoluteUpperTailSmall`
then uses `actual_higher_tail_domination`, actual source summability, legal
cutoffs and radial damping. `selected_absolute_upper_tail_small` constructs
the common structure internally for all `j <= (2*p)^2/2-1`.

Consequently the generic helpers' analytic estimates and structure fields are
not extra external hypotheses of the final selected-tail theorem. The
absolute norm remains inside the infinite sum. The physical wrappers retain
their existing E1/E2/E3 boundaries.

## Remaining auxiliary-label scope, without creating a new final obstruction

1. A literal all-clauses, common-constant `lem:originaldisk` export is not
   supplied by this review. The actual final proof uses the already assembled
   complete integral/Cauchy consequences. Separate linear gaps are available
   from the existing attenuation proof but are not the literal conclusion of
   `original_current_global_factors`.
2. Manuscript lines 1039–1045 place K-support and full-lambda uniformity in one
   statement. The reviewed original-K product/deleted-product declarations use
   `angleTuple`, hence lambda zero; named-current declarations use the actual
   deformation for every lambda in [0,1]. No single exported broader
   deformed-K-for-all-lambda theorem was identified. Do not claim that stronger
   raw formulation verbatim from the current endpoint names. This does not
   weaken the source FKS objects, whose K term is explicitly at lambda zero.
3. A single raw finite-jet lemma on the whole stated support/parameter range
   should not be confused with the established, sufficient sector-specific
   jet routes. Those routes now feed all actual intermediate sectors, with
   their small-current restrictions enforced before use. The source-used
   attachment is implemented; broader packaging remains a separate claim.

These are precise boundaries on auxiliary-label reporting, not a finding of
an unproved load-bearing estimate in the new final FKS route. No ledger label
is promoted to CLOSED, CANDIDATE_CLOSED or AUDITED_CLOSED by this document.
