<!-- CONTINUATION_20261006_CURRENT_BEGIN -->
# Current Ising continuation: v0.2.1

The frozen v0.2.0 baseline (9,199 safe declarations) received an independent adversarial audit with verdict `PASS_WITH_NONBLOCKING_ISSUES` and no blocking or load-bearing mathematical defect. The Lean/post-audit release [v0.2.1](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/tag/v0.2.1), published on 2026-10-07, completes targeted remediation of those findings, including verification hardening and complete TAIL endpoint packaging. Its final validation is separate from that baseline audit; no independent re-audit of the entire v0.2.1 tree is claimed.

- Release commit: `de23d9475744fb4625666142d5a03b3d688195e6`
- Release tree: `c4f8dd4e81dba9e88e18dadfdb0778cf3771d1d2`
- Proof payload: `6989420e855e0c3d882ce51e302dbc6579890da81aa0fd866176bab583067715`

The exact v0.2.1 commit passed a clean full build, the project-wide axiom audit of 9,200 safe declarations, 14/14 endpoint checks, 13/13 targeted production regressions, 13/13 manifest controls, 6/6 Lean controls, and fresh kernel replay. The axiom union is exactly `propext`, `Classical.choice`, `Quot.sound`. Exact-commit [full CI run 37518976590](https://github.com/LeoLam233/ising-bulk-natural-boundary/actions/runs/37518976590) and [smoke CI run 37518976672](https://github.com/LeoLam233/ising-bulk-natural-boundary/actions/runs/37518976672) both completed with `SUCCESS`.

The core natural-boundary theorems are unchanged: the normalized theorem retains E3 and the physical theorem retains E1/E2/E3 as explicit external literature premises. The manuscript remains the frozen `v0.1-rc4` AI-assisted candidate proof; no independent human expert validation or peer review is claimed. Cached dependency binary/source correspondence remains trusted; build and fresh replay use the same Lean kernel implementation; the expected-ID pin is inside the Git commit, not cryptographically external.

Historical counts, stop instructions, open-tail claims and earlier audit schedules below remain historical. Current source mapping is in [CONTINUATION_SOURCE_CORRESPONDENCE.md](CONTINUATION_SOURCE_CORRESPONDENCE.md). Historical declaration inventories and receipts remain stage-specific evidence, not complete current-project inventories.
<!-- CONTINUATION_20261006_CURRENT_END -->

<!-- ASTRA_RECOVERY_CURRENT_BEGIN -->
# Astra continuation — current authority

Recovered from the verified 2026-10-04 00:40:48 UTC partial TAIL checkpoint.
All 1,585 payload files passed its verifier; the writable tree was separately
copied and hash-checked. Recovery deltas are already integrated; newer live
proof repairs were retained. See [recovery reconciliation](../../recovery_receipts/RECOVERY_RECONCILIATION.md).

Current status: COMPACT_RIGHT_VERIFIED — continuation checkpoint; TAIL remains partial.
The all-B exterior, mixed/left, and compact-right estimates are implemented.
The aggregate root build reaches 1,066 production modules (4,830 build jobs).
The compact-right endpoint is `IsingBulk.Tail.compact_right_sector_sum_littleO`.
It includes literal original and integrated named-current sectors, finite label
sums, and the permitted particle-window absolute sum, with one common selector
choice before width and derivative order. See [compact-right acceptance](../../recovery_receipts/compact_right_closure_acceptance.json).
The root build and all eight endpoint axiom checks passed. The subsequent full
declaration trust check passed for 9,125 kernel-safe project declarations, with
axiom union exactly `propext`, `Classical.choice`, `Quot.sound`.
See [full trust receipt](../../recovery_receipts/compact_right_checkpoint_full_trust.log).

The latest user instruction stops this run after the verified compact-right
continuation checkpoint. No new proof development on absolute TAIL or the final
natural-boundary theorem is authorized in this run. The next central target is
common-parameter and exact full-sector attachment to the intermediate KS window,
then the actual absolute TAIL little-o. Existing conditional endpoints retain
their explicit absolute-tail premise; `thm:tail` and `thm:nb` remain open.
No final clean candidate gate or independent adversarial audit is claimed.
The chronological continuation notes below retain their stage-local status.
Recovery evidence, historical FIRST evidence and dependency pins stay unchanged.
Use one agent; do not run `lake update` or mutate any remote repository.
<!-- ASTRA_CUTOFF_LIMIT_BEGIN -->
Verified continuation: the selected-pair cutoff now converges in every actual
parameter derivative of the original all-B integral. The source chart radius is
chosen before epsilon and the particle number. Removal uses the actual analytic
density on the compact chart, bounded measurable pair weights, and dominated
convergence at fixed positive epsilon; no puncture-flux premise is added.
This closes the qualitative truncation-removal step only. Uniform quantitative
near/far estimates, their integration, and full TAIL composition remain open.
See [compiled endpoint and trust receipt](../../recovery_receipts/cutoff_limit_acceptance.json).
<!-- ASTRA_CUTOFF_LIMIT_END -->

<!-- ASTRA_POSITIVE_DIAMETER_BEGIN -->
Verified continuation: the full positive-region two-kernel integral, including
all original branch arclength factors, is bounded with a positive diameter power.
Actual minimum/maximum pairs are selected after absolute values; their finite
cover costs at most N squared. The collision Jacobian is absorbed by one diameter
power. This is an alternative coordinate route to the source near-diagonal
mean/shape coarea, with a different intermediate power, not a claim of the source
polar exponent. Quantitative differentiated-numerator attachment, negative
coordinates, all-B closure, and final TAIL composition remain open.
See [compiled endpoint and trust receipt](../../recovery_receipts/positive_diameter_acceptance.json).
<!-- ASTRA_POSITIVE_DIAMETER_END -->

<!-- ASTRA_NEGATIVE_KERNEL_BEGIN -->
Verified continuation: the genuine regular-kernel density, including every
original branch arclength factor, has a full anchored negative-region integral
bound. A negative anchor supplies its own separated Z gap; a positive anchor
uses a distinct negative coordinate and the explicit reciprocal-distance log
integral. This equivalent decomposition needs no auxiliary negative cutoff
scale. The chart radius precedes epsilon and particle number. The separated
positive integral is also bounded. No external estimate is introduced.
Differentiated numerator/cutoff attachment, uniform all-B closure, the remaining
mixed/left and compact-right estimates, and final TAIL composition remain open.
See [compiled endpoints and trust receipt](../../recovery_receipts/negative_kernel_acceptance.json).
<!-- ASTRA_NEGATIVE_KERNEL_END -->

<!-- ASTRA_COLLISION_ATTACHMENT_BEGIN -->
Verified continuation: the positive weighted kernel integral is attached to the genuine regular-kernel density with an internally derived common radius. Actual near-numerator jets retain their natural collision powers; the recovered Lie filtration leaves diameter power N(N-1)-2j. The selected-pair guard has a pole bound independent of its removal scale. Multiplication by fixed cutoffs preserves one inverse scale per spatial derivative. These are intermediate attachments: the complete spatial cutoff, generated-term integration, uniform all-B estimate, remaining mixed/left and compact-right estimates, and final TAIL composition remain open. No new external input is added.
See [compiled endpoints and trust receipt](../../recovery_receipts/collision_attachment_acceptance.json).
<!-- ASTRA_COLLISION_ATTACHMENT_END -->

<!-- ASTRA_NEAR_SOURCE_BEGIN -->
Verified continuation: the complete generated near-source Lie sum now has a uniform local bound with diameter power N(N-1)-2j, using actual numerator jets and actual regular coefficients. The radius and constants precede particle number, epsilon, the spatial cutoff, and the artificial pair-cutoff scale. The remaining spatial-jet input is separately proved for the actual fixed chart cutoff times the near-equality anchor cutoff, without an exponential equality-scale factor in its constant. Support/parameter assembly, integration and limit passage for the full source estimate, uniform all-B closure, and final TAIL composition remain open. No new external input is added.
See [compiled endpoints and trust receipt](../../recovery_receipts/near_source_acceptance.json).
<!-- ASTRA_NEAR_SOURCE_END -->

<!-- ASTRA_NEAR_INTEGRAL_BEGIN -->
Verified continuation: the actual full near-chart parameter derivative is bounded, with original numerator/regular coefficients/kernel, actual smooth anchor and equality cutoffs, finite pair partition, and removal of the artificial pair cutoff. The intermediate majorants are proved internally. Constants are fixed before epsilon, particle number, microcore radius b and equality radius rho; fixed chart cutoff constants precede b and rho. The explicit bound retains N(N-1)-2j collision powers and the one inverse diameter in the positive-kernel cost. This equivalent extreme-pair route differs from the manuscript's polar shape calculation but is not yet promoted to its final uniform estimate. Exponential-scale growth absorption, the complete far-chart bound, source partition/window assembly, remaining sector estimates and final TAIL composition are open. No new external input is added.
See [compiled endpoints and trust receipt](../../recovery_receipts/near_integral_acceptance.json).
<!-- ASTRA_NEAR_INTEGRAL_END -->

<!-- ASTRA_FAR_INTEGRAL_BEGIN -->
Verified continuation: the actual complete far-chart derivative is bounded after internally estimating the generated source sum, integrating its majorant, removing the artificial pair puncture and summing the finite pair partition. The original numerator retains the exact Gaussian pair budget; cutoff and separation losses are explicit. The support has a named anchor and arbitrary coordinate signs. For negative coordinates the already verified anchor/logarithmic alternative is reused; the majorant conservatively adds an extra inverse far separation. All constants precede particle number, epsilon, b and rho, apart from explicit displayed dependence. Both near and far actual chart derivative bounds now compile. Exponential-scale growth absorption, source partition/window assembly, the remaining sector estimates and final TAIL composition remain open; prop:allB remains PARTIAL. No new external input is added.
See [compiled endpoints and trust receipt](../../recovery_receipts/far_integral_acceptance.json).
<!-- ASTRA_FAR_INTEGRAL_END -->

<!-- ASTRA_KERNEL_SCALAR_BEGIN -->
Verified continuation: the exact near/far kernel cost at epsilon=exp(-H) is bounded by K*N^4*max(1,lengthC)^N*a^(-1)*D^(Q-1)*(H+1)^2 for H>=0, 0<a,D<=1, 0<=R<=1 and N,Q>=1. K is fixed before all these variables. This isolates the full radial dependence without a new analytic premise and retains the single positive-Jacobian diameter loss. Full exponential-scale absorption and source-window assembly are still open; prop:allB and final TAIL remain PARTIAL. No new external input is added.
See [compiled endpoints and trust receipt](../../recovery_receipts/kernel_scalar_acceptance.json).
<!-- ASTRA_KERNEL_SCALAR_END -->

<!-- ASTRA_EXTERIOR_SCALE_BEGIN -->
Verified continuation: scalar majorants including the anchor/pair polynomial count, actual near/far cutoff costs, regular coefficient budgets, and the simplified kernel cost are summable after the prescribed exponential radii are substituted. The near majorant uses a conservative collision slope (1+2U)/b, whose geometric applicability remains to be attached. Its positive cubic bound is fixed independently of the equality exponent B; a threshold B0 is chosen first and every B>=B0 yields summability. This is a coarser constant selection than the manuscript's half-coefficient cubic calculation, with the same final decay and no strengthened external premise. The far majorant is summable for every fixed B by the already proved Gaussian numerator estimate. Attaching the geometric conditions and uniform epsilon window, the actual source partition, remaining sectors and final TAIL chain is still required. prop:allB remains PARTIAL.
See [compiled endpoints and trust receipt](../../recovery_receipts/exterior_scale_acceptance.json).
<!-- ASTRA_EXTERIOR_SCALE_END -->

<!-- ASTRA_EXTERIOR_GEOMETRY_BEGIN -->
Verified continuation: the coarse near slope (1+2U)/b is now proved to dominate U/sqrt(b/4). A single lower threshold for the equality exponent ensures its product with 4rho is at most one, as well as the source's common-sign scale inclusion, for every N>=1. Every fixed multiple of epsilon is uniformly smaller than b throughout N<=D*sqrt(H) at one eventual H threshold. The source higher-even-order condition implies 2j+2<=N(N-1). These discharge the geometric premises of the near/far scale route; assembly into the actual source-window theorem, remaining sectors and final TAIL composition is still open. prop:allB remains PARTIAL.
See [compiled endpoints and trust receipt](../../recovery_receipts/exterior_geometry_acceptance.json).
<!-- ASTRA_EXTERIOR_GEOMETRY_END -->

<!-- ASTRA_ALLB_CLOSURE_BEGIN -->
Verified continuation: prop:allB is now IMPLEMENTED. The actual near/far chart derivatives are identified with every term of the literal angular partition. A common cutoff choice handles all j<=k; the named-anchor norm sum has the displayed source bound and the stronger summable-N bound S(N)(H+1)^2. Its absolute window sum is proved o(epsilon^(-1/2)). The source endpoint constructs BranchEstimates internally, and the original all-B sector is bounded by its microcore plus this complement. The positive-region proof uses the already verified min/max diameter-weighted coarea route; the larger conservative near slope is absorbed by choosing the equality exponent after all fixed-order constants. No external TAIL premise is added. Mixed/left, compact-right, combined-sector attachment, final TAIL composition, and the clean candidate gate remain open; this is not a completed project candidate.
See [compiled endpoints and trust receipt](../../recovery_receipts/allb_closure_acceptance.json).
<!-- ASTRA_ALLB_CLOSURE_END -->

<!-- ASTRA_ALLB_ATTACHMENT_BEGIN -->
The original all-B sector's full absolute window sum is now attached: selected_original_allBranch_window_littleO combines the compiled microcore and complement estimates on the literal original contour. One angular width handles all j <= (2p)^2/2-1. For each fixed D >= 0, the sum over 2p+2 <= N <= D sqrt(log(1/epsilon)) is eventually summable and is o(epsilon^(-1/2)). Particle-offset padding preserves the actual particle index and exact infinite sum. This closes the all-B attachment previously listed as subsequent work. Mixed/left, compact-right, final composition, and the clean candidate gate remain open.
See [compiled endpoints and trust receipt](../../recovery_receipts/allb_attachment_acceptance.json).
<!-- ASTRA_ALLB_ATTACHMENT_END -->

<!-- ASTRA_MIXED_SCALAR_TRANSPORT_BEGIN -->
The literal mixed-sector scalar transport is now identified with the three active analytic directions. The compact residual has the required minus sign. The identity holds at arbitrary nearby source points with background, analytic function, and residual models fixed before differentiation; it retains the coupled contour and all spectator parameter dependence. Assumptions are explicit source smoothness, active selector plateaus, branch sign, and the actual separated domain, with no estimate imported as a new premise. Hybrid-volume divergence and the iterated full-density/integral estimate remain open; prop:mixed is still PARTIAL.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_scalar_transport_acceptance.json).
<!-- ASTRA_MIXED_SCALAR_TRANSPORT_END -->

<!-- ASTRA_MIXED_DENSITY_GERM_BEGIN -->
The actual mixed density has a compiled recurrence on a joint source neighborhood with its analytic background fixed. The hybrid divergence equals the sum of the two residual directional derivatives; both simple global kernels are proved frozen and the full coupled determinant and factorial/contour normalization are preserved exactly. Source smoothness, selector plateaus, branch sign, and separated-domain facts are explicit. Residual and amplitude analyticity are the same local analytic properties already established by the actual source jet modules, not external estimates. The new source-germ bridge supports iteration but does not itself close the real-cutoff descendant recurrence, kernel coarea estimates, or uniform mixed/left integrated bound. prop:mixed remains PARTIAL; the final theorem chain and clean candidate gate remain open.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_density_germ_acceptance.json).
<!-- ASTRA_MIXED_DENSITY_GERM_END -->

<!-- ASTRA_MIXED_DENSITY_EXPANSION_BEGIN -->
The literal unfrozen mixed source density now has an exact finite all-order expansion in the existing sparse analytic recurrence. Every real-cutoff derivative is retained, and restriction to active coordinates is proved to commute with the actual Lie iterates on the source smoothness domain. The finite expansion has (N+1)^k terms and its pointwise norm budget exposes the original normalization, both simple kernels, and the full hybrid branch volume for subsequent absolute integration. Analyticity and finite jet bounds remain explicit internally supplied hypotheses of the reusable attachment theorem; no quantitative mixed estimate is asserted before instantiating the source constants and integrating. Uniform mixed/left source estimates, compact-right, final composition, and the clean candidate gate remain open.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_density_expansion_acceptance.json).
<!-- ASTRA_MIXED_DENSITY_EXPANSION_END -->

<!-- ASTRA_MIXED_SOURCE_POINTWISE_BEGIN -->
Actual original and named-current mixed-sector pointwise estimates are now proved from internal source geometry and finite jet estimates. Uniform constants are selected after any sufficiently small positive inner width; the Gaussian coefficient precedes the derivative order and particle number. The complete Lie iterate, including real cutoff derivatives, full contour determinant, factorial/contour normalization, and actual -2 i tau current multiplier, is bounded by C^N N^(5 order) exp(-kappa N^2) times the norm of the two simple kernels and full branch-volume product, for every k <= order on the actual sector support. Source slope separation and current selector plateau germs are discharged internally; original lambda-zero selector independence removes any plateau requirement on its outer anchor. No quantitative integrated mixed estimate is asserted: positive/negative absolute kernel integration and the left-sector route remain open, along with compact-right, final composition, and the clean candidate gate. No external inputs were added.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_source_pointwise_acceptance.json).
<!-- ASTRA_MIXED_SOURCE_POINTWISE_END -->

<!-- ASTRA_MIXED_POSITIVE_COAREA_BEGIN -->
The actual mixed two-phase coordinate map, its determinant, and injectivity on convex source cells are compiled. Its full-dimensional positive-branch coarea bound retains coupled occupancy and integrates all unchanged spectator coordinates with their scalar L1 costs. A common branch majorant is uniform in particle number, epsilon, lambda, and admissible occupancy, and has a fixed integral cost on the whole angular interval. These are internal tools with explicit cell geometry hypotheses, not yet the full source mixed estimate: the source angular cover, negative-branch integration, and left-sector route remain open. No external inputs were added.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_positive_coarea_acceptance.json).
<!-- ASTRA_MIXED_POSITIVE_COAREA_END -->

<!-- ASTRA_MIXED_POSITIVE_DENSITY_BEGIN -->
The positive branch half of the literal all-order original and current mixed Lie densities is now integrated from internal source estimates. A finite scalar interval cover includes all compact-anchor support endpoints; source geometry proves the selected slope cone, separation and selector plateaus on its enlarged convex cells. Every actual unselected branch factor is dominated uniformly in the coupled occupancy by the proved scalar L1 majorant, while compact spectators pay the unit measure. The final positive-half endpoints have no caller-supplied density, geometric or integration bound: they compose the actual Gaussian pointwise theorem, Lie integrability and exact support inheritance with these cell estimates. The Gaussian coefficient precedes derivative order and dimension; the current estimate is uniform in lambda subject to the recorded small-product constraint. These endpoints explicitly require a selected branch and a nonbranch compact anchor, and estimate only the positive angular half. Negative-half integration, zero-support assignments, the left route and the full source-window little-o composition remain open; prop:mixed remains PARTIAL. No external inputs were added.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_positive_density_acceptance.json).
<!-- ASTRA_MIXED_POSITIVE_DENSITY_END -->

<!-- ASTRA_MIXED_NEGATIVE_DENSITY_BEGIN -->
Actual original and current all-order mixed Lie densities now have negative-half absolute integral estimates, complementing the positive-half endpoints. The selected branch attenuation absorbs the actual Z denominator; the true angular sum phase handles the Y denominator, and unchanged spectators retain the proved uniform L1 majorant. Both logarithmic costs are explicit. The final endpoints use internally proved source support, plateau, kernel, volume, integrability and Gaussian jet facts; the current multiplier and coupled occupancy are retained, lambda is uniform under its recorded small-product constraint, and kappa precedes derivative order. A compiled sign-combination lemma splits only the final absolute integral and requires no differentiated sign cutoff. These endpoints retain the explicit selected-branch/nonbranch-anchor conditions. Uniform scalar budget simplification, parameter reconciliation across the two signs, zero-support assignments and source-window composition are still needed before declaring the separated mixed estimate closed. The left all-compact route, compact-right estimate and final theorem composition also remain open. prop:mixed stays PARTIAL and no external inputs were added.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_negative_density_acceptance.json).
<!-- ASTRA_MIXED_NEGATIVE_DENSITY_END -->

<!-- ASTRA_MIXED_SECTOR_GAUSSIAN_BEGIN -->
The actual original and current separated mixed-sector derivatives now have full angular integral Gaussian bounds, after combining the two signs and simplifying both logarithmic kernel budgets. The bound is C^N N^(5*order+2) exp(-kappa*N^2) (H+1)^2 with epsilon=exp(-H), with kappa preceding derivative order and one eventual H cutoff uniform in N, labelled sector and k<=order. The literal source sector integral is identified with its full Lie iterate. A summable Gaussian envelope with this logarithmic cost is proved little-o of epsilon^(-1/2). The original endpoint allows arbitrary nonnegative tau; the current endpoint retains its stated positive small tau and lambda*tau<t constraints, with lambda uniform on that domain. Both endpoints still explicitly require a selected branch label and nonbranch anchor. Zero-support labels, whole-current lambda coverage, finite sector aggregation, the left all-compact and compact-right estimates, and final composition remain to be completed. prop:mixed remains PARTIAL, and no external inputs were added.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_sector_gaussian_acceptance.json).
<!-- ASTRA_MIXED_SECTOR_GAUSSIAN_END -->

<!-- ASTRA_MIXED_SECTOR_ASYMPTOTIC_BEGIN -->
The separated mixed route now includes all nested labels containing a true branch, their finite absolute original sum, and the finite absolute current sum after actual integration from zero to epsilon^beta. Impossible anchor-branch and named-current-branch assignments vanish identically; no nonbranch-label premise survives on the aggregate endpoints. The label counts are absorbed into the dimension-exponential factor. Both complete positive-particle sums are eventually absolutely summable and little-o of epsilon^(-1/2), proving a stronger full-sum conclusion for this component than the requested intermediate particle window. One inner width works for all k<=order. The current small-product restriction is satisfied uniformly on [0,epsilon^beta] for every fixed beta>0; the existing large-current route covers the rest. Source derivatives, the current multiplier, nested cutoffs and actual homotopy integral are retained. The left case with no true branch, compact-right estimate, common parameter composition and final theorem chain remain open. prop:mixed remains PARTIAL solely because its left all-compact case remains unclosed; no external inputs were added.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_sector_asymptotic_acceptance.json).
<!-- ASTRA_MIXED_SECTOR_ASYMPTOTIC_END -->

<!-- ASTRA_MIXED_LEFT_CLOSURE_BEGIN -->
prop:mixed is implemented. The left all-compact route now differentiates the actual density using the existing compact-root and fixed Z-gap jets, retains the Y kernel, integrates its true angular sum phase, and obtains a Gaussian particle envelope with logarithmic radial cost. Both original and current literal sector integrals and finite absolute sums are attached; the current determinant and multiplier are retained. MixedLeftAsymptotic reconciles the four previously separate parameter families into one acyclic selector/inner-width choice for all k<=order and every fixed beta>0, proving eventual absolute summability and little-o of epsilon^(-1/2) for their combined full particle sum. Exhaustive label classification leaves only all-compact right assignments beyond these components. Source Gaussian coefficients precede derivative order, and radial cutoffs are uniform in particle number, labels and the permitted lambda interval. Compact-right, attachment to the complete source decomposition, final TAIL/conditional/NB composition, and the single clean candidate gate remain open. No external inputs were added and no independent adversarial audit is claimed.
See [compiled endpoints and trust receipt](../../recovery_receipts/mixed_left_closure_acceptance.json).
<!-- ASTRA_MIXED_LEFT_CLOSURE_END -->

<!-- ASTRA_COMPACT_SOURCE_COAREA_BEGIN -->
Compact-right now has a compiled actual whole-cube two-pole coarea estimate. A finite ordered extreme-pair cover is taken only after absolute values, with every cell's injectivity already proved for the coupled source phase. Generic near/far integral attachments charge one diameter power or one inverse separation. The actual source kernel has no assumed root-modulus or phase multiplicity input: the existing original-disk coupled-root theorem and damping domain prove its floor, including the lambda interval. Differentiated compact-right numerator/Lie bounds, source-sector support and periodic attachment, finite-window summation, final TAIL composition, and the single clean candidate gate remain open. No external inputs or project axioms were added.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_source_coarea_acceptance.json).
<!-- ASTRA_COMPACT_SOURCE_COAREA_END -->

<!-- ASTRA_COMPACT_SELECTED_TRANSPORT_BEGIN -->
Compact-right source transport is now attached: joint source regularity, actual Y/Z kernel freezing, exact regular-density factorization, and all-order selected-pair Lie factorization compile. The selected-pair representation uses the raw angular determinant and will permit the existing polynomial pair weights to cancel selected-diagonal poles; it does not assume smoothness across a pole. The named current coordinate can be excluded explicitly. Curvature and the verified divided-determinant margin prove membership of the regular locus on the actual source intermediate window. Quantitative differentiated numerator/field jets, selected/full-diagonal flux control, periodic source-sector attachment, particle-window summation and final TAIL/conditional/NB composition remain open. No new external input or project axiom is used.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_selected_transport_acceptance.json).
<!-- ASTRA_COMPACT_SELECTED_TRANSPORT_END -->

<!-- ASTRA_COMPACT_SELECTED_JETS_BEGIN -->
The compact-right quantitative field blocker is closed: true joint source/angular log-Y and phase jets give polynomial bounds on the actual angular and parameter coefficients and raw determinant. The internal determinant margin then yields selected-pair field jets with polynomial N cost and degree -1. A real scaled jet calculus proves multiplication, reciprocal bounds, directional differentiation and the all-order two-scale-degree loss under Lie iteration. This does not yet close prop:compactR: weighted numerator jets, selected/full collision removal, source-sector integration and window summation are still required. The full TAIL/conditional/NB composition and normal final candidate gate also remain open. No new external premise or project axiom is introduced.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_selected_jets_acceptance.json).
<!-- ASTRA_COMPACT_SELECTED_JETS_END -->

<!-- ASTRA_COMPACT_WEIGHTED_JETS_BEGIN -->
The rational-weight quantitative calculus is implemented for arbitrary fixed allowed pair sets, including current free pairs. Polynomial numerator zeros and homogeneous denominator jets are retained separately through every Lie order. For M large enough, selected-pair poles are canceled by the weight without discarding the full-collision degree. The proof remains a real smooth argument and does not divide by a vanishing pair factor. The next load-bearing task is the actual regular-density numerator jet bound, followed by selected/full collision removal, periodic source-sector integration and compact-right window summation. TAIL and final conditional/NB composition remain open. No new external input or project axiom is used.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_weighted_jets_acceptance.json).
<!-- ASTRA_COMPACT_WEIGHTED_JETS_END -->

<!-- ASTRA_DEFORMED_VANDERMONDE_BEGIN -->
Actual coupled-coordinate and Vandermonde finite jets are implemented with constants chosen before particle number. The occupancy coupling is differentiated and diagonal vanishing is proved for the literal deformation. No pair factor is divided out. The full regular-density numerator and its far Gaussian bounds, collision removal and source-sector integration remain open, followed by compact-right window summation and TAIL/final composition. No new external premise or project mathematical axiom is introduced.
See [compiled endpoints and trust receipt](../../recovery_receipts/deformed_vandermonde_acceptance.json).
<!-- ASTRA_DEFORMED_VANDERMONDE_END -->

<!-- ASTRA_COMPACT_NUMERATOR_JETS_BEGIN -->
The actual compact regular numerator collision jets are implemented, including every source factor and the exact normalization. Direct determinant expansion cancels its factorial cost against the source factorial; no matrix inverse or stronger premise is used. The selected-pair weight and Lie calculus can now consume a proved numerator input. Remaining work is far-region Gaussian attachment, sector cutoff/current multiplier jets, selected/full collision removal and integral identities, compact-right window summation, and TAIL/final composition. No new external input or project mathematical axiom is introduced.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_numerator_jets_acceptance.json).
<!-- ASTRA_COMPACT_NUMERATOR_JETS_END -->

<!-- ASTRA_COMPACT_GAUSSIAN_JETS_BEGIN -->
Actual original and current Gaussian numerator jets are implemented by reusing the compiled source deleted-pair estimates. Periodic support transfer is proved rather than assuming signed-angle bounds. The decay rate is fixed before derivative order; no internal estimate is promoted to an external premise. Remaining work is sector cutoff/current-multiplier jets, selected/full collision removal and integral identities, compact-right window summation, and TAIL/final composition. No new external input or project mathematical axiom is introduced.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_gaussian_jets_acceptance.json).
<!-- ASTRA_COMPACT_GAUSSIAN_JETS_END -->

<!-- ASTRA_COMPACT_SECTOR_JETS_BEGIN -->
Compiled the actual sector-weighted near-collision and Gaussian numerator jets, including the complete current multiplier and full joint real derivatives. All constants are fixed before particle number and sector labels; kappa is fixed before derivative order. Remaining compact-right work is selected Lie attachment, collision cutoff removal, integral identities and window summation, followed by TAIL/final composition. No new external input or project mathematical axiom is introduced.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_sector_jets_acceptance.json).
<!-- ASTRA_COMPACT_SECTOR_JETS_END -->

<!-- ASTRA_COMPACT_GUARDED_INTEGRAL_BEGIN -->
Compiled the actual guarded source integral identity, convergence of all true parameter derivatives as the guard shrinks, radius-uniform real guard jets, and source attachment of guarded weighted Lie jets. The all-right signed sector has a smooth compact zero extension with unchanged local jets and integral. This route proves compactly supported flux cancellation and derives the cutoff limit without adding a flux premise or assuming analytic angular bumps. The next remaining attachment is the numerical near/far Lie bound and its coarea integral, then compact-right window summation and TAIL/final composition. No new external input or project mathematical axiom is introduced.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_guarded_integral_acceptance.json).
<!-- ASTRA_COMPACT_GUARDED_INTEGRAL_END -->

<!-- ASTRA_COMPACT_PAIR_INTEGRAL_BEGIN -->
Compiled allowed-pair diameter geometry, near/far value bounds for the actual guarded Lie operator, and a cutoff-free bound for every actual parameter derivative of the pair-weighted compact source integral. The source kernel and coarea estimates give Q^N N^4 (H+1)^2; the proof removes the guard by the established derivative limit, without a flux premise. Finite rational pair partitions reconstruct the full integral derivative with N^2 cost. Remaining: attach actual sector numerator jets to this bound, select a summable near scale, sum compact-right windows and compose TAIL/final theorems. No new external input or mathematical axiom.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_pair_integral_acceptance.json).
<!-- ASTRA_COMPACT_PAIR_INTEGRAL_END -->

<!-- ASTRA_COMPACT_SUMMABLE_MAJORANT_BEGIN -->
Compiled the complete near/far full-integral composition estimate, the explicit summable particle majorant with an exponential collision split, uniform-in-interval selector/Gaussian quantifiers, and exact literal-sector to compact-integral derivative bridges. The stronger uniform Gaussian statements reuse the existing deleted-pair proof; no prior claim is assumed with strengthened quantifiers. The exponential split is documented as an alternative proof representation. The live compact-right source node remains partial until actual source jets are combined into a uniform window estimate and the sector sums are closed. No new external premise or mathematical axiom.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_summable_majorant_acceptance.json).
<!-- ASTRA_COMPACT_SUMMABLE_MAJORANT_END -->

<!-- ASTRA_COMPACT_RIGHT_CLOSURE_BEGIN -->
Closed prop:compactR from the actual normalized source density, real smooth sector jets, source selected field, rational pair partition, coarea estimate, and cutoff derivative limit. Literal original and integrated-current compact-right windows have summable absolute norms with one common selector choice and all permitted derivative orders. The exponential near-radius alternative and its Gaussian far estimate preserve the source interval, branches, current range, and quantifier order. No compact-right estimate or flux identity is externalized. Remaining work: common parameters and exact full-sector decomposition for TAIL, then thm:conditional/thm:nb and the single normal clean candidate gate. No independent adversarial audit has been run.
See [compiled endpoints and trust receipt](../../recovery_receipts/compact_right_closure_acceptance.json).
<!-- ASTRA_COMPACT_RIGHT_CLOSURE_END -->

<!-- ASTRA_RECOVERY_CURRENT_END -->

<!-- TAIL_CONTINUATION_CURRENT_BEGIN -->
# TAIL and final-chain continuation

The user has authorized all TAIL nodes through thm:conditional and thm:nb. The prior FIRST-only boundary below is preserved historical evidence, not the current task scope. All older NOT_STARTED FIRST tables and FIRST-only/TAIL-unadvanced instructions below are historical and superseded for live status by this continuation header and the latest claim ledger; they do not undo verified FIRST candidate status. All 387 FIRST candidate source hashes matched at continuation start. Historical records were snapshotted before this additive update; see ../../tail_integration/CONTINUATION_BASELINE_RECEIPT.json.

Current stage: implementation in progress, no TAIL source node is CANDIDATE_CLOSED. Recovery 18:27–18:47 restored verified 18:18 source plus separately logged reconstructed deltas, exact pinned runtime/dependencies, and a fresh 4,132-job FIRST module build. The whole-exterior series and full conditional natural-boundary endpoint now have fresh targeted acceptance. Their genuine source statements retain all necessary hypotheses; no unconditional TAIL/nb conclusion follows yet. New generic final-chain supporting lemmas do not establish the physical sector estimates. Whole-exterior series convergence, actual sector attachment, full summation and the final natural-boundary theorem remain open. Three same-candidate full hostile audits are required after final clean freeze.

Dependency map: ../../tail_integration/DEPENDENCY_MAP.md. Baseline preflight: ../../environment/tail_continuation_preflight_20261003T1742Z/receipt.json. No new whole-tree clean build has yet been claimed.
<!-- TAIL_CONTINUATION_CURRENT_END -->

<!-- FIRST_PILOT_CURRENT_BEGIN -->
# FIRST pilot: current verified progress

Final source scope: all six FIRST nodes are CANDIDATE_CLOSED, not AUDITED_CLOSED. Symmetry is the internally constructed physical exterior germ plus symmetry of any continuation under consideration; its global existence and whole-exterior full-series convergence are not asserted. The three exact user-authorized Jets replacements are recorded separately from the preserved immutable r1. TAIL is unadvanced.

Baseline clean Linux build PASS on 2026-10-03 at 11:25 UTC: 3,629 jobs, 1,666 baseline declarations; exact three-axiom whitelist. Original baseline evidence remains unchanged.

The held modified tree received coordinated canonical-equivalent clean verification: environment/final_six_node_clean_20261003T1615Z. All production modules were included and frozen sources preserved. Source-node status is separate from this kernel verification. TAIL remains unadvanced.

- `lem:residue`: **CANDIDATE_CLOSED** — Actual normalized double-contour residue reduction, the complete canceled pair identity, the same arbitrary fixed continuous y-weight reduction, and absolute/stage integrability are proved from precisely the source enclosed-root/radius hypotheses. Apparent zero poles, every remaining rational denominator and successive Cauchy legality are discharged. The actual global radial root, branch identity and uniform complex-disk admissibility are constructed. Subsequent radius-locality and source-attachment bridges are proved.
- `lem:symmetry`: **CANDIDATE_CLOSED** — Actual normalized susceptibility exterior-germ symmetry is proved: the literal fixed-quarter-radius even-order series has an internally derived summable geometric majorant, absolute convergence and holomorphy near infinity, and both symmetry identities. Real-only physical E1 identifies that actual germ with the normalized physical real response. Any named holomorphic continuation on the unit exterior is proved unique and symmetric. Actual normalized even form-factor contour symmetries, including orientations, measures and prefactor branch, are also proved.
- `lem:mean`: **CANDIDATE_CLOSED** — The actual mean/zero-sum shape coordinate map and Jacobian, selected lower chart, b,d positivity, true Y pole derivative, explicit clockwise orientation and +2π residue are proved. Uniform source rectangles and pair/Z-pole exclusion are constructed. Actual displaced-side and smooth-edge integrals have every fixed-s derivative bounded on a common tube. The actual nonlinear denominator gap c(ε+Σt²) and full fixed-cutoff physical mean identity are proved, with selected arithmetic instantiated and arbitrary sufficiently small prescribed delta supported.
- `lem:period`: **CANDIDATE_CLOSED** — The literal constrained coordinate integral is absolutely convergent, equals the displayed beta formula and is nonzero. The actual zero-sum hyperplane, Euclidean measure/Jacobian 1/√N, Vandermonde degree, positive angular constant and precise source radial exponent are proved. A genuine real-positive scalar integral evaluation, complex half-plane analytic continuation and boundary dominated limit with explicit integrable majorant yield the principal-branch value, with every factor nonzero.
- `lem:complement`: **CANDIDATE_CLOSED** — The actual complementary double-contour integral has bounded fixed-order s derivatives. Exhaustive active-factor classification, real separation, true half-line exponential representation, all-q integration by parts including generated coefficient derivatives, actual fixed-radius differentiation/Fubini, uniform small/tail auxiliary integrability, genuine finite smooth torus refinement, seam lifts and finite integral sums are proved. The constructed compatible y-only remainder satisfies the exact support hypotheses. One epsilon threshold precedes all derivative orders; each bound may depend on its fixed order.
- `thm:first`: **CANDIDATE_CLOSED** — The literal source fixed-radius offsite T_(2p) has kth derivative 2L epsilon^(−1/2)+o(epsilon^(−1/2)) with actual L nonzero. Both local residues are attached through the same constructed delta, eta and chi; their actual coefficients are equal. The actual smooth/hard mean error is bounded and the true complement is controlled. Every j<k of this first term is bounded on one common interval. Every positive even lower N and every fixed derivative order is bounded via the narrow published full-site theorem and internally proved onsite subtraction/radius transfer.

## Module verification evidence

- `IsingBulk.First.ActualAmplitudeNeighborhood`: 4 kernel-safe declarations; source SHA-256 `f8bacc8214cc767e834f2cc9a2c2cf634bb6190a80a1d48bac6243ee5a33d3e2`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualAmplitudeNeighborhood.receipt.json`
- `IsingBulk.First.ActualDensityAnalytic`: 14 kernel-safe declarations; source SHA-256 `f7847d372d598e9e64c52d432231f598c8ce1e4d0803a23299e1a9e563ff9701`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualDensityAnalytic.receipt.json`
- `IsingBulk.First.ActualDensityBounds`: 9 kernel-safe declarations; source SHA-256 `c806b021ed8d3ac7c7074a0829a2e84e450239bd6f2ff6dece38489a6ad9b7a5`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualDensityBounds.receipt.json`
- `IsingBulk.First.ActualDensityCenter`: 30 kernel-safe declarations; source SHA-256 `cb135892e94f8ccbf33a1682d6250e260ac13a70e4a472a3b975878518fadc1c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualDensityCenter.receipt.json`
- `IsingBulk.First.ActualDensityExpansion`: 4 kernel-safe declarations; source SHA-256 `8cda27b2e4fb1ec8a0e4b390372679ad54eb67d73b4c4b9c1c8e34344a4eb06b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualDensityExpansion.receipt.json`
- `IsingBulk.First.ActualDensityJets`: 7 kernel-safe declarations; source SHA-256 `8c80a06eec4c5767174f9b917a1ea3e7075bbc325e9fad3f29f2d4026bcb79a6`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualDensityJets.receipt.json`
- `IsingBulk.First.ActualDensityNeighborhood`: 3 kernel-safe declarations; source SHA-256 `ee690852ac69120d800a130961eeeb91350416e21c68016de30ebbb4c8f02f45`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualDensityNeighborhood.receipt.json`
- `IsingBulk.First.ActualLeadingCoordinateLimit`: 7 kernel-safe declarations; source SHA-256 `2791cac1b3e00579aca1afcc5c0283e9943172adbdc6bcc55613eabb58f76bd7`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualLeadingCoordinateLimit.receipt.json`
- `IsingBulk.First.ActualLeadingDensity`: 14 kernel-safe declarations; source SHA-256 `5bd3f467db837a5bd5c867dbefedaace72435a046ba554f39df73b557f1bc1c7`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualLeadingDensity.receipt.json`
- `IsingBulk.First.ActualLeadingShapeLimit`: 2 kernel-safe declarations; source SHA-256 `9d535937e1d2ff63b390f4b896abbe98334dcb3a17813b872213c4401e1d764b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualLeadingShapeLimit.receipt.json`
- `IsingBulk.First.ActualLocalFullProfile`: 1 kernel-safe declarations; source SHA-256 `0112a592e5d9dbbde88c5ba81e3f42a55340ef5ecb6489b50aad7c5e51ee7e0a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualLocalFullProfile.receipt.json`
- `IsingBulk.First.ActualLocalLowerBounds`: 1 kernel-safe declarations; source SHA-256 `44790062d9066d3f2de0eebf66c18a1718eed3306bea450cfce12b8e7914e0b1`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualLocalLowerBounds.receipt.json`
- `IsingBulk.First.ActualLocalMeanAsymptotic`: 1 kernel-safe declarations; source SHA-256 `b4da51b970e0d0ee3fdad540df1a61e49e7454e139e9831a9a3d4c46833a2ed4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualLocalMeanAsymptotic.receipt.json`
- `IsingBulk.First.ActualLocalizedPostMeanAsymptotic`: 3 kernel-safe declarations; source SHA-256 `8ec67947e65b093b12bbb3978ec0caf04230b5bc9d87af2e5d23bcbe8403ce64`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualLocalizedPostMeanAsymptotic.receipt.json`
- `IsingBulk.First.ActualLowerDerivativeBound`: 12 kernel-safe declarations; source SHA-256 `6f73a5c26aa1250a6aa92e50022d606e519cf55fef26c4a6c9c1d0837d9e5c0d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualLowerDerivativeBound.receipt.json`
- `IsingBulk.First.ActualLowerIntegralBounds`: 3 kernel-safe declarations; source SHA-256 `28583b2f91dcdfb95cb4e3ff4d50f7021b57d18a9c4791de3d4b9a5f975f0b36`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualLowerIntegralBounds.receipt.json`
- `IsingBulk.First.ActualPoleDerivative`: 5 kernel-safe declarations; source SHA-256 `d442795c2e444aa1e0f79a31822e0e4ba96633623969bf2cd51cdd951d9d4118`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualPoleDerivative.receipt.json`
- `IsingBulk.First.ActualPostMeanAnalyticTube`: 12 kernel-safe declarations; source SHA-256 `1b616eaed42d8bd8f77e8471186ca3e09d3d484c3100009516041c507af87fff`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualPostMeanAnalyticTube.receipt.json`
- `IsingBulk.First.ActualPostMeanCoordinateLimit`: 7 kernel-safe declarations; source SHA-256 `02b2c21bb9ec8b5714c05d75ac4253b51cbea44c68ddab1e022e128c12ab3ba0`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualPostMeanCoordinateLimit.receipt.json`
- `IsingBulk.First.ActualPostMeanInterchange`: 12 kernel-safe declarations; source SHA-256 `5166dd138c3fdf0938fe907cfe7f24ae2ccdbd19eb86cabb59f4488edf45b38a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualPostMeanInterchange.receipt.json`
- `IsingBulk.First.ActualPostMeanLocalRegularity`: 4 kernel-safe declarations; source SHA-256 `0de290e05bfd54a16fc8809f9a5e89fd7f709742e6b9916ef0b1b59a3a2479a3`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualPostMeanLocalRegularity.receipt.json`
- `IsingBulk.First.ActualPostMeanShapeLimit`: 1 kernel-safe declarations; source SHA-256 `dfdc78dec5993e0e6b7562f81fcfd478e7a18262946b20b21a930b7f4f637183`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualPostMeanShapeLimit.receipt.json`
- `IsingBulk.First.ActualRemainderShapeBound`: 4 kernel-safe declarations; source SHA-256 `77b1f1bb1f301acde2057cebe676995225a697f3281db6336979b6d1e02f5c6d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualRemainderShapeBound.receipt.json`
- `IsingBulk.First.ActualShapeAmplitude`: 11 kernel-safe declarations; source SHA-256 `eb6956c229ab0dda15cf0fe23b803859f2733c034af8382ab5e285640d8d766e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualShapeAmplitude.receipt.json`
- `IsingBulk.First.ActualShapeDenominator`: 10 kernel-safe declarations; source SHA-256 `486380535523a13067b40ff5d0353e6983c4fe1b14d3f80abf9b4cff4857836b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualShapeDenominator.receipt.json`
- `IsingBulk.First.ActualShapeDerivative`: 5 kernel-safe declarations; source SHA-256 `264e1e6eb507fbcf6a21a506979051c34e4637c563bc16639d45f2750dac06cc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualShapeDerivative.receipt.json`
- `IsingBulk.First.ActualShapeIntegrability`: 2 kernel-safe declarations; source SHA-256 `d8abc9e20767e456dfd3794b38d24a41f344d4c7efda4eea94a5298fd323bfbc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualShapeIntegrability.receipt.json`
- `IsingBulk.First.ActualShapeNeighborhood`: 3 kernel-safe declarations; source SHA-256 `822414283bd71dd34437a08d865f8832969799991a9001e5ae781de7982059df`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualShapeNeighborhood.receipt.json`
- `IsingBulk.First.ActualVandermonde`: 21 kernel-safe declarations; source SHA-256 `f3936b68101eba26a79330cec3e383fe07dd9bd4549896c0da015781478b98a6`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ActualVandermonde.receipt.json`
- `IsingBulk.First.AnalyticQuadraticLimit`: 9 kernel-safe declarations; source SHA-256 `a18bc408cbf002337f251a7be3dafff49e1d45de8d767362f5add033c2ae8bc9`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AnalyticQuadraticLimit.receipt.json`
- `IsingBulk.First.AngularCoordinateSplit`: 1 kernel-safe declarations; source SHA-256 `0bf466b2dc75414d7d0cc4b058698a3f425da4aa434adc168a6ebbcac07124b6`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AngularCoordinateSplit.receipt.json`
- `IsingBulk.First.AngularFubini`: 7 kernel-safe declarations; source SHA-256 `9ef2cae98031c8b6ba8e6eb97bbe1467a6351aae3d45ae2316fff9863a04e911`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AngularFubini.receipt.json`
- `IsingBulk.First.AngularReindex`: 15 kernel-safe declarations; source SHA-256 `3745dc86a0a161a4043e386e20d10927fcb88731a04587f1ef0f1e913eb8c474`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AngularReindex.receipt.json`
- `IsingBulk.First.AngularResolvent`: 10 kernel-safe declarations; source SHA-256 `993fd6d3423d3acccc3ec3e4cba4b01263157d8313da8541dd080906c34b5a6f`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AngularResolvent.receipt.json`
- `IsingBulk.First.AnnularDensity`: 4 kernel-safe declarations; source SHA-256 `3693eb80c6c2d39322323735c81755057c9796e9b2058ed7232059de53e5e3b6`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AnnularDensity.receipt.json`
- `IsingBulk.First.AnnularOnsiteDensity`: 3 kernel-safe declarations; source SHA-256 `0f959b17d194a0696601cb4d6b2d8f0a5dc8d3d52023306abb306777f3096e5a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AnnularOnsiteDensity.receipt.json`
- `IsingBulk.First.AnnulusContour`: 9 kernel-safe declarations; source SHA-256 `8b40a60b94a1a24478aa7d4ee1994bba8370a37d20e5f528990ef7c19d2c0681`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AnnulusContour.receipt.json`
- `IsingBulk.First.AnnulusProduct`: 4 kernel-safe declarations; source SHA-256 `e54a8a9fc5211f7fa7ba0fa124234d6689508fe872d610f81636869f7ee6cf6e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AnnulusProduct.receipt.json`
- `IsingBulk.First.AuxiliaryDomination`: 4 kernel-safe declarations; source SHA-256 `b10b5424066d46d7ebb0bbd17792d44eb050f1bf98bc835067e0d6d0e3bbf228`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/AuxiliaryDomination.receipt.json`
- `IsingBulk.First.BulkSymmetry`: 12 kernel-safe declarations; source SHA-256 `c981ebf6140008225ff81af439c8527fcbe727c4d206d8b685806f9ac5cdf8e3`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/BulkSymmetry.receipt.json`
- `IsingBulk.First.CoefficientPhase`: 9 kernel-safe declarations; source SHA-256 `6c219354a306530d83f8884a389dfcb9d285009663b5aa1bf9a8ba9e76b98344`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CoefficientPhase.receipt.json`
- `IsingBulk.First.CompactAnalyticShapeIntegral`: 6 kernel-safe declarations; source SHA-256 `3386e74710a4fe365272c76e200a7e8691934a65efe201a700631c492d377da4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompactAnalyticShapeIntegral.receipt.json`
- `IsingBulk.First.CompactIntegralHolomorphic`: 2 kernel-safe declarations; source SHA-256 `8a6c1879fb153c297776b3e53633029ce21a384dc10d12bc39a2e9798780e838`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompactIntegralHolomorphic.receipt.json`
- `IsingBulk.First.CompactJetIntegral`: 2 kernel-safe declarations; source SHA-256 `68dd4c2bc43b150c61b604870689979cbe9102adcf027fa5265411e2a9646ff1`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompactJetIntegral.receipt.json`
- `IsingBulk.First.CompactParameterContinuity`: 1 kernel-safe declarations; source SHA-256 `973f39a9aaa894ba85b1287d12119d7e8387be5fca6fba1449c590d0f709c2ae`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompactParameterContinuity.receipt.json`
- `IsingBulk.First.CompactParameterIntegral`: 1 kernel-safe declarations; source SHA-256 `807f3e2c02e23a0de4d16fdac7c3d84a80a4137adf378c61738dbbbac13d63f4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompactParameterIntegral.receipt.json`
- `IsingBulk.First.CompatibleComplement`: 8 kernel-safe declarations; source SHA-256 `69cc3f88ff4426d5b762be9b5c37e4a21481a4c9de5a8ee023d6cef5079b0507`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompatibleComplement.receipt.json`
- `IsingBulk.First.CompatibleMeanAttachment`: 2 kernel-safe declarations; source SHA-256 `6f5c306be90c3a24670c710589775ddd937f024815b3528ead492147f3077ff0`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompatibleMeanAttachment.receipt.json`
- `IsingBulk.First.CompatibleMeanSource`: 3 kernel-safe declarations; source SHA-256 `0511b62fe8392dae2a0a8eb0d94bb4e0262d9f41e19d28a128e52451421ec63b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompatibleMeanSource.receipt.json`
- `IsingBulk.First.CompatibleYCutoffAtDelta`: 7 kernel-safe declarations; source SHA-256 `ae6b52163661e86c7d94a6e45630aa1770f4cdc69709424c7579cbc9743201d8`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompatibleYCutoffAtDelta.receipt.json`
- `IsingBulk.First.CompatibleYCutoffData`: 48 kernel-safe declarations; source SHA-256 `b7278ef6543b269ca8a6a3398d6e0c60141b53ffcb6581f6b8bc96d93850c65d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompatibleYCutoffData.receipt.json`
- `IsingBulk.First.CompatibleYLocalization`: 11 kernel-safe declarations; source SHA-256 `49c16d63e5c0e6d716bad0d1afb5e952d46c337753b88a04af1a103367617c20`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/CompatibleYLocalization.receipt.json`
- `IsingBulk.First.ComplementActiveChart`: 2 kernel-safe declarations; source SHA-256 `97d1d5aca066931fccd2918c2809593fdd9068ab06d9f9a6469ff2f3735fafd9`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementActiveChart.receipt.json`
- `IsingBulk.First.ComplementAuxiliary`: 17 kernel-safe declarations; source SHA-256 `7d739354dbcbf8a3525e76bf783b448ae1c49259b13058511cd4659927ef73e6`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementAuxiliary.receipt.json`
- `IsingBulk.First.ComplementAuxiliaryJets`: 8 kernel-safe declarations; source SHA-256 `56924417751fc97edae02f3e530a359c01b7a0312dac34099d6f691679da3157`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementAuxiliaryJets.receipt.json`
- `IsingBulk.First.ComplementAuxiliaryMajorant`: 2 kernel-safe declarations; source SHA-256 `1c9b836a3b17fbf9c7ad03ddf934abaecde0f02827fcbc26fa9a0a4edc3e3310`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementAuxiliaryMajorant.receipt.json`
- `IsingBulk.First.ComplementAuxiliaryTailBound`: 4 kernel-safe declarations; source SHA-256 `b4001e6493cb1a13f9dbf665c93610157cc4864f008bd26d54309f6af8de1fce`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementAuxiliaryTailBound.receipt.json`
- `IsingBulk.First.ComplementClosedDamping`: 3 kernel-safe declarations; source SHA-256 `cc77da30348b383abf4fa7b4a7d6595edb0d6cc0d00f4c5ce80e3727b6abbb47`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementClosedDamping.receipt.json`
- `IsingBulk.First.ComplementDampedGradients`: 30 kernel-safe declarations; source SHA-256 `02e57bb1fa66a467d575c7101c74bcd3004b9741abb747ffb1c14db95fa0ab91`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementDampedGradients.receipt.json`
- `IsingBulk.First.ComplementDamping`: 5 kernel-safe declarations; source SHA-256 `021762fd383c05562a502741ea3bb4c5e7de62d9a19f4a74ba1b7c5b7806592d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementDamping.receipt.json`
- `IsingBulk.First.ComplementDecay`: 10 kernel-safe declarations; source SHA-256 `42dd3771b875b2bae242215e8a1b8e4a9a172f35b7ab8aee80c948c6cadea174`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementDecay.receipt.json`
- `IsingBulk.First.ComplementExponentialProduct`: 5 kernel-safe declarations; source SHA-256 `caad3dcdaa3a54a7fcc3a00a79df24fffb5b8b4db7f2ba59f1a1966f5dda1a42`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementExponentialProduct.receipt.json`
- `IsingBulk.First.ComplementFactorization`: 25 kernel-safe declarations; source SHA-256 `6f36da5c19d8682228aba60311ee5e027ed0c6e1e8da86bd43366d9932ad5953`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementFactorization.receipt.json`
- `IsingBulk.First.ComplementFiniteAuxiliary`: 7 kernel-safe declarations; source SHA-256 `5f19abfbf9985785b8a7e25006434d2968a164d12160b3361ec004db4eef0fac`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementFiniteAuxiliary.receipt.json`
- `IsingBulk.First.ComplementFiniteRefinement`: 2 kernel-safe declarations; source SHA-256 `55486eaf8faa6d0fe2ae5f049d5378ff5354e6e46077f05d9b3246516338ff4f`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementFiniteRefinement.receipt.json`
- `IsingBulk.First.ComplementFiniteSum`: 3 kernel-safe declarations; source SHA-256 `4316bb83358736ea76743fdee8d73f9159c6610a8c501382f9df15ced60e4c8c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementFiniteSum.receipt.json`
- `IsingBulk.First.ComplementFubini`: 5 kernel-safe declarations; source SHA-256 `d670a7d85283b35bd0db15a12a12eb01a800441ca69d8671e90e98f15292fb0f`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementFubini.receipt.json`
- `IsingBulk.First.ComplementFullPhaseJets`: 11 kernel-safe declarations; source SHA-256 `1d0058c1775f6486d11c6f1fc3bce9df8ce3f646977a3af2020a77d11f548d65`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementFullPhaseJets.receipt.json`
- `IsingBulk.First.ComplementGeometry`: 65 kernel-safe declarations; source SHA-256 `bdc8e289813f04d4b8e4960306af23313c2997bf2644781098d906b5bfe18280`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementGeometry.receipt.json`
- `IsingBulk.First.ComplementGlobalBound`: 2 kernel-safe declarations; source SHA-256 `0633dfdd3a8158a890a345b442f1de039829f081a2d753d451b30099425dfa90`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementGlobalBound.receipt.json`
- `IsingBulk.First.ComplementGradients`: 16 kernel-safe declarations; source SHA-256 `75aa090bf27ed145ff8f3b56445cb5cac62c1f629803f7c4947471c5a51469aa`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementGradients.receipt.json`
- `IsingBulk.First.ComplementIBP`: 24 kernel-safe declarations; source SHA-256 `d5ca7e95bb17ecfd9e0eae6d2ff7d14a45f546b8b3eb78e9cfdebfde7e544a97`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementIBP.receipt.json`
- `IsingBulk.First.ComplementInactiveNeighborhood`: 3 kernel-safe declarations; source SHA-256 `28d121ac7af3146cc7c8e3d516e4f7253e0198044e8c34b282179ca4bc03bebe`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementInactiveNeighborhood.receipt.json`
- `IsingBulk.First.ComplementLocalBound`: 3 kernel-safe declarations; source SHA-256 `3c935d475b8cb829ffea3079e569234ace6f873a5ea927865b78ac8eda82a97a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementLocalBound.receipt.json`
- `IsingBulk.First.ComplementLocalFormFactor`: 1 kernel-safe declarations; source SHA-256 `ae51709b518a232ffd7f3f0056984ef979b23e3167ec2aa915286161c72e02ca`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementLocalFormFactor.receipt.json`
- `IsingBulk.First.ComplementLocalParameterRegularity`: 4 kernel-safe declarations; source SHA-256 `091f8889f25c7695cd374c09c9333576f13b8ee73a2556c65750ebedd2e07331`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementLocalParameterRegularity.receipt.json`
- `IsingBulk.First.ComplementLocalizedFactors`: 18 kernel-safe declarations; source SHA-256 `7261b54e3dc47144b62d66184a2451df437331444629e642f13bd57adedb117c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementLocalizedFactors.receipt.json`
- `IsingBulk.First.ComplementMixedRegularity`: 2 kernel-safe declarations; source SHA-256 `cb911f3c48b3239e45467aab3b5bb0d55950169b9f9db2691488d6b281398167`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementMixedRegularity.receipt.json`
- `IsingBulk.First.ComplementNormalizedJets`: 21 kernel-safe declarations; source SHA-256 `1eb3352835d3b84896f30452375f2bdff3fd967b7ca1f5c3c30ca61e51957b39`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementNormalizedJets.receipt.json`
- `IsingBulk.First.ComplementOnsiteGeometry`: 5 kernel-safe declarations; source SHA-256 `ba12605d3e8bf179bf96aac91f2a58a8d4017426a7209d5092adb09dda595d5e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementOnsiteGeometry.receipt.json`
- `IsingBulk.First.ComplementParameterJets`: 50 kernel-safe declarations; source SHA-256 `faf97aed8c0605b64141275ffa13442d19eef71ff60234f53536b10117a4dde5`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementParameterJets.receipt.json`
- `IsingBulk.First.ComplementParameterRegularity`: 5 kernel-safe declarations; source SHA-256 `12dced171bd0b6ad256710ae77ba313d8216a391b88b2b512d534b74013194d4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementParameterRegularity.receipt.json`
- `IsingBulk.First.ComplementPhase`: 9 kernel-safe declarations; source SHA-256 `c2e4c1e001254b44bff5e897a3b5f81e076120254aaacadafd099f6216c1b3aa`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementPhase.receipt.json`
- `IsingBulk.First.ComplementPhaseSum`: 14 kernel-safe declarations; source SHA-256 `75f883e4b7a0f4b7f390795dc0d0878a3b876e7811fc00d5b471ba7eca3e8395`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementPhaseSum.receipt.json`
- `IsingBulk.First.ComplementRadialChartDecay`: 1 kernel-safe declarations; source SHA-256 `148d3612d03f11c14f87ed32a1addf3c288b2e0030f6a6f1d25d0e2118798696`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementRadialChartDecay.receipt.json`
- `IsingBulk.First.ComplementRadialCompact`: 8 kernel-safe declarations; source SHA-256 `3eb96802b54b8285a82acee2f282ec25f679773dc54b409b5398fda35b1d706d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementRadialCompact.receipt.json`
- `IsingBulk.First.ComplementRadialRegularChart`: 1 kernel-safe declarations; source SHA-256 `16e6aba4c8ae51a5d900e3ac6f46cef5530eb427b408c59e8d8ebae71e506670`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementRadialRegularChart.receipt.json`
- `IsingBulk.First.ComplementSeparation`: 33 kernel-safe declarations; source SHA-256 `778d18d68dc2712130edfc059332e2cd5a7cf0e600f3ae69b2fd8d0349b2c80f`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementSeparation.receipt.json`
- `IsingBulk.First.ComplementSimplex`: 4 kernel-safe declarations; source SHA-256 `f0cac1f9cbc72dd9428dd22b2d7856d41fabb34a5a8031bfff23b18d63b9be09`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementSimplex.receipt.json`
- `IsingBulk.First.ComplementSmallAuxiliary`: 3 kernel-safe declarations; source SHA-256 `039ba3ad21aa9bfc342b65977867623b87b649400c8cfe4b08e5fe865399bd0b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementSmallAuxiliary.receipt.json`
- `IsingBulk.First.ComplementSourceAmplitudeSupport`: 2 kernel-safe declarations; source SHA-256 `193369f7b5fc55bf0a553d6dfc05f8723c64553d54b5e9b5ccc7a9b77f47caaf`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementSourceAmplitudeSupport.receipt.json`
- `IsingBulk.First.ComplementSourceAnalytic`: 5 kernel-safe declarations; source SHA-256 `9b4ea173b7872b1fde7b3cc2f290427e47eebc3aebe2a28b8da8d4358290a66c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementSourceAnalytic.receipt.json`
- `IsingBulk.First.ComplementSourceNormalizedJets`: 7 kernel-safe declarations; source SHA-256 `810808a7617cc2bf650c7dbb4b2b63876ae9d9ede1d62fbb84fe56e8bf6c9fb4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementSourceNormalizedJets.receipt.json`
- `IsingBulk.First.ComplementSourcePhaseSmooth`: 2 kernel-safe declarations; source SHA-256 `be35d0959d971a10a483b8a1250ab2cb2939c0c937708ebd66f710b81b84a875`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementSourcePhaseSmooth.receipt.json`
- `IsingBulk.First.ComplementSourceSmooth`: 6 kernel-safe declarations; source SHA-256 `07a7c58a273ece567ce441cd3185d51d8478cc0edb261d741a72b9098d2da7a1`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementSourceSmooth.receipt.json`
- `IsingBulk.First.ComplementSourceUniform`: 7 kernel-safe declarations; source SHA-256 `e084a8b2c7acb997dcd4bebea913dbe98942c2d19141b58738ea4489e96d4c8c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementSourceUniform.receipt.json`
- `IsingBulk.First.ComplementUniform`: 2 kernel-safe declarations; source SHA-256 `622ca2f145dd00b41a341b36ef6914df4415e3d0212fa049d8e05133f96fb69e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementUniform.receipt.json`
- `IsingBulk.First.ComplementVectors`: 36 kernel-safe declarations; source SHA-256 `67695147a952a0bc3f31dbda4b1bf7832c7c756b267889c19f33bcb2f71801d0`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ComplementVectors.receipt.json`
- `IsingBulk.First.ContourAngular`: 19 kernel-safe declarations; source SHA-256 `00d9392a9215e60c14bbecf1d1ec0db38eb68e9ecde5b7d360d14fdfe9894834`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ContourAngular.receipt.json`
- `IsingBulk.First.ContourDefinitions`: 33 kernel-safe declarations; source SHA-256 `d74981f80deaa2bf1aae0881b3b0608dd0b915ca72d7e9b1d1463b925f219d43`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ContourDefinitions.receipt.json`
- `IsingBulk.First.ContourIntegrability`: 15 kernel-safe declarations; source SHA-256 `1805d37a51f9cc39405fad1102444d65431f3aef39817e3429f5727f7ebb5a92`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ContourIntegrability.receipt.json`
- `IsingBulk.First.ContourNormBounds`: 4 kernel-safe declarations; source SHA-256 `8caf47872a82b68fd8752bb6c5b7571ae47bfc7c15879e06dce7e6343c2de840`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ContourNormBounds.receipt.json`
- `IsingBulk.First.ContourParameterDomain`: 2 kernel-safe declarations; source SHA-256 `74c62e8219391fae4e228628cc7ee2bbe4905ec944db4d283f8803eae9a29126`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ContourParameterDomain.receipt.json`
- `IsingBulk.First.DominatedAnalyticIntegral`: 4 kernel-safe declarations; source SHA-256 `6f6d8961655455a4a3d815b36248e33a96fa9a957f36414316efa5d232309e43`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/DominatedAnalyticIntegral.receipt.json`
- `IsingBulk.First.DoubleContourFubini`: 1 kernel-safe declarations; source SHA-256 `4f8912e03572d8bf5b948e4d3fbaf49d8dcc71d95c0b2879ad43ecfc8ef79761`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/DoubleContourFubini.receipt.json`
- `IsingBulk.First.DoublePeriodicBump`: 12 kernel-safe declarations; source SHA-256 `f260f1004700252e893bec5a7990e9ae1b1b7745e53a7f4f39f470e7b52b2131`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/DoublePeriodicBump.receipt.json`
- `IsingBulk.First.DoublePeriodicIntegral`: 3 kernel-safe declarations; source SHA-256 `656cc62cc306f2c88ca0bcf19a47360257fc0151473271847434073ad74a3650`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/DoublePeriodicIntegral.receipt.json`
- `IsingBulk.First.DoublePeriodicLiftIntegral`: 3 kernel-safe declarations; source SHA-256 `236946bd22e272fd32ab5566045d463546d846bcad5601107128fa1f2058cdd4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/DoublePeriodicLiftIntegral.receipt.json`
- `IsingBulk.First.ExteriorAnalyticGeometry`: 7 kernel-safe declarations; source SHA-256 `c6b5a7adb7b689b6114b290608c2a1251aef39f254383fb2f52a8e5993a0caa9`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ExteriorAnalyticGeometry.receipt.json`
- `IsingBulk.First.ExteriorContinuationUniqueness`: 1 kernel-safe declarations; source SHA-256 `e468bc3a1db59014812a34906423f6f81cef6b7d8415135bfaa908a3be3325a8`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ExteriorContinuationUniqueness.receipt.json`
- `IsingBulk.First.ExteriorIdentitySymmetry`: 5 kernel-safe declarations; source SHA-256 `d0bd5dc1e1800fba8333b57a0789a19c504940667dda6aa204cd78f5a18540f3`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ExteriorIdentitySymmetry.receipt.json`
- `IsingBulk.First.ExteriorSymmetry`: 3 kernel-safe declarations; source SHA-256 `1f5cd9d892d3c9bec1bab3b029585542033749e0d539cac928e768fad9c32383`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ExteriorSymmetry.receipt.json`
- `IsingBulk.First.FarExteriorAnnularDensity`: 6 kernel-safe declarations; source SHA-256 `05724b837fd09284da2e32ad04bfa2768128e43fd71d643d510a7d715649ddb3`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FarExteriorAnnularDensity.receipt.json`
- `IsingBulk.First.FarExteriorDensityBound`: 1 kernel-safe declarations; source SHA-256 `df37ed7a5600066696d9c03b5e1fae67f31a0e5a93aa688f545ccfc27aac4e3e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FarExteriorDensityBound.receipt.json`
- `IsingBulk.First.FarExteriorFormFactor`: 3 kernel-safe declarations; source SHA-256 `977a470733da0182ce7369d6eb70c23779bd153a24728129c3d03047c6c254de`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FarExteriorFormFactor.receipt.json`
- `IsingBulk.First.FarExteriorMixedContour`: 3 kernel-safe declarations; source SHA-256 `1451d429a6a3d770e9a4a5d0c119f32026d8064335e51bc97df6862310daacc4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FarExteriorMixedContour.receipt.json`
- `IsingBulk.First.FarExteriorRadiusIndependence`: 2 kernel-safe declarations; source SHA-256 `aad219beb4f09be9e45919cbde4aa4e9ec19f0ab307793976d243fcfb11f89f9`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FarExteriorRadiusIndependence.receipt.json`
- `IsingBulk.First.FiniteTorusBumpCover`: 3 kernel-safe declarations; source SHA-256 `29e25d9649f20b9b51656e4255966bbc59f4b5c5704ce1fbfb3181839091bd41`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FiniteTorusBumpCover.receipt.json`
- `IsingBulk.First.FiniteTorusRefinement`: 12 kernel-safe declarations; source SHA-256 `148c0d546479d9f8bae733bc0fd297586d25026e59f8a0efa30b46f4b46f7775`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FiniteTorusRefinement.receipt.json`
- `IsingBulk.First.FirstCoefficient`: 8 kernel-safe declarations; source SHA-256 `51f73c9fd7a9eb1c24a732b3a97e02598c29bdc76554731c4d780eacb18f5d58`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FirstCoefficient.receipt.json`
- `IsingBulk.First.FirstTheorem`: 5 kernel-safe declarations; source SHA-256 `ff911290da8735d017b9982a35b09faaa227a5fba59aa088c5445d9bb098152c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FirstTheorem.receipt.json`
- `IsingBulk.First.FirstUpperAsymptotic`: 5 kernel-safe declarations; source SHA-256 `26be86815ec2a2eb67f186e02db95c38b20d3a77ada9436690a793d8c05d9ff3`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FirstUpperAsymptotic.receipt.json`
- `IsingBulk.First.FixedRadiusAnalytic`: 3 kernel-safe declarations; source SHA-256 `634784e1623992fb47df706f48d5f4600ea9e76bddb0211936f544d38501ca47`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FixedRadiusAnalytic.receipt.json`
- `IsingBulk.First.FormFactorAnalytic`: 5 kernel-safe declarations; source SHA-256 `f46f8195953788400211e755d04edea94507c25ad6b173f32c57344706780000`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FormFactorAnalytic.receipt.json`
- `IsingBulk.First.FormFactorNormalization`: 2 kernel-safe declarations; source SHA-256 `ab0ae202491f05a32b2dbd2cf0fe68390106ad9694057bf99b25cb71bc1cb005`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/FormFactorNormalization.receipt.json`
- `IsingBulk.First.GlobalResidueRoot`: 11 kernel-safe declarations; source SHA-256 `4e051613e9ff5d9f44ffe29b9630b77ca337be3c60111260d5e40a5c9c472a51`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/GlobalResidueRoot.receipt.json`
- `IsingBulk.First.GlobalRootChartBridge`: 2 kernel-safe declarations; source SHA-256 `bbd90042f34516396c5a55d0a3640029c6e5a08ac877b62631b24592a9df2bd8`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/GlobalRootChartBridge.receipt.json`
- `IsingBulk.First.IntegratedMeanDecomposition`: 12 kernel-safe declarations; source SHA-256 `f206a304605a8ce1ecfaa7fe2e4ae3ed9f24057ee8ee641a9bc439db4c6397c7`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/IntegratedMeanDecomposition.receipt.json`
- `IsingBulk.First.InteriorRoot`: 13 kernel-safe declarations; source SHA-256 `867fa530034f7296c83dad36d06b2220cd620d3467e3be8de1f87f301746b92e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/InteriorRoot.receipt.json`
- `IsingBulk.First.JointPoleRegularity`: 7 kernel-safe declarations; source SHA-256 `de67564e63005f983404e22d6944314c918703812ed853d009cbc2e79af08516`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/JointPoleRegularity.receipt.json`
- `IsingBulk.First.LiftedSourceIntegrability`: 3 kernel-safe declarations; source SHA-256 `e6383ea3c5df5df298c17a91c5b46bd202b74be42832b0b9140bfc99ced3f53c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/LiftedSourceIntegrability.receipt.json`
- `IsingBulk.First.LocalizedAnalytic`: 4 kernel-safe declarations; source SHA-256 `4d1065b74fadca5b2e1b9842d489d284cda109c2e1232496a5bfd760945518c1`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/LocalizedAnalytic.receipt.json`
- `IsingBulk.First.LocalizedDouble`: 6 kernel-safe declarations; source SHA-256 `31b0a3bba092bd408f8f2dfe1202e93f3b2a7fee9a64d58b187fe34ae5c1f75f`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/LocalizedDouble.receipt.json`
- `IsingBulk.First.LocalizedPartition`: 4 kernel-safe declarations; source SHA-256 `7ba1b636bab9e79daef531b427a9bf1109897a70e6814f1a88bb8261752104ef`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/LocalizedPartition.receipt.json`
- `IsingBulk.First.LowerOrderCommonInterval`: 3 kernel-safe declarations; source SHA-256 `034f4c7751de6792467e199ab4372d6eafd2782a0bfb3d48f3bd4079485d5ef7`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/LowerOrderCommonInterval.receipt.json`
- `IsingBulk.First.LowerOrderFiniteWindow`: 3 kernel-safe declarations; source SHA-256 `033f35a8a90251e7284796c1eafdd494678a4382e74376f1080c189836d33546`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/LowerOrderFiniteWindow.receipt.json`
- `IsingBulk.First.LowerOrderFixedRadius`: 2 kernel-safe declarations; source SHA-256 `856bc0cc2e9308f743ff94358df315c51f85292bc28dd630d144b8c54f4c3f26`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/LowerOrderFixedRadius.receipt.json`
- `IsingBulk.First.LowerOrderTransfer`: 2 kernel-safe declarations; source SHA-256 `942799dc5ba3c1d1f50c7a2ac15ac7d0d82262399e64c522e7dc267adfd66dac`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/LowerOrderTransfer.receipt.json`
- `IsingBulk.First.MeanAnalyticIntegral`: 4 kernel-safe declarations; source SHA-256 `7e6d564a0e4a7d01bf6014d2fb727c35ab8a679a95022c717c697a823bfb3bb4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanAnalyticIntegral.receipt.json`
- `IsingBulk.First.MeanAnalyticTube`: 2 kernel-safe declarations; source SHA-256 `c6126c7f4091b6e8ba1f8c28ce7abdbeebcc20df10b8a6345020f7447fcfb284`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanAnalyticTube.receipt.json`
- `IsingBulk.First.MeanAngularIdentity`: 5 kernel-safe declarations; source SHA-256 `064c4df06ab771723ec36004af71c357b7cc15dbc0304177a4b5bebf29c6c02e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanAngularIdentity.receipt.json`
- `IsingBulk.First.MeanAttenuation`: 6 kernel-safe declarations; source SHA-256 `2e206d37fe6bfa6d7c79bd8d3ccfce6b530a22d7e3f1196143aa50fd721bfd8d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanAttenuation.receipt.json`
- `IsingBulk.First.MeanCompatibleLemma`: 1 kernel-safe declarations; source SHA-256 `5e581026fc83a8eefe57950ca66261765ba4952f8687a0cbccc6327fb61983ac`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanCompatibleLemma.receipt.json`
- `IsingBulk.First.MeanConstrainedConcavity`: 2 kernel-safe declarations; source SHA-256 `00dbd54f879d0903f3c746409fa723ce63477f4c15ffd1c0825c530b9bc95c78`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanConstrainedConcavity.receipt.json`
- `IsingBulk.First.MeanCoordinateMeasure`: 6 kernel-safe declarations; source SHA-256 `909ca20fc74e05e89217e92e4c5c6c1ab1f80107808b135c94b49a30d7632267`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanCoordinateMeasure.receipt.json`
- `IsingBulk.First.MeanCoordinates`: 23 kernel-safe declarations; source SHA-256 `3152a2d75ecd584cdd338a1cc3620483f435e9374d049d6f116564fc32beb1cd`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanCoordinates.receipt.json`
- `IsingBulk.First.MeanDeformedDomain`: 6 kernel-safe declarations; source SHA-256 `af51abc34c8102022ee73b9747c43fd23e15d69e664f95e393d8dd191d53371d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanDeformedDomain.receipt.json`
- `IsingBulk.First.MeanDerivativeTube`: 9 kernel-safe declarations; source SHA-256 `6480bea5612dbab8d4d7a2e60d039bf159a408d53b78afa0c846cc294848968b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanDerivativeTube.receipt.json`
- `IsingBulk.First.MeanEdgeBounds`: 6 kernel-safe declarations; source SHA-256 `9be48f5afa31f8a6b69b60e47324d59a128da6ee3d8d524901dfceb70dfc9c18`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanEdgeBounds.receipt.json`
- `IsingBulk.First.MeanErrorShapeContinuity`: 5 kernel-safe declarations; source SHA-256 `a21752a0f358661026b19ccf4f42c6b5ca1457458f7e90f7e6087417efcb0262`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanErrorShapeContinuity.receipt.json`
- `IsingBulk.First.MeanErrorShapeIntegral`: 7 kernel-safe declarations; source SHA-256 `ae68ca4abdff0715d7caf88aea47c6ceec204a96b52fce4ed532033887cbf927`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanErrorShapeIntegral.receipt.json`
- `IsingBulk.First.MeanErrorShapeLimit`: 7 kernel-safe declarations; source SHA-256 `6d9073f0ce4c44f299e198c24f48c773f7066046fe5b0586b6aa72ab2239f7a3`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanErrorShapeLimit.receipt.json`
- `IsingBulk.First.MeanErrorShapeRegularity`: 3 kernel-safe declarations; source SHA-256 `078ce665caf136571b05a53d50c643ce56802c8a9d04b70c5bdd14402c32cab4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanErrorShapeRegularity.receipt.json`
- `IsingBulk.First.MeanFullIntegral`: 1 kernel-safe declarations; source SHA-256 `d624ef64f18976dcd4b83ac55b4a4ee390775ad92d37142448eed0bbb5fd7e04`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanFullIntegral.receipt.json`
- `IsingBulk.First.MeanImaginaryMargin`: 14 kernel-safe declarations; source SHA-256 `ab7fa61f1b7d5f44d0ce06d1dba25905b530c5fc51f6e7f5051dd500c6c2c8f1`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanImaginaryMargin.receipt.json`
- `IsingBulk.First.MeanJacobian`: 17 kernel-safe declarations; source SHA-256 `b310ba742ec5f8a6475377963465a28a72b635fd8b91647302b4d12dbceab6b2`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanJacobian.receipt.json`
- `IsingBulk.First.MeanJointAnalytic`: 13 kernel-safe declarations; source SHA-256 `a58d601f703d9ffcba935830f36ab3b3568bd37b9681e67c5c04980a4850e846`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanJointAnalytic.receipt.json`
- `IsingBulk.First.MeanLocalDensity`: 8 kernel-safe declarations; source SHA-256 `71daee7694c7a0863bb249af0929f87334d355c9f5d9c0cc243f363bd0e1c369`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanLocalDensity.receipt.json`
- `IsingBulk.First.MeanLocalDomain`: 5 kernel-safe declarations; source SHA-256 `272ae6ef9de356ed9d1ecaf7f2d4bdbfe207f014fe7221e1f293c7beb71dab5f`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanLocalDomain.receipt.json`
- `IsingBulk.First.MeanLocalRegularity`: 5 kernel-safe declarations; source SHA-256 `d8ef3f4c4e45ceb26313c2a4e9999fe98dcff928b21255cf9bc441922d5a1e69`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanLocalRegularity.receipt.json`
- `IsingBulk.First.MeanMotion`: 6 kernel-safe declarations; source SHA-256 `a3f0747d3e09d0f9f444a6e9ca8651ec3a969c321580b629cf96c288736615ae`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanMotion.receipt.json`
- `IsingBulk.First.MeanNonlinearBound`: 3 kernel-safe declarations; source SHA-256 `9cf14549ea6b2df47e8afcbdb15dfd6d7f6ad74e524d688a9b014575d07b1307`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanNonlinearBound.receipt.json`
- `IsingBulk.First.MeanParameterDisk`: 1 kernel-safe declarations; source SHA-256 `d2f487ac091accbe4ffd65e21461e52944240df4d3f9c41b21082e2274f726ba`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanParameterDisk.receipt.json`
- `IsingBulk.First.MeanParameterDomain`: 7 kernel-safe declarations; source SHA-256 `22e3c9c9c0ad5172695613fe7af613d9f05d499f46d15bbdc6d705231721ed9d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanParameterDomain.receipt.json`
- `IsingBulk.First.MeanParameterIntegral`: 2 kernel-safe declarations; source SHA-256 `4a530b80f57854664dd4e59d1b58ae3798cab5b80fba17d24858644dfee62406`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanParameterIntegral.receipt.json`
- `IsingBulk.First.MeanParameterRectangle`: 3 kernel-safe declarations; source SHA-256 `a35f9998e36978f6ee8605386a759240fe1193e847cbc35b05db9c55fa48c952`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanParameterRectangle.receipt.json`
- `IsingBulk.First.MeanPhase`: 43 kernel-safe declarations; source SHA-256 `8392c679066fd08c224bd987eac4fbb2baf969cd5150a91d1a95a8424cd8b179`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanPhase.receipt.json`
- `IsingBulk.First.MeanPhaseSecond`: 13 kernel-safe declarations; source SHA-256 `0b2f8f82905f7a444e3009ecabc5e19e339aa21e8de36c56bb2e3ff189e5afd0`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanPhaseSecond.receipt.json`
- `IsingBulk.First.MeanPhysicalDecomposition`: 5 kernel-safe declarations; source SHA-256 `22cad71b3082d63f1383a5a0d7e3222e05a1aaa791af57e7ae979fdd3261ab69`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanPhysicalDecomposition.receipt.json`
- `IsingBulk.First.MeanPhysicalLemma`: 2 kernel-safe declarations; source SHA-256 `94d0f16f6c1231de8fa4c9e3d28c23a7ae5b8284c5be0a5b9964176f6b3ace5c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanPhysicalLemma.receipt.json`
- `IsingBulk.First.MeanPole`: 18 kernel-safe declarations; source SHA-256 `d8f5ff0c368737f78b74cafc581d6793ff81658c16f35db381268d108f51bb66`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanPole.receipt.json`
- `IsingBulk.First.MeanPoleExclusion`: 9 kernel-safe declarations; source SHA-256 `ad26591505aa5cf5bbfb181e7e42ea7294142154ef62f073e6bb7b5ac246a866`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanPoleExclusion.receipt.json`
- `IsingBulk.First.MeanPrescribedLemma`: 1 kernel-safe declarations; source SHA-256 `70d68f6573fe499d0ee46ad56243375dc827bcf5b25732d9568369bd98639b7c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanPrescribedLemma.receipt.json`
- `IsingBulk.First.MeanRadialPhase`: 17 kernel-safe declarations; source SHA-256 `370c64e4a50ad8a4aae10a96978405304a555d683d42f9d6095b9b8fc85ee46a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRadialPhase.receipt.json`
- `IsingBulk.First.MeanRadialTaylor`: 3 kernel-safe declarations; source SHA-256 `72b5013167bcac982510e6aa8b2bcbf613e958bd17e3a9a76bed17cc335c1a7d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRadialTaylor.receipt.json`
- `IsingBulk.First.MeanRealDomain`: 5 kernel-safe declarations; source SHA-256 `2c23a505eb347e953cbb1de38e04c20939c2585c2c2bacfd539ceab368750618`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRealDomain.receipt.json`
- `IsingBulk.First.MeanRealPhase`: 6 kernel-safe declarations; source SHA-256 `ceefb601543147ccc8c0d29036f55667dc7d9eecd37730a5549d0ae6d900a4a2`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRealPhase.receipt.json`
- `IsingBulk.First.MeanRectangle`: 9 kernel-safe declarations; source SHA-256 `4fab5f281b36de64347797529aca5394585f631e98efc43b4b21900007b6e6a0`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRectangle.receipt.json`
- `IsingBulk.First.MeanRectanglePhysical`: 4 kernel-safe declarations; source SHA-256 `69ca0504b1b8402d7319c24614cf0ab23b0de9daa4e038f1db03e61e5d170f75`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRectanglePhysical.receipt.json`
- `IsingBulk.First.MeanRectangleResidue`: 14 kernel-safe declarations; source SHA-256 `4cf790cc3a8bba83ce0416bf166e37e5546e55e6d7f6899b0beb69dbe636a774`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRectangleResidue.receipt.json`
- `IsingBulk.First.MeanRegularDerivatives`: 24 kernel-safe declarations; source SHA-256 `65025360872a01266ba672b51cb9fc95f19d282a8d57bd30fbd73080bc1243c0`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRegularDerivatives.receipt.json`
- `IsingBulk.First.MeanRegularError`: 3 kernel-safe declarations; source SHA-256 `a9a2b13ebf35d6f60df62bd914dbb7ef729358e5d10f362a3c57f73ef5815bea`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRegularError.receipt.json`
- `IsingBulk.First.MeanRegularPhase`: 12 kernel-safe declarations; source SHA-256 `1d74954dea862378b11f4a76693a6a4f49435bf8383aebebb4118fb8be827e5f`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRegularPhase.receipt.json`
- `IsingBulk.First.MeanResidueDomain`: 9 kernel-safe declarations; source SHA-256 `9eba5d80ec7a53aeee65f21103e262c39f7e08640567ba6ed9eb46bf4467041d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanResidueDomain.receipt.json`
- `IsingBulk.First.MeanRootBridge`: 3 kernel-safe declarations; source SHA-256 `fe1424d19b85b914dff81986619bf5cedeae715b1341956f18475522e6dd390a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanRootBridge.receipt.json`
- `IsingBulk.First.MeanSelectedData`: 10 kernel-safe declarations; source SHA-256 `f16ae96d2b7a3410440ec46a5ee889b5334378d11ec1e245aa919844c261b7fb`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSelectedData.receipt.json`
- `IsingBulk.First.MeanSeparatedDerivativeBounds`: 12 kernel-safe declarations; source SHA-256 `9187ae4de00e131747f6c6084fb91d75878954cd25fa44db39b6454ac7b6177d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSeparatedDerivativeBounds.receipt.json`
- `IsingBulk.First.MeanSeparatedIntegral`: 5 kernel-safe declarations; source SHA-256 `ab9d579314344c200ad5c7f024e53fe31a1d3bd70ef3975b05135c2b6769581d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSeparatedIntegral.receipt.json`
- `IsingBulk.First.MeanShapeContinuity`: 2 kernel-safe declarations; source SHA-256 `7977ac0764145176887d1096427e6d960d8d603af179c53f0c27530e9e5e7c82`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanShapeContinuity.receipt.json`
- `IsingBulk.First.MeanShapeDensity`: 12 kernel-safe declarations; source SHA-256 `38e7b19f49163857a2045f6fa821eed493a78e57e0d6b781d0250e47e3ace6a6`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanShapeDensity.receipt.json`
- `IsingBulk.First.MeanShapeGap`: 10 kernel-safe declarations; source SHA-256 `b40c6a1a7aa42e7ce57a9ebd260ee1ec6e24ca30f707381950b0db8311e74556`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanShapeGap.receipt.json`
- `IsingBulk.First.MeanShapeIntegral`: 2 kernel-safe declarations; source SHA-256 `17823af35e714b60afaf61bab11a9b5a2e8934ce092e2ab4870216ad02f00e50`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanShapeIntegral.receipt.json`
- `IsingBulk.First.MeanShapePhaseSum`: 2 kernel-safe declarations; source SHA-256 `c006a46133c2fa14b0ee3b22ac8204906096a0e82b46e8da6167c15b621df7ba`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanShapePhaseSum.receipt.json`
- `IsingBulk.First.MeanSideBounds`: 1 kernel-safe declarations; source SHA-256 `d7a6099f21a6f3a3eb457594b21804b16e6f8bea09bb59df84713341e3e4a494`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSideBounds.receipt.json`
- `IsingBulk.First.MeanSideCurves`: 15 kernel-safe declarations; source SHA-256 `1b227b8dd4e16a887f675c6b3a729ac368d80227ce397a0cbd8f402eebe952bd`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSideCurves.receipt.json`
- `IsingBulk.First.MeanSideIsolation`: 16 kernel-safe declarations; source SHA-256 `92a50ce83bb1aba27c6a5b6d55cbcc1ac5d11d719a6d351e292acf1c196423ae`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSideIsolation.receipt.json`
- `IsingBulk.First.MeanSmallAnnulus`: 2 kernel-safe declarations; source SHA-256 `e9965e053c129af17e56b51cbd072ff202c5ce14a030eb0e8813c605425dc01a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSmallAnnulus.receipt.json`
- `IsingBulk.First.MeanSmallRectangle`: 1 kernel-safe declarations; source SHA-256 `65fa94550a54a497a19f1ed3836a07b385056d06d8966d24c994a8cb236e4bd5`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSmallRectangle.receipt.json`
- `IsingBulk.First.MeanSmoothDecomposition`: 5 kernel-safe declarations; source SHA-256 `2ec7f77f2b7a8f578d1f3bedbe68273bf3b01f472b99bfa8d578a0bfaef962bc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSmoothDecomposition.receipt.json`
- `IsingBulk.First.MeanSourceIntegral`: 5 kernel-safe declarations; source SHA-256 `dfe2f097f49b15447b3efa2eeedd91c92f457f021919caf262e59e2f64220f9a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanSourceIntegral.receipt.json`
- `IsingBulk.First.MeanUniformConcavity`: 8 kernel-safe declarations; source SHA-256 `e8cc909c7dc7567ef2b9cd5ddbcf50b33c56e71b27727768bd10f901e2393ea7`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanUniformConcavity.receipt.json`
- `IsingBulk.First.MeanUniformRectangle`: 1 kernel-safe declarations; source SHA-256 `db8ea1aaa140b27a66f1a841dae34302273e583e346e396ad4eca3b932fb8ca0`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanUniformRectangle.receipt.json`
- `IsingBulk.First.MeanYResidue`: 17 kernel-safe declarations; source SHA-256 `356888285c6462f256e59fef474eb41e931064e0845dfc08df9692909a37ee51`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MeanYResidue.receipt.json`
- `IsingBulk.First.MixedDoubleContour`: 5 kernel-safe declarations; source SHA-256 `87cadf9cb437d3db6b843a649097d7fb2ff608ca7d415f8f7d1cb614b0bc83dc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MixedDoubleContour.receipt.json`
- `IsingBulk.First.MixedOnsiteContour`: 5 kernel-safe declarations; source SHA-256 `c8ecf6de8365dbbd708f9ee163d623d797aa6f096fb56264e5e7dd453a361811`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MixedOnsiteContour.receipt.json`
- `IsingBulk.First.MixedRadiusDamping`: 5 kernel-safe declarations; source SHA-256 `b7ea0ce4c2782e11161c647ea2190f866f60982fbd11e3632a61edde792a875b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/MixedRadiusDamping.receipt.json`
- `IsingBulk.First.NearInfinityBulkSeries`: 12 kernel-safe declarations; source SHA-256 `624749341a263beb0c8bcf4bb63c6a85d3a8ee47bba30bc4036350d67bf6f0cc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/NearInfinityBulkSeries.receipt.json`
- `IsingBulk.First.NormalizationDerivatives`: 3 kernel-safe declarations; source SHA-256 `c33ea6a8aeab97d15adc42cd2d818df34f03ed833fa0c1ad46d2d8ebe7c4ee9e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/NormalizationDerivatives.receipt.json`
- `IsingBulk.First.NormalizationIntegral`: 3 kernel-safe declarations; source SHA-256 `10778fee2cf53208ad9c11da597efd639ecd9ea6f506764ee644349cb527a564`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/NormalizationIntegral.receipt.json`
- `IsingBulk.First.NormalizationRegularity`: 2 kernel-safe declarations; source SHA-256 `ed9712390da3dc89c29ec87a253dcc0b9e018d4cf722bf8f62c7efae86a8bf5b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/NormalizationRegularity.receipt.json`
- `IsingBulk.First.NormalizedContour`: 16 kernel-safe declarations; source SHA-256 `4b6c70284395649631c491ebfe3fe6773f2d5ce40987132f56116d28dc61d606`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/NormalizedContour.receipt.json`
- `IsingBulk.First.OnsiteActiveChart`: 1 kernel-safe declarations; source SHA-256 `efb34049db4a96dfdccebd8353ecb3ed881eff075c2cfe33ab17ec979f8b1710`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteActiveChart.receipt.json`
- `IsingBulk.First.OnsiteAmplitudeSupport`: 2 kernel-safe declarations; source SHA-256 `d76696f5b0a115528d51e18358d0d561dcb82d179e25667691736e0dac20885e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteAmplitudeSupport.receipt.json`
- `IsingBulk.First.OnsiteAuxiliaryDomination`: 3 kernel-safe declarations; source SHA-256 `3e97c7e7c60b63e0a68df441284de256b2565c4a2a5364e28351cfe29e874c83`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteAuxiliaryDomination.receipt.json`
- `IsingBulk.First.OnsiteAuxiliaryInterchange`: 5 kernel-safe declarations; source SHA-256 `9649671a3bdae2a9d59070cb0c754aa51431a46b92f906dc6332899c25442351`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteAuxiliaryInterchange.receipt.json`
- `IsingBulk.First.OnsiteAuxiliaryJets`: 6 kernel-safe declarations; source SHA-256 `91697818c130b35605428d86af8ec4d4346360936bada54c301b14c7c8733b5d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteAuxiliaryJets.receipt.json`
- `IsingBulk.First.OnsiteAuxiliaryRegularity`: 5 kernel-safe declarations; source SHA-256 `9a667119f317051023b2111318a784c1e81151531e0bd1cddc7e83ecee79807c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteAuxiliaryRegularity.receipt.json`
- `IsingBulk.First.OnsiteAuxiliaryTailBound`: 3 kernel-safe declarations; source SHA-256 `7ac6688cf9d0e6892f08667337e5ac9bee589bbf1e1867e456ab739ea86c8427`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteAuxiliaryTailBound.receipt.json`
- `IsingBulk.First.OnsiteFactorization`: 24 kernel-safe declarations; source SHA-256 `fd56429e68661d9f9e20a4ed6f19142841845aad40012374ca2fe7217b05e528`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteFactorization.receipt.json`
- `IsingBulk.First.OnsiteFiniteRefinement`: 2 kernel-safe declarations; source SHA-256 `8f2281616d2052bfb83d6198708101e1a64d4b4a856183a0c746c94e07872493`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteFiniteRefinement.receipt.json`
- `IsingBulk.First.OnsiteFiniteSum`: 4 kernel-safe declarations; source SHA-256 `878dcafcebb1e0c1ddd3524356560828c479b4ac1a867dfcc0b9e7cfce94111d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteFiniteSum.receipt.json`
- `IsingBulk.First.OnsiteGlobalBound`: 1 kernel-safe declarations; source SHA-256 `5239657b18e044b2a7bc3b2c2faeb72cced86b6539a9d77ba4e88899bdffd069`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteGlobalBound.receipt.json`
- `IsingBulk.First.OnsiteInactiveNeighborhood`: 3 kernel-safe declarations; source SHA-256 `47e9f7da69b5e5f2d5c0142859809721dfcfb1b2072e8d6a306445a51ab978b1`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteInactiveNeighborhood.receipt.json`
- `IsingBulk.First.OnsiteLocalBound`: 2 kernel-safe declarations; source SHA-256 `a8deb0a5e1f71c6168b596e03ca168aac2af7bef41ba1ba5c2459a8b9cb73bf9`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteLocalBound.receipt.json`
- `IsingBulk.First.OnsiteLocalFormFactor`: 1 kernel-safe declarations; source SHA-256 `1941de76a4fc17da93fbd27bc79d0b84a5174f3d4fd83fecc58695ea33d6175b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteLocalFormFactor.receipt.json`
- `IsingBulk.First.OnsiteLocalizationAlgebra`: 1 kernel-safe declarations; source SHA-256 `c330123f8e1a8ee3fa4b62d86b2e0128cd637539710c9a860a6237df03e53eb9`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteLocalizationAlgebra.receipt.json`
- `IsingBulk.First.OnsiteNormalizedJets`: 4 kernel-safe declarations; source SHA-256 `e39aa97bf1ec0c573ada1272eb6a1aed42c4380318ec4c679d336f4b4a2cb7f4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteNormalizedJets.receipt.json`
- `IsingBulk.First.OnsitePeriodicLift`: 5 kernel-safe declarations; source SHA-256 `e2a380070d871ef1b857a3c2a67bca24329a8f5e20782f87a618f9b85e585ebe`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsitePeriodicLift.receipt.json`
- `IsingBulk.First.OnsiteRadialChartDecay`: 1 kernel-safe declarations; source SHA-256 `0ba2b7ac092f532a5bee5bed9f751ebccdcf653de394824a654e6ad71c3e2a3f`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteRadialChartDecay.receipt.json`
- `IsingBulk.First.OnsiteRadialRegularChart`: 1 kernel-safe declarations; source SHA-256 `5baa9bc1c3d01540f30ee552c49c3bb9e55ec54b6b2b480bb1026d85f88eb355`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteRadialRegularChart.receipt.json`
- `IsingBulk.First.OnsiteRadiusIndependence`: 5 kernel-safe declarations; source SHA-256 `2b7dd395af3ba634ff6200b356bcf7a20b6911d50ee43a242170d3106a991a72`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteRadiusIndependence.receipt.json`
- `IsingBulk.First.OnsiteRegularity`: 5 kernel-safe declarations; source SHA-256 `ba8938aa22dbf809617a9deb89418ca84ace636fb13f5459cbdb3c12afdd14c9`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteRegularity.receipt.json`
- `IsingBulk.First.OnsiteSeparation`: 1 kernel-safe declarations; source SHA-256 `7e658ffc933752955db5cbef1f3e264a0041505fe88d07f61d8e4f7c791fa949`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteSeparation.receipt.json`
- `IsingBulk.First.OnsiteSmallAuxiliary`: 3 kernel-safe declarations; source SHA-256 `cc7f89986bf6b60968d19ba5ee00d90d77c58de1f5d00b89e47288579aecd6db`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteSmallAuxiliary.receipt.json`
- `IsingBulk.First.OnsiteUniform`: 3 kernel-safe declarations; source SHA-256 `2401f8c2e0f85fa6a8f1c65434a878b8b32f811d52cbb74479f16a43bcbb3d89`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/OnsiteUniform.receipt.json`
- `IsingBulk.First.PeriodicAngularChart`: 19 kernel-safe declarations; source SHA-256 `34134e6d81ee08784aa6a64e3d45c64cca4b947cc48ed4362441caac7d54516c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PeriodicAngularChart.receipt.json`
- `IsingBulk.First.PeriodicBoxIntegral`: 6 kernel-safe declarations; source SHA-256 `c39743fd57f49741b1db139106bc28e176e17943364d967545313b75dc3de61b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PeriodicBoxIntegral.receipt.json`
- `IsingBulk.First.PeriodicBump`: 11 kernel-safe declarations; source SHA-256 `5d55ffa796f97dab5f72677e7564659e4ab8427570bad50b640eb1e43f19b68c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PeriodicBump.receipt.json`
- `IsingBulk.First.PeriodicLiftIntegral`: 2 kernel-safe declarations; source SHA-256 `37cdd7eec5c5d419397b96d982c90a0e2ae22ec91b6df6ea1f29c53e7725045b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PeriodicLiftIntegral.receipt.json`
- `IsingBulk.First.PeriodicWrapInvariant`: 5 kernel-safe declarations; source SHA-256 `50acd3cd47a4e7cef2c5126b55b5316ce4fa3cc480110e847221c8a69b6b51dc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PeriodicWrapInvariant.receipt.json`
- `IsingBulk.First.PeriodicYCutoff`: 12 kernel-safe declarations; source SHA-256 `724369af769a1b75ecfbc68df0a510edeeb4e014465db080c448b43d75475e42`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PeriodicYCutoff.receipt.json`
- `IsingBulk.First.PeriodicYPartition`: 7 kernel-safe declarations; source SHA-256 `0dfb4d8b1bd556cc865765d339c2bc58020fff97aeea3af17b5feb11938287c5`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PeriodicYPartition.receipt.json`
- `IsingBulk.First.PeriodicYSupport`: 7 kernel-safe declarations; source SHA-256 `3455876c00a8f68c88875ad6448a80b5410bd3ba27ba12a8c9ce55072caa95a8`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PeriodicYSupport.receipt.json`
- `IsingBulk.First.PhysicalMeanResidue`: 1 kernel-safe declarations; source SHA-256 `c15f650082b359b843f83d8d4e5d00084823fe66121705e4fe650e4fa20273c2`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PhysicalMeanResidue.receipt.json`
- `IsingBulk.First.PoleDifferentiation`: 31 kernel-safe declarations; source SHA-256 `7fc11ca84e24460c631d389da929efa7c95918b79b49d06c1a2d1e50665cd7e2`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PoleDifferentiation.receipt.json`
- `IsingBulk.First.PublishedFixedOrder`: 4 kernel-safe declarations; source SHA-256 `a3a27b64bd5287a27f9731522be88416802826fe20f07db18b524b9bb8c66493`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/PublishedFixedOrder.receipt.json`
- `IsingBulk.First.QuarterContourBound`: 1 kernel-safe declarations; source SHA-256 `ada768b7f433dd3ee0f61aa1281530c1dd818780a1488198d39802ec3f4c8a4e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/QuarterContourBound.receipt.json`
- `IsingBulk.First.RadialAdmissibility`: 9 kernel-safe declarations; source SHA-256 `0c4cffa0bfb8a5a1685e923ffa209922c8cbfcaf0f4a5571c65154838882ce28`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/RadialAdmissibility.receipt.json`
- `IsingBulk.First.RadialDiskAdmissibility`: 2 kernel-safe declarations; source SHA-256 `dc06ee5dbbac9001bbacc965e3c60accbf419853a265a20b01184c60e1b97627`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/RadialDiskAdmissibility.receipt.json`
- `IsingBulk.First.RadialFirstRepresentation`: 1 kernel-safe declarations; source SHA-256 `6ebb1a92840eb89007218de57391cc1802986c79287a0ac753063365defcc4af`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/RadialFirstRepresentation.receipt.json`
- `IsingBulk.First.RadiusIndependence`: 11 kernel-safe declarations; source SHA-256 `ff22c7401ef21050c7a18121cccdd88fc136f1cfa76d165050e88479d66f4546`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/RadiusIndependence.receipt.json`
- `IsingBulk.First.RealFredholmIdentification`: 5 kernel-safe declarations; source SHA-256 `65445c241ad06446e59d721157d0f32fd90eaf6efd4eb37f788b9aeb60fb8ce7`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/RealFredholmIdentification.receipt.json`
- `IsingBulk.First.ReducedLocalization`: 4 kernel-safe declarations; source SHA-256 `0ab8a559380a3e14587b3c8f0cf8d9541c48b40e222e53a2b0ee6c9af6c288d9`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ReducedLocalization.receipt.json`
- `IsingBulk.First.ResidueAdmissibility`: 14 kernel-safe declarations; source SHA-256 `f87cdcdb0634cc5158db7c3cba2930307c2e743c2241a41cc2d9eebf4bc8e72e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ResidueAdmissibility.receipt.json`
- `IsingBulk.First.ResidueAlgebra`: 16 kernel-safe declarations; source SHA-256 `fc0233ed82e7d082dc2fe40d564c519078246ec6253a579d20332e7b8f70244e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ResidueAlgebra.receipt.json`
- `IsingBulk.First.ResidueBounds`: 6 kernel-safe declarations; source SHA-256 `248e3beab2b037b33bff41e4ea0480dac51e84d660628d60c7fe7988bf12f126`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ResidueBounds.receipt.json`
- `IsingBulk.First.ResidueBranch`: 6 kernel-safe declarations; source SHA-256 `fcdf9ae9bca18c92a06cca704e3cc3151119783e4d30f787a85cf8b3d9f29fcc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ResidueBranch.receipt.json`
- `IsingBulk.First.ResidueCancellation`: 14 kernel-safe declarations; source SHA-256 `d2ef7d0f6dbf9ea9a2c1816ad8d3de4e23fe7916e3ff74fde0021c069e287a73`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ResidueCancellation.receipt.json`
- `IsingBulk.First.ResidueEndpoint`: 2 kernel-safe declarations; source SHA-256 `92384ae591edbf617b3fe97c2f1bcb997550d029f3e4a03467a632c39c4464d2`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ResidueEndpoint.receipt.json`
- `IsingBulk.First.ResidueIntegral`: 6 kernel-safe declarations; source SHA-256 `c8529d4dbf623c4f37b0794b891a064ee45eec32f3f95d172a1ed23b03907981`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ResidueIntegral.receipt.json`
- `IsingBulk.First.ResidueRegularity`: 8 kernel-safe declarations; source SHA-256 `ed95d4c786a7fbb5c773ec13d40e7971dce95c7d36d4d6879a515506489a3660`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ResidueRegularity.receipt.json`
- `IsingBulk.First.ResolventParameterIntegral`: 7 kernel-safe declarations; source SHA-256 `47197df737f3919035ef2c7d10c5cb793cb63ff98801a3a247c27145eac07cef`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ResolventParameterIntegral.receipt.json`
- `IsingBulk.First.ScalarBeta`: 26 kernel-safe declarations; source SHA-256 `893e8860d4f9d1c474fb0c6e1dcf8870170c3049c81d35e5ad11d85fa6860340`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ScalarBeta.receipt.json`
- `IsingBulk.First.SelectedComplementBound`: 5 kernel-safe declarations; source SHA-256 `20ebec93dea17461e4ec2d79e7e899f2ada3c0c57278b5f8edd1b960dfa7537d`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SelectedComplementBound.receipt.json`
- `IsingBulk.First.SelectedLocalPair`: 3 kernel-safe declarations; source SHA-256 `357daf6d0a82bec49f15391e1f53d889cc832ebfa05b51a4731c67aae55b327a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SelectedLocalPair.receipt.json`
- `IsingBulk.First.SelectedPhysicalMean`: 2 kernel-safe declarations; source SHA-256 `b5ae2e4b24cdfb81c3efd1fe8532f4e43015e57458f892c10597fd69148e6851`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SelectedPhysicalMean.receipt.json`
- `IsingBulk.First.SelectedYCutoffs`: 6 kernel-safe declarations; source SHA-256 `ac824a5f2193834e4c1b2f6b1b9ee0eb10c9413222ab8ab690c3e02695050eb1`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SelectedYCutoffs.receipt.json`
- `IsingBulk.First.ShapeArithmetic`: 5 kernel-safe declarations; source SHA-256 `e6828474b902efb72c7e2d129041ab6c8f762f180f9484f7303213dfde332afb`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeArithmetic.receipt.json`
- `IsingBulk.First.ShapeCutoffBounds`: 5 kernel-safe declarations; source SHA-256 `b080a14a58e4e366afe9510d23eff1339925660bc9ea3a34d7cbc66a95c86e3b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeCutoffBounds.receipt.json`
- `IsingBulk.First.ShapeCutoffLift`: 12 kernel-safe declarations; source SHA-256 `a5a6d7692c034320c9e8d98a56cc2562058686628f1128624af0a35261014e9e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeCutoffLift.receipt.json`
- `IsingBulk.First.ShapeCutoffLimit`: 2 kernel-safe declarations; source SHA-256 `faf70c874491ce5c1698dacb4a332f69400a50052fc9b3222e41998f8f4a4671`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeCutoffLimit.receipt.json`
- `IsingBulk.First.ShapeDominatedLimit`: 5 kernel-safe declarations; source SHA-256 `6059f47044330d5082e55c8f361d49356501504e63e628685a981df8074436ca`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeDominatedLimit.receipt.json`
- `IsingBulk.First.ShapeGeometry`: 25 kernel-safe declarations; source SHA-256 `cc81c29a31c16bc85bac9e0accf81b53bc7fa665075899c596a72b861366cb24`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeGeometry.receipt.json`
- `IsingBulk.First.ShapeIntegrability`: 4 kernel-safe declarations; source SHA-256 `28b009661efecb0f036f9c4fcf735dd195cbb36b5fdc7e1f0476c155dcacb188`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeIntegrability.receipt.json`
- `IsingBulk.First.ShapeLimitTransfer`: 11 kernel-safe declarations; source SHA-256 `d1e6ca7421bdd24ec492e0c1c9f991ca8d2756d30230a4ef87f7b4134a59d054`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeLimitTransfer.receipt.json`
- `IsingBulk.First.ShapeLowerOrderBounds`: 4 kernel-safe declarations; source SHA-256 `b23c4f6f15415896c4e2194ebb7938ff814dbf894550751256c2480b2eedd90e`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeLowerOrderBounds.receipt.json`
- `IsingBulk.First.ShapeLowerOrders`: 3 kernel-safe declarations; source SHA-256 `1384e080087ab0914a7f8ba068faa3ef983bf8804ce3ced57c120e2e11c51bcb`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeLowerOrders.receipt.json`
- `IsingBulk.First.ShapeMeasure`: 4 kernel-safe declarations; source SHA-256 `b1707f719698a20a3ca5ed59c0b14eca9c295f3949157d7147307992300cf0fd`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeMeasure.receipt.json`
- `IsingBulk.First.ShapePeriodTheorem`: 7 kernel-safe declarations; source SHA-256 `8375fb1dc825f646420c861e1e4b386b9b88e224416944ddea6f1d41baa26813`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapePeriodTheorem.receipt.json`
- `IsingBulk.First.ShapePolar`: 14 kernel-safe declarations; source SHA-256 `31c1f5ac5f20c5e6c4014fa492ee0a853cfcb6ac98ee5a90fc57df425db82093`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapePolar.receipt.json`
- `IsingBulk.First.ShapeRadialAnalytic`: 7 kernel-safe declarations; source SHA-256 `60a1e5be1aefbd17e498596e317005abea19ac2b60277f539636fce5c1772d68`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeRadialAnalytic.receipt.json`
- `IsingBulk.First.ShapeRadialBounds`: 14 kernel-safe declarations; source SHA-256 `73c6b20f88e35d37b57245fc899df429a5323a6ee8d24963455e62141e3545a3`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeRadialBounds.receipt.json`
- `IsingBulk.First.ShapeRadialContinuation`: 2 kernel-safe declarations; source SHA-256 `d47da701cac87412c76df87735651ecb90724192b364aeb070a24b11bb896b59`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeRadialContinuation.receipt.json`
- `IsingBulk.First.ShapeRadialLimit`: 2 kernel-safe declarations; source SHA-256 `6eff111277741e01820fce811c1ac90dc863fa099b81b8fa745c6d1dfcb7c103`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeRadialLimit.receipt.json`
- `IsingBulk.First.ShapeRadialValue`: 11 kernel-safe declarations; source SHA-256 `a574c0ee9c8c18e7703ecc552db4cf1531c595be22f5f100320e955dfa25d4c4`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeRadialValue.receipt.json`
- `IsingBulk.First.ShapeRescaling`: 8 kernel-safe declarations; source SHA-256 `c3ffdc910809f36eb4fcb9d46e596276ec0b628a85331aa7bf2456c53e8da7dc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeRescaling.receipt.json`
- `IsingBulk.First.ShapeScaledDenominator`: 24 kernel-safe declarations; source SHA-256 `3814330b96f249ea014a8faa7425a097473b4f845404c4b25798528599c752c0`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeScaledDenominator.receipt.json`
- `IsingBulk.First.ShapeScaledPhase`: 26 kernel-safe declarations; source SHA-256 `2e8cb87e15b4178ab71953c98cd2c991b2bf34e6bf6b7986f8e9fee4e527386c`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeScaledPhase.receipt.json`
- `IsingBulk.First.ShapeSource`: 8 kernel-safe declarations; source SHA-256 `75fcf0f15d8a81c73740b85e00ad34368acd5fe63e92e48cc8cd3209529e1d2a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeSource.receipt.json`
- `IsingBulk.First.ShapeSphere`: 9 kernel-safe declarations; source SHA-256 `b1edd7a445c7f7d5d9b4de7845c916c82ff4f88f066efdec8d6f92222dce0c16`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeSphere.receipt.json`
- `IsingBulk.First.ShapeVandermonde`: 27 kernel-safe declarations; source SHA-256 `2215baf472c4ddd9787edcbd42abcdc226f6a7bb9e4870e94bcb245b0d44f2a9`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/ShapeVandermonde.receipt.json`
- `IsingBulk.First.SmallRadiusDensityBounds`: 8 kernel-safe declarations; source SHA-256 `29a9752870885a471ae9a963d0815e74c75c6dc9c837e4e580d7ff63e4fa8fff`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SmallRadiusDensityBounds.receipt.json`
- `IsingBulk.First.SmoothCutoffConstruction`: 5 kernel-safe declarations; source SHA-256 `396380d181cc3263b657e817e82bc855fe8b703c05171310a07102136c38e0b7`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SmoothCutoffConstruction.receipt.json`
- `IsingBulk.First.SourceAngularPeriodicity`: 10 kernel-safe declarations; source SHA-256 `27d702dd80ea1251bb9e1f2e25285631585385f05a99af654defb4749b5be5cc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SourceAngularPeriodicity.receipt.json`
- `IsingBulk.First.SourceAsymptoticAttachment`: 4 kernel-safe declarations; source SHA-256 `e53461d6182d6c3a492f1d148ecd0edca123ef87bf97e79e88d17d614f989f01`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SourceAsymptoticAttachment.receipt.json`
- `IsingBulk.First.SourceAuxiliaryDomination`: 4 kernel-safe declarations; source SHA-256 `b1ac254fcba9d5ba364d279e9a68369d2bc7d0aa1ecfffb603747cd7cbc02ef5`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SourceAuxiliaryDomination.receipt.json`
- `IsingBulk.First.SourceAuxiliaryInterchange`: 3 kernel-safe declarations; source SHA-256 `3cad7edda4b4ff711b1b6fdbcf2fcdd5981f7dca5d4e9149d2c636e02ec7a403`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SourceAuxiliaryInterchange.receipt.json`
- `IsingBulk.First.SourceAuxiliaryJets`: 1 kernel-safe declarations; source SHA-256 `98c70c67d9ea60839d958ca00df5feb7282660780293024b2d18c45567d75283`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SourceAuxiliaryJets.receipt.json`
- `IsingBulk.First.SourceAuxiliaryRegularity`: 8 kernel-safe declarations; source SHA-256 `336450512e9db09dd1362472b94c386f49745e8b399ab3624ed800f194ec71c5`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SourceAuxiliaryRegularity.receipt.json`
- `IsingBulk.First.SourceLowerAttachment`: 1 kernel-safe declarations; source SHA-256 `e0936faa0207e5f1a3419dae5f0a3704d1945fe4fdc79a8739585fd3eb909c0b`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SourceLowerAttachment.receipt.json`
- `IsingBulk.First.SourceParameterBounds`: 10 kernel-safe declarations; source SHA-256 `aa161ff9cd18a35f73c609889bbaa839f1ac44d302e20226de0015998248a571`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SourceParameterBounds.receipt.json`
- `IsingBulk.First.SwappedChartCoefficient`: 39 kernel-safe declarations; source SHA-256 `6dbd8378c8d94e15a7cb64c046d1e5a0d1dbcc3acbbd00442a9f5471db16db75`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SwappedChartCoefficient.receipt.json`
- `IsingBulk.First.SwappedPeriodScaling`: 8 kernel-safe declarations; source SHA-256 `8262ca16f9b704a2a7b613ee93a366339a2423f95215b7edca1c8560623b06ec`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SwappedPeriodScaling.receipt.json`
- `IsingBulk.First.SymmetryAlgebra`: 18 kernel-safe declarations; source SHA-256 `873b8adfc0b67adc8ed318692b3d981a9a489ffe89f2964381cc816a0dc00ad1`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SymmetryAlgebra.receipt.json`
- `IsingBulk.First.SymmetryEndpoint`: 3 kernel-safe declarations; source SHA-256 `90cdcd8b6c6690bd7e1f882229914c52a3603414b095c5605819aac4e55907c7`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SymmetryEndpoint.receipt.json`
- `IsingBulk.First.SymmetryIntegral`: 7 kernel-safe declarations; source SHA-256 `8b66a1b56f60b36c78b6283f0d1ddb73f588d7811296704d07de71eb622f85cc`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/SymmetryIntegral.receipt.json`
- `IsingBulk.First.VariableContour`: 10 kernel-safe declarations; source SHA-256 `8b159dbfb7fa755f72a5018be8f0c7c534c7c3da773fd0bbab215c1f869950ab`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/VariableContour.receipt.json`
- `IsingBulk.First.WeightedResidue`: 24 kernel-safe declarations; source SHA-256 `15731b7ae2cb3be967baf3d36ac640e6c9b9bd0aa7015a51a56f2b484329601a`; `../../integration/canonical_modules_final_six_node_clean_20261003T1615Z/WeightedResidue.receipt.json`

Historical frozen machinery record follows; earlier statements about FIRST reflect that baseline.
<!-- FIRST_PILOT_CURRENT_END -->

<!-- AUTHORIZED_JETS_REPAIR_20261003_BEGIN -->
## Authorized Jets smooth-cutoff repair, 2026-10-03 13:15 UTC

The user-approved three-file working overlay passed exact input/hash verification, affected-path compilation and the complete original1666-declaration axiom audit. The final `lemma_jets` bundle now accepts `ContDiff ℝ ∞ w`; regular coefficient analyticity is unchanged. Immutable `_r1` and historical clean snapshots are preserved. This targeted acceptance does not assert a new whole-current-FIRST clean build. Receipt/report: `../../integration/jets_repair_20261003T1308Z/REPAIR_REPORT.md`. Future canonical-equivalent verification explicitly uses `--jets-repair-20261003`. FIRST statuses below are unchanged.
<!-- AUTHORIZED_JETS_REPAIR_20261003_END -->

# Coverage and final report — branch closure

**CLOSURE SUCCESS: `lem:branch` is CLOSED.** The constructed endpoint proves
the displayed original-branch and current-plateau clauses. Kernel compilation,
axiom trust and source correspondence were checked separately.

## 1. Frozen pins

- Lean `4.34.1`, executable commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Normative source snapshot `1b4b506c9cb19d5fdbf9f59d89c7a179739d337d`.
- `paper/manuscript.tex` Git blob `1c6c0f47e3f1e4d13e59b49c52c18414e9dd3939`.
- `source_snapshot/manuscript.tex`, toolchain, lakefile, manifest, existing
  freeze, all nine dependency heads and dependency sources are unchanged.
  No Physlib, `lake update`, or configuration/semantic change.

## 2. Final source status

Only `lem:branch` is newly CLOSED in this run. All prior closures are preserved.

| Source node | Status |
|---|---|
| `lem:residue` | NOT_STARTED |
| `lem:symmetry` | NOT_STARTED |
| `thm:prime` | CLOSED |
| `lem:resultant` | CLOSED |
| `lem:mean` | NOT_STARTED |
| `lem:period` | NOT_STARTED |
| `lem:complement` | NOT_STARTED |
| `thm:first` | NOT_STARTED |
| `prop:selector` | NOT_STARTED |
| `prop:ultrahigh` | NOT_STARTED |
| `prop:F` | NOT_STARTED |
| `lem:partition` | NOT_STARTED |
| `lem:contraction` | NOT_STARTED |
| `lem:originaldisk` | NOT_STARTED |
| `lem:branch` | CLOSED |
| `prop:micro` | NOT_STARTED |
| `prop:allB` | NOT_STARTED |
| `prop:mixed` | NOT_STARTED |
| `prop:compactR` | NOT_STARTED |
| `lem:protected` | NOT_STARTED |
| `prop:largeS` | NOT_STARTED |
| `prop:highKS` | NOT_STARTED |
| `thm:tail` | NOT_STARTED |
| `thm:conditional` | NOT_STARTED |
| `thm:nb` | NOT_STARTED |
| `lem:cyclotomic` | CLOSED |
| `lem:schur` | CLOSED |
| `lem:lie` | CLOSED |
| `lem:jets` | CLOSED |

## 3. Source-facing endpoint

`IsingBulk.Branch.lemma_branch (d : LocalBranchData)` proves
`Nonempty (BranchEstimates d)`. It constructs the conclusion bundle from
the actual analytic proofs. `BranchEndpoint` supplies its common-arc
projections, including `positive_slope`, `concavity`, `separated`,
`comparable`, `original_sheet`, `current_sheet`, `current_occupancy`,
`source_inner_radius`, and `length_restrict`. The inner constructed `OriginalQuotientData` has the
proved `separated_eventually` and `comparable_eventually` corollaries.
The bundle fields are conclusions, never unproved caller premises.

## 4. Exact new compiling declarations

Every new authored declaration, kind and source location appears in the
inventory below. AUTHORED_DECLARATIONS.tsv also includes all preserved
declarations; DECLARATIONS.tsv includes compiler-generated declarations
from the project-wide kernel-safe audit. Definitions and conclusion
structures do not themselves count as source proofs.

## 5. Original normal form

`original_normal_form` proves the explicit uniform inequality
norm(D_orig-(a_B*u-i*b_B*epsilon)) <= C*(u^2+epsilon*abs(u)+epsilon^2).
`LocalBranchData.a_pos/b_pos` prove the stated coefficient positivity.
The endpoint's `normal` field places it on the same final closed arc and
epsilon range as the remaining conclusions. The exact radial/cosh formulas
and a proved analytic remainder supply the estimate.

## 6. Actual original branch inclusion

`originalW_dispersion` identifies the actual s_epsilon and original radius
exp(-c0*epsilon). `current_branch_inclusion` and its t=0 specialization prove
positive real and imaginary parts of W. The endpoint's `original_sheet`
proves cos(phi)=W, 0<Re(phi)<pi/2 and Im(phi)<0. The preserved uniqueness
theorem identifies this with the source fourth-quadrant branch.

## 7. Original derivative, integral, attenuation and slope

`original_derivative_magnitude` proves both c/sqrt(abs(u)+epsilon) and
C/sqrt(abs(u)+epsilon) bounds for the actual real-u derivative.
`original_branch_length` proves integrability and a bound independent of
epsilon; `length_restrict` passes it to any source support inside the fixed
arc. `original_negative_attenuation` proves the actual phase estimate.
`original_positive_slope` bounds x'=deriv(Re phi) on both sides, and the
endpoint additionally proves positivity. `realPhase_deriv` supplies its
identification with Re(phi'). No norm-only substitute is used.

## 8. Second derivative and concavity

`currentPhase_second_hasDerivAt/currentPhase_second_deriv` compute the actual
second derivative. Local equality holds on an eventual open quadrant before
it is differentiated. `realPhase_second_deriv` transfers it to x''.
`original_concavity` proves -x''>=c/(u*sqrt(u)) for u>=C0*epsilon.
The scaled expression with epsilon=u*v is continuous at the origin with a
strictly negative limit; scaling is applied after the fixed-epsilon derivative
has been computed. `BranchEstimates.concavity` gives the exact Real.rpow form
c*u^(-3/2), using `reciprocal_three_halves_rpow`.

## 9. Separated extremes and asymptotics

The fixed threshold is R_sep=4*C^2*(C0+1)/a^2 for the constructed slope data.
`separated_difference` covers all 0<=m<=M/2, splitting at m=C0*epsilon.
It proves difference>=min(k/4,a/2)/sqrt(m+epsilon). `separated_quotient`
proves denominator positivity and quotient<=C_sep/sqrt(M).
`BranchEstimates.separated` exposes both on the common final arc.
`separated_eventually` proves the source implication for any filter with
M/epsilon tending to infinity and eventual local-domain conditions.

## 10. Comparable extremes and asymptotics

For M/2<m<M and R_cmp*epsilon<=m, R_cmp=C0, the mean value theorem and proved
concavity give the slope difference >=k*(M-m)/(M*sqrt(M)).
`comparable_quotient` and the endpoint projection prove denominator positivity
and quotient<=(2*C^2/k)*sqrt(M)/(M-m). `comparable_eventually` proves the
corresponding implication from m/epsilon tending to infinity for any filter.
The fixed thresholds therefore have proved asymptotic correspondence.

## 11. Current plateau at s=s_epsilon

`currentW/currentD/currentPhase` use the actual radial parameter and
height -c0*epsilon+tau*t/2. The current theorem has no free s.
`current_imaginary_factorization` keeps beta exact and possibly u-dependent;
`current_imaginary_margin` bounds beta by positive multiples of Q.
`current_real_remainder` retains the real quadratic displacement;
`current_modulus_Q` gives both modulus bounds. No sign of Re D at u=0 is
assumed. The original is exactly the t=0 specialization.

## 12. Source lambda_* and occupancy specialization

`source_current_range` proves that for fixed t0>0 an epsilon0>0 can be chosen
such that lambda<=epsilon^alpha and 0<=rho<=1 imply 0<=lambda*rho<t0.
The proof uses alpha>0 and continuity at zero. `lemma_branch` applies this
after choosing the common radius/current threshold, and then shrinks the
final epsilon0 for all other restrictions.
`BranchEstimates.current_occupancy` proves rho=P/N belongs to [0,1] from
N>0 and 0<=P<=N, and exposes the actual t=lambda*P/N estimate.
`source_inner_radius` restricts the common arc to the source
r0=deltaB/(2*L^2), for deltaB<=r and L>=1.

## 13. Current derivative, attenuation and exact cone

The endpoint's `current` and `current_occupancy` give two-sided actual
derivative bounds using E=epsilon+t, negative-side attenuation and exactly
Re(phi_u)>=(2/3)*norm(phi_u) for u>=0. The Q/E comparison uses fixed tau>0.
All real-u derivatives keep P,lambda,t,E,Q fixed. The direct logarithmic/
square-root proof handles the actual phase and the allowed O(E^2) real
center displacement; it is not restricted to an abstract linear model.

## 14. Constant and quantifier order

Fixed source point/angles/c0, tau and alpha come first. Analytic/sector
margins, radii, all estimate constants, C0 and both quotient thresholds are
chosen next. A smaller common radius r fixes t0=r. Only then is final
epsilon0 chosen, including epsilon^alpha<t0. The theorem subsequently
quantifies over epsilon,N,lambda,P/N,u,m,M. No constant or neighborhood
depends on those varying parameters. No uniformity as tau tends to zero
is claimed. The source's c,C notation can denote minima/maxima of the
finitely many positive fixed constants in the conclusion bundle.

## 15. Remaining fixed source assumptions

`LocalBranchData` contains only 0<theta<pi/2, 0<thetaB<pi,
cos(thetaB)=2*cos(theta)-1, c0>0, the positive b_B margin, tau>0, alpha>0.
The occupancy corollary exposes N>0 and 0<=P<=N. No desired estimate,
branch inclusion, source-range implication or unformalized manuscript lemma
is an input. CORRESPONDENCE.md gives the complete clause-by-clause audit.

## 16. Clean verification

The unchanged verifier was run:

```powershell
Set-Location -LiteralPath 'I:\Codex\Ising lean\formalization'
.\verify.ps1 -Clean
```

It validates frozen pins and dependency sources, the exact manuscript blob,
the forbidden-construct scan and explicit root imports. It removes only the
checked project build directory and performs ordinary `lake build` from
source, retaining dependency caches. Canonical receipts:
`../run_logs/final_build_receipt.json` and `../run_logs/final_build.log`.
Console receipt: `../run_logs/branch_finish_verify_console.log`.

## 17. Reachable axiom union

Exactly `propext`, `Classical.choice`, `Quot.sound`. The verifier, auditor
and whitelist were unchanged. All production modules are root-imported.
No proof holes, project-local mathematical axioms or unsafe/native bypasses.

## 18. Remaining blockers and representation choices

No source-relevant blocker remains for the displayed `lem:branch`.
The direct logarithmic branch and exact radial/cosh formulas were retained.
Analytic Taylor bounds, direct branch transfer and a scaled actual second
derivative supplied all estimates. A general h(D) factorization was unnecessary.
The optional proof-internal chord and |phi'|/|1-Z| consequences are unclaimed.
`SchurRecurrence R` remains OPEN/UNUSED, unrelated to branch closure.

## 19. Changed files and reproduction

New production modules and exact declarations are listed below. Among prior
production files only `IsingBulk.lean` changed, to add root imports. Updated
records: CORRESPONDENCE.md, CLAIM_LEDGER.tsv, COVERAGE.md, GAP_MANIFEST.md,
AUTHORED_DECLARATIONS.tsv, DECLARATIONS.tsv, README.md, LIBRARY_INVENTORY.md.
Local attempt/build logs and baseline copies are `../run_logs/branch_finish_*`.
`refresh_branch_finish_records.ps1` regenerates inventories and records from
the successful clean audit. `final_build*` are the existing canonical receipts.

```powershell
Set-Location -LiteralPath 'I:\Codex\Ising lean\formalization'
.\verify.ps1 -Clean
& '..\run_logs\refresh_branch_finish_records.ps1'
```

For an affected-module build:

```powershell
$env:PATH = 'I:\Codex\GauLean\toolchain\lean-4.34.1-windows\bin;' + $env:PATH
lake build IsingBulk.Analysis.BranchEndpoint
```

## 20. Scope preservation

FIRST and TAIL remain NOT_STARTED. No selector/contraction/originaldisk or
later TAIL node was advanced. The prior arithmetic/Pfaffian, Lie and Jets
proofs and all three original Branch modules match baseline hashes.
The local identities cited from originaldisk were proved directly from
definitions, so no global unformalized dependency entered the proof.

## 21. Frozen payloads and remote state

The manuscript identity and frozen configuration/dependency pins pass the
unchanged verifier. Every control-packet file is rehash-compared with the
supplied ZIP. No frozen manuscript, audit, provenance, release or control
payload was edited. No push, tag, release, merge, history rewrite or other
remote repository action occurred. MR1, W1/W2 and historical audits supply
no mathematical premise.

## Verified build totals

- Build: PASS (3629 jobs), exit 0.
- Clean started: 10/03/2026 11:06:44.
- Clean finished: 10/03/2026 11:12:39.
- Audited kernel-safe declarations: 1666.
- Authored declarations: 687, including 511 theorems.
- New authored declarations: 135, including 110 theorems, in 21 modules.
- Unmodified packet files checked: 31.

## New production modules

- `IsingBulk/Analysis/BranchAsymptotic.lean`
- `IsingBulk/Analysis/BranchAttenuation.lean`
- `IsingBulk/Analysis/BranchConcavity.lean`
- `IsingBulk/Analysis/BranchCone.lean`
- `IsingBulk/Analysis/BranchCurrentTaylor.lean`
- `IsingBulk/Analysis/BranchData.lean`
- `IsingBulk/Analysis/BranchDerivative.lean`
- `IsingBulk/Analysis/BranchEndpoint.lean`
- `IsingBulk/Analysis/BranchInclusion.lean`
- `IsingBulk/Analysis/BranchLength.lean`
- `IsingBulk/Analysis/BranchMagnitude.lean`
- `IsingBulk/Analysis/BranchModulus.lean`
- `IsingBulk/Analysis/BranchQuotientData.lean`
- `IsingBulk/Analysis/BranchQuotients.lean`
- `IsingBulk/Analysis/BranchScaled.lean`
- `IsingBulk/Analysis/BranchSecondDerivative.lean`
- `IsingBulk/Analysis/BranchSeparated.lean`
- `IsingBulk/Analysis/BranchSlope.lean`
- `IsingBulk/Analysis/BranchSourceRange.lean`
- `IsingBulk/Analysis/BranchTaylor.lean`
- `IsingBulk/Analysis/BranchTheorem.lean`

## Exact new authored declaration inventory

| Declaration | Kind | Source file:line |
|---|---|---|
| `IsingBulk.Branch.ratio_atTop_eventually_threshold` | theorem | `IsingBulk/Analysis/BranchAsymptotic.lean:8` |
| `IsingBulk.Branch.OriginalQuotientData.separated_eventually` | theorem | `IsingBulk/Analysis/BranchAsymptotic.lean:14` |
| `IsingBulk.Branch.OriginalQuotientData.comparable_eventually` | theorem | `IsingBulk/Analysis/BranchAsymptotic.lean:30` |
| `IsingBulk.Branch.sqrt_negative_cone_of_real_margin` | theorem | `IsingBulk/Analysis/BranchAttenuation.lean:8` |
| `IsingBulk.Branch.logarithmic_attenuation` | theorem | `IsingBulk/Analysis/BranchAttenuation.lean:18` |
| `IsingBulk.Branch.factor_real_upper` | theorem | `IsingBulk/Analysis/BranchAttenuation.lean:63` |
| `IsingBulk.Branch.current_negative_factor_margin` | theorem | `IsingBulk/Analysis/BranchAttenuation.lean:79` |
| `IsingBulk.Branch.current_negative_attenuation_Q` | theorem | `IsingBulk/Analysis/BranchAttenuation.lean:121` |
| `IsingBulk.Branch.current_negative_attenuation` | theorem | `IsingBulk/Analysis/BranchAttenuation.lean:165` |
| `IsingBulk.Branch.original_negative_attenuation` | theorem | `IsingBulk/Analysis/BranchAttenuation.lean:182` |
| `IsingBulk.Branch.original_concavity` | theorem | `IsingBulk/Analysis/BranchConcavity.lean:8` |
| `IsingBulk.Branch.sqrt_cone_of_real_margin` | theorem | `IsingBulk/Analysis/BranchCone.lean:8` |
| `IsingBulk.Branch.quotient_two_thirds_cone` | theorem | `IsingBulk/Analysis/BranchCone.lean:18` |
| `IsingBulk.Branch.factor_real_lower` | theorem | `IsingBulk/Analysis/BranchCone.lean:53` |
| `IsingBulk.Branch.current_positive_factor_margin` | theorem | `IsingBulk/Analysis/BranchCone.lean:68` |
| `IsingBulk.Branch.current_positive_cone` | theorem | `IsingBulk/Analysis/BranchCone.lean:113` |
| `IsingBulk.Branch.current_remainder_identity` | theorem | `IsingBulk/Analysis/BranchCurrentTaylor.lean:9` |
| `IsingBulk.Branch.current_normal_form` | theorem | `IsingBulk/Analysis/BranchCurrentTaylor.lean:30` |
| `IsingBulk.Branch.current_real_remainder` | theorem | `IsingBulk/Analysis/BranchCurrentTaylor.lean:88` |
| `IsingBulk.Branch.LocalBranchData` | structure | `IsingBulk/Analysis/BranchData.lean:13` |
| `IsingBulk.Branch.LocalBranchData.a` | def | `IsingBulk/Analysis/BranchData.lean:29` |
| `IsingBulk.Branch.LocalBranchData.b` | def | `IsingBulk/Analysis/BranchData.lean:30` |
| `IsingBulk.Branch.LocalBranchData.a_pos` | theorem | `IsingBulk/Analysis/BranchData.lean:32` |
| `IsingBulk.Branch.LocalBranchData.b_pos` | theorem | `IsingBulk/Analysis/BranchData.lean:34` |
| `IsingBulk.Branch.currentW` | def | `IsingBulk/Analysis/BranchData.lean:36` |
| `IsingBulk.Branch.currentD` | def | `IsingBulk/Analysis/BranchData.lean:38` |
| `IsingBulk.Branch.currentPhase` | def | `IsingBulk/Analysis/BranchData.lean:39` |
| `IsingBulk.Branch.originalW` | def | `IsingBulk/Analysis/BranchData.lean:40` |
| `IsingBulk.Branch.originalD` | def | `IsingBulk/Analysis/BranchData.lean:41` |
| `IsingBulk.Branch.originalPhase` | def | `IsingBulk/Analysis/BranchData.lean:42` |
| `IsingBulk.Branch.originalRealPhase` | def | `IsingBulk/Analysis/BranchData.lean:43` |
| `IsingBulk.Branch.currentW_dispersion` | theorem | `IsingBulk/Analysis/BranchData.lean:45` |
| `IsingBulk.Branch.originalW_dispersion` | theorem | `IsingBulk/Analysis/BranchData.lean:50` |
| `IsingBulk.Branch.current_components` | theorem | `IsingBulk/Analysis/BranchData.lean:56` |
| `IsingBulk.Branch.radialTraceModel` | def | `IsingBulk/Analysis/BranchData.lean:71` |
| `IsingBulk.Branch.branchDModel` | def | `IsingBulk/Analysis/BranchData.lean:75` |
| `IsingBulk.Branch.radialTraceModel_eq` | theorem | `IsingBulk/Analysis/BranchData.lean:80` |
| `IsingBulk.Branch.branchDModel_eq` | theorem | `IsingBulk/Analysis/BranchData.lean:96` |
| `IsingBulk.Branch.branchDModel_zero` | theorem | `IsingBulk/Analysis/BranchData.lean:102` |
| `IsingBulk.Branch.branchDModel_analytic` | theorem | `IsingBulk/Analysis/BranchData.lean:107` |
| `IsingBulk.Branch.sin_lowerArccos` | theorem | `IsingBulk/Analysis/BranchDerivative.lean:9` |
| `IsingBulk.Branch.currentDu` | def | `IsingBulk/Analysis/BranchDerivative.lean:21` |
| `IsingBulk.Branch.currentDuu` | def | `IsingBulk/Analysis/BranchDerivative.lean:25` |
| `IsingBulk.Branch.currentD_hasDerivAt` | theorem | `IsingBulk/Analysis/BranchDerivative.lean:29` |
| `IsingBulk.Branch.currentDu_hasDerivAt` | theorem | `IsingBulk/Analysis/BranchDerivative.lean:37` |
| `IsingBulk.Branch.currentPhase_hasDerivAt` | theorem | `IsingBulk/Analysis/BranchDerivative.lean:49` |
| `IsingBulk.Branch.currentPhase_deriv` | theorem | `IsingBulk/Analysis/BranchDerivative.lean:60` |
| `IsingBulk.Branch.currentPhase_deriv_norm` | theorem | `IsingBulk/Analysis/BranchDerivative.lean:67` |
| `IsingBulk.Branch.reciprocal_sqrt_rpow` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:9` |
| `IsingBulk.Branch.reciprocal_three_halves_rpow` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:13` |
| `IsingBulk.Branch.BranchEstimates.positive_slope` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:21` |
| `IsingBulk.Branch.BranchEstimates.concavity` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:30` |
| `IsingBulk.Branch.BranchEstimates.separated` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:39` |
| `IsingBulk.Branch.BranchEstimates.comparable` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:54` |
| `IsingBulk.Branch.BranchEstimates.original_sheet` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:65` |
| `IsingBulk.Branch.BranchEstimates.current_sheet` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:73` |
| `IsingBulk.Branch.BranchEstimates.current_occupancy` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:82` |
| `IsingBulk.Branch.BranchEstimates.source_inner_radius` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:100` |
| `IsingBulk.Branch.BranchEstimates.length_restrict` | theorem | `IsingBulk/Analysis/BranchEndpoint.lean:113` |
| `IsingBulk.Branch.sinhQuotient` | def | `IsingBulk/Analysis/BranchInclusion.lean:9` |
| `IsingBulk.Branch.sinhQuotient_zero` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:11` |
| `IsingBulk.Branch.sinhQuotient_continuous` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:14` |
| `IsingBulk.Branch.sinhQuotient_identity` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:17` |
| `IsingBulk.Branch.betaE` | def | `IsingBulk/Analysis/BranchInclusion.lean:20` |
| `IsingBulk.Branch.betaT` | def | `IsingBulk/Analysis/BranchInclusion.lean:24` |
| `IsingBulk.Branch.beta_coefficients_continuous` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:27` |
| `IsingBulk.Branch.beta_coefficients_zero` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:37` |
| `IsingBulk.Branch.current_imaginary_factorization` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:42` |
| `IsingBulk.Branch.beta_coefficients_near_zero` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:52` |
| `IsingBulk.Branch.current_imaginary_margin` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:66` |
| `IsingBulk.Branch.currentW_zero` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:92` |
| `IsingBulk.Branch.currentW_continuous` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:99` |
| `IsingBulk.Branch.current_branch_inclusion` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:107` |
| `IsingBulk.Branch.current_phase_sheet` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:128` |
| `IsingBulk.Branch.original_branch_inclusion` | theorem | `IsingBulk/Analysis/BranchInclusion.lean:140` |
| `IsingBulk.Branch.reciprocal_sqrt_integral` | theorem | `IsingBulk/Analysis/BranchLength.lean:11` |
| `IsingBulk.Branch.original_branch_length` | theorem | `IsingBulk/Analysis/BranchLength.lean:55` |
| `IsingBulk.Branch.currentDu_zero` | theorem | `IsingBulk/Analysis/BranchMagnitude.lean:9` |
| `IsingBulk.Branch.currentDu_continuous` | theorem | `IsingBulk/Analysis/BranchMagnitude.lean:12` |
| `IsingBulk.Branch.current_factors_near_zero` | theorem | `IsingBulk/Analysis/BranchMagnitude.lean:17` |
| `IsingBulk.Branch.sqrt_quotient_bounds` | theorem | `IsingBulk/Analysis/BranchMagnitude.lean:41` |
| `IsingBulk.Branch.current_derivative_magnitude_Q` | theorem | `IsingBulk/Analysis/BranchMagnitude.lean:63` |
| `IsingBulk.Branch.current_derivative_magnitude` | theorem | `IsingBulk/Analysis/BranchMagnitude.lean:91` |
| `IsingBulk.Branch.original_derivative_magnitude` | theorem | `IsingBulk/Analysis/BranchMagnitude.lean:130` |
| `IsingBulk.Branch.modulus_of_component_bounds` | theorem | `IsingBulk/Analysis/BranchModulus.lean:8` |
| `IsingBulk.Branch.current_modulus_Q` | theorem | `IsingBulk/Analysis/BranchModulus.lean:43` |
| `IsingBulk.Branch.original_slope_regular` | theorem | `IsingBulk/Analysis/BranchQuotientData.lean:10` |
| `IsingBulk.Branch.OriginalQuotientData` | structure | `IsingBulk/Analysis/BranchQuotientData.lean:27` |
| `IsingBulk.Branch.original_quotient_data` | theorem | `IsingBulk/Analysis/BranchQuotientData.lean:48` |
| `IsingBulk.Branch.OriginalQuotientData.slope_drop` | theorem | `IsingBulk/Analysis/BranchQuotientData.lean:72` |
| `IsingBulk.Branch.separated_quotient_algebra` | theorem | `IsingBulk/Analysis/BranchQuotients.lean:6` |
| `IsingBulk.Branch.OriginalQuotientData.separated_quotient` | theorem | `IsingBulk/Analysis/BranchQuotients.lean:17` |
| `IsingBulk.Branch.OriginalQuotientData.comparable_quotient` | theorem | `IsingBulk/Analysis/BranchQuotients.lean:39` |
| `IsingBulk.Branch.coshSlope` | def | `IsingBulk/Analysis/BranchScaled.lean:9` |
| `IsingBulk.Branch.coshSlope_continuous` | theorem | `IsingBulk/Analysis/BranchScaled.lean:12` |
| `IsingBulk.Branch.coshSlope_zero` | theorem | `IsingBulk/Analysis/BranchScaled.lean:18` |
| `IsingBulk.Branch.coshSlope_identity` | theorem | `IsingBulk/Analysis/BranchScaled.lean:24` |
| `IsingBulk.Branch.scaledOriginalD` | def | `IsingBulk/Analysis/BranchScaled.lean:29` |
| `IsingBulk.Branch.scaledOriginalD_zero` | theorem | `IsingBulk/Analysis/BranchScaled.lean:34` |
| `IsingBulk.Branch.scaledOriginalD_continuous` | theorem | `IsingBulk/Analysis/BranchScaled.lean:37` |
| `IsingBulk.Branch.scaledOriginalD_identity` | theorem | `IsingBulk/Analysis/BranchScaled.lean:44` |
| `IsingBulk.Branch.sqrt_positive_real_mul` | theorem | `IsingBulk/Analysis/BranchScaled.lean:62` |
| `IsingBulk.Branch.scaledH` | def | `IsingBulk/Analysis/BranchScaled.lean:74` |
| `IsingBulk.Branch.originalD_scaled_continuous` | theorem | `IsingBulk/Analysis/BranchScaled.lean:77` |
| `IsingBulk.Branch.scaledH_zero` | theorem | `IsingBulk/Analysis/BranchScaled.lean:88` |
| `IsingBulk.Branch.scaledH_continuous` | theorem | `IsingBulk/Analysis/BranchScaled.lean:92` |
| `IsingBulk.Branch.scaledSecond` | def | `IsingBulk/Analysis/BranchScaled.lean:96` |
| `IsingBulk.Branch.sqrt_scaledH_zero` | theorem | `IsingBulk/Analysis/BranchScaled.lean:101` |
| `IsingBulk.Branch.scaledSecond_zero` | theorem | `IsingBulk/Analysis/BranchScaled.lean:107` |
| `IsingBulk.Branch.scaledSecond_continuous` | theorem | `IsingBulk/Analysis/BranchScaled.lean:111` |
| `IsingBulk.Branch.scaledSecond_negative_near` | theorem | `IsingBulk/Analysis/BranchScaled.lean:123` |
| `IsingBulk.Branch.scaledSecond_identity` | theorem | `IsingBulk/Analysis/BranchScaled.lean:143` |
| `IsingBulk.Branch.real_parameter_sin_derivative` | theorem | `IsingBulk/Analysis/BranchSecondDerivative.lean:9` |
| `IsingBulk.Branch.current_phase_sin_ne_zero` | theorem | `IsingBulk/Analysis/BranchSecondDerivative.lean:15` |
| `IsingBulk.Branch.current_phase_quadrant_near` | theorem | `IsingBulk/Analysis/BranchSecondDerivative.lean:29` |
| `IsingBulk.Branch.currentPhase_second_hasDerivAt` | theorem | `IsingBulk/Analysis/BranchSecondDerivative.lean:43` |
| `IsingBulk.Branch.currentPhase_second_deriv` | theorem | `IsingBulk/Analysis/BranchSecondDerivative.lean:67` |
| `IsingBulk.Branch.realPhase_deriv` | theorem | `IsingBulk/Analysis/BranchSecondDerivative.lean:76` |
| `IsingBulk.Branch.OriginalQuotientData.slope_antitone` | theorem | `IsingBulk/Analysis/BranchSeparated.lean:7` |
| `IsingBulk.Branch.OriginalQuotientData.large_separation` | theorem | `IsingBulk/Analysis/BranchSeparated.lean:19` |
| `IsingBulk.Branch.OriginalQuotientData.separationThreshold` | def | `IsingBulk/Analysis/BranchSeparated.lean:42` |
| `IsingBulk.Branch.OriginalQuotientData.separationThreshold_pos` | theorem | `IsingBulk/Analysis/BranchSeparated.lean:45` |
| `IsingBulk.Branch.OriginalQuotientData.small_separation` | theorem | `IsingBulk/Analysis/BranchSeparated.lean:53` |
| `IsingBulk.Branch.OriginalQuotientData.separated_difference` | theorem | `IsingBulk/Analysis/BranchSeparated.lean:85` |
| `IsingBulk.Branch.realPhase_second_deriv` | theorem | `IsingBulk/Analysis/BranchSlope.lean:7` |
| `IsingBulk.Branch.original_positive_slope` | theorem | `IsingBulk/Analysis/BranchSlope.lean:20` |
| `IsingBulk.Branch.source_current_range` | theorem | `IsingBulk/Analysis/BranchSourceRange.lean:9` |
| `IsingBulk.Branch.source_occupancy_range` | theorem | `IsingBulk/Analysis/BranchSourceRange.lean:26` |
| `IsingBulk.Branch.analytic_quadratic_remainder` | theorem | `IsingBulk/Analysis/BranchTaylor.lean:8` |
| `IsingBulk.Branch.shifted_cosh_remainder` | theorem | `IsingBulk/Analysis/BranchTaylor.lean:25` |
| `IsingBulk.Branch.original_remainder_identity` | theorem | `IsingBulk/Analysis/BranchTaylor.lean:46` |
| `IsingBulk.Branch.original_normal_form` | theorem | `IsingBulk/Analysis/BranchTaylor.lean:66` |
| `IsingBulk.Branch.CurrentParameters` | def | `IsingBulk/Analysis/BranchTheorem.lean:11` |
| `IsingBulk.Branch.BranchEstimates` | structure | `IsingBulk/Analysis/BranchTheorem.lean:14` |
| `IsingBulk.Branch.lemma_branch` | theorem | `IsingBulk/Analysis/BranchTheorem.lean:54` |
