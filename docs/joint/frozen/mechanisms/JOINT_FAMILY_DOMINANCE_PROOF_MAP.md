# JOINT compact-family discrete dominance and coefficient assembly

Author-development proof map, 23 October 2026. This is not an independent audit or a clean frozen build receipt. All listed Lean modules have passed the task's strict module compiler. Namespace: `IsingBulk.Joint.Negative`.

## Scope and quantifier discipline

The family is genuinely complex: `B rootB : ℂ × E → ℂ`, with `E` an arbitrary complex normed space and `K : Set E` compact. Both functions are jointly analytic at `(0, eta)` for each `eta ∈ K`, and their central values are nonzero. Only the natural fiber-germ square identity is assumed. No real-valued anisotropy, fixed phase, fixed B, coefficient dominance, or extension obstruction is assumed.

All family radii, error constants and particle/order thresholds are chosen before `eta ∈ K`. Selected integer orders are allowed to vary with eta, exactly as stated in JOINT §5.10. A common selected order for every parameter is not asserted.

## Paper-to-declaration map

| Paper mechanism | Module and declaration | Actual content and dependencies |
|---|---|---|
| §5.10, common scalar neighborhoods | `FamilyDominanceData.compact_family_square_identity` | A common disk follows from joint analytic bounds on the compact parameter set and fiberwise analytic uniqueness. A common square-identity disk is not assumed. |
| §5.8, exact analytic corrections | `FamilyDominanceScalar.compact_family_hessian_sequence`, `compact_family_B_log_norm_bound`, `compact_family_modelAnalyticError_bound`, `compact_family_model_constants_bound` | Actual Hessian converges quadratically on a common particle tail; actual B logarithmic increment is O(n⁻²); the model's complete analytic correction and central logarithmic constants have common bounds. Uses actual moving-center logarithms and compact joint Cauchy estimates. |
| Exact prefactor/nonvanishing | `FamilyDominanceData.compact_family_model_data`; `FamilyDominancePrefactor.compact_family_physical_prefactor_eventually_nonzero` | Actual B(tau n,eta), rootB(tau n,eta), Hessian and full model prefactor are nonzero on a common tail. Actual square identity and bounded correction accompany these data. |
| (5.68), strict discrete concavity | `FamilyDominanceConcavity.compact_family_physical_model_second_difference_upper`, `compact_family_physical_model_strict_concavity` | A genuine exact finite-difference upper bound and common strict concavity on the entire eligible Gamma range. Reuses the frozen algebraic model decomposition and Gamma error estimate, not a differentiated asymptotic remainder. |
| (5.72)–(5.75), actual integer selection | `FamilyDominanceCrossing.compact_family_physical_model_integer_selection`; `FamilyDominanceCentered.compact_family_physical_model_centered_selection` | Actual integer derivative orders in the crossing interval, O(p/n) balance, and strict gaps to both admissible neighbors. The threshold is common; the selected integer is parameter dependent. |
| (5.76), whole intermediate sum | `FamilyDominanceMiddle.compact_family_physical_model_middle_dominance`; `FamilyDominanceMiddleSum.compact_family_physical_model_middle_sum`; `FamilyDominanceResonantSum.compact_family_physical_resonant_middle_sum`; `FamilyDominanceResonantSmall.compact_family_physical_resonant_middle_small` | Covers every other resonant particle in the whole eligible middle range, not a fixed window. Complex phases are arbitrary. Finite sum norm estimates follow from exact concavity and actual nonzero central prefactor. |
| §5.9, model growth and complementary ranges | `FamilyDominanceGrowth.compact_family_physical_model_growth_bound`; `FamilyDominanceRangeGrowth.compact_family_physical_growth_on_crossing_range`, `compact_family_physical_low_on_crossing_range`; `FamilyDominanceOuterRanges.compact_family_physical_high_on_crossing_range`, `compact_family_physical_gaussian_on_crossing_range` | A common lower logarithmic rate `j(2 log n-G)` and comparison of all low/high/Gaussian envelopes at EVERY order in the crossing interval. Thus the same order selected for middle dominance controls all ranges. |
| §5.9, exact complete particle assembly | `FamilyDominanceAssembly.family_particle_series_ranges`, `compact_family_particle_estimates_ranges`, `compact_family_negative_paper_ranges_of_particle_estimates` | Derives exact `HasCoefficientRanges` and infinite summability from common low/nonresonant/middle/high per-particle estimates. D,C precede every model and parameter. The final declaration uses the actual `negativePaperCoefficient` and literal odd-coefficient lift. This algebraic layer holds over any parameter set and needs no compactness itself. |
| (5.84), no cancellation in the complete coefficient | `FamilyDominanceSelection.compact_family_complete_coefficient_selected_growth` | From the exact common `HasCoefficientRanges` interface, derives `‖selected physicalModel‖/2 ≤ ‖coeff eta j‖` and `exp(j(2 log n-G))/2 ≤ ‖coeff eta j‖`, at the SAME selected j, with G,N before eta. No selected-coefficient dominance is supplied as a premise. |
| §5.10, actual formal radius zero | `FamilyDominanceRadius.compact_family_complete_coefficient_radius_zero` | The actual scalar formal series of each family member has radius zero, derived from the common selected-growth theorem. The coefficient-range interface is an INTERNAL mathematical input to this generic lemma, not an external physics premise. It is discharged by `FamilyCurveRanges.compact_normalized_negative_family_ranges` and supplied by `FamilyObstruction.compact_normalized_negative_family_obstruction` in the final physical endpoint. |
| §5.10, uniform failure of Cauchy bounds | `FamilyDominanceUniformGrowth.compact_family_complete_coefficient_uniform_unbounded` | For every r>0 and C, a COMMON particle threshold works for every family member, and each later admissible particle has a selected j with `C < ‖coeff eta j‖ r^j`. This quantifies uniformity beyond merely asserting pointwise zero radius. |

## Internal interfaces discharged by the final physical endpoint

`compact_family_complete_coefficient_selected_growth` consumes a common `a>0`, `D>0`, `C`, one error sequence tending to zero, and

`∀ᶠ j in atTop, ∀ eta ∈ K, HasCoefficientRanges (coeff eta) (familyMember B eta) (familyMember rootB eta) phi p a D C error j`.

The algebraic physical export takes `curve : E → ℂ → Coupling` and `amp B rootB : E → ℂ → ℂ`. Therefore a jointly analytic family is passed as `fun eta => familyMember B eta`; no freezing at t=0 is performed. Its complete coefficient is `negativePaperCoefficient (curve eta) (amp eta)`.

The low and nonresonant bounds in that assembly are common bounds on individual actual particles. The middle/high estimates are `∀ᶠ j, ∀ eta ∈ K, ...`, not `∀ eta, ∀ᶠ j, ...`. The assembly cannot promote pointwise eventual thresholds to uniform ones. These exact internal inputs are discharged by the actual cycle, Cauchy, winding and Gaussian estimates in `FamilyCoefficientRanges.compact_family_negative_paper_ranges` and `FamilyCurveRanges.compact_normalized_negative_family_ranges`. `FamilyObstruction.lean:47–68` passes the resulting common range statement to the three generic dominance endpoints; the final physical and arbitrary-original-family endpoints therefore have no `HasCoefficientRanges` or other estimate premise. This internal mathematical interface is distinct from the separately typed published real-temperature spin/Gibbs interfaces.

## Honest stronger-estimate boundary

The sharp auxiliary asymptotics `j_n = n²(log n + ½ log log n - c*(eta) + o(1))` and `|a_(j_n)|^(1/j_n) ~ 4j_n/(eπ² log j_n)` are not established by these declarations. They are not silently identified with the coarser crossing and supergeometric-growth results. The proved results suffice for the frozen J/R/I nonextension conclusions and actual compact-family dominance, but any final manuscript-coverage statement must retain this distinction.

## Reproduction

From `project/lean`, run `../../coordination/COMPILE_ONE.sh IsingBulk/Joint/Negative/FamilyDominanceNAME.lean`. The helper uses pinned Lean 4.34.1, warnings as errors, and canonical `.lake/build/lib/lean` output. All source files are additive; no baseline rewrite is involved. Final clean validation and independent audits are separate root-owned obligations.
