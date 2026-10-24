# Theorem and proof correspondence

## Actual terminal theorem

The frozen declaration in [FullTheorem.lean](../../lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) is:

```lean
theorem full_uniform_field_conclusion {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL) :
    FullUniformFieldConclusion J lam corrH corrL mH mL
```

Its full name is `IsingBulk.Anisotropic.full_uniform_field_conclusion`; `LatticeSite` is `ℤ × ℤ`. Every real `J > 0` and `lam > 0` is covered. The two explicit physical inputs are expanded in [PHYSICAL_INPUTS.md](PHYSICAL_INPUTS.md). They are theorem parameters, so an axiom listing alone cannot audit them.

`FullUniformFieldConclusion` in [CompleteTarget.lean](../../lean/IsingBulk/Anisotropic/Final/CompleteTarget.lean) is the conjunction of `FullPhysicalConclusion` and `RealUniformFieldIdentification`. The former in [Target.lean](../../lean/IsingBulk/Anisotropic/Final/Target.lean) contains four natural-boundary claims plus real full-site summability and covariance/energy-field equalities. The latter contains the bilateral HT derivative at zero, zero HT mean, right-sided LT derivative, LT zero-field magnetization square, and positive plus mean.

## Complex domains and full observables

Write `z = 2βJ`, `p = sinh z sinh(lam z)`, and let `P(x) = cosh x tanh(lam x)`, `Q(x) = cosh(lam x) tanh x` on the nonnegative real axis. With `Y = π/(2 max(1,lam))`, the profiles are

```text
H(y) = min(P⁻¹(cos y), Q⁻¹(cos(lam y)))       (|y| < Y)
L(y) = max(P⁻¹(|cos y|), Q⁻¹(|cos(lam y)|))
omegaH = {z : |Im z| < Y and |Re z| < H(Im z)}
omegaL = {z : L(Im z) < Re z}
```

These domains are defined independently of the boundary obstruction. [Geometry](../../lean/IsingBulk/Anisotropic/Geometry/) establishes their spectral identities and frontiers. `NaturalBoundaryOn D f` means `AnalyticOnNhd ℂ f D` and, for every `z ∈ frontier D`, absence of a genuine local analytic extension agreeing with `f` on the intersection with `D`. [LocalExtension.lean](../../lean/IsingBulk/Anisotropic/Final/LocalExtension.lean) quantifies an open neighborhood and an analytic function; it is not a surrogate singularity predicate. The frontier quantifier concerns every finite complex point, including exceptional contacts handled by closure/density.

The actual HT target is the prefactor times `∑' n, p^n * unscaledFullCoefficient (2*n+1) lam z`; the connected LT target uses `∑' n, p^(n+1) * unscaledFullCoefficient (2*n+2) lam z`. The energy-field targets multiply these functions by `z/(2J)`. [CompleteScope.lean](../../lean/IsingBulk/Anisotropic/Controls/CompleteScope.lean) checks every odd/positive-even order, the full lattice rather than a diagonal, finite-particle countermodels, and exact lambda-one correspondence.

## Dependency routes

| Part of the argument | Frozen source route |
|---|---|
| Exact spectral geometry, lens and epigraph | `Geometry/` |
| Real spin coefficients, full-site exchange and complex contour sums | `FormFactors/` |
| Positive HT edges and both LT signs; differentiated infinite-tail bounds | `RegularEdges/` and final high/low assembly |
| Negative HT edges, permutation-equivariant pole normal form and beta-period bounds | `NegativeNormalForm/`, `NegativeCycles/`, `NegativeDominance/` |
| Selected particle dominance and zero Taylor radius | `NegativeDominance.high_negative_prime_no_extension`, `actual_negative_paper_radius_zero` and their actual physical-kernel dependencies |
| All frontier points and analytic factors | `Final/BoundaryReduction.lean`, `BoundaryClosure.lean`, `HighTheorem.lean`, `LowTheorem.lean`, `AnalyticFactor.lean` |
| Exact isotropic seeds | `Final/IsotropicSeeds.lean` imports `IsingBulk.HT.Final.interiorFullBulk_unit_circle_no_extension` and `IsingBulk.Final.theorem_nb` for the normalized exterior bulk |
| Exact lambda-one full-sum identification | `Final/IsotropicHighReal.lean`, `IsotropicLowReal.lean`, `IsotropicHighTheorem.lean`, `IsotropicLowTheorem.lean` |
| Uniform-field finite-law calculus and thermodynamic squeeze | `PhysicalField/` and `Final/FieldDerivative.lean`, `CompleteTarget.lean` |

The lambda-one step uses the normalized LT exterior theorem at its existing scope and an exact real-interval/full-sum match; it does not assume an enlarged LT physical chart or take an anisotropic limit.

## Executed closure and nonvacuity checks

The unchanged [AuditAnisotropic.lean](../../lean/AuditAnisotropic.lean) prints the elaborated endpoint/contract types and definitions, traverses checked types and proof values, checks required substantive dependencies and restricts axioms to `propext`, `Classical.choice`, `Quot.sound`. The new [AuditAnisotropicClosure.lean](../../lean/AuditAnisotropicClosure.lean) adds `isPartial` to the transitive closure check and explicitly inventories the 30 compiler-generated project partial execution helpers outside that closure. The full build is not claimed to contain no partial declarations.

The frozen [Nonvacuity.lean](../../lean/IsingBulk/Anisotropic/Controls/Nonvacuity.lean) constructs nonempty domains/frontiers, proves constants admit the actual extension predicate, and rejects a constant as an LT natural boundary. [PhysicalConventions.lean](../../lean/IsingBulk/Anisotropic/Controls/PhysicalConventions.lean) checks the positive-coupling requirement, connected subtraction and exact beta factor. These controls and the original audit are executed strictly in addition to separate fresh kernel replays.
