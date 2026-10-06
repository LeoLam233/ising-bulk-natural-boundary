import IsingBulk.First.ComplementLocalizedFactors
import IsingBulk.First.ComplementParameterJets

/-! Genuine fixed-radius parameter analyticity of the source regular amplitude.
The selected singular factors have been removed; inactive denominators are
explicitly required nonzero at the actual source point. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- The scalar phase carrying all source s-dependence in active exponentials. -/
def sourceTemperaturePhase (s : ℂ) : ℂ := Complex.I * sourceS s

theorem sourceTemperaturePhase_analyticAt {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ sourceTemperaturePhase s := by
  exact analyticAt_const.mul (analyticAt_id.add (analyticAt_id.inv hs))

theorem sourceFactorDenominator_analyticAt {N : ℕ} (x y : Fin N → ℂ)
    (f : SingularFactorIndex N) {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (fun z => sourceFactorDenominator z x y f) s := by
  rcases f with b | (⟨b, i, j⟩ | i)
  · cases b <;> exact analyticAt_const
  · cases b <;> exact analyticAt_const
  · exact ((analyticAt_id.add (analyticAt_id.inv hs)).sub analyticAt_const).sub analyticAt_const

/-- The literal regular amplitude is holomorphic in s with r and the angular
weight fixed. No smooth angular weight is analytically continued. -/
theorem localizedRegularAmplitude_analyticAt {N : ℕ} (r : ℝ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (u : DoubleAngularVector N) {s : ℂ} (hs : s ≠ 0)
    (hden : ∀ f ∈ Jᶜ, sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0) :
    AnalyticAt ℂ (fun z => localizedRegularAmplitude r z w J u) s := by
  have hp : AnalyticAt ℂ (fun z => ∏ f ∈ Jᶜ,
      (sourceFactorDenominator z (angleTuple r u.1) (angleTuple r u.2) f)⁻¹) s := by
    apply Finset.analyticAt_fun_prod
    intro f hf
    exact (sourceFactorDenominator_analyticAt _ _ f hs).inv (hden f hf)
  exact (analyticAt_const.mul hp).mul analyticAt_const

/-- Complex derivative identity and degree bound instantiated at the actual
source amplitude and scalar temperature phase, with every radius held fixed. -/
theorem source_regular_parameter_exponential_derivative {N : ℕ} (r : ℝ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N))
    (u : DoubleAngularVector N) (U : Set ℂ) (hU : IsOpen U)
    (hs : ∀ s ∈ U, s ≠ 0)
    (hden : ∀ s ∈ U, ∀ f ∈ Jᶜ,
      sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0)
    (j : ℕ) (z : ℂ) :
    (∀ T ∈ parameterExpTerms (fun s => localizedRegularAmplitude r s w J u) sourceTemperaturePhase j,
      T.degree ≤ j) ∧
    ∀ s ∈ U,
      (deriv^[j] (fun s => localizedRegularAmplitude r s w J u *
        Complex.exp (sourceTemperaturePhase s * z))) s =
      parameterExpPolynomial z
        (parameterExpTerms (fun s => localizedRegularAmplitude r s w J u) sourceTemperaturePhase j) s *
        Complex.exp (sourceTemperaturePhase s * z) := by
  refine ⟨parameterExpTerms_degree _ _ j, ?_⟩
  exact parameter_exponential_derivative _ _ U hU
    (fun s hsU => localizedRegularAmplitude_analyticAt r w J u (hs s hsU) (hden s hsU))
    (fun s hsU => sourceTemperaturePhase_analyticAt (hs s hsU)) j z

end
end IsingBulk.First
