import IsingBulk.Anisotropic.Final.PhysicalIdentification
import IsingBulk.Anisotropic.PhysicalField.GibbsFieldConditions

namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors PhysicalField Set

/-- Literal uniform energy-field derivatives, separate from the βX definitions. -/
structure RealFieldDerivativeIdentification (J lam : ℝ)
    (corrH corrL : ℝ → LatticeSite → ℝ) (mH mL : ℝ → ℝ → ℝ) : Prop where
  high : ∀ x, 0<x → realProduct lam x<1 →
    HasDerivWithinAt (mH x) (highEnergyFieldResponse J corrH x) (Ioi 0) 0
  low : ∀ x, 0<x → 1<realProduct lam x →
    HasDerivWithinAt (mL x) (lowEnergyFieldResponse J lam corrL x) (Ioi 0) 0

/-- Internally proved thermodynamic response theorem once genuine real Gibbs
field data are attached. This does not assert that the form-factor predicate
alone implies the additional Gibbs-field conditions. -/
theorem realFieldDerivativeIdentification_of_gibbs {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hH : ∀ x, 0<x → realProduct lam x<1 →
      GibbsFieldConditions (x/(2*J)) (corrH x) (mH x))
    (hL : ∀ x, 0<x → 1<realProduct lam x →
      GibbsFieldConditions (x/(2*J)) (fun v => corrL x v-realMagnetizationSq lam x) (mL x)) :
    RealFieldDerivativeIdentification J lam corrH corrL mH mL := by
  constructor
  · intro x hx hp
    exact field_response_of_gibbs_conditions (le_of_lt (div_pos hx (mul_pos (by norm_num) hJ)))
      (hH x hx hp) (high_covariance_sum hlam hx hp hphys).1
  · intro x hx hp
    exact field_response_of_gibbs_conditions (le_of_lt (div_pos hx (mul_pos (by norm_num) hJ)))
      (hL x hx hp) (low_covariance_sum hlam hx hp hphys).1

end
end IsingBulk.Anisotropic
