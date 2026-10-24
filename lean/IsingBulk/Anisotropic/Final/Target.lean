import IsingBulk.Anisotropic.Final.AnalyticFactor
import IsingBulk.Anisotropic.FormFactors.ComplexContours
import IsingBulk.Anisotropic.FormFactors.PublishedRealInput

/-! Early exact endpoint contract, tied to the literal infinite contour sums.
These definitions are specifications, NOT established ANISO theorems. A final
proof must construct every field from the real physical input and internal
ANISO lemmas, without taking this contract as an external assumption. -/
namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors

def highPhysicalBulk (J lam : ℝ) : ℂ → ℂ := inverseTemperature J * highNormalizedBulk lam
def lowPhysicalBulk (J lam : ℝ) : ℂ → ℂ := inverseTemperature J * lowNormalizedBulk lam

/-- All four analytic/natural-boundary claims in original Theorem 1.1. -/
def FullAnalyticConclusion (J lam : ℝ) : Prop :=
  NaturalBoundaryOn (omegaH lam) (highNormalizedBulk lam) ∧
  NaturalBoundaryOn (omegaL lam) (lowNormalizedBulk lam) ∧
  NaturalBoundaryOn (omegaH lam) (highPhysicalBulk J lam) ∧
  NaturalBoundaryOn (omegaL lam) (lowPhysicalBulk J lam)

/-- Full-site physical identification includes summability, not only equality
between totalized divergent sums. This covers every positive real temperature
on the appropriate side, not a finite-order approximation. -/
structure RealPhysicalIdentification (J lam : ℝ)
    (corrH corrL : ℝ → LatticeSite → ℝ) : Prop where
  high : ∀ x : ℝ, 0 < x → realProduct lam x < 1 →
    Summable (corrH x) ∧
    highNormalizedBulk lam (x:ℂ) = (highCovarianceSum corrH x:ℂ) ∧
    highPhysicalBulk J lam (x:ℂ) = (highEnergyFieldResponse J corrH x:ℂ)
  low : ∀ x : ℝ, 0 < x → 1 < realProduct lam x →
    Summable (fun v : LatticeSite => corrL x v-realMagnetizationSq lam x) ∧
    lowNormalizedBulk lam (x:ℂ) = (lowCovarianceSum lam corrL x:ℂ) ∧
    lowPhysicalBulk J lam (x:ℂ) = (lowEnergyFieldResponse J lam corrL x:ℂ)

def FullPhysicalConclusion (J lam : ℝ) (corrH corrL : ℝ → LatticeSite → ℝ) : Prop :=
  FullAnalyticConclusion J lam ∧ RealPhysicalIdentification J lam corrH corrL

/-- Exact energy-field normalization transfer, once real covariance equality
has actually been proved. The field-derivative interpretation is separate. -/
theorem highPhysicalBulk_real_of_covariance {J lam x : ℝ}
    {corrH : ℝ → LatticeSite → ℝ}
    (h : highNormalizedBulk lam (x:ℂ) = (highCovarianceSum corrH x:ℂ)) :
    highPhysicalBulk J lam (x:ℂ) = (highEnergyFieldResponse J corrH x:ℂ) := by
  simp only [highPhysicalBulk,Pi.mul_apply,inverseTemperature,h,highEnergyFieldResponse]
  push_cast
  rfl

theorem lowPhysicalBulk_real_of_covariance {J lam x : ℝ}
    {corrL : ℝ → LatticeSite → ℝ}
    (h : lowNormalizedBulk lam (x:ℂ) = (lowCovarianceSum lam corrL x:ℂ)) :
    lowPhysicalBulk J lam (x:ℂ) = (lowEnergyFieldResponse J lam corrL x:ℂ) := by
  simp only [lowPhysicalBulk,Pi.mul_apply,inverseTemperature,h,lowEnergyFieldResponse]
  push_cast
  rfl

end
end IsingBulk.Anisotropic
