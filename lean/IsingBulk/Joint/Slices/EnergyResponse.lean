import IsingBulk.Joint.Slices.FullBoundary
import IsingBulk.Joint.PhysicalField.Identification
import IsingBulk.Anisotropic.Final.PhysicalNormalization

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic

def highEnergyResponse (J lam : ℝ) : ℂ → ℂ :=
  inverseTemperature J * (FormFactors.highNormalizedBulk ∘ ratioSlice lam)
def lowEnergyResponse (J lam : ℝ) : ℂ → ℂ :=
  inverseTemperature J * (FormFactors.lowNormalizedBulk ∘ ratioSlice lam)

theorem high_energy_slice_naturalBoundary {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam) :
    NaturalBoundaryOn (omegaH lam) (highEnergyResponse J lam) := by
  have h := joint_high_slice_naturalBoundary hphys hlam
  refine ⟨fun z hz => (inverseTemperature_analytic J z).mul (h.1 z hz),?_⟩
  intro z hz
  exact physical_response_no_extension hJ (high_boundary_ne_zero hlam hz) (h.2 z hz)

theorem low_energy_slice_naturalBoundary {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam) :
    NaturalBoundaryOn (omegaL lam) (lowEnergyResponse J lam) := by
  have h := joint_low_slice_naturalBoundary hphys hlam
  refine ⟨fun z hz => (inverseTemperature_analytic J z).mul (h.1 z hz),?_⟩
  intro z hz
  exact physical_response_no_extension hJ (low_boundary_ne_zero hlam hz) (h.2 z hz)

theorem high_energy_slice_componentwise {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam) :
    HolomorphicNaturalBoundaryOn (omegaH lam) (highEnergyResponse J lam) := by
  have h := high_energy_slice_naturalBoundary hphys hJ hlam
  refine ⟨h.1.differentiableOn,?_⟩
  intro z hz he
  exact h.2 z hz (scalar_fullExtension_of_holomorphic
    (holomorphicFullExtension_of_component (omegaH_hasLocalCollar hlam) hz he))

theorem low_energy_slice_componentwise {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam) :
    HolomorphicNaturalBoundaryOn (omegaL lam) (lowEnergyResponse J lam) := by
  have h := low_energy_slice_naturalBoundary hphys hJ hlam
  refine ⟨h.1.differentiableOn,?_⟩
  intro z hz he
  exact h.2 z hz (scalar_fullExtension_of_holomorphic
    (holomorphicFullExtension_of_component (omegaL_hasLocalCollar hlam) hz he))

end
end IsingBulk.Joint
