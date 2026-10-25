import IsingBulk.Joint.Slices.EnergyResponse
import IsingBulk.Joint.FormFactors.NormalizedRestriction

namespace IsingBulk.Joint
noncomputable section
open Set

/-- Exact positive-ratio recovery. Each boundary assertion is proved by actual
transversals and slice density, not by restricting an ambient obstruction. -/
structure JointRecoveryConclusion : Prop where
  high_domain : ∀ lam : ℝ, 0 < lam → ratioSlice lam ⁻¹' highDomain = Anisotropic.omegaH lam
  low_domain : ∀ lam : ℝ, 0 < lam → ratioSlice lam ⁻¹' lowDomain = Anisotropic.omegaL lam
  high_identification : ∀ lam : ℝ, 0 < lam → ∀ z ∈ Anisotropic.omegaH lam,
    FormFactors.highNormalizedBulk (ratioSlice lam z) = Anisotropic.FormFactors.highNormalizedBulk lam z
  low_identification : ∀ lam : ℝ, 0 < lam → ∀ z ∈ Anisotropic.omegaL lam,
    FormFactors.lowNormalizedBulk (ratioSlice lam z) = Anisotropic.FormFactors.lowNormalizedBulk lam z
  high_boundary : ∀ lam : ℝ, 0 < lam →
    HolomorphicNaturalBoundaryOn (Anisotropic.omegaH lam)
      (FormFactors.highNormalizedBulk ∘ ratioSlice lam)
  low_boundary : ∀ lam : ℝ, 0 < lam →
    HolomorphicNaturalBoundaryOn (Anisotropic.omegaL lam)
      (FormFactors.lowNormalizedBulk ∘ ratioSlice lam)
  high_energy_formula : ∀ (J lam : ℝ) (z : ℂ), highEnergyResponse J lam z =
    (z/(2*(J:ℂ)))*FormFactors.highNormalizedBulk (ratioSlice lam z)
  low_energy_formula : ∀ (J lam : ℝ) (z : ℂ), lowEnergyResponse J lam z =
    (z/(2*(J:ℂ)))*FormFactors.lowNormalizedBulk (ratioSlice lam z)
  high_energy_boundary : ∀ J lam : ℝ, 0 < J → 0 < lam →
    HolomorphicNaturalBoundaryOn (Anisotropic.omegaH lam) (highEnergyResponse J lam)
  low_energy_boundary : ∀ J lam : ℝ, 0 < J → 0 < lam →
    HolomorphicNaturalBoundaryOn (Anisotropic.omegaL lam) (lowEnergyResponse J lam)

theorem joint_recovery_conclusion {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    JointRecoveryConclusion where
  high_domain := fun _ h => highDomain_pullback h
  low_domain := fun _ h => lowDomain_pullback h
  high_identification := fun _ h _ hz => FormFactors.highNormalizedBulk_ratioSlice h hz
  low_identification := fun _ h _ hz => FormFactors.lowNormalizedBulk_ratioSlice h hz
  high_boundary := fun _ h => joint_high_slice_componentwise hphys h
  low_boundary := fun _ h => joint_low_slice_componentwise hphys h
  high_energy_formula := fun _ _ _ => rfl
  low_energy_formula := fun _ _ _ => rfl
  high_energy_boundary := fun _ _ hJ hl => high_energy_slice_componentwise hphys hJ hl
  low_energy_boundary := fun _ _ hJ hl => low_energy_slice_componentwise hphys hJ hl

end
end IsingBulk.Joint
