import IsingBulk.Joint.Final.PhysicalContinuation
import IsingBulk.Joint.Transverse.AllOrientations
import IsingBulk.Joint.Slices.EnergyResponse

namespace IsingBulk.Joint
noncomputable section
open Set Transverse

/-- Qualitative boundary clauses, including actual transversals and exact
slice obstructions. Quantitative family uniformity is bundled separately. -/
structure JointBoundaryConclusion : Prop where
  high_ambient : HolomorphicNaturalBoundaryOn highDomain FormFactors.highNormalizedBulk
  high_dense : frontier highDomain ⊆ closure (frontier highDomain ∩ primeRegularJointEdges)
  high_transverse : ∀ (c : ℂ→Coupling) (z : ℂ), AnalyticAt ℂ c z →
    c z∈frontier highDomain → IsPrimeRegularJointEdge (c z) →
    IsNonramifiedJointTransversal c z →
    ¬HasHolomorphicFullExtension (c ⁻¹' highDomain) (FormFactors.highNormalizedBulk∘c) z
  high_slice : ∀ lam : ℝ, 0 < lam →
    HolomorphicNaturalBoundaryOn (Anisotropic.omegaH lam)
      (FormFactors.highNormalizedBulk ∘ ratioSlice lam)
  high_energy : ∀ J lam : ℝ, 0 < J → 0 < lam →
    HolomorphicNaturalBoundaryOn (Anisotropic.omegaH lam) (highEnergyResponse J lam)
  low_ambient : HolomorphicNaturalBoundaryOn lowDomain FormFactors.lowNormalizedBulk
  low_dense : frontier lowDomain ⊆ closure (frontier lowDomain ∩ primeRegularJointEdges)
  low_transverse : ∀ (c : ℂ→Coupling) (z : ℂ), AnalyticAt ℂ c z →
    c z∈frontier lowDomain → IsPrimeRegularJointEdge (c z) →
    IsNonramifiedJointTransversal c z →
    ¬HasHolomorphicFullExtension (c ⁻¹' lowDomain) (FormFactors.lowNormalizedBulk∘c) z
  low_slice : ∀ lam : ℝ, 0 < lam →
    HolomorphicNaturalBoundaryOn (Anisotropic.omegaL lam)
      (FormFactors.lowNormalizedBulk ∘ ratioSlice lam)
  low_energy : ∀ J lam : ℝ, 0 < J → 0 < lam →
    HolomorphicNaturalBoundaryOn (Anisotropic.omegaL lam) (lowEnergyResponse J lam)

theorem joint_boundary_conclusion {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) : JointBoundaryConclusion where
  high_ambient := high_holomorphic_natural_boundary hphys
  high_dense := frontier_high_subset_closure_primeRegularJointEdges
  high_transverse := fun _ _ hc hK hr ht => prime_regular_high_curve_no_holomorphic_extension hphys hc hK hr ht
  high_slice := fun _ h => joint_high_slice_componentwise hphys h
  high_energy := fun _ _ hJ hl => high_energy_slice_componentwise hphys hJ hl
  low_ambient := low_holomorphic_natural_boundary hphys
  low_dense := frontier_low_subset_closure_primeRegularJointEdges
  low_transverse := fun _ _ hc hK hr ht => prime_regular_low_curve_no_holomorphic_extension hphys hc hK hr ht
  low_slice := fun _ h => joint_low_slice_componentwise hphys h
  low_energy := fun _ _ hJ hl => low_energy_slice_componentwise hphys hJ hl

end
end IsingBulk.Joint
