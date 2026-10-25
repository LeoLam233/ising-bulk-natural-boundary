import IsingBulk.Joint.Slices.NegativeOddBoundary
import IsingBulk.Joint.Slices.NegativeEvenBoundary
import IsingBulk.Joint.Slices.Collars
import IsingBulk.Joint.FormFactors.CompactNormal
import IsingBulk.Joint.PhysicalField.RealFamily
import IsingBulk.Anisotropic.Final.BoundaryClosure
import IsingBulk.Joint.Final.HolomorphicExtension

namespace IsingBulk.Joint
noncomputable section
open Set IsingBulk.Anisotropic

private theorem actual_high_oriented_slice {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaH lam)) (he : OrientedPrimeVEdge lam z) :
    ¬ HasDomainExtension (omegaH lam) (Anisotropic.FormFactors.highNormalizedBulk lam) z := by
  obtain ⟨hd,e,he,hv,hu,hder,hprime,ho⟩ := he
  rcases he with rfl | rfl
  · exact high_positive_slice_no_extension hlam hz (by simpa using ho) hv hu (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hder) hprime
  · exact high_negative_slice_no_extension hlam hz (by simpa using ho) hv hu (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hder) hprime

private theorem actual_low_oriented_slice {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ frontier (omegaL lam)) (he : OrientedPrimeVEdge lam z) :
    ¬ HasDomainExtension (omegaL lam) (Anisotropic.FormFactors.lowNormalizedBulk lam) z := by
  obtain ⟨hd,e,he,hv,hu,hder,hprime,ho⟩ := he
  rcases he with rfl | rfl
  · exact low_positive_slice_no_extension hlam hz (by simpa using ho) hv hu (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hder) hprime
  · exact low_negative_slice_no_extension hlam hz (by simpa using ho) hv hu (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hder) hprime

theorem joint_high_slice_analytic {lam : ℝ} (hlam : 0 < lam) :
    AnalyticOnNhd ℂ (FormFactors.highNormalizedBulk ∘ ratioSlice lam) (omegaH lam) := by
  apply DifferentiableOn.analyticOnNhd _ (omegaH_isOpen hlam)
  apply FormFactors.highNormalizedBulk_differentiableOn.comp
    (fun z _ => (FormFactors.ratioSlice_analyticAt lam z).differentiableWithinAt)
  intro z hz
  change z ∈ ratioSlice lam ⁻¹' highDomain
  rwa [highDomain_pullback hlam]

theorem joint_low_slice_analytic {lam : ℝ} (hlam : 0 < lam) :
    AnalyticOnNhd ℂ (FormFactors.lowNormalizedBulk ∘ ratioSlice lam) (omegaL lam) := by
  apply DifferentiableOn.analyticOnNhd _ (omegaL_isOpen hlam)
  apply FormFactors.lowNormalizedBulk_differentiableOn.comp
    (fun z _ => (FormFactors.ratioSlice_analyticAt lam z).differentiableWithinAt)
  intro z hz
  change z ∈ ratioSlice lam ⁻¹' lowDomain
  rwa [lowDomain_pullback hlam]

/-- Every positive finite ratio. The geometric reduction calls the newly proved
joint transverse-curve obstructions, including the entire negative odd sum. -/
theorem joint_high_slice_naturalBoundary {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {lam : ℝ} (hlam : 0 < lam) :
    NaturalBoundaryOn (omegaH lam) (FormFactors.highNormalizedBulk ∘ ratioSlice lam) := by
  have hb := high_naturalBoundary_of_oriented
    (fun _ h _ hz he => actual_high_oriented_slice h hz he) hlam (hphys lam hlam)
  refine ⟨joint_high_slice_analytic hlam,?_⟩
  intro z hz
  exact no_domain_extension_of_eqOn
    (fun w hw => (FormFactors.highNormalizedBulk_ratioSlice hlam hw).symm) (hb.2 z hz)

theorem joint_low_slice_naturalBoundary {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {lam : ℝ} (hlam : 0 < lam) :
    NaturalBoundaryOn (omegaL lam) (FormFactors.lowNormalizedBulk ∘ ratioSlice lam) := by
  have hb := low_naturalBoundary_of_oriented
    (fun _ h _ hz he => actual_low_oriented_slice h hz he) hlam (hphys lam hlam)
  refine ⟨joint_low_slice_analytic hlam,?_⟩
  intro z hz
  exact no_domain_extension_of_eqOn
    (fun w hw => (FormFactors.lowNormalizedBulk_ratioSlice hlam hw).symm) (hb.2 z hz)

theorem joint_high_slice_componentwise {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {lam : ℝ} (hlam : 0 < lam) :
    HolomorphicNaturalBoundaryOn (omegaH lam) (FormFactors.highNormalizedBulk ∘ ratioSlice lam) := by
  have h := joint_high_slice_naturalBoundary hphys hlam
  refine ⟨h.1.differentiableOn,?_⟩
  intro z hz he
  exact h.2 z hz (scalar_fullExtension_of_holomorphic
    (holomorphicFullExtension_of_component (omegaH_hasLocalCollar hlam) hz he))

theorem joint_low_slice_componentwise {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    {lam : ℝ} (hlam : 0 < lam) :
    HolomorphicNaturalBoundaryOn (omegaL lam) (FormFactors.lowNormalizedBulk ∘ ratioSlice lam) := by
  have h := joint_low_slice_naturalBoundary hphys hlam
  refine ⟨h.1.differentiableOn,?_⟩
  intro z hz he
  exact h.2 z hz (scalar_fullExtension_of_holomorphic
    (holomorphicFullExtension_of_component (omegaL_hasLocalCollar hlam) hz he))

end
end IsingBulk.Joint
