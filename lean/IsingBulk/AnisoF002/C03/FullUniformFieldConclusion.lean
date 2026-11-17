import IsingBulk.AnisoF002.C03.IsotropicFullBoundary
import IsingBulk.AnisoF002.C03.PhysicalNegativeHighBoundary
import IsingBulk.AnisoF002.C03.PhysicalUniformIdentification
import IsingBulk.AnisoF002.TargetSpec

/-!
# The exact original full uniform-field conclusion

The independent F002 anisotropic and internal isotropic mechanisms cover
every positive finite ratio. The unchanged original physical premises
then identify the complete lattice susceptibility and the literal HT
bilateral and LT plus-phase right energy-field derivatives. This module
assembles only independently proved F002 results into the frozen type.
-/

namespace IsingBulk.AnisoF002
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.Anisotropic.PhysicalField

theorem literal_fullAnalyticConclusion {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam) :
    FullAnalyticConclusion J lam := by
  by_cases hunit : lam = 1
  · subst lam
    exact ⟨Isotropic.isotropic_high_normalized_naturalBoundary,
      Isotropic.isotropic_low_normalized_naturalBoundary,
      Isotropic.isotropic_high_physical_naturalBoundary hJ,
      Isotropic.isotropic_low_physical_naturalBoundary hJ⟩
  · exact ⟨RegularTail.C03.anisotropic_high_normalized_naturalBoundary hlam hunit,
      RegularTail.C03.anisotropic_low_normalized_naturalBoundary hlam hunit,
      RegularTail.C03.anisotropic_high_physical_naturalBoundary hJ hlam hunit,
      RegularTail.C03.anisotropic_low_physical_naturalBoundary hJ hlam hunit⟩

theorem full_analytic_conclusion
    {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (_hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    FullAnalyticConclusion J lam :=
  literal_fullAnalyticConclusion hJ hlam

theorem full_uniform_field_conclusion
    {J lam : ℝ} (hJ : 0 < J) (hlam : 0 < lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    {mH mL : ℝ → ℝ → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL) :
    FullUniformFieldConclusion J lam corrH corrL mH mL :=
  ⟨⟨literal_fullAnalyticConclusion hJ hlam,
      RegularTail.C03.literal_realPhysicalIdentification J hlam hphys⟩,
    Physical.literal_realUniformFieldIdentification hJ hlam hphys hG⟩

end
end IsingBulk.AnisoF002
