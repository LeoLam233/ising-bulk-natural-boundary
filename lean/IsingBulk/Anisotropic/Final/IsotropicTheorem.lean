import IsingBulk.Anisotropic.Final.IsotropicHighTheorem
import IsingBulk.Anisotropic.Final.IsotropicLowTheorem
import IsingBulk.Anisotropic.Final.PhysicalIdentification
import IsingBulk.Anisotropic.Final.PhysicalNormalization

namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors

/-- Exact λ=1 instance of the full ANISO scope, including both complete sums,
all boundary points, the LT covering, and physical β normalization. -/
theorem isotropic_full_physical_conclusion {J : ℝ} (hJ : 0<J)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors 1 corrH corrL) :
    FullPhysicalConclusion J 1 corrH corrL :=
  ⟨fullAnalyticConclusion_of_normalized hJ (by norm_num)
    highNormalizedBulk_one_naturalBoundary (lowNormalizedBulk_one_naturalBoundary hphys),
    realPhysicalIdentification_of_published J (by norm_num) hphys⟩

end
end IsingBulk.Anisotropic
