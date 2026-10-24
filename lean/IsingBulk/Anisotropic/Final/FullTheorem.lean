import IsingBulk.Anisotropic.Final.HighTheorem
import IsingBulk.Anisotropic.Final.LowTheorem
import IsingBulk.Anisotropic.Final.CompleteTarget

namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors PhysicalField

/-- Full analytic Theorem 1.1: HT and connected pure-phase LT, normalized
covariance and energy-field susceptibility, all finite positive anisotropies. -/
theorem full_analytic_conclusion {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    FullAnalyticConclusion J lam :=
  fullAnalyticConclusion_of_normalized hJ hlam
    (highNormalizedBulk_naturalBoundary hlam hphys)
    (lowNormalizedBulk_naturalBoundary hlam hphys)

/-- Full-lattice physical covariance identification and all four natural
boundaries. The sole physical-entry input is the published real spin formula. -/
theorem full_physical_conclusion {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    FullPhysicalConclusion J lam corrH corrL :=
  ⟨full_analytic_conclusion hJ hlam hphys,
    realPhysicalIdentification_of_published J hlam hphys⟩

/-- Full literal uniform-field result, including the bilateral HT and
right-sided plus-phase LT thermodynamic derivatives. Published Gibbs-field
conditions remain separate from the published spin/form-factor interface. -/
theorem full_uniform_field_conclusion {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL) :
    FullUniformFieldConclusion J lam corrH corrL mH mL :=
  fullUniformFieldConclusion_of_analytic hJ hlam hphys hG (full_analytic_conclusion hJ hlam hphys)

end
end IsingBulk.Anisotropic
