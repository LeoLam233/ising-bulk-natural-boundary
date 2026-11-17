import IsingBulk.AnisoF002.C03.PhysicalUniformField
import IsingBulk.AnisoF002.C03.PhysicalRealIdentification

/-!
# Original physical field identification from the original physical premises

The independently constructed finite residues and full lattice sum discharge
the summability required by the generic Gibbs squeeze.  The conclusion is
the unchanged original five-field specification; no extra analytic or
physical premise is added.
-/

namespace IsingBulk.AnisoF002.Physical
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.Anisotropic.PhysicalField

theorem literal_realUniformFieldIdentification {J lam : ℝ}
    (hJ : 0 < J) (hlam : 0 < lam)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL) :
    RealUniformFieldIdentification J lam corrH corrL mH mL :=
  literal_uniformField_of_realIdentification hJ hG
    (RegularTail.C03.literal_realPhysicalIdentification J hlam hphys)

end
end IsingBulk.AnisoF002.Physical
