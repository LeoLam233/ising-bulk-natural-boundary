import IsingBulk.AnisoF002.C03.PhysicalCovarianceAttachment
import IsingBulk.AnisoF002.C03.PhysicalFiniteLatticeBridge

/-!
# The exact original full real-lattice physical identification

The finite residue construction discharges the remaining mathematical
input of the covariance assembly.  Only the original published real spin
form-factor premise remains.  Both full lattice sums, the connected
subtraction, the onsite normalization, and the original beta factor are
the unchanged fields of the original output specification.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors

theorem literal_realPhysicalIdentification (J : ℝ) {lam : ℝ}
    (hlam : 0 < lam) {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    RealPhysicalIdentification J lam corrH corrL := by
  apply literal_realPhysicalIdentification_from_finite_residues J hlam hphys
  intro x hx hp
  exact exists_physical_finite_lattice_identity hlam hx hp

end
end IsingBulk.AnisoF002.RegularTail.C03
