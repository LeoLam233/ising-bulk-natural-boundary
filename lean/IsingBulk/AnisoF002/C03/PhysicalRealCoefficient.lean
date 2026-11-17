import IsingBulk.AnisoF002.C03.PhysicalFourierIdentification
import IsingBulk.AnisoF002.C03.PhysicalFiniteLatticeBridge

/-!
# Exact positive-real coefficient attachment at every particle number

The finite residue and actual lattice/Fourier exchanges now have no
remaining supplied identities.  Both physical real intervals and every
positive particle number use the literal original coefficients.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open scoped BigOperators

theorem canonical_coefficient_eq_original_real (n : ℕ) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) :
    canonicalAngularCoefficientF002 lam n (x : ℂ) =
      (Real.sqrt (realProduct lam x) : ℂ) ^ (n + 1) * unscaledFullCoefficient (n + 1) lam (x : ℂ) := by
  obtain ⟨r, hr, hrep⟩ := exists_physical_finite_lattice_identity hlam hx hp
  exact literal_canonical_coefficient_of_finite_residues n hlam hx hp hr hrep

theorem published_angular_coefficient_eq_original_real (n : ℕ) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) :
    angularCoefficient n (realB lam x) (realC lam x) =
      (Real.sqrt (realProduct lam x) : ℂ) ^ (n + 1) * unscaledFullCoefficient (n + 1) lam (x : ℂ) := by
  rw [← canonical_coefficient_eq_published_real n hlam hx hp]
  exact canonical_coefficient_eq_original_real n hlam hx hp

end
end IsingBulk.AnisoF002.RegularTail.C03
