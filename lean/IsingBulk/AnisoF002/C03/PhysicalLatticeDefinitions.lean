import IsingBulk.Anisotropic.FormFactors.PublishedRealInput
import IsingBulk.Anisotropic.FormFactors.ComplexContours

/-!
# Explicit finite lattice contours for F002's physical identification

The contour radius is a parameter, so one actual radius may be fixed before
all particle numbers and all lattice sites.  Both integer displacement signs
are retained through their absolute values; their equivalence to the original
Fourier convention is a separate proof obligation.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.FormFactors

def literalLatticeDensity {N : ℕ} (lam : ℝ) (z : ℂ) (v : LatticeSite)
    (x y : Fin N → ℂ) : ℂ :=
  coordinateProduct x ^ v.1.natAbs * coordinateProduct y ^ v.2.natAbs *
    onsiteDensity lam z x y

def literalLatticeCoefficientAtRadius (N : ℕ) (r lam : ℝ) (z : ℂ) (v : LatticeSite) : ℂ :=
  (N.factorial : ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
    multiCircleIntegral r N (fun x => literalLatticeDensity lam z v x y))

end
end IsingBulk.AnisoF002.RegularTail.C03
