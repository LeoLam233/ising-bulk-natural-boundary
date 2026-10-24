import IsingBulk.Anisotropic.RegularEdges.VerticalAngularSum
import IsingBulk.HT.Contour.FourierTorusCoordinates
import IsingBulk.Anisotropic.FormFactors.PhysicalLatticeSum

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open FormFactors IsingBulk.First IsingBulk.HT.Contour IsingBulk.HT.Final
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

theorem anisotropic_horizontal_tsum (n m : ℕ) {B C : ℝ}
    (hB : 0 < B) (hgap : 1<C-B)
    (hsum : Summable (latticeCoefficient (n+1) B C)) :
    (∑' k : ℤ, latticeCoefficient (n+1) B C ((m:ℤ),k)) =
      anisotropicConstrainedVerticalCoefficient n B C m := by
  let c : ℂ := ((n+1).factorial:ℂ)⁻¹
  let F : (Fin (n+1) → ℝ) → ℂ := fun phi =>
    c*((angularWeight B C phi*(rootProduct B C phi)^m:ℝ):ℂ)
  have hF : Continuous F := continuous_const.mul (Complex.continuous_ofReal.comp
    ((angularWeight_continuous (n+1) hB.le hgap).mul
      ((rootProduct_continuous (n+1) hB.le hgap).pow m)))
  have hperiod : CoordinatePeriodic (n+1) F := by
    have hA : CoordinatePeriodic (n+1) (fun phi =>
        ((angularWeight B C phi*(rootProduct B C phi)^m:ℝ):ℂ)) := by
      simpa only [Int.natAbs_natCast,Int.cast_zero,mul_zero,zero_mul,Complex.exp_zero,mul_one] using
        lattice_integrand_periodic (n+1) hB hgap ((m:ℤ),0)
    intro phi q
    exact congrArg (fun z : ℂ => c*z) (hA phi q)
  let f : C(AddCircle (2*Real.pi),ℂ) := torusMeanCircle n F hF hperiod
  have hcoefficient (k : ℤ) :
      latticeCoefficient (n+1) B C ((m:ℤ),k) = fourierCoeff f (-k) := by
    change latticeCoefficient (n+1) B C ((m:ℤ),k) =
      fourierCoeff (torusMeanCircle n F hF hperiod) (-k)
    rw [← torus_exponential_coefficient n F hF hperiod k]
    unfold latticeCoefficient
    simp only [F,Int.natAbs_natCast,mul_assoc]
    rw [physical_multiAngleIntegral_const_mul]
    dsimp only [c]
    ring
  have hq : Summable (fun k : ℤ => latticeCoefficient (n+1) B C ((m:ℤ),k)) :=
    hsum.prod_factor (m:ℤ)
  have hcoeff : ∀ k : ℤ, latticeCoefficient (n+1) B C ((m:ℤ),k) =
      fourierCoeff f k := by
    intro k
    have hk := hcoefficient (-k)
    rw [neg_neg,latticeCoefficient_horizontal_reflection (n+1) hB hgap ((m:ℤ),k)] at hk
    exact hk
  calc
    (∑' k : ℤ,latticeCoefficient (n+1) B C ((m:ℤ),k)) =
        f 0 := horizontal_fourier_sum_at_zero f hq hcoeff
    _ = anisotropicConstrainedVerticalCoefficient n B C m := by
      change torusMeanCircle n F hF hperiod 0 = _
      rw [torusMeanCircle_zero]
      dsimp only [F]
      rw [physical_multiAngleIntegral_const_mul]
      unfold anisotropicConstrainedVerticalCoefficient
      dsimp only [c,shapeExtend,physicalDependentAngles]
      ring


end
end IsingBulk.Anisotropic.RegularEdges
