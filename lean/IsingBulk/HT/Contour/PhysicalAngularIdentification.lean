import IsingBulk.HT.Contour.FourierTorusCoordinates
import IsingBulk.HT.Contour.PhysicalVerticalSummation

/-!
# The published angular coefficient is the full lattice contour coefficient

The horizontal Fourier constraint is imposed on the genuine continuous
total-angle marginal. Absolute summability comes from the displaced contour
representation, not from an additional physical hypothesis. The vertical
sum is then interchanged with the constrained integral by the proved
geometric majorant.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.HT.Final
open scoped BigOperators

local instance : Fact (0 < 2*Real.pi) := ⟨Real.two_pi_pos⟩

/-- Fourier inversion at total angle zero gives the actual dependent-last
angular slice at every vertical displacement. -/
theorem physicalLatticeCoefficient_horizontal_tsum (n m : ℕ) {t r : ℝ}
    (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    (∑' k : ℤ, physicalLatticeCoefficient (n+1) t m k) =
      physicalConstrainedVerticalCoefficient n t m := by
  let c : ℂ := ((n+1).factorial:ℂ)⁻¹
  let F : (Fin (n+1) → ℝ) → ℂ := fun phi =>
    c*((physicalAngularWeight t phi*(physicalZ t phi)^m:ℝ):ℂ)
  have hF : Continuous F := continuous_const.mul (Complex.continuous_ofReal.comp
    ((physicalAngularWeight_continuous (n+1) ht).mul
      ((physicalZ_continuous (n+1) ht).pow m)))
  have hperiod : CoordinatePeriodic (n+1) F := by
    have hA : CoordinatePeriodic (n+1) (fun phi =>
        ((physicalAngularWeight t phi*(physicalZ t phi)^m:ℝ):ℂ)) := by
      simpa only [Int.cast_zero,mul_zero,zero_mul,Complex.exp_zero,mul_one] using
        physical_latticeAngularIntegrand_periodic (n+1) ht m 0
    intro phi q
    exact congrArg (fun z : ℂ => c*z) (hA phi q)
  let f : C(AddCircle (2*Real.pi),ℂ) := torusMeanCircle n F hF hperiod
  have hcoefficient (k : ℤ) :
      physicalLatticeCoefficient (n+1) t m k = fourierCoeff f (-k) := by
    change physicalLatticeCoefficient (n+1) t m k =
      fourierCoeff (torusMeanCircle n F hF hperiod) (-k)
    rw [← torus_exponential_coefficient n F hF hperiod k]
    unfold physicalLatticeCoefficient
    simp only [F,mul_assoc]
    rw [physical_multiAngleIntegral_const_mul]
    dsimp only [c]
    ring
  have hq : Summable (fun k : ℤ => physicalLatticeCoefficient (n+1) t m k) := by
    simpa only [physicalFullLatticeCoefficient,Int.natAbs_natCast] using
      (physicalFullLatticeCoefficient_summable (n+1) (by omega)
        ht hr hr1 hm).prod_factor (m:ℤ)
  have hcoeff : ∀ k : ℤ, physicalLatticeCoefficient (n+1) t m k =
      fourierCoeff f k := by
    intro k
    have hk := hcoefficient (-k)
    rw [neg_neg,physicalLatticeCoefficient_horizontal_reflection (n+1) ht m k] at hk
    exact hk
  calc
    (∑' k : ℤ,physicalLatticeCoefficient (n+1) t m k) =
        f 0 := horizontal_fourier_sum_at_zero f hq hcoeff
    _ = physicalConstrainedVerticalCoefficient n t m := by
      change torusMeanCircle n F hF hperiod 0 = _
      rw [torusMeanCircle_zero]
      dsimp only [F]
      rw [physical_multiAngleIntegral_const_mul]
      unfold physicalConstrainedVerticalCoefficient
      dsimp only [c,shapeExtend,physicalDependentAngles]
      ring

/-- The literal N-1-angle coefficient is the absolutely convergent full
square-lattice sum, with both displacement directions and every particle. -/
theorem physicalAngularCoefficient_eq_fullLattice_tsum (n : ℕ) {t r : ℝ}
    (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    physicalAngularCoefficient n t =
      ∑' v : ℤ × ℤ, physicalFullLatticeCoefficient (n+1) t v := by
  have hs := physicalFullLatticeCoefficient_summable (n+1) (by omega)
    ht hr hr1 hm
  symm
  rw [hs.tsum_prod]
  calc
    (∑' m : ℤ, ∑' k : ℤ, physicalFullLatticeCoefficient (n+1) t (m,k)) =
        ∑' m : ℤ, physicalConstrainedVerticalCoefficient n t m.natAbs := by
      apply tsum_congr
      intro m
      exact physicalLatticeCoefficient_horizontal_tsum n m.natAbs ht hr hr1 hm
    _ = physicalAngularCoefficient n t :=
      (physicalConstrainedVerticalCoefficient_summable_eq_angular n ht).2

/-- Exact physical angular-to-double-contour bridge. The radius is merely
an admissible integration contour; no equality with a physical coefficient
is included among the hypotheses. -/
theorem physicalAngularCoefficient_eq_standardFormFactor (n : ℕ) {t r : ℝ}
    (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    physicalAngularCoefficient n t = standardFormFactor (n+1) r (t:ℂ) := by
  rw [physicalAngularCoefficient_eq_fullLattice_tsum n ht hr hr1 hm]
  exact physicalFullLatticeCoefficient_tsum_eq_standardFormFactor
    (n+1) (by omega) ht hr hr1 hm

end
end IsingBulk.HT.Contour
