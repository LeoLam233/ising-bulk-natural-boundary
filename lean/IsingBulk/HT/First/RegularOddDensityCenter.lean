import IsingBulk.First.RegularDensityJets
import IsingBulk.HT.First.OrderArithmetic

/-! Actual regular-chart density and pole jets, preserving every physical
source expression. Only required source-facing statements are generalized. -/
namespace IsingBulk.HT.First.Regular
noncomputable section
open Complex Filter Set Metric IsingBulk.Branch IsingBulk.First IsingBulk.First.Regular
open scoped Topology BigOperators

theorem actualRegularFactor_center_eq_odd_K (a : RegularChartData) (n : ℕ)
    (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    actualRegularFactor (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ) /
      ((n+1).factorial:ℂ) = -I*(a.K (n+1):ℂ) := by
  rw [actualRegularFactor_center_explicit a n ha hb,firstStrictPairs_twice_card]
  have hex : (n+1)*n+(n+1) = (n+1)^2 := by ring
  rw [hex,mul_pow,mul_inv_rev]
  have hi : (I^((n+1)^2))⁻¹ = -I := by
    simpa only [← Nat.cast_pow,zpow_neg,zpow_natCast] using odd_particle_phase ho
  rw [hi]
  simp only [IsingBulk.First.RegularChartData.K,ofReal_mul,ofReal_div,ofReal_ofNat,
    ofReal_inv,ofReal_pow,ofReal_natCast,Nat.add_sub_cancel]
  ring

/-- Highest-pole amplitude of the literal odd density at its actual center. -/
theorem actualLeadingAmplitude_odd_center (a : RegularChartData) (n k : ℕ)
    (ho : Odd (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    actualLeadingAmplitude a n k (exp ((a.theta:ℂ)*I),0) =
      -I*((-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k) := by
  have hB : complexDensityRegular a.alpha
      (exp ((a.theta:ℂ)*I),(0 : Fin (n+1) → ℂ))/((n+1).factorial:ℂ) =
      -I*(a.K (n+1):ℂ) := by
    convert actualRegularFactor_center_eq_odd_K a n ho ha hb using 1
    rw [← complexDensityRegular_real_shape]
    simp only [shapeExtend_zero_exact,Pi.zero_apply,ofReal_zero]
    rfl
  unfold IsingBulk.First.Regular.actualLeadingAmplitude
  rw [actualSincFactor_zero,ofReal_one,one_mul,realShapeEmbedding_center]
  unfold jointPoleLeadingNumerator poleLeadingNumerator
  rw [(actual_shape_denominator_hasDerivAt a n hb).deriv]
  linear_combination (-1:ℂ)^k*(k.factorial:ℂ)*a.Ds (n+1)^k*hB

end
end IsingBulk.HT.First.Regular
