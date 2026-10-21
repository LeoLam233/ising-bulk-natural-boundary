import IsingBulk.First.RegularDensityAnalytic
import IsingBulk.First.CoefficientPhase

/-! Actual regular-chart density and pole jets, preserving every physical
source expression. Only required source-facing statements are generalized. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set Metric IsingBulk.Branch IsingBulk.First
open scoped Topology BigOperators

theorem Ds_eq_sourceSPrime (a : RegularChartData) (N : ℕ) :
    a.Ds N = -Complex.I * (N : ℂ) *
      IsingBulk.Jets.sourceSPrime (Complex.exp ((a.theta : ℂ)*Complex.I)) /
        (Real.sin a.beta : ℂ) := by
  have he : Complex.exp (-Complex.I*(a.theta : ℂ)) =
      (Complex.exp ((a.theta : ℂ)*Complex.I))⁻¹ := by
    rw [show -Complex.I*(a.theta : ℂ) = -((a.theta : ℂ)*Complex.I) by ring, Complex.exp_neg]
  have he' : Complex.exp (-(a.theta : ℂ)*Complex.I) =
      (Complex.exp ((a.theta : ℂ)*Complex.I))⁻¹ := by
    rw [neg_mul, Complex.exp_neg]
  unfold RegularChartData.Ds IsingBulk.Jets.sourceSPrime
  rw [Complex.ofReal_sin, Complex.sin, he, he']
  field_simp [Complex.exp_ne_zero, Complex.ofReal_ne_zero.mpr a.sin_beta_pos.ne']
  ring

theorem actualRegularFactor_center_explicit (a : RegularChartData) (n : ℕ)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    actualRegularFactor (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ) =
      2 * (2 ^ (2*(firstStrictPairs (n+1)).card) : ℂ)⁻¹ *
        ((I*(Real.sin a.beta:ℂ))^(2*(firstStrictPairs (n+1)).card+(n+1)))⁻¹ *
        ((2*(Real.pi:ℂ))^(n+1))⁻¹ := by
  have hy : exp (-(a.alpha:ℂ)*I)^(n+1) = 1 := negative_angle_pow (by simpa using ha)
  have hz : exp (-(a.beta:ℂ)*I)^(n+1) = 1 := negative_angle_pow (by simpa using hb)
  have hp : shapeZProduct (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ) = 1 := by
    simpa [shapeZProduct, coordinateProduct] using hz
  unfold actualRegularFactor
  simp only [hp, inv_one, shapeZ_density_center, shapeY_zero_exact,
    negative_angle_pair_value, negative_angle_residue_value,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, hy, hz]
  rw [pow_add]
  simp only [one_div, mul_pow, ← pow_mul, mul_inv_rev]
  ring

theorem actual_center_root_hasDerivAt (a : RegularChartData) :
    HasDerivAt (fun s : ℂ => phaseRoot (sourceW s (exp (-(a.alpha:ℂ)*I))))
      (exp (-(a.beta:ℂ)*I) * I * IsingBulk.Jets.sourceSPrime (exp ((a.theta:ℂ)*I)) /
        (Real.sin a.beta:ℂ)) (exp ((a.theta:ℂ)*I)) := by
  let s₀ := exp ((a.theta:ℂ)*I)
  have hw : HasDerivAt (fun s => sourceW s (exp (-(a.alpha:ℂ)*I)))
      (IsingBulk.Jets.sourceSPrime s₀) s₀ :=
    (IsingBulk.Jets.sourceS_hasDerivAt s₀ (exp_ne_zero _)).sub_const _
  have ho := lowerArccos_hasDerivAt_regular (Real.cos a.beta:ℂ)
    (lowerArccos_analytic_cos_of_lt_pi a.beta a.beta_pos a.beta_lt_pi)
  rw [lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt_pi, Real.pi_pos])] at ho
  have hc := ho.comp_of_eq s₀ hw (sourceW_density_center a).symm
  have hr := (hc.const_mul (-I)).cexp
  convert hr using 1
  · funext s
    rfl
  · dsimp [s₀]
    rw [sourceW_density_center, lowerArccos_cos a.beta a.beta_pos
      (by linarith [a.beta_lt_pi, Real.pi_pos])]
    rw [show -I*(a.beta:ℂ) = -(a.beta:ℂ)*I by ring, ← ofReal_sin]
    ring

theorem actual_shape_denominator_hasDerivAt (a : RegularChartData) (n : ℕ)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    HasDerivAt (fun s => complexDensityDenominator a.alpha (s,(0 : Fin (n+1) → ℂ)))
      (a.Ds (n+1)) (exp ((a.theta:ℂ)*I)) := by
  have h := ((actual_center_root_hasDerivAt a).pow (n+1)).const_sub 1
  have hz : exp (-(a.beta:ℂ)*I)^(n+1) = 1 := negative_angle_pow (by simpa using hb)
  convert h using 1
  · funext s
    simp [complexDensityDenominator, complexDensityZ, complexDensityY]
  · rw [sourceW_density_center, phaseRoot,
      lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt_pi, Real.pi_pos])]
    rw [show -I*(a.beta:ℂ) = -(a.beta:ℂ)*I by ring]
    simp only [Nat.add_sub_cancel]
    rw [Ds_eq_sourceSPrime a]
    have hm : exp (-(a.beta:ℂ)*I)^n * exp (-(a.beta:ℂ)*I) = 1 := by
      rw [← pow_succ, hz]
    simp only [Nat.cast_add, Nat.cast_one]
    linear_combination (-(n+1:ℂ)*I*IsingBulk.Jets.sourceSPrime (exp ((a.theta:ℂ)*I)) /
      (Real.sin a.beta:ℂ)) * (hm.symm)

theorem actual_shape_denominator_deriv (a : RegularChartData) (n : ℕ)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    deriv (fun s => shapePoleDenominator s a.alpha (0 : Fin n → ℝ))
      (exp ((a.theta:ℂ)*I)) = a.Ds (n+1) := by
  have h := (actual_shape_denominator_hasDerivAt a n hb).deriv
  convert h using 1
  congr 1
  funext s
  simp only [← complexDensityDenominator_real_shape, shapeExtend_zero_exact, Pi.zero_apply, ofReal_zero]
  rfl

end
end IsingBulk.First.Regular
