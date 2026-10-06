import IsingBulk.First.ActualDensityAnalytic
import IsingBulk.First.CoefficientPhase

/-! The highest pole's parameter derivative belongs to the actual physical
radius-free denominator; the scalar Ds formula is identified with that derivative. -/
namespace IsingBulk.First
noncomputable section
open Complex

theorem actual_center_root_hasDerivAt (a : OrderedChartData) :
    HasDerivAt (fun s : ℂ => phaseRoot (sourceW s (exp (-(a.alpha:ℂ)*I))))
      (exp (-(a.beta:ℂ)*I) * I * IsingBulk.Jets.sourceSPrime (exp ((a.theta:ℂ)*I)) /
        (Real.sin a.beta:ℂ)) (exp ((a.theta:ℂ)*I)) := by
  let s₀ := exp ((a.theta:ℂ)*I)
  have hw : HasDerivAt (fun s => sourceW s (exp (-(a.alpha:ℂ)*I)))
      (IsingBulk.Jets.sourceSPrime s₀) s₀ :=
    (IsingBulk.Jets.sourceS_hasDerivAt s₀ (exp_ne_zero _)).sub_const _
  have ho := lowerArccos_hasDerivAt_regular (Real.cos a.beta:ℂ)
    (lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt)
  rw [lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])] at ho
  have hc := ho.comp_of_eq s₀ hw (sourceW_density_center a).symm
  have hr := (hc.const_mul (-I)).cexp
  convert hr using 1
  · funext s
    rfl
  · dsimp [s₀]
    rw [sourceW_density_center, lowerArccos_cos a.beta a.beta_pos
      (by linarith [a.beta_lt, Real.pi_pos])]
    rw [show -I*(a.beta:ℂ) = -(a.beta:ℂ)*I by ring, ← ofReal_sin]
    ring

theorem actual_shape_denominator_hasDerivAt (a : OrderedChartData) (n : ℕ)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    HasDerivAt (fun s => complexDensityDenominator a.alpha (s,(0 : Fin (n+1) → ℂ)))
      (a.Ds (n+1)) (exp ((a.theta:ℂ)*I)) := by
  have h := ((actual_center_root_hasDerivAt a).pow (n+1)).const_sub 1
  have hz : exp (-(a.beta:ℂ)*I)^(n+1) = 1 := negative_angle_pow (by simpa using hb)
  convert h using 1
  · funext s
    simp [complexDensityDenominator, complexDensityZ, complexDensityY]
  · rw [sourceW_density_center, phaseRoot,
      lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])]
    rw [show -I*(a.beta:ℂ) = -(a.beta:ℂ)*I by ring]
    simp only [Nat.add_sub_cancel]
    rw [a.Ds_eq_sourceSPrime]
    have hm : exp (-(a.beta:ℂ)*I)^n * exp (-(a.beta:ℂ)*I) = 1 := by
      rw [← pow_succ, hz]
    simp only [Nat.cast_add, Nat.cast_one]
    linear_combination (-(n+1:ℂ)*I*IsingBulk.Jets.sourceSPrime (exp ((a.theta:ℂ)*I)) /
      (Real.sin a.beta:ℂ)) * (hm.symm)

theorem actual_shape_denominator_deriv (a : OrderedChartData) (n : ℕ)
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
end IsingBulk.First
