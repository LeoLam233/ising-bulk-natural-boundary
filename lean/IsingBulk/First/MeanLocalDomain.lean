import IsingBulk.First.MeanLocalRegularity

/-! Explicit geometric chart conditions imply every denominator condition
needed for the actual mean-residue contour identity. -/
namespace IsingBulk.First
noncomputable section
open Complex Set

/-- Two exponential variables on the strictly lower-right angular arc cannot
have product one, even when their moduli exceed one during mean deformation. -/
theorem exp_pair_denominator_ne_zero {u v : ℂ}
    (hu : -(Real.pi/2) < u.im ∧ u.im < 0)
    (hv : -(Real.pi/2) < v.im ∧ v.im < 0) :
    1-exp u*exp v ≠ 0 := by
  have hs : Real.sin (u.im+v.im) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hu.2, hv.2]) (by linarith [hu.1, hv.1])
  have him : (exp (u+v)).im < 0 := by
    rw [exp_im, add_im]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) hs
  intro h
  have he : exp (u+v) = 1 := by rw [exp_add]; exact (sub_eq_zero.mp h).symm
  rw [he, one_im] at him
  exact lt_irrefl _ him

/-- The source complex angular exponent, before taking its exponential. -/
def meanChartExponent {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ)
    (v : ℂ) (j : Fin (n+1)) : ℂ :=
  (rho:ℂ)+(((shapeExtend t j:ℝ):ℂ)+v/(n+1)-(alpha:ℂ))*I

theorem meanChartY_eq_exp {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ)
    (v : ℂ) (j : Fin (n+1)) : meanChartY rho alpha t v j =
      exp (meanChartExponent rho alpha t v j) := rfl

theorem meanChartY_pair_denominator_ne_zero {n : ℕ} (rho alpha : ℝ)
    (t : Fin n → ℝ) (v : ℂ)
    (ha : ∀ j, -(Real.pi/2) < (meanChartExponent rho alpha t v j).im ∧
      (meanChartExponent rho alpha t v j).im < 0) (i j : Fin (n+1)) :
    1-meanChartY rho alpha t v i*meanChartY rho alpha t v j ≠ 0 :=
  exp_pair_denominator_ne_zero (ha i) (ha j)

/-- All regularity assumptions of the actual contour theorem are discharged
from explicit pointwise geometric inequalities for its physical variables. -/
theorem meanLocalNumerator_shift_differentiableOn {n : ℕ} (s : ℂ)
    (rho alpha delta top bottom : ℝ) (t : Fin n → ℝ)
    (hr : ∀ w ∈ rectangleSet delta top bottom, ∀ j,
      0 < (IsingBulk.Jets.chartW s rho alpha
        (((shapeExtend t j:ℝ):ℂ)+(physicalMeanPole (n+1) rho+w)/(n+1))).re)
    (hi : ∀ w ∈ rectangleSet delta top bottom, ∀ j,
      0 < (IsingBulk.Jets.chartW s rho alpha
        (((shapeExtend t j:ℝ):ℂ)+(physicalMeanPole (n+1) rho+w)/(n+1))).im)
    (ha : ∀ w ∈ rectangleSet delta top bottom, ∀ j,
      -(Real.pi/2) < (meanChartExponent rho alpha t (physicalMeanPole (n+1) rho+w) j).im ∧
      (meanChartExponent rho alpha t (physicalMeanPole (n+1) rho+w) j).im < 0) :
    DifferentiableOn ℂ
      (fun w => meanLocalNumerator s rho alpha t (physicalMeanPole (n+1) rho+w))
      (rectangleSet delta top bottom) := by
  intro w hw
  have hd := meanLocalNumerator_differentiableAt s rho alpha t
    (physicalMeanPole (n+1) rho+w) (hr w hw) (hi w hw)
    (fun i j _ => meanChartY_pair_denominator_ne_zero rho alpha t
      (physicalMeanPole (n+1) rho+w) (ha w hw) i j)
  exact (hd.comp w (differentiableAt_id.const_add (physicalMeanPole (n+1) rho))).differentiableWithinAt

end
end IsingBulk.First
