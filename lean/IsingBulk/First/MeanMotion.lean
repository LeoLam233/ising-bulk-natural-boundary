import IsingBulk.First.MeanDeformedDomain

/-! Exact real/imaginary mean coordinates and uniform full-rectangle geometry. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch

theorem meanChartExponent_re {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ)
    (v : ℂ) (j : Fin (n+1)) :
    (meanChartExponent rho alpha t v j).re = rho-v.im/(n+1:ℝ) := by
  have hdiv : (v/(n+1:ℂ)).im = v.im/(n+1:ℝ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using Complex.div_ofReal_im v (n+1:ℝ)
  simp [meanChartExponent, hdiv, Complex.mul_re]
  ring

theorem meanChartExponent_im {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ)
    (v : ℂ) (j : Fin (n+1)) :
    (meanChartExponent rho alpha t v j).im = -alpha+shapeExtend t j+v.re/(n+1:ℝ) := by
  have hdiv : (v/(n+1:ℂ)).re = v.re/(n+1:ℝ) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using Complex.div_ofReal_re v (n+1:ℝ)
  simp [meanChartExponent, hdiv, Complex.mul_im]
  ring

theorem meanChartExponent_eq_polar {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ)
    (v : ℂ) (j : Fin (n+1)) :
    meanChartExponent rho alpha t v j = ((rho-v.im/(n+1:ℝ):ℝ):ℂ)+
      (((-alpha+shapeExtend t j+v.re/(n+1:ℝ):ℝ):ℂ))*I := by
  apply Complex.ext
  · rw [meanChartExponent_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
  · rw [meanChartExponent_im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]

theorem meanChartW_eq_deformed {n : ℕ} (a : OrderedChartData) (c₀ epsilon : ℝ)
    (t : Fin n → ℝ) (v : ℂ) (j : Fin (n+1)) :
    IsingBulk.Jets.chartW (radialParameter a.theta epsilon) (-c₀*epsilon) a.alpha
      (((shapeExtend t j:ℝ):ℂ)+v/(n+1)) =
    deformedMeanW a c₀ (epsilon,shapeExtend t j+v.re/(n+1:ℝ),-v.im/(n+1:ℝ)) := by
  change IsingBulk.Branch.dispersion _ (exp (meanChartExponent (-c₀*epsilon) a.alpha t v j)) = _
  rw [meanChartExponent_eq_polar]
  unfold deformedMeanW
  congr 2
  push_cast
  ring

/-- The entire downward rectangle is inside one genuinely regular physical
chart; sizes are fixed before epsilon and the zero-sum shape tuple. -/
theorem full_mean_rectangle_domain (a : OrderedChartData) (c₀ : ℝ)
    (hA : 0 < a.A₀ c₀) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Real.pi ∧ ∀ (n : ℕ) (epsilon : ℝ) (t : Fin n → ℝ) (v : ℂ),
      0 < epsilon → epsilon < R → (∀ j, |shapeExtend t j| < R/4) →
      |v.re| ≤ R/4 → -R/4 ≤ v.im → v.im ≤ 0 →
      (∀ j, 0 < (IsingBulk.Jets.chartW (radialParameter a.theta epsilon) (-c₀*epsilon) a.alpha
        (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).re) ∧
      (∀ j, 0 < (IsingBulk.Jets.chartW (radialParameter a.theta epsilon) (-c₀*epsilon) a.alpha
        (((shapeExtend t j:ℝ):ℂ)+v/(n+1))).im) ∧
      (∀ j, -(Real.pi/2) < (meanChartExponent (-c₀*epsilon) a.alpha t v j).im ∧
        (meanChartExponent (-c₀*epsilon) a.alpha t v j).im < 0) := by
  obtain ⟨r,hr,hD⟩ := deformedMeanW_uniform_domain a c₀ hA
  let R := min r Real.pi
  have hR : 0 < R := lt_min hr Real.pi_pos
  have hRr : R ≤ r := min_le_left _ _
  refine ⟨R,hR,min_le_right _ _,?_⟩
  intro n epsilon t v he her ht hvre hvlo hvhi
  have hN : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hNp : (0:ℝ) < n+1 := by positivity
  have hq : |v.re/(n+1:ℝ)| ≤ R/4 := by
    rw [abs_div, abs_of_pos hNp]
    apply (div_le_iff₀ hNp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hN (show 0 ≤ R/4 by positivity)]
  have hdepth : 0 ≤ -v.im/(n+1:ℝ) := div_nonneg (by linarith) hNp.le
  have hdepth' : -v.im/(n+1:ℝ) < r := by
    have hle : -v.im/(n+1:ℝ) ≤ R/4 := by
      apply (div_le_iff₀ hNp).mpr
      nlinarith [mul_le_mul_of_nonneg_left hN (show 0 ≤ R/4 by positivity)]
    linarith
  have hpoint (j : Fin (n+1)) := hD epsilon (shapeExtend t j+v.re/(n+1:ℝ))
    (-v.im/(n+1:ℝ)) he (her.trans_le hRr)
    (show |shapeExtend t j+v.re/(n+1:ℝ)| < r from by
      have htri := abs_add_le (shapeExtend t j) (v.re/(n+1:ℝ))
      have hj := ht j
      linarith) hdepth hdepth'
  refine ⟨?_,?_,?_⟩
  · intro j
    rw [meanChartW_eq_deformed]
    exact (hpoint j).1
  · intro j
    rw [meanChartW_eq_deformed]
    exact (hpoint j).2.1
  · intro j
    rw [meanChartExponent_im]
    simpa only [add_assoc] using (hpoint j).2.2

end
end IsingBulk.First
