import IsingBulk.Anisotropic.Geometry.Profiles

namespace IsingBulk.Anisotropic
noncomputable section

theorem geometryF1_factor (lam x y : ℝ) :
    geometryF1 lam x y = Real.cosh (lam*x)^2 * (Real.cos y^2 - sliceP lam x^2) := by
  unfold geometryF1 sliceP
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem geometryF2_factor (lam x y : ℝ) :
    geometryF2 lam x y = Real.cosh x^2 * (Real.cos (lam*y)^2 - sliceQ lam x^2) := by
  unfold geometryF2 sliceQ
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem sliceP_nonneg {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) : 0 ≤ sliceP lam x := by
  simpa only [sliceP_zero] using (sliceP_strictMono hlam).monotone hx

theorem sliceQ_nonneg {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) : 0 ≤ sliceQ lam x := by
  simpa only [sliceQ_zero] using (sliceQ_strictMono hlam).monotone hx

theorem geometryF1_neg_iff {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (y : ℝ) :
    geometryF1 lam x y < 0 ↔ slicePInv lam |Real.cos y| < x := by
  conv_rhs => rw [← (sliceP_strictMono hlam).lt_iff_lt]
  rw [sliceP_apply_inv hlam,
    geometryF1_factor, show ∀ a : ℝ, Real.cosh (lam*x)^2 * a < 0 ↔ a < 0 from fun a => by
      simpa using (mul_lt_mul_iff_right₀ (sq_pos_of_pos (Real.cosh_pos (lam*x))) :
        Real.cosh (lam*x)^2 * a < Real.cosh (lam*x)^2 * 0 ↔ a < 0)]
  have hp := sliceP_nonneg hlam hx
  have ha := abs_nonneg (Real.cos y)
  have hs := sq_abs (Real.cos y)
  constructor <;> intro h <;> nlinarith

theorem geometryF2_neg_iff {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (y : ℝ) :
    geometryF2 lam x y < 0 ↔ sliceQInv lam |Real.cos (lam*y)| < x := by
  conv_rhs => rw [← (sliceQ_strictMono hlam).lt_iff_lt]
  rw [sliceQ_apply_inv hlam,
    geometryF2_factor, show ∀ a : ℝ, Real.cosh x^2 * a < 0 ↔ a < 0 from fun a => by
      simpa using (mul_lt_mul_iff_right₀ (sq_pos_of_pos (Real.cosh_pos x)) :
        Real.cosh x^2 * a < Real.cosh x^2 * 0 ↔ a < 0)]
  have hp := sliceQ_nonneg hlam hx
  have ha := abs_nonneg (Real.cos (lam*y))
  have hs := sq_abs (Real.cos (lam*y))
  constructor <;> intro h <;> nlinarith

theorem geometryF1_pos_iff {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (y : ℝ) :
    0 < geometryF1 lam x y ↔ x < slicePInv lam |Real.cos y| := by
  conv_rhs => rw [← (sliceP_strictMono hlam).lt_iff_lt]
  rw [sliceP_apply_inv hlam,
    geometryF1_factor, mul_pos_iff_of_pos_left (sq_pos_of_pos (Real.cosh_pos _))]
  have hp := sliceP_nonneg hlam hx
  have ha := abs_nonneg (Real.cos y)
  have hs := sq_abs (Real.cos y)
  constructor <;> intro h <;> nlinarith

theorem geometryF2_pos_iff {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) (y : ℝ) :
    0 < geometryF2 lam x y ↔ x < sliceQInv lam |Real.cos (lam*y)| := by
  conv_rhs => rw [← (sliceQ_strictMono hlam).lt_iff_lt]
  rw [sliceQ_apply_inv hlam,
    geometryF2_factor, mul_pos_iff_of_pos_left (sq_pos_of_pos (Real.cosh_pos _))]
  have hp := sliceQ_nonneg hlam hx
  have ha := abs_nonneg (Real.cos (lam*y))
  have hs := sq_abs (Real.cos (lam*y))
  constructor <;> intro h <;> nlinarith

/-- The two negative signs in the right half-plane give exactly the stated LT epigraph. -/
theorem negative_signs_iff_omegaL {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 ≤ z.re) :
    (geometryF1 lam z.re z.im < 0 ∧ geometryF2 lam z.re z.im < 0) ↔ z ∈ omegaL lam := by
  rw [geometryF1_neg_iff hlam hz, geometryF2_neg_iff hlam hz]
  exact max_lt_iff.symm

end
end IsingBulk.Anisotropic
