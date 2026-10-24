import IsingBulk.Anisotropic.FormFactors.PublishedRealInput

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section

theorem real_dispersion_factorization (lam x : ℝ) :
    (Real.cosh x*Real.cosh (lam*x)-Real.sinh x-Real.sinh (lam*x))*
    (Real.cosh x*Real.cosh (lam*x)+Real.sinh x+Real.sinh (lam*x)) =
      (realProduct lam x-1)^2 := by
  have hx := Real.cosh_sq_sub_sinh_sq x
  have hy := Real.cosh_sq_sub_sinh_sq (lam*x)
  unfold realProduct
  nlinarith [sq_nonneg (Real.sinh x),sq_nonneg (Real.sinh (lam*x)),
    mul_nonneg (sq_nonneg (Real.sinh x)) (sq_nonneg (Real.sinh (lam*x)))]

theorem realB_pos {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    0 < realB lam x :=
  div_pos (Real.sinh_pos_iff.mpr (mul_pos hlam hx)) (Real.sinh_pos_iff.mpr hx)

/-- Positive physical gap holds on both temperature sides; criticality is
the only excluded positive real point. -/
theorem real_dispersion_gap {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) : 1 < realC lam x-realB lam x := by
  have hS : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hT : 0 < Real.sinh (lam*x) := Real.sinh_pos_iff.mpr (mul_pos hlam hx)
  have hA : 0 < Real.cosh x*Real.cosh (lam*x) := mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have hprod : 0 <
      (Real.cosh x*Real.cosh (lam*x)-Real.sinh x-Real.sinh (lam*x))*
      (Real.cosh x*Real.cosh (lam*x)+Real.sinh x+Real.sinh (lam*x)) := by
    rw [real_dispersion_factorization]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hp)
  have hsum : 0 < Real.cosh x*Real.cosh (lam*x)+Real.sinh x+Real.sinh (lam*x) := by positivity
  have hdiff := pos_of_mul_pos_left hprod hsum.le
  unfold realC realB
  rw [← sub_div]
  apply (lt_div_iff₀ hS).mpr
  linarith

theorem physical_gamma_pos {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) (q : ℝ) :
    0 < gamma (realB lam x) (realC lam x) q :=
  gamma_pos (realB_pos hlam hx).le (real_dispersion_gap hlam hx hp) q
end
end IsingBulk.Anisotropic.FormFactors
