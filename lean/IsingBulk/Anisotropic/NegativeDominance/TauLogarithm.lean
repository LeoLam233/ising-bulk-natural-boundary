import IsingBulk.Anisotropic.NegativeDominance.LogSineBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! An explicit O(n⁻²) logarithmic error for the exact resonance displacement. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem tau_eq_sine_square (n : ℕ) :
    tau n = 2 * Real.sin (Real.pi / (2 * (n : ℝ)))^2 := by
  have hh := Real.sin_sq_eq_half_sub (Real.pi / (2 * (n : ℝ)))
  have he : 2 * (Real.pi / (2 * (n : ℝ))) = Real.pi / n := by ring
  rw [he] at hh
  unfold tau
  linarith

theorem log_tau_exact_sine_ratio (n : ℕ) (hn : 0 < n) :
    Real.log (tau n) = Real.log (Real.pi^2 / 2) - 2 * Real.log n +
      2 * Real.log (Real.sin (Real.pi / (2 * (n : ℝ))) / (Real.pi / (2 * (n : ℝ)))) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < Real.pi / (2 * (n : ℝ)) := by positivity
  have hsin : Real.sin (Real.pi / (2 * (n : ℝ))) ≠ 0 := by
    have ht := tau_pos n hn
    rw [tau_eq_sine_square] at ht
    intro hz
    rw [hz] at ht
    norm_num at ht
  rw [tau_eq_sine_square, Real.log_mul (by norm_num) (pow_ne_zero _ hsin), Real.log_pow,
    Real.log_div hsin hx.ne', Real.log_div (pow_ne_zero _ Real.pi_ne_zero) (by norm_num),
    Real.log_pow, Real.log_div Real.pi_ne_zero (mul_ne_zero (by norm_num) hnr.ne'),
    Real.log_mul (by norm_num) hnr.ne']
  ring

/-- Uniform explicit error bound at all n≥2. -/
theorem log_tau_error_bounds (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ Real.log (Real.pi^2 / 2) - 2 * Real.log n - Real.log (tau n) ∧
    Real.log (Real.pi^2 / 2) - 2 * Real.log n - Real.log (tau n) ≤
      Real.pi^2 / (10 * (n : ℝ)^2) := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < Real.pi / (2 * (n : ℝ)) := div_pos Real.pi_pos (by linarith)
  have hx1 : Real.pi / (2 * (n : ℝ)) ≤ 1 := by
    apply (div_le_one (by linarith)).mpr
    linarith [Real.pi_lt_four]
  have hb := log_sin_div_bounds hx hx1
  rw [log_tau_exact_sine_ratio n (by omega)]
  have he : 2 * ((Real.pi / (2 * (n : ℝ)))^2 / 5) = Real.pi^2 / (10 * (n : ℝ)^2) := by ring
  constructor
  · linarith [hb.1]
  · rw [← he]
    linarith [hb.2]

end
end IsingBulk.Anisotropic.NegativeDominance
