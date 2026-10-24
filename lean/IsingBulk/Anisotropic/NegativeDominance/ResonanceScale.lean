import IsingBulk.Anisotropic.NegativeDominance.ExactModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform exact bounds on the resonant parameter. These establish the
scale comparison needed for the dimension-uniform beta measure. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem tau_bounds (n : ℕ) (hn : 0 < n) :
    2 / (n : ℝ)^2 ≤ tau n ∧ tau n ≤ Real.pi^2 / (2 * (n : ℝ)^2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : |Real.pi / n| ≤ Real.pi := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_self Real.pi_pos.le hn1
  have hl := Real.cos_le_one_sub_mul_cos_sq hx
  have hu := Real.one_sub_sq_div_two_le_cos (x := Real.pi / n)
  have hlow : 2 / Real.pi^2 * (Real.pi / n)^2 = 2 / (n : ℝ)^2 := by
    field_simp
  have hhigh : (Real.pi / n)^2 / 2 = Real.pi^2 / (2 * (n : ℝ)^2) := by ring
  rw [hlow] at hl
  rw [hhigh] at hu
  unfold tau
  constructor <;> linarith

theorem tau_pos (n : ℕ) (hn : 0 < n) : 0 < tau n :=
  lt_of_lt_of_le (by positivity) (tau_bounds n hn).1

/-- Exact constants bounding `2 n² τₙ`, as used in the radial beta error. -/
theorem scaled_tau_bounds (n : ℕ) (hn : 0 < n) :
    4 ≤ 2 * (n : ℝ)^2 * tau n ∧
      2 * (n : ℝ)^2 * tau n ≤ Real.pi^2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hl, hu⟩ := tau_bounds n hn
  have hl' := (div_le_iff₀ (show 0 < (n : ℝ)^2 by positivity)).mp hl
  have hu' := (le_div_iff₀ (show 0 < 2 * (n : ℝ)^2 by positivity)).mp hu
  constructor <;> nlinarith

end
end IsingBulk.Anisotropic.NegativeDominance
