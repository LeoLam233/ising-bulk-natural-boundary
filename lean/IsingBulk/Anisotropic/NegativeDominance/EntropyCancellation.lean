import IsingBulk.Anisotropic.NegativeDominance.ParticleLogConvexity
import IsingBulk.Anisotropic.NegativeDominance.FactorialDifferences

/-! Exact cancellation of factorial entropy against the quadratic-log term,
with a bound uniform in the particle index. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

def entropyPart (n : ℕ) : ℝ := Real.log (factorialProduct n) - particleLog n

theorem log_factorialProduct_second_difference_upper (n d : ℕ) (hn : 0 < n) :
    Real.log (factorialProduct (n + 2 * d)) - 2 * Real.log (factorialProduct (n + d)) +
      Real.log (factorialProduct n) ≤ (d : ℝ)^2 * Real.log (n + 2 * d) - (d : ℝ)^2 * Real.log 2 := by
  rw [log_factorialProduct_step_second_difference]
  apply sub_le_sub_right
  calc
    _ ≤ ∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d, Real.log ((n + 2 * d : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      apply Real.log_le_log (by positivity)
      exact_mod_cast (by have := Finset.mem_range.mp hk; have := Finset.mem_range.mp hl; omega :
        n + k + l + 1 ≤ n + 2 * d)
    _ = _ := by simp; ring

theorem entropyPart_second_difference_upper (n d : ℕ) (hn : 0 < n) :
    entropyPart (n + 2 * d) - 2 * entropyPart (n + d) + entropyPart n ≤ 2 * (d : ℝ)^3 := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hp := particleLog_second_difference_lower (d := (d : ℝ)) hnpos (by positivity)
  have hf := log_factorialProduct_second_difference_upper n d hn
  have hratio : 0 < ((n : ℝ) + 2 * d) / n := by positivity
  have hl := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (by positivity) hnpos.ne'] at hl
  have he : ((n : ℝ) + 2 * d) / n - 1 = 2 * d / n := by field_simp; ring
  rw [he] at hl
  have hdiv : 2 * (d : ℝ) / n ≤ 2 * d := by
    apply (div_le_iff₀ hnpos).mpr
    nlinarith [show (0 : ℝ) ≤ d by positivity]
  have hlog : Real.log ((n : ℝ) + 2 * d) - Real.log n ≤ 2 * d := hl.trans hdiv
  have hmul := mul_le_mul_of_nonneg_left hlog (sq_nonneg (d : ℝ))
  have htwo : 0 ≤ (d : ℝ)^2 * Real.log 2 := mul_nonneg (sq_nonneg _) (Real.log_nonneg (by norm_num))
  unfold entropyPart
  push_cast at hp hf ⊢
  nlinarith

end
end IsingBulk.Anisotropic.NegativeDominance
