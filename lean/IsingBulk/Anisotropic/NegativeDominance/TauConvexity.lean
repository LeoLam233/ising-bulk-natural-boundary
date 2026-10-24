import IsingBulk.Anisotropic.NegativeDominance.LogSineConvexity
import IsingBulk.Anisotropic.NegativeDominance.TauLogarithm

/-! Exact positivity of the log-tau second difference. Consequently the
j-amplified term is nonpositive on the entire large-particle range. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set

theorem log_tau_eq_logSineReciprocal (n : ℕ) (hn : 0 < n) :
    Real.log (tau n) = Real.log 2 + 2 * logSineReciprocal (Real.pi / 2) n := by
  have ht := tau_pos n hn
  have hs : Real.sin (Real.pi / (2 * (n : ℝ))) ≠ 0 := by
    rw [tau_eq_sine_square] at ht
    intro hz
    rw [hz] at ht
    norm_num at ht
  rw [tau_eq_sine_square, Real.log_mul (by norm_num) (pow_ne_zero _ hs), Real.log_pow]
  unfold logSineReciprocal
  congr 2
  ring

theorem log_tau_second_difference_nonneg (n d : ℕ) (hn : 4 ≤ n) :
    0 ≤ Real.log (tau (n + 2 * d)) - 2 * Real.log (tau (n + d)) + Real.log (tau n) := by
  have hc := convexOn_logSineReciprocal (show 0 < Real.pi / 2 by positivity)
  have hnr : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (n : ℝ) ∈ Ici (2 * (Real.pi / 2)) := by
    simp only [mem_Ici]
    linarith [Real.pi_lt_four]
  have hy : ((n + 2 * d : ℕ) : ℝ) ∈ Ici (2 * (Real.pi / 2)) := by
    simp only [mem_Ici] at hx ⊢
    push_cast
    linarith [show (0 : ℝ) ≤ d by positivity]
  have hm := hc.2 hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) • (n : ℝ) + (1 / 2 : ℝ) • ((n + 2 * d : ℕ) : ℝ) =
      ((n + d : ℕ) : ℝ) := by simp only [smul_eq_mul]; push_cast; ring
  rw [hmid] at hm
  simp only [smul_eq_mul] at hm
  rw [log_tau_eq_logSineReciprocal _ (by omega),
    log_tau_eq_logSineReciprocal _ (by omega), log_tau_eq_logSineReciprocal _ (by omega)]
  linarith

end
end IsingBulk.Anisotropic.NegativeDominance
