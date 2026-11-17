import IsingBulk.AnisoF002.C03.NegativeHighParticleThreshold
import IsingBulk.AnisoF002.NegativeHT.IntegerSelection

/-!
# Actual integer-selection endpoint scales

The exact-factor crossing formula is tested at the two integer endpoint
scales in the frozen proof.  All logarithmic and rounding errors are
bounded explicitly; no continuous interpolation of the Taylor order is
used by the subsequent first-crossing selection.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem log_log_le_sixteenth {n : ℝ} (ht : 256 ≤ Real.log n) :
    Real.log (Real.log n) ≤ Real.log n / 16 := by
  have ht0 : 0 < Real.log n := by linarith
  have hs0 := Real.sqrt_pos.2 ht0
  have hs2 := Real.sq_sqrt ht0.le
  have hs16 : 16 ≤ Real.sqrt (Real.log n) := by nlinarith
  have hsle : Real.sqrt (Real.log n) ≤ Real.log n / 16 := by nlinarith
  have hl := log_le_half_of_pos hs0
  rw [Real.log_sqrt ht0.le] at hl
  linarith

theorem selection_scale_estimates {n j : ℝ} (hn : 1 ≤ n)
    (ht : 256 ≤ Real.log n)
    (hlo : n ^ 2 * Real.log n / 3 ≤ j)
    (hhi : j ≤ 3 * n ^ 2 * Real.log n / 2) :
    0 < j ∧ n ^ 2 ≤ j ∧ n + n ^ 3 / j + j / n ^ 3 ≤ 4 * n := by
  have hn0 : 0 < n := by linarith
  have ht3 : 3 ≤ Real.log n := by linarith
  have hm := mul_le_mul_of_nonneg_left ht3 (sq_nonneg n)
  have hsq : n ^ 2 ≤ j := by nlinarith
  have hj0 : 0 < j := (sq_pos_of_pos hn0).trans_le hsq
  have hlog : Real.log n ≤ n := by
    have hh := Real.log_le_sub_one_of_pos hn0
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (sq_nonneg n)
  have hupper : j ≤ 2 * n ^ 3 := by nlinarith [pow_nonneg hn0.le 3]
  have hdiv1 : n ^ 3 / j ≤ n := by
    apply (div_le_iff₀ hj0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hn0.le]
  have hdiv2 : j / n ^ 3 ≤ 2 := (div_le_iff₀ (pow_pos hn0 3)).mpr hupper
  exact ⟨hj0, hsq, by linarith⟩

theorem crossing_lead_lower_endpoint {n j : ℝ} (hn : 1 ≤ n)
    (ht : 256 ≤ Real.log n)
    (hlo : n ^ 2 * Real.log n / 3 ≤ j)
    (hhi : j ≤ n ^ 2 * Real.log n / 2) :
    2 * j / n - n * Real.log j ≤ -n * Real.log n := by
  have hn0 : 0 < n := by linarith
  have hwide : j ≤ 3 * n ^ 2 * Real.log n / 2 := by
    nlinarith [mul_nonneg (sq_nonneg n) (show 0 ≤ Real.log n by linarith)]
  obtain ⟨hj0, hsq, _⟩ := selection_scale_estimates hn ht hlo hwide
  have hl := Real.log_le_log (sq_pos_of_pos hn0) hsq
  rw [Real.log_pow] at hl
  norm_num at hl
  have hlmul := mul_le_mul_of_nonneg_left hl hn0.le
  have hlead : 2 * j / n ≤ n * Real.log n := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  nlinarith

theorem crossing_lead_upper_endpoint {n j : ℝ} (hn : 1 ≤ n)
    (ht : 256 ≤ Real.log n)
    (hlo : 5 * n ^ 2 * Real.log n / 4 ≤ j)
    (hhi : j ≤ 3 * n ^ 2 * Real.log n / 2) :
    n * Real.log n / 4 ≤ 2 * j / n - n * Real.log j := by
  have hn0 : 0 < n := by linarith
  have ht0 : 0 < Real.log n := by linarith
  have hj0 : 0 < j := (by positivity : 0 < 5 * n ^ 2 * Real.log n / 4).trans_le hlo
  have hl := Real.log_le_log hj0 hhi
  rw [show 3 * n ^ 2 * Real.log n / 2 = (3 / 2 : ℝ) * n ^ 2 * Real.log n by ring,
    Real.log_mul (by positivity) ht0.ne',
    Real.log_mul (by norm_num) (pow_ne_zero 2 hn0.ne'), Real.log_pow] at hl
  have hc : Real.log (3 / 2 : ℝ) ≤ Real.log n / 16 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    linarith
  have hlogj : Real.log j ≤ 17 * Real.log n / 8 := by
    linarith [log_log_le_sixteenth ht]
  have hlogmul := mul_le_mul_of_nonneg_left hlogj hn0.le
  have hlead : 5 * n * Real.log n / 2 ≤ 2 * j / n := by
    apply (le_div_iff₀ hn0).mpr
    nlinarith
  have hnt : 0 ≤ n * Real.log n := mul_nonneg hn0.le ht0.le
  nlinarith

theorem controlled_crossing_lower_negative {n j F C d : ℝ}
    (hn : 1 ≤ n) (ht : 256 ≤ Real.log n) (hC : 0 ≤ C) (hd : 0 < d)
    (hlarge : 32 * (C + 1) ≤ Real.log n)
    (hlo : n ^ 2 * Real.log n / 3 ≤ j)
    (hhi : j ≤ n ^ 2 * Real.log n / 2)
    (happrox : |F / (2 * d) - (2 * j / n - n * Real.log j)| ≤
      C * (n + n ^ 3 / j + j / n ^ 3)) : F < 0 := by
  have hn0 : 0 < n := by linarith
  have hwide : j ≤ 3 * n ^ 2 * Real.log n / 2 := by
    nlinarith [mul_nonneg (sq_nonneg n) (show 0 ≤ Real.log n by linarith)]
  have herr := mul_le_mul_of_nonneg_left (selection_scale_estimates hn ht hlo hwide).2.2 hC
  have hlead := crossing_lead_lower_endpoint hn ht hlo hhi
  have hscaled := (abs_le.mp happrox).2
  have hbig := mul_le_mul_of_nonneg_left hlarge hn0.le
  have hneg : F / (2 * d) < 0 := by nlinarith
  have hh := (div_lt_iff₀ (mul_pos (by norm_num) hd)).mp hneg
  simpa only [zero_mul] using hh

theorem controlled_crossing_upper_positive {n j F C d : ℝ}
    (hn : 1 ≤ n) (ht : 256 ≤ Real.log n) (hC : 0 ≤ C) (hd : 0 < d)
    (hlarge : 32 * (C + 1) ≤ Real.log n)
    (hlo : 5 * n ^ 2 * Real.log n / 4 ≤ j)
    (hhi : j ≤ 3 * n ^ 2 * Real.log n / 2)
    (happrox : |F / (2 * d) - (2 * j / n - n * Real.log j)| ≤
      C * (n + n ^ 3 / j + j / n ^ 3)) : 0 < F := by
  have hn0 : 0 < n := by linarith
  have hnlog : 0 ≤ n ^ 2 * Real.log n := mul_nonneg (sq_nonneg n) (by linarith)
  have hwide : n ^ 2 * Real.log n / 3 ≤ j := by nlinarith
  have herr := mul_le_mul_of_nonneg_left (selection_scale_estimates hn ht hwide hhi).2.2 hC
  have hlead := crossing_lead_upper_endpoint hn ht hlo hhi
  have hscaled := (abs_le.mp happrox).1
  have hbig := mul_le_mul_of_nonneg_left hlarge hn0.le
  have hpos : 0 < F / (2 * d) := by nlinarith
  exact (div_pos_iff_of_pos_right (mul_pos (by norm_num) hd)).mp hpos

end
end IsingBulk.AnisoF002.NegativeHT
