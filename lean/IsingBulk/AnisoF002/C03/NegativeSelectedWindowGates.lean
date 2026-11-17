import IsingBulk.AnisoF002.C03.NegativeSelectedModelGrowth

/-!
# The selected integer orders lie inside the full physical middle window

These estimates attach the genuine integer selection scale to the actual
low/high particle cutoffs and to the vanishing first-winding model error.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem selected_scale_log_range {n j : ℝ} (hn : 1 ≤ n)
    (ht : 256 ≤ Real.log n)
    (hlo : n ^ 2 * Real.log n / 3 ≤ j)
    (hhi : j ≤ 3 * n ^ 2 * Real.log n / 2) :
    2 * Real.log n ≤ Real.log j ∧ Real.log j ≤ 3 * Real.log n := by
  obtain ⟨hj, hsq, _⟩ := selection_scale_estimates hn ht hlo hhi
  have hn0 : 0 < n := by linarith
  constructor
  · have hh := Real.log_le_log (sq_pos_of_pos hn0) hsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  · have hhalf := log_le_half_of_pos hn0
    have hcubic : j ≤ n ^ 3 := by
      have hh := mul_le_mul_of_nonneg_left hhalf (sq_nonneg n)
      nlinarith [pow_nonneg hn0.le 3]
    have hh := Real.log_le_log hj hcubic
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh

theorem selected_scale_middle_window {n : ℝ} {j : ℕ} (hn : 1 ≤ n)
    (ht : 256 ≤ Real.log n)
    (hlo : n ^ 2 * Real.log n / 3 ≤ (j : ℝ))
    (hhi : (j : ℝ) ≤ 3 * n ^ 2 * Real.log n / 2) :
    Real.log j ≤ n ∧ 8 * n ^ 2 ≤ (j : ℝ) ∧
      n ^ 2 ≤ highParticleThreshold j ∧
      n / Real.sqrt ((j : ℝ) + 1) ≤ 3 / Real.sqrt (Real.log j) := by
  obtain ⟨hj, hsq, _⟩ := selection_scale_estimates hn ht hlo hhi
  obtain ⟨hloglo, hloghi⟩ := selected_scale_log_range hn ht hlo hhi
  have hn0 : 0 < n := by linarith
  have hlogj : 0 < Real.log j := by linarith
  have hlogn : 0 < Real.log n := by linarith
  have hn512 : 512 ≤ n := by have hh := log_le_half_of_pos hn0; linarith
  have hsN : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsN2 := Real.sq_sqrt hn0.le
  have hlogroot : Real.log n ≤ Real.sqrt n := by
    have hh := log_le_half_of_pos hsN
    rw [Real.log_sqrt hn0.le] at hh
    linarith
  have hroot : 3 * Real.sqrt n ≤ n := by nlinarith
  have hwindowlow : Real.log j ≤ n := by linarith
  have hwindow8 : 8 * n ^ 2 ≤ (j : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left ht (sq_nonneg n)
    nlinarith
  have hslog : 0 < Real.sqrt (Real.log j) := Real.sqrt_pos.mpr hlogj
  have hslog2 := Real.sq_sqrt hlogj.le
  have hlogsqrt : Real.sqrt (Real.log j) ≤ Real.log n / 3 := by nlinarith
  have hwindowhigh : n ^ 2 ≤ highParticleThreshold j := by
    unfold highParticleThreshold
    apply (le_div_iff₀ hslog).mpr
    have hh := mul_le_mul_of_nonneg_left hlogsqrt (sq_nonneg n)
    nlinarith
  have hprod : n ^ 2 * Real.log j ≤ 9 * (j : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hloghi (sq_nonneg n)
    nlinarith
  have hsj : 0 < Real.sqrt ((j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hsj2 := Real.sq_sqrt (show 0 ≤ (j : ℝ) + 1 by positivity)
  have hquot : n / Real.sqrt ((j : ℝ) + 1) ≤ 3 / Real.sqrt (Real.log j) := by
    apply (div_le_div_iff₀ hsj hslog).mpr
    apply (sq_le_sq₀ (mul_nonneg hn0.le hslog.le) (by positivity)).mp
    rw [mul_pow, mul_pow, hslog2, hsj2]
    nlinarith
  exact ⟨hwindowlow, hwindow8, hwindowhigh, hquot⟩

theorem middle_window_curvature_upper_gate {n : ℝ} {j : ℕ}
    (ht : 64 ≤ Real.log j) (hhigh : n ^ 2 ≤ highParticleThreshold j) :
    8 * n ^ 2 ≤ (j : ℝ) := by
  have ht0 : 0 < Real.log j := by linarith
  have hs := Real.sqrt_pos.mpr ht0
  have hs2 := Real.sq_sqrt ht0.le
  have hs8 : 8 ≤ Real.sqrt (Real.log j) := by nlinarith
  have hh := (le_div_iff₀ hs).mp hhigh
  have hm := mul_le_mul_of_nonneg_left hs8 (sq_nonneg n)
  linarith

end
end IsingBulk.AnisoF002.NegativeHT
