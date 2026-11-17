import IsingBulk.AnisoF002.C03.NegativeWindowScale

/-! # Exact logarithmic lower edge of the paper's negative-HT order window -/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem log_succ_le_double_bound {j : ℕ} {N : ℝ}
    (hj : 1 ≤ j) (hN : 1 ≤ N) (hlog : Real.log (j : ℝ) ≤ N) :
    Real.log ((j + 1 : ℕ) : ℝ) ≤ 2 * N := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by linarith
  have hle : ((j + 1 : ℕ) : ℝ) ≤ 2 * (j : ℝ) := by push_cast; linarith
  have hh := Real.log_le_log (show (0 : ℝ) < ((j + 1 : ℕ) : ℝ) by positivity) hle
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hj0.ne'] at hh
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem gaussian_radial_tail_le_double_log_scale {N k : ℝ}
    (hN : 4 ≤ N) (hk : 0 < k) (hlog : Real.log k ≤ 2 * N) :
    Real.exp (-N ^ 2 / 4) ≤ N / Real.sqrt k := by
  have hs := Real.sqrt_pos.mpr hk
  have he : -N ^ 2 / 4 ≤ -Real.log (Real.sqrt k) := by
    rw [Real.log_sqrt hk.le]
    nlinarith
  calc
    _ ≤ Real.exp (-Real.log (Real.sqrt k)) := Real.exp_le_exp.mpr he
    _ = 1 / Real.sqrt k := by rw [Real.exp_neg, Real.exp_log hs, one_div]
    _ ≤ N / Real.sqrt k := div_le_div_of_nonneg_right (by linarith) hs.le

end
end IsingBulk.AnisoF002.NegativeHT
