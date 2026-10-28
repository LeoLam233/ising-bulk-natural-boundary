import IsingBulk.Preferred22.SelectedKernelPerturbation

namespace IsingBulk.HT22.Selected

/-- Relative sheet continuation preserves an inverse-root bound. -/
theorem inverse_norm_of_relative {u v : ℂ} {K : ℝ} (hu : u≠0)
    (hK : ‖u⁻¹‖≤K) (hrel : ‖v/u-1‖≤(1/2:ℝ)) :
    v≠0 ∧ ‖v⁻¹‖≤2*K := by
  have hn := norm_sub_norm_le (1:ℂ) (v/u)
  rw [norm_one,norm_sub_rev] at hn
  have hr : (1/2:ℝ)≤‖v/u‖ := by linarith
  have hvu : v/u≠0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hr)
  have hv : v≠0 := (div_ne_zero_iff.mp hvu).1
  have hmul : v⁻¹=u⁻¹*(v/u)⁻¹ := by field_simp
  refine ⟨hv,?_⟩
  rw [hmul,norm_mul,norm_inv]
  have hi : ‖v/u‖⁻¹≤2 := by
    have hh := inv_anti₀ (by norm_num : (0:ℝ)<1/2) hr
    norm_num at hh ⊢
    exact hh
  simp only [norm_inv] at hK ⊢
  exact (mul_le_mul hK hi (by positivity) ((inv_nonneg.mpr (norm_nonneg u)).trans hK)).trans_eq (mul_comm _ _)

end IsingBulk.HT22.Selected
