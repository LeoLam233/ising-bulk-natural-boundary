import IsingBulk.Anisotropic.NegativeDominance.ResonanceScale

/-! An explicit relative logarithmic error, uniform down to zero angle.
This controls the exact tau factor without replacing tau by its leading term. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem log_sin_div_bounds {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ -Real.log (Real.sin x / x) ∧
      -Real.log (Real.sin x / x) ≤ x^2 / 5 := by
  have hx2 : x^2 ≤ 1 := by nlinarith
  have hsin := Real.sin_ge_sub_cube hx.le
  have hlo : 1 - x^2 / 6 ≤ Real.sin x / x := by
    apply (le_div_iff₀ hx).mpr
    nlinarith
  have hu : Real.sin x / x ≤ 1 := (div_le_one hx).mpr (Real.sin_le hx.le)
  have hpos : 0 < Real.sin x / x := by linarith
  have hmin : 5 / 6 ≤ Real.sin x / x := by linarith
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos hpos.le hu)
  · have hl := Real.one_sub_inv_le_log_of_pos hpos
    have he : (Real.sin x / x)⁻¹ - 1 = (1 - Real.sin x / x) / (Real.sin x / x) := by
      have hs : Real.sin x ≠ 0 := ((div_pos_iff_of_pos_right hx).mp hpos).ne'
      field_simp [hx.ne', hs]
    have hb : (1 - Real.sin x / x) / (Real.sin x / x) ≤ (x^2 / 6) / (5 / 6) := by
      apply div_le_div₀ (by linarith) (by linarith) (by norm_num) hmin
    have he' : (x^2 / 6) / (5 / 6) = x^2 / 5 := by ring
    rw [he'] at hb
    linarith

end
end IsingBulk.Anisotropic.NegativeDominance
