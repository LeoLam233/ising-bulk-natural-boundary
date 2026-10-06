import IsingBulk.First.GlobalResidueRoot

/-! Elementary local parameter control for the actual source trace S=s+s⁻¹. -/
namespace IsingBulk.First
noncomputable section

theorem sourceS_sub_norm_le {s t : ℂ} (hs : (1:ℝ)/2 ≤ ‖s‖) (ht : 1 ≤ ‖t‖) :
    ‖sourceS s-sourceS t‖ ≤ 3*‖s-t‖ := by
  have hs0 : s ≠ 0 := norm_pos_iff.mp (by linarith)
  have ht0 : t ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : s⁻¹-t⁻¹=(t-s)/(s*t) := by field_simp
  have hden : (1:ℝ)/2 ≤ ‖s‖*‖t‖ := by
    nlinarith [mul_nonneg (show 0 ≤ ‖s‖-1/2 by linarith) (show 0 ≤ ‖t‖-1 by linarith)]
  have hinv : ‖s⁻¹-t⁻¹‖ ≤ 2*‖s-t‖ := by
    rw [he, norm_div, norm_mul, norm_sub_rev]
    calc
      ‖s-t‖/(‖s‖*‖t‖) ≤ ‖s-t‖/((1:ℝ)/2) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
      _ = _ := by ring
  have hsplit : sourceS s-sourceS t=(s-t)+(s⁻¹-t⁻¹) := by unfold sourceS; ring
  rw [hsplit]
  exact (norm_add_le _ _).trans (by linarith)

theorem sourceS_im_lower {s t : ℂ} (hs : (1:ℝ)/2 ≤ ‖s‖) (ht : 1 ≤ ‖t‖) :
    (sourceS t).im-3*‖s-t‖ ≤ (sourceS s).im := by
  have hh := (abs_le.mp (Complex.abs_im_le_norm (sourceS s-sourceS t))).1
  have hb := sourceS_sub_norm_le hs ht
  simp only [Complex.sub_im] at hh
  linarith

theorem norm_ge_half_of_near_unit {s t : ℂ} (ht : 1 ≤ ‖t‖) (hst : ‖s-t‖ < (1:ℝ)/2) :
    (1:ℝ)/2 ≤ ‖s‖ := by
  have hh := norm_sub_norm_le t s
  rw [norm_sub_rev] at hh
  linarith

end
end IsingBulk.First
