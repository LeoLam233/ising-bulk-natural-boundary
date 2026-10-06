import IsingBulk.First.BulkSymmetry

/-! The physical exterior is covered by upper, lower, right and left trace
charts. No branch continuation is postulated. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

theorem real_trace_gt_two {a : ℝ} (ha : 1 < a) : 2 < a+a⁻¹ := by
  have hp : 0 < a := by linarith
  have he : a+a⁻¹ = (a^2+1)/a := by field_simp
  rw [he, lt_div_iff₀ hp]
  nlinarith [sq_pos_of_pos (show 0 < a-1 by linarith)]

theorem exterior_trace_charts {s : ℂ} (hs : 1 < ‖s‖) :
    0 < (sourceS s).im ∨ (sourceS s).im < 0 ∨
      2 < (sourceS s).re ∨ (sourceS s).re < -2 := by
  rcases lt_trichotomy 0 (sourceS s).im with h | h | h
  · exact Or.inl h
  · have hn : 1 < Complex.normSq s := Complex.one_lt_normSq_iff.mpr hs
    have hi : s.im = 0 := by
      have hh : s.im-s.im/Complex.normSq s = 0 := by
        simpa only [sourceS, Complex.add_im, Complex.inv_im, neg_div,
          ← sub_eq_add_neg] using h.symm
      have hh' := (div_eq_iff (by linarith : Complex.normSq s ≠ 0)).mp
        (show s.im/Complex.normSq s = s.im by linarith)
      have hf : s.im*(Complex.normSq s-1)=0 := by nlinarith
      exact (mul_eq_zero.mp hf).resolve_right (by linarith)
    have he : s = (s.re:ℂ) := by apply Complex.ext <;> simp [hi]
    have hnorm : ‖s‖ = |s.re| := by
      conv_lhs => rw [he]
      simp
    have hnre : 1 < |s.re| := by rwa [hnorm] at hs
    have ht : (sourceS s).re = s.re+(s.re)⁻¹ := by
      conv_lhs => rw [he]
      simp [sourceS]
    rcases (lt_abs.mp hnre) with hp | hn
    · exact Or.inr (Or.inr (Or.inl (ht ▸ real_trace_gt_two hp)))
    · have hb := real_trace_gt_two (show 1 < -s.re by linarith)
      simp only [inv_neg] at hb
      exact Or.inr (Or.inr (Or.inr (by rw [ht]; linarith)))
  · exact Or.inr (Or.inl h)

end
end IsingBulk.Tail
