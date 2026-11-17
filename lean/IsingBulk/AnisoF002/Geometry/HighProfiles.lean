import IsingBulk.AnisoF002.Geometry.ProfileBounds

/-!
# The central HT lens profile and its two tips

F002 `eq:Hdef`, `eq:domains`, and `thm:components`.
The width is exactly pi/(2 max(1,lam)); both physical cosines are strictly
positive in its open strip.  The profile is positive there, vanishes at
both tips, and increases under contraction towards the central line.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open Set

theorem highStripWidth_bounds {lam : ℝ} (_hlam : 0 < lam) :
    0 < highStripWidthF002 lam ∧ highStripWidthF002 lam ≤ Real.pi / 2 ∧
      lam * highStripWidthF002 lam ≤ Real.pi / 2 := by
  have hm : 0 < max (1 : ℝ) lam := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hY : 0 < highStripWidthF002 lam := by
    unfold highStripWidthF002
    exact div_pos Real.pi_pos (mul_pos (by norm_num) hm)
  have hYeq : 2 * max (1 : ℝ) lam * highStripWidthF002 lam = Real.pi := by
    unfold highStripWidthF002
    exact mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num) hm))
  have h1 := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) lam) hY.le
  have h2 := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) lam) hY.le
  exact ⟨hY, by nlinarith, by nlinarith⟩

theorem high_strip_cosines_pos {lam y : ℝ} (hlam : 0 < lam)
    (hy : |y| < highStripWidthF002 lam) : 0 < Real.cos y ∧ 0 < Real.cos (lam * y) := by
  have hb := highStripWidth_bounds hlam
  have hy1 : |y| < Real.pi / 2 := lt_of_lt_of_le hy hb.2.1
  have hy2 : |lam * y| < Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hlam]
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hy hlam) hb.2.2
  exact ⟨Real.cos_pos_of_mem_Ioo (abs_lt.mp hy1), Real.cos_pos_of_mem_Ioo (abs_lt.mp hy2)⟩

theorem highProfile_pos {lam y : ℝ} (hlam : 0 < lam)
    (hy : |y| < highStripWidthF002 lam) : 0 < highProfileF002 lam y := by
  obtain ⟨hc1, hc2⟩ := high_strip_cosines_pos hlam hy
  have hp := profilePInv_strictMono hlam hc1
  have hq := profileQInv_strictMono hlam hc2
  rw [profilePInv_zero hlam] at hp
  rw [profileQInv_zero hlam] at hq
  exact lt_min hp hq

theorem highProfile_neg (lam y : ℝ) : highProfileF002 lam (-y) = highProfileF002 lam y := by
  unfold highProfileF002
  rw [Real.cos_neg, mul_neg, Real.cos_neg]

theorem highProfile_abs (lam y : ℝ) : highProfileF002 lam |y| = highProfileF002 lam y := by
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg (lt_of_not_ge hy), highProfile_neg]

theorem highProfile_width_zero {lam : ℝ} (hlam : 0 < lam) :
    highProfileF002 lam (highStripWidthF002 lam) = 0 := by
  have hb := highStripWidth_bounds hlam
  by_cases hl : lam ≤ 1
  · have hY : highStripWidthF002 lam = Real.pi / 2 := by
      simp only [highStripWidthF002, max_eq_left hl, mul_one]
    have hcos : Real.cos (highStripWidthF002 lam) = 0 := by rw [hY, Real.cos_pi_div_two]
    have hcos2 : 0 ≤ Real.cos (lam * highStripWidthF002 lam) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [mul_pos hlam hb.1, Real.pi_pos], hb.2.2⟩
    rw [highProfileF002, hcos, profilePInv_zero hlam]
    exact min_eq_left (profileQInv_nonneg hlam hcos2)
  · have hl' : 1 ≤ lam := le_of_not_ge hl
    have hY : lam * highStripWidthF002 lam = Real.pi / 2 := by
      unfold highStripWidthF002
      rw [max_eq_right hl']
      field_simp
    have hcos : Real.cos (lam * highStripWidthF002 lam) = 0 := by rw [hY, Real.cos_pi_div_two]
    have hcos1 : 0 ≤ Real.cos (highStripWidthF002 lam) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], hb.2.1⟩
    rw [highProfileF002, hcos, profileQInv_zero hlam]
    exact min_eq_right (profilePInv_nonneg hlam hcos1)

theorem highProfile_tip_zero {lam y : ℝ} (hlam : 0 < lam)
    (hy : |y| = highStripWidthF002 lam) : highProfileF002 lam y = 0 := by
  rw [← highProfile_abs lam y, hy, highProfile_width_zero hlam]

theorem high_tip_cosine_zero {lam y : ℝ} (hlam : 0 < lam)
    (hy : |y| = highStripWidthF002 lam) : Real.cos y = 0 ∨ Real.cos (lam * y) = 0 := by
  by_cases hl : lam ≤ 1
  · left
    rw [← Real.cos_abs y, hy]
    simp only [highStripWidthF002, max_eq_left hl, mul_one, Real.cos_pi_div_two]
  · right
    have hY : lam * highStripWidthF002 lam = Real.pi / 2 := by
      unfold highStripWidthF002
      rw [max_eq_right (le_of_not_ge hl)]
      field_simp
    rw [← Real.cos_abs (lam * y), abs_mul, abs_of_pos hlam, hy, hY, Real.cos_pi_div_two]

theorem real_cos_contraction_f002 {a y : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hy : |y| ≤ Real.pi) : Real.cos y ≤ Real.cos (a * y) := by
  have hh : |a * y| ≤ |y| := by
    rw [abs_mul, abs_of_nonneg ha]
    nlinarith [abs_nonneg y]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (a * y)) hy hh
  simpa only [Real.cos_abs] using hcos

theorem highProfile_contraction {lam a y : ℝ} (hlam : 0 < lam)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hy : |y| ≤ highStripWidthF002 lam) :
    highProfileF002 lam y ≤ highProfileF002 lam (a * y) := by
  have hb := highStripWidth_bounds hlam
  have hy1 : |y| ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hy2 : |lam * y| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos hlam]
    have hh := mul_le_mul_of_nonneg_left hy hlam.le
    nlinarith [Real.pi_pos]
  have hc1 := real_cos_contraction_f002 ha ha1 hy1
  have hc2 := real_cos_contraction_f002 ha ha1 hy2
  have heq : a * (lam * y) = lam * (a * y) := by ring
  rw [heq] at hc2
  exact min_le_min ((profilePInv_strictMono hlam).monotone hc1)
    ((profileQInv_strictMono hlam).monotone hc2)

end
end IsingBulk.AnisoF002.Geometry
