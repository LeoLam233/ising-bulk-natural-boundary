import IsingBulk.AnisoF002.C03.RegularModelElementaryBounds

/-!
# The centered polynomial-logarithm factor

The leading log(x) pieces are retained explicitly so that they cancel
against the finite factorial product, instead of producing a spurious
logarithmic error in the curvature estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set
open scoped Topology

def realModelElementary (x : ℝ) : ℝ := (-x ^ 2 / 2 + 1) * Real.log x

theorem modelElementary_re (x : ℝ) :
    (modelElementary (x : ℂ)).re = realModelElementary x := by
  have hc : (-(x : ℂ) ^ 2 / 2 + 1) = (-x ^ 2 / 2 + 1 : ℝ) := by push_cast; rfl
  rw [modelElementary, hc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.log_ofReal_re,
    realModelElementary]

theorem modelElementaryFirst_re (x : ℝ) :
    (modelElementaryFirst (x : ℂ)).re = -x * Real.log x - x / 2 + x⁻¹ := by
  have hc : (x : ℂ) / 2 = (x / 2 : ℝ) := by push_cast; rfl
  rw [modelElementaryFirst, hc, ← Complex.ofReal_inv]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.log_ofReal_re]

theorem modelElementarySecond_re (x : ℝ) :
    (modelElementarySecond (x : ℂ)).re = -Real.log x - 3 / 2 - x⁻¹ ^ 2 := by
  have hc : (3 : ℂ) / 2 = (3 / 2 : ℝ) := by push_cast; rfl
  have hi : (x : ℂ)⁻¹ ^ 2 = (x⁻¹ ^ 2 : ℝ) := by push_cast; rfl
  rw [modelElementarySecond, hc, hi]
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.log_ofReal_re]

theorem modelElementary_centered_bounds {x d : ℝ} (hx : 1 ≤ x) (hd : 0 ≤ d) (hstep : d ≤ x / 4) :
    |realModelElementary (x + d) - realModelElementary (x - d) + 2 * d * x * Real.log x| ≤
        (3 * d + d ^ 3 + 200 * d ^ 4) * x ∧
      |realModelElementary (x + d) - 2 * realModelElementary x + realModelElementary (x - d) +
        d ^ 2 * Real.log x| ≤ 3 * d ^ 2 + 200 * d ^ 4 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hgeom {z : ℂ} (hz : z ∈ Metric.closedBall (x : ℂ) (x / 2)) := model_log_disk_geometry hx0 hz
  have ha : AnalyticOnNhd ℂ modelElementary (Metric.closedBall (x : ℂ) (x / 2)) := by
    intro z hz
    exact ((((analyticAt_id.pow 2).neg.div_const).add analyticAt_const).mul
      (analyticAt_id.clog (hgeom hz).1))
  have hfour (z : ℂ) (hz : z ∈ Metric.closedBall (x : ℂ) (x / 2)) :
      ‖deriv (deriv (deriv (deriv modelElementary))) z‖ ≤ 100 := by
    rw [(modelElementary_first_four_derivatives (hgeom hz).1).2.2.2, modelElementaryFourth]
    have hi : ‖z⁻¹‖ ≤ 2 := (hgeom hz).2.trans (div_le_self (by norm_num) hx)
    calc
      _ ≤ ‖z⁻¹ ^ 2‖ + ‖6 * z⁻¹ ^ 4‖ := norm_sub_le _ _
      _ = ‖z⁻¹‖ ^ 2 + 6 * ‖z⁻¹‖ ^ 4 := by rw [norm_pow, norm_mul, norm_pow, Complex.norm_ofNat]
      _ ≤ 100 := by
        have h2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
        have h4 := pow_le_pow_left₀ (norm_nonneg _) hi 4
        norm_num only [Nat.reducePow] at h2 h4
        linarith
  have hxn : ‖((x : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hthird : ‖modelElementaryThird (x : ℂ)‖ ≤ 3 := by
    rw [modelElementaryThird]
    calc
      _ ≤ ‖-((x : ℂ)⁻¹)‖ + ‖2 * (x : ℂ)⁻¹ ^ 3‖ := norm_add_le _ _
      _ = ‖((x : ℂ)⁻¹)‖ + 2 * ‖((x : ℂ)⁻¹)‖ ^ 3 := by
        rw [norm_neg, norm_mul, norm_pow, Complex.norm_ofNat]
      _ ≤ 3 := by
        have h3 := pow_le_pow_left₀ (norm_nonneg _) hxn 3
        norm_num only [one_pow] at h3
        linarith
  obtain ⟨hc, hp, hm⟩ := model_centered_disk_points hx0 hd hstep
  have hh := centered_third_taylor_bounds (convex_closedBall (x : ℂ) (x / 2)) ha hc hp hm
    (by norm_num : (0 : ℝ) ≤ 100) hfour
  have hder := modelElementary_first_four_derivatives (Complex.ofReal_mem_slitPlane.mpr hx0)
  rw [hder.1, hder.2.1, hder.2.2.1] at hh
  simp only [Complex.norm_real, Real.norm_of_nonneg hd] at hh
  have hR1 : |realModelElementary (x + d) - realModelElementary (x - d) -
      2 * (-x * Real.log x - x / 2 + x⁻¹) * d| ≤ d ^ 3 + 200 * d ^ 4 := by
    have h := (Complex.abs_re_le_norm
      (modelElementary ((x : ℂ) + d) - modelElementary ((x : ℂ) - d) -
        2 * modelElementaryFirst x * d)).trans hh.1
    have he : (2 * modelElementaryFirst (x : ℂ) * (d : ℂ)).re =
        2 * (-x * Real.log x - x / 2 + x⁻¹) * d := by
      norm_num only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
        zero_mul, zero_sub, mul_zero, sub_zero, Complex.ofReal_re, Complex.ofReal_im]
      rw [modelElementaryFirst_re]
    rw [Complex.sub_re, Complex.sub_re, ← Complex.ofReal_add, ← Complex.ofReal_sub,
      modelElementary_re, modelElementary_re, he] at h
    apply h.trans
    have hc' : ‖modelElementaryThird (x : ℂ)‖ / 3 ≤ 1 := by linarith
    have hm' := mul_le_mul_of_nonneg_right hc' (pow_nonneg hd 3)
    linarith
  have hR2 : |realModelElementary (x + d) - 2 * realModelElementary x + realModelElementary (x - d) -
      (-Real.log x - 3 / 2 - x⁻¹ ^ 2) * d ^ 2| ≤ 200 * d ^ 4 := by
    have h := (Complex.abs_re_le_norm
      (modelElementary ((x : ℂ) + d) - 2 * modelElementary x + modelElementary ((x : ℂ) - d) -
        modelElementarySecond x * (d : ℂ) ^ 2)).trans hh.2
    have he : (modelElementarySecond (x : ℂ) * (d : ℂ) ^ 2).re =
        (-Real.log x - 3 / 2 - x⁻¹ ^ 2) * d ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, modelElementarySecond_re]
    rw [Complex.sub_re, he] at h
    rw [← Complex.ofReal_add, ← Complex.ofReal_sub] at h
    norm_num only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, modelElementary_re] at h
    convert h using 1
  have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hi1 : x⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hx
  have hf1 : |-x / 2 + x⁻¹| ≤ 3 * x / 2 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hf2 : |-3 / 2 - x⁻¹ ^ 2| ≤ 3 := by
    have hsq : x⁻¹ ^ 2 ≤ 1 := by nlinarith
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x⁻¹]
  constructor
  · calc
      _ = |(realModelElementary (x + d) - realModelElementary (x - d) -
          2 * (-x * Real.log x - x / 2 + x⁻¹) * d) + 2 * d * (-x / 2 + x⁻¹)| := by congr 1; ring
      _ ≤ |realModelElementary (x + d) - realModelElementary (x - d) -
          2 * (-x * Real.log x - x / 2 + x⁻¹) * d| + |2 * d * (-x / 2 + x⁻¹)| := abs_add_le _ _
      _ ≤ d ^ 3 + 200 * d ^ 4 + (2 * d) * (3 * x / 2) := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * d)]
        exact add_le_add hR1 (mul_le_mul_of_nonneg_left hf1 (by positivity))
      _ ≤ (3 * d + d ^ 3 + 200 * d ^ 4) * x := by
        have h := le_mul_of_one_le_right (show 0 ≤ d ^ 3 + 200 * d ^ 4 by positivity) hx
        nlinarith
  · calc
      _ = |(realModelElementary (x + d) - 2 * realModelElementary x + realModelElementary (x - d) -
          (-Real.log x - 3 / 2 - x⁻¹ ^ 2) * d ^ 2) + (-3 / 2 - x⁻¹ ^ 2) * d ^ 2| := by congr 1; ring
      _ ≤ |realModelElementary (x + d) - 2 * realModelElementary x + realModelElementary (x - d) -
          (-Real.log x - 3 / 2 - x⁻¹ ^ 2) * d ^ 2| + |(-3 / 2 - x⁻¹ ^ 2) * d ^ 2| := abs_add_le _ _
      _ ≤ 200 * d ^ 4 + 3 * d ^ 2 := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg d)]
        exact add_le_add hR2 (mul_le_mul_of_nonneg_right hf2 (sq_nonneg d))
      _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
