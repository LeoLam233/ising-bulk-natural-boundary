import IsingBulk.AnisoF002.C03.RegularModelElementaryJets

/-!
# Quantitative centered logarithmic differences at the actual particle center

The complex disk stays in the principal logarithm's slit plane.  Exact
third-order Taylor cancellation gives the O(d^4/x^4) curvature remainder,
which is needed after multiplication by the derivative order.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set
open scoped Topology

theorem model_log_disk_geometry {x : ℝ} (hx : 0 < x) {z : ℂ}
    (hz : z ∈ Metric.closedBall (x : ℂ) (x / 2)) :
    z ∈ Complex.slitPlane ∧ ‖z⁻¹‖ ≤ 2 / x := by
  have hd : ‖z - (x : ℂ)‖ ≤ x / 2 := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
  have hre := Complex.re_le_norm ((x : ℂ) - z)
  rw [Complex.sub_re, Complex.ofReal_re, norm_sub_rev] at hre
  have hn := norm_sub_norm_le (x : ℂ) z
  rw [Complex.norm_real, Real.norm_of_nonneg hx.le, norm_sub_rev] at hn
  refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith)), ?_⟩
  rw [norm_inv]
  have hh := one_div_le_one_div_of_le (half_pos hx) (show x / 2 ≤ ‖z‖ by linarith)
  simpa only [one_div, inv_div] using hh

theorem model_centered_disk_points {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) (hstep : d ≤ x / 4) :
    (x : ℂ) ∈ Metric.closedBall (x : ℂ) (x / 2) ∧
      (x : ℂ) + d ∈ Metric.closedBall (x : ℂ) (x / 2) ∧
      (x : ℂ) - d ∈ Metric.closedBall (x : ℂ) (x / 2) := by
  refine ⟨Metric.mem_closedBall_self (half_pos hx).le, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hd]
    linarith
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hd]
    linarith

theorem model_log_centered_precise {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) (hstep : d ≤ x / 4) :
    |Real.log (x + d) - Real.log (x - d) - 2 * d / x| ≤
        2 / (3 * x ^ 3) * d ^ 3 + 192 * d ^ 4 / x ^ 4 ∧
      |Real.log (x + d) - 2 * Real.log x + Real.log (x - d) + d ^ 2 / x ^ 2| ≤
        192 * d ^ 4 / x ^ 4 := by
  have hgeom {z : ℂ} (hz : z ∈ Metric.closedBall (x : ℂ) (x / 2)) := model_log_disk_geometry hx hz
  have ha : AnalyticOnNhd ℂ Complex.log (Metric.closedBall (x : ℂ) (x / 2)) :=
    fun z hz => analyticAt_id.clog (hgeom hz).1
  have hfour (z : ℂ) (hz : z ∈ Metric.closedBall (x : ℂ) (x / 2)) :
      ‖deriv (deriv (deriv (deriv Complex.log))) z‖ ≤ 96 / x ^ 4 := by
    rw [(model_log_first_four_derivatives (hgeom hz).1).2.2.2, norm_mul, norm_neg,
      norm_pow, Complex.norm_ofNat]
    calc
      6 * ‖z⁻¹‖ ^ 4 ≤ 6 * (2 / x) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hgeom hz).2 4) (by norm_num)
      _ = _ := by ring
  obtain ⟨hc, hp, hm⟩ := model_centered_disk_points hx hd hstep
  have hh := centered_third_taylor_bounds (convex_closedBall (x : ℂ) (x / 2)) ha hc hp hm
    (show 0 ≤ 96 / x ^ 4 by positivity) hfour
  have hder := model_log_first_four_derivatives (Complex.ofReal_mem_slitPlane.mpr hx)
  have hnorm : ‖((x : ℂ)⁻¹)‖ = x⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hx.le]
  rw [hder.1, hder.2.1, hder.2.2.1] at hh
  simp only [norm_mul, norm_pow, Complex.norm_ofNat, hnorm, Complex.norm_real,
    Real.norm_of_nonneg hd] at hh
  have hpR := (Complex.abs_re_le_norm
    (Complex.log ((x : ℂ) + d) - Complex.log ((x : ℂ) - d) - 2 * (x : ℂ)⁻¹ * d)).trans hh.1
  have hmR := (Complex.abs_re_le_norm
    (Complex.log ((x : ℂ) + d) - 2 * Complex.log (x : ℂ) + Complex.log ((x : ℂ) - d) -
      (-((x : ℂ)⁻¹ ^ 2)) * (d : ℂ) ^ 2)).trans hh.2
  have hre1 : (Complex.log ((x : ℂ) + d) - Complex.log ((x : ℂ) - d) - 2 * (x : ℂ)⁻¹ * d).re =
      Real.log (x + d) - Real.log (x - d) - 2 * d / x := by
    rw [← Complex.ofReal_add, ← Complex.ofReal_sub]
    simp only [Complex.sub_re, Complex.log_ofReal_re]
    have hc' : 2 * (x : ℂ)⁻¹ * d = (2 * d / x : ℝ) := by push_cast; ring
    rw [hc', Complex.ofReal_re]
  have hre2 : (Complex.log ((x : ℂ) + d) - 2 * Complex.log (x : ℂ) + Complex.log ((x : ℂ) - d) -
      (-((x : ℂ)⁻¹ ^ 2)) * (d : ℂ) ^ 2).re =
      Real.log (x + d) - 2 * Real.log x + Real.log (x - d) + d ^ 2 / x ^ 2 := by
    rw [← Complex.ofReal_add, ← Complex.ofReal_sub]
    have hc' : (-((x : ℂ)⁻¹ ^ 2)) * (d : ℂ) ^ 2 = (-(d ^ 2 / x ^ 2) : ℝ) := by push_cast; ring
    rw [hc']
    norm_num only [Complex.sub_re, Complex.add_re, Complex.log_ofReal_re, Complex.mul_re,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, Complex.ofReal_re]
    ring
  rw [hre1] at hpR
  rw [hre2] at hmR
  constructor
  · convert hpR using 1
    ring
  · convert hmR using 1
    ring

theorem model_log_centered_bounds {x d : ℝ} (hx : 0 < x) (hd : 0 ≤ d) (hstep : d ≤ x / 4) :
    |Real.log (x + d) - Real.log (x - d) - 2 * d / x| ≤ 50 * d ^ 3 / x ^ 3 ∧
      |Real.log (x + d) - 2 * Real.log x + Real.log (x - d) + d ^ 2 / x ^ 2| ≤
        192 * d ^ 4 / x ^ 4 := by
  have hh := model_log_centered_precise hx hd hstep
  refine ⟨hh.1.trans ?_, hh.2⟩
  apply (le_div_iff₀ (pow_pos hx 3)).mpr
  have h : d / x ≤ 1 / 4 := (div_le_iff₀ hx).mpr (by linarith)
  have he : (2 / (3 * x ^ 3) * d ^ 3 + 192 * d ^ 4 / x ^ 4) * x ^ 3 =
      (2 / 3 + 192 * (d / x)) * d ^ 3 := by field_simp
  rw [he]
  have hb : 2 / 3 + 192 * (d / x) ≤ (50 : ℝ) := by linarith
  exact mul_le_mul_of_nonneg_right hb (pow_nonneg hd 3)

end
end IsingBulk.AnisoF002.NegativeHT
