import IsingBulk.AnisoF002.C03.IsotropicPhysicalCurvature

/-!
# Quantitative oblique positivity of the reciprocal cubic phase sine

The sector estimate is converted into a strict quantitative projection.
The argument is polynomial and remains valid on a fixed enlargement
of the limiting branch sector. It is the scalar denominator step in
the genuine physical phase curvature estimate.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology

theorem enlarged_sector_cubic_numerator {x y a b : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ (11 / 10 : ℝ) * x)
    (ha : 0 ≤ a) (hab : 2 * a ≤ b) :
    a * x ^ 3 ≤ a * (x ^ 3 - 3 * x * y ^ 2) + b * (3 * x ^ 2 * y - y ^ 3) := by
  have hxy := mul_le_mul_of_nonneg_left hyx hx
  have hyy := pow_le_pow_left₀ hy hyx 2
  have him : 0 ≤ 3 * x ^ 2 - y ^ 2 := by nlinarith only [hyy, sq_nonneg x]
  have hrem : 0 ≤ 6 * x ^ 2 - 3 * x * y - 2 * y ^ 2 := by
    nlinarith only [hxy, hyy, sq_nonneg x]
  have hterm : 0 ≤ 3 * x ^ 2 * y - y ^ 3 := by
    nlinarith only [mul_nonneg hy him]
  have hbterm := mul_le_mul_of_nonneg_right hab hterm
  have harem := mul_nonneg (mul_nonneg ha hy) hrem
  nlinarith only [hbterm, harem]

theorem oblique_reciprocal_cube_lower (z : ℂ) (a b : ℝ)
    (hx : 0 < z.re) (hy : z.im ≤ 0) (hyx : -z.im ≤ (11 / 10 : ℝ) * z.re)
    (ha : 0 < a) (hab : 2 * a ≤ b) :
    a / (27 * ‖z‖ ^ 3) ≤ (((a : ℂ) - Complex.I * (b : ℂ)) / z ^ 3).re := by
  have hz : z ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hx; exact hx.false
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let x := z.re
  let y := -z.im
  let P := a * (x ^ 3 - 3 * x * y ^ 2) + b * (3 * x ^ 2 * y - y ^ 3)
  have hP : a * x ^ 3 ≤ P := enlarged_sector_cubic_numerator hx.le
    (neg_nonneg.mpr hy) hyx ha.le hab
  have hnorm : ‖z‖ ≤ 3 * x := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos hx, abs_of_nonpos hy] at hh
    dsimp [x]
    linarith only [hh, hyx, hx]
  have hcub : ‖z‖ ^ 3 ≤ 27 * x ^ 3 :=
    (pow_le_pow_left₀ (norm_nonneg z) hnorm 3).trans_eq (by ring)
  have hnum : a * ‖z‖ ^ 3 / 27 ≤ P := by
    have hh := mul_le_mul_of_nonneg_left hcub ha.le
    nlinarith only [hh, hP]
  have he : (((a : ℂ) - Complex.I * (b : ℂ)) / z ^ 3).re = P / (‖z‖ ^ 2) ^ 3 := by
    rw [Complex.div_re, Complex.normSq_eq_norm_sq, norm_pow]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.sub_im,
      Complex.mul_im, one_mul, zero_add, zero_sub]
    simp only [pow_succ, pow_zero, Complex.mul_re, Complex.mul_im]
    dsimp [P, x, y]
    ring
  rw [he]
  have hiden : a / (27 * ‖z‖ ^ 3) = (a * ‖z‖ ^ 3 / 27) / (‖z‖ ^ 2) ^ 3 := by
    field_simp
  rw [hiden]
  exact div_le_div_of_nonneg_right hnum (by positivity)

end IsingBulk.AnisoF002.Isotropic
