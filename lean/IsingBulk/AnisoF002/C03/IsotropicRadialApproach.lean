import IsingBulk.AnisoF002.C03.IsotropicInitialAmplitude

/-!
# The actual exterior radial parameter in frozen F002

The path is exactly t_e = (1+e) exp(i alpha), S_e = t_e+t_e^{-1}.
Its positive imaginary displacement and quadratic real displacement are
proved quantitatively. These bounds justify the branch-scale approach;
they are not asserted for arbitrary points of the upper half-plane.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

def isotropicExteriorRadial (α ε : ℝ) : ℂ :=
  ((1 + ε : ℝ) : ℂ) * Complex.exp ((α : ℂ) * Complex.I)

def isotropicRadialParameter (α ε : ℝ) : ℂ :=
  isotropicExteriorRadial α ε + (isotropicExteriorRadial α ε)⁻¹

theorem isotropicExteriorRadial_norm (α ε : ℝ) :
    ‖isotropicExteriorRadial α ε‖ = |1 + ε| := by
  rw [isotropicExteriorRadial, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

theorem isotropicExteriorRadial_exterior (α ε : ℝ) (hε : 0 < ε) :
    1 < ‖isotropicExteriorRadial α ε‖ := by
  rw [isotropicExteriorRadial_norm, abs_of_pos (by linarith : 0 < 1 + ε)]
  linarith

theorem isotropicRadialParameter_formula (α ε : ℝ) :
    isotropicRadialParameter α ε =
      (((1 + ε) + (1 + ε)⁻¹) * Real.cos α : ℝ) +
        ((((1 + ε) - (1 + ε)⁻¹) * Real.sin α : ℝ) : ℂ) * Complex.I := by
  have hinv : (Complex.exp ((α : ℂ) * Complex.I))⁻¹ =
      (Real.cos α : ℂ) - (Real.sin α : ℂ) * Complex.I := by
    rw [← Complex.exp_neg, show -((α : ℂ) * Complex.I) = (-α : ℂ) * Complex.I by ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, neg_mul, sub_eq_add_neg]
  unfold isotropicRadialParameter isotropicExteriorRadial
  rw [mul_inv_rev, hinv, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_inv]
  push_cast
  ring

theorem isotropicRadialParameter_re (α ε : ℝ) :
    (isotropicRadialParameter α ε).re = ((1 + ε) + (1 + ε)⁻¹) * Real.cos α := by
  rw [isotropicRadialParameter_formula]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem isotropicRadialParameter_im (α ε : ℝ) :
    (isotropicRadialParameter α ε).im = ((1 + ε) - (1 + ε)⁻¹) * Real.sin α := by
  rw [isotropicRadialParameter_formula]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

theorem isotropicRadialParameter_real_shift (α ε : ℝ) (hε : 1 + ε ≠ 0) :
    (isotropicRadialParameter α ε).re - 2 * Real.cos α =
      Real.cos α * ε ^ 2 / (1 + ε) := by
  rw [isotropicRadialParameter_re]
  field_simp
  ring

theorem isotropicRadialParameter_im_shift (α ε : ℝ) (hε : 1 + ε ≠ 0) :
    (isotropicRadialParameter α ε).im =
      Real.sin α * ε * (2 + ε) / (1 + ε) := by
  rw [isotropicRadialParameter_im]
  field_simp
  ring

/-- Exact radial control, including the quadratic real displacement
needed at the lower branch. The upper bound is uniform in alpha. -/
theorem isotropicRadialParameter_estimates (α ε : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.sin α * ε ≤ (isotropicRadialParameter α ε).im ∧
      (isotropicRadialParameter α ε).im ≤ 3 * ε ∧
      |(isotropicRadialParameter α ε).re - 2 * Real.cos α| ≤ ε ^ 2 ∧
      0 < (isotropicRadialParameter α ε).im ∧
      dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) ≤ 4 * ε := by
  have hsin : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hr : 0 < 1 + ε := by linarith
  have hratioL : (1 : ℝ) ≤ (2 + ε) / (1 + ε) := by
    apply (le_div_iff₀ hr).mpr
    linarith
  have hratioU : (2 + ε) / (1 + ε) ≤ 3 := by
    apply (div_le_iff₀ hr).mpr
    linarith
  have hi : (isotropicRadialParameter α ε).im = Real.sin α * ε * ((2 + ε) / (1 + ε)) := by
    rw [isotropicRadialParameter_im_shift α ε hr.ne']
    ring
  have hlow : Real.sin α * ε ≤ (isotropicRadialParameter α ε).im := by
    rw [hi]
    exact le_mul_of_one_le_right (mul_nonneg hsin.le hε.le) hratioL
  have hupp : (isotropicRadialParameter α ε).im ≤ 3 * ε := by
    rw [hi]
    have hm : Real.sin α * ε ≤ ε := by nlinarith [Real.sin_le_one α]
    have hh := mul_le_mul hm hratioU (by positivity : (0 : ℝ) ≤ (2 + ε) / (1 + ε)) hε.le
    nlinarith
  have hre : |(isotropicRadialParameter α ε).re - 2 * Real.cos α| ≤ ε ^ 2 := by
    rw [isotropicRadialParameter_real_shift α ε hr.ne', abs_div, abs_mul,
      abs_of_nonneg (sq_nonneg ε), abs_of_pos hr]
    apply (div_le_iff₀ hr).mpr
    have hc := Real.abs_cos_le_one α
    nlinarith [sq_nonneg ε, mul_nonneg hε.le (sq_nonneg ε)]
  have him : 0 < (isotropicRadialParameter α ε).im := (mul_pos hsin hε).trans_le hlow
  refine ⟨hlow, hupp, hre, him, ?_⟩
  rw [dist_eq_norm]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [abs_of_pos him]
  nlinarith

end IsingBulk.AnisoF002.Isotropic
