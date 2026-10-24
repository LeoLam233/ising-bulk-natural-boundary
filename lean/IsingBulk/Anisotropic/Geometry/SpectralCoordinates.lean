import IsingBulk.Anisotropic.Geometry.RealGeometryAlgebra
import IsingBulk.Anisotropic.Geometry.IsotropicDensity

namespace IsingBulk.Anisotropic
noncomputable section

theorem spectralS_re (z : ℂ) : (spectralS z).re = Real.sinh z.re * Real.cos z.im := sinh_re_formula z
theorem spectralS_im (z : ℂ) : (spectralS z).im = Real.cosh z.re * Real.sin z.im := sinh_im_formula z

theorem spectralT_re (lam : ℝ) (z : ℂ) :
    (spectralT lam z).re = Real.sinh (lam*z.re) * Real.cos (lam*z.im) := by
  simp only [spectralT, sinh_re_formula, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]

theorem spectralT_im (lam : ℝ) (z : ℂ) :
    (spectralT lam z).im = Real.cosh (lam*z.re) * Real.sin (lam*z.im) := by
  simp only [spectralT, sinh_im_formula, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]

theorem spectralA_re (lam : ℝ) (z : ℂ) :
    (spectralA lam z).re = Real.cosh z.re * Real.cosh (lam*z.re) * Real.cos z.im * Real.cos (lam*z.im) -
      Real.sinh z.re * Real.sinh (lam*z.re) * Real.sin z.im * Real.sin (lam*z.im) := by
  simp only [spectralA, Complex.mul_re, cosh_re_formula, cosh_im_formula,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

theorem spectralA_im (lam : ℝ) (z : ℂ) :
    (spectralA lam z).im = Real.cosh z.re * Real.sinh (lam*z.re) * Real.cos z.im * Real.sin (lam*z.im) +
      Real.sinh z.re * Real.cosh (lam*z.re) * Real.sin z.im * Real.cos (lam*z.im) := by
  simp only [spectralA, Complex.mul_re, cosh_re_formula, cosh_im_formula,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

theorem spectralDet_formula (lam : ℝ) (z : ℂ) :
    spectralDet lam z =
      Real.sinh z.re * Real.cosh (lam*z.re) * Real.cos z.im * Real.sin (lam*z.im) -
      Real.cosh z.re * Real.sinh (lam*z.re) * Real.sin z.im * Real.cos (lam*z.im) := by
  simp only [spectralDet, spectralS_re, spectralS_im, spectralT_re, spectralT_im]
  ring

theorem spectralNU_formula (lam : ℝ) (z : ℂ) :
    spectralNU lam z =
      Real.cosh z.re * Real.cos z.im * Real.cos (lam*z.im) * Real.sin (lam*z.im) -
      Real.sinh z.re * Real.sinh (lam*z.re) * Real.cosh (lam*z.re) * Real.sin z.im := by
  simp only [spectralNU, spectralA_re, spectralA_im, spectralT_re, spectralT_im]
  linear_combination
    Real.sin (lam*z.im)*Real.cos (lam*z.im)*Real.cosh z.re*Real.cos z.im *
      Real.cosh_sq_sub_sinh_sq (lam*z.re) -
    Real.cosh (lam*z.re)*Real.sinh (lam*z.re)*Real.sinh z.re*Real.sin z.im *
      Real.sin_sq_add_cos_sq (lam*z.im)

theorem spectralNV_formula (lam : ℝ) (z : ℂ) :
    spectralNV lam z =
      Real.sinh z.re * Real.cosh z.re * Real.sinh (lam*z.re) * Real.sin (lam*z.im) -
      Real.cosh (lam*z.re) * Real.cos z.im * Real.sin z.im * Real.cos (lam*z.im) := by
  simp only [spectralNV, spectralA_re, spectralA_im, spectralS_re, spectralS_im]
  linear_combination
    -Real.cosh (lam*z.re)*Real.cos (lam*z.im)*Real.sin z.im*Real.cos z.im *
      Real.cosh_sq_sub_sinh_sq z.re +
    Real.sinh (lam*z.re)*Real.sin (lam*z.im)*Real.cosh z.re*Real.sinh z.re *
      Real.sin_sq_add_cos_sq z.im

theorem spectralNU_sq_sub_det_sq (lam : ℝ) (z : ℂ) :
    spectralNU lam z ^2 - spectralDet lam z ^2 = geometryF2 lam z.re z.im *
      (Real.cos z.im^2 * Real.sin (lam*z.im)^2 - Real.sinh (lam*z.re)^2 * Real.sin z.im^2) := by
  rw [spectralNU_formula, spectralDet_formula]
  exact numeratorU_factor _ _ _ _ _ _ _ _

theorem spectralNV_sq_sub_det_sq (lam : ℝ) (z : ℂ) :
    spectralNV lam z ^2 - spectralDet lam z ^2 = -geometryF1 lam z.re z.im *
      (Real.sinh z.re^2 * Real.sin (lam*z.im)^2 - Real.sin z.im^2 * Real.cos (lam*z.im)^2) := by
  rw [spectralNV_formula, spectralDet_formula]
  convert numeratorV_factor (Real.sinh z.re) (Real.cosh z.re) (Real.sinh (lam*z.re))
    (Real.cosh (lam*z.re)) (Real.cos z.im) (Real.sin z.im) (Real.cos (lam*z.im))
    (Real.sin (lam*z.im)) using 1
  unfold geometryF1
  ring

end
end IsingBulk.Anisotropic
