import IsingBulk.AnisoF002.Geometry.EndpointDefect
import IsingBulk.Anisotropic.Geometry.Definitions
import Mathlib.Tactic

/-!
# Literal spectral-coordinate attachment of the new F002 defect

Only five historical definitions are used: `spectralS`, `spectralT`,
`spectralA`, `geometryF1`, and `geometryF2`.  No historical theorem is used.
The new endpoint identity is attached to the unsquared physical incidence
`A = S*u + T*v` without first dividing by the Cramer determinant.

The strict-coordinate result remains local.  Global domains, endpoint
realization, nonramification, and density are not asserted here.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic

def spectralDetF002 (lam : ℝ) (z : ℂ) : ℝ :=
  (spectralS z).re * (spectralT lam z).im - (spectralS z).im * (spectralT lam z).re

def spectralNumF002 (lam : ℝ) (z : ℂ) : ℝ :=
  (spectralA lam z).re * (spectralT lam z).im - (spectralA lam z).im * (spectralT lam z).re

theorem complex_sinh_re (z : ℂ) :
    (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.sinh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp [Complex.sinh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem complex_sinh_im (z : ℂ) :
    (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.sinh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp [Complex.sinh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem complex_cosh_re (z : ℂ) :
    (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp [Complex.cosh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem complex_cosh_im (z : ℂ) :
    (Complex.cosh z).im = Real.sinh z.re * Real.sin z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp [Complex.sinh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem determinant_formula (lam : ℝ) (z : ℂ) :
    spectralDetF002 lam z =
      detExpr (Real.sinh z.re) (Real.cosh z.re)
        (Real.sinh (lam * z.re)) (Real.cosh (lam * z.re))
        (Real.cos z.im) (Real.sin z.im) (Real.cos (lam * z.im)) (Real.sin (lam * z.im)) := by
  delta spectralDetF002 spectralS spectralT
  simp only [complex_sinh_re, complex_sinh_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, detExpr]
  ring

theorem numerator_formula (lam : ℝ) (z : ℂ) :
    spectralNumF002 lam z =
      numExpr (Real.sinh z.re) (Real.cosh z.re)
        (Real.sinh (lam * z.re)) (Real.cosh (lam * z.re))
        (Real.cos z.im) (Real.sin z.im) (Real.cos (lam * z.im)) (Real.sin (lam * z.im)) := by
  delta spectralNumF002 spectralA spectralT
  simp only [Complex.mul_re, Complex.mul_im,
    complex_cosh_re, complex_cosh_im, complex_sinh_re, complex_sinh_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero, numExpr]
  linear_combination
    Real.sin (lam * z.im) * Real.cos (lam * z.im) * Real.cosh z.re * Real.cos z.im *
      Real.cosh_sq_sub_sinh_sq (lam * z.re) -
    Real.cosh (lam * z.re) * Real.sinh (lam * z.re) * Real.sinh z.re * Real.sin z.im *
      Real.sin_sq_add_cos_sq (lam * z.im)

theorem cramer_numerator_of_unsquared_incidence {lam : ℝ} {z : ℂ} {u v : ℝ}
    (h : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)) :
    spectralNumF002 lam z = spectralDetF002 lam z * u := by
  unfold spectralNumF002
  rw [h]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add]
  unfold spectralDetF002
  ring

/-- The precise division-free spectral defect of F002. -/
theorem spectral_endpoint_defect {lam : ℝ} {z : ℂ} {u v : ℝ}
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ))
    (hedge : geometryF1 lam z.re z.im = 0) :
    Real.cosh (lam * z.re) ^ 2 * spectralDetF002 lam z ^ 2 * (1 - u ^ 2) =
      Real.sinh (lam * z.re) ^ 2 * geometryF2 lam z.re z.im ^ 2 := by
  have hc := cramer_numerator_of_unsquared_incidence hinc
  rw [numerator_formula, determinant_formula] at hc
  rw [determinant_formula]
  exact edge_defect_identity _ _ _ _ _ _ _ _ u
    (Real.cosh_sq_sub_sinh_sq z.re) (Real.cosh_sq_sub_sinh_sq (lam * z.re))
    (Real.cos_sq_add_sin_sq z.im) (Real.cos_sq_add_sin_sq (lam * z.im)) hedge hc

theorem spectral_regular_endpoint_strict {lam : ℝ} {z : ℂ} {u v : ℝ}
    (hlam : 0 < lam) (hx : 0 < z.re)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ))
    (hedge : geometryF1 lam z.re z.im = 0)
    (hsecond : geometryF2 lam z.re z.im ≠ 0) :
    spectralDetF002 lam z ≠ 0 ∧ |u| < 1 := by
  have hc := cramer_numerator_of_unsquared_incidence hinc
  rw [numerator_formula, determinant_formula] at hc
  rw [determinant_formula]
  exact regular_edge_strict_coordinate _ _ _ _ _ _ _ _ u
    (Real.cosh_sq_sub_sinh_sq z.re) (Real.cosh_sq_sub_sinh_sq (lam * z.re))
    (Real.cos_sq_add_sin_sq z.im) (Real.cos_sq_add_sin_sq (lam * z.im)) hedge hc
    (ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos hlam hx))) hsecond

end
end IsingBulk.AnisoF002.Geometry
