import IsingBulk.Anisotropic.Geometry.Definitions
import Mathlib.Tactic

namespace IsingBulk.Anisotropic
noncomputable section

/-- The unsquared spectral equation cannot hold at the common sine zero. -/
theorem zero_not_mem_spectralSet (lam : ℝ) : (0 : ℂ) ∉ spectralSet lam := by
  rintro ⟨u, hu, v, hv, h⟩
  simp [spectralA, spectralS, spectralT] at h

/-- The algebraic dispersion identity, without selecting any square-root sign. -/
theorem spectralA_sq (lam : ℝ) (z : ℂ) :
    spectralA lam z ^ 2 = (1 + spectralS z ^ 2) * (1 + spectralT lam z ^ 2) := by
  unfold spectralA spectralS spectralT
  have h := Complex.cosh_sq_sub_sinh_sq z
  have h' := Complex.cosh_sq_sub_sinh_sq ((lam : ℂ) * z)
  calc
    _ = Complex.cosh z ^ 2 * Complex.cosh ((lam : ℂ) * z) ^ 2 := by ring
    _ = _ := by rw [show Complex.cosh z ^ 2 = 1 + Complex.sinh z ^ 2 by linear_combination h,
      show Complex.cosh ((lam : ℂ)*z)^2 = 1 + Complex.sinh ((lam : ℂ)*z)^2 by linear_combination h']

/-- The corner identity (2.22) at arbitrary complex temperature. -/
theorem spectral_corner_identity (lam : ℝ) (z : ℂ) (e f : ℂ)
    (he : e ^ 2 = 1) (hf : f ^ 2 = 1) :
    spectralA lam z ^ 2 - (e * spectralS z + f * spectralT lam z) ^ 2 =
      (spectralProduct lam z - e*f)^2 := by
  rw [spectralA_sq]
  unfold spectralProduct
  linear_combination -(spectralS z)^2 * he - (spectralT lam z)^2 * hf - f^2 * he - hf

/-- Cramer's rule for the two *real* spectral coordinates, with no squaring. -/
theorem real_coordinates_unique (a b A : ℂ) (u v : ℝ)
    (h : A = a * (u : ℂ) + b * (v : ℂ)) :
    A.re * b.im - A.im * b.re = (a.re * b.im - a.im * b.re) * u ∧
    a.re * A.im - a.im * A.re = (a.re * b.im - a.im * b.re) * v := by
  subst A
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.add_im, Complex.mul_im, zero_add]
  constructor <;> ring

/-- A nonzero determinant makes real representing coordinates unique. -/
theorem real_coordinates_injective (a b : ℂ)
    (hd : a.re * b.im - a.im * b.re ≠ 0) (u v u' v' : ℝ)
    (h : a * (u : ℂ) + b * (v : ℂ) = a * (u' : ℂ) + b * (v' : ℂ)) :
    u = u' ∧ v = v' := by
  have h1 := real_coordinates_unique a b _ u v rfl
  have h2 := real_coordinates_unique a b _ u' v' h
  constructor
  · apply mul_left_cancel₀ hd
    exact h1.1.symm.trans h2.1
  · apply mul_left_cancel₀ hd
    exact h1.2.symm.trans h2.2

end
end IsingBulk.Anisotropic
