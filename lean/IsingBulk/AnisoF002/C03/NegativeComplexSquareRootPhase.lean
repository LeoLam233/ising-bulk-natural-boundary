import IsingBulk.AnisoF002.C03.NegativeHalfIntegerBase

/-! # Principal square-root phase of the actual half-integer radial period -/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set

theorem complex_sqrt_sq (h : ℂ) : (Complex.sqrt h) ^ 2 = h := by
  exact Complex.cpow_nat_inv_pow h two_ne_zero

theorem complex_sqrt_ne_zero {h : ℂ} (hh : h ≠ 0) : Complex.sqrt h ≠ 0 := by
  intro he
  have hs := complex_sqrt_sq h
  rw [he, zero_pow two_ne_zero] at hs
  exact hh hs.symm

theorem gaussian_complex_sqrt_phase {h : ℂ} (hh : 0 < h.re) :
    (Real.pi / h) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) / Complex.sqrt h := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have ha : h.arg ≠ Real.pi := (Complex.arg_lt_pi_iff.mpr (Or.inl hh.le)).ne
  rw [div_eq_mul_inv, complex_cpow_positive_real_mul Real.pi_pos (inv_ne_zero hh0),
    Complex.inv_cpow h (1 / 2 : ℂ) ha]
  have hp : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    convert (Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)).symm using 1
    norm_num
  rw [hp]
  simp only [Complex.sqrt, div_eq_mul_inv, one_mul]

theorem integral_inverse_complex_quadratic_sqrt {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ x in Ioi (0 : ℝ), ((τ : ℂ) + h * (x : ℂ) ^ 2)⁻¹) =
      (Real.pi : ℂ) / (2 * (Real.sqrt τ : ℂ) * Complex.sqrt h) := by
  rw [integral_inverse_complex_quadratic hτ hh, gaussian_complex_sqrt_phase hh,
    Real.sqrt_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  have hπ : (Real.sqrt Real.pi : ℂ) ^ 2 = Real.pi := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hsτ : (Real.sqrt τ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hτ).ne'
  have hsh : Complex.sqrt h ≠ 0 := complex_sqrt_ne_zero (by intro he; simp [he] at hh)
  field_simp
  linear_combination hπ

end
end IsingBulk.AnisoF002.NegativeHT.Angular
