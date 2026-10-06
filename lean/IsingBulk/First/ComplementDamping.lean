import IsingBulk.First.ComplementDampedGradients
import IsingBulk.First.ComplementAuxiliary

/-! Damping of the exact positive-half-line phase on admissible radial contours. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

theorem norm_angularCurve (z : ℂ) (a t : ℝ) : ‖angularCurve z a t‖ = ‖z‖ := by
  have he : ‖Complex.exp ((t : ℂ) * (a : ℂ) * Complex.I)‖ = 1 := by
    rw [← Complex.ofReal_mul]
    exact Complex.norm_exp_ofReal_mul_I (t*a)
  simp only [angularCurve, norm_mul, he, mul_one]

theorem angularCurve_real_mul (r : ℝ) (z : ℂ) (a t : ℝ) :
    angularCurve ((r : ℂ) * z) a t = (r : ℂ) * angularCurve z a t := by
  unfold angularCurve
  ring

/-- Exact imaginary dispersion on a damped pair of unit-circle coordinates. -/
theorem damped_dispersion_im {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (r : ℝ) (s : ℂ) :
    (dispersion ((r : ℂ) * x) ((r : ℂ) * y) s).im =
      (sourceS s).im + (r⁻¹ - r) / 2 * (x.im + y.im) := by
  simp only [dispersion, Complex.sub_im, Complex.div_ofNat_im, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    damped_inverse_im hx, damped_inverse_im hy]
  ring

/-- The explicit radius/parameter margin makes every dispersion denominator
lie in the upper half-plane, uniformly in both angular coordinates. -/
theorem damped_dispersion_im_positive {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hmargin : r⁻¹ - r < (sourceS s).im) :
    0 < (dispersion ((r : ℂ) * x) ((r : ℂ) * y) s).im := by
  have hri : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hk : 0 ≤ (r⁻¹ - r) / 2 := by linarith
  have hxi : -1 ≤ x.im := by
    have := (Complex.abs_im_le_norm x)
    rw [hx] at this
    exact (abs_le.mp this).1
  have hyi : -1 ≤ y.im := by
    have := (Complex.abs_im_le_norm y)
    rw [hy] at this
    exact (abs_le.mp this).1
  rw [damped_dispersion_im hx hy]
  nlinarith [mul_nonneg hk (show 0 ≤ x.im + y.im + 2 by linarith)]

/-- All actual factor exponents have strictly negative real part on the
admissible common circle. The phase is not merely a local linear model. -/
theorem singularFactorExponent_re_negative {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hmargin : r⁻¹ - r < (sourceS s).im)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (e : DoubleAngularVector N) (f : SingularFactorIndex N) (t : ℝ) :
    (singularFactorExponent r s x y e f t).re < 0 := by
  have hn (z : ℂ) (hz : ‖z‖ = 1) (a : ℝ) :
      ‖angularCurve ((r : ℂ) * z) a t‖ = r := by
    rw [norm_angularCurve, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one]
  have hprod (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖ = 1) (a : Fin N → ℝ) :
      ((∏ i, angularCurve ((r : ℂ) * z i) (a i) t) - 1).re < 0 := by
    have hnorm : ‖∏ i, angularCurve ((r : ℂ) * z i) (a i) t‖ = r ^ N := by
      rw [norm_prod]
      simp only [hn _ (hz _) _, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hle := Complex.re_le_norm (∏ i, angularCurve ((r : ℂ) * z i) (a i) t)
    rw [hnorm] at hle
    have hp : r ^ N < 1 := pow_lt_one₀ hr.le hr1 hN.ne'
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hpair (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (a b : ℝ) :
      (angularCurve ((r : ℂ) * z) a t * angularCurve ((r : ℂ) * w) b t - 1).re < 0 := by
    have hle := Complex.re_le_norm (angularCurve ((r : ℂ) * z) a t * angularCurve ((r : ℂ) * w) b t)
    rw [norm_mul, hn z hz, hn w hw] at hle
    have hp : r*r < 1 := by nlinarith
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  rcases f with b | (⟨b, i, j⟩ | i)
  · cases b
    · exact hprod x hx e.1
    · exact hprod y hy e.2
  · cases b
    · exact hpair (x i) (x j) (hx i) (hx j) (e.1 i) (e.1 j)
    · exact hpair (y i) (y j) (hy i) (hy j) (e.2 i) (e.2 j)
  · simp only [singularFactorExponent, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub]
    rw [angularCurve_real_mul, angularCurve_real_mul]
    exact neg_neg_of_pos (damped_dispersion_im_positive
      (by rw [norm_angularCurve, hx i]) (by rw [norm_angularCurve, hy i]) hr hr1 hmargin)

end
end IsingBulk.First
