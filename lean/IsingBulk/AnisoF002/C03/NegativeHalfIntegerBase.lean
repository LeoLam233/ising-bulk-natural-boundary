import IsingBulk.AnisoF002.C03.NegativeComplexQuadraticPeriod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.RCLike.Sqrt

/-!
# The complex half-integer base period on the real radius

A positive real Laplace variable and the complex Gaussian integral evaluate
the actual real-radius period.  Absolute convergence of the double integral
is proved from its real positive-curvature majorant before Fubini is used.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem integrable_real_inverse_quadratic {τ b : ℝ} (hτ : 0 < τ) (hb : 0 < b) :
    Integrable (fun x : ℝ => (τ + b * x ^ 2)⁻¹) := by
  let c := min τ b
  have hc : 0 < c := lt_min hτ hb
  apply ((integrable_inv_one_add_sq).const_mul c⁻¹).mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.inv₀ (by fun_prop)
    intro x
    positivity
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity : 0 < τ + b * x ^ 2)),
      ← mul_inv]
    apply inv_anti₀ (by positivity)
    have hcτ : c ≤ τ := min_le_left _ _
    have hcb : c ≤ b := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hcb (sq_nonneg x)]

def quadraticLaplace (τ : ℝ) (h : ℂ) (x t : ℝ) : ℂ :=
  Complex.exp (-((τ : ℂ) + h * (x : ℂ) ^ 2) * t)

theorem quadraticLaplace_norm (τ : ℝ) (h : ℂ) (x t : ℝ) :
    ‖quadraticLaplace τ h x t‖ = Real.exp (-(τ + h.re * x ^ 2) * t) := by
  simp [quadraticLaplace, Complex.norm_exp, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.mul_im]

theorem quadraticLaplace_integral_time {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), quadraticLaplace τ h x t) =
      ((τ : ℂ) + h * (x : ℂ) ^ 2)⁻¹ := by
  have hp : 0 < ((τ : ℂ) + h * (x : ℂ) ^ 2).re := by
    simpa only [Complex.ofReal_pow] using radial_denominator_re_pos hτ hh (sq_nonneg x)
  unfold quadraticLaplace
  rw [integral_exp_mul_complex_Ioi (show (-((τ : ℂ) + h * (x : ℂ) ^ 2)).re < 0 by
    rw [Complex.neg_re]
    exact neg_lt_zero.mpr hp)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [neg_div_neg_eq, one_div]

theorem quadraticLaplace_integral_norm_time {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), ‖quadraticLaplace τ h x t‖) =
      (τ + h.re * x ^ 2)⁻¹ := by
  simp_rw [quadraticLaplace_norm]
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity : 0 < τ + h.re * x ^ 2))]
  simp only [mul_zero, Real.exp_zero]
  rw [neg_div_neg_eq, one_div]

theorem quadraticLaplace_integrable {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    Integrable (Function.uncurry (quadraticLaplace τ h))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  apply (integrable_prod_iff (by
    exact (show Continuous (Function.uncurry (quadraticLaplace τ h)) by
      unfold quadraticLaplace Function.uncurry; fun_prop).aestronglyMeasurable)).mpr
  constructor
  · filter_upwards with x
    change IntegrableOn (fun t : ℝ =>
      Complex.exp (-((τ : ℂ) + h * (x : ℂ) ^ 2) * t)) (Ioi 0)
    apply integrableOn_exp_mul_complex_Ioi
    have hp := radial_denominator_re_pos hτ hh (sq_nonneg x)
    simpa only [Complex.neg_re, Complex.ofReal_pow, neg_lt_zero] using hp
  · have hi : Integrable (fun x : ℝ => (τ + h.re * x ^ 2)⁻¹)
        (volume.restrict (Ioi 0)) := (integrable_real_inverse_quadratic hτ hh).integrableOn
    simpa only [Function.uncurry_apply_pair, quadraticLaplace_integral_norm_time hτ hh] using hi

theorem quadraticLaplace_integral_radius {τ : ℝ} {h : ℂ}
    (hh : 0 < h.re) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), quadraticLaplace τ h x t) =
      (Real.exp (-τ * t) : ℂ) * ((Real.pi / (h * t)) ^ (1 / 2 : ℂ) / 2) := by
  have he : (fun x : ℝ => quadraticLaplace τ h x t) =
      (fun x : ℝ => (Real.exp (-τ * t) : ℂ) *
        Complex.exp (-(h * t) * (x : ℂ) ^ 2)) := by
    funext x
    unfold quadraticLaplace
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he, integral_const_mul, integral_gaussian_complex_Ioi]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] using mul_pos hh ht

theorem complex_cpow_positive_real_mul {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ≠ 0)
    (w : ℂ) : ((r : ℂ) * z) ^ w = (r : ℂ) ^ w * z ^ w := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hz),
    Complex.log_ofReal_mul hr hz, add_mul, Complex.exp_add,
    Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hz,
    Complex.ofReal_log hr.le]

theorem gaussian_complex_radius_factor {h : ℂ} (hh : 0 < h.re)
    {t : ℝ} (ht : 0 < t) :
    (Real.pi / (h * t)) ^ (1 / 2 : ℂ) =
      (t ^ (-(1 / 2) : ℝ) : ℝ) * (Real.pi / h) ^ (1 / 2 : ℂ) := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show (Real.pi : ℂ) / (h * t) = (t⁻¹ : ℝ) * (Real.pi / h) by
    push_cast; ring,
    complex_cpow_positive_real_mul (inv_pos.mpr ht) (div_ne_zero hp hh0)]
  congr 1
  calc
    ((t⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((t⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      convert (Complex.ofReal_cpow (inv_pos.mpr ht).le (1 / 2 : ℝ)).symm using 1
      norm_num
    _ = _ := by rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]

theorem integral_inverse_sqrt_laplace {τ : ℝ} (hτ : 0 < τ) :
    (∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) * Real.exp (-τ * t)) =
      Real.sqrt τ⁻¹ * Real.sqrt Real.pi := by
  have he := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (show (0 : ℝ) < 1 / 2 by norm_num) hτ
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num,
    Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow] at he
  simpa only [neg_mul, one_div] using he

/-- The half-integer base period, with the principal complex Gaussian phase. -/
theorem integral_inverse_complex_quadratic {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ x in Ioi (0 : ℝ), ((τ : ℂ) + h * (x : ℂ) ^ 2)⁻¹) =
      (Real.pi / h) ^ (1 / 2 : ℂ) / 2 *
        ((Real.sqrt τ⁻¹ * Real.sqrt Real.pi : ℝ) : ℂ) := by
  calc
    _ = ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), quadraticLaplace τ h x t := by
      simp_rw [quadraticLaplace_integral_time hτ hh]
    _ = ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), quadraticLaplace τ h x t :=
      integral_integral_swap (quadraticLaplace_integrable hτ hh)
    _ = ∫ t in Ioi (0 : ℝ), (Real.pi / h) ^ (1 / 2 : ℂ) / 2 *
        ((t ^ (-(1 / 2) : ℝ) * Real.exp (-τ * t) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [quadraticLaplace_integral_radius hh ht,
        gaussian_complex_radius_factor hh ht, Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      calc
        _ = ((∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) * Real.exp (-τ * t) : ℝ) : ℂ) := by
          exact integral_ofReal
        _ = _ := by rw [integral_inverse_sqrt_laplace hτ]

theorem integral_inverse_complex_quadratic_ne_zero {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ x in Ioi (0 : ℝ), ((τ : ℂ) + h * (x : ℂ) ^ 2)⁻¹) ≠ 0 := by
  rw [integral_inverse_complex_quadratic hτ hh]
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply mul_ne_zero
  · exact div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hp hh0))) (by norm_num)
  · exact_mod_cast (mul_pos (Real.sqrt_pos.mpr (inv_pos.mpr hτ))
      (Real.sqrt_pos.mpr Real.pi_pos)).ne'

end
end IsingBulk.AnisoF002.NegativeHT.Angular
