import IsingBulk.AnisoF002.C03.NegativeVandermondeRadial
import IsingBulk.AnisoF002.NegativeHT.ComplexRadialBeta

/-!
# Exact complex quadratic periods for the actual constrained Vandermonde measure

The radial measure and its Mehta normalization are constructed in F002.
The remaining scalar half-line integral is the already checked independent
F002 complex Beta calculation.  No angular distribution or normalization
is an additional premise.  The final even-dimension specialization covers
every odd particle population at least three and every convergent order.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators

def quadraticPeriodIntegrand (d k : ℕ) (τ : ℝ) (h : ℂ)
    (v : constrainedPlane d) : ℂ :=
  (planeVandermonde v : ℂ) / ((τ : ℂ) + h * (‖v‖ ^ 2 : ℝ)) ^ k

theorem radialShape_of_radialPower {d a : ℕ} (ha : radialPower d = 2 * a + 1) :
    radialShape d = (a : ℝ) + 1 := by
  unfold radialShape
  rw [ha]
  push_cast
  ring

/-- The exact full-plane period, including the independent-coordinate Jacobian. -/
theorem integral_quadraticPeriod_of_radialPower {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a + 1) (m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ v, quadraticPeriodIntegrand d (a + m + 2) τ h v ∂independentMeasure d) =
      (constrainedGaussianIntegral d : ℂ) * (m.factorial : ℂ) /
        (((a + m + 1).factorial : ℂ) * h ^ (a + 1) * (τ : ℂ) ^ (m + 1)) := by
  have hf : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hΓ : Real.Gamma (radialShape d) = a.factorial := by
    rw [radialShape_of_radialPower ha, Real.Gamma_nat_eq_factorial]
  have hr := vandermonde_quadratic_complex_integral hd ha
    (fun q => (1 : ℂ) / ((τ : ℂ) + h * q) ^ (a + m + 2))
  have hl : (fun v : constrainedPlane d =>
      planeVandermonde v • ((1 : ℂ) / ((τ : ℂ) + h * (‖v‖ ^ 2 : ℝ)) ^ (a + m + 2))) =
      quadraticPeriodIntegrand d (a + m + 2) τ h := by
    funext v
    simp only [quadraticPeriodIntegrand, Complex.real_smul, mul_one_div]
  have hq : (fun q : ℝ =>
      q ^ a • ((1 : ℂ) / ((τ : ℂ) + h * q) ^ (a + m + 2))) =
      complexRadialIntegrand a m τ h := by
    funext q
    simp only [complexRadialIntegrand, Complex.real_smul, Complex.ofReal_pow, mul_one_div]
  rw [hl, hq, integral_complexRadialBeta a m hτ hh, hΓ, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_natCast] at hr
  rw [hr]
  field_simp

theorem quadraticPeriod_ne_zero_of_radialPower {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a + 1) (m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ v, quadraticPeriodIntegrand d (a + m + 2) τ h v ∂independentMeasure d) ≠ 0 := by
  rw [integral_quadraticPeriod_of_radialPower hd ha m hτ hh]
  have hG : (constrainedGaussianIntegral d : ℂ) ≠ 0 := by
    exact_mod_cast (constrainedGaussianIntegral_pos d).ne'
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  exact div_ne_zero (mul_ne_zero hG (by exact_mod_cast Nat.factorial_ne_zero m))
    (mul_ne_zero (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (a + m + 1))
      (pow_ne_zero _ hh0)) (pow_ne_zero _ hτ0))

theorem quadraticPeriod_integrable_of_radialPower {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a + 1) (m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    Integrable (quadraticPeriodIntegrand d (a + m + 2) τ h) (independentMeasure d) :=
  Integrable.of_integral_ne_zero (quadraticPeriod_ne_zero_of_radialPower hd ha m hτ hh)

theorem radialPower_of_integer_shape {d α : ℕ} (hα : radialShape d = (α : ℝ)) :
    0 < α ∧ radialPower d = 2 * (α - 1) + 1 := by
  have hpos : 0 < α := by exact_mod_cast hα ▸ radialShape_pos d
  have he : radialPower d + 1 = 2 * α := by
    have hr : (radialPower d : ℝ) + 1 = 2 * (α : ℝ) := by
      rw [← hα, radialShape]
      ring
    exact_mod_cast hr
  exact ⟨hpos, by omega⟩

/-- Integer-shape interface for the actual constrained plane, all orders at once. -/
theorem integral_quadraticPeriod_integer {d α : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ v, quadraticPeriodIntegrand d (α + m + 1) τ h v ∂independentMeasure d) =
      (constrainedGaussianIntegral d : ℂ) * (m.factorial : ℂ) /
        (((α + m).factorial : ℂ) * h ^ α * (τ : ℂ) ^ (m + 1)) := by
  obtain ⟨hpos, hp⟩ := radialPower_of_integer_shape hα
  simpa only [show α - 1 + m + 2 = α + m + 1 by omega,
    show α - 1 + m + 1 = α + m by omega, Nat.sub_add_cancel hpos] using
    integral_quadraticPeriod_of_radialPower hd hp m hτ hh

theorem radialShape_even_dimension {k : ℕ} (hk : 0 < k) :
    radialShape (2 * k) = ((2 * k * (k + 1) : ℕ) : ℝ) := by
  rw [radialShape_exact (by omega : 0 < 2 * k)]
  push_cast
  ring

/-- Full physical odd-particle period, with no unproved radial-shape hypothesis. -/
theorem integral_quadraticPeriod_odd_particles {k : ℕ} (hk : 0 < k)
    (m : ℕ) {τ : ℝ} {h : ℂ} (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ v, quadraticPeriodIntegrand (2 * k) (2 * k * (k + 1) + m + 1) τ h v
      ∂independentMeasure (2 * k)) =
      (constrainedGaussianIntegral (2 * k) : ℂ) * (m.factorial : ℂ) /
        (((2 * k * (k + 1) + m).factorial : ℂ) * h ^ (2 * k * (k + 1)) *
          (τ : ℂ) ^ (m + 1)) :=
  integral_quadraticPeriod_integer (by omega) (radialShape_even_dimension hk) m hτ hh

end
end IsingBulk.AnisoF002.NegativeHT.Angular
