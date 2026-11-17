import IsingBulk.AnisoF002.C03.NegativeHalfIntegerPeriod
import IsingBulk.AnisoF002.C03.NegativeComplexSquareRootPhase

/-! # Exact physical parity interfaces for constrained complex quadratic periods -/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set

theorem quadraticPeriod_integer_ne_zero {d α : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ v, quadraticPeriodIntegrand d (α + m + 1) τ h v ∂independentMeasure d) ≠ 0 := by
  obtain ⟨hpos, hp⟩ := radialPower_of_integer_shape hα
  simpa only [show α - 1 + m + 2 = α + m + 1 by omega] using
    quadraticPeriod_ne_zero_of_radialPower hd hp m hτ hh

theorem quadraticPeriod_integer_integrable {d α : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    Integrable (quadraticPeriodIntegrand d (α + m + 1) τ h) (independentMeasure d) :=
  Integrable.of_integral_ne_zero (quadraticPeriod_integer_ne_zero hd hα m hτ hh)

theorem integral_quadraticPeriod_half_integer_sqrt {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ v, quadraticPeriodIntegrand d (a + 1) τ h v ∂independentMeasure d) =
      (constrainedGaussianIntegral d : ℂ) * (Real.sqrt Real.pi : ℂ) * Complex.sqrt h /
        ((a.factorial : ℂ) * h ^ (a + 1) * (Real.sqrt τ : ℂ)) := by
  rw [integral_quadraticPeriod_half_integer hd ha hτ hh, gaussian_complex_sqrt_phase hh,
    Real.sqrt_inv, Complex.ofReal_inv]
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hs : Complex.sqrt h ≠ 0 := complex_sqrt_ne_zero hh0
  have hτs : (Real.sqrt τ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hτ).ne'
  have hf : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  rw [show h ^ (a + 1) = h ^ a * (Complex.sqrt h) ^ 2 by
    rw [pow_succ, complex_sqrt_sq]]
  field_simp

theorem quadraticPeriod_half_integer_integrable {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    Integrable (quadraticPeriodIntegrand d (a + 1) τ h) (independentMeasure d) :=
  Integrable.of_integral_ne_zero (quadraticPeriod_half_integer_ne_zero hd ha hτ hh)

theorem radialPower_odd_dimension (k : ℕ) :
    radialPower (2 * k + 1) = 2 * (2 * (k + 1) ^ 2 - 1) := by
  have hnat : 1 ≤ 2 * (k + 1) ^ 2 := by
    have : 0 < 2 * (k + 1) ^ 2 := by positivity
    omega
  have hc : ((2 * (k + 1) ^ 2 - 1 : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) ^ 2 - 1 := by
    rw [Nat.cast_sub hnat]
    push_cast
    ring
  have hshape := radialShape_exact (show 0 < 2 * k + 1 by omega)
  unfold radialShape at hshape
  have hr : (radialPower (2 * k + 1) : ℝ) =
      2 * ((2 * (k + 1) ^ 2 - 1 : ℕ) : ℝ) := by
    rw [hc]
    push_cast at hshape
    nlinarith
  exact_mod_cast hr

/-- Every even particle population, including the two-particle base population. -/
theorem quadraticPeriod_even_particles_ne_zero (k : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ v, quadraticPeriodIntegrand (2 * k + 1) (2 * (k + 1) ^ 2) τ h v
      ∂independentMeasure (2 * k + 1)) ≠ 0 := by
  have hnat : 1 ≤ 2 * (k + 1) ^ 2 := by
    have : 0 < 2 * (k + 1) ^ 2 := by positivity
    omega
  simpa only [Nat.sub_add_cancel hnat] using
    quadraticPeriod_half_integer_ne_zero (show 0 < 2 * k + 1 by omega)
      (radialPower_odd_dimension k) hτ hh

end
end IsingBulk.AnisoF002.NegativeHT.Angular
