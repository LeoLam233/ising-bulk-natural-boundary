import IsingBulk.AnisoF002.C03.NegativeModelNormalization
import IsingBulk.AnisoF002.C03.NegativeCenterAmplitude

/-!
# Actual center normalization times the complete constrained quadratic period

The complete independent-coordinate period retains its `1 / sqrt n`.
The physical root `b` is not identified with a principal square root by
definition: the exact answer contains `sqrt B / b`, a common branch sign
when `b² = B`.  This is an equality with the unchanged frozen model.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open MeasureTheory Angular Filter
open scoped BigOperators Topology

def centerDensityScalar (n : ℕ) (b : ℂ) (s : ℝ) : ℂ :=
  -(2 * b ^ (n ^ 2 - 2)) /
    ((n : ℂ) * windingNormalization n * (2 : ℂ) ^ (n * (n - 1)) *
      (s : ℂ) ^ (n ^ 2 - 1))

theorem odd_physical_root_power {k : ℕ} (hk : 0 < k)
    {b B : ℂ} (hb : b ^ 2 = B) (hb0 : b ≠ 0) :
    b ^ ((2 * k + 1) ^ 2 - 2) = B ^ (2 * k * (k + 1)) / b := by
  apply (eq_div_iff hb0).mpr
  rw [← pow_succ]
  have he : (2 * k + 1) ^ 2 - 2 + 1 = 2 * (2 * k * (k + 1)) := by
    have hdeg : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    have ha : 0 < 2 * k * (k + 1) := by positivity
    omega
  rw [he, pow_mul, hb]

theorem odd_center_density_scalar {k : ℕ} (hk : 0 < k)
    {b B : ℂ} (hb : b ^ 2 = B) (hb0 : b ≠ 0) (s : ℝ) :
    centerDensityScalar (2 * k + 1) b s =
      -(2 * B ^ (2 * k * (k + 1))) /
      (b * ((2 * k + 1 : ℕ) : ℂ) * ((2 * k + 1).factorial : ℂ) *
        (2 : ℂ) ^ (2 * (2 * k * (k + 1))) * (Real.pi : ℂ) ^ (2 * k) *
        (s : ℂ) ^ (2 * (2 * k * (k + 1)))) := by
  have hdeg : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by
    have hh : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    omega
  have htwo : (2 : ℂ) ^ (2 * k) * (2 : ℂ) ^ ((2 * k + 1) * (2 * k)) =
      (2 : ℂ) ^ (2 * (2 * k * (k + 1))) := by
    rw [← pow_add]
    congr 1
    ring
  have hden : (((2 * k + 1 : ℕ) : ℂ) * windingNormalization (2 * k + 1) *
      (2 : ℂ) ^ ((2 * k + 1) * ((2 * k + 1) - 1)) *
      (s : ℂ) ^ ((2 * k + 1) ^ 2 - 1)) =
      ((2 * k + 1 : ℕ) : ℂ) * ((2 * k + 1).factorial : ℂ) *
        (2 : ℂ) ^ (2 * (2 * k * (k + 1))) * (Real.pi : ℂ) ^ (2 * k) *
        (s : ℂ) ^ (2 * (2 * k * (k + 1))) := by
    rw [windingNormalization, Nat.add_sub_cancel, hdeg, mul_pow]
    calc
      _ = ((2 * k + 1 : ℕ) : ℂ) * ((2 * k + 1).factorial : ℂ) *
          ((2 : ℂ) ^ (2 * k) * (2 : ℂ) ^ ((2 * k + 1) * (2 * k))) *
          (Real.pi : ℂ) ^ (2 * k) * (s : ℂ) ^ (2 * (2 * k * (k + 1))) := by ring
      _ = _ := by rw [htwo]
  rw [centerDensityScalar, hden, odd_physical_root_power hk hb hb0]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem twice_center_quadratic_period_model {k : ℕ} (hk : 0 < k) (m : ℕ)
    {b B h : ℂ} (hB : B ≠ 0) (hb : b ^ 2 = B)
    {s τ : ℝ} (hs : s ≠ 0) (hτ : 0 < τ) (hh : 0 < h.re) :
    2 * centerDensityScalar (2 * k + 1) b s *
      (∫ v, quadraticPeriodIntegrand (2 * k) (2 * k * (k + 1) + m + 1) τ
        (h / (2 * ((2 * k + 1 : ℕ) : ℂ))) v ∂independentMeasure (2 * k)) =
      (Complex.sqrt B / b) *
        modelCoefficient (2 * k + 1) (2 * k * (k + 1) + m) B h s τ := by
  have hb0 : b ≠ 0 := by
    intro he
    rw [he, zero_pow two_ne_zero] at hb
    exact hB hb.symm
  have hn : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hnc : (((2 * k + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hn.ne'
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsn : (Real.sqrt ((2 * k + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
  have hsb : Complex.sqrt B ≠ 0 := complex_sqrt_ne_zero hB
  have hnf : ((2 * k + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
  have hjf : ((2 * k * (k + 1) + m).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k * (k + 1) + m)
  have hhscaled : 0 < (h / (2 * ((2 * k + 1 : ℕ) : ℂ))).re := by
    rw [show (2 : ℂ) * ((2 * k + 1 : ℕ) : ℂ) =
      ((2 * ((2 * k + 1 : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.div_ofReal_re]
    exact div_pos hh (mul_pos (by norm_num) hn)
  rw [integral_quadraticPeriod_odd_particles hk m hτ hhscaled,
    constrainedGaussianIntegral_odd_exact, odd_center_density_scalar hk hb hb0,
    model_natural_power_form _ _ hB, gammaQuotient, Nat.add_sub_cancel_left]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  rw [show (2 : ℂ) ^ (2 * (2 * k * (k + 1))) =
      (2 : ℂ) ^ (2 * k * (k + 1)) * (2 : ℂ) ^ (2 * k * (k + 1)) by
      rw [← pow_add]; congr 1; omega,
    show (Real.pi : ℂ) ^ (2 * k) = (Real.pi : ℂ) ^ k * (Real.pi : ℂ) ^ k by
      rw [← pow_add]; congr 1; omega,
    show (τ : ℂ) ^ (2 * k * (k + 1) + m + 1) =
      (τ : ℂ) ^ (2 * k * (k + 1)) * (τ : ℂ) ^ (m + 1) by
      simpa only [Nat.add_assoc] using
        (pow_add (τ : ℂ) (2 * k * (k + 1)) (m + 1))]
  simp only [div_pow, mul_pow]
  field_simp
  ring

theorem physical_root_branch_sign_sq {b B : ℂ} (hB : B ≠ 0) (hb : b ^ 2 = B) :
    (Complex.sqrt B / b) ^ 2 = 1 := by
  rw [div_pow, complex_sqrt_sq, hb, div_self hB]

theorem physical_root_branch_sign_norm {b B : ℂ} (hB : B ≠ 0) (hb : b ^ 2 = B) :
    ‖Complex.sqrt B / b‖ = 1 := by
  have he := eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt B / b) (1 : ℂ)
    (by simpa using physical_root_branch_sign_sq hB hb)
  rcases he with he | he <;> simp [he]

/-- The complete actual first-winding center, twice for the two conjugate
angular centers, times the full independent-coordinate quadratic period.
The only remaining factor is the explicitly retained physical root sign. -/
theorem actual_twice_center_quadratic_period_model {k : ℕ} (hk : 0 < k) (m : ℕ)
    (b B : ℂ → ℂ) (g : ℂ × ℂ → ℂ) (φ d : ℝ) {h : ℂ}
    (hφ : Real.sin φ ≠ 0) (hτ : 0 < 1 - Real.cos d) (hh : 0 < h.re)
    (hB : AnalyticAt ℂ B ((1 - Real.cos d : ℝ) : ℂ))
    (hBne : B ((1 - Real.cos d : ℝ) : ℂ) ≠ 0)
    (hb : b ((1 - Real.cos d : ℝ) : ℂ) ^ 2 = B ((1 - Real.cos d : ℝ) : ℂ))
    (hga : AnalyticAt ℂ g ((1 - Real.cos d : ℝ), (d : ℂ)))
    (hgv : g ((1 - Real.cos d : ℝ), (d : ℂ)) = (φ : ℂ) * Complex.I)
    (hge : ∀ᶠ a in 𝓝 ((1 - Real.cos d : ℝ), (d : ℂ)),
      Complex.cosh (g a) = localNegativeDispersion B φ a) :
    2 * filledNegativeDensityAt (2 * k + 1) b g (d : ℂ)
        ((1 - Real.cos d : ℝ) : ℂ) 0 *
      (∫ v, quadraticPeriodIntegrand (2 * k) (2 * k * (k + 1) + m + 1)
        (1 - Real.cos d) (h / (2 * ((2 * k + 1 : ℕ) : ℂ))) v
        ∂independentMeasure (2 * k)) =
      (Complex.sqrt (B ((1 - Real.cos d : ℝ) : ℂ)) /
        b ((1 - Real.cos d : ℝ) : ℂ)) *
      modelCoefficient (2 * k + 1) (2 * k * (k + 1) + m)
        (B ((1 - Real.cos d : ℝ) : ℂ)) h (Real.sin φ) (1 - Real.cos d) := by
  rw [filledNegativeDensity_exact_center (2 * k + 1) (by exact ⟨k, rfl⟩)
    (by omega) b B g φ d hφ hB hBne hb hga hgv hge]
  exact twice_center_quadratic_period_model hk m hBne hb hφ hτ hh

end
end IsingBulk.AnisoF002.NegativeHT
